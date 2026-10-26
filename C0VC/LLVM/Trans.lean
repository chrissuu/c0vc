import C0VC.Ast.TypedAst
import C0VC.LLVM.Tree
import C0VC.Utils.Label
import C0VC.Utils.Temp

import Std.Data.HashMap

namespace C0VC.LLVM.Tree.Trans
open C0VC.LLVM.Tree
open C0VC.Utils.Label
open C0VC.Utils.Temp

abbrev TempEnv := Std.HashMap String Temp
abbrev SEnv := Std.HashMap String (List C0VC.TypedAst.Field)

private def resultTempName : String := "$c0vc_result"

/-- The translation state: variables in scope and the temp and label counters. -/
structure TState where
  env : TempEnv
  tc : TempCounter
  lc : LabelCounter

abbrev TransM := StateM TState

def freshTemp : TransM Temp :=
  modifyGet fun st => let (t, tc) := Temp.bumpAndCreate st.tc; (t, { st with tc })

def freshLabel : TransM Label :=
  modifyGet fun st => let (l, lc) := Label.bumpAndCreate st.lc; (l, { st with lc })

def freshLabelNamed (name : String) : TransM Label :=
  modifyGet fun st => let (l, lc) := Label.bumpAndCreateNamed st.lc name; (l, { st with lc })

/-- The temp of a variable. The typechecker guarantees variables are declared;
an unknown one gets a fresh temp, as before. -/
def varTemp (name : String) : TransM Temp := do
  match (← get).env.get? name with
  | some temp => pure temp
  | none =>
      let temp ← freshTemp
      modify fun st => { st with env := st.env.insert name temp }
      pure temp

def translateTau : C0VC.TypedAst.Tau → Tree.Tau
  | .int | .char => .int
  | .bool => .bool
  | .string => panic! "[Error] strings are not yet handled"
  | .void => .void
  | .struct name => .struct name
  | .ptr tau => .ptr (translateTau tau)
  | .array tau => .array (translateTau tau)
  | .null => .null

def defaultValOfTau : C0VC.TypedAst.Tau → Tree.Expr
  | .int => .const .int 0
  | .bool => .const .bool 0
  | .void => .const .void 0
  | .ptr _ | .array _ | .null => .null

  -- '\0'; strings are rejected by the typechecker.
  | .char
  | .string => .const .int 0
  | .struct _ => .null

def collectSEnv (structs : List (String × List C0VC.TypedAst.Field)) : SEnv :=
  structs.foldl (fun env (name, fields) => env.insert name fields) {}

def findFieldIndex? (fields : List C0VC.TypedAst.Field) (field : String) : Option Nat :=
  let rec go (idx : Nat) : List C0VC.TypedAst.Field → Option Nat
    | [] => none
    | (_, name) :: rest => if name == field then some idx else go (idx + 1) rest
  go 0 fields

def lookupFieldIndex (senv : SEnv) (structName field : String) : Nat :=
  match senv.get? structName with
  | some fields =>
      match findFieldIndex? fields field with
      | some idx => idx
      | none => panic! s!"[Error] struct {structName} has no field {field}"
  | none => panic! s!"[Error] struct {structName} used before declaration"


def exprAlreadyMaterialized : Tree.Expr → Bool
  | .const .. | .temp _ => true
  | _ => false

def translateExpr (senv : SEnv) (texpr : C0VC.TypedAst.TypedExpr) : TransM (List Tree.Command × Tree.Expr) := do
  match h : texpr.node with
  | .var name => pure ([], .temp (← varTemp name))
  | .intLit val => pure ([], .const .int (Int32.ofInt val))
  | .binop op lhs rhs =>
    let tempRes ← freshTemp
    let (cmdsLhs, transLhs) ← translateExpr senv lhs
    let (cmdsRhs, transRhs) ← translateExpr senv rhs
    -- In C0, division/modulus by zero is not undefined behavior and instead
    -- always raises a runtime exception. The checks run in runtime wrappers,
    -- which are not inlined because the runtime is a separate C file;
    -- emitting them inline (compare and branch to a cold error block) would
    -- save a call per operation.
    let cmd := match op with
      | .div => .move tempRes (.runtimeCall .checkedDiv [transLhs, transRhs])
      | .mod => .move tempRes (.runtimeCall .checkedMod [transLhs, transRhs])
      | .shl => .move tempRes (.runtimeCall .checkedShl [transLhs, transRhs])
      | .shr => .move tempRes (.runtimeCall .checkedShr [transLhs, transRhs])
      -- Assumes that binops input types are equal
      | _ => .move tempRes (.binop op (translateTau lhs.tau) transLhs transRhs)
    pure (cmdsLhs ++ cmdsRhs ++ [cmd], .temp tempRes)

  -- Ternaries are lowered to branches rather than LLVM `select`: `&&`, `||` and
  -- `!` elaborate to ternaries, and their operands must not be evaluated
  -- unconditionally.
  | .ternary test thenVal elseVal =>
    let tempRes ← freshTemp
    let (cmdsTest, transTest) ← translateExpr senv test
    let labelThen ← freshLabel
    let labelElse ← freshLabel
    let (cmdsThen, transThen) ← translateExpr senv thenVal
    let (cmdsElse, transElse) ← translateExpr senv elseVal
    let labelDone ← freshLabel
    pure ([.declare tempRes (translateTau texpr.tau)]
      ++ cmdsTest
      ++ [.ite transTest labelThen labelElse, .label labelThen]
      ++ cmdsThen
      ++ [.move tempRes transThen, .goto labelDone, .label labelElse]
      ++ cmdsElse
      ++ [.move tempRes transElse, .goto labelDone, .label labelDone]
      , .temp tempRes)

  | .trueLit => pure ([], .const .bool 1)
  | .falseLit => pure ([], .const .bool 0)

  -- TODO: chars are represented as i32. That is exact for C0 programs (chars
  -- are ASCII and only compared with == and !=), but a C function returning
  -- `char` (i8) would need an i8 type with zeroext at the external boundary.
  | .charLit c => pure ([], .const .int (Int32.ofNat c.toNat))

  | .call fname args =>
    -- Arguments are translated right to left (which numbers their temps) and
    -- their commands emitted left to right.
    let mut argCmds : List Tree.Command := []
    let mut argExps : List Tree.Expr := []
    for ⟨arg, _⟩ in args.attach.reverse do
      let (cmds, exp) ← translateExpr senv arg
      argCmds := cmds ++ argCmds
      argExps := exp :: argExps
    match texpr.tau with
    | .void => pure (argCmds ++ [.call fname argExps], .const .void 0)
    | _ =>
      let tempRes ← freshTemp
      pure (argCmds ++ [.move tempRes (.call fname argExps)], .temp tempRes)

  | .length arrayLike =>
    let (cmds, trans) ← translateExpr senv arrayLike
    let tempRes ← freshTemp
    pure (cmds ++ [.move tempRes (.runtimeCall .arrayLength [trans])], .temp tempRes)

  -- The typechecker only allows \result in @ensures, which is translated
  -- with the result temp bound.
  | .result =>
    match (← get).env.get? resultTempName with
    | some temp => pure ([], .temp temp)
    | none => panic! "[Error] \\result found outside postcondition"
  | .hastag => pure ([], .const .int 0)
  | .stringLit _ => pure ([], .const .int 0)
  | .null => pure ([], .null)
  -- Allocations run (and can fail) where they occur, before later operands.
  | .alloc tau =>
    let temp ← freshTemp
    pure ([.move temp (.alloc (translateTau tau))], .temp temp)
  | .allocArray tau size =>
    let (cmdsSize, transSize) ← translateExpr senv size
    let temp ← freshTemp
    pure (cmdsSize ++ [.move temp (.allocArray (translateTau tau) transSize)], .temp temp)
  | .deref ptr =>
    let (cmdsPtr, transPtr) ← translateExpr senv ptr
    let temp ← freshTemp
    pure (cmdsPtr ++ [.move temp (.deref transPtr (translateTau texpr.tau))], .temp temp)
  | .arrAccess arr index =>
    let (cmdsArr, transArr) ← translateExpr senv arr
    let (cmdsIndex, transIndex) ← translateExpr senv index
    let temp ← freshTemp
    pure (cmdsArr ++ cmdsIndex ++ [.move temp (.arrAccess transArr transIndex (translateTau texpr.tau))], .temp temp)
  | .dot struct field =>
    let (cmdsStruct, transStruct) ← translateExpr senv struct
    match struct.tau with
    | .struct structName =>
        let temp ← freshTemp
        let expr := .dot transStruct structName (lookupFieldIndex senv structName field) (translateTau texpr.tau)
        pure (cmdsStruct ++ [.move temp expr], .temp temp)
    | _ => panic! "[Error] dot expected struct type"
  | .arrow structPtr field =>
    let (cmdsStructPtr, transStructPtr) ← translateExpr senv structPtr
    match structPtr.tau with
    | .ptr (.struct structName) =>
        let temp ← freshTemp
        let expr := .arrow transStructPtr structName (lookupFieldIndex senv structName field) (translateTau texpr.tau)
        pure (cmdsStructPtr ++ [.move temp expr], .temp temp)
    | _ => panic! "[Error] arrow expected pointer-to-struct type"
termination_by sizeOf texpr
decreasing_by
  all_goals
    have h1 := C0VC.TypedAst.TypedExpr.sizeOf_node_lt texpr
    have h2 := congrArg sizeOf h
    simp at h2
    first
      | omega
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ args›; omega)

def translateLValueExpr (senv : SEnv) (tlv : C0VC.TypedAst.TypedLValue) :
    TransM (List Tree.Command × Tree.Expr) := do
  match h : tlv.node with
  | .var name => pure ([], .temp (← varTemp name))
  -- lvalues and their side effects are computed before the right-hand side.
  | .deref ptr =>
    let (cmdsPtr, transPtr) ← translateExpr senv ptr.toExpr
    pure (cmdsPtr, .deref transPtr (translateTau tlv.tau))
  | .arrAccess arr index =>
    let (cmdsArr, transArr) ← translateExpr senv arr.toExpr
    let (cmdsIndex, transIndex) ← translateExpr senv index
    pure (cmdsArr ++ cmdsIndex, .arrAccess transArr transIndex (translateTau tlv.tau))
  | .dot struct field =>
    let (cmdsStruct, transStruct) ← translateLValueExpr senv struct
    match struct.tau with
    | .struct structName =>
        pure (cmdsStruct, .dot transStruct structName (lookupFieldIndex senv structName field) (translateTau tlv.tau))
    | _ => panic! "[Error] dot lvalue expected struct type"
  | .arrow structPtr field =>
    let (cmdsStructPtr, transStructPtr) ← translateLValueExpr senv structPtr
    match structPtr.tau with
    | .ptr (.struct structName) =>
        pure (cmdsStructPtr, .arrow transStructPtr structName (lookupFieldIndex senv structName field) (translateTau tlv.tau))
    | _ => panic! "[Error] arrow lvalue expected pointer-to-struct type"
termination_by sizeOf tlv
decreasing_by
  all_goals
    have h1 := C0VC.TypedAst.TypedLValue.sizeOf_node_lt tlv
    have h2 := congrArg sizeOf h
    simp at h2
    omega

/-- Runtime checks for the `@requires` (or `@ensures`) clauses of a contract. -/
def translateContract (senv : SEnv) (preconditions : Bool) (annotations : List C0VC.TypedAst.Anno) :
    TransM (List Tree.Command) := do
  let mut cmds := []
  for anno in annotations do
    match anno, preconditions with
    | .requires e, true | .ensures e, false =>
        let (cmdsE, trans) ← translateExpr senv e
        cmds := cmds ++ cmdsE ++ [.runtimeCall .assert [trans]]
    | .requires _, false | .ensures _, true => pure ()
    | .asserts _, _ => panic! "[Error] asserts annotation found in function contract position"
    | .loopInvariant _, _ => panic! "[Error] loop invariant annotation found in function contract position"
  pure cmds

def translateStm (senv : SEnv) (ensures : List C0VC.TypedAst.Anno) (mstm : C0VC.TypedAst.Stm) :
    TransM (List Tree.Command) := do
  match mstm with
  | .assign lhs val =>
    match lhs.node with
    | .var varName =>
        let (cmds, expr) ← translateExpr senv val
        pure (cmds ++ [.move (← varTemp varName) expr])
    | _ =>
        -- C0 evaluates the target address, with its checks, before the
        -- right-hand side, which may change the memory the address reads.
        let (cmdsLhs, lhsExpr) ← translateLValueExpr senv lhs
        let addrTemp ← freshTemp
        let (cmdsRhs, expr) ← translateExpr senv val
        let rhsTemp ← freshTemp
        pure (cmdsLhs ++ [.computeAddr addrTemp lhsExpr] ++ cmdsRhs ++
          [.move rhsTemp expr, .store (.temp addrTemp) (.temp rhsTemp)])

  | .ifLit test thenBranch elseBranch =>
    let fallsThrough (cmds : List Command) : Bool :=
      match cmds.getLast? with
      | some (.ret _) => false
      | _ => true
    let (cmdsTest, transTest) ← translateExpr senv test
    let cmdsThen ← translateStm senv ensures thenBranch
    let cmdsElse ← translateStm senv ensures elseBranch
    let labelThen ← freshLabel
    let labelElse ← freshLabel
    let labelDone ← freshLabel
    let thenFalls := fallsThrough cmdsThen
    let elseFalls := fallsThrough cmdsElse
    pure (cmdsTest
      ++ [.ite transTest labelThen labelElse, .label labelThen]
      ++ cmdsThen
      ++ (if thenFalls then [.goto labelDone] else [])
      ++ [.label labelElse]
      ++ cmdsElse
      ++ (if elseFalls then [.goto labelDone] else [])
      ++ (if thenFalls || elseFalls then [.label labelDone] else []))

  | .whileLit test body =>
    -- Loop invariants (present with --dyn-check) are checked before every
    -- evaluation of the condition, including the one that exits the loop.
    let mut cmdsInvs := []
    for inv in body.peelInvariants.1 do
      let (cmds, transInv) ← translateExpr senv inv
      cmdsInvs := cmdsInvs ++ cmds ++ [.runtimeCall .assert [transInv]]
    let (cmdsTest, transTest) ← translateExpr senv test
    let cmdsBody ← translateStm senv ensures body.peelInvariants.2
    let labelGuard ← freshLabelNamed "cond"
    let labelBody ← freshLabelNamed "body"
    let labelDone ← freshLabelNamed "end"
    pure ([.goto labelGuard, .label labelGuard]
      ++ cmdsInvs
      ++ cmdsTest
      ++ [.ite transTest labelBody labelDone, .label labelBody]
      ++ cmdsBody
      ++ [.goto labelGuard, .label labelDone])

  | .ret valOpt =>
    match valOpt with
    | some retVal =>
      let (cmdsRetVal, transRetVal) ← translateExpr senv retVal
      let resultTemp ← freshTemp
      modify fun st => { st with env := st.env.insert resultTempName resultTemp }
      let cmdsEnsures ← translateContract senv false ensures
      modify fun st => { st with env := st.env.erase resultTempName }
      pure (cmdsRetVal
        ++ [.declare resultTemp (translateTau retVal.tau), .move resultTemp transRetVal]
        ++ cmdsEnsures ++ [.ret (some (.temp resultTemp))])
    | none =>
      let cmdsEnsures ← translateContract senv false ensures
      pure (cmdsEnsures ++ [.ret none])

  | .seq first rest =>
    let cmdsFirst ← translateStm senv ensures first
    let cmdsRest ← translateStm senv ensures rest
    pure (cmdsFirst ++ cmdsRest)

  | .declare varName tau init value =>
    let temp ← freshTemp
    let cmdsInit ← match init with
      | some initExpr =>
          let (cmds, transInit) ← translateExpr senv initExpr
          pure ([Tree.Command.declare temp (translateTau tau)] ++ cmds ++ [Tree.Command.move temp transInit])
      | none =>
          pure [Tree.Command.declare temp (translateTau tau), Tree.Command.move temp (defaultValOfTau tau)]
    modify fun st => { st with env := st.env.insert varName temp }
    let cmdsValue ← translateStm senv ensures value
    modify fun st => { st with env := st.env.erase varName }
    pure (cmdsInit ++ cmdsValue)

  | .expr e =>
    let (cmds, expr) ← translateExpr senv e
    if exprAlreadyMaterialized expr then
      pure cmds
    else
      pure (cmds ++ [Tree.Command.move (← freshTemp) expr])

  | .nop => pure []

  | .assert test =>
    let (cmds, transTest) ← translateExpr senv test
    pure (cmds ++ [.runtimeCall .assert [transTest]])

  | .error e =>
    let (cmds, _) ← translateExpr senv e
    pure (cmds ++ [.runtimeCall .error []])

  | .annotation a =>
    let (cmds, transTest) ← match a with
      | .requires _ => panic! "[Error] requires annotation found in function body"
      | .ensures _ => panic! "[Error] ensures annotation found in function body"
      | .asserts e | .loopInvariant e => translateExpr senv e
    pure (cmds ++ [.runtimeCall .assert [transTest]])
termination_by sizeOf mstm
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := C0VC.TypedAst.Stm.sizeOf_peelInvariants_le body; omega)

def translateParam (param : C0VC.TypedAst.Param) : Tree.Arg :=
  let (tau, name) := param

  -- Only used for external declarations, whose parameter names are not emitted.
  (translateTau tau, Temp.fromName name)

def endsWithRet : List Tree.Command → Bool
  | [] => false
  | cmds =>
      match cmds.getLast! with
      | .ret _ => true
      | _ => false

def isVoidTau : C0VC.TypedAst.Tau → Bool
  | .void => true
  | _ => false

def translateFunctionDef (fdefn : C0VC.TypedAst.FunctionDef) : Tree.FunctionDef :=
  let senv := collectSEnv fdefn.structs
  let structs := fdefn.structs.map (fun (name, fields) => (name, fields.map (fun (tau, fieldName) => (translateTau tau, fieldName))))
  if fdefn.external then
    { fname := fdefn.fname
    , tau := translateTau fdefn.retType
    , args := fdefn.params.map translateParam
    , commands := []
    , structs := structs
    , external := true }
  else
  let params := fdefn.params
  let (temps, tc) := Temp.bumpAndCreateK 0 params.length
  let paramsTemps := List.zip params temps
  let (params', seededEnv) := List.foldr
    (λ ((tau, varName), temp) (paramsAcc, envAcc) => ((translateTau tau, temp)::paramsAcc, envAcc.insert varName temp))
    ([], {})
    paramsTemps

  let body : TransM (List Tree.Command) := do
    let pre ← translateContract senv true fdefn.annotations
    let mut cmds := pre
    for mstm in fdefn.body do
      cmds := cmds ++ (← translateStm senv fdefn.annotations mstm)
    -- A void function may fall off its end, which also checks @ensures.
    if isVoidTau fdefn.retType && !(endsWithRet cmds) then
      cmds := cmds ++ (← translateContract senv false fdefn.annotations)
    pure cmds
  let cmds := (body.run' { env := seededEnv, tc, lc := 0 })
  { fname := fdefn.fname
  , tau := translateTau fdefn.retType
  , args := params'
  , commands := cmds
  , structs := structs
  , external := false }

def run (program : C0VC.TypedAst.Program) : Tree.Program :=
  List.map translateFunctionDef program

end C0VC.LLVM.Tree.Trans
