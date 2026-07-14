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

instance : Inhabited C0VC.TypedAst.TypedExpr where
  default := { node := .intLit 0, tau := .int }

-- TODO: consider wrapping env meta things into here / change to StateM
structure Env where
  tempEnv : TempEnv
  tc : TempCounter
  lc : LabelCounter

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

  -- TODO
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


def translateBinOp (op: C0VC.TypedAst.BinOp) : Tree.BinOp :=
  match op with
  | .plus => .plus
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .mod => .mod
  | .lt => .lt
  | .lte => .lte
  | .gt => .gt
  | .gte => .gte
  | .eq => .eq
  | .neq => .neq
  | .bitAnd => .bitAnd
  | .xor => .xor
  | .bitOr => .bitOr
  | .shl => .shl
  | .shr => .shr

def tauOfBinOp : C0VC.TypedAst.BinOp → Tree.Tau
  | .lt
  | .lte
  | .gt
  | .gte
  | .eq
  | .neq => .bool
  | _ => .int

def exprAlreadyMaterialized : Tree.Expr → Bool
  | .const .. | .temp _ => true
  | _ => false

partial def translateExpr
  (senv : SEnv)
  (texpr : C0VC.TypedAst.TypedExpr)
  (env : Std.HashMap String Temp)
  (tc : TempCounter)
  (lc : LabelCounter)
  : List Tree.Command × Tree.Expr × TempEnv × TempCounter × LabelCounter :=
  match texpr.node with
  | .var name =>
    match env.get? name with
    | some temp => ([], .temp temp, env, tc, lc)
    | _ =>
      let (temp, tc') := Temp.bumpAndCreate tc
      ([], .temp temp, env.insert name temp, tc', lc)

  | .intLit val => ([], .const .int (Int32.ofInt val), env, tc, lc)

  | .binop op lhs rhs =>
    let (tempRes, tc') := Temp.bumpAndCreate tc
    let (cmdsLhs, transLhs, env', tc'', lc') := translateExpr senv lhs env tc' lc
    let (cmdsRhs, transRhs, env'', tc''', lc'') := translateExpr senv rhs env' tc'' lc'
    let cmd :=

      -- in C0, division/modulus by zero is not undefined behavior and instead always
      -- raises a runtime exception.

      -- TODO: Currently, we call a wrapper for div/mod ops
      -- but to save a function call, we may not want to do this.
      -- benchmark LLVM's inliner opt to see if this gets inlined otherwise, we should
      -- not call this wrapper for all div/mod ops
      match op with
      | .div => .move tempRes (.runtimeCall .checkedDiv [transLhs, transRhs])
      | .mod => .move tempRes (.runtimeCall .checkedMod [transLhs, transRhs])
      | .shl => .move tempRes (.runtimeCall .checkedShl [transLhs, transRhs])
      | .shr => .move tempRes (.runtimeCall .checkedShr [transLhs, transRhs])

      -- Assumes that binops input types are equal
      | _ => .move tempRes (.binop (translateBinOp op) (translateTau lhs.tau) transLhs transRhs)

    (cmdsLhs ++ cmdsRhs ++ [cmd]
    , .temp tempRes
    , env''
    , tc'''
    , lc'')

  -- TODO: LLVM supports select. is this really something we want to elaborate?
  | .ternary test thenVal elseVal =>
    let (tempRes, tc') := Temp.bumpAndCreate tc
    let (cmdsTest, transTest, env', tc'', lc') := translateExpr senv test env tc' lc
    let (labelThen, lc'') := Label.bumpAndCreate lc'
    let (labelElse, lc''') := Label.bumpAndCreate lc''

    let (cmdsThen, transThen, env'', tc''', lc''') := translateExpr senv thenVal env' tc'' lc'''
    let (cmdsElse, transElse, env''', tc'''', lc'''') := translateExpr senv elseVal env'' tc''' lc'''
    let (labelDone, lc''''') := Label.bumpAndCreate lc''''

    ([.declare tempRes (translateTau texpr.tau)]
    ++ cmdsTest
    ++ [.ite transTest labelThen labelElse]
    ++ [.label labelThen]
    ++ cmdsThen
    ++ [.move tempRes transThen]
    ++ [.goto labelDone]
    ++ [.label labelElse]
    ++ cmdsElse
    ++ [.move tempRes transElse]
    ++ [.goto labelDone]
    ++ [.label labelDone]

    , .temp tempRes
    , env'''
    , tc''''
    , lc'''''
    )

  | .trueLit => ([], .const .bool 1, env, tc, lc)
  | .falseLit => ([], .const .bool 0, env, tc, lc)

  -- TODO: fix this. definitely not the correct handling of chars
  | .charLit c => ([], .const .int (Int32.ofNat c.toNat), env, tc, lc)

  | .call fname args =>
    let (argCmds, argExps, env', tc', lc') := List.foldr
      (λ arg (cmdsAcc, expsAcc, envAcc, tcAcc, lcAcc) =>
        let (cmds, exp, env'', tc''', lc'') := translateExpr senv arg envAcc tcAcc lcAcc
        (cmds ++ cmdsAcc, exp :: expsAcc, env'', tc''', lc'')
      )
      ([], [], env, tc, lc)
      args
    match texpr.tau with
    | .void => (argCmds ++ [.call fname argExps], .const .void 0, env', tc', lc')
    | _ =>
      let (tempRes, tc'') := Temp.bumpAndCreate tc'
      (argCmds ++ [.move tempRes (.call fname argExps)], .temp tempRes, env', tc'', lc')

  -- TODO
  | .length _ => ([], .const .int 0, env, tc, lc)
  | .result =>
    match env.get? resultTempName with
    | some temp => ([], .temp temp, env, tc, lc)
    -- TODO: catch this error earlier?
    | none => panic! "[Error] \\result found outside postcondition"
  | .hastag => ([], .const .int 0, env, tc, lc)
  | .stringLit _ => ([], .const .int 0, env, tc, lc)
  | .null => ([], .null, env, tc, lc)
  | .alloc tau => ([], .alloc (translateTau tau), env, tc, lc)
  | .allocArray tau size =>
      let (cmdsSize, transSize, env', tc', lc') := translateExpr senv size env tc lc
      (cmdsSize, .allocArray (translateTau tau) transSize, env', tc', lc')
  | .deref ptr =>
      let (cmdsPtr, transPtr, env', tc', lc') := translateExpr senv ptr env tc lc
      let (temp, tc'') := Temp.bumpAndCreate tc'
      let expr := .deref transPtr (translateTau texpr.tau)
      (cmdsPtr ++ [.move temp expr], .temp temp, env', tc'', lc')
  | .arrAccess arr index =>
      let (cmdsArr, transArr, env', tc', lc') := translateExpr senv arr env tc lc
      let (cmdsIndex, transIndex, env'', tc'', lc'') := translateExpr senv index env' tc' lc'
      let (temp, tc''') := Temp.bumpAndCreate tc''
      let expr := .arrAccess transArr transIndex (translateTau texpr.tau)
      (cmdsArr ++ cmdsIndex ++ [.move temp expr], .temp temp, env'', tc''', lc'')
  | .dot struct field =>
      let (cmdsStruct, transStruct, env', tc', lc') := translateExpr senv struct env tc lc
      match struct.tau with
      | .struct structName =>
          let (temp, tc'') := Temp.bumpAndCreate tc'
          let expr := .dot transStruct structName (lookupFieldIndex senv structName field) (translateTau texpr.tau)
          (cmdsStruct ++ [.move temp expr], .temp temp, env', tc'', lc')
      | _ => panic! "[Error] dot expected struct type"
  | .arrow structPtr field =>
      let (cmdsStructPtr, transStructPtr, env', tc', lc') := translateExpr senv structPtr env tc lc
      match structPtr.tau with
      | .ptr (.struct structName) =>
          let (temp, tc'') := Temp.bumpAndCreate tc'
          let expr := .arrow transStructPtr structName (lookupFieldIndex senv structName field) (translateTau texpr.tau)
          (cmdsStructPtr ++ [.move temp expr], .temp temp, env', tc'', lc')
      | _ => panic! "[Error] arrow expected pointer-to-struct type"

partial def typedLValueToExpr (tlv : C0VC.TypedAst.TypedLValue) : C0VC.TypedAst.TypedExpr :=
  let node :=
    match tlv.node with
    | .var name => .var name
    | .deref ptr => .deref (typedLValueToExpr ptr)
    | .dot struct field => .dot (typedLValueToExpr struct) field
    | .arrow structPtr field => .arrow (typedLValueToExpr structPtr) field
    | .arrAccess arr index => .arrAccess (typedLValueToExpr arr) index
  { node := node, tau := tlv.tau }

partial def translateLValueExpr
  (senv : SEnv)
  (tlv : C0VC.TypedAst.TypedLValue)
  (env : Std.HashMap String Temp)
  (tc : TempCounter)
  (lc : LabelCounter)
  : List Tree.Command × Tree.Expr × TempEnv × TempCounter × LabelCounter :=
  match tlv.node with
  | .var name =>
    match env.get? name with
    | some temp => ([], .temp temp, env, tc, lc)
    | none =>
      let (temp, tc') := Temp.bumpAndCreate tc
      ([], .temp temp, env.insert name temp, tc', lc)

  -- lvalues and its side effects are computed first before doing rhs.
  | .deref ptr =>
      let (cmdsPtr, transPtr, env', tc', lc') := translateExpr senv (typedLValueToExpr ptr) env tc lc
      (cmdsPtr, .deref transPtr (translateTau tlv.tau), env', tc', lc')
  | .arrAccess arr index =>
      let (cmdsArr, transArr, env', tc', lc') := translateExpr senv (typedLValueToExpr arr) env tc lc
      let (cmdsIndex, transIndex, env'', tc'', lc'') := translateExpr senv index env' tc' lc'
      (cmdsArr ++ cmdsIndex, .arrAccess transArr transIndex (translateTau tlv.tau), env'', tc'', lc'')
  | .dot struct field =>
      let (cmdsStruct, transStruct, env', tc', lc') := translateLValueExpr senv struct env tc lc
      match struct.tau with
      | .struct structName =>
          (cmdsStruct, .dot transStruct structName (lookupFieldIndex senv structName field) (translateTau tlv.tau), env', tc', lc')
      | _ => panic! "[Error] dot lvalue expected struct type"
  | .arrow structPtr field =>
      let (cmdsStructPtr, transStructPtr, env', tc', lc') := translateLValueExpr senv structPtr env tc lc
      match structPtr.tau with
  | .ptr (.struct structName) =>
          (cmdsStructPtr, .arrow transStructPtr structName (lookupFieldIndex senv structName field) (translateTau tlv.tau), env', tc', lc')
      | _ => panic! "[Error] arrow lvalue expected pointer-to-struct type"

def translatePreconditions
  (senv : SEnv)
  (annotations : List C0VC.TypedAst.Anno)
  (env : Std.HashMap String Temp)
  (tc : TempCounter)
  (lc : LabelCounter)
  : List Tree.Command × TempEnv × TempCounter × LabelCounter :=
  annotations.foldl
    (fun (cmdsAcc, envAcc, tcAcc, lcAcc) anno =>
      match anno with
      | .requires pre =>
          let (cmds, transTest, env', tc', lc') := translateExpr senv pre envAcc tcAcc lcAcc
          (cmdsAcc ++ cmds ++ [.runtimeCall .assert [transTest]], env', tc', lc')
      | .ensures _ =>
          (cmdsAcc, envAcc, tcAcc, lcAcc)
      | .asserts _ =>
          panic! "[Error] asserts annotation found in function contract position"
      | .loopInvariant _ =>
          panic! "[Error] loop invariant annotation found in function contract position")
    ([], env, tc, lc)

def translatePostconditions
  (senv : SEnv)
  (annotations : List C0VC.TypedAst.Anno)
  (env : Std.HashMap String Temp)
  (tc : TempCounter)
  (lc : LabelCounter)
  : List Tree.Command × TempEnv × TempCounter × LabelCounter :=
  annotations.foldl
    (fun (cmdsAcc, envAcc, tcAcc, lcAcc) anno =>
      match anno with
      | .requires _ =>
          (cmdsAcc, envAcc, tcAcc, lcAcc)
      | .ensures post =>
          let (cmds, transTest, env', tc', lc') := translateExpr senv post envAcc tcAcc lcAcc
          (cmdsAcc ++ cmds ++ [.runtimeCall .assert [transTest]], env', tc', lc')
      | .asserts _ =>
          panic! "[Error] asserts annotation found in function contract position"
      | .loopInvariant _ =>
          panic! "[Error] loop invariant annotation found in function contract position")
    ([], env, tc, lc)

partial def translateStm
  (senv : SEnv)
  (ensures : List C0VC.TypedAst.Anno)
  (mstm : C0VC.TypedAst.Stm)
  (env : Std.HashMap String Temp)
  (tc : TempCounter)
  (lc : LabelCounter)
  : List Tree.Command × TempEnv × TempCounter × LabelCounter :=
  match mstm with
  | .assign lhs val =>
    match lhs.node with
    | .var varName =>
        let (cmds, expr, env', tc', lc') := translateExpr senv val env tc lc
        match env.get? varName with
        | some temp =>
          (cmds ++ [.move temp expr], env', tc', lc')
        | none =>
          let (temp, tc') := Temp.bumpAndCreate tc
          (cmds ++ [.move temp expr], env', tc', lc')
    | _ =>
        -- Evaluate lvalue subexpressions before the rhs, but delay the final
        -- destination check until the store. This preserves C0's exception
        -- order for cases like *p = 1 / 0 when p is NULL.
        let (cmdsLhs, lhsExpr, env', tc', lc') := translateLValueExpr senv lhs env tc lc
        let (cmdsRhs, expr, env'', tc'', lc'') := translateExpr senv val env' tc' lc'
        let (rhsTemp, tc''') := Temp.bumpAndCreate tc''
        (cmdsLhs ++ cmdsRhs ++ [.move rhsTemp expr, .store lhsExpr (.temp rhsTemp)], env'', tc''', lc'')

  | .ifLit test thenBranch elseBranch =>
    let emitLabel (cmds : List Command) :=
      match List.getLast? cmds with
      | some last =>
        match last with
        | .ret _ => false
        | _ => true
      | _ => true

    let (cmdsTest, transTest, env', tc', lc') := translateExpr senv test env tc lc
    let (cmdsThen, env'', tc'', lc'') := translateStm senv ensures thenBranch env' tc' lc'
    let (cmdsElse, env''', tc''', lc''') := translateStm senv ensures elseBranch env'' tc'' lc''

    let (labelThen, lc'''') := Label.bumpAndCreate lc'''
    let emitLabelThen := emitLabel cmdsThen
    let (labelElse, lc''''') := Label.bumpAndCreate lc''''
    let emitLabelElse := emitLabel cmdsElse
    let (labelDone, lc'''''') := Label.bumpAndCreate lc'''''

    (cmdsTest
    ++ [.ite transTest labelThen labelElse]
    ++ [.label labelThen]
    ++ cmdsThen
    ++ (if emitLabelThen then [.goto labelDone] else [])
    ++ [.label labelElse]
    ++ cmdsElse
    ++ (if emitLabelElse then [.goto labelDone] else [])
    ++ (if (emitLabelThen || emitLabelElse) then [.label labelDone] else [])
    , env'''
    , tc'''
    , lc''''''
    )

  | .whileLit test body =>
    let (cmdsTest, transTest, env', tc', lc') := translateExpr senv test env tc lc
    let (cmdsBody, env'', tc'', lc'') := translateStm senv ensures body env' tc' lc'

    let (labelGuard, lc''') := Label.bumpAndCreateNamed lc'' "cond"
    let (labelBody, lc'''') := Label.bumpAndCreateNamed lc''' "body"
    let (labelDone, lc''''') := Label.bumpAndCreateNamed lc'''' "end"

    ([ .goto labelGuard
     , .label labelGuard]
    ++ cmdsTest
    ++ [ .ite transTest labelBody labelDone
       , .label labelBody]
    ++ cmdsBody
    ++ [ .goto labelGuard
       , .label labelDone]
    , env''
    , tc''
    , lc''''')

  | .ret valOpt =>
    match valOpt with
    | some retVal =>
      let (cmdsRetVal, transRetVal, env', tc', lc') := translateExpr senv retVal env tc lc
      let (resultTemp, tc'') := Temp.bumpAndCreate tc'
      let envWithResult := env'.insert resultTempName resultTemp
      let resultSetup := [.declare resultTemp (translateTau retVal.tau), .move resultTemp transRetVal]
      let (cmdsEnsures, env'', tc''', lc'') := translatePostconditions senv ensures envWithResult tc'' lc'
      (cmdsRetVal ++ resultSetup ++ cmdsEnsures ++ [.ret (some (.temp resultTemp))], env''.erase resultTempName, tc''', lc'')
    | none =>
      let (cmdsEnsures, env', tc', lc') := translatePostconditions senv ensures env tc lc
      (cmdsEnsures ++ [.ret none], env', tc', lc')

  | .seq first rest =>
    let (cmdsFirst, env', tc', lc') := translateStm senv ensures first env tc lc
    let (cmdsRest, env'', tc'', lc'') := translateStm senv ensures rest env' tc' lc'

    (cmdsFirst ++ cmdsRest
    , env''
    , tc''
    , lc'')

  | .declare varName tau init value =>
    let (temp, tc') := Temp.bumpAndCreate tc
    let defaultVal := defaultValOfTau tau
    let (cmdsInit, tc'', lc'', envAfterInit) :=
      match init with
      | some initExpr =>
          let (cmds, transInit, env', tc'', lc'') := translateExpr senv initExpr env tc' lc
          ([Tree.Command.declare temp (translateTau tau)] ++ cmds ++ [Tree.Command.move temp transInit], tc'', lc'', env')
      | none =>
          ([Tree.Command.declare temp (translateTau tau), Tree.Command.move temp defaultVal], tc', lc, env)
    let (cmdsValue, env', tc''', lc''') := translateStm senv ensures value (envAfterInit.insert varName temp) tc'' lc''
    (cmdsInit ++ cmdsValue, env'.erase varName, tc''', lc''')

  | .expr mexpr =>
    let (cmds, expr, env', tc', lc') := translateExpr senv mexpr env tc lc
    if exprAlreadyMaterialized expr then
      (cmds, env', tc', lc')
    else
      let (temp, tc'') := Temp.bumpAndCreate tc'
      (cmds ++ [Tree.Command.move temp expr], env', tc'', lc')

  | .nop => ([], env, tc, lc)

  -- TODO
  | .assert test =>
    let (cmds, transTest, env', tc', lc') := translateExpr senv test env tc lc

    ( cmds ++
      [ .runtimeCall .assert [transTest] ]
    , env'
    , tc'
    , lc')

  | .error _ => panic! "[Error] unimplemented (error)"

  | .annotation a =>
    let (cmds, transTest, env', tc', lc') :=
      match a with
      | .requires _ => panic! "[Error] requires annotation found in function body"
      | .ensures _ => panic! "[Error] ensures annotation found in function body"
      | .asserts e => translateExpr senv e env tc lc
      | .loopInvariant e => translateExpr senv e env tc lc
    ( cmds ++
      [ .runtimeCall .assert [transTest] ]
    , env'
    , tc'
    , lc')

def translateParam (param : C0VC.TypedAst.Param) : Tree.Arg :=
  let (tau, name) := param

  -- TODO: make this cleaner. why are we creating temp from name? seems dangerous
  (translateTau tau, Temp.fromName name)

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
    -- TODO: i don't really like this, since it assumes that in the downstream pass,
    -- function args will preserve temp.name and also explicitly emit %temp.name
    (λ ((tau, varName), temp) (paramsAcc, envAcc) => ((translateTau tau, temp)::paramsAcc, envAcc.insert varName temp))
    ([], {})
    paramsTemps

  let (cmdsPre, preEnv, preTc, preLc) := translatePreconditions senv fdefn.annotations seededEnv tc 0
  let (cmds, _, _, _) := (List.foldl
    (λ (cmdsAcc, envAcc, tcAcc, lcAcc) mstm =>
      let (cmds, env', tc', lc') := translateStm senv fdefn.annotations mstm envAcc tcAcc lcAcc
      (cmdsAcc ++ cmds, env', tc', lc')
    )
    (cmdsPre, preEnv, preTc, preLc)
    fdefn.body)
  { fname := fdefn.fname
  , tau := translateTau fdefn.retType
  , args := params'
  , commands := cmds
  , structs := structs
  , external := false }

def run (program : C0VC.TypedAst.Program) : Tree.Program :=
  List.map translateFunctionDef program

end C0VC.LLVM.Tree.Trans
