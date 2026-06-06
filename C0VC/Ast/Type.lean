import C0VC.Ast.ElabbedAst
import C0VC.Ast.TypedAst
import Std.Data.HashMap

open C0VC.ElabbedAst
open Std.HashMap

namespace C0VC.Typechecker

def tauEq : Tau → Tau → Bool
  | .int, .int => true
  | .char, .char => true
  | .string, .string => true
  | .bool, .bool => true
  | .void, .void => true
  | .struct lhs, .struct rhs => lhs == rhs
  | .ptr lhs, .ptr rhs => tauEq lhs rhs
  | .array lhs, .array rhs => tauEq lhs rhs
  | .null, .null => true
  | _, _ => false

def tauIsRef : Tau → Bool
  | .ptr _ | .array _ => true
  | _ => false

def tauAssignable (expected actual : Tau) : Bool :=
  tauEq expected actual || (tauIsRef expected && tauEq actual .null)

def coerceNullTo (expected : Tau) (expr : C0VC.TypedAst.TypedExpr) : C0VC.TypedAst.TypedExpr :=
  if tauEq expr.tau .null && tauIsRef expected then
    { expr with tau := expected }
  else
    expr

def tauComparable (lhs rhs : Tau) : Bool :=
  if tauEq lhs .void || tauEq rhs .void then
    false
  else
    tauEq lhs rhs || (tauEq lhs .null && tauIsRef rhs) || (tauEq rhs .null && tauIsRef lhs)

structure FnInfo where
  retType : Tau
  fname : String
  params : List Param

abbrev FEnv := Std.HashMap String FnInfo
abbrev SEnv := Std.HashMap String (List Field)

def collectFEnv (program : Program) : FEnv :=
  program.foldl
    (fun env gdecl =>
      match gdecl with
      | .fdecl retType fname params _ =>
          env.insert fname { retType, fname, params }
      | .fdefn fdefn =>
          env.insert fdefn.fname { retType := fdefn.retType, fname := fdefn.fname, params := fdefn.params }
      | .sdecl .. => env)
    {}

def collectSEnv (program : Program) : Except String SEnv :=
  program.foldlM
    (fun env gdecl => do
      match gdecl with
      | .sdecl name fields =>
          if env.contains name then
            .error s!"struct {name} declared more than once"
          else
            .ok (env.insert name fields)
      | _ => .ok env)
    {}

def collectStructs (program : Program) : List (String × List Field) :=
  program.filterMap (fun
    | .sdecl name fields => some (name, fields)
    | _ => none)

def collectFnDefNames (program : Program) : List String :=
  program.filterMap (fun
    | .fdefn fdefn => some fdefn.fname
    | _ => none)

def tcMainFn (program : Program) : Except String Unit := do
  let fnNames := collectFnDefNames program
  let mainFns := fnNames.filter (λ fname => fname == "main")
  let _ ← match List.length mainFns with
    | 0 => .error "Could not find a main function"
    | 1 => .ok ()
    | _ => .error "Found more than one main function"
  let fenv := collectFEnv program
  match fenv.get? "main" with
  | some info =>
    let _ ← if info.params.isEmpty then
      .ok ()
    else
      .error "main function must not take parameters"

    let _ ← if (tauEq info.retType .int) then
      .ok ()
    else
      .error "main function must return an int"

  | none => .error "Could not find a main function"

structure VarInfo where
  name : String
  varType : Tau
  initialized : Bool

abbrev VEnv := Std.HashMap String VarInfo

def insertVEnv (venv : VEnv) (name : String) (varType : Tau) (initialized : Bool) : VEnv :=
  venv.insert name { name := name, varType := varType, initialized := initialized }

def markVEnvInitialized (venv : VEnv) (name : String) : Except String VEnv :=
  match venv.get? name with
  | some info => .ok (venv.insert name { info with initialized := true })
  | none => .error s!"variable {name} used before decl"

def tcVarDeclared (venv : VEnv) (name : String) : Except String VarInfo :=
  match venv.get? name with
  | some info => .ok info
  | none => .error s!"variable {name} used before decl"

def tcVarReadable (venv : VEnv) (name : String) : Except String VarInfo :=
  match venv.get? name with
  | some info =>
    if info.initialized then
      .ok info
    else
      .error s!"variable {name} used before initialized"
  | none => .error s!"Used {name} before defined"

def mergeVEnvAfterBranches (before thenEnv elseEnv : VEnv) : VEnv :=
  before.toList.foldl
    (fun env (name, info) =>
      match thenEnv.get? name, elseEnv.get? name with
      | some thenInfo, some elseInfo =>
          env.insert name { info with initialized := info.initialized || (thenInfo.initialized && elseInfo.initialized) }
      | _, _ => env)
    before

def initializeAllVEnv (venv : VEnv) : VEnv :=
  venv.toList.foldl
    (fun env (name, info) => env.insert name { info with initialized := true })
    venv

def minInt32 : Int := -2147483648

def maxInt32 : Int := -1 * minInt32

def intLitInRange (n : Int) : Bool :=
  minInt32 <= n && n <= maxInt32

def tcIntLitRange (n : Int) : Except String Unit :=
  if intLitInRange n then
    .ok ()
  else
    .error s!"integer literal {n} is outside int range"


-- TODO: this func, and many others (?) are duplicated across the Ast modules, let's deduplicate`
def ppTau : Tau → String
  | .int => "int"
  | .char => "char"
  | .string => "string"
  | .bool => "bool"
  | .void => "void"
  | .struct name => s!"struct {name}"
  | .ptr tau => s!"{ppTau tau}*"
  | .array tau => s!"{ppTau tau}[]"
  | .null => "null"

def binopType : BinOp → Tau
  | .plus
  | .sub
  | .mul
  | .div
  | .mod
  | .bitAnd
  | .xor
  | .bitOr
  | .shl
  | .shr => .int
  | .lt
  | .lte
  | .gt
  | .gte
  | .eq
  | .neq => .bool

def binopArgTypesOk (op : BinOp) (lhs rhs : Tau) : Bool :=
  match op with
  | .plus
  | .sub
  | .mul
  | .div
  | .mod
  | .lt
  | .lte
  | .gt
  | .gte
  | .bitAnd
  | .xor
  | .bitOr
  | .shl
  | .shr => tauEq lhs .int && tauEq rhs .int
  | .eq
  | .neq => tauComparable lhs rhs

def mkTExpr (node : C0VC.TypedAst.Expr) (tau : Tau) : C0VC.TypedAst.TypedExpr :=
  { node := node, tau := tau }

def lookupStructFields (senv : SEnv) (name : String) : Except String (List Field) :=
  match senv.get? name with
  | some fields => .ok fields
  | none => .error s!"struct {name} used before declaration"

def lookupField (senv : SEnv) (structName fieldName : String) : Except String Tau := do
  let fields ← lookupStructFields senv structName
  match fields.find? (fun (_, name) => name == fieldName) with
  | some (tau, _) => .ok tau
  | none => .error s!"struct {structName} has no field {fieldName}"

def tcAllocType (tau : Tau) : Except String Unit := do
  if tauEq tau .void then
    .error "cannot allocate a value of type void"
  else if tauEq tau .null then
    .error "cannot allocate a value of type null"
  else
    .ok ()

mutual
partial def tcExpr (senv : SEnv) (fenv : FEnv) (resultType : Option Tau) (mexpr : MarkedExpr) (venv : VEnv) :
    Except String C0VC.TypedAst.TypedExpr := do
  match mexpr.node with
  | .var name =>
    let info ← tcVarReadable venv name
    .ok (mkTExpr (.var name) info.varType)
  | .intLit n =>
    let _ ← tcIntLitRange n
    .ok (mkTExpr (.intLit n) .int)
  | .trueLit =>
    .ok (mkTExpr .trueLit .bool)
  | .falseLit =>
    .ok (mkTExpr .falseLit .bool)
  | .null =>
    .ok (mkTExpr .null .null)
  | .charLit c =>
    .ok (mkTExpr (.charLit c) .char)
  | .stringLit s =>
    .ok (mkTExpr (.stringLit s) .string)
  | .binop op lhs rhs =>
    let tlhs ← tcExpr senv fenv resultType lhs venv
    let trhs ← tcExpr senv fenv resultType rhs venv
    if binopArgTypesOk op tlhs.tau trhs.tau then
      .ok (mkTExpr (.binop op tlhs trhs) (binopType op))
    else
      .error "binary operator arguments have invalid types"
  | .ternary test thenVal elseVal =>
    let ttest ← tcExpr senv fenv resultType test venv
    if not (tauEq ttest.tau .bool) then
      .error "ternary condition must have type Tau.bool"
    let tthen ← tcExpr senv fenv resultType thenVal venv
    let telse ← tcExpr senv fenv resultType elseVal venv
    if tauEq tthen.tau telse.tau then
      .ok (mkTExpr (.ternary ttest tthen telse) tthen.tau)
    else if tauEq tthen.tau .null && tauIsRef telse.tau then
      .ok (mkTExpr (.ternary ttest (coerceNullTo telse.tau tthen) telse) telse.tau)
    else if tauEq telse.tau .null && tauIsRef tthen.tau then
      .ok (mkTExpr (.ternary ttest tthen (coerceNullTo tthen.tau telse)) tthen.tau)
    else
      .error "ternary branches have different types"
  | .call fname args =>
    if venv.contains fname then
      .error s!"cannot call {fname}: name refers to a local variable"
    else
      match fenv.get? fname with
      | none => .error s!"function {fname} used before decl"
      | some info =>
        let targs ← tcCallArgs senv fenv resultType fname args info.params venv
        .ok (mkTExpr (.call fname targs) info.retType)
  | .length arrayLike =>
    let tarrayLike ← tcExpr senv fenv resultType arrayLike venv
    match tarrayLike.tau with
    | .array _ => .ok (mkTExpr (.length tarrayLike) .int)
    | _ => .error "\\length argument must have array type"
  | .result =>
    match resultType with
    | some tau => .ok (mkTExpr .result tau)
    | none => .error "Cannot infer type for annotation-only expression"
  | .hastag =>
    .ok (mkTExpr .hastag .bool)
  | .dot struct field =>
    let tstruct ← tcExpr senv fenv resultType struct venv
    match tstruct.tau with
    | .struct name =>
      let fieldTau ← lookupField senv name field
      .ok (mkTExpr (.dot tstruct field) fieldTau)
    | _ => .error "left side of field access must have struct type"
  | .arrow structPtr field =>
    let tstructPtr ← tcExpr senv fenv resultType structPtr venv
    match tstructPtr.tau with
    | .ptr (.struct name) =>
      let fieldTau ← lookupField senv name field
      .ok (mkTExpr (.arrow tstructPtr field) fieldTau)
    | _ => .error "left side of arrow access must have pointer-to-struct type"
  | .alloc type =>
    let _ ← tcAllocType type
    .ok (mkTExpr (.alloc type) (.ptr type))
  | .allocArray type size =>
    let _ ← tcAllocType type
    let tsize ← tcExpr senv fenv resultType size venv
    if tauEq tsize.tau .int then
      .ok (mkTExpr (.allocArray type tsize) (.array type))
    else
      .error "alloc_array size must have type int"
  | .deref ptr =>
    let tptr ← tcExpr senv fenv resultType ptr venv
    match tptr.tau with
    | .ptr tau => .ok (mkTExpr (.deref tptr) tau)
    | _ => .error "dereference operand must have pointer type"
  | .arrAccess arr index =>
    let tarr ← tcExpr senv fenv resultType arr venv
    let tindex ← tcExpr senv fenv resultType index venv
    if not (tauEq tindex.tau .int) then
      .error "array index must have type int"
    match tarr.tau with
    | .array tau => .ok (mkTExpr (.arrAccess tarr tindex) tau)
    | _ => .error "array access operand must have array type"

partial def tcCallArgs (senv : SEnv) (fenv : FEnv) (resultType : Option Tau) (fname : String)
    (args : List MarkedExpr) (params : List Param) (venv : VEnv) :
    Except String (List C0VC.TypedAst.TypedExpr) := do
  match args, params with
  | [], [] => .ok []
  | arg :: restArgs, (expected, _) :: restParams =>
    let targ ← tcExpr senv fenv resultType arg venv
    if tauAssignable expected targ.tau then
      let trest ← tcCallArgs senv fenv resultType fname restArgs restParams venv
      .ok (coerceNullTo expected targ :: trest)
    else
      .error s!"argument to {fname} must have type {ppTau expected}"
  | _, _ => .error s!"function {fname} called with wrong number of arguments"
end

def tcExprHasType (senv : SEnv) (fenv : FEnv) (resultType : Option Tau) (mexpr : MarkedExpr) (venv : VEnv)
    (expected : Tau) (ctx : String) : Except String C0VC.TypedAst.TypedExpr := do
  let actual ← tcExpr senv fenv resultType mexpr venv
  if tauAssignable expected actual.tau then
    .ok (coerceNullTo expected actual)
  else
    .error s!"{ctx} must have type {ppTau expected}"

partial def tcAnno (senv : SEnv) (fenv : FEnv) (resultType : Option Tau) (anno : MarkedAnno) (venv : VEnv) :
    Except String C0VC.TypedAst.Anno := do
  match anno.node with
  | .requires e =>
    let te ← tcExpr senv fenv resultType e venv
    .ok (.requires te)
  | .ensures e =>
    let te ← tcExpr senv fenv resultType e venv
    .ok (.ensures te)
  | .asserts e =>
    let te ← tcExpr senv fenv resultType e venv
    .ok (.asserts te)
  | .loopInvariant e =>
    let te ← tcExpr senv fenv resultType e venv
    .ok (.loopInvariant te)

partial def tcMStm (senv : SEnv) (fenv : FEnv) (expectedRet : Tau) (mstm : MarkedStm) (venv : VEnv) :
    Except String (C0VC.TypedAst.Stm × VEnv) := do
  match mstm.node with
  | .assign varName val =>
    let varInfo ← tcVarDeclared venv varName
    let tval ← tcExpr senv fenv none val venv
    if tauAssignable varInfo.varType tval.tau then
      let venv' ← markVEnvInitialized venv varName
      .ok (.assign varName (coerceNullTo varInfo.varType tval), venv')
    else
      .error s!"assigning to {varName} an expression of different type"

  | .ifLit test thenBranch elseBranch =>
    let ttest ← tcExprHasType senv fenv none test venv .bool "if condition"
    let (tthen, thenEnv) ← tcMStm senv fenv expectedRet thenBranch venv
    let (telse, elseEnv) ← tcMStm senv fenv expectedRet elseBranch venv
    .ok (.ifLit ttest tthen telse, mergeVEnvAfterBranches venv thenEnv elseEnv)

  | .whileLit test body step =>
    match step.node with
    | .declare .. => .error "found a declaration in the step of a for loop"
    | _ =>
      let ttest ← tcExprHasType senv fenv none test venv .bool "while condition"
      let (tbody, bodyEnv) ← tcMStm senv fenv expectedRet body venv
      let (tstep, _) ← tcMStm senv fenv expectedRet step bodyEnv
      let tbodyWithStep :=
        match tstep with
        | .nop => tbody
        | _ => .seq tbody tstep
      .ok (.whileLit ttest tbodyWithStep, venv)

  | .declare varName varType init body =>
    if venv.contains varName then
      .error s!"variable {varName} declared more than once"
    if tauEq varType .void then
      .error s!"cannot have a value of type void"
    let (tinit, venvForBody) ←
      match init with
      | some initVal =>
        let tinit ← tcExpr senv fenv none initVal venv
        if not (tauAssignable varType tinit.tau) then
          .error s!"assigning to {varName} an expression of different type"
        .ok (some (coerceNullTo varType tinit), insertVEnv venv varName varType true)
      | none =>
        .ok (none, insertVEnv venv varName varType false)
    let (tbody, venvAfter) ← tcMStm senv fenv expectedRet body venvForBody
    .ok (.declare varName varType tinit tbody, venvAfter.erase varName)

  | .ret valOpt =>
    match valOpt with
    | some val =>
      let tval ← tcExpr senv fenv none val venv
      if tauEq tval.tau .void then
        .error "cannot return a void type as a value of a return statement"
      else if tauAssignable expectedRet tval.tau then
        .ok (.ret (some (coerceNullTo expectedRet tval)), initializeAllVEnv venv)
      else
        .error "return type does not match function return type"
    | none =>
      if tauEq expectedRet .void then
        .ok (.ret none, initializeAllVEnv venv)
      else
        .error "return type does not match function return type"

  | .seq first rest =>
    let (tfirst, venv') ← tcMStm senv fenv expectedRet first venv
    let (trest, venv'') ← tcMStm senv fenv expectedRet rest venv'
    .ok (.seq tfirst trest, venv'')

  | .expr e =>
    let te ← tcExpr senv fenv none e venv
    match e.node with
    | .ternary .. =>
      if tauEq te.tau .void then .error "ternary exp as stm cannot have void types"
      else .ok (.expr te, venv)
    | _ =>
      .ok (.expr te, venv)

  | .assert test =>
    let ttest ← tcExprHasType senv fenv none test venv .bool "assert condition"
    .ok (.assert ttest, venv)

  | .error e =>
    let te ← tcExpr senv fenv none e venv
    .ok (.error te, venv)

  | .nop =>
    .ok (.nop, venv)

  | .annotation a =>
    let ta ← tcAnno senv fenv (some expectedRet) a venv
    .ok (.annotation ta, venv)

partial def typedStmtGuaranteedReturn (mstm : C0VC.TypedAst.Stm) : Bool :=
  match mstm with
  | .ret _ => true
  | .seq first rest => typedStmtGuaranteedReturn first || typedStmtGuaranteedReturn rest
  | .ifLit _ thenBranch elseBranch =>
    typedStmtGuaranteedReturn thenBranch && typedStmtGuaranteedReturn elseBranch
  | .declare _ _ _ value => typedStmtGuaranteedReturn value
  | _ => false

def typedBodyGuaranteedReturn (body : List C0VC.TypedAst.Stm) : Bool :=
  body.any typedStmtGuaranteedReturn

partial def collectReturnedValueOptsFromStmt (tstm : C0VC.TypedAst.Stm) :
    List (Option C0VC.TypedAst.TypedExpr) :=
  match tstm with
  | .ret valOpt => [valOpt]
  | .seq first rest =>
    collectReturnedValueOptsFromStmt first ++ collectReturnedValueOptsFromStmt rest
  | .ifLit _ thenBranch elseBranch =>
    collectReturnedValueOptsFromStmt thenBranch ++ collectReturnedValueOptsFromStmt elseBranch
  | .whileLit _ body => collectReturnedValueOptsFromStmt body
  | .declare _ _ _ value => collectReturnedValueOptsFromStmt value
  | _ => []

def collectReturnedValueOpts (tbody : List C0VC.TypedAst.Stm) :
    List (Option C0VC.TypedAst.TypedExpr) :=
  tbody.foldr (fun tstm acc => collectReturnedValueOptsFromStmt tstm ++ acc) []

def returnedValueOptHasType (expectedRet : Tau) : Option C0VC.TypedAst.TypedExpr → Bool
  | some val => tauAssignable expectedRet val.tau
  | none => tauEq expectedRet .void

def tcReturnedValuesHaveType (expectedRet : Tau) (tbody : List C0VC.TypedAst.Stm) :
    Except String Unit :=
  if (collectReturnedValueOpts tbody).all (returnedValueOptHasType expectedRet) then
    .ok ()
  else
    .error "return type does not match function return type"

def tcFunctionDef (structs : List (String × List Field)) (senv : SEnv) (fenv : FEnv) (fdefn : FunctionDef) : Except String C0VC.TypedAst.FunctionDef := do
  let venv ← fdefn.params.foldlM
    (fun env (varType, name) =>
      if env.contains name then
        .error s!"variable {name} declared more than once"
      else
        .ok (insertVEnv env name varType true))
    {}
  let (tbodyRev, _) ← fdefn.body.foldlM
    (fun (acc, venv) mstm => do
      let (tmstm, venv') ← tcMStm senv fenv fdefn.retType mstm venv
      .ok (tmstm :: acc, venv'))
    ([], venv)
  let tannotations ← fdefn.annotations.mapM (fun mstm => do
    let (tmstm, _) ← tcMStm senv fenv fdefn.retType mstm venv
    .ok tmstm)
  let tbody := tbodyRev.reverse
  let _ ← tcReturnedValuesHaveType fdefn.retType tbody
  if typedBodyGuaranteedReturn tbody || tauEq fdefn.retType .void then
    .ok { retType := fdefn.retType, fname := fdefn.fname, params := fdefn.params, body := tbody, annotations := tannotations, structs := structs, external := false }
  else
    .error "Could not find a return statement in function definition"

def tcGDecl (structs : List (String × List Field)) (senv : SEnv) (fenv : FEnv) : GDecl → Except String (Option C0VC.TypedAst.FunctionDef)
  | .fdecl retType fname params external =>
      if external then
        .ok (some { retType, fname, params, body := [], annotations := [], structs := structs, external := true })
      else
        .ok none
  | .fdefn fdefn => do
      let tfdefn ← tcFunctionDef structs senv fenv fdefn
      .ok (some tfdefn)
  | .sdecl .. =>
      .ok none

def tc (program : Program) : Except String C0VC.TypedAst.Program := do
  let _ ← tcMainFn program
  let senv ← collectSEnv program
  let structs := collectStructs program
  let fenv := collectFEnv program
  let typed ← program.mapM (tcGDecl structs senv fenv)
  .ok (typed.filterMap id)

end C0VC.Typechecker
