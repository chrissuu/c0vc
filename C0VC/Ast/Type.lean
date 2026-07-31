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
  | .ptr _ => true
  | _ => false

def tauIsSmall : Tau → Bool
  | .int | .char | .bool => true
  | .ptr _ | .array _ | .null => true
  | .void | .string | .struct _ => false

def tauIsReturnable : Tau → Bool
  | .void => true
  | tau => tauIsSmall tau

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
  else if not (tauIsSmall lhs) || not (tauIsSmall rhs) then
    false
  else
    tauEq lhs rhs
    || (tauEq lhs .null && tauIsRef rhs)
    || (tauEq rhs .null && tauIsRef lhs)

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
      | .sdecl .. | .sdefn .. => env)
    {}

def collectSEnv (program : Program) : Except String SEnv :=
  program.foldlM
    (fun env gdecl => do
      match gdecl with
      | .sdecl _ =>
          .ok env
      | .sdefn name fields =>
          if env.contains name then
            .error s!"struct {name} declared more than once"
          else
            .ok (env.insert name fields)
      | _ => .ok env)
    {}

def collectStructs (program : Program) : List (String × List Field) :=
  program.filterMap (fun
    | .sdefn name fields => some (name, fields)
    | _ => none)

def valueStructDeps : Tau → List String
  | .struct name => [name]
  | .ptr _ => []
  | .array _ => []
  | _ => []

partial def checkStructAcyclicFrom (senv : SEnv) (stack : List String) (name : String) :
    Except String Unit := do
  if stack.contains name then
    .error s!"cyclic struct definition involving struct {name}"
  else
    match senv.get? name with
    | none => .error s!"struct {name} used before declaration"
    | some fields =>
        let stack' := name :: stack
        fields.forM (fun (tau, _) =>
          (valueStructDeps tau).forM (fun dep => checkStructAcyclicFrom senv stack' dep))

def checkStructsAcyclic (senv : SEnv) : Except String Unit := do
  senv.toList.forM (fun (name, _) => checkStructAcyclicFrom senv [] name)

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

instance : Inhabited C0VC.TypedAst.TypedExpr where
  default := { node := .intLit 0, tau := .int }

instance : Inhabited C0VC.TypedAst.TypedLValue where
  default := { node := .var "$c0vc_default", tau := .int }

instance : Inhabited C0VC.TypedAst.Stm where
  default := .nop

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

partial def tauContainsVoidOrString : Tau → Bool
  | .void | .string => true
  | .ptr tau | .array tau => tauContainsVoidOrString tau
  | _ => false

def tcValueTypeValid (tau : Tau) (ctx : String) : Except String Unit :=
  if tauContainsVoidOrString tau then
    .error s!"{ctx} cannot contain void or string"
  else if tauEq tau .null then
    .error s!"{ctx} cannot have null type"
  else
    .ok ()

def tcReturnTypeValid (tau : Tau) : Except String Unit :=
  match tau with
  | .void => .ok ()
  | _ => tcValueTypeValid tau "function return type"

def tauNeedsStructSize : Tau → Option String
  | .struct name => some name
  | _ => none

def tcStructSizeKnown (senv : SEnv) (tau : Tau) (ctx : String) : Except String Unit :=
  match tauNeedsStructSize tau with
  | some name =>
      if senv.contains name then
        .ok ()
      else
        .error s!"{ctx} needs definition of struct {name}"
  | none => .ok ()

def tcStructFieldTypeKnown (senv : SEnv) (tau : Tau) : Except String Unit :=
  tcStructSizeKnown senv tau "struct field"

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

def mkTLValue (node : C0VC.TypedAst.LValue) (tau : Tau) : C0VC.TypedAst.TypedLValue :=
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

def tcAllocType (senv : SEnv) (tau : Tau) (ctx : String) : Except String Unit := do
  let _ ← tcValueTypeValid tau ctx
  tcStructSizeKnown senv tau ctx

def tcSmallType (tau : Tau) (ctx : String) : Except String Unit :=
  if tauIsSmall tau then
    .ok ()
  else
    .error s!"{ctx} must have small type"

def tcReturnType (tau : Tau) : Except String Unit :=
  if tauIsReturnable tau then
    .ok ()
  else
    .error "function return type must be small"

def tcParamTypesSmall (params : List Param) : Except String Unit :=
  params.forM (fun (tau, _) => do
    let _ ← tcValueTypeValid tau "function parameter"
    tcSmallType tau "function parameter")

def tcFunctionSignature (retType : Tau) (params : List Param) : Except String Unit := do
  let _ ← tcReturnTypeValid retType
  let _ ← tcReturnType retType
  tcParamTypesSmall params

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
      let _ ← tcSmallType tthen.tau "ternary expression"
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
    match resultType with
    | none =>
        .error "\\length can only be used in contracts"
    | some _ =>
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
    let _ ← tcAllocType senv type "alloc type"
    .ok (mkTExpr (.alloc type) (.ptr type))
  | .allocArray type size =>
    let _ ← tcAllocType senv type "alloc_array element type"
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

partial def tcLValue (senv : SEnv) (fenv : FEnv) (resultType : Option Tau) (mlv : MarkedLValue) (venv : VEnv) :
    Except String C0VC.TypedAst.TypedLValue := do
  match mlv.node with
  | .var name =>
    let info ← tcVarReadable venv name
    .ok (mkTLValue (.var name) info.varType)
  | .deref ptr =>
    let tptr ← tcLValue senv fenv resultType ptr venv
    match tptr.tau with
    | .ptr tau => .ok (mkTLValue (.deref tptr) tau)
    | _ => .error "dereference lvalue operand must have pointer type"
  | .dot struct field =>
    let tstruct ← tcLValue senv fenv resultType struct venv
    match tstruct.tau with
    | .struct name =>
        let fieldTau ← lookupField senv name field
        .ok (mkTLValue (.dot tstruct field) fieldTau)
    | _ => .error "left side of field lvalue access must have struct type"
  | .arrow structPtr field =>
    let tstructPtr ← tcLValue senv fenv resultType structPtr venv
    match tstructPtr.tau with
    | .ptr (.struct name) =>
        let fieldTau ← lookupField senv name field
        .ok (mkTLValue (.arrow tstructPtr field) fieldTau)
    | _ => .error "left side of arrow lvalue access must have pointer-to-struct type"
  | .arrAccess arr index =>
    let tarr ← tcLValue senv fenv resultType arr venv
    let tindex ← tcExpr senv fenv resultType index venv
    if not (tauEq tindex.tau .int) then
      .error "array index must have type int"
    match tarr.tau with
    | .array tau => .ok (mkTLValue (.arrAccess tarr tindex) tau)
    | _ => .error "array lvalue access operand must have array type"

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

partial def typedLValueToExpr (tlv : C0VC.TypedAst.TypedLValue) : C0VC.TypedAst.TypedExpr :=
  let node :=
    match tlv.node with
    | .var name => .var name
    | .deref ptr => .deref (typedLValueToExpr ptr)
    | .dot struct field => .dot (typedLValueToExpr struct) field
    | .arrow structPtr field => .arrow (typedLValueToExpr structPtr) field
    | .arrAccess arr index => .arrAccess (typedLValueToExpr arr) index
  { node := node, tau := tlv.tau }

def assignOpToBinOp : AssignOp → Option BinOp
  | .assign => none
  | .plusEq => some .plus
  | .subEq => some .sub
  | .mulEq => some .mul
  | .divEq => some .div
  | .modEq => some .mod
  | .bitAndEq => some .bitAnd
  | .xorEq => some .xor
  | .bitOrEq => some .bitOr
  | .shlEq => some .shl
  | .shrEq => some .shr

partial def materializeAsopLValue (next : Nat) (tlv : C0VC.TypedAst.TypedLValue) :
    Nat × (C0VC.TypedAst.Stm → C0VC.TypedAst.Stm) × C0VC.TypedAst.TypedLValue :=
  match tlv.node with
  | .var _ =>
    (next, id, tlv)
  | .deref ptr =>
    let (next', wrap, ptr') := materializeAsopLValue next ptr
    (next', wrap, { tlv with node := .deref ptr' })
  | .dot struct field =>
    let (next', wrap, struct') := materializeAsopLValue next struct
    (next', wrap, { tlv with node := .dot struct' field })
  | .arrow structPtr field =>
    let (next', wrap, structPtr') := materializeAsopLValue next structPtr
    (next', wrap, { tlv with node := .arrow structPtr' field })
  | .arrAccess arr index =>
    let (next', wrapArr, arr') := materializeAsopLValue next arr
    let baseName := s!"$c0vc_asop_base_{next'}"
    let indexName := s!"$c0vc_asop_idx_{next' + 1}"
    let baseExpr := typedLValueToExpr arr'
    let baseLValue := mkTLValue (.var baseName) arr.tau
    let indexExpr := mkTExpr (.var indexName) .int
    let tlv' := { tlv with node := .arrAccess baseLValue indexExpr }
    let wrap : C0VC.TypedAst.Stm → C0VC.TypedAst.Stm := fun body =>
      wrapArr (.declare baseName arr.tau (some baseExpr) (.declare indexName .int (some index) body))
    (next' + 2, wrap, tlv')

partial def tcMStm (senv : SEnv) (fenv : FEnv) (expectedRet : Tau) (mstm : MarkedStm) (venv : VEnv) :
    Except String (C0VC.TypedAst.Stm × VEnv) := do
  match mstm.node with
  | .assign lhs val =>
    match lhs.node with
    | .var varName =>
      let varInfo ← tcVarDeclared venv varName
      let _ ← tcSmallType varInfo.varType "assignment target"
      let tval ← tcExpr senv fenv none val venv
      let _ ← tcSmallType tval.tau "assigned expression"
      if tauAssignable varInfo.varType tval.tau then
        let venv' ← markVEnvInitialized venv varName
        .ok (.assign (mkTLValue (.var varName) varInfo.varType) (coerceNullTo varInfo.varType tval), venv')
      else
        .error s!"assigning to {varName} an expression of different type"
    | _ =>
      let tlhs ← tcLValue senv fenv none lhs venv
      let _ ← tcSmallType tlhs.tau "assignment target"
      let tval ← tcExpr senv fenv none val venv
      let _ ← tcSmallType tval.tau "assigned expression"
      if tauAssignable tlhs.tau tval.tau then
        .ok (.assign tlhs (coerceNullTo tlhs.tau tval), venv)
      else
        .error s!"assigning expression of type {ppTau tval.tau} to lvalue of type {ppTau tlhs.tau}"

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
    let _ ← tcValueTypeValid varType "local variable"
    if tauEq varType .void then
      .error s!"cannot have a value of type void"
    let _ ← tcSmallType varType "local variable"
    let (tinit, venvForBody) ←
      match init with
      | some initVal =>
        let tinit ← tcExpr senv fenv none initVal venv
        let _ ← tcSmallType tinit.tau "initializer"
        if not (tauAssignable varType tinit.tau) then
          .error s!"assigning to {varName} an expression of different type"
        .ok (some (coerceNullTo varType tinit), insertVEnv venv varName varType true)
      | none =>
        .ok (none, insertVEnv venv varName varType false)
    let (tbody, venvAfter) ← tcMStm senv fenv expectedRet body venvForBody
    .ok (.declare varName varType tinit tbody, venvAfter.erase varName)

  | .asop lhs op value =>
    match assignOpToBinOp op with
    | none =>
      tcMStm senv fenv expectedRet { node := .assign lhs value, span := mstm.span } venv
    | some binop =>
      let tlhs ← tcLValue senv fenv none lhs venv
      let _ ← tcSmallType tlhs.tau "assignment target"
      let tvalue ← tcExpr senv fenv none value venv
      let _ ← tcSmallType tvalue.tau "assigned expression"
      let (_, wrap, tlhs') := materializeAsopLValue 0 tlhs
      let lhsExpr := typedLValueToExpr tlhs'
      if not (binopArgTypesOk binop lhsExpr.tau tvalue.tau) then
        .error "compound assignment arguments have invalid types"
      let rhsTau := binopType binop
      if not (tauAssignable tlhs'.tau rhsTau) then
        .error s!"assigning expression of type {ppTau rhsTau} to lvalue of type {ppTau tlhs'.tau}"
      let rhs := mkTExpr (.binop binop lhsExpr tvalue) rhsTau
      .ok (wrap (.assign tlhs' rhs), venv)

  | .ret valOpt =>
    match valOpt with
    | some val =>
      let tval ← tcExpr senv fenv none val venv
      if tauEq tval.tau .void then
        .error "cannot return a void type as a value of a return statement"
      else if not (tauIsSmall tval.tau) then
        .error "return value must have small type"
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
    if not (tauEq te.tau .void) then
      let _ ← tcSmallType te.tau "expression statement"
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
  let _ ← tcFunctionSignature fdefn.retType fdefn.params
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
  let tannotations ← fdefn.annotations.mapM (fun anno =>
    tcAnno senv fenv (some fdefn.retType) anno venv)
  let tbody := tbodyRev.reverse
  let _ ← tcReturnedValuesHaveType fdefn.retType tbody
  if typedBodyGuaranteedReturn tbody || tauEq fdefn.retType .void then
    .ok { retType := fdefn.retType, fname := fdefn.fname, params := fdefn.params, body := tbody, annotations := tannotations, structs := structs, external := false }
  else
    .error "Could not find a return statement in function definition"

def tcGDecl (structs : List (String × List Field)) (senv : SEnv) (fenv : FEnv) : GDecl → Except String (Option C0VC.TypedAst.FunctionDef)
  | .fdecl retType fname params external => do
      let _ ← tcFunctionSignature retType params
      if external then
        .ok (some { retType, fname, params, body := [], annotations := [], structs := structs, external := true })
      else
        .ok none
  | .fdefn fdefn => do
      let tfdefn ← tcFunctionDef structs senv fenv fdefn
      .ok (some tfdefn)
  | .sdecl .. | .sdefn .. =>
      .ok none

def tcStructDeclFields (visibleSenv : SEnv) (name : String) (fields : List Field) : Except String Unit :=
  fields.forM (fun (tau, fieldName) => do
    let _ ← tcValueTypeValid tau s!"field {fieldName} of struct {name}"
    tcStructFieldTypeKnown visibleSenv tau)

def tcProgramOrdered
    (structs : List (String × List Field))
    (fenv : FEnv)
    (program : Program) : Except String C0VC.TypedAst.Program := do
  let (typedRev, _) ← program.foldlM
    (fun (typedAcc, visibleSenv) gdecl => do
      match gdecl with
      | .sdecl _ =>
          .ok (typedAcc, visibleSenv)
      | .sdefn name fields =>
          let _ ← tcStructDeclFields visibleSenv name fields
          .ok (typedAcc, visibleSenv.insert name fields)
      | .fdecl .. | .fdefn .. =>
          let typed? ← tcGDecl structs visibleSenv fenv gdecl
          match typed? with
          | some typed => .ok (typed :: typedAcc, visibleSenv)
          | none => .ok (typedAcc, visibleSenv))
    ([], {})
  .ok typedRev.reverse

def run (program : Program) : Except String C0VC.TypedAst.Program := do
  let _ ← tcMainFn program
  let senv ← collectSEnv program
  let _ ← checkStructsAcyclic senv
  let structs := collectStructs program
  let fenv := collectFEnv program
  tcProgramOrdered structs fenv program

end C0VC.Typechecker
