import C0VC.Ast.ElabbedAst
import C0VC.Ast.TypedAst
import Std.Data.HashMap

open C0VC.ElabbedAst
open Std.HashMap

namespace C0VC.Typechecker

def tauEq (lhs rhs : Tau) : Bool := lhs == rhs

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
      | .fdecl retType fname params _ _ =>
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
  | none => .error s!"variable {name} is not declared"

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


def ppTau : Tau → String := Print.ppTau

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

/-- Where an expression occurs, which decides the contract-only forms it may use. -/
inductive ExprCtx where
  /-- Code: no contract-only forms. -/
  | code
  /-- `@requires`, `@loop_invariant` and `@assert`: `\length` but not `\result`. -/
  | contract
  /-- `@ensures` of a function returning `ret`: `\length` and `\result`. -/
  | postcondition (ret : Tau)
deriving Inhabited

/-- Prefix an error message with a source location, unless it already has one. -/
def locateError (span? : Option C0VC.Utils.SrcSpan.SrcSpan) (msg : String) : String :=
  match span? with
  | some span =>
      if msg.startsWith s!"{span.fileName}:" then msg
      else s!"{span.fileName}:{span.startLoc.line}:{span.startLoc.col}: {msg}"
  | none => msg

mutual
partial def tcExpr (senv : SEnv) (fenv : FEnv) (ctx : ExprCtx) (mexpr : MarkedExpr) (venv : VEnv) :
    Except String C0VC.TypedAst.TypedExpr :=
  match tcExprCore senv fenv ctx mexpr venv with
  | .ok te => .ok { te with span := mexpr.span <|> te.span }
  | .error msg => .error (locateError mexpr.span msg)

partial def tcExprCore (senv : SEnv) (fenv : FEnv) (ctx : ExprCtx) (mexpr : MarkedExpr) (venv : VEnv) :
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
    let tlhs ← tcExpr senv fenv ctx lhs venv
    let trhs ← tcExpr senv fenv ctx rhs venv
    if binopArgTypesOk op tlhs.tau trhs.tau then
      .ok (mkTExpr (.binop op tlhs trhs) (binopType op))
    else
      .error "binary operator arguments have invalid types"

  | .ternary test thenVal elseVal =>
    let ttest ← tcExpr senv fenv ctx test venv
    if not (tauEq ttest.tau .bool) then
      .error "ternary condition must have type bool"
    let tthen ← tcExpr senv fenv ctx thenVal venv
    let telse ← tcExpr senv fenv ctx elseVal venv
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
        let targs ← tcCallArgs senv fenv ctx fname args info.params venv
        .ok (mkTExpr (.call fname targs) info.retType)

  | .length arrayLike =>
    match ctx with
    | .code =>
        .error "\\length can only be used in contracts"
    | _ =>
        let tarrayLike ← tcExpr senv fenv ctx arrayLike venv
        match tarrayLike.tau with
        | .array _ => .ok (mkTExpr (.length tarrayLike) .int)
        | _ => .error "\\length argument must have array type"
  | .result =>
    match ctx with
    | .postcondition .void => .error "\\result cannot be used in a function that returns void"
    | .postcondition tau => .ok (mkTExpr .result tau)
    | _ => .error "\\result can only be used in @ensures"

  | .hastag =>
    .error "\\hastag is not supported"
  | .dot struct field =>
    let tstruct ← tcExpr senv fenv ctx struct venv
    match tstruct.tau with
    | .struct name =>
      let fieldTau ← lookupField senv name field
      .ok (mkTExpr (.dot tstruct field) fieldTau)
    | _ => .error "left side of field access must have struct type"
  | .arrow structPtr field =>
    let tstructPtr ← tcExpr senv fenv ctx structPtr venv
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
    let tsize ← tcExpr senv fenv ctx size venv
    if tauEq tsize.tau .int then
      .ok (mkTExpr (.allocArray type tsize) (.array type))
    else
      .error "alloc_array size must have type int"
  | .deref ptr =>
    let tptr ← tcExpr senv fenv ctx ptr venv
    match tptr.tau with
    | .ptr tau => .ok (mkTExpr (.deref tptr) tau)
    | _ => .error "dereference operand must have pointer type"
  | .arrAccess arr index =>
    let tarr ← tcExpr senv fenv ctx arr venv
    let tindex ← tcExpr senv fenv ctx index venv
    if not (tauEq tindex.tau .int) then
      .error "array index must have type int"
    match tarr.tau with
    | .array tau => .ok (mkTExpr (.arrAccess tarr tindex) tau)
    | _ => .error "array access operand must have array type"

partial def tcLValue (senv : SEnv) (fenv : FEnv) (ctx : ExprCtx) (mlv : MarkedLValue) (venv : VEnv) :
    Except String C0VC.TypedAst.TypedLValue :=
  match tcLValueCore senv fenv ctx mlv venv with
  | .ok tlv => .ok { tlv with span := mlv.span <|> tlv.span }
  | .error msg => .error (locateError mlv.span msg)

partial def tcLValueCore (senv : SEnv) (fenv : FEnv) (ctx : ExprCtx) (mlv : MarkedLValue) (venv : VEnv) :
    Except String C0VC.TypedAst.TypedLValue := do
  match mlv.node with
  | .var name =>
    let info ← tcVarReadable venv name
    .ok (mkTLValue (.var name) info.varType)
  | .deref ptr =>
    let tptr ← tcLValue senv fenv ctx ptr venv
    match tptr.tau with
    | .ptr tau => .ok (mkTLValue (.deref tptr) tau)
    | _ => .error "dereference lvalue operand must have pointer type"
  | .dot struct field =>
    let tstruct ← tcLValue senv fenv ctx struct venv
    match tstruct.tau with
    | .struct name =>
        let fieldTau ← lookupField senv name field
        .ok (mkTLValue (.dot tstruct field) fieldTau)
    | _ => .error "left side of field lvalue access must have struct type"
  | .arrow structPtr field =>
    let tstructPtr ← tcLValue senv fenv ctx structPtr venv
    match tstructPtr.tau with
    | .ptr (.struct name) =>
        let fieldTau ← lookupField senv name field
        .ok (mkTLValue (.arrow tstructPtr field) fieldTau)
    | _ => .error "left side of arrow lvalue access must have pointer-to-struct type"
  | .arrAccess arr index =>
    let tarr ← tcLValue senv fenv ctx arr venv
    let tindex ← tcExpr senv fenv ctx index venv
    if not (tauEq tindex.tau .int) then
      .error "array index must have type int"
    match tarr.tau with
    | .array tau => .ok (mkTLValue (.arrAccess tarr tindex) tau)
    | _ => .error "array lvalue access operand must have array type"

partial def tcCallArgs (senv : SEnv) (fenv : FEnv) (ctx : ExprCtx) (fname : String)
    (args : List MarkedExpr) (params : List Param) (venv : VEnv) :
    Except String (List C0VC.TypedAst.TypedExpr) := do
  match args, params with
  | [], [] => .ok []
  | arg :: restArgs, (expected, _) :: restParams =>
    let targ ← tcExpr senv fenv ctx arg venv
    if tauAssignable expected targ.tau then
      let trest ← tcCallArgs senv fenv ctx fname restArgs restParams venv
      .ok (coerceNullTo expected targ :: trest)
    else
      .error s!"argument to {fname} must have type {ppTau expected}"
  | _, _ => .error s!"function {fname} called with wrong number of arguments"
end

def tcExprHasType (senv : SEnv) (fenv : FEnv) (ctx : ExprCtx) (mexpr : MarkedExpr) (venv : VEnv)
    (expected : Tau) (what : String) : Except String C0VC.TypedAst.TypedExpr := do
  let actual ← tcExpr senv fenv ctx mexpr venv
  if tauAssignable expected actual.tau then
    .ok (coerceNullTo expected actual)
  else
    .error s!"{what} must have type {ppTau expected}"

partial def tcAnno (senv : SEnv) (fenv : FEnv) (ret : Tau) (anno : MarkedAnno) (venv : VEnv) :
    Except String C0VC.TypedAst.Anno := do
  match anno.node with
  | .requires e => .ok (.requires (← tcExpr senv fenv .contract e venv))
  | .ensures e => .ok (.ensures (← tcExpr senv fenv (.postcondition ret) e venv))
  | .asserts e => .ok (.asserts (← tcExpr senv fenv .contract e venv))
  | .loopInvariant e => .ok (.loopInvariant (← tcExpr senv fenv .contract e venv))

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
    let baseExpr := arr'.toExpr
    let baseLValue := mkTLValue (.var baseName) arr.tau
    let indexExpr := mkTExpr (.var indexName) .int
    let tlv' := { tlv with node := .arrAccess baseLValue indexExpr }
    let wrap : C0VC.TypedAst.Stm → C0VC.TypedAst.Stm := fun body =>
      wrapArr (.declare baseName arr.tau (some baseExpr) (.declare indexName .int (some index) body))
    (next' + 2, wrap, tlv')

mutual
partial def tcMStm (senv : SEnv) (fenv : FEnv) (expectedRet : Tau) (mstm : MarkedStm) (venv : VEnv) :
    Except String (C0VC.TypedAst.Stm × VEnv) :=
  match tcMStmCore senv fenv expectedRet mstm venv with
  | .ok result => .ok result
  | .error msg => .error (locateError mstm.span msg)

partial def tcMStmCore (senv : SEnv) (fenv : FEnv) (expectedRet : Tau) (mstm : MarkedStm) (venv : VEnv) :
    Except String (C0VC.TypedAst.Stm × VEnv) := do
  match mstm.node with
  | .assign lhs val =>
    match lhs.node with
    | .var varName =>
      let varInfo ← tcVarDeclared venv varName
      let _ ← tcSmallType varInfo.varType "assignment target"
      let tval ← tcExpr senv fenv .code val venv
      let _ ← tcSmallType tval.tau "assigned expression"
      if tauAssignable varInfo.varType tval.tau then
        let venv' ← markVEnvInitialized venv varName
        .ok (.assign (mkTLValue (.var varName) varInfo.varType) (coerceNullTo varInfo.varType tval), venv')
      else
        .error s!"assigning to {varName} an expression of different type"
    | _ =>
      let tlhs ← tcLValue senv fenv .code lhs venv
      let _ ← tcSmallType tlhs.tau "assignment target"
      let tval ← tcExpr senv fenv .code val venv
      let _ ← tcSmallType tval.tau "assigned expression"
      if tauAssignable tlhs.tau tval.tau then
        .ok (.assign tlhs (coerceNullTo tlhs.tau tval), venv)
      else
        .error s!"assigning expression of type {ppTau tval.tau} to lvalue of type {ppTau tlhs.tau}"

  | .ifLit test thenBranch elseBranch =>
    let ttest ← tcExprHasType senv fenv .code test venv .bool "if condition"
    let (tthen, thenEnv) ← tcMStm senv fenv expectedRet thenBranch venv
    let (telse, elseEnv) ← tcMStm senv fenv expectedRet elseBranch venv
    .ok (.ifLit ttest tthen telse, mergeVEnvAfterBranches venv thenEnv elseEnv)

  | .whileLit test body =>
    let ttest ← tcExprHasType senv fenv .code test venv .bool "while condition"
    let (tbody, _) ← tcMStm senv fenv expectedRet body venv
    .ok (.whileLit ttest tbody, venv)

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
        let tinit ← tcExpr senv fenv .code initVal venv
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
      let tlhs ← tcLValue senv fenv .code lhs venv
      let _ ← tcSmallType tlhs.tau "assignment target"
      let tvalue ← tcExpr senv fenv .code value venv
      let _ ← tcSmallType tvalue.tau "assigned expression"
      let (_, wrap, tlhs') := materializeAsopLValue 0 tlhs
      let lhsExpr := tlhs'.toExpr
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
      let tval ← tcExpr senv fenv .code val venv
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
    let te ← tcExpr senv fenv .code e venv
    if not (tauEq te.tau .void) then
      let _ ← tcSmallType te.tau "expression statement"
    match e.node with
    | .ternary .. =>
      if tauEq te.tau .void then .error "ternary exp as stm cannot have void types"
      else .ok (.expr te, venv)
    | _ =>
      .ok (.expr te, venv)

  | .assert test =>
    let ttest ← tcExprHasType senv fenv .code test venv .bool "assert condition"
    .ok (.assert ttest, venv)

  | .error e =>
    let te ← tcExpr senv fenv .code e venv
    .ok (.error te, venv)

  | .nop =>
    .ok (.nop, venv)

  | .annotation a =>
    let ta ← tcAnno senv fenv expectedRet a venv
    .ok (.annotation ta, venv)

end

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
    tcAnno senv fenv fdefn.retType anno venv)
  let tbody := tbodyRev.reverse
  let _ ← tcReturnedValuesHaveType fdefn.retType tbody
  if typedBodyGuaranteedReturn tbody || tauEq fdefn.retType .void then
    .ok { retType := fdefn.retType, fname := fdefn.fname, params := fdefn.params, body := tbody, annotations := tannotations, structs := structs, external := false }
  else
    .error "Could not find a return statement in function definition"

def tcGDecl (structs : List (String × List Field)) (senv : SEnv) (fenv : FEnv) : GDecl → Except String (Option C0VC.TypedAst.FunctionDef)
  | .fdecl retType fname params external annotations => do
      let _ ← tcFunctionSignature retType params
      if external then
        let venv := params.foldl (fun env (varType, name) => insertVEnv env name varType true) {}
        let tannotations ← annotations.mapM (fun anno => tcAnno senv fenv retType anno venv)
        .ok (some { retType, fname, params, body := [], annotations := tannotations, structs := structs, external := true })
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

partial def renameExprVars (σ : List (String × String)) (e : C0VC.TypedAst.TypedExpr) : C0VC.TypedAst.TypedExpr :=
  let r := renameExprVars σ
  let node : C0VC.TypedAst.Expr :=
    match e.node with
    | .var name => .var ((σ.lookup name).getD name)
    | .binop op l rhs => .binop op (r l) (r rhs)
    | .ternary c t f => .ternary (r c) (r t) (r f)
    | .call fname args => .call fname (args.map r)
    | .length a => .length (r a)
    | .dot a field => .dot (r a) field
    | .arrow a field => .arrow (r a) field
    | .allocArray tau n => .allocArray tau (r n)
    | .deref a => .deref (r a)
    | .arrAccess a i => .arrAccess (r a) (r i)
    | other => other
  { e with node }

def renameAnnoVars (σ : List (String × String)) : C0VC.TypedAst.Anno → C0VC.TypedAst.Anno
  | .requires e => .requires (renameExprVars σ e)
  | .ensures e => .ensures (renameExprVars σ e)
  | .asserts e => .asserts (renameExprVars σ e)
  | .loopInvariant e => .loopInvariant (renameExprVars σ e)

/--
Merge prototypes into their definitions. C0 checks the contracts of every
declaration of a function, so a prototype's annotations are added to the
definition. Functions that are only declared (header functions) keep a single
external entry carrying the annotations of all of their declarations.
-/
def mergeDeclarations (program : C0VC.TypedAst.Program) : C0VC.TypedAst.Program :=
  -- The parameter names that each function's annotations are rewritten to:
  -- the definition's if there is one, otherwise the first declaration's.
  let canonical : Std.HashMap String (List String) :=
    program.foldl
      (fun acc f =>
        if !f.external then acc.insert f.fname (f.params.map (·.2))
        else if acc.contains f.fname then acc
        else acc.insert f.fname (f.params.map (·.2)))
      {}
  let declAnnos : Std.HashMap String (List C0VC.TypedAst.Anno) :=
    program.foldl
      (fun acc f =>
        if f.external then
          let σ := (f.params.map (·.2)).zip (canonical.getD f.fname [])
          acc.insert f.fname ((acc.getD f.fname []) ++ f.annotations.map (renameAnnoVars σ))
        else acc)
      {}
  let defined : Std.HashSet String :=
    program.foldl (fun acc f => if f.external then acc else acc.insert f.fname) {}
  let (keptRev, _) := program.foldl
    (fun (acc, seen) (f : C0VC.TypedAst.FunctionDef) =>
      if f.external then
        if defined.contains f.fname || seen.contains f.fname then (acc, seen)
        else ({ f with annotations := declAnnos.getD f.fname [] } :: acc, seen.insert f.fname)
      else
        ({ f with annotations := declAnnos.getD f.fname [] ++ f.annotations } :: acc, seen.insert f.fname))
    (([] : List C0VC.TypedAst.FunctionDef), ({} : Std.HashSet String))
  keptRev.reverse

/--
"The body of a function may not assign to any variable that occurs in an
@ensures clause" (C0 reference, section 13.1). Checked after prototypes are
merged, so the contracts of every declaration are covered.
-/
def tcEnsuresNotAssigned (f : C0VC.TypedAst.FunctionDef) : Except String Unit := do
  let assigned := f.body.flatMap C0VC.TypedAst.Stm.assignedVars
  for anno in f.annotations do
    match anno with
    | .ensures e =>
        match e.vars.find? assigned.contains with
        | some name =>
            throw (locateError e.span
              s!"{f.fname} assigns {name}, which occurs in an @ensures clause; C0 does not allow assigning to variables in a postcondition")
        | none => pure ()
    | _ => pure ()

/--
Annotations inside a function body must be `@assert`s, or `@loop_invariant`s
directly after a loop header.
-/
partial def tcAnnotationPlacement : C0VC.TypedAst.Stm → Except String Unit
  | .annotation (.requires e) => .error (locateError e.span "@requires can only annotate a function")
  | .annotation (.ensures e) => .error (locateError e.span "@ensures can only annotate a function")
  | .annotation (.loopInvariant e) =>
      .error (locateError e.span "@loop_invariant must directly follow a loop header, as in `while (c) //@loop_invariant I; { ... }`")
  | .whileLit _ body => tcAnnotationPlacement body.peelInvariants.2
  | .ifLit _ t f => do tcAnnotationPlacement t; tcAnnotationPlacement f
  | .seq a b => do tcAnnotationPlacement a; tcAnnotationPlacement b
  | .declare _ _ _ body => tcAnnotationPlacement body
  | _ => .ok ()

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
  let merged := mergeDeclarations typedRev.reverse
  merged.forM tcEnsuresNotAssigned
  merged.forM fun f => f.body.forM tcAnnotationPlacement
  .ok merged

def run (program : Program) (requireMain : Bool := true) : Except String C0VC.TypedAst.Program := do
  if requireMain then
    tcMainFn program
  let senv ← collectSEnv program
  let _ ← checkStructsAcyclic senv
  let structs := collectStructs program
  let fenv := collectFEnv program
  tcProgramOrdered structs fenv program

end C0VC.Typechecker
