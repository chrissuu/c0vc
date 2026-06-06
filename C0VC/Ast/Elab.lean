/-
Elaboration

Desugars the any syntactic sugar of C0 and makes some conveniences as to
allow for better proof automation by Boole and relevant backends.

Currently, the following are elaborated:
1. Assignment ops
2. Unary ops (!, ~, -)
3. For loops
4. Typedefs
5. &&, || operators

Depending on whether we want to allow a "do-faithful-translation" functionality,
we may want to have a flag that turns the elaborator on and off.

Since typechecker (mostly) works on the elaborated AST, we can still resume
typechecking on the elaborated AST, but lowering to Boole happens on the original
AST.

The elaborator also resolves typedefs that may have been defined throughout
the source file.

Author: Chris Su <chrjs@cmu.edu>
-/

import C0VC.Ast.ParsedAst
import C0VC.Ast.Trans
import C0VC.Utils.SrcSpan
import Std.Data.HashMap

open C0VC.Ast
open C0VC.Utils.SrcSpan
open Std.HashMap

abbrev Env := Std.HashMap String Tau

namespace C0VC.Elab

structure FnInfo where
  retType : Tau
  paramTypes : List Tau
  defined : Bool
  external : Bool

abbrev FnEnv := Std.HashMap String FnInfo

partial def countUnopOfType (acc : Nat) (type : UnOp) (mexp : MarkedExpr) :=
  match mexp.node with
  | .unop type' mexp' => if type = type' then countUnopOfType (acc + 1) type mexp' else (acc, mexp)
  | _ => (acc, mexp)

def mkElabExpr (node : Expr) (span : Option SrcSpan) : MarkedExpr :=
  MarkedExpr.mk node span

instance : Inhabited MarkedExpr where
  default := mkElabExpr .trueLit none

def mkElabStm (node : Stm) (span : Option SrcSpan) : MarkedStm :=
  MarkedStm.mk node span

def mkElabAnno (node : Anno) (span : Option SrcSpan) : MarkedAnno :=
  MarkedAnno.mk node span

def mkElabLValue (node : LValue) (span : Option SrcSpan) : MarkedLValue :=
  MarkedLValue.mk node span

partial def resolveTypeName (env : Env) (seen : Std.HashSet String) : Tau → Except String Tau
  | .typeName name =>
      if seen.contains name then
        .error s!"cyclic typedef involving `{name}`"
      else
        match env.get? name with
        | some tau => resolveTypeName env (seen.insert name) tau
        | none => .error s!"unknown typedef `{name}`"
  | .ptr tau => do
      let tau' ← resolveTypeName env seen tau
      .ok (.ptr tau')
  | .array tau => do
      let tau' ← resolveTypeName env seen tau
      .ok (.array tau')
  | tau => .ok tau

def elabTypeName (env : Env) (tau : Tau) : Except String Tau :=
  resolveTypeName env {} tau

partial def elabMExpr (env : Env) (mexp : MarkedExpr) : Except String MarkedExpr := do
  match mexp.node with
  | .binop op lhs rhs =>
    match op with
    | .land =>
      let lhs' ← elabMExpr env lhs
      let rhs' ← elabMExpr env rhs
      .ok <| mkElabExpr (.ternary lhs' rhs' (mkElabExpr .falseLit mexp.span)) mexp.span
    | .lor =>
      let lhs' ← elabMExpr env lhs
      let rhs' ← elabMExpr env rhs
      .ok <| mkElabExpr (.ternary lhs' (mkElabExpr .trueLit mexp.span) rhs') mexp.span
    | _ =>
      let lhs' ← elabMExpr env lhs
      let rhs' ← elabMExpr env rhs
      .ok <| mkElabExpr (.binop op lhs' rhs') mexp.span
  | .unop op mexp' =>
    match op with
    | .bang =>
      let (numBangs, reducedMexp) := countUnopOfType 1 .bang mexp'
      let reducedMexp' ← elabMExpr env reducedMexp
      if numBangs % 2 = 0 then
        .ok <| mkElabExpr reducedMexp'.node mexp.span
      else
        .ok <| mkElabExpr
          (.ternary reducedMexp' (mkElabExpr .falseLit mexp.span) (mkElabExpr .trueLit mexp.span))
          mexp.span
    | .bitNot =>
      let (numBitNot, reducedMexp) := countUnopOfType 1 .bitNot mexp'
      let reducedMexp' ← elabMExpr env reducedMexp
      if numBitNot % 2 = 0 then
        .ok <| mkElabExpr reducedMexp'.node mexp.span
      else
        .ok <| mkElabExpr
          (.binop .xor reducedMexp' (mkElabExpr (.intLit (-1)) mexp.span))
          mexp.span
    | .negative =>
      match mexp'.node with
      | .intLit n => .ok <| mkElabExpr (.intLit (-n)) mexp.span
      | _ =>
        let mexp'' ← elabMExpr env mexp'
        .ok <| mkElabExpr (.binop .sub (mkElabExpr (.intLit 0) mexp.span) mexp'') mexp.span

  | .ternary test thenBranch elseBranch =>
    let test' ← elabMExpr env test
    let thenBranch' ← elabMExpr env thenBranch
    let elseBranch' ← elabMExpr env elseBranch
    .ok <| mkElabExpr (.ternary test' thenBranch' elseBranch') mexp.span
  | .call fname args =>
    let args' ← args.mapM (elabMExpr env)
    .ok <| mkElabExpr (.call fname args') mexp.span
  | .length arrayLike =>
    let arrayLike' ← elabMExpr env arrayLike
    .ok <| mkElabExpr (.length arrayLike') mexp.span
  | .dot struct field =>
    let struct' ← elabMExpr env struct
    .ok <| mkElabExpr (.dot struct' field) mexp.span
  | .arrow structPtr field =>
    let structPtr' ← elabMExpr env structPtr
    .ok <| mkElabExpr (.arrow structPtr' field) mexp.span
  | .alloc type =>
    let type' ← elabTypeName env type
    .ok <| mkElabExpr (.alloc type') mexp.span
  | .allocArray type size =>
    let type' ← elabTypeName env type
    let size' ← elabMExpr env size
    .ok <| mkElabExpr (.allocArray type' size') mexp.span
  | .deref ptr =>
    let ptr' ← elabMExpr env ptr
    .ok <| mkElabExpr (.deref ptr') mexp.span
  | .arrAccess arr index =>
    let arr' ← elabMExpr env arr
    let index' ← elabMExpr env index
    .ok <| mkElabExpr (.arrAccess arr' index') mexp.span
  | _ => .ok mexp

mutual
partial def elabMLValue (env : Env) (mlv : MarkedLValue) : Except String MarkedLValue := do
  let node ← elabLValue env mlv.node
  .ok { node, span := mlv.span }

partial def elabLValue (env : Env) : LValue → Except String LValue
  | .var name => .ok (.var name)
  | .deref ptr => do
      let ptr' ← elabMLValue env ptr
      .ok (.deref ptr')
  | .dot struct field => do
      let struct' ← elabMLValue env struct
      .ok (.dot struct' field)
  | .arrow structPtr field => do
      let structPtr' ← elabMLValue env structPtr
      .ok (.arrow structPtr' field)
  | .arrAccess arr index => do
      let arr' ← elabMLValue env arr
      let index' ← elabMExpr env index
      .ok (.arrAccess arr' index')
end

mutual
partial def lvalueToExpr (lv : LValue) (span : Option SrcSpan) : MarkedExpr :=
  match lv with
  | .var name => mkElabExpr (.var name) span
  | .deref ptr => mkElabExpr (.deref (markedLValueToExpr ptr)) span
  | .dot struct field => mkElabExpr (.dot (markedLValueToExpr struct) field) span
  | .arrow structPtr field => mkElabExpr (.arrow (markedLValueToExpr structPtr) field) span
  | .arrAccess arr index => mkElabExpr (.arrAccess (markedLValueToExpr arr) index) span

partial def markedLValueToExpr (lv : MarkedLValue) : MarkedExpr :=
  lvalueToExpr lv.node lv.span
end

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

partial def elabMStm (env : Env) (mstm : MarkedStm) : Except String MarkedStm := do
  match mstm.node with
  | .assign lhs val => do
    let lhs' ← elabMLValue env lhs
    let val' ← elabMExpr env val
    .ok (mkElabStm (.assign lhs' val') mstm.span)
  | .ifLit test thenBranch elseBranch =>
    let test' ← elabMExpr env test
    let thenBranch' ← elabMStm env thenBranch
    let elseBranch' ← elabMStm env elseBranch
    .ok (mkElabStm (.ifLit test' thenBranch' elseBranch') mstm.span)
  | .whileLit test body step =>
    let test' ← elabMExpr env test
    let body' ← elabMStm env body
    let step' ← elabMStm env step
    .ok (mkElabStm (.whileLit test' body' step') mstm.span)
  | .ret valOpt =>
    match valOpt with
    | some val =>
      let val' ← elabMExpr env val
      .ok (mkElabStm (.ret (some val')) mstm.span)
    | none => .ok (mkElabStm (.ret none) mstm.span)
  | .seq first rest =>
    let first' ← elabMStm env first
    let rest' ← elabMStm env rest
    let span := spanCoverOpt first.span rest.span
    .ok (mkElabStm (.seq first' rest') span)
  | .declare varName tau init value =>
    if env.contains varName then
      throw "Variable cannot have the same name as a type"
    let t ← elabTypeName env tau
    let init' ← init.mapM (elabMExpr env)
    let value' ← elabMStm env value
    .ok (mkElabStm (.declare varName t init' value') mstm.span)
  | .asop lhs op value =>
    let lhs' ← elabMLValue env lhs
    match assignOpToBinOp op with
    | none =>
      let value' ← elabMExpr env value
      .ok (mkElabStm (.assign lhs' value') mstm.span)
    | some binop =>
      let lhsExpr := markedLValueToExpr lhs'
      let value' ← elabMExpr env value
      let rhs := mkElabExpr (.binop binop lhsExpr value') mstm.span
      .ok (mkElabStm (.assign lhs' rhs) mstm.span)
  | .forLit init test update body =>
    let bodySpan := spanCoverOpt body.span update.span
    let whileSpan := spanCoverOpt test.span bodySpan
    let forSpan := spanCoverOpt init.span whileSpan
    let desugaredWhile := mkElabStm (.whileLit test body update) whileSpan
    match init.node with
    | .declare varName tau init initBody =>
      let scopedFor := mkElabStm (.declare varName tau init (mkElabStm (.seq initBody desugaredWhile) forSpan)) forSpan
      elabMStm env scopedFor
    | _ =>
      let desugaredFor := mkElabStm (.seq init desugaredWhile) forSpan
      elabMStm env desugaredFor
  | .expr e => do
    let e' ← elabMExpr env e
    .ok (mkElabStm (.expr e') mstm.span)
  | .assert test => do
    let test' ← elabMExpr env test
    .ok (mkElabStm (.assert test') mstm.span)
  | .error e => do
    let e' ← elabMExpr env e
    .ok (mkElabStm (.error e') mstm.span)
  | .incr lhs =>
    let lhs' ← elabMLValue env lhs
    let lhsExpr := markedLValueToExpr lhs'
    let one := mkElabExpr (.intLit 1) mstm.span
    let rhs := mkElabExpr (.binop .plus lhsExpr one) mstm.span
    .ok (mkElabStm (.assign lhs' rhs) mstm.span)
  | .decr lhs =>
    let lhs' ← elabMLValue env lhs
    let lhsExpr := markedLValueToExpr lhs'
    let one := mkElabExpr (.intLit 1) mstm.span
    let rhs := mkElabExpr (.binop .sub lhsExpr one) mstm.span
    .ok (mkElabStm (.assign lhs' rhs) mstm.span)
  | _ => .ok mstm

def elabMAnno (env : Env) (a : MarkedAnno) : Except String MarkedAnno := do
  match a.node with
  | .requires precondition =>
    let precondition' ← elabMExpr env precondition
    .ok <| mkElabAnno (.requires precondition') a.span
  | .ensures postcondition =>
    let postcondition' ← elabMExpr env postcondition
    .ok <| mkElabAnno (.ensures postcondition') a.span
  | .asserts e =>
    let e' ← elabMExpr env e
    .ok <| mkElabAnno (.asserts e') a.span
  | .loopInvariant e =>
    let e' ← elabMExpr env e
    .ok <| mkElabAnno (.loopInvariant e') a.span

def elabParams (params : List Param) (env : Env) : Except String (List Param) :=
  List.mapM (λ (tau, paramName) => do
    let tau' ← elabTypeName env tau
    .ok (tau', paramName))
  params

def tauEq : Tau → Tau → Bool
  | .int, .int => true
  | .char, .char => true
  | .string, .string => true
  | .bool, .bool => true
  | .void, .void => true
  | .typeName lhs, .typeName rhs => lhs == rhs
  | .struct lhs, .struct rhs => lhs == rhs
  | .ptr lhs, .ptr rhs => tauEq lhs rhs
  | .array lhs, .array rhs => tauEq lhs rhs
  | _, _ => false

def fnSigEq (retType : Tau) (paramTypes : List Tau) (info : FnInfo) : Bool :=
  tauEq retType info.retType
    && paramTypes.length == info.paramTypes.length
    && (List.zip paramTypes info.paramTypes).all (fun (lhs, rhs) => tauEq lhs rhs)

def paramTypes (params : List Param) : List Tau :=
  params.map (fun (tau, _) => tau)

def registerFn
    (fenv : FnEnv) (fname : String) (retType : Tau) (params : List Param)
    (defined external : Bool) : Except String FnEnv := do
  let paramTypes := paramTypes params
  match fenv.get? fname with
  | none =>
      .ok (fenv.insert fname { retType, paramTypes, defined, external })
  | some info =>
      if not (fnSigEq retType paramTypes info) then
        .error s!"function {fname} declared with inconsistent types"
      else if defined && info.external && not external then
        .error s!"function {fname} cannot define an external function"
      else if defined && info.defined then
        .error s!"function {fname} defined more than once"
      else
        .ok (fenv.insert fname { info with defined := info.defined || defined, external := info.external || external })

mutual
partial def collectCallsMExpr (mexpr : MarkedExpr) : Std.HashSet String :=
  match mexpr.node with
  | .var _ | .intLit _ | .trueLit | .falseLit | .null | .charLit _ | .stringLit _ | .result | .hastag | .alloc _ => {}
  | .binop _ lhs rhs =>
      (collectCallsMExpr lhs).fold (fun acc fname => acc.insert fname) (collectCallsMExpr rhs)
  | .unop _ operand =>
      collectCallsMExpr operand
  | .ternary test thenVal elseVal =>
      let calls := collectCallsMExpr test
      let calls := (collectCallsMExpr thenVal).fold (fun acc fname => acc.insert fname) calls
      (collectCallsMExpr elseVal).fold (fun acc fname => acc.insert fname) calls
  | .call fname args =>
      args.foldl
        (fun calls arg => (collectCallsMExpr arg).fold (fun acc called => acc.insert called) calls)
        (({} : Std.HashSet String).insert fname)
  | .length arrayLike =>
      collectCallsMExpr arrayLike
  | .dot struct _ =>
      collectCallsMExpr struct
  | .arrow structPtr _ =>
      collectCallsMExpr structPtr
  | .allocArray _ size =>
      collectCallsMExpr size
  | .deref ptr =>
      collectCallsMExpr ptr
  | .arrAccess arr index =>
      (collectCallsMExpr arr).fold (fun acc fname => acc.insert fname) (collectCallsMExpr index)

partial def collectCallsMLValue (mlv : MarkedLValue) : Std.HashSet String :=
  match mlv.node with
  | .var _ => {}
  | .deref ptr => collectCallsMLValue ptr
  | .dot struct _ => collectCallsMLValue struct
  | .arrow structPtr _ => collectCallsMLValue structPtr
  | .arrAccess arr index =>
      (collectCallsMLValue arr).fold (fun acc fname => acc.insert fname) (collectCallsMExpr index)

partial def collectCallsMAnno (manno : MarkedAnno) : Std.HashSet String :=
  match manno.node with
  | .requires e | .ensures e | .asserts e | .loopInvariant e => collectCallsMExpr e

partial def collectCallsMStm (mstm : MarkedStm) : Std.HashSet String :=
  match mstm.node with
  | .assert val | .error val | .expr val =>
      collectCallsMExpr val
  | .assign lhs val | .asop lhs _ val =>
      (collectCallsMLValue lhs).fold (fun acc fname => acc.insert fname) (collectCallsMExpr val)
  | .ifLit test thenBranch elseBranch =>
      let calls := collectCallsMExpr test
      let calls := (collectCallsMStm thenBranch).fold (fun acc fname => acc.insert fname) calls
      (collectCallsMStm elseBranch).fold (fun acc fname => acc.insert fname) calls
  | .whileLit test body step =>
      let calls := collectCallsMExpr test
      let calls := (collectCallsMStm body).fold (fun acc fname => acc.insert fname) calls
      (collectCallsMStm step).fold (fun acc fname => acc.insert fname) calls
  | .ret (some val) =>
      collectCallsMExpr val
  | .ret none | .nop =>
      {}
  | .incr lhs | .decr lhs =>
      collectCallsMLValue lhs
  | .seq first rest =>
      (collectCallsMStm first).fold (fun acc fname => acc.insert fname) (collectCallsMStm rest)
  | .declare _ _ init value =>
      let calls := match init with | some e => collectCallsMExpr e | none => {}
      (collectCallsMStm value).fold (fun acc fname => acc.insert fname) calls
  | .forLit init test update body =>
      let calls := collectCallsMStm init
      let calls := (collectCallsMExpr test).fold (fun acc fname => acc.insert fname) calls
      let calls := (collectCallsMStm update).fold (fun acc fname => acc.insert fname) calls
      (collectCallsMStm body).fold (fun acc fname => acc.insert fname) calls
  | .annotation a =>
      collectCallsMAnno a
end

def collectCallsGDecl : GDecl → Std.HashSet String
  | .fdecl _ _ _ annotations =>
      annotations.foldl (fun calls anno => (collectCallsMStm anno).fold (fun acc fname => acc.insert fname) calls) {}
  | .fdefn _ _ _ body annotations =>
      let calls := body.foldl (fun calls stm => (collectCallsMStm stm).fold (fun acc fname => acc.insert fname) calls) {}
      annotations.foldl (fun calls anno => (collectCallsMStm anno).fold (fun acc fname => acc.insert fname) calls) calls
  | .typedef .. => {}
  | .sdecl .. => {}

def checkReferencedFnsDefined (fenv : FnEnv) (referenced : Std.HashSet String) : Except String Unit :=
  referenced.fold
    (fun result fname => do
      let _ ← result
      match fenv.get? fname with
      | none => .ok ()
      | some info =>
          if info.defined || info.external then
            .ok ()
          else
            .error s!"function {fname} declared and referenced but never defined")
    (.ok ())

def checkFnNameNotTypedef (fname : String) (env : Env) : Except String Unit := do
  if env.contains fname then
    .error "Found a function sharing a name with a typedef"
  else
    .ok ()

def checkTypedefNameNotFunction (alias : String) (fenv : FnEnv) : Except String Unit := do
  if fenv.contains alias then
    .error "Found a typedef sharing a name with a function"
  else
    .ok ()

def checkFnParamNamesNotTypedef (params : List Param) (env : Env) : Except String Unit := do
  params.forM (λ (_, paramName) =>
    if env.contains paramName then
      .error "Param name is the name of a typedef"
    else
      .ok ())

def checkParamNamesUnique (params : List Param) : Except String Unit := do
  let _ ← List.foldlM
    (λ (seenParams : Std.HashSet String) (_, param) =>
      if seenParams.contains param then
        .error "Function contains non-unique param names"
      else
        .ok (seenParams.insert param))
    {}
    params
  .ok ()

def checkParamTypesNotVoid (params : List Param) : Except String Unit := do
  params.forM (λ (tau, _) =>
    if tauEq tau .void then
      .error "Param type cannot be of type void"
    else
      .ok ())

def elabFields (fields : List Field) (env : Env) : Except String (List Field) :=
  List.mapM (λ (tau, fieldName) => do
    let tau' ← elabTypeName env tau
    .ok (tau', fieldName))
  fields

def checkFieldNamesUnique (fields : List Field) : Except String Unit := do
  let _ ← List.foldlM
    (λ (seenFields : Std.HashSet String) (_, field) =>
      if seenFields.contains field then
        .error "Struct contains non-unique field names"
      else
        .ok (seenFields.insert field))
    {}
    fields
  .ok ()

def checkFieldTypesNotVoid (fields : List Field) : Except String Unit := do
  fields.forM (λ (tau, _) =>
    if tauEq tau .void then
      .error "Field type cannot be of type void"
    else
      .ok ())

def elabGDecl (gdecl : GDecl) (env : Env) : Except String (GDecl × Env) := do
  match gdecl with
  | .fdefn retType fname params body annotations =>
    let _ ← checkFnNameNotTypedef fname env
    let _ ← checkFnParamNamesNotTypedef params env
    let _ ← checkParamNamesUnique params
    let _ ← checkParamTypesNotVoid params
    let retType' ← elabTypeName env retType
    let params' ← elabParams params env
    let body' ← List.mapM (elabMStm env) body
    let annotations' ← List.mapM (elabMStm env) annotations
    .ok
      ( .fdefn retType' fname params' body' annotations'
      , env
      )
  | .fdecl retType fname params annotations =>
    let _ ← checkFnNameNotTypedef fname env
    let _ ← checkFnParamNamesNotTypedef params env
    let _ ← checkParamNamesUnique params
    let _ ← checkParamTypesNotVoid params
    let retType' ← elabTypeName env retType
    let params' ← elabParams params env
    let annotations' ← List.mapM (elabMStm env) annotations
    .ok
      ( .fdecl retType' fname params' annotations'
      , env
      )

  | .typedef tau alias =>
    let t ← elabTypeName env tau
    let _ ← if env.contains alias then
      .error "typedef aliases must be unique"
    if tauEq t .void then
      .error "typedef cannot alias void"
    else
      .ok (.typedef t alias, env.insert alias t)
  | .sdecl name fields =>
    let _ ← checkFieldNamesUnique fields
    let _ ← checkFieldTypesNotVoid fields
    let fields' ← elabFields fields env
    .ok (.sdecl name fields', env)

def checkCallsDeclared (fenv : FnEnv) (calledFns : Std.HashSet String) : Except String Unit :=
  calledFns.fold
    (fun result fname => do
      let _ ← result
      if fenv.contains fname then
        .ok ()
      else
        .error s!"function {fname} used before decl")
    (.ok ())

private def registerHeaderGDecl (fenv : FnEnv) : GDecl → Except String FnEnv
  | .fdecl retType fname params _ =>
      if fname == "main" then
        .error "Headers cannot declare main function"
      else
        registerFn fenv fname retType params false true
  | .fdefn .. =>
      .error "Function definitions are not allowed in header files"
  | .typedef .. => .ok fenv
  | .sdecl .. => .ok fenv

private def registerSourceGDecl (fenv : FnEnv) : GDecl → Except String FnEnv
  | .fdecl retType fname params _ =>
      registerFn fenv fname retType params false false
  | .fdefn retType fname params _ _ =>
      registerFn fenv fname retType params true false
  | .typedef .. => .ok fenv
  | .sdecl .. => .ok fenv

private def keepHeaderGDecl : GDecl → Bool
  | .fdecl .. => true
  | .fdefn .. => true
  | .sdecl .. => true
  | .typedef .. => false

private def keepSourceGDecl : GDecl → Bool
  | .fdefn .. => true
  | .fdecl .. => true
  | .sdecl .. => true
  | _ => false

private def seedMainFn (fenv : FnEnv) : Except String FnEnv :=
  match fenv.get? "main" with
  | some _ => .ok fenv
  | none => registerFn fenv "main" .int [] false false

private def elabHeader (program : Ast.Program) : Except String (Ast.Program × Env × FnEnv) :=
  match program.foldlM
    (λ (progAcc, envAcc, fenvAcc) gdecl => do
      match gdecl with
      | .typedef _ alias => checkTypedefNameNotFunction alias fenvAcc
      | _ => .ok ()
      let (elabbedGDecl, envAcc') ← elabGDecl gdecl envAcc
      let fenvAcc' ← registerHeaderGDecl fenvAcc elabbedGDecl
      .ok
        ( if keepHeaderGDecl elabbedGDecl then elabbedGDecl :: progAcc else progAcc
        , envAcc'
        , fenvAcc' ))
    ([], {}, {})
    with
  | .ok (elabbedHeader, env, fenv) => .ok (List.reverse elabbedHeader, env, fenv)
  | .error err => .error err

private def elabSourceWithHeaderEnv
    (initEnv : Env) (initFnEnv : FnEnv) (program : Ast.Program) : Except String Ast.Program :=
  match program.foldlM
    (λ (progAcc, envAcc, fenvAcc, referencedAcc) gdecl => do
      match gdecl with
      | .typedef _ alias => checkTypedefNameNotFunction alias fenvAcc
      | _ => .ok ()
      let (elabbedGDecl, envAcc') ← elabGDecl gdecl envAcc
      let fenvAcc' ← registerSourceGDecl fenvAcc elabbedGDecl
      let calledFns := collectCallsGDecl elabbedGDecl
      let _ ← checkCallsDeclared fenvAcc' calledFns
      let referencedAcc' :=
        calledFns.fold (λ (acc : Std.HashSet String) fname => acc.insert fname) referencedAcc
      .ok
        ( if keepSourceGDecl elabbedGDecl then elabbedGDecl :: progAcc else progAcc
        , envAcc'
        , fenvAcc'
        , referencedAcc' ))
    ([], initEnv, initFnEnv, {})
    with
  | .ok (elabbedSource, _, fenv, referenced) => do
      let _ ← checkReferencedFnsDefined fenv referenced
      .ok (List.reverse elabbedSource)
  | .error err => .error err

def elabHeaderAndSource (header : Ast.Program) (source : Ast.Program) :
    Except String C0VC.ElabbedAst.Program := do
  let (elabbedHeader, headerEnv, headerFnEnv) ← elabHeader header
  let sourceFnEnv ← seedMainFn headerFnEnv
  let elabbedSourceParsed ← elabSourceWithHeaderEnv headerEnv sourceFnEnv source
  C0VC.ElabbedAst.Trans.convertProgram (elabbedHeader ++ elabbedSourceParsed)

end C0VC.Elab
