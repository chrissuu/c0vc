import C0VC.Ast.TypedAst
import C0VC.StrataBoole.IR
import C0VC.StrataBoole.Struct
import Std.Data.HashMap
import Std.Data.HashSet

/-!
StrataBoole.Trans

Lowers the typed C0 AST into the Boole IR.

Expressions are lowered into a list of `Pre` items followed by a pure Boole
expression. A `Pre` is either a statement that must run first (a procedure
call, an allocation, a fresh string) or a proof obligation (a C0 runtime check
such as a null check or an array bounds check). Pre items appear in C0
evaluation order, and obligations under `&&`, `||` and `?:` are guarded by the
branch condition, so short-circuiting is preserved.

Statement contexts turn obligations into `check` statements. Contract contexts
(requires, ensures, loop invariants) turn them into extra contract clauses and
reject statements.

Memory model: see `C0VC/StrataBoole/README.md`.

Author(s):
  ~ Chris Su <chrjs@cmu.edu>
-/

namespace C0VC.StrataBoole.Trans

open C0VC.StrataBoole
open C0VC.Utils.SrcSpan

abbrev CTau := C0VC.TypedAst.Tau
abbrev CExpr := C0VC.TypedAst.TypedExpr
abbrev CLValue := C0VC.TypedAst.TypedLValue
abbrev CStm := C0VC.TypedAst.Stm

instance : Inhabited CExpr := ⟨{ node := .null, tau := .null }⟩

structure Config where
  intModel : IntModel := .bv32
  resultName : String := "__result"

/-- Heap model globals, in the order they are declared and listed in `modifies`. -/
def heapGlobals : List String :=
  [ "nextRef", "len", "hInt", "hBool", "hRef", "hStr" ]

def zeroMaps : List (String × String) :=
  [ ("hInt", "zeroInt"), ("hBool", "zeroBool"), ("hRef", "zeroRef") ]

def bodyLabel : String := "__body"

def booleKeywords : List String :=
  [ "program", "Boole", "type", "function", "var", "procedure", "returns", "spec"
  , "requires", "ensures", "modifies", "free", "assert", "assume", "havoc", "call"
  , "if", "then", "else", "while", "invariant", "for", "to", "downto", "by"
  , "decreases", "let", "in", "old", "result", "true", "false", "int", "bool"
  , "string", "real", "Map", "bv", "exit", "forall", "exists", "axiom", "const"
  , "div", "mod", "sdiv", "smod", "ashr", "slt", "sle", "sgt", "sge", "out", "inout"
  , "cover", "datatype", "mapConst", "as_sint", "as_uint", "as_bv32", "C0String" ]

def intMin : Int := -2147483648
def intMax : Int := 2147483647

/-- Wrap a literal into the signed 32-bit range, as C0 does for hex literals. -/
def normInt (n : Int) : Int :=
  let m := n % 4294967296
  if m >= 2147483648 then m - 4294967296 else m

/-- Contract and naming information computed before any body is lowered. -/
structure FnSig where
  boogieName : String
  /-- Boole parameter names, paired with the C0 parameter names. -/
  params : List (Tau × String × String)
  ret : Option (Tau × String)
  /-- Checked preconditions over the Boole parameter names. Call sites assert them. -/
  requires : List (Expr × Option SrcSpan)
  specs : List Spec
deriving Inhabited

structure St where
  cfg : Config
  layout : Struct.Layout
  sigs : Std.HashMap String FnSig := {}
  procNames : Std.HashMap String String := {}
  reserved : Std.HashSet String := {}
  procName : String := ""
  used : Std.HashSet String := {}
  scopes : List (Std.HashMap String String) := []
  varTaus : Std.HashMap String Tau := {}
  usedExit : Bool := false
  inSpec : Bool := false
  labels : Array LabelInfo := #[]
  usedLabels : Std.HashSet String := {}
  usesStrings : Bool := false

abbrev M := StateT St (Except String)

inductive Pre where
  | stmt (s : Stmt)
  | ob (label : String) (cond : Expr)
deriving Inhabited

/-! ## Helpers -/

private def locate (span? : Option SrcSpan) (msg : String) : String :=
  match span? with
  | some span => s!"{span.fileName}:{span.startLoc.line}:{span.startLoc.col}: {msg}"
  | none => msg

private def fail (msg : String) (span? : Option SrcSpan := none) : M α :=
  throw (locate span? msg)

private def sanitize (name : String) : String :=
  String.map (fun c => if c.isAlphanum || c == '_' then c else '_') name

private partial def pickName (taken : String → Bool) (base : String) (k : Nat := 0) : String :=
  let candidate := if k == 0 then base else s!"{base}_{k}"
  if taken candidate then pickName taken base (k + 1) else candidate

private def freshName (base : String) : M String := do
  let st ← get
  let name := pickName (fun n => st.used.contains n || st.reserved.contains n) (sanitize base)
  set { st with used := st.used.insert name }
  pure name

private def bindAs (c0Name boogieName : String) (tau : Tau) : M Unit :=
  modify fun st =>
    let scope := (st.scopes.head?.getD {}).insert c0Name boogieName
    { st with
      scopes := scope :: st.scopes.drop 1
      used := st.used.insert boogieName
      varTaus := st.varTaus.insert boogieName tau }

private def bindVar (c0Name : String) (tau : Tau) : M String := do
  let name ← freshName c0Name
  bindAs c0Name name tau
  pure name

private def lookupVar (c0Name : String) (span? : Option SrcSpan) : M String := do
  match (← get).scopes.findSome? (·.get? c0Name) with
  | some name => pure name
  | none => fail s!"internal error: unbound variable {c0Name}" span?

private def withScope (m : M α) : M α := do
  modify fun st => { st with scopes := {} :: st.scopes }
  let result ← m
  modify fun st => { st with scopes := st.scopes.drop 1 }
  pure result

private def withSpec (m : M α) : M α := do
  let saved := (← get).inSpec
  modify fun st => { st with inSpec := true }
  let result ← m
  modify fun st => { st with inSpec := saved }
  pure result

private def freshTemp (hint : String) (tau : Tau) : M String := do
  let name ← freshName s!"__{hint}"
  modify fun st => { st with varTaus := st.varTaus.insert name tau }
  pure name

private def mkLabel (kind message : String) (span? : Option SrcSpan) : M String := do
  let st ← get
  let label :=
    match span? with
    | some span => pickName (st.usedLabels.contains ·) s!"{kind}_L{span.startLoc.line}C{span.startLoc.col}"
    | none => pickName (st.usedLabels.contains ·) kind 1
  set { st with
    usedLabels := st.usedLabels.insert label
    labels := st.labels.push { label, message, procedure := st.procName, span := span? } }
  pure label

private def obligation (kind message : String) (span? : Option SrcSpan) (cond : Expr) : M Pre := do
  pure (.ob (← mkLabel kind message span?) cond)

private def lowerTau (span? : Option SrcSpan) : CTau → M Tau
  | .int | .char => pure .int
  | .bool => pure .bool
  | .ptr _ | .array _ | .null | .struct _ => pure .ref
  | .string => do
      modify fun st => { st with usesStrings := true }
      pure .string
  | .void => fail "void has no value representation" span?

private def heapOf (span? : Option SrcSpan) : CTau → M String
  | .int | .char => pure "hInt"
  | .bool => pure "hBool"
  | .ptr _ | .array _ | .null => pure "hRef"
  | .string => do
      modify fun st => { st with usesStrings := true }
      pure "hStr"
  | .struct name => fail s!"struct {name} values cannot be used directly; access a field instead" span?
  | .void => fail "void values are not stored in memory" span?

private def structName (span? : Option SrcSpan) : CTau → M String
  | .struct name => pure name
  | .ptr (.struct name) => pure name
  | _ => fail "internal error: expected a struct type" span?

private def isStructTau : CTau → Bool
  | .struct _ => true
  | _ => false

private def fieldInfo (span? : Option SrcSpan) (sname field : String) : M Struct.FieldInfo := do
  match Struct.lookupField (← get).layout sname field with
  | .ok info => pure info
  | .error msg => fail msg span?

/-! ## Expression builders -/

private def mkAnd : Expr → Expr → Expr
  | .boolLit true, e => e
  | e, .boolLit true => e
  | a, b => .and a b

private def mkNot : Expr → Expr
  | .boolLit b => .boolLit !b
  | .not e => e
  | e => .not e

private def mkImplies : Expr → Expr → Expr
  | .boolLit true, e => e
  | _, .boolLit true => .boolLit true
  | a, b => .implies a b

private def mkIte (test thenVal elseVal : Expr) : Expr :=
  match thenVal, elseVal with
  | .boolLit true, .boolLit false => test
  | .boolLit false, .boolLit true => mkNot test
  | t, .boolLit false => mkAnd test t
  | .boolLit true, f => .or test f
  | t, f => .ite test t f

private def mathAdd : Expr → Expr → Expr
  | .mathLit 0, e => e
  | e, .mathLit 0 => e
  | .mathLit a, .mathLit b => .mathLit (a + b)
  | a, b => .mathArith .add a b

/--
Heap cells are addressed by object, element index (a C0 int) and field offset.
Scalars and pointees use element 0; non-struct array elements use field 0.
-/
private def heapAt (heap : String) (ref elem field : Expr) : Expr :=
  .mapGet (.mapGet (.mapGet (.var heap) ref) elem) field

private def heapSlot (heap : String) (ref elem field : Expr) : LValue :=
  .mapSlot (.mapGet (.mapGet (.var heap) ref) elem) field

private def lenOf (ref : Expr) : Expr :=
  .mapGet (.var "len") ref

private def nextRef : Expr := .var "nextRef"

/-- A reference is NULL or names an allocated object. -/
def validRef (r : Expr) : Expr :=
  .or (.eq r .null) (.and (.mathCmp .lt (.mathLit 0) r) (.mathCmp .lt r nextRef))

private def allocated (r : Expr) : Expr :=
  .and (.mathCmp .lt (.mathLit 0) r) (.mathCmp .lt r nextRef)

/--
Heap well-formedness. It holds in every reachable C0 state, because C0 has no
pointer arithmetic, no casts and no deallocation.
-/
def heapWF : Expr :=
  let r := Expr.var "__r"
  let e := Expr.var "__e"
  let i := Expr.var "__i"
  List.foldl mkAnd (.mathCmp .gt nextRef (.mathLit 0))
    [ .eq (lenOf .null) (.intLit 0)
    , .forall [("__r", .math)] (mkImplies (allocated r) (.cmp .le (.intLit 0) (lenOf r)))
    , .forall [("__r", .math), ("__e", .int), ("__i", .math)]
        (mkImplies (allocated r) (validRef (heapAt "hRef" r e i)))
    ]

def zeroWF : Expr :=
  let e := Expr.var "__e"
  let i := Expr.var "__i"
  let zeroAt (name : String) := Expr.mapGet (.mapGet (.var name) e) i
  .forall [("__e", .int), ("__i", .math)]
    (List.foldl mkAnd (.eq (zeroAt "zeroInt") (.intLit 0))
      [ .eq (zeroAt "zeroBool") (.boolLit false)
      , .eq (zeroAt "zeroRef") .null ])

partial def subst (σ : List (String × Expr)) : Expr → Expr
  | .var name => (σ.lookup name).getD (.var name)
  | .arith op a b => .arith op (subst σ a) (subst σ b)
  | .cmp op a b => .cmp op (subst σ a) (subst σ b)
  | .mathArith op a b => .mathArith op (subst σ a) (subst σ b)
  | .mathCmp op a b => .mathCmp op (subst σ a) (subst σ b)
  | .eq a b => .eq (subst σ a) (subst σ b)
  | .neq a b => .neq (subst σ a) (subst σ b)
  | .and a b => .and (subst σ a) (subst σ b)
  | .or a b => .or (subst σ a) (subst σ b)
  | .not e => .not (subst σ e)
  | .implies a b => .implies (subst σ a) (subst σ b)
  | .ite c t f => .ite (subst σ c) (subst σ t) (subst σ f)
  | .mapGet m k => .mapGet (subst σ m) (subst σ k)
  | .old e => .old (subst σ e)
  | .forall bs body => .forall bs (subst (σ.filter fun (n, _) => !bs.any (·.1 == n)) body)
  | e => e

/-! ## Pre items -/

private def guardPre (guard : Expr) : Pre → Pre
  | .ob label cond => .ob label (mkImplies guard cond)
  | p => p

private def onlyObligations (pres : List Pre) : Bool :=
  pres.all fun
    | .ob .. => true
    | .stmt _ => false

private partial def stmtHasCall : Stmt → Bool
  | .call .. => true
  | .ifElse _ t f => t.any stmtHasCall || f.any stmtHasCall
  | .whileLoop _ _ body | .block _ body => body.any stmtHasCall
  | _ => false

private def hasCall (pres : List Pre) : Bool :=
  pres.any fun
    | .stmt s => stmtHasCall s
    | .ob .. => false

private def flush (pres : List Pre) : List Stmt :=
  pres.map fun
    | .stmt s => s
    | .ob label cond => .check label cond

private def specObligations (what : String) (span? : Option SrcSpan) (pres : List Pre) :
    M (List (String × Expr)) :=
  pres.mapM fun
    | .ob label cond => pure (label, cond)
    | .stmt _ => fail s!"{what} cannot call functions, allocate memory, or use string literals" span?

private def isStable : Expr → Bool
  | .var _ | .intLit _ | .mathLit _ | .boolLit _ | .null => true
  | _ => false

/-- Save a value in a temporary so that later calls cannot change it. -/
private def snapshot (tau : Tau) (pres : List Pre) (e : Expr) : M (List Pre × Expr) := do
  if isStable e then
    pure (pres, e)
  else
    let tmp ← freshTemp "v" tau
    pure (pres ++ [.stmt (.declare tmp tau), .stmt (.assign (.var tmp) e)], .var tmp)

/-- Combine operands evaluated left to right, protecting earlier values from later calls. -/
private partial def sequenceOperands : List (Tau × List Pre × Expr) → M (List Pre × List Expr)
  | [] => pure ([], [])
  | (tau, pres, e) :: rest => do
      let (pres, e) ←
        if rest.any (fun (_, p, _) => hasCall p) then snapshot tau pres e else pure (pres, e)
      let (restPres, restExprs) ← sequenceOperands rest
      pure (pres ++ restPres, e :: restExprs)

/-! ## Expressions -/

private def arithOp : C0VC.TypedAst.BinOp → Option ArithOp
  | .plus => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .mod => some .mod
  | .bitAnd => some .bitAnd
  | .bitOr => some .bitOr
  | .xor => some .xor
  | .shl => some .shl
  | .shr => some .shr
  | _ => none

private def cmpOp : C0VC.TypedAst.BinOp → Option CmpOp
  | .lt => some .lt
  | .lte => some .le
  | .gt => some .gt
  | .gte => some .ge
  | _ => none

private def arithObligations (op : ArithOp) (lhs rhs result : Expr) (span? : Option SrcSpan) :
    M (List Pre) := do
  let st ← get
  match op with
  | .div | .mod =>
      pure
        [ ← obligation "divzero" "divisor may be zero" span? (.neq rhs (.intLit 0))
        , ← obligation "divoverflow" "division may overflow (INT_MIN / -1)" span?
            (mkNot (.and (.eq lhs (.intLit intMin)) (.eq rhs (.intLit (-1))))) ]
  | .shl | .shr =>
      pure [ ← obligation "shift" "shift amount may be outside [0, 32)" span?
               (.and (.cmp .le (.intLit 0) rhs) (.cmp .lt rhs (.intLit 32))) ]
  | .add | .sub | .mul =>
      if st.cfg.intModel == .checked && !st.inSpec then
        pure [ ← obligation "overflow" "arithmetic may overflow" span?
                 (.and (.cmp .le (.intLit intMin) result) (.cmp .le result (.intLit intMax))) ]
      else
        pure []
  | _ => pure []

private def heapsToZero (span? : Option SrcSpan) (elemTau : CTau) : M (List String) := do
  let leaves ←
    match elemTau with
    | .struct name => pure ((← get).layout.leaves.getD name [])
    | tau => pure [tau]
  let heaps ← leaves.mapM (heapOf span?)
  pure (zeroMaps.filterMap fun (heap, _) => if heaps.contains heap then some heap else none)

mutual
partial def lowerExpr (e : CExpr) : M (List Pre × Expr) := do
  let span := e.span
  match e.node with
  | .var name => pure ([], .var (← lookupVar name span))
  | .intLit n => pure ([], .intLit (normInt n))
  | .charLit c => pure ([], .intLit c.toNat)
  | .trueLit => pure ([], .boolLit true)
  | .falseLit => pure ([], .boolLit false)
  | .null => pure ([], .null)
  | .result => pure ([], .var (← get).cfg.resultName)
  | .stringLit _ =>
      if (← get).inSpec then
        fail "string literals are not supported in contracts" span
      else
        let _ ← lowerTau span .string
        let tmp ← freshTemp "str" .string
        pure ([.stmt (.declare tmp .string), .stmt (.havoc tmp)], .var tmp)
  | .hastag => fail "\\hastag is not supported by the Boole backend" span
  | .binop op lhs rhs => do
      let (pl, l) ← lowerExpr lhs
      let (pr, r) ← lowerExpr rhs
      let (pre, ops) ← sequenceOperands [(← lowerTau span lhs.tau, pl, l), (← lowerTau span rhs.tau, pr, r)]
      let (l, r) := (ops.getD 0 l, ops.getD 1 r)
      match arithOp op, cmpOp op, op with
      | some aop, _, _ =>
          let result := Expr.arith aop l r
          pure (pre ++ (← arithObligations aop l r result span), result)
      | _, some cop, _ => pure (pre, .cmp cop l r)
      | _, _, .eq => pure (pre, .eq l r)
      | _, _, _ => pure (pre, .neq l r)
  | .ternary test thenVal elseVal => do
      let (pc, c) ← lowerExpr test
      let (pt, t) ← lowerExpr thenVal
      let (pf, f) ← lowerExpr elseVal
      if onlyObligations pt && onlyObligations pf then
        pure (pc ++ pt.map (guardPre c) ++ pf.map (guardPre (mkNot c)), mkIte c t f)
      else
        let tau ← lowerTau span e.tau
        let tmp ← freshTemp "t" tau
        let branch := Stmt.ifElse c
          (flush pt ++ [.assign (.var tmp) t])
          (flush pf ++ [.assign (.var tmp) f])
        pure (pc ++ [.stmt (.declare tmp tau), .stmt branch], .var tmp)
  | .call fname args => lowerCall span fname args e.tau
  | .length arr => do
      let (pa, a) ← lowerExpr arr
      pure (pa, lenOf a)
  | .alloc tau => lowerAlloc span tau none
  | .allocArray tau size => lowerAlloc span tau (some size)
  | .deref _ | .arrAccess .. | .dot .. | .arrow .. => do
      if isStructTau e.tau then
        fail "struct values can only be used through a field access" span
      let (pre, heap, ref, elem, field) ← lowerAddr e
      pure (pre, heapAt heap ref elem field)

/-- Lower a scalar memory access to its heap, object, element index and field offset. -/
partial def lowerAddr (e : CExpr) : M (List Pre × String × Expr × Expr × Expr) := do
  let span := e.span
  let heap ← heapOf span e.tau
  match e.node with
  | .deref ptr => do
      let (pp, p) ← lowerExpr ptr
      let nullCheck ← obligation "null" "pointer may be NULL" span (.neq p .null)
      pure (pp ++ [nullCheck], heap, p, .intLit 0, .mathLit 0)
  | .arrAccess arr index => do
      let (pre, ref, idx) ← lowerIndex span arr index
      pure (pre, heap, ref, idx, .mathLit 0)
  | .dot struct field => do
      let (pre, ref, elem, base, sname) ← lowerStructBase struct
      let info ← fieldInfo span sname field
      pure (pre, heap, ref, elem, mathAdd base (.mathLit info.offset))
  | .arrow structPtr field => do
      let (pp, p) ← lowerExpr structPtr
      let nullCheck ← obligation "null" "pointer may be NULL" span (.neq p .null)
      let info ← fieldInfo span (← structName span structPtr.tau) field
      pure (pp ++ [nullCheck], heap, p, .intLit 0, .mathLit info.offset)
  | _ => fail "internal error: expected a memory access" span

/-- Lower `arr[index]` to its object reference and checked element index. -/
partial def lowerIndex (span? : Option SrcSpan) (arr index : CExpr) : M (List Pre × Expr × Expr) := do
  let (pa, a) ← lowerExpr arr
  let (pi, i) ← lowerExpr index
  let (pa, a) ← if hasCall pi then snapshot .ref pa a else pure (pa, a)
  let bounds ← obligation "bounds" "array index may be out of bounds" span?
    (mkAnd (.cmp .le (.intLit 0) i) (.cmp .lt i (lenOf a)))
  pure (pa ++ pi ++ [bounds], a, i)

/--
Lower a struct-typed expression to the object, element index and first field
offset that hold it.
-/
partial def lowerStructBase (e : CExpr) : M (List Pre × Expr × Expr × Expr × String) := do
  let span := e.span
  let sname ← structName span e.tau
  match e.node with
  | .deref ptr => do
      let (pp, p) ← lowerExpr ptr
      let nullCheck ← obligation "null" "pointer may be NULL" span (.neq p .null)
      pure (pp ++ [nullCheck], p, .intLit 0, .mathLit 0, sname)
  | .arrAccess arr index => do
      let (pre, ref, idx) ← lowerIndex span arr index
      pure (pre, ref, idx, .mathLit 0, sname)
  | .dot struct field => do
      let (pre, ref, elem, base, outer) ← lowerStructBase struct
      let info ← fieldInfo span outer field
      pure (pre, ref, elem, mathAdd base (.mathLit info.offset), sname)
  | .arrow structPtr field => do
      let (pp, p) ← lowerExpr structPtr
      let nullCheck ← obligation "null" "pointer may be NULL" span (.neq p .null)
      let info ← fieldInfo span (← structName span structPtr.tau) field
      pure (pp ++ [nullCheck], p, .intLit 0, .mathLit info.offset, sname)
  | _ => fail "struct values can only be used through a field access" span

partial def lowerCall (span? : Option SrcSpan) (fname : String) (args : List CExpr) (retTau : CTau) :
    M (List Pre × Expr) := do
  if (← get).inSpec then
    fail s!"calls in contracts are not supported yet (call to {fname})" span?
  let sig ← match (← get).sigs.get? fname with
    | some sig => pure sig
    | none => fail s!"internal error: unknown function {fname}" span?
  let lowered ← args.mapM fun arg => do
    let (pre, e) ← lowerExpr arg
    pure (← lowerTau arg.span arg.tau, pre, e)
  let (pre, argExprs) ← sequenceOperands lowered
  let σ := (sig.params.map (·.2.1)).zip argExprs
  let preconditions ← sig.requires.mapM fun (req, reqSpan?) => do
    let declared := match reqSpan? with
      | some span => s!" (declared at line {span.startLoc.line})"
      | none => ""
    obligation "precondition" s!"precondition of {fname}{declared} may not hold" span? (subst σ req)
  match retTau with
  | .void =>
      pure (pre ++ preconditions ++ [.stmt (.call none sig.boogieName argExprs)], .boolLit true)
  | _ =>
      let tau ← lowerTau span? retTau
      let tmp ← freshTemp "call" tau
      pure (pre ++ preconditions ++
        [.stmt (.declare tmp tau), .stmt (.call (some tmp) sig.boogieName argExprs)], .var tmp)

partial def lowerAlloc (span? : Option SrcSpan) (elemTau : CTau) (size? : Option CExpr) :
    M (List Pre × Expr) := do
  if (← get).inSpec then
    fail "allocation is not allowed in contracts" span?
  let (pre, length) ← match size? with
    | none => pure ([], .intLit 1)
    | some size => do
        let (ps, s) ← lowerExpr size
        let sizeCheck ← obligation "allocsize" "array size may be negative" span? (.cmp .le (.intLit 0) s)
        pure (ps ++ [sizeCheck], s)
  let tmp ← freshTemp "alloc" .ref
  let heaps ← heapsToZero span? elemTau
  let zeroes := heaps.filterMap fun heap =>
    (zeroMaps.lookup heap).map fun zero => Stmt.assign (.mapSlot (.var heap) (.var tmp)) (.var zero)
  let stms :=
    [ Stmt.declare tmp .ref
    , .assign (.var tmp) nextRef
    , .assign (.var "nextRef") (mathAdd nextRef (.mathLit 1))
    , .assign (.mapSlot (.var "len") (.var tmp)) length ] ++ zeroes
  pure (pre ++ stms.map .stmt, .var tmp)
end

/-! ## Statements -/

private partial def lvalueToExpr (lv : CLValue) : CExpr :=
  let node : C0VC.TypedAst.Expr :=
    match lv.node with
    | .var name => .var name
    | .deref ptr => .deref (lvalueToExpr ptr)
    | .dot struct field => .dot (lvalueToExpr struct) field
    | .arrow structPtr field => .arrow (lvalueToExpr structPtr) field
    | .arrAccess arr index => .arrAccess (lvalueToExpr arr) index
  { node, tau := lv.tau, span := lv.span }

/-- Split the loop invariants that lead a loop body from the rest of the body. -/
private partial def peelInvariants : CStm → List CExpr × CStm
  | .annotation (.loopInvariant inv) => ([inv], .nop)
  | .seq first rest =>
      let (invs, first') := peelInvariants first
      match first' with
      | .nop =>
          let (moreInvs, rest') := peelInvariants rest
          (invs ++ moreInvs, rest')
      | _ => (invs, .seq first' rest)
  | stm => ([], stm)

private partial def assignedVars : CStm → List String
  | .assign lhs _ =>
      match lhs.node with
      | .var name => [name]
      | _ => []
  | .ifLit _ thenBranch elseBranch => assignedVars thenBranch ++ assignedVars elseBranch
  | .whileLit _ body => assignedVars body
  | .seq first rest => assignedVars first ++ assignedVars rest
  | .declare _ _ _ body => assignedVars body
  | _ => []

private partial def exprVars (e : CExpr) : List String :=
  match e.node with
  | .var name => [name]
  | .binop _ l r => exprVars l ++ exprVars r
  | .ternary c t f => exprVars c ++ exprVars t ++ exprVars f
  | .call _ args => args.flatMap exprVars
  | .length a | .deref a | .dot a _ | .arrow a _ => exprVars a
  | .allocArray _ size => exprVars size
  | .arrAccess a i => exprVars a ++ exprVars i
  | _ => []

private partial def declaredIn : Stmt → List String
  | .declare name _ => [name]
  | .ifElse _ t f => t.flatMap declaredIn ++ f.flatMap declaredIn
  | .whileLoop _ _ body | .block _ body => body.flatMap declaredIn
  | _ => []

private partial def assignedIn : Stmt → List String
  | .assign (.var name) _ => [name]
  | .assign (.mapSlot map _) _ =>
      let rec root : Expr → List String
        | .var name => [name]
        | .mapGet m _ => root m
        | _ => []
      root map
  | .call (some name) _ _ => [name]
  | .havoc name => [name]
  | .ifElse _ t f => t.flatMap assignedIn ++ f.flatMap assignedIn
  | .whileLoop _ _ body | .block _ body => body.flatMap assignedIn
  | _ => []

/--
Facts that a loop's havoc forgets but that hold in every reachable C0 state:
heap well-formedness and the validity of references held in local variables.
-/
private def loopAssumptions (usesHeap : Bool) (body : List Stmt) : M (List Stmt) := do
  if !usesHeap then
    return []
  let st ← get
  let declared := body.flatMap declaredIn
  let assigned := (body.flatMap assignedIn).eraseDups
  let touchesHeap := body.any stmtHasCall || assigned.any heapGlobals.contains
  let refLocals := assigned.filter fun name =>
    !declared.contains name && st.varTaus.get? name == some .ref
  let wf := if touchesHeap then [Stmt.assume heapWF] else []
  pure (wf ++ refLocals.map fun name => .assume (validRef (.var name)))

private def checkStm (kind message : String) (test : CExpr) : M (List Stmt) := do
  let (pre, t) ← lowerExpr test
  let label ← mkLabel kind message test.span
  pure (flush pre ++ [.check label t])

mutual
partial def lowerStm (usesHeap tail : Bool) (stm : CStm) : M (List Stmt) := do
  match stm with
  | .nop => pure []
  | .seq first rest => do
      let a ← lowerStm usesHeap false first
      let b ← lowerStm usesHeap tail rest
      pure (a ++ b)
  | .declare name tau init body => withScope do
      let bt ← lowerTau none tau
      let initStms ← match init with
        | none => pure none
        | some e => some <$> lowerExpr e
      let n ← bindVar name bt
      let initStms := match initStms with
        | none => []
        | some (pre, e) => flush pre ++ [.assign (.var n) e]
      let bodyStms ← lowerStm usesHeap tail body
      pure ([.declare n bt] ++ initStms ++ bodyStms)
  | .assign lhs val => lowerAssign lhs val
  | .ret valOpt => do
      let resultName := (← get).cfg.resultName
      let stms ← match valOpt with
        | some e => do
            let (pre, v) ← lowerExpr e
            pure (flush pre ++ [.assign (.var resultName) v])
        | none => pure []
      if tail then
        pure stms
      else
        modify fun st => { st with usedExit := true }
        pure (stms ++ [.exit bodyLabel])
  | .expr e => do
      let (pre, _) ← lowerExpr e
      pure (flush pre)
  | .assert test => checkStm "assert" "assert() may fail" test
  | .annotation (.asserts test) => checkStm "assert" "//@assert may fail" test
  | .error e => do
      let (pre, _) ← lowerExpr e
      let label ← mkLabel "error" "error() may be reached" e.span
      pure (flush pre ++ [.check label (.boolLit false)])
  | .annotation (.loopInvariant inv) =>
      fail "a loop invariant must directly follow a loop header, as in `while (c) //@loop_invariant I; { ... }`" inv.span
  | .annotation (.requires e) =>
      fail "//@requires can only annotate a function declaration" e.span
  | .annotation (.ensures e) =>
      fail "//@ensures can only annotate a function declaration" e.span
  | .ifLit test thenBranch elseBranch => do
      let (pre, c) ← lowerExpr test
      let thenStms ← withScope (lowerStm usesHeap tail thenBranch)
      let elseStms ← withScope (lowerStm usesHeap tail elseBranch)
      pure (flush pre ++ [.ifElse c thenStms elseStms])
  | .whileLit test body => lowerWhile usesHeap test body

partial def lowerAssign (lhs : CLValue) (val : CExpr) : M (List Stmt) := do
  match lhs.node with
  | .var name => do
      let (pre, v) ← lowerExpr val
      pure (flush pre ++ [.assign (.var (← lookupVar name lhs.span)) v])
  | _ => do
      if isStructTau lhs.tau then
        fail "struct values cannot be assigned" lhs.span
      let (pa, heap, ref, elem, field) ← lowerAddr (lvalueToExpr lhs)
      let (pv, v) ← lowerExpr val
      let (pa, ref, elem) ←
        if hasCall pv then do
          let (pa, ref) ← snapshot .ref pa ref
          let (pa, elem) ← snapshot .int pa elem
          pure (pa, ref, elem)
        else
          pure (pa, ref, elem)
      pure (flush pa ++ flush pv ++ [.assign (heapSlot heap ref elem field) v])

partial def lowerWhile (usesHeap : Bool) (test : CExpr) (body : CStm) : M (List Stmt) := do
  let (invs, rest) := peelInvariants body
  let invariants ← withSpec do
    invs.flatMapM fun inv => do
      let (pre, e) ← lowerExpr inv
      let obs ← specObligations "loop invariants" inv.span pre
      let label ← mkLabel "invariant" "loop invariant may not hold" inv.span
      pure (obs ++ [(label, e)])
  let (pc, c) ← lowerExpr test
  let bodyStms ← withScope (lowerStm usesHeap false rest)
  let testStms := flush pc
  let assumptions ← loopAssumptions usesHeap (testStms ++ bodyStms)
  if pc.isEmpty then
    pure ([.whileLoop c invariants (assumptions ++ bodyStms)] ++ assumptions)
  else
    -- C0 checks the invariant, then evaluates the condition. A condition with
    -- checks or calls is evaluated at the top of the loop body.
    let label ← freshName "__loop"
    let loopBody := assumptions ++ testStms ++ [.ifElse (mkNot c) [.exit label] []] ++ bodyStms
    pure ([.block label [.whileLoop (.boolLit true) invariants loopBody]] ++ assumptions)
end

/-! ## Procedures -/

private def bodyStm : List CStm → CStm
  | [] => .nop
  | [stm] => stm
  | stm :: rest => .seq stm (bodyStm rest)

private def resetProc (fname : String) : M Unit :=
  modify fun st => { st with
    procName := fname
    used := {}
    scopes := []
    varTaus := {}
    usedExit := false
    inSpec := false }

private def lowerSig (usesHeap : Bool) (f : C0VC.TypedAst.FunctionDef) : M FnSig := do
  resetProc f.fname
  let assigned := (assignedVars (bodyStm f.body)).filter fun n => f.params.any (·.2 == n)
  withScope do
    let params ← f.params.mapM fun (tau, name) => do
      let bt ← lowerTau none tau
      pure (bt, ← bindVar name bt, name)
    let resultName := (← get).cfg.resultName
    let ret ← match f.retType with
      | .void => pure none
      | tau => pure (some (← lowerTau none tau, resultName))
    let (requires, specs) ← withSpec do
      f.annotations.foldlM (init := ([], [])) fun (requires, specs) anno => do
        match anno with
        | .requires e =>
            let (pre, c) ← lowerExpr e
            let obs ← specObligations "preconditions" e.span pre
            let label ← mkLabel "requires" "precondition may not hold" e.span
            let clauses := obs ++ [(label, c)]
            pure (requires ++ clauses.map (fun (_, c) => (c, e.span)),
                  specs ++ clauses.map fun (l, c) => { kind := .requires, expr := c, label := some l })
        | .ensures e =>
            -- C0 tools disagree on whether a postcondition sees a parameter's
            -- entry value or its final value, so reject the ambiguous case.
            match (exprVars e).find? assigned.contains with
            | some name =>
                fail s!"postcondition mentions parameter {name}, which {f.fname} assigns; copy {name} into a local variable and assign that instead" e.span
            | none => pure ()
            let (pre, c) ← lowerExpr e
            let obs ← specObligations "postconditions" e.span pre
            let label ← mkLabel "ensures" "postcondition may not hold" e.span
            let clauses := obs ++ [(label, c)]
            pure (requires, specs ++ clauses.map fun (l, c) => { kind := .ensures, expr := c, label := some l })
        | .asserts e => fail "//@assert cannot annotate a function declaration" e.span
        | .loopInvariant e => fail "//@loop_invariant cannot annotate a function declaration" e.span
    let freeSpecs : List Spec :=
      if usesHeap then
        let refParams := params.filter (·.1 == .ref)
        [{ kind := .requires, expr := mkAnd heapWF zeroWF, free := true }] ++
        refParams.map fun (_, name, _) => { kind := .requires, expr := validRef (.var name), free := true }
      else []
    let boogieName := (← get).procNames.getD f.fname f.fname
    pure { boogieName, params, ret, requires, specs := freeSpecs ++ specs }

private def lowerBody (usesHeap : Bool) (f : C0VC.TypedAst.FunctionDef) (sig : FnSig) : M (List Stmt) := do
  resetProc f.fname
  withScope do
    let body := bodyStm f.body
    let assigned := assignedVars body
    let mut prelude := #[]
    for (tau, boogieName, c0Name) in sig.params do
      if assigned.contains c0Name then
        -- Boole parameters are immutable, and C0 postconditions see the
        -- parameter values from function entry. Mutate a local copy.
        modify fun st => { st with used := st.used.insert boogieName }
        let localName ← bindVar c0Name tau
        prelude := prelude.push (Stmt.declare localName tau) |>.push (.assign (.var localName) (.var boogieName))
      else
        bindAs c0Name boogieName tau
    let stms ← lowerStm usesHeap true body
    let stms := if (← get).usedExit then [Stmt.block bodyLabel stms] else stms
    pure (prelude.toList ++ stms)

/-! ## Effects -/

/-- Heap globals written and procedures called by some statements. -/
private partial def effectsOf (stms : List Stmt) : List String × List String :=
  stms.foldl
    (fun (mods, calls) stm =>
      match stm with
      | .assign lhs _ =>
          (mods ++ (assignedIn (.assign lhs (.boolLit true))).filter heapGlobals.contains, calls)
      | .call _ fname _ => (mods, calls ++ [fname])
      | .ifElse _ t f =>
          let (m1, c1) := effectsOf t
          let (m2, c2) := effectsOf f
          (mods ++ m1 ++ m2, calls ++ c1 ++ c2)
      | .whileLoop _ _ body | .block _ body =>
          let (m, c) := effectsOf body
          (mods ++ m, calls ++ c)
      | _ => (mods, calls))
    ([], [])

/-- Each procedure's `modifies` set, closed over the call graph. -/
private def computeModifies (procs : List (String × Option (List Stmt))) : Std.HashMap String (List String) :=
  let direct := procs.map fun (name, body) =>
    match body with
    | some stms => (name, effectsOf stms)
    | none => (name, ([], []))
  let init : Std.HashMap String (List String) :=
    direct.foldl (fun acc (name, (mods, _)) => acc.insert name mods.eraseDups) {}
  let step (mods : Std.HashMap String (List String)) : Std.HashMap String (List String) :=
    direct.foldl
      (fun acc (name, (own, callees)) =>
        let all := callees.foldl (fun all callee => all ++ mods.getD callee []) own
        acc.insert name all.eraseDups)
      mods
  let order (names : List String) := heapGlobals.filter names.contains
  let final := (List.range (procs.length + 1)).foldl (fun mods _ => step mods) init
  final.fold (fun acc name mods => acc.insert name (order mods)) {}

/-! ## Programs -/

private partial def tauUsesHeap : CTau → Bool
  | .ptr _ | .array _ | .struct _ | .null => true
  | _ => false

private partial def exprUsesHeap (e : CExpr) : Bool :=
  tauUsesHeap e.tau ||
  match e.node with
  | .binop _ l r => exprUsesHeap l || exprUsesHeap r
  | .ternary c t f => exprUsesHeap c || exprUsesHeap t || exprUsesHeap f
  | .call _ args => args.any exprUsesHeap
  | .length _ | .alloc _ | .allocArray .. | .deref _ | .arrAccess .. | .dot .. | .arrow .. => true
  | _ => false

private partial def stmUsesHeap : CStm → Bool
  | .assign lhs val => tauUsesHeap lhs.tau || exprUsesHeap val ||
      (match lhs.node with | .var _ => false | _ => true)
  | .ifLit c t f => exprUsesHeap c || stmUsesHeap t || stmUsesHeap f
  | .whileLit c body => exprUsesHeap c || stmUsesHeap body
  | .ret v => v.any exprUsesHeap
  | .seq a b => stmUsesHeap a || stmUsesHeap b
  | .declare _ tau init body => tauUsesHeap tau || init.any exprUsesHeap || stmUsesHeap body
  | .expr e | .assert e | .error e => exprUsesHeap e
  | .annotation (.requires e) | .annotation (.ensures e)
  | .annotation (.asserts e) | .annotation (.loopInvariant e) => exprUsesHeap e
  | .nop => false

private def annoUsesHeap : C0VC.TypedAst.Anno → Bool
  | .requires e | .ensures e | .asserts e | .loopInvariant e => exprUsesHeap e

private def programUsesHeap (program : C0VC.TypedAst.Program) : Bool :=
  program.any fun f =>
    tauUsesHeap f.retType || f.params.any (tauUsesHeap ·.1) ||
    f.annotations.any annoUsesHeap || f.body.any stmUsesHeap

def heapGlobalDecls (cfgUsesStrings : Bool) : List (String × Tau) :=
  let cells (tau : Tau) := Tau.map .int (.map .math tau)
  [ ("nextRef", .math)
  , ("len", .map .math .int)
  , ("hInt", .map .math (cells .int))
  , ("hBool", .map .math (cells .bool))
  , ("hRef", .map .math (cells .ref)) ] ++
  (if cfgUsesStrings then [("hStr", .map .math (cells .string))] else []) ++
  [ ("zeroInt", cells .int)
  , ("zeroBool", cells .bool)
  , ("zeroRef", cells .ref) ]

def runWithConfig (cfg : Config) (program : C0VC.TypedAst.Program) : Except String Program := do
  let structs := program.flatMap (·.structs)
  let layout ← Struct.computeLayout structs
  let usesHeap := programUsesHeap program
  let baseReserved : Std.HashSet String :=
    Std.HashSet.ofList (booleKeywords ++ heapGlobals ++ zeroMaps.map (·.2) ++
      [cfg.resultName, bodyLabel, "__r", "__e", "__i"])
  let procNames : Std.HashMap String String :=
    program.foldl
      (fun acc f =>
        let taken (n : String) := baseReserved.contains n || acc.toList.any (·.2 == n)
        acc.insert f.fname (pickName taken (sanitize f.fname)))
      {}
  let reserved := procNames.fold (fun acc _ name => acc.insert name) baseReserved
  let st0 : St := { cfg, layout, procNames, reserved }
  let action : M (List (C0VC.TypedAst.FunctionDef × FnSig × Option (List Stmt))) := do
    for f in program do
      let sig ← lowerSig usesHeap f
      modify fun st => { st with sigs := st.sigs.insert f.fname sig }
    program.mapM fun f => do
      let sig := (← get).sigs.getD f.fname default
      let body ← if f.external then pure none else some <$> lowerBody usesHeap f sig
      pure (f, sig, body)
  let (lowered, st) ← action.run st0
  let mods := computeModifies (lowered.map fun (_, sig, body) => (sig.boogieName, body))
  let procedures := lowered.map fun (_, sig, body) =>
    let modifies := mods.getD sig.boogieName []
    let resultFacts : List Spec :=
      match sig.ret with
      | some (.ref, name) => [{ kind := .ensures, expr := validRef (.var name), free := true }]
      | _ => []
    let frameFacts : List Spec :=
      if usesHeap && !modifies.isEmpty && body.isSome then
        [{ kind := .ensures, expr := heapWF, free := true }] ++
        (if modifies.contains "nextRef" then
          [{ kind := .ensures, expr := .mathCmp .ge nextRef (.old nextRef), free := true }]
        else [])
      else []
    let resultFacts := if usesHeap && body.isSome then resultFacts else []
    { name := sig.boogieName
      params := sig.params.map fun (tau, name, _) => (tau, name)
      ret := sig.ret
      specs := sig.specs ++ frameFacts ++ resultFacts
      modifies
      body }
  pure {
    intModel := cfg.intModel
    usesStrings := st.usesStrings
    globals := if usesHeap then heapGlobalDecls st.usesStrings else []
    procedures
    labels := st.labels }

def run (program : C0VC.TypedAst.Program) : Except String Program :=
  runWithConfig {} program

end C0VC.StrataBoole.Trans
