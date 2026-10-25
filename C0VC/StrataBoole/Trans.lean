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


structure Config where
  intModel : IntModel := .bv32
  resultName : String := "__result"

/-!
The heap is split into one map per kind of memory location (Burstall-Bornat):
`aInt`, `aBool`, `aRef` and `aStr` hold array elements and pointees by element
type, and every scalar leaf field of every struct gets its own map, such as
`h_node_next`. All of them are indexed by object and element index. Because
C0 is type safe, an object is only ever accessed through maps of its own type,
so separate maps never alias, and a write to one field leaves every other map
unchanged.
-/

/-- Maps for array elements and pointees, by C0 element type. -/
def arrayMaps : List (String × Tau) :=
  [ ("aInt", .int), ("aBool", .bool), ("aRef", .ref), ("aStr", .string) ]

/-- Zero-filled rows used to initialize fresh objects, by cell type. -/
def zeroMaps : List (Tau × String) :=
  [ (.int, "zeroInt"), (.bool, "zeroBool"), (.ref, "zeroRef") ]

def zeroMapNames : List String := zeroMaps.map (·.2)

def bodyLabel : String := "__body"

/-- The next unallocated object id. -/
def nextRefName : String := "nextRef"

/-- Object lengths, as C0 ints. -/
def lenName : String := "len"

/-- Quantified variables of the well-formedness facts: an object and an element index. -/
def objBinder : String := "__r"
def elemBinder : String := "__e"

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
  usesHeap : Bool := false
  /-- Pure C0 functions, mapped to the Boole functions that stand for them. -/
  specFns : Std.HashMap String String := {}
  /-- The map holding each struct leaf field, keyed by (struct, slot). -/
  fieldMaps : Std.HashMap (String × Nat) (String × Tau) := {}
  /-- Every heap global, in declaration and `modifies` order. -/
  heapNames : List String := []
  /-- Heap maps whose cells hold references. -/
  refMaps : List String := []

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

/-- The map holding array elements and pointees of a C0 type. -/
private def arrayMapOf (span? : Option SrcSpan) : CTau → M String
  | .int | .char => pure "aInt"
  | .bool => pure "aBool"
  | .ptr _ | .array _ | .null => pure "aRef"
  | .string => do
      modify fun st => { st with usesStrings := true }
      pure "aStr"
  | .struct name => fail s!"struct {name} values cannot be used directly; access a field instead" span?
  | .void => fail "void values are not stored in memory" span?

/-- The map holding the struct leaf field at `slot` of `root`. -/
private def fieldMapOf (span? : Option SrcSpan) (root : String) (slot : Nat) : M String := do
  match (← get).fieldMaps.get? (root, slot) with
  | some (name, tau) =>
      if tau == .string then modify fun st => { st with usesStrings := true }
      pure name
  | none => fail s!"internal error: struct {root} has no field in slot {slot}" span?

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

/-- A heap cell, addressed by its map, object and element index (0 for pointees). -/
private def heapAt (heap : String) (ref elem : Expr) : Expr :=
  .mapGet (.mapGet (.var heap) ref) elem

private def heapSlot (heap : String) (ref elem : Expr) : LValue :=
  .mapSlot (.mapGet (.var heap) ref) elem

private def lenOf (ref : Expr) : Expr :=
  .mapGet (.var lenName) ref

private def nextRef : Expr := .var nextRefName

/-- A reference is NULL or names an allocated object. -/
def validRef (r : Expr) : Expr :=
  .or (.eq r .null) (.and (.mathCmp .lt (.mathLit 0) r) (.mathCmp .lt r nextRef))

private def allocated (r : Expr) : Expr :=
  .and (.mathCmp .lt (.mathLit 0) r) (.mathCmp .lt r nextRef)

/--
Heap well-formedness. It holds in every reachable C0 state, because C0 has no
pointer arithmetic, no casts and no deallocation.
-/
def heapWF (refMaps : List String) : Expr :=
  let r := Expr.var objBinder
  let e := Expr.var elemBinder
  List.foldl mkAnd (.mathCmp .gt nextRef (.mathLit 0))
    ([ .eq (lenOf .null) (.intLit 0)
     , .forall [(objBinder, .math)] (mkImplies (allocated r) (.cmp .le (.intLit 0) (lenOf r))) ] ++
     refMaps.map fun m =>
       .forall [(objBinder, .math), (elemBinder, .int)] (mkImplies (allocated r) (validRef (heapAt m r e))))

def zeroWF : Expr :=
  let e := Expr.var elemBinder
  let zeroAt (name : String) := Expr.mapGet (.var name) e
  .forall [(elemBinder, .int)]
    (List.foldl mkAnd (.eq (zeroAt "zeroInt") (.intLit 0))
      [ .eq (zeroAt "zeroBool") (.boolLit false)
      , .eq (zeroAt "zeroRef") .null ])

/-- Formal parameter names for the heap maps of a spec function. -/
def heapFormal (heap : String) : String := "__" ++ heap

/-! ## Pre items -/

private def guardPre (guard : Expr) : Pre → Pre
  | .ob label cond => .ob label (mkImplies guard cond)
  | p => p

private def onlyObligations (pres : List Pre) : Bool :=
  pres.all fun
    | .ob .. => true
    | .stmt _ => false

private def stmtHasCall (s : Stmt) : Bool :=
  !s.calls.isEmpty

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

/-- The maps that hold the cells of a fresh object, with the zero row for each. -/
private def zeroRows (span? : Option SrcSpan) (elemTau : CTau) : M (List (String × String)) := do
  let cells ←
    match elemTau with
    | .struct name =>
        ((← get).layout.leaves.getD name []).zipIdx.mapM fun ((_, tau), slot) => do
          pure (← fieldMapOf span? name slot, ← lowerTau span? tau)
    | tau => pure [(← arrayMapOf span? tau, ← lowerTau span? tau)]
  -- Strings are opaque, so string cells start out unconstrained.
  pure (cells.filterMap fun (heap, tau) => (zeroMaps.lookup tau).map (heap, ·))

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
      let (pre, heap, ref, elem) ← lowerAddr e
      pure (pre, heapAt heap ref elem)

/-- Lower a scalar memory access to its heap map, object and element index. -/
partial def lowerAddr (e : CExpr) : M (List Pre × String × Expr × Expr) := do
  let span := e.span
  match e.node with
  | .deref ptr => do
      let (pp, p) ← lowerExpr ptr
      let nullCheck ← obligation "null" "pointer may be NULL" span (.neq p .null)
      pure (pp ++ [nullCheck], ← arrayMapOf span e.tau, p, .intLit 0)
  | .arrAccess arr index => do
      let (pre, ref, idx) ← lowerIndex span arr index
      pure (pre, ← arrayMapOf span e.tau, ref, idx)
  | .dot struct field => do
      let (pre, ref, elem, base, root, sname) ← lowerStructBase struct
      let info ← fieldInfo span sname field
      pure (pre, ← fieldMapOf span root (base + info.offset), ref, elem)
  | .arrow structPtr field => do
      let (pp, p) ← lowerExpr structPtr
      let nullCheck ← obligation "null" "pointer may be NULL" span (.neq p .null)
      let root ← structName span structPtr.tau
      let info ← fieldInfo span root field
      pure (pp ++ [nullCheck], ← fieldMapOf span root info.offset, p, .intLit 0)
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
Lower a struct-typed expression to the object and element index that hold it,
the slot of its first leaf within the outermost struct (the root), the root
struct, and its own struct type.
-/
partial def lowerStructBase (e : CExpr) : M (List Pre × Expr × Expr × Nat × String × String) := do
  let span := e.span
  let sname ← structName span e.tau
  match e.node with
  | .deref ptr => do
      let (pp, p) ← lowerExpr ptr
      let nullCheck ← obligation "null" "pointer may be NULL" span (.neq p .null)
      pure (pp ++ [nullCheck], p, .intLit 0, 0, sname, sname)
  | .arrAccess arr index => do
      let (pre, ref, idx) ← lowerIndex span arr index
      pure (pre, ref, idx, 0, sname, sname)
  | .dot struct field => do
      let (pre, ref, elem, base, root, outer) ← lowerStructBase struct
      let info ← fieldInfo span outer field
      pure (pre, ref, elem, base + info.offset, root, sname)
  | .arrow structPtr field => do
      let (pp, p) ← lowerExpr structPtr
      let nullCheck ← obligation "null" "pointer may be NULL" span (.neq p .null)
      let root ← structName span structPtr.tau
      let info ← fieldInfo span root field
      pure (pp ++ [nullCheck], p, .intLit 0, info.offset, root, sname)
  | _ => fail "struct values can only be used through a field access" span

partial def lowerCall (span? : Option SrcSpan) (fname : String) (args : List CExpr) (retTau : CTau) :
    M (List Pre × Expr) := do
  let sig ← match (← get).sigs.get? fname with
    | some sig => pure sig
    | none => fail s!"internal error: unknown function {fname}" span?
  if (← get).inSpec then
    return ← lowerSpecCall span? fname sig args
  let lowered ← args.mapM fun arg => do
    let (pre, e) ← lowerExpr arg
    pure (← lowerTau arg.span arg.tau, pre, e)
  let (pre, argExprs) ← sequenceOperands lowered
  let σ := (sig.params.map (·.2.1)).zip argExprs
  let preconditions ← sig.requires.mapM fun (req, reqSpan?) => do
    let declared := match reqSpan? with
      | some span => s!" (declared at line {span.startLoc.line})"
      | none => ""
    obligation "precondition" s!"precondition of {fname}{declared} may not hold" span? (req.subst σ)
  match retTau with
  | .void =>
      pure (pre ++ preconditions ++ [.stmt (.call none sig.boogieName argExprs)], .boolLit true)
  | _ =>
      let tau ← lowerTau span? retTau
      let tmp ← freshTemp "call" tau
      pure (pre ++ preconditions ++
        [.stmt (.declare tmp tau), .stmt (.call (some tmp) sig.boogieName argExprs)], .var tmp)

/-- A call inside a contract applies the Boole function of a pure C0 function. -/
partial def lowerSpecCall (span? : Option SrcSpan) (fname : String) (sig : FnSig) (args : List CExpr) :
    M (List Pre × Expr) := do
  let st ← get
  let some fnName := st.specFns.get? fname
    | let reason := if sig.ret.isNone then "returns void"
        else "writes memory or allocates, directly or through a call"
      fail s!"contracts can only call pure functions, but {fname} {reason}" span?
  let lowered ← args.mapM lowerExpr
  let argExprs := lowered.map (·.2)
  let σ := (sig.params.map (·.2.1)).zip argExprs
  let preconditions ← sig.requires.mapM fun (req, reqSpan?) => do
    let declared := match reqSpan? with
      | some span => s!" (declared at line {span.startLoc.line})"
      | none => ""
    obligation "precondition" s!"precondition of {fname}{declared} may not hold" span? (req.subst σ)
  -- The heap maps the function reads are added once they are known.
  pure (lowered.flatMap (·.1) ++ preconditions, .fnCall fnName argExprs)

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
  let rows ← zeroRows span? elemTau
  let zeroes := rows.map fun (heap, zero) => Stmt.assign (.mapSlot (.var heap) (.var tmp)) (.var zero)
  let stms :=
    [ Stmt.declare tmp .ref
    , .assign (.var tmp) nextRef
    , .assign (.var nextRefName) (mathAdd nextRef (.mathLit 1))
    , .assign (.mapSlot (.var lenName) (.var tmp)) length ] ++ zeroes
  pure (pre ++ stms.map .stmt, .var tmp)
end

/-! ## Statements -/

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
  let touchesHeap := body.any stmtHasCall || assigned.any st.heapNames.contains
  let refLocals := assigned.filter fun name =>
    !declared.contains name && st.varTaus.get? name == some .ref
  let wf := if touchesHeap then [Stmt.assume (heapWF st.refMaps)] else []
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
      let (pa, heap, ref, elem) ← lowerAddr lhs.toExpr
      let (pv, v) ← lowerExpr val
      let (pa, ref, elem) ←
        if hasCall pv then do
          let (pa, ref) ← snapshot .ref pa ref
          let (pa, elem) ← snapshot .int pa elem
          pure (pa, ref, elem)
        else
          pure (pa, ref, elem)
      pure (flush pa ++ flush pv ++ [.assign (heapSlot heap ref elem) v])

partial def lowerWhile (usesHeap : Bool) (test : CExpr) (body : CStm) : M (List Stmt) := do
  let (invs, rest) := body.peelInvariants
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
            let (pre, c) ← lowerExpr e
            let obs ← specObligations "postconditions" e.span pre
            let label ← mkLabel "ensures" "postcondition may not hold" e.span
            let clauses := obs ++ [(label, c)]
            -- A header function has no body to check its postcondition
            -- against; its contract is trusted.
            pure (requires, specs ++ clauses.map fun (l, c) =>
              { kind := .ensures, expr := c, label := some l, free := f.external })
        | .asserts e => fail "//@assert cannot annotate a function declaration" e.span
        | .loopInvariant e => fail "//@loop_invariant cannot annotate a function declaration" e.span
    let refMaps := (← get).refMaps
    let freeSpecs : List Spec :=
      if usesHeap then
        let refParams := params.filter (·.1 == .ref)
        [{ kind := .requires, expr := mkAnd (heapWF refMaps) zeroWF, free := true }] ++
        refParams.map fun (_, name, _) => { kind := .requires, expr := validRef (.var name), free := true }
      else []
    let boogieName := (← get).procNames.getD f.fname f.fname
    pure { boogieName, params, ret, requires, specs := freeSpecs ++ specs }

private def lowerBody (usesHeap : Bool) (f : C0VC.TypedAst.FunctionDef) (sig : FnSig) : M (List Stmt) := do
  resetProc f.fname
  withScope do
    let body := bodyStm f.body
    let assigned := body.assignedVars
    let mut prelude := #[]
    for (tau, boogieName, c0Name) in sig.params do
      if assigned.contains c0Name then
        -- Boole parameters are immutable, so mutate a local copy. The
        -- typechecker guarantees the parameter does not occur in @ensures.
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
private partial def effectsOf (heapNames : List String) (stms : List Stmt) : List String × List String :=
  stms.foldl
    (fun (mods, calls) stm =>
      match stm with
      | .assign lhs _ =>
          (mods ++ (assignedIn (.assign lhs (.boolLit true))).filter heapNames.contains, calls)
      | .call _ fname _ => (mods, calls ++ [fname])
      | .ifElse _ t f =>
          let (m1, c1) := effectsOf heapNames t
          let (m2, c2) := effectsOf heapNames f
          (mods ++ m1 ++ m2, calls ++ c1 ++ c2)
      | .whileLoop _ _ body | .block _ body =>
          let (m, c) := effectsOf heapNames body
          (mods ++ m, calls ++ c)
      | _ => (mods, calls))
    ([], [])

/--
Close per-procedure sets over the call graph: each procedure's set gains its
callees' sets. Nodes are (name, own items, callees); results keep the order of
`items`, which lists every item that can occur.
-/
def closeOverCalls (items : List String) (nodes : List (String × List String × List String)) :
    Std.HashMap String (List String) := Id.run do
  let mut sets : Std.HashMap String (List String) :=
    nodes.foldl (fun acc (name, own, _) => acc.insert name own) {}
  -- A set can only grow through a path of at most `nodes.length` calls.
  for _ in [0:nodes.length + 1] do
    sets := nodes.foldl
      (fun acc (name, own, callees) =>
        let all := callees.foldl (fun all callee => all ++ sets.getD callee []) own
        acc.insert name (items.filter all.contains))
      sets
  return sets

/-- Each procedure's `modifies` set, closed over the call graph. -/
private def computeModifies (heapNames : List String) (procs : List (String × Option (List Stmt))) :
    Std.HashMap String (List String) :=
  closeOverCalls heapNames <| procs.map fun (name, body) =>
    let (mods, calls) := (body.map (effectsOf heapNames)).getD ([], [])
    (name, mods, calls)

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

private def leafTau : CTau → Tau
  | .int | .char => .int
  | .bool => .bool
  | .string => .string
  | _ => .ref

/-- The heap globals of a program. -/
structure HeapLayout where
  fieldMaps : Std.HashMap (String × Nat) (String × Tau) := {}
  /-- Declarations of all heap globals, including the zero rows. -/
  decls : List (String × Tau) := []
  /-- Heap globals that procedures can modify, in `modifies` order. -/
  names : List String := []
  refMaps : List String := []

def heapLayout (layout : Struct.Layout) (structs : List String) (usesStrings : Bool)
    (reserved : Std.HashSet String) : HeapLayout := Id.run do
  let row (tau : Tau) := Tau.map .math (.map .int tau)
  let arrays := arrayMaps.filter fun (_, tau) => usesStrings || tau != .string
  let mut taken := reserved
  let mut fieldMaps : Std.HashMap (String × Nat) (String × Tau) := {}
  let mut fieldDecls : Array (String × Tau) := #[]
  for sname in structs.eraseDups do
    for ((path, tau), slot) in (layout.leaves.getD sname []).zipIdx do
      let name := pickName taken.contains (sanitize ("h_" ++ String.intercalate "_" (sname :: path)))
      taken := taken.insert name
      fieldMaps := fieldMaps.insert (sname, slot) (name, leafTau tau)
      fieldDecls := fieldDecls.push (name, leafTau tau)
  let maps := arrays ++ fieldDecls.toList
  return {
    fieldMaps
    decls := [(nextRefName, .math), (lenName, .map .math .int)] ++
      maps.map (fun (name, tau) => (name, row tau)) ++
      zeroMaps.map fun (tau, name) => (name, Tau.map .int tau)
    names := [nextRefName, lenName] ++ maps.map (·.1)
    refMaps := (maps.filter (·.2 == .ref)).map (·.1) }

/-! ## Spec functions

A pure C0 function (one that neither writes memory nor allocates, directly or
through calls) gets a Boole `function` so that contracts can call it. The
function takes the heap maps it may read as extra arguments. Its procedure gets
the free postcondition `\result == f_fn(heap, args)`, which links calls in code
to calls in contracts; it holds because a pure C0 function is deterministic.

The function body is
- definitional when the C0 body is in expression form (returns, `if`, local
  declarations and assignments), or is the standard search loop
  `for (int i = lo; i < hi; i++) if (c) return false; return true;`
  (a `forall`) or its dual returning `true` from the loop (an `exists`);
- uninterpreted otherwise, including for recursive functions.
-/

private partial def stmWritesMemory : CStm → Bool
  | .assign lhs _ =>
      match lhs.node with
      | .var _ => false
      | _ => true
  | .ifLit _ t f => stmWritesMemory t || stmWritesMemory f
  | .whileLit _ body => stmWritesMemory body
  | .seq a b => stmWritesMemory a || stmWritesMemory b
  | .declare _ _ _ body => stmWritesMemory body
  | _ => false

private def isAlloc (e : CExpr) : Bool :=
  match e.node with
  | .alloc _ | .allocArray .. => true
  | _ => false

/-- Functions that neither write memory nor allocate, directly or through calls. -/
def pureFunctions (program : C0VC.TypedAst.Program) : Std.HashSet String := Id.run do
  let info := program.map fun f =>
    let exprs := f.body.flatMap C0VC.TypedAst.Stm.exprs
    let direct := !f.external && (f.body.any stmWritesMemory || exprs.any (·.any isAlloc))
    (f.fname, direct, exprs.flatMap C0VC.TypedAst.TypedExpr.callees)
  let mut pureFns : Std.HashSet String :=
    Std.HashSet.ofList (info.filterMap fun (name, direct, _) => if direct then none else some name)
  for _ in [0:program.length + 1] do
    pureFns := info.foldl
      (fun acc (name, _, callees) =>
        if acc.contains name && callees.all acc.contains then acc else acc.erase name)
      pureFns
  return pureFns

private partial def stmAnnoExprs : CStm → List CExpr
  | .annotation a => [a.expr]
  | .ifLit _ t f => stmAnnoExprs t ++ stmAnnoExprs f
  | .whileLit _ body => stmAnnoExprs body
  | .seq a b => stmAnnoExprs a ++ stmAnnoExprs b
  | .declare _ _ _ body => stmAnnoExprs body
  | _ => []

/--
Pure functions that contracts use: those called in a contract or annotation,
and the pure functions their bodies call.
-/
def contractFunctions (program : C0VC.TypedAst.Program) (pureFns : Std.HashSet String) :
    Std.HashSet String := Id.run do
  let callees : Std.HashMap String (List String) :=
    program.foldl (fun acc f => acc.insert f.fname ((f.body.flatMap C0VC.TypedAst.Stm.exprs).flatMap C0VC.TypedAst.TypedExpr.callees)) {}
  let seeds := program.flatMap fun f =>
    ((f.annotations.map C0VC.TypedAst.Anno.expr) ++ f.body.flatMap stmAnnoExprs).flatMap C0VC.TypedAst.TypedExpr.callees
  let mut needed : Std.HashSet String := {}
  let mut work := seeds.filter pureFns.contains
  for _ in [0:program.length + 1] do
    let fresh := work.filter (!needed.contains ·)
    needed := fresh.foldl (·.insert ·) needed
    work := (fresh.flatMap (callees.getD · [])).filter pureFns.contains
  return needed

/-- Order functions so that functions called in a contract come before its function. -/
private def orderByContractCalls (program : C0VC.TypedAst.Program) : List C0VC.TypedAst.FunctionDef := Id.run do
  let byName : Std.HashMap String C0VC.TypedAst.FunctionDef :=
    program.foldl (fun acc f => acc.insert f.fname f) {}
  let mut visited : Std.HashSet String := {}
  let mut order : Array C0VC.TypedAst.FunctionDef := #[]
  -- Iterative DFS; contract call graphs are tiny, so repeated passes are fine.
  for _ in [0:program.length + 1] do
    for f in program do
      if visited.contains f.fname then continue
      let deps := (f.annotations.map C0VC.TypedAst.Anno.expr).flatMap C0VC.TypedAst.TypedExpr.callees
      if deps.all (fun d => visited.contains d || d == f.fname || !byName.contains d) then
        visited := visited.insert f.fname
        order := order.push f
  for f in program do
    if !visited.contains f.fname then
      order := order.push f
  return order.toList

private partial def flatItems : CStm → List CStm
  | .seq a b => flatItems a ++ flatItems b
  | .declare x tau init body => [.declare x tau init .nop] ++ flatItems body
  | .nop | .annotation _ => []
  | s => [s]

private def boolLitOf (e : CExpr) : Option Bool :=
  match e.node with
  | .trueLit => some true
  | .falseLit => some false
  | _ => none

private def isVar (name : String) (e : CExpr) : Bool :=
  match e.node with
  | .var n => n == name
  | _ => false

private def isIncrement (name : String) : CStm → Bool
  | .assign lhs val =>
      match lhs.node, val.node with
      | .var n, .binop .plus v one =>
          n == name && isVar name v &&
            (match one.node with
              | .intLit 1 => true
              | _ => false)
      | _, _ => false
  | _ => false

/--
Recognize `for (int i = lo; i < hi; i++) if (c) return b; return !b;` and
return the C0 loop variable, `lo`, `hi`, whether the bound is inclusive, `c`,
and `b`.
-/
private def searchLoop? (body : CStm) : Option (String × CExpr × CExpr × Bool × CExpr × Bool) :=
  match flatItems body with
  | [.declare i _ (some lo) .nop, .whileLit test loopBody, .ret (some after)] =>
      match test.node, flatItems loopBody, boolLitOf after with
      | .binop op v hi, [.ifLit c thenS elseS, incr], some afterB =>
          let inclusive := match op with
            | .lte => some true
            | .lt => some false
            | _ => none
          match inclusive, flatItems thenS, flatItems elseS with
          | some incl, [.ret (some inLoop)], [] =>
              if isVar i v && isIncrement i incr && boolLitOf inLoop == some !afterB then
                some (i, lo, hi, incl, c, afterB)
              else none
          | _, _, _ => none
      | _, _, _ => none
  | _ => none

private def notExpressionForm : M α := throw "not in expression form"

/-- The value of a function body in expression form, given the value of what follows. -/
private partial def stmtThen (stm : CStm) (rest : Option Expr) : M (Option Expr) := do
  match stm with
  | .nop | .annotation _ | .assert _ | .error _ | .expr _ => pure rest
  | .ret (some e) => some <$> (Prod.snd <$> lowerExpr e)
  | .ret none => pure none
  | .seq a b => do
      let restB ← stmtThen b rest
      stmtThen a restB
  | .declare x tau init body => withScope do
      let bt ← lowerTau none tau
      let initE ← init.mapM fun e => Prod.snd <$> lowerExpr e
      let n ← bindVar x bt
      let r ← stmtThen body rest
      pure (r.map fun r => match initE with
        | some ie => r.subst [(n, ie)]
        | none => r)
  | .assign lhs val =>
      match lhs.node with
      | .var x => do
          let n ← lookupVar x lhs.span
          let (_, v) ← lowerExpr val
          pure (rest.map (·.subst [(n, v)]))
      | _ => notExpressionForm
  | .ifLit c t f => do
      let (_, c') ← lowerExpr c
      let tr ← withScope (stmtThen t rest)
      let fr ← withScope (stmtThen f rest)
      match tr, fr with
      | some a, some b => pure (some (mkIte c' a b))
      | _, _ => notExpressionForm
  | .whileLit .. => notExpressionForm

private def attempt (m : M α) : M (Option α) := do
  let saved ← get
  try
    some <$> m
  catch _ =>
    set saved
    pure none

/-- The definitional body of a spec function, over the heap formals and parameters. -/
private def specBody (f : C0VC.TypedAst.FunctionDef) (sig : FnSig) : M (Option Expr) := do
  let saved ← get
  resetProc f.fname
  let result ← attempt <| withSpec <| withScope do
    for (tau, boogieName, c0Name) in sig.params do
      bindAs c0Name boogieName tau
    let body := bodyStm f.body
    match searchLoop? body with
    | some (i, lo, hi, inclusive, c, afterB) =>
        let (_, lo') ← lowerExpr lo
        let (_, hi') ← lowerExpr hi
        withScope do
          let n ← bindVar i .int
          let (_, c') ← lowerExpr c
          let range := Expr.and (.cmp .le lo' (.var n))
            (.cmp (if inclusive then .le else .lt) (.var n) hi')
          if afterB then
            pure (some (Expr.forall [(n, .int)] (mkImplies range (mkNot c'))))
          else
            pure (some (Expr.exists [(n, .int)] (mkAnd range c')))
    | none => stmtThen body none
  -- Obligations met while lowering a definition are checked in the procedure.
  modify fun st => { st with labels := saved.labels, usedLabels := saved.usedLabels }
  pure result.join

/-- Drop bodies that depend on themselves, and order definitions before their uses. -/
private def orderFunctions (fns : List Function) : List Function := Id.run do
  let mut emitted : Std.HashSet String := Std.HashSet.ofList (fns.filter (·.body.isNone) |>.map (·.name))
  let mut out : Array Function := (fns.filter (·.body.isNone)).toArray
  let mut pending := fns.filter (·.body.isSome)
  for _ in [0:fns.length + 1] do
    let (ready, waiting) := pending.partition fun fn =>
      (fn.body.map Expr.fnCalls |>.getD []).all emitted.contains
    for fn in ready do
      emitted := emitted.insert fn.name
      out := out.push fn
    pending := waiting
  -- Recursive definitions stay uninterpreted.
  return (pending.map ({ · with body := none })) ++ out.toList

/-! ## Heap arguments of spec functions

A spec function takes as arguments exactly the heap maps that its C0 body
reads, directly or through calls. Its value then only changes when one of
those maps changes, so writes to unrelated fields keep facts such as
`is_sorted(A, 0, n)`. Read sets are computed after lowering, and every
application is then given its heap arguments.
-/

/--
The heap maps each procedure reads, closed over calls; keyed by procedure
name. A function without a body is assumed to read every heap map.
-/
private def computeReads (heapNames : List String) (fnToProc : Std.HashMap String String)
    (procs : List (String × Option (List Stmt))) : Std.HashMap String (List String) := Id.run do
  let readable := heapNames.filter (· != nextRefName)
  let direct := procs.map fun (name, body) =>
    match body with
    | none => (name, readable, ([] : List String))
    | some stms =>
        let exprs := stms.flatMap Stmt.exprs
        let vars := exprs.flatMap Expr.freeVars
        let fnCallees := (exprs.flatMap Expr.fnCalls).filterMap fnToProc.get?
        (name, readable.filter vars.contains, stms.flatMap Stmt.calls ++ fnCallees)
  return closeOverCalls readable direct

/-- Give one application of a spec function its heap arguments. -/
private def heapArgsAt (fnReads : Std.HashMap String (List String)) (formal : Bool) : Expr → Expr
  | .fnCall name args =>
      let heaps := (fnReads.getD name []).map fun h => Expr.var (if formal then heapFormal h else h)
      .fnCall name (heaps ++ args)
  | e => e

/-- Give every application of a spec function in an expression its heap arguments. -/
private def addHeapArgs (fnReads : Std.HashMap String (List String)) (formal : Bool) : Expr → Expr :=
  Expr.mapBottomUp (heapArgsAt fnReads formal)

private partial def stmDeclTaus : CStm → List CTau
  | .declare _ tau _ body => tau :: stmDeclTaus body
  | .ifLit _ t f => stmDeclTaus t ++ stmDeclTaus f
  | .whileLit _ body => stmDeclTaus body
  | .seq a b => stmDeclTaus a ++ stmDeclTaus b
  | _ => []

private def programUsesStrings (program : C0VC.TypedAst.Program) : Bool :=
  let isString (tau : CTau) : Bool := match tau with
    | .string => true
    | _ => false
  program.any fun f =>
    isString f.retType || f.params.any (isString ·.1) ||
    f.body.any (fun stm => (stmDeclTaus stm).any isString ||
      (C0VC.TypedAst.Stm.exprs stm).any (·.any (isString ·.tau)))

def runWithConfig (cfg : Config) (program : C0VC.TypedAst.Program) : Except String Program := do
  let structs := program.flatMap (·.structs)
  let layout ← Struct.computeLayout structs
  let usesHeap := programUsesHeap program
  let structNames := structs.map (·.1)
  let usesStrings := programUsesStrings program ||
    structNames.any fun n => (layout.leaves.getD n []).any fun (_, tau) => match tau with
      | .string => true
      | _ => false
  let fixedReserved : Std.HashSet String :=
    Std.HashSet.ofList (booleKeywords ++ [nextRefName, lenName] ++ arrayMaps.map (·.1) ++ zeroMapNames ++
      [cfg.resultName, bodyLabel, objBinder, elemBinder])
  let heap := heapLayout layout structNames usesStrings fixedReserved
  let baseReserved : Std.HashSet String :=
    (heap.names ++ heap.names.map heapFormal).foldl (·.insert ·) fixedReserved
  let procNames : Std.HashMap String String :=
    program.foldl
      (fun acc f =>
        let taken (n : String) := baseReserved.contains n || acc.toList.any (·.2 == n)
        acc.insert f.fname (pickName taken (sanitize f.fname)))
      {}
  let reserved := procNames.fold (fun acc _ name => acc.insert name) baseReserved
  let pureFns := pureFunctions program
  let neededFns := contractFunctions program pureFns
  let specFns : Std.HashMap String String :=
    program.foldl
      (fun acc f =>
        let isVoid := match f.retType with
          | .void => true
          | _ => false
        if neededFns.contains f.fname && !isVoid then
          let base := procNames.getD f.fname f.fname ++ "_fn"
          let taken (n : String) := reserved.contains n || acc.toList.any (·.2 == n)
          acc.insert f.fname (pickName taken base)
        else acc)
      {}
  let reserved := specFns.fold (fun acc _ name => acc.insert name) reserved
  let st0 : St := {
    cfg, layout, procNames, reserved, specFns, usesHeap, usesStrings
    fieldMaps := heap.fieldMaps, heapNames := heap.names, refMaps := heap.refMaps }
  let action : M (List (C0VC.TypedAst.FunctionDef × FnSig × Option (List Stmt)) × List Function) := do
    for f in orderByContractCalls program do
      let sig ← lowerSig usesHeap f
      modify fun st => { st with sigs := st.sigs.insert f.fname sig }
    let functions ← program.filterMapM fun f => do
      let some fnName := (← get).specFns.get? f.fname | pure none
      let sig := (← get).sigs.getD f.fname default
      let body ← if f.external then pure none else specBody f sig
      let ret := (sig.ret.map (·.1)).getD .int
      pure (some { name := fnName, params := sig.params.map (fun (t, n, _) => (t, n)), ret, body })
    let procs ← program.mapM fun f => do
      let sig := (← get).sigs.getD f.fname default
      let body ← if f.external then pure none else some <$> lowerBody usesHeap f sig
      pure (f, sig, body)
    pure (procs, orderFunctions functions)
  let ((lowered, functions), st) ← action.run st0
  let mods := computeModifies heap.names (lowered.map fun (_, sig, body) => (sig.boogieName, body))
  let fnToProc : Std.HashMap String String :=
    lowered.foldl (fun acc (f, sig, _) => match st.specFns.get? f.fname with
      | some fn => acc.insert fn sig.boogieName
      | none => acc) {}
  let readableHeap := if usesHeap then heap.names else []
  let procReads := computeReads readableHeap fnToProc (lowered.map fun (_, sig, body) => (sig.boogieName, body))
  let fnReads : Std.HashMap String (List String) :=
    functions.foldl
      (fun acc fn =>
        let fromProc := procReads.getD (fnToProc.getD fn.name "") []
        let fromBody := (fn.body.map Expr.freeVars).getD []
        acc.insert fn.name (heap.names.filter fun h => fromProc.contains h || fromBody.contains h))
      {}
  let heapTau (h : String) := (heap.decls.lookup h).getD .math
  let functions := functions.map fun fn =>
    let reads := fnReads.getD fn.name []
    let toFormal := reads.map fun h => (h, Expr.var (heapFormal h))
    { fn with
      params := reads.map (fun h => (heapTau h, heapFormal h)) ++ fn.params
      body := fn.body.map fun b => addHeapArgs fnReads true (b.subst toFormal) }
  let procedures := lowered.map fun (f, sig, body) =>
    let modifies := mods.getD sig.boogieName []
    let linkFacts : List Spec :=
      match st.specFns.get? f.fname, sig.ret with
      | some fnName, some (_, resultName) =>
          let args := sig.params.map fun (_, name, _) => Expr.var name
          [{ kind := .ensures, expr := .eq (.var resultName) (.fnCall fnName args), free := true }]
      | _, _ => []
    let resultFacts : List Spec :=
      match sig.ret with
      | some (.ref, name) => [{ kind := .ensures, expr := validRef (.var name), free := true }]
      | _ => []
    let frameFacts : List Spec :=
      if usesHeap && !modifies.isEmpty && body.isSome then
        [{ kind := .ensures, expr := heapWF heap.refMaps, free := true }] ++
        (if modifies.contains nextRefName then
          [{ kind := .ensures, expr := .mathCmp .ge nextRef (.old nextRef), free := true }]
        else [])
      else []
    let resultFacts := if usesHeap && body.isSome then resultFacts else []
    { name := sig.boogieName
      params := sig.params.map fun (tau, name, _) => (tau, name)
      ret := sig.ret
      specs := (sig.specs ++ frameFacts ++ resultFacts ++ linkFacts).map fun spec =>
        { spec with expr := addHeapArgs fnReads false spec.expr }
      modifies
      body := body.map (·.map (Stmt.mapExprs (addHeapArgs fnReads false))) }
  pure {
    intModel := cfg.intModel
    usesStrings := st.usesStrings
    globals := if usesHeap then heap.decls else []
    functions
    procedures
    labels := st.labels }

def run (program : C0VC.TypedAst.Program) : Except String Program :=
  runWithConfig {} program

end C0VC.StrataBoole.Trans
