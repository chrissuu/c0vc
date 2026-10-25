import C0VC.Utils.SrcSpan

namespace C0VC.StrataBoole

/--
How C0 `int` values are represented in Boole.

- `bv32`: 32-bit bitvectors. Arithmetic wraps exactly like C0, so a verified
  program is verified under the real C0 semantics. Nonlinear arithmetic over
  bitvectors can be hard for SMT solvers.
- `checked`: unbounded mathematical integers. Every arithmetic operation that
  could leave the 32-bit range gets an overflow proof obligation, so a verified
  program never overflows and therefore behaves the same as under `bv32`.
  Contracts are interpreted over mathematical integers.
-/
inductive IntModel where
  | bv32
  | checked
deriving Inhabited, BEq, Repr

inductive Tau where
  /-- A C0 `int` or `char`; rendered according to the `IntModel`. -/
  | int
  | bool
  /-- An object reference: `0` is NULL, valid objects are `0 < r < nextRef`. -/
  | ref
  /-- A mathematical integer, used for object ids and field offsets. -/
  | math
  /-- An opaque C0 string. -/
  | string
  | map (key val : Tau)
deriving Inhabited, BEq, Repr

/-- Arithmetic and bitwise operators over C0 ints. -/
inductive ArithOp where
  | add | sub | mul | div | mod
  | bitAnd | bitOr | xor | shl | shr
deriving Inhabited, BEq, Repr

inductive CmpOp where
  | lt | le | gt | ge
deriving Inhabited, BEq, Repr

inductive Expr where
  | var (name : String)
  /-- A C0 int literal. -/
  | intLit (val : Int)
  /-- A mathematical integer literal. -/
  | mathLit (val : Int)
  | boolLit (val : Bool)
  | null
  /-- C0 int arithmetic, rendered according to the `IntModel`. -/
  | arith (op : ArithOp) (lhs rhs : Expr)
  /-- Signed comparison of C0 ints. -/
  | cmp (op : CmpOp) (lhs rhs : Expr)
  /-- Mathematical integer arithmetic (only `add`, `sub` and `mul`). -/
  | mathArith (op : ArithOp) (lhs rhs : Expr)
  | mathCmp (op : CmpOp) (lhs rhs : Expr)
  | eq (lhs rhs : Expr)
  | neq (lhs rhs : Expr)
  | and (lhs rhs : Expr)
  | or (lhs rhs : Expr)
  | not (e : Expr)
  | implies (lhs rhs : Expr)
  | ite (test thenVal elseVal : Expr)
  | mapGet (map key : Expr)
  | old (e : Expr)
  | forall (binders : List (String × Tau)) (body : Expr)
deriving Inhabited, BEq, Repr

inductive LValue where
  | var (name : String)
  | mapSlot (map key : Expr)
deriving Inhabited, Repr

inductive Stmt where
  | declare (name : String) (tau : Tau)
  | assign (lhs : LValue) (rhs : Expr)
  /--
  A C0 check. C0 aborts when a check fails, so the condition is assumed after
  it is asserted.
  -/
  | check (label : String) (expr : Expr)
  | assume (expr : Expr)
  | havoc (name : String)
  | ifElse (test : Expr) (thenBody elseBody : List Stmt)
  | whileLoop (test : Expr) (invariants : List (String × Expr)) (body : List Stmt)
  | call (lhs : Option String) (fname : String) (args : List Expr)
  | block (label : String) (body : List Stmt)
  | exit (label : String)
deriving Inhabited, Repr

inductive SpecKind where
  | requires
  | ensures
deriving Inhabited, BEq, Repr

structure Spec where
  kind : SpecKind
  expr : Expr
  label : Option String := none
  /-- Free specs are assumed but never checked. -/
  free : Bool := false
deriving Inhabited, Repr

structure Procedure where
  name : String
  params : List (Tau × String)
  ret : Option (Tau × String)
  specs : List Spec
  modifies : List String := []
  body : Option (List Stmt)
deriving Inhabited, Repr

/-- What a labelled proof obligation means at the C0 level. -/
structure LabelInfo where
  label : String
  message : String
  procedure : String
  span : Option C0VC.Utils.SrcSpan.SrcSpan := none
deriving Inhabited, Repr

structure Program where
  intModel : IntModel := .bv32
  /-- Whether the program uses the opaque C0 string type. -/
  usesStrings : Bool := false
  globals : List (String × Tau) := []
  procedures : List Procedure
  labels : Array LabelInfo := #[]
deriving Inhabited, Repr

end C0VC.StrataBoole
