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
  | exists (binders : List (String × Tau)) (body : Expr)
  /-- Application of a Boole `function`. -/
  | fnCall (name : String) (args : List Expr)
deriving Inhabited, BEq, Repr

namespace Expr

/-- The immediate subexpressions of an expression. -/
def children : Expr → List Expr
  | .arith _ a b | .cmp _ a b | .mathArith _ a b | .mathCmp _ a b
  | .eq a b | .neq a b | .and a b | .or a b | .implies a b | .mapGet a b => [a, b]
  | .not e | .old e | .forall _ e | .exists _ e => [e]
  | .ite c t f => [c, t, f]
  | .fnCall _ args => args
  | _ => []

/-- Rebuild an expression with `f` applied to each immediate subexpression. -/
def mapChildren (f : Expr → Expr) : Expr → Expr
  | .arith op a b => .arith op (f a) (f b)
  | .cmp op a b => .cmp op (f a) (f b)
  | .mathArith op a b => .mathArith op (f a) (f b)
  | .mathCmp op a b => .mathCmp op (f a) (f b)
  | .eq a b => .eq (f a) (f b)
  | .neq a b => .neq (f a) (f b)
  | .and a b => .and (f a) (f b)
  | .or a b => .or (f a) (f b)
  | .implies a b => .implies (f a) (f b)
  | .mapGet a b => .mapGet (f a) (f b)
  | .not e => .not (f e)
  | .old e => .old (f e)
  | .forall bs e => .forall bs (f e)
  | .exists bs e => .exists bs (f e)
  | .ite c t e => .ite (f c) (f t) (f e)
  | .fnCall name args => .fnCall name (args.map f)
  | e => e

/-- Apply `g` to every node, children first. -/
partial def mapBottomUp (g : Expr → Expr) (e : Expr) : Expr :=
  g (e.mapChildren (mapBottomUp g))

/-- Variables that occur free in an expression. -/
partial def freeVars : Expr → List String
  | .var name => [name]
  | .forall bs e | .exists bs e => (freeVars e).filter fun n => !bs.any (·.1 == n)
  | e => e.children.flatMap freeVars

/-- Names of the Boole functions an expression applies. -/
partial def fnCalls (e : Expr) : List String :=
  (match e with
    | .fnCall name _ => [name]
    | _ => []) ++ e.children.flatMap fnCalls

/-- Capture-avoiding substitution of variables; quantifiers shadow `σ`. -/
partial def subst (σ : List (String × Expr)) : Expr → Expr
  | .var name => (σ.lookup name).getD (.var name)
  | .forall bs e => .forall bs (subst (σ.filter fun (n, _) => !bs.any (·.1 == n)) e)
  | .exists bs e => .exists bs (subst (σ.filter fun (n, _) => !bs.any (·.1 == n)) e)
  | e => e.mapChildren (subst σ)

end Expr

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

namespace Stmt

/-- Every expression a statement evaluates, including in nested statements. -/
partial def exprs : Stmt → List Expr
  | .assign lhs rhs =>
      (match lhs with
        | .var _ => []
        | .mapSlot map key => [map, key]) ++ [rhs]
  | .check _ e | .assume e => [e]
  | .ifElse c t f => [c] ++ t.flatMap exprs ++ f.flatMap exprs
  | .whileLoop c invs body => [c] ++ invs.map (·.2) ++ body.flatMap exprs
  | .call _ _ args => args
  | .block _ body => body.flatMap exprs
  | _ => []

/-- Procedures a statement calls, including in nested statements. -/
partial def calls : Stmt → List String
  | .call _ fname _ => [fname]
  | .ifElse _ t f => t.flatMap calls ++ f.flatMap calls
  | .whileLoop _ _ body | .block _ body => body.flatMap calls
  | _ => []

/-- Apply `f` to every expression a statement evaluates, including in nested statements. -/
partial def mapExprs (f : Expr → Expr) : Stmt → Stmt
  | .assign lhs rhs =>
      let lhs := match lhs with
        | .var n => LValue.var n
        | .mapSlot map key => .mapSlot (f map) (f key)
      .assign lhs (f rhs)
  | .check l e => .check l (f e)
  | .assume e => .assume (f e)
  | .ifElse c t e => .ifElse (f c) (t.map (mapExprs f)) (e.map (mapExprs f))
  | .whileLoop c invs body => .whileLoop (f c) (invs.map fun (l, e) => (l, f e)) (body.map (mapExprs f))
  | .call lhs fname args => .call lhs fname (args.map f)
  | .block l body => .block l (body.map (mapExprs f))
  | stm => stm

end Stmt

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

/--
A Boole `function` standing for a pure C0 function, so that contracts can call
it. Without a body it is uninterpreted.
-/
structure Function where
  name : String
  params : List (Tau × String)
  ret : Tau
  body : Option Expr := none
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
  functions : List Function := []
  procedures : List Procedure
  labels : Array LabelInfo := #[]
deriving Inhabited, Repr

end C0VC.StrataBoole
