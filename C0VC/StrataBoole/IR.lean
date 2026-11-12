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

mutual
/-- Apply `g` to every node, children first. -/
def mapBottomUp (g : Expr → Expr) : Expr → Expr
  | .arith op a b => g (.arith op (mapBottomUp g a) (mapBottomUp g b))
  | .cmp op a b => g (.cmp op (mapBottomUp g a) (mapBottomUp g b))
  | .mathArith op a b => g (.mathArith op (mapBottomUp g a) (mapBottomUp g b))
  | .mathCmp op a b => g (.mathCmp op (mapBottomUp g a) (mapBottomUp g b))
  | .eq a b => g (.eq (mapBottomUp g a) (mapBottomUp g b))
  | .neq a b => g (.neq (mapBottomUp g a) (mapBottomUp g b))
  | .and a b => g (.and (mapBottomUp g a) (mapBottomUp g b))
  | .or a b => g (.or (mapBottomUp g a) (mapBottomUp g b))
  | .implies a b => g (.implies (mapBottomUp g a) (mapBottomUp g b))
  | .mapGet a b => g (.mapGet (mapBottomUp g a) (mapBottomUp g b))
  | .not e => g (.not (mapBottomUp g e))
  | .old e => g (.old (mapBottomUp g e))
  | .forall bs e => g (.forall bs (mapBottomUp g e))
  | .exists bs e => g (.exists bs (mapBottomUp g e))
  | .ite c t e => g (.ite (mapBottomUp g c) (mapBottomUp g t) (mapBottomUp g e))
  | .fnCall name args => g (.fnCall name (mapBottomUpList g args))
  | e => g e

def mapBottomUpList (g : Expr → Expr) : List Expr → List Expr
  | [] => []
  | e :: es => mapBottomUp g e :: mapBottomUpList g es
end

mutual
/-- The expression and all of its subexpressions, outermost first. -/
def subexprs : Expr → List Expr
  | e@(.fnCall _ args) => e :: subexprsList args
  | e@(.arith _ a b) | e@(.cmp _ a b) | e@(.mathArith _ a b) | e@(.mathCmp _ a b)
  | e@(.eq a b) | e@(.neq a b) | e@(.and a b) | e@(.or a b) | e@(.implies a b)
  | e@(.mapGet a b) => e :: (subexprs a ++ subexprs b)
  | e@(.not x) | e@(.old x) | e@(.forall _ x) | e@(.exists _ x) => e :: subexprs x
  | e@(.ite c t f) => e :: (subexprs c ++ subexprs t ++ subexprs f)
  | e => [e]

def subexprsList : List Expr → List Expr
  | [] => []
  | e :: es => subexprs e ++ subexprsList es
end

mutual
/-- Variables that occur free in an expression. -/
def freeVars : Expr → List String
  | .var name => [name]
  | .forall bs e | .exists bs e => (freeVars e).filter fun n => !bs.any (·.1 == n)
  | .fnCall _ args => freeVarsList args
  | .arith _ a b | .cmp _ a b | .mathArith _ a b | .mathCmp _ a b
  | .eq a b | .neq a b | .and a b | .or a b | .implies a b | .mapGet a b =>
      freeVars a ++ freeVars b
  | .not e | .old e => freeVars e
  | .ite c t f => freeVars c ++ freeVars t ++ freeVars f
  | _ => []

def freeVarsList : List Expr → List String
  | [] => []
  | e :: es => freeVars e ++ freeVarsList es
end

/-- Names of the Boole functions an expression applies. -/
def fnCalls (e : Expr) : List String :=
  e.subexprs.filterMap fun
    | .fnCall name _ => some name
    | _ => none

mutual
/-- Capture-avoiding substitution of variables; quantifiers shadow `σ`. -/
def subst (σ : List (String × Expr)) : Expr → Expr
  | .var name => (σ.lookup name).getD (.var name)
  | .forall bs e => .forall bs (subst (σ.filter fun (n, _) => !bs.any (·.1 == n)) e)
  | .exists bs e => .exists bs (subst (σ.filter fun (n, _) => !bs.any (·.1 == n)) e)
  | .arith op a b => .arith op (subst σ a) (subst σ b)
  | .cmp op a b => .cmp op (subst σ a) (subst σ b)
  | .mathArith op a b => .mathArith op (subst σ a) (subst σ b)
  | .mathCmp op a b => .mathCmp op (subst σ a) (subst σ b)
  | .eq a b => .eq (subst σ a) (subst σ b)
  | .neq a b => .neq (subst σ a) (subst σ b)
  | .and a b => .and (subst σ a) (subst σ b)
  | .or a b => .or (subst σ a) (subst σ b)
  | .implies a b => .implies (subst σ a) (subst σ b)
  | .mapGet a b => .mapGet (subst σ a) (subst σ b)
  | .not e => .not (subst σ e)
  | .old e => .old (subst σ e)
  | .ite c t e => .ite (subst σ c) (subst σ t) (subst σ e)
  | .fnCall name args => .fnCall name (substList σ args)
  | e => e

def substList (σ : List (String × Expr)) : List Expr → List Expr
  | [] => []
  | e :: es => subst σ e :: substList σ es
end

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
def exprs : Stmt → List Expr
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
def calls : Stmt → List String
  | .call _ fname _ => [fname]
  | .ifElse _ t f => t.flatMap calls ++ f.flatMap calls
  | .whileLoop _ _ body | .block _ body => body.flatMap calls
  | _ => []

/-- Apply `f` to every expression a statement evaluates, including in nested statements. -/
def mapExprs (f : Expr → Expr) : Stmt → Stmt
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
