namespace C0VC.StrataBoole

inductive Tau where
  | int
  | bool
  | void
  | ref
  | heapRef
  | map (key val : Tau)
deriving Inhabited, BEq

inductive BinOp where
  | plus
  | sub
  | mul
  | div
  | mod
  | lt
  | lte
  | gt
  | gte
  | eq
  | neq
  | bitAnd
  | xor
  | bitOr
  | shl
  | shr
deriving Inhabited, BEq

mutual
inductive Expr where
  | var (name : String)
  | intLit (val : Int)
  | boolLit (val : Bool)
  | null
  | binop (op : BinOp) (lhs rhs : Expr)
  | ite (test thenVal elseVal : Expr)
  | call (fname : String) (args : List Expr)
  | mapGet (map key : Expr)

inductive LValue where
  | var (name : String)
  | mapSlot (map key : Expr)
end

inductive Spec where
  | requires (expr : Expr)
  | ensures (expr : Expr)

inductive Stmt where
  | declare (name : String) (tau : Tau)
  | assign (lhs : LValue) (rhs : Expr)
  | assert (expr : Expr)
  | ifElse (test : Expr) (thenBody elseBody : List Stmt)
  | whileLoop (test : Expr) (invariants : List Expr) (body : List Stmt)

structure Procedure where
  name : String
  params : List (Tau × String)
  ret : Option (Tau × String)
  specs : List Spec
  modifies : List String := []
  body : Option (List Stmt)

structure Program where
  procedures : List Procedure

structure Config where
  resultName : String := "__result"

end C0VC.StrataBoole
