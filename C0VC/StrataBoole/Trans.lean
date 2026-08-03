import C0VC.Ast.TypedAst
import C0VC.StrataBoole.IR
import C0VC.StrataBoole.Struct

namespace C0VC.StrataBoole.Trans

open C0VC.StrataBoole

structure Config where
  resultName : String := "__result"
  fieldLayout : Struct.FieldIndexMap := {}

private def fieldIndexExpr (cfg : Config) (root : String) (fields : List String) : Except String Expr := do
  .ok (.intLit (← Struct.lookupFieldIndex cfg.fieldLayout root fields))

private def structNameOfTau : C0VC.TypedAst.Tau → Option String
  | .struct name => some name
  | _ => none

private def ptrStructNameOfTau : C0VC.TypedAst.Tau → Option String
  | .ptr (.struct name) => some name
  | _ => none

partial def transTau : C0VC.TypedAst.Tau → Except String Tau
  | .int | .char => .ok .int
  | .bool => .ok .bool
  | .void => .ok .void
  | .ptr _ | .array _ | .null | .struct _ => .ok .ref
  | .string => .error "StrataBoole backend does not support string values yet"

private def transBinOp : C0VC.TypedAst.BinOp → BinOp
  | .plus => .plus
  | .sub => .sub
  | .mul => .mul
  | .div => .div
  | .mod => .mod
  | .lt => .lt
  | .lte => .lte
  | .gt => .gt
  | .gte => .gte
  | .eq => .eq
  | .neq => .neq
  | .bitAnd => .bitAnd
  | .xor => .xor
  | .bitOr => .bitOr
  | .shl => .shl
  | .shr => .shr

private def heapAt (ref index : Expr) : Expr :=
  .mapGet (.mapGet (.var "hRef") ref) index

mutual
partial def transExpr (cfg : Config) (e : C0VC.TypedAst.TypedExpr) : Except String Expr := do
  match e.node with
  | .var name => .ok (.var name)
  | .intLit val => .ok (.intLit val)
  | .trueLit => .ok (.boolLit true)
  | .falseLit => .ok (.boolLit false)
  | .null => .ok .null
  | .charLit c => .ok (.intLit c.toNat)
  | .stringLit _ => .error "StrataBoole backend does not support string literals yet"
  | .result => .ok (.var cfg.resultName)
  | .hastag => .error "StrataBoole backend does not support hastag expressions yet"
  | .binop op lhs rhs => .ok (.binop (transBinOp op) (← transExpr cfg lhs) (← transExpr cfg rhs))
  | .ternary test thenVal elseVal =>
      .ok (.ite (← transExpr cfg test) (← transExpr cfg thenVal) (← transExpr cfg elseVal))
  | .call fname args => .ok (.call fname (← args.mapM (transExpr cfg)))
  | .length arrayLike => .ok (.mapGet (.var "len") (← transExpr cfg arrayLike))
  | .alloc _ | .allocArray .. =>
      .error "StrataBoole backend does not lower allocation yet; heap allocation needs the logical heap pass"
  | .deref ptr => .ok (heapAt (← transExpr cfg ptr) (.intLit 0))
  | .arrAccess arr index => .ok (heapAt (← transExpr cfg arr) (← transExpr cfg index))
  | .dot struct field => do
      let (base, root, path) ← transStructExprRefAndPath cfg struct
      .ok (heapAt base (← fieldIndexExpr cfg root (path ++ [field])))
  | .arrow structPtr field => do
      let root ← match ptrStructNameOfTau structPtr.tau with
        | some root => .ok root
        | none => .error "arrow access expected pointer-to-struct type"
      .ok (heapAt (← transExpr cfg structPtr) (← fieldIndexExpr cfg root [field]))

partial def transLValue (cfg : Config) (lv : C0VC.TypedAst.TypedLValue) : Except String LValue := do
  match lv.node with
  | .var name => .ok (.var name)
  | .deref ptr => .ok (.mapSlot (.mapGet (.var "hRef") (← transLValueAsExpr cfg ptr)) (.intLit 0))
  | .arrAccess arr index => .ok (.mapSlot (.mapGet (.var "hRef") (← transLValueAsExpr cfg arr)) (← transExpr cfg index))
  | .dot struct field => do
      let (base, root, path) ← transStructLValueRefAndPath cfg struct
      .ok (.mapSlot (.mapGet (.var "hRef") base) (← fieldIndexExpr cfg root (path ++ [field])))
  | .arrow structPtr field => do
      let root ← match ptrStructNameOfTau structPtr.tau with
        | some root => .ok root
        | none => .error "arrow lvalue access expected pointer-to-struct type"
      .ok (.mapSlot (.mapGet (.var "hRef") (← transLValueAsExpr cfg structPtr)) (← fieldIndexExpr cfg root [field]))

partial def transLValueAsExpr (cfg : Config) (lv : C0VC.TypedAst.TypedLValue) : Except String Expr := do
  match ← transLValue cfg lv with
  | .var name => .ok (.var name)
  | .mapSlot map key => .ok (.mapGet map key)

partial def transStructExprRefAndPath
  (cfg : Config)
  (e : C0VC.TypedAst.TypedExpr)
  : Except String (Expr × String × List String) := do
  match e.node with
  | .dot struct field => do
      let (base, root, path) ← transStructExprRefAndPath cfg struct
      .ok (base, root, path ++ [field])
  | .arrow structPtr field => do
      let root ← match ptrStructNameOfTau structPtr.tau with
        | some root => .ok root
        | none => .error "arrow access expected pointer-to-struct type"
      .ok (← transExpr cfg structPtr, root, [field])
  | _ =>
      let root ← match structNameOfTau e.tau with
        | some root => .ok root
        | none => .error "field access expected struct type"
      .ok (← transExpr cfg e, root, [])

partial def transStructLValueRefAndPath
  (cfg : Config)
  (lv : C0VC.TypedAst.TypedLValue)
  : Except String (Expr × String × List String) := do
  match lv.node with
  | .dot struct field => do
      let (base, root, path) ← transStructLValueRefAndPath cfg struct
      .ok (base, root, path ++ [field])
  | .arrow structPtr field => do
      let root ← match ptrStructNameOfTau structPtr.tau with
        | some root => .ok root
        | none => .error "arrow lvalue access expected pointer-to-struct type"
      .ok (← transLValueAsExpr cfg structPtr, root, [field])
  | _ =>
      let root ← match structNameOfTau lv.tau with
        | some root => .ok root
        | none => .error "field lvalue access expected struct type"
      .ok (← transLValueAsExpr cfg lv, root, [])
end

private def checkReturns (tail : Bool) : C0VC.TypedAst.Stm → Except String Unit
  | .ret _ =>
      if tail then .ok () else .error "StrataBoole backend does not support non-tail return statements yet"
  | .seq first rest => do
      checkReturns false first
      checkReturns tail rest
  | .ifLit _ thenBranch elseBranch => do
      checkReturns tail thenBranch
      checkReturns tail elseBranch
  | .whileLit _ body =>
      checkReturns false body
  | .declare _ _ _ body =>
      checkReturns tail body
  | _ => .ok ()

partial def transStm (cfg : Config) : C0VC.TypedAst.Stm → Except String (List Stmt)
  | .nop => .ok []
  | .assign lhs val => do
      .ok [.assign (← transLValue cfg lhs) (← transExpr cfg val)]
  | .ret none => .ok []
  | .ret (some val) => do
      .ok [.assign (.var cfg.resultName) (← transExpr cfg val)]
  | .expr _ => .ok [.assert (.boolLit true)]
  | .assert test => do
      .ok [.assert (← transExpr cfg test)]
  | .error _ => .ok [.assert (.boolLit false)]
  | .annotation (.asserts e) => do
      .ok [.assert (← transExpr cfg e)]
  | .annotation (.loopInvariant _) =>
      .error "loop invariant annotation must immediately precede a while loop for Boole emission"
  | .annotation (.requires _) =>
      .error "requires annotation cannot appear in a function body"
  | .annotation (.ensures _) =>
      .error "ensures annotation cannot appear in a function body"
  | .ifLit test thenBranch elseBranch => do
      .ok [.ifElse (← transExpr cfg test) (← transStm cfg thenBranch) (← transStm cfg elseBranch)]
  | .whileLit test body => do
      .ok [.whileLoop (← transExpr cfg test) [] (← transStm cfg body)]
  | .seq (.annotation (.loopInvariant inv)) (.whileLit test body) => do
      .ok [.whileLoop (← transExpr cfg test) [← transExpr cfg inv] (← transStm cfg body)]
  | .seq (.annotation (.loopInvariant inv)) (.seq (.whileLit test body) rest) => do
      let loop ← transStm cfg (.seq (.annotation (.loopInvariant inv)) (.whileLit test body))
      let rest ← transStm cfg rest
      .ok (loop ++ rest)
  | .seq first rest => do
      .ok ((← transStm cfg first) ++ (← transStm cfg rest))
  | .declare varName tau init body => do
      let decl := Stmt.declare varName (← transTau tau)
      let initStms ← match init with
        | none => .ok []
        | some e => do
            .ok [.assign (.var varName) (← transExpr cfg e)]
      let bodyStms ← transStm cfg body
      .ok ([decl] ++ initStms ++ bodyStms)

private def transSpec (cfg : Config) : C0VC.TypedAst.Anno → Except String (Option Spec)
  | .requires e => do
      .ok (some (.requires (← transExpr cfg e)))
  | .ensures e => do
      .ok (some (.ensures (← transExpr cfg e)))
  | .asserts _ => .error "assert annotation cannot appear in a function contract"
  | .loopInvariant _ => .error "loop invariant annotation cannot appear in a function contract"

private def bodyStm : List C0VC.TypedAst.Stm → C0VC.TypedAst.Stm
  | [] => .nop
  | [stm] => stm
  | stm :: rest => .seq stm (bodyStm rest)

private def transProcedure (cfg : Config) (f : C0VC.TypedAst.FunctionDef) : Except String Procedure := do
  let params ← f.params.mapM fun (tau, name) => do
    .ok (← transTau tau, name)
  let ret ← match f.retType with
    | .void => .ok none
    | _ => .ok (some (← transTau f.retType, cfg.resultName))
  let specs ← f.annotations.filterMapM (transSpec cfg)
  let body ←
    if f.external then
      .ok none
    else
      let stm := bodyStm f.body
      checkReturns true stm
      .ok (some (← transStm cfg stm))
  .ok { name := f.fname, params, ret, specs, body }

def runWithConfig (cfg : Config) (program : C0VC.TypedAst.Program) : Except String Program := do
  let structs := program.flatMap (fun f => f.structs)
  let fieldLayout ← Struct.computeFieldLayout structs
  let cfg := { cfg with fieldLayout }
  .ok { procedures := ← program.mapM (transProcedure cfg) }

def run (program : C0VC.TypedAst.Program) : Except String Program :=
  runWithConfig {} program

end C0VC.StrataBoole.Trans
