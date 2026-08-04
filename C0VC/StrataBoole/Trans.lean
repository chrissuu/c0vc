import C0VC.Ast.TypedAst
import C0VC.StrataBoole.IR
import C0VC.StrataBoole.Struct

namespace C0VC.StrataBoole.Trans

open C0VC.StrataBoole

structure Config where
  resultName : String := "__result"
  fieldLayout : Struct.FieldIndexMap := {}
  structWidths : Struct.StructWidthMap := {}

private def fieldInfo (cfg : Config) (root : String) (fields : List String) : Except String Struct.FieldInfo :=
  Struct.lookupFieldInfo cfg.fieldLayout root fields

private def structNameOfTau : C0VC.TypedAst.Tau → Option String
  | .struct name => some name
  | _ => none

private def ptrStructNameOfTau : C0VC.TypedAst.Tau → Option String
  | .ptr (.struct name) => some name
  | _ => none

private def isStructTau : C0VC.TypedAst.Tau → Bool
  | .struct _ => true
  | _ => false

private def heapNameOfTau : C0VC.TypedAst.Tau → Except String String
  | .int | .char => .ok "hInt"
  | .bool => .ok "hBool"
  | .ptr _ | .array _ | .null | .struct _ => .ok "hRef"
  | .void => .error "void values do not have a Boole heap"
  | .string => .error "StrataBoole backend does not support string heap values yet"

private def heapAt (heapName : String) (ref index : Expr) : Expr :=
  .mapGet (.mapGet (.var heapName) ref) index

private def heapSlot (heapName : String) (ref index : Expr) : LValue :=
  .mapSlot (.mapGet (.var heapName) ref) index

private def typedHeapNames : List String :=
  [ "hInt", "hBool", "hRef" ]

private def isTypedHeapName (name : String) : Bool :=
  typedHeapNames.contains name

private def lvalueAsExpr : LValue → Expr
  | .var name => .var name
  | .mapSlot map key => .mapGet map key

private def refAllocated (ref : Expr) : Expr :=
  .mapGet (.var "alloc") ref

private def refLengthSlot (ref : Expr) : LValue :=
  .mapSlot (.var "len") ref

private def refAllocSlot (ref : Expr) : LValue :=
  .mapSlot (.var "alloc") ref

private def nextRef : Expr :=
  .var "nextRef"

private def one : Expr :=
  .intLit 1

private def structWidth (cfg : Config) (name : String) : Except String Nat :=
  Struct.lookupStructWidth cfg.structWidths name

private def allocWidthExpr (cfg : Config) : C0VC.TypedAst.Tau → Except String Expr
  | .struct name => do
      .ok (.intLit (← structWidth cfg name))
  | _ => .ok one

private def arrayAllocLengthExpr (cfg : Config) (elemTau : C0VC.TypedAst.Tau) (size : Expr) : Except String Expr := do
  match elemTau with
  | .struct name =>
      let width ← structWidth cfg name
      .ok (.binop .mul size (.intLit width))
  | _ => .ok size

private def slotOffset (cfg : Config) (structName : String) (index : Expr) : Except String Expr := do
  .ok (.binop .mul index (.intLit (← structWidth cfg structName)))

private def fieldSlot (offset? : Option Expr) (info : Struct.FieldInfo) : Expr :=
  match offset? with
  | none => .intLit info.index
  | some offset =>
      if info.index == 0 then
        offset
      else
        .binop .plus offset (.intLit info.index)

private def validRefAssertions (ref : Expr) : List Stmt :=
  [ .assert (.binop .neq ref .null)
  , .assert (refAllocated ref)
  ]

private def knownNonnegative : Expr → Bool
  | .intLit val => val >= 0
  | _ => false

private def validSlotAssertions (ref slot : Expr) : List Stmt :=
  let lowerBound :=
    if knownNonnegative slot then
      []
    else
      [.assert (.binop .lte (.intLit 0) slot)]
  validRefAssertions ref ++ lowerBound ++
  [.assert (.binop .lt slot (.mapGet (.var "len") ref))]

mutual
partial def safetyExpr : Expr → List Stmt
  | .var _ | .intLit _ | .boolLit _ | .null => []
  | .binop _ lhs rhs => safetyExpr lhs ++ safetyExpr rhs
  | .ite test thenVal elseVal => safetyExpr test ++ safetyExpr thenVal ++ safetyExpr elseVal
  | .call _ args => args.flatMap safetyExpr
  | .mapGet (.mapGet (.var heapName) ref) slot =>
      let nested := safetyExpr ref ++ safetyExpr slot
      if isTypedHeapName heapName then
        nested ++ validSlotAssertions ref slot
      else
        nested
  | .mapGet (.var "len") ref =>
      safetyExpr ref ++ validRefAssertions ref
  | .mapGet map key => safetyExpr map ++ safetyExpr key

partial def safetyLValue : LValue → List Stmt
  | .var _ => []
  | .mapSlot (.mapGet (.var heapName) ref) slot =>
      let nested := safetyExpr ref ++ safetyExpr slot
      if isTypedHeapName heapName then
        nested ++ validSlotAssertions ref slot
      else if heapName == "alloc" || heapName == "len" then
        nested ++ validRefAssertions ref
      else
        nested
  | .mapSlot map key => safetyExpr map ++ safetyExpr key
end

private def finishAllocation (lhs : LValue) (logicalLength : Expr) : List Stmt :=
  let allocatedRef := lvalueAsExpr lhs
  [ .assert (.binop .neq nextRef .null)
  , .assert (.binop .eq (refAllocated nextRef) (.boolLit false))
  , .assign lhs nextRef
  , .assign (refAllocSlot allocatedRef) (.boolLit true)
  , .assign (refLengthSlot allocatedRef) logicalLength
  , .assign (.var "nextRef") (.binop .plus nextRef one)
  ]

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
  | .deref ptr => .ok (heapAt (← heapNameOfTau e.tau) (← transExpr cfg ptr) (.intLit 0))
  | .arrAccess arr index =>
      if isStructTau e.tau then
        .error "StrataBoole backend does not lower array-of-struct values yet"
      else
        .ok (heapAt (← heapNameOfTau e.tau) (← transExpr cfg arr) (← transExpr cfg index))
  | .dot struct field => do
      let (base, root, path, offset?) ← transStructExprRefAndPath cfg struct
      let path := path ++ [field]
      let info ← fieldInfo cfg root path
      .ok (heapAt (← heapNameOfTau info.tau) base (fieldSlot offset? info))
  | .arrow structPtr field => do
      let root ← match ptrStructNameOfTau structPtr.tau with
        | some root => .ok root
        | none => .error "arrow access expected pointer-to-struct type"
      let info ← fieldInfo cfg root [field]
      .ok (heapAt (← heapNameOfTau info.tau) (← transExpr cfg structPtr) (.intLit info.index))

partial def transLValue (cfg : Config) (lv : C0VC.TypedAst.TypedLValue) : Except String LValue := do
  match lv.node with
  | .var name => .ok (.var name)
  | .deref ptr => .ok (heapSlot (← heapNameOfTau lv.tau) (← transLValueAsExpr cfg ptr) (.intLit 0))
  | .arrAccess arr index =>
      if isStructTau lv.tau then
        .error "StrataBoole backend does not lower array-of-struct lvalues yet"
      else
        .ok (heapSlot (← heapNameOfTau lv.tau) (← transLValueAsExpr cfg arr) (← transExpr cfg index))
  | .dot struct field => do
      let (base, root, path, offset?) ← transStructLValueRefAndPath cfg struct
      let path := path ++ [field]
      let info ← fieldInfo cfg root path
      .ok (heapSlot (← heapNameOfTau info.tau) base (fieldSlot offset? info))
  | .arrow structPtr field => do
      let root ← match ptrStructNameOfTau structPtr.tau with
        | some root => .ok root
        | none => .error "arrow lvalue access expected pointer-to-struct type"
      let info ← fieldInfo cfg root [field]
      .ok (heapSlot (← heapNameOfTau info.tau) (← transLValueAsExpr cfg structPtr) (.intLit info.index))

partial def transLValueAsExpr (cfg : Config) (lv : C0VC.TypedAst.TypedLValue) : Except String Expr := do
  match ← transLValue cfg lv with
  | .var name => .ok (.var name)
  | .mapSlot map key => .ok (.mapGet map key)

partial def transStructExprRefAndPath
  (cfg : Config)
  (e : C0VC.TypedAst.TypedExpr)
  : Except String (Expr × String × List String × Option Expr) := do
  match e.node with
  | .dot struct field => do
      let (base, root, path, offset?) ← transStructExprRefAndPath cfg struct
      .ok (base, root, path ++ [field], offset?)
  | .arrow structPtr field => do
      let root ← match ptrStructNameOfTau structPtr.tau with
        | some root => .ok root
        | none => .error "arrow access expected pointer-to-struct type"
      .ok (← transExpr cfg structPtr, root, [field], none)
  | .deref ptr => do
      let root ← match structNameOfTau e.tau with
        | some root => .ok root
        | none => .error "struct dereference expected struct type"
      .ok (← transExpr cfg ptr, root, [], none)
  | .arrAccess arr index => do
      let root ← match structNameOfTau e.tau with
        | some root => .ok root
        | none => .error "array-of-struct access expected struct element type"
      let index ← transExpr cfg index
      .ok (← transExpr cfg arr, root, [], some (← slotOffset cfg root index))
  | _ =>
      let root ← match structNameOfTau e.tau with
        | some root => .ok root
        | none => .error "field access expected struct type"
      .ok (← transExpr cfg e, root, [], none)

partial def transStructLValueRefAndPath
  (cfg : Config)
  (lv : C0VC.TypedAst.TypedLValue)
  : Except String (Expr × String × List String × Option Expr) := do
  match lv.node with
  | .dot struct field => do
      let (base, root, path, offset?) ← transStructLValueRefAndPath cfg struct
      .ok (base, root, path ++ [field], offset?)
  | .arrow structPtr field => do
      let root ← match ptrStructNameOfTau structPtr.tau with
        | some root => .ok root
        | none => .error "arrow lvalue access expected pointer-to-struct type"
      .ok (← transLValueAsExpr cfg structPtr, root, [field], none)
  | .deref ptr => do
      let root ← match structNameOfTau lv.tau with
        | some root => .ok root
        | none => .error "struct dereference lvalue expected struct type"
      .ok (← transLValueAsExpr cfg ptr, root, [], none)
  | .arrAccess arr index => do
      let root ← match structNameOfTau lv.tau with
        | some root => .ok root
        | none => .error "array-of-struct lvalue access expected struct element type"
      let index ← transExpr cfg index
      .ok (← transLValueAsExpr cfg arr, root, [], some (← slotOffset cfg root index))
  | _ =>
      let root ← match structNameOfTau lv.tau with
        | some root => .ok root
        | none => .error "field lvalue access expected struct type"
      .ok (← transLValueAsExpr cfg lv, root, [], none)
end

private def transAllocationTo (cfg : Config) (lhs : LValue) (val : C0VC.TypedAst.TypedExpr) : Except String (Option (List Stmt)) := do
  match val.node with
  | .alloc tau =>
      .ok (some (finishAllocation lhs (← allocWidthExpr cfg tau)))
  | .allocArray tau size => do
      let size ← transExpr cfg size
      let length ← arrayAllocLengthExpr cfg tau size
      .ok (some (safetyExpr size ++ [.assert (.binop .lte (.intLit 0) size)] ++ finishAllocation lhs length))
  | _ =>
      .ok none

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
      if isStructTau lhs.tau || isStructTau val.tau then
        .error "StrataBoole backend does not lower whole-struct assignment yet"
      else
        let lhs ← transLValue cfg lhs
        match ← transAllocationTo cfg lhs val with
        | some stms => .ok (safetyLValue lhs ++ stms)
        | none =>
            let rhs ← transExpr cfg val
            .ok (safetyExpr rhs ++ safetyLValue lhs ++ [.assign lhs rhs])
  | .ret none => .ok []
  | .ret (some val) => do
      let val ← transExpr cfg val
      .ok (safetyExpr val ++ [.assign (.var cfg.resultName) val])
  | .expr e => do
      let e ← transExpr cfg e
      .ok (safetyExpr e ++ [.assert (.boolLit true)])
  | .assert test => do
      let test ← transExpr cfg test
      .ok (safetyExpr test ++ [.assert test])
  | .error _ => .ok [.assert (.boolLit false)]
  | .annotation (.asserts e) => do
      let e ← transExpr cfg e
      .ok (safetyExpr e ++ [.assert e])
  | .annotation (.loopInvariant _) =>
      .error "loop invariant annotation must immediately precede a while loop for Boole emission"
  | .annotation (.requires _) =>
      .error "requires annotation cannot appear in a function body"
  | .annotation (.ensures _) =>
      .error "ensures annotation cannot appear in a function body"
  | .ifLit test thenBranch elseBranch => do
      let test ← transExpr cfg test
      .ok (safetyExpr test ++ [.ifElse test (← transStm cfg thenBranch) (← transStm cfg elseBranch)])
  | .whileLit test body => do
      let test ← transExpr cfg test
      let testSafety := safetyExpr test
      let body ← transStm cfg body
      .ok (testSafety ++ [.whileLoop test [] (body ++ testSafety)])
  | .seq (.annotation (.loopInvariant inv)) (.whileLit test body) => do
      let test ← transExpr cfg test
      let inv ← transExpr cfg inv
      let testSafety := safetyExpr test
      let body ← transStm cfg body
      .ok (testSafety ++ [.whileLoop test [inv] (body ++ testSafety)])
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
            match ← transAllocationTo cfg (.var varName) e with
            | some stms => .ok stms
            | none =>
                let e ← transExpr cfg e
                .ok (safetyExpr e ++ [.assign (.var varName) e])
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
  let layout ← Struct.computeLayout structs
  let cfg := { cfg with fieldLayout := layout.fields, structWidths := layout.widths }
  .ok { procedures := ← program.mapM (transProcedure cfg) }

def run (program : C0VC.TypedAst.Program) : Except String Program :=
  runWithConfig {} program

end C0VC.StrataBoole.Trans
