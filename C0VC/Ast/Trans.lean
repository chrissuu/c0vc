import C0VC.Ast.ParsedAst
import C0VC.Ast.ElabbedAst

namespace C0VC.ElabbedAst.Trans

def convertTau : C0VC.Ast.Tau → Except String C0VC.ElabbedAst.Tau
  | .int => .ok .int
  | .char => .ok .char
  | .string => .ok .string
  | .bool => .ok .bool
  | .void => .ok .void
  | .struct name => .ok (.struct name)
  | .typeName name =>
      .error s!"type name `{name}` found after elaboration"

def convertBinOp : C0VC.Ast.BinOp → Except String C0VC.ElabbedAst.BinOp
  | .plus => .ok .plus
  | .sub => .ok .sub
  | .mul => .ok .mul
  | .div => .ok .div
  | .mod => .ok .mod
  | .lt => .ok .lt
  | .lte => .ok .lte
  | .gt => .ok .gt
  | .gte => .ok .gte
  | .eq => .ok .eq
  | .neq => .ok .neq
  | .bitAnd => .ok .bitAnd
  | .xor => .ok .xor
  | .bitOr => .ok .bitOr
  | .shl => .ok .shl
  | .shr => .ok .shr
  | .land => .error "logical && found after elaboration"
  | .lor => .error "logical || found after elaboration"

mutual
partial def convertMExpr (mexpr : C0VC.Ast.MarkedExpr) : Except String C0VC.ElabbedAst.MarkedExpr := do
  let node ← convertExpr mexpr.node
  .ok { node, span := mexpr.span }

partial def convertExpr : C0VC.Ast.Expr → Except String C0VC.ElabbedAst.Expr
  | .var name => .ok (.var name)
  | .intLit val => .ok (.intLit val)
  | .binop op lhs rhs => do
      let op' ← convertBinOp op
      let lhs' ← convertMExpr lhs
      let rhs' ← convertMExpr rhs
      .ok (.binop op' lhs' rhs')
  | .unop .. =>
      .error "unary operator found after elaboration"
  | .ternary test thenVal elseVal => do
      let test' ← convertMExpr test
      let thenVal' ← convertMExpr thenVal
      let elseVal' ← convertMExpr elseVal
      .ok (.ternary test' thenVal' elseVal')
  | .trueLit => .ok .trueLit
  | .falseLit => .ok .falseLit
  | .null => .ok .null
  | .charLit char => .ok (.charLit char)
  | .stringLit string => .ok (.stringLit string)
  | .call fname args => do
      let args' ← args.mapM convertMExpr
      .ok (.call fname args')
  | .length arrayLike => do
      let arrayLike' ← convertMExpr arrayLike
      .ok (.length arrayLike')
  | .result => .ok .result
  | .hastag => .ok .hastag
  | .dot struct field => do
      let struct' ← convertMExpr struct
      .ok (.dot struct' field)
  | .arrow structPtr field => do
      let structPtr' ← convertMExpr structPtr
      .ok (.arrow structPtr' field)
  | .alloc type => do
      let type' ← convertTau type
      .ok (.alloc type')
  | .allocArray type size => do
      let type' ← convertTau type
      let size' ← convertMExpr size
      .ok (.allocArray type' size')
  | .deref ptr => do
      let ptr' ← convertMExpr ptr
      .ok (.deref ptr')
  | .arrAccess arr index => do
      let arr' ← convertMExpr arr
      let index' ← convertMExpr index
      .ok (.arrAccess arr' index')
end

mutual
partial def convertMAnno (manno : C0VC.Ast.MarkedAnno) : Except String C0VC.ElabbedAst.MarkedAnno := do
  let node ← convertAnno manno.node
  .ok { node, span := manno.span }

partial def convertAnno : C0VC.Ast.Anno → Except String C0VC.ElabbedAst.Anno
  | .requires precondition => do
      let precondition' ← convertMExpr precondition
      .ok (.requires precondition')
  | .ensures postcondition => do
      let postcondition' ← convertMExpr postcondition
      .ok (.ensures postcondition')
  | .asserts e => do
      let e' ← convertMExpr e
      .ok (.asserts e')
  | .loopInvariant e => do
      let e' ← convertMExpr e
      .ok (.loopInvariant e')
end

mutual
partial def convertMStm (mstm : C0VC.Ast.MarkedStm) : Except String C0VC.ElabbedAst.MarkedStm := do
  let node ← convertStm mstm.node
  .ok { node, span := mstm.span }

partial def convertStm : C0VC.Ast.Stm → Except String C0VC.ElabbedAst.Stm
  | .assign varName val => do
      let val' ← convertMExpr val
      .ok (.assign varName val')
  | .ifLit test thenBranch elseBranch => do
      let test' ← convertMExpr test
      let thenBranch' ← convertMStm thenBranch
      let elseBranch' ← convertMStm elseBranch
      .ok (.ifLit test' thenBranch' elseBranch')
  | .whileLit test body step => do
      let test' ← convertMExpr test
      let body' ← convertMStm body
      let step' ← convertMStm step
      .ok (.whileLit test' body' step')
  | .ret valOpt => do
      let valOpt' ← valOpt.mapM convertMExpr
      .ok (.ret valOpt')
  | .seq first rest => do
      let first' ← convertMStm first
      let rest' ← convertMStm rest
      .ok (.seq first' rest')
  | .declare varName tau init value => do
      let tau' ← convertTau tau
      let init' ← init.mapM convertMExpr
      let value' ← convertMStm value
      .ok (.declare varName tau' init' value')
  | .asop .. =>
      .error "assignment operator found after elaboration"
  | .forLit .. =>
      .error "for loop found after elaboration"
  | .expr e => do
      let e' ← convertMExpr e
      .ok (.expr e')
  | .assert test => do
      let test' ← convertMExpr test
      .ok (.assert test')
  | .error e => do
      let e' ← convertMExpr e
      .ok (.error e')
  | .nop => .ok .nop
  | .annotation a => do
      let a' ← convertMAnno a
      .ok (.annotation a')
  | .incr .. =>
      .error "increment found after elaboration"
  | .decr .. =>
      .error "decrement found after elaboration"
end

def convertParam (param : C0VC.Ast.Param) : Except String C0VC.ElabbedAst.Param := do
  let (tau, name) := param
  let tau' ← convertTau tau
  .ok (tau', name)

def convertField (field : C0VC.Ast.Field) : Except String C0VC.ElabbedAst.Field := do
  let (tau, name) := field
  let tau' ← convertTau tau
  .ok (tau', name)

def convertGDecl : C0VC.Ast.GDecl → Except String C0VC.ElabbedAst.GDecl
  | .fdefn retType fname params body annotations => do
      let retType' ← convertTau retType
      let params' ← params.mapM convertParam
      let body' ← body.mapM convertMStm
      let annotations' ← annotations.mapM convertMStm
      .ok (.fdefn {
        retType := retType',
        fname,
        params := params',
        body := body',
        annotations := annotations'
      })

  | .fdecl retType fname params _ => do
      let retType' ← convertTau retType
      let params' ← params.mapM convertParam
      .ok (.fdecl retType' fname params' true)

  | .typedef .. =>
      .error "typedef found after elaboration"

  | .sdecl name fields => do
      let fields' ← fields.mapM convertField
      .ok (.sdecl name fields')



def convertProgram (program : C0VC.Ast.Program) : Except String C0VC.ElabbedAst.Program := do
  program.mapM convertGDecl

end C0VC.ElabbedAst.Trans
