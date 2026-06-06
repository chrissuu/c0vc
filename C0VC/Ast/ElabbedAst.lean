/-
Elaborated AST Core Definitions

This AST is the post-elaboration surface for later compiler phases. It omits
syntax that should be desugared away before typechecking/lowering, such as
assignment operators, for loops, increment/decrement, unary operators, short
circuit operators, and typedef declarations.
-/
import C0VC.Utils.SrcSpan

open C0VC.Utils.SrcSpan

namespace C0VC.ElabbedAst

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
deriving Inhabited

inductive Tau where
  | int
  | char
  | string
  | bool
  | void
  | struct (name : String)
  | ptr (tau : Tau)
  | array (tau : Tau)
  | null
deriving Inhabited

mutual
inductive Expr where
  | var (name : String)
  | intLit (val : Int)
  | binop (op : BinOp) (lhs : MarkedExpr) (rhs : MarkedExpr)
  | ternary (test : MarkedExpr) (thenVal : MarkedExpr) (elseVal : MarkedExpr)
  | trueLit
  | falseLit
  | null
  | charLit (char : Char)
  | stringLit (string : String)
  | call (fname : String) (args : List MarkedExpr)
  | length (arrayLike : MarkedExpr)
  | result
  | hastag
  | dot (struct : MarkedExpr) (field : String)
  | arrow (structPtr : MarkedExpr) (field : String)
  | alloc (type : Tau)
  | allocArray (type : Tau) (size : MarkedExpr)
  | deref (ptr : MarkedExpr)
  | arrAccess (arr : MarkedExpr) (index : MarkedExpr)

structure MarkedExpr where
  node : Expr
  span : Option SrcSpan
end

mutual
inductive LValue where
  | var (name : String)
  | deref (ptr : MarkedLValue)
  | dot (struct : MarkedLValue) (field : String)
  | arrow (structPtr : MarkedLValue) (field : String)
  | arrAccess (arr : MarkedLValue) (index : MarkedExpr)

structure MarkedLValue where
  node : LValue
  span : Option SrcSpan
end

mutual
inductive Anno where
  | requires (precondition : MarkedExpr)
  | ensures (postcondition : MarkedExpr)
  | asserts (e : MarkedExpr)
  | loopInvariant (e : MarkedExpr)

structure MarkedAnno where
  node : Anno
  span : Option SrcSpan
end

mutual
inductive Stm where
  | assign (lhs : MarkedLValue) (val : MarkedExpr)
  | ifLit (test : MarkedExpr) (thenBranch : MarkedStm) (elseBranch : MarkedStm)
  | whileLit (test : MarkedExpr) (body : MarkedStm) (step : MarkedStm)
  | ret (valOpt : Option MarkedExpr)
  | seq (first : MarkedStm) (rest : MarkedStm)
  | declare (varName : String) (type : Tau) (init : Option MarkedExpr) (body : MarkedStm)
  | expr (e : MarkedExpr)
  | assert (test : MarkedExpr)
  | error (e : MarkedExpr)
  | nop
  | annotation (a : MarkedAnno)

structure MarkedStm where
  node : Stm
  span : Option SrcSpan
end

abbrev Param := Tau × String
abbrev Field := Tau × String

structure FunctionDef where
  retType : Tau
  fname : String
  params : List Param
  body : List MarkedStm
  annotations : List MarkedStm

inductive GDecl where
  | fdecl (retType : Tau) (fname : String) (params : List Param) (external : Bool)
  | fdefn (fdefn : FunctionDef)
  | sdecl (name : String) (fields : List Field)

abbrev Program := List GDecl

namespace Print

def ppBinOp : BinOp → String
  | .plus => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "%"
  | .lt => "<"
  | .lte => "<="
  | .gt => ">"
  | .gte => ">="
  | .eq => "=="
  | .neq => "!="
  | .bitAnd => "&"
  | .xor => "^"
  | .bitOr => "|"
  | .shl => "<<"
  | .shr => ">>"

def ppTau : Tau → String
  | .string => "string"
  | .char => "char"
  | .int => "int"
  | .bool => "bool"
  | .void => "void"
  | .struct name => s!"struct {name}"
  | .ptr tau => s!"{ppTau tau}*"
  | .null => s!"null"
  | .array tau => s!"{ppTau tau}[]"

private def indent (str : String) : String :=
  str.splitOn "\n"
    |> List.map (fun line => "  " ++ line)
    |> String.intercalate "\n"

private def spaces (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

mutual
partial def ppExpr : Expr → String
  | .var id => id
  | .intLit n => toString n
  | .trueLit => "true"
  | .falseLit => "false"
  | .null => "NULL"
  | .stringLit s => s
  | .charLit c => toString c
  | .binop op lhs rhs =>
      s!"({ppMarkedExpr lhs} {ppBinOp op} {ppMarkedExpr rhs})"
  | .ternary test thenBranch elseBranch =>
      s!"({ppMarkedExpr test} ? {ppMarkedExpr thenBranch} : {ppMarkedExpr elseBranch})"
  | .call fname args =>
      let argsStr := String.intercalate ", " (args.map ppMarkedExpr)
      s!"{fname}({argsStr})"
  | .length arrayLike => s!"\\length ({ppMarkedExpr arrayLike})"
  | .result => "\\result"
  | .hastag => "\\hastag"
  | .dot struct field => s!"{ppMarkedExpr struct}.{field}"
  | .arrow structPtr field => s!"{ppMarkedExpr structPtr}->{field}"
  | .alloc type => s!"alloc({ppTau type})"
  | .allocArray type size => s!"alloc_array({ppTau type}, {ppMarkedExpr size})"
  | .deref ptr => s!"*({ppMarkedExpr ptr})"
  | .arrAccess arr index => s!"{ppMarkedExpr arr}[{ppMarkedExpr index}]"

partial def ppMarkedExpr (e : MarkedExpr) : String :=
  ppExpr e.node
end

mutual
partial def ppLValue : LValue → String
  | .var id => id
  | .deref ptr => s!"*({ppMarkedLValue ptr})"
  | .dot struct field => s!"{ppMarkedLValue struct}.{field}"
  | .arrow structPtr field => s!"{ppMarkedLValue structPtr}->{field}"
  | .arrAccess arr index => s!"{ppMarkedLValue arr}[{ppMarkedExpr index}]"

partial def ppMarkedLValue (lv : MarkedLValue) : String :=
  ppLValue lv.node
end

mutual
def ppAnno : Anno → String
  | .requires precondition => s!"//@requires ({ppMarkedExpr precondition})"
  | .ensures postcondition => s!"//@ensures ({ppMarkedExpr postcondition})"
  | .asserts e => s!"//@asserts ({ppMarkedExpr e})"
  | .loopInvariant e => s!"//@loop_invariant ({ppMarkedExpr e})"

def ppMarkedAnno (a : MarkedAnno) : String :=
  ppAnno a.node
end

mutual
partial def ppStm : Stm → String
  | .assign lhs e =>
      s!"{ppMarkedLValue lhs} = {ppMarkedExpr e};"
  | .ret valOpt =>
      match valOpt with
      | some e => s!"return {ppMarkedExpr e};"
      | none => "return;"
  | .nop =>
      "/* nop */"
  | .expr e =>
      s!"{ppMarkedExpr e};"
  | .assert test =>
      s!"assert({ppMarkedExpr test});"
  | .error e =>
      s!"error({ppMarkedExpr e});"
  | .declare id tau init body =>
      let bodyStr := ppStm body.node
      let declStr :=
        match init with
        | some e => s!"{ppTau tau} {id} = {ppMarkedExpr e};"
        | none => s!"{ppTau tau} {id};"
      if bodyStr.isEmpty || bodyStr == "/* nop */" then declStr else s!"{declStr}\n{bodyStr}"
  | .seq s1 s2 =>
      s!"{ppMarkedStm s1}\n{ppMarkedStm s2}"
  | .ifLit cond thenBranch elseBranch =>
      let thenStr := indent (ppMarkedStm thenBranch)
      let elseStr := ppMarkedStm elseBranch
      if elseStr == "/* nop */" then
        s!"if ({ppMarkedExpr cond}) \{\n{thenStr}\n}"
      else
        s!"if ({ppMarkedExpr cond}) \{\n{thenStr}\n} else \{\n{indent elseStr}\n}"
  | .whileLit cond body step =>
      let bodyStr :=
        match step.node with
        | .nop => ppMarkedStm body
        | _ => s!"{ppMarkedStm body}\n{ppMarkedStm step}"
      s!"while ({ppMarkedExpr cond}) \{\n{indent bodyStr}\n}"
  | .annotation a => s!"{ppMarkedAnno a}"

partial def ppMarkedStm (s : MarkedStm) : String :=
  ppStm s.node
end

def ppStms (stms : List MarkedStm) : String :=
  String.intercalate "" (stms.map fun stm => indent (ppMarkedStm stm) ++ "\n")

def ppParam : Param → String
  | (tau, id) => s!"{ppTau tau} {id}"

def ppField : Field → String
  | (tau, id) => s!"{ppTau tau} {id};"

def ppParams (params : List Param) : String :=
  let paramsStr := String.intercalate ", " (params.map ppParam)
  s!"({paramsStr})"

def ppFields (fields : List Field) : String :=
  String.intercalate "\n" (fields.map fun field => indent (ppField field))

def ppAnnos (annos : List MarkedStm) : String :=
  let annosStr := String.intercalate ", " (annos.map ppMarkedStm)
  s!"[{annosStr}]"

def ppFunctionDef (fdefn : FunctionDef) : String :=
  if fdefn.body.isEmpty then
    s!"{ppAnnos fdefn.annotations}\n{ppTau fdefn.retType} {fdefn.fname}{ppParams fdefn.params} \{\n}"
  else
    s!"{ppAnnos fdefn.annotations}\n{ppTau fdefn.retType} {fdefn.fname}{ppParams fdefn.params} \{\n{ppStms fdefn.body}}"

def ppGDecl : GDecl → String
  | .fdecl retType fname params true =>
      s!"external {ppTau retType} {fname}{ppParams params};"
  | .fdecl retType fname params false =>
      s!"{ppTau retType} {fname}{ppParams params};"
  | .fdefn fdefn => ppFunctionDef fdefn
  | .sdecl name fields =>
      s!"struct {name} \{\n{ppFields fields}\n};"

def ppProgram (program : Program) : String :=
  String.intercalate "\n\n" (program.map ppGDecl)

mutual
partial def ppExprRaw (indentLevel : Nat) : Expr → String
  | .var id => s!"{spaces indentLevel}Var({id})"
  | .intLit n => s!"{spaces indentLevel}IntLit({n})"
  | .trueLit => s!"{spaces indentLevel}TrueLit"
  | .falseLit => s!"{spaces indentLevel}FalseLit"
  | .null => s!"{spaces indentLevel}Null"
  | .stringLit s => s!"{spaces indentLevel}StringLit({s})"
  | .charLit c => s!"{spaces indentLevel}CharLit({c})"
  | .binop op lhs rhs =>
      s!"{spaces indentLevel}Binop({ppBinOp op},\n{ppMarkedExprRaw (indentLevel + 1) lhs},\n{ppMarkedExprRaw (indentLevel + 1) rhs}\n{spaces indentLevel})"
  | .ternary test thenBranch elseBranch =>
      s!"{spaces indentLevel}Ternary(\n{ppMarkedExprRaw (indentLevel + 1) test},\n{ppMarkedExprRaw (indentLevel + 1) thenBranch},\n{ppMarkedExprRaw (indentLevel + 1) elseBranch}\n{spaces indentLevel})"
  | .call fname args =>
      let argsStr := String.intercalate ",\n" (args.map (ppMarkedExprRaw (indentLevel + 1)))
      s!"{spaces indentLevel}Call({fname}, [\n{argsStr}\n{spaces indentLevel}])"
  | .length arrayLike =>
      s!"{spaces indentLevel}Length(\n{ppMarkedExprRaw (indentLevel + 1) arrayLike}\n{spaces indentLevel})"
  | .result => s!"{spaces indentLevel}Result"
  | .hastag => s!"{spaces indentLevel}Hastag"
  | .dot struct field =>
      s!"{spaces indentLevel}Dot(\n{ppMarkedExprRaw (indentLevel + 1) struct},\n{spaces (indentLevel + 1)}{field}\n{spaces indentLevel})"
  | .arrow structPtr field =>
      s!"{spaces indentLevel}Arrow(\n{ppMarkedExprRaw (indentLevel + 1) structPtr},\n{spaces (indentLevel + 1)}{field}\n{spaces indentLevel})"
  | .alloc type =>
      s!"{spaces indentLevel}Alloc({ppTau type})"
  | .allocArray type size =>
      s!"{spaces indentLevel}AllocArray({ppTau type},\n{ppMarkedExprRaw (indentLevel + 1) size}\n{spaces indentLevel})"
  | .deref ptr =>
      s!"{spaces indentLevel}Deref(\n{ppMarkedExprRaw (indentLevel + 1) ptr}\n{spaces indentLevel})"
  | .arrAccess arr index =>
      s!"{spaces indentLevel}ArrAccess(\n{ppMarkedExprRaw (indentLevel + 1) arr},\n{ppMarkedExprRaw (indentLevel + 1) index}\n{spaces indentLevel})"

partial def ppMarkedExprRaw (indentLevel : Nat) (e : MarkedExpr) : String :=
  ppExprRaw indentLevel e.node
end

def ppAnnoRaw (indentLevel : Nat) : Anno → String
  | .requires precondition =>
      s!"{spaces indentLevel}Requires(\n{ppMarkedExprRaw (indentLevel + 1) precondition}\n{spaces indentLevel})"
  | .ensures postcondition =>
      s!"{spaces indentLevel}Ensures(\n{ppMarkedExprRaw (indentLevel + 1) postcondition}\n{spaces indentLevel})"
  | .asserts e =>
      s!"{spaces indentLevel}Asserts(\n{ppMarkedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"
  | .loopInvariant e =>
      s!"{spaces indentLevel}LoopInvariant(\n{ppMarkedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"

mutual
partial def ppStmRaw (indentLevel : Nat) : Stm → String
  | .assign lhs e =>
      s!"{spaces indentLevel}Assign({ppMarkedLValue lhs},\n{ppMarkedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"
  | .ret valOpt =>
      match valOpt with
      | some e => s!"{spaces indentLevel}Ret(\n{ppMarkedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"
      | none => s!"{spaces indentLevel}Ret(None)"
  | .nop =>
      s!"{spaces indentLevel}Nop"
  | .expr e =>
      s!"{spaces indentLevel}Expr(\n{ppMarkedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"
  | .assert test =>
      s!"{spaces indentLevel}Assert(\n{ppMarkedExprRaw (indentLevel + 1) test}\n{spaces indentLevel})"
  | .error e =>
      s!"{spaces indentLevel}Error(\n{ppMarkedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"
  | .declare id tau init body =>
      let initStr := match init with | some e => ppMarkedExprRaw (indentLevel + 1) e | none => s!"{spaces (indentLevel + 1)}None"
      s!"{spaces indentLevel}Declare({id}, {ppTau tau},\n{initStr},\n{ppMarkedStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .seq s1 s2 =>
      s!"{spaces indentLevel}Seq(\n{ppMarkedStmRaw (indentLevel + 1) s1},\n{ppMarkedStmRaw (indentLevel + 1) s2}\n{spaces indentLevel})"
  | .ifLit cond thenBranch elseBranch =>
      s!"{spaces indentLevel}If(\n{ppMarkedExprRaw (indentLevel + 1) cond},\n{ppMarkedStmRaw (indentLevel + 1) thenBranch},\n{ppMarkedStmRaw (indentLevel + 1) elseBranch}\n{spaces indentLevel})"
  | .whileLit cond body step =>
      s!"{spaces indentLevel}While(\n{ppMarkedExprRaw (indentLevel + 1) cond},\n{ppMarkedStmRaw (indentLevel + 1) body},\n{ppMarkedStmRaw (indentLevel + 1) step}\n{spaces indentLevel})"
  | .annotation a =>
      s!"{spaces indentLevel}Annotation(\n{ppAnnoRaw (indentLevel + 1) a.node}\n{spaces indentLevel})"

partial def ppMarkedStmRaw (indentLevel : Nat) (stm : MarkedStm) : String :=
  ppStmRaw indentLevel stm.node
end

def ppFunctionDefRaw (fdefn : FunctionDef) : String :=
  let paramsStr := String.intercalate ", " (fdefn.params.map ppParam)
  let annotationsStr := String.intercalate ",\n" (fdefn.annotations.map (ppMarkedStmRaw 2))
  let bodyStr := String.intercalate ",\n" (fdefn.body.map (ppMarkedStmRaw 2))
  s!"FunctionDef({ppTau fdefn.retType}, {fdefn.fname}, ({paramsStr}), [\n{annotationsStr}\n  ], [\n{bodyStr}\n  ])"

def ppGDeclRaw : GDecl → String
  | .fdecl retType fname params external =>
      let paramsStr := String.intercalate ", " (params.map ppParam)
      s!"Fdecl({ppTau retType}, {fname}, external={external}, ({paramsStr}))"
  | .fdefn fdefn => ppFunctionDefRaw fdefn
  | .sdecl name fields =>
      s!"StructDecl({name}, [{String.intercalate ", " (fields.map ppParam)}])"

def ppProgramRaw (program : Program) : String :=
  s!"Program:\n{String.intercalate "\n" (program.map ppGDeclRaw)}"

end Print

end C0VC.ElabbedAst
