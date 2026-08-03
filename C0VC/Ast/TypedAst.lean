import C0VC.Ast.ElabbedAst

namespace C0VC.TypedAst

abbrev Tau := C0VC.ElabbedAst.Tau
abbrev BinOp := C0VC.ElabbedAst.BinOp
abbrev Param := Tau × String
abbrev Field := Tau × String
abbrev Struct := String × (List Field)

mutual
inductive Expr where
  | var (name : String)
  | intLit (val : Int)
  | binop (op : BinOp) (lhs : TypedExpr) (rhs : TypedExpr)
  | ternary (test : TypedExpr) (thenVal : TypedExpr) (elseVal : TypedExpr)
  | trueLit
  | falseLit
  | null
  | charLit (char : Char)
  | stringLit (string : String)
  | call (fname : String) (args : List TypedExpr)
  | length (arrayLike : TypedExpr)
  | result
  | hastag
  | dot (struct : TypedExpr) (field : String)
  | arrow (structPtr : TypedExpr) (field : String)
  | alloc (type : Tau)
  | allocArray (type : Tau) (size : TypedExpr)
  | deref (ptr : TypedExpr)
  | arrAccess (arr : TypedExpr) (index : TypedExpr)

structure TypedExpr where
  node : Expr
  tau : Tau
end

mutual
inductive LValue where
  | var (name : String)
  | deref (ptr : TypedLValue)
  | dot (struct : TypedLValue) (field : String)
  | arrow (structPtr : TypedLValue) (field : String)
  | arrAccess (arr : TypedLValue) (index : TypedExpr)

structure TypedLValue where
  node : LValue
  tau : Tau
end

mutual
inductive Anno where
  | requires (precondition : TypedExpr)
  | ensures (postcondition : TypedExpr)
  | asserts (e : TypedExpr)
  | loopInvariant (e : TypedExpr)
end

mutual
inductive Stm where
  | assign (lhs : TypedLValue) (val : TypedExpr)
  | ifLit (test : TypedExpr) (thenBranch : Stm) (elseBranch : Stm)
  | whileLit (test : TypedExpr) (body : Stm)
  | ret (valOpt : Option TypedExpr)
  | seq (first : Stm) (rest : Stm)
  | declare (varName : String) (type : Tau) (init : Option TypedExpr) (body : Stm)
  | expr (e : TypedExpr)
  | assert (test : TypedExpr)
  | error (e : TypedExpr)
  | nop
  | annotation (a : Anno)
end

structure FunctionDef where
  retType : Tau
  fname : String
  params : List Param
  body : List Stm
  annotations : List Anno
  structs : List Struct := []
  external : Bool := false

abbrev Program := List FunctionDef

namespace Print

def ppBinOp : BinOp → String :=
  C0VC.ElabbedAst.Print.ppBinOp

def ppTau : Tau → String :=
  C0VC.ElabbedAst.Print.ppTau

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
      s!"({ppTypedExpr lhs} {ppBinOp op} {ppTypedExpr rhs})"
  | .ternary test thenBranch elseBranch =>
      s!"({ppTypedExpr test} ? {ppTypedExpr thenBranch} : {ppTypedExpr elseBranch})"
  | .call fname args =>
      let argsStr := String.intercalate ", " (args.map ppTypedExpr)
      s!"{fname}({argsStr})"
  | .length arrayLike => s!"\\length ({ppTypedExpr arrayLike})"
  | .result => "\\result"
  | .hastag => "\\hastag"
  | .dot struct field => s!"{ppTypedExpr struct}.{field}"
  | .arrow structPtr field => s!"{ppTypedExpr structPtr}->{field}"
  | .alloc type => s!"alloc({ppTau type})"
  | .allocArray type size => s!"alloc_array({ppTau type}, {ppTypedExpr size})"
  | .deref ptr => s!"*({ppTypedExpr ptr})"
  | .arrAccess arr index => s!"{ppTypedExpr arr}[{ppTypedExpr index}]"

partial def ppTypedExpr (e : TypedExpr) : String :=
  s!"{ppExpr e.node}:{ppTau e.tau}"
end

mutual
partial def ppLValue : LValue → String
  | .var id => id
  | .deref ptr => s!"*({ppTypedLValue ptr})"
  | .dot struct field => s!"{ppTypedLValue struct}.{field}"
  | .arrow structPtr field => s!"{ppTypedLValue structPtr}->{field}"
  | .arrAccess arr index => s!"{ppTypedLValue arr}[{ppTypedExpr index}]"

partial def ppTypedLValue (lv : TypedLValue) : String :=
  s!"{ppLValue lv.node}:{ppTau lv.tau}"
end

mutual
def ppAnno : Anno → String
  | .requires precondition => s!"//@requires ({ppTypedExpr precondition})"
  | .ensures postcondition => s!"//@ensures ({ppTypedExpr postcondition})"
  | .asserts e => s!"//@asserts ({ppTypedExpr e})"
  | .loopInvariant e => s!"//@loop_invariant ({ppTypedExpr e})"
end

mutual
partial def ppStm : Stm → String
  | .assign lhs e =>
      s!"{ppTypedLValue lhs} = {ppTypedExpr e};"
  | .ret valOpt =>
      match valOpt with
      | some e => s!"return {ppTypedExpr e};"
      | none => "return;"
  | .nop =>
      "/* nop */"
  | .expr e =>
      s!"{ppTypedExpr e};"
  | .assert test =>
      s!"assert({ppTypedExpr test});"
  | .error e =>
      s!"error({ppTypedExpr e});"
  | .declare id tau init body =>
      let bodyStr := ppStm body
      let declStr :=
        match init with
        | some e => s!"{ppTau tau} {id} = {ppTypedExpr e};"
        | none => s!"{ppTau tau} {id};"
      if bodyStr.isEmpty || bodyStr == "/* nop */" then declStr else s!"{declStr}\n{bodyStr}"
  | .seq s1 s2 =>
      s!"{ppStm s1}\n{ppStm s2}"
  | .ifLit cond thenBranch elseBranch =>
      let thenStr := indent (ppStm thenBranch)
      let elseStr := ppStm elseBranch
      if elseStr == "/* nop */" then
        s!"if ({ppTypedExpr cond}) \{\n{thenStr}\n}"
      else
        s!"if ({ppTypedExpr cond}) \{\n{thenStr}\n} else \{\n{indent elseStr}\n}"
  | .whileLit cond body =>
      s!"while ({ppTypedExpr cond}) \{\n{indent (ppStm body)}\n}"
  | .annotation a => s!"{ppAnno a}"
end

def ppStms (stms : List Stm) : String :=
  String.intercalate "" (stms.map fun stm => indent (ppStm stm) ++ "\n")

def ppParam : Param → String
  | (tau, id) => s!"{ppTau tau} {id}"

def ppParams (params : List Param) : String :=
  let paramsStr := String.intercalate ", " (params.map ppParam)
  s!"({paramsStr})"

def ppAnnos (annos : List Anno) : String :=
  let annosStr := String.intercalate ", " (annos.map ppAnno)
  s!"[{annosStr}]"

def ppFunctionDef (fdefn : FunctionDef) : String :=
  if fdefn.external then
    s!"external {ppTau fdefn.retType} {fdefn.fname}{ppParams fdefn.params};"
  else if fdefn.body.isEmpty then
    s!"{ppAnnos fdefn.annotations}\n{ppTau fdefn.retType} {fdefn.fname}{ppParams fdefn.params} \{\n}"
  else
    s!"{ppAnnos fdefn.annotations}\n{ppTau fdefn.retType} {fdefn.fname}{ppParams fdefn.params} \{\n{ppStms fdefn.body}}"

def ppProgram (program : Program) : String :=
  String.intercalate "\n\n" (program.map ppFunctionDef)

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
      s!"{spaces indentLevel}Binop({ppBinOp op},\n{ppTypedExprRaw (indentLevel + 1) lhs},\n{ppTypedExprRaw (indentLevel + 1) rhs}\n{spaces indentLevel})"
  | .ternary test thenBranch elseBranch =>
      s!"{spaces indentLevel}Ternary(\n{ppTypedExprRaw (indentLevel + 1) test},\n{ppTypedExprRaw (indentLevel + 1) thenBranch},\n{ppTypedExprRaw (indentLevel + 1) elseBranch}\n{spaces indentLevel})"
  | .call fname args =>
      let argsStr := String.intercalate ",\n" (args.map (ppTypedExprRaw (indentLevel + 1)))
      s!"{spaces indentLevel}Call({fname}, [\n{argsStr}\n{spaces indentLevel}])"
  | .length arrayLike =>
      s!"{spaces indentLevel}Length(\n{ppTypedExprRaw (indentLevel + 1) arrayLike}\n{spaces indentLevel})"
  | .result => s!"{spaces indentLevel}Result"
  | .hastag => s!"{spaces indentLevel}Hastag"
  | .dot struct field =>
      s!"{spaces indentLevel}Dot(\n{ppTypedExprRaw (indentLevel + 1) struct},\n{spaces (indentLevel + 1)}{field}\n{spaces indentLevel})"
  | .arrow structPtr field =>
      s!"{spaces indentLevel}Arrow(\n{ppTypedExprRaw (indentLevel + 1) structPtr},\n{spaces (indentLevel + 1)}{field}\n{spaces indentLevel})"
  | .alloc type =>
      s!"{spaces indentLevel}Alloc({ppTau type})"
  | .allocArray type size =>
      s!"{spaces indentLevel}AllocArray({ppTau type},\n{ppTypedExprRaw (indentLevel + 1) size}\n{spaces indentLevel})"
  | .deref ptr =>
      s!"{spaces indentLevel}Deref(\n{ppTypedExprRaw (indentLevel + 1) ptr}\n{spaces indentLevel})"
  | .arrAccess arr index =>
      s!"{spaces indentLevel}ArrAccess(\n{ppTypedExprRaw (indentLevel + 1) arr},\n{ppTypedExprRaw (indentLevel + 1) index}\n{spaces indentLevel})"

partial def ppTypedExprRaw (indentLevel : Nat) (e : TypedExpr) : String :=
  s!"{spaces indentLevel}TypedExpr({ppTau e.tau},\n{ppExprRaw (indentLevel + 1) e.node}\n{spaces indentLevel})"
end

def ppAnnoRaw (indentLevel : Nat) : Anno → String
  | .requires precondition =>
      s!"{spaces indentLevel}Requires(\n{ppTypedExprRaw (indentLevel + 1) precondition}\n{spaces indentLevel})"
  | .ensures postcondition =>
      s!"{spaces indentLevel}Ensures(\n{ppTypedExprRaw (indentLevel + 1) postcondition}\n{spaces indentLevel})"
  | .asserts e =>
      s!"{spaces indentLevel}Asserts(\n{ppTypedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"
  | .loopInvariant e =>
      s!"{spaces indentLevel}LoopInvariant(\n{ppTypedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"

partial def ppStmRaw (indentLevel : Nat) : Stm → String
  | .assign lhs e =>
      s!"{spaces indentLevel}Assign({ppTypedLValue lhs},\n{ppTypedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"
  | .ret valOpt =>
      match valOpt with
      | some e => s!"{spaces indentLevel}Ret(\n{ppTypedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"
      | none => s!"{spaces indentLevel}Ret(None)"
  | .nop =>
      s!"{spaces indentLevel}Nop"
  | .expr e =>
      s!"{spaces indentLevel}Expr(\n{ppTypedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"
  | .assert test =>
      s!"{spaces indentLevel}Assert(\n{ppTypedExprRaw (indentLevel + 1) test}\n{spaces indentLevel})"
  | .error e =>
      s!"{spaces indentLevel}Error(\n{ppTypedExprRaw (indentLevel + 1) e}\n{spaces indentLevel})"
  | .declare id tau init body =>
      let initStr := match init with | some e => ppTypedExprRaw (indentLevel + 1) e | none => s!"{spaces (indentLevel + 1)}None"
      s!"{spaces indentLevel}Declare({id}, {ppTau tau},\n{initStr},\n{ppStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .seq s1 s2 =>
      s!"{spaces indentLevel}Seq(\n{ppStmRaw (indentLevel + 1) s1},\n{ppStmRaw (indentLevel + 1) s2}\n{spaces indentLevel})"
  | .ifLit cond thenBranch elseBranch =>
      s!"{spaces indentLevel}If(\n{ppTypedExprRaw (indentLevel + 1) cond},\n{ppStmRaw (indentLevel + 1) thenBranch},\n{ppStmRaw (indentLevel + 1) elseBranch}\n{spaces indentLevel})"
  | .whileLit cond body =>
      s!"{spaces indentLevel}While(\n{ppTypedExprRaw (indentLevel + 1) cond},\n{ppStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .annotation a =>
      s!"{spaces indentLevel}Annotation(\n{ppAnnoRaw (indentLevel + 1) a}\n{spaces indentLevel})"

def ppFunctionDefRaw (fdefn : FunctionDef) : String :=
  let paramsStr := String.intercalate ", " (fdefn.params.map ppParam)
  let annotationsStr := String.intercalate ",\n" (fdefn.annotations.map (ppAnnoRaw 2))
  let bodyStr := String.intercalate ",\n" (fdefn.body.map (ppStmRaw 2))
  s!"FunctionDef({ppTau fdefn.retType}, {fdefn.fname}, external={fdefn.external}, ({paramsStr}), [\n{annotationsStr}\n  ], [\n{bodyStr}\n  ])"

def ppProgramRaw (program : Program) : String :=
  s!"Program:\n{String.intercalate "\n" (program.map ppFunctionDefRaw)}"

end Print

end C0VC.TypedAst
