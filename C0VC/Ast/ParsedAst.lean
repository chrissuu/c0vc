/-
AST Core Definitions

See C0 reference manual here: https://c0.cs.cmu.edu/docs/c0-reference.pdf

Author: Chris Su <chrjs@cmu.edu>
-/

import C0VC.Utils.SrcSpan

open C0VC.Utils.SrcSpan

namespace C0VC.Ast

inductive AssignOp where
  | assign     -- assignment
  | plusEq     -- +=
  | subEq      -- -=
  | mulEq      -- *=
  | divEq      -- /=
  | modEq      -- %=
  | bitAndEq   -- &=
  | xorEq      -- ^=
  | bitOrEq    -- |=
  | shlEq      -- <<=
  | shrEq      -- >>=

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
  | land
  | lor
  | bitAnd
  | xor
  | bitOr
  | shl
  | shr
deriving Inhabited

inductive UnOp where
  | bang
  | bitNot
  | negative
deriving BEq, DecidableEq, Inhabited

inductive Tau where
  | int
  | char
  | string
  | bool
  | void
  | typeName (name : String)
  | struct (name : String)
deriving Inhabited

mutual
inductive Expr where
  | var   (name : String)

  -- this is an Int here which gets lowered to Int32 in downstream
  -- the typechecker enforces the bounds of representable I32 range
  | intLit (val : Int)
  | binop (op : BinOp) (lhs : MarkedExpr) (rhs : MarkedExpr)
  | unop (op : UnOp) (operand : MarkedExpr)
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
  | assign (varName : String) (val : MarkedExpr)
  -- this encapsulates both ite and if statements. If no elseBranch is needed, the elseBranch is simply Nop
  | ifLit (test : MarkedExpr) (thenBranch : MarkedStm) (elseBranch : MarkedStm)
  | whileLit (test : MarkedExpr) (body : MarkedStm) (step : MarkedStm)
  -- none in the case of void functions.
  | ret (valOpt : Option MarkedExpr)
  | seq (first : MarkedStm) (rest : MarkedStm)
  | declare (varName : String) (type : Tau) (init : Option MarkedExpr) (body : MarkedStm)
  | asop (varName : String) (op : AssignOp) (value : MarkedExpr)
  | forLit (init : MarkedStm) (test : MarkedExpr) (update : MarkedStm) (body : MarkedStm)
  -- handles well-typed lines of the form [MarkedExpr];
  | expr : MarkedExpr -> Stm
  | assert (test : MarkedExpr)
  | error (e : MarkedExpr)
  | nop
  | annotation (a : MarkedAnno)

  | incr (varName : String)
  | decr (varName : String)
deriving Inhabited

structure MarkedStm where
  node : Stm
  span : Option SrcSpan
deriving Inhabited
end

abbrev Param := Tau × String
abbrev Field := Tau × String

inductive GDecl where
  | fdecl (retType : Tau) (fname : String) (params : List Param) (annotations : List MarkedStm)
  | fdefn (retType : Tau) (fname : String) (params : List Param) (body : List MarkedStm) (annotations : List MarkedStm)
  | typedef (type : Tau) (alias : String)
  | sdecl (name : String) (fields : List Field)
deriving Inhabited

abbrev Program := List GDecl

namespace Print

def ppAssignOp : AssignOp → String
  | .assign => "="
  | .plusEq => "+="
  | .subEq => "-="
  | .mulEq => "*="
  | .divEq => "/="
  | .modEq => "%="
  | .bitAndEq => "&="
  | .xorEq => "^="
  | .bitOrEq => "|="
  | .shlEq => "<<="
  | .shrEq => ">>="

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
  | .land => "&&"
  | .lor => "||"
  | .bitAnd => "&"
  | .xor => "^"
  | .bitOr => "|"
  | .shl => "<<"
  | .shr => ">>"

def ppUnOp : UnOp → String
  | .bang => "!"
  | .bitNot => "~"
  | .negative => "-"

def ppTau : Tau → String
  | .string => "string"
  | .char => "char"
  | .int => "int"
  | .bool => "bool"
  | .void => "void"
  | .typeName t => t
  | .struct s => s!"struct {s}"

private def indent (str : String) : String :=
  str.splitOn "\n"
    |> List.map (fun line => "  " ++ line)
    |> String.intercalate "\n"

private def trimTrailingSemicolon (str : String) : String :=
  match str.toList.reverse with
  | ';' :: rest => String.ofList rest.reverse
  | _ => str

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
  | .unop op operand =>
      s!"{ppUnOp op}({ppMarkedExpr operand})"
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
  | .assign id e =>
      s!"{id} = {ppMarkedExpr e};"
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
  | .forLit init cond update body =>
      s!"for ({trimTrailingSemicolon (ppMarkedStm init)}; {ppMarkedExpr cond}; {trimTrailingSemicolon (ppMarkedStm update)}) \{\n{indent (ppMarkedStm body)}\n}"
  | .asop id op e =>
      s!"{id} {ppAssignOp op} {ppMarkedExpr e};"

  | .annotation a => s!"{ppMarkedAnno a}"
  | .incr id => s!"{id}++"
  | .decr id => s!"{id}--"

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

def ppGDecl : GDecl → String
  | .typedef tau id =>
      s!"typedef {ppTau tau} {id};"
  | .sdecl name fields =>
      s!"struct {name} \{\n{ppFields fields}\n};"
  | .fdecl ret id params annotations =>
      s!"{ppAnnos annotations}\{\n}{ppTau ret} {id}{ppParams params};"
  | .fdefn ret id params stms annotations =>
      if stms.isEmpty then
        s!"{ppAnnos annotations}\n{ppTau ret} {id}{ppParams params} \{\n}"
      else
        s!"{ppAnnos annotations}\n{ppTau ret} {id}{ppParams params} \{\n{ppStms stms}}"

def ppProgram (program : Program) : String :=
  String.intercalate "\n\n" (program.map ppGDecl)

mutual
partial def ppStmRaw (indentLevel : Nat) : Stm → String
  | .assign id e =>
      s!"{spaces indentLevel}Assign({id}, {ppMarkedExpr e})"
  | .ret valOpt =>
      let retStr := match valOpt with | some e => ppMarkedExpr e | none => "None"
      s!"{spaces indentLevel}Return({retStr})"
  | .nop =>
      s!"{spaces indentLevel}Nop"
  | .expr e =>
      s!"{spaces indentLevel}Expr({ppMarkedExpr e})"
  | .declare id tau init body =>
      let initStr := match init with | some e => ppMarkedExpr e | none => "None"
      s!"{spaces indentLevel}Declare({id}, {ppTau tau}, {initStr},\n{ppMarkedStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .seq s1 s2 =>
      s!"{spaces indentLevel}Seq(\n{ppMarkedStmRaw (indentLevel + 1) s1},\n{ppMarkedStmRaw (indentLevel + 1) s2}\n{spaces indentLevel})"
  | .ifLit cond thenBranch elseBranch =>
      s!"{spaces indentLevel}If({ppMarkedExpr cond},\n{ppMarkedStmRaw (indentLevel + 1) thenBranch},\n{ppMarkedStmRaw (indentLevel + 1) elseBranch}\n{spaces indentLevel})"
  | .whileLit cond body step =>
      s!"{spaces indentLevel}While({ppMarkedExpr cond},\n{ppMarkedStmRaw (indentLevel + 1) body},\n{ppMarkedStmRaw (indentLevel + 1) step}\n{spaces indentLevel})"
  | .forLit init cond update body =>
      s!"{spaces indentLevel}For(\n{ppMarkedStmRaw (indentLevel + 1) init},\n{spaces (indentLevel + 1)}{ppMarkedExpr cond},\n{ppMarkedStmRaw (indentLevel + 1) update},\n{ppMarkedStmRaw (indentLevel + 1) body}\n{spaces indentLevel})"
  | .asop id op e =>
      s!"{spaces indentLevel}Asop({id}, {ppAssignOp op}, {ppMarkedExpr e})"
  | .assert test =>
      s!"{spaces indentLevel}Assert({ppMarkedExpr test})"
  | .error e =>
      s!"{spaces indentLevel}Error({ppMarkedExpr e})"
  | .annotation a =>
      s!"{spaces indentLevel}Annotation({ppMarkedAnno a})"

  | .incr id =>
      s!"{spaces indentLevel}Incr({id})"
  | .decr id =>
      s!"{spaces indentLevel}Decr({id})"

partial def ppMarkedStmRaw (indentLevel : Nat) (stm : MarkedStm) : String :=
  ppStmRaw indentLevel stm.node
end

def ppStmsRaw (stms : List MarkedStm) : String :=
  String.intercalate "\n" (stms.map (ppMarkedStmRaw 0))

def ppGDeclRaw : GDecl → String
  | .typedef tau id =>
      s!"Typedef({ppTau tau}, {id})"
  | .sdecl name fields =>
      s!"StructDecl({name}, [{String.intercalate ", " (fields.map ppParam)}])"
  | .fdecl ret id params annotations =>
      s!"Fdecl({ppTau ret}, {id}, [{String.intercalate ", " (params.map ppParam)}], [{String.intercalate ", " (annotations.map ppMarkedStm)}])"
  | .fdefn ret id params stms annotations =>
      s!"Fdefn({ppTau ret}, {id}, [{String.intercalate ", " (params.map ppParam)}], [\n{ppStmsRaw stms}\n], [{String.intercalate ", " (annotations.map ppMarkedStm)}])"

def ppProgramRaw (program : Program) : String :=
  s!"Program:\n{String.intercalate "\n" (program.map ppGDeclRaw)}"

end Print

instance : ToString Program where
  toString := Print.ppProgram

end C0VC.Ast
