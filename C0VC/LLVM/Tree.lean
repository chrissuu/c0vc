/-
Tree Representation

Author(s):
  ~ Chris Su <chrjs@cmu.edu>
-/
import C0VC.Utils.Temp
import C0VC.Utils.Label
import C0VC.LLVM.Runtime

namespace C0VC.LLVM.Tree

open C0VC.Utils.Temp
open C0VC.Utils.Label
open C0VC.LLVM.Runtime

-- TODO: maybe consider deduplicating this definition against AST.BinOp?
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
  | bool
  | void
  | ptr (tau : Tau)
  | array (tau : Tau)
  | struct (name : String)
  | null
deriving Inhabited

inductive Expr where
  -- TODO: consider changing val type to val opt type to support voids
  -- eventually, will have to move this type to something more expressive
  -- than ints to be able to support chars/strings/etc
  | const (tau : Tau) (val : Int32)
  | temp (t : Temp)
  | binop (op : BinOp) (tau : Tau) (lhs : Expr) (rhs : Expr)
  | call (fname : String) (args : List Expr)
  | runtimeCall (fn : Runtime.Fn) (args : List Expr)
  | null
  | alloc (tau : Tau)
  | allocArray (tau : Tau) (size : Expr)
  | deref (ptr : Expr) (tau : Tau)
  | dot (struct : Expr) (structName : String) (fieldIndex : Nat) (fieldTau : Tau)
  | arrow (structPtr : Expr) (structName : String) (fieldIndex : Nat) (fieldTau : Tau)
  | arrAccess (arr : Expr) (index : Expr) (elemTau : Tau)
deriving Inhabited

inductive Command where
  | declare (dest : Temp) (tau : Tau)
  | move (dest : Temp) (src : Expr)
  | store (dest : Expr) (src : Expr)
  | call (fname : String) (args : List Expr)
  | runtimeCall (fn : Runtime.Fn) (args : List Expr)
  | ite (test : Expr) (thenBranch : Label) (elseBranch : Label)
  | goto (label : Label)
  | label (l : Label)
  | ret (valOpt : Option Expr)
deriving Inhabited

abbrev Arg := Tau × Temp

structure FunctionDef where
  fname : String
  tau : Tau
  args : List Arg
  commands : List Command
  structs : List (String × List (Tau × String)) := []
  external : Bool := false

abbrev Program := List FunctionDef

namespace Print

private def spaces (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

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
  | .int => "int"
  | .bool => "bool"
  | .void => "void"
  | .ptr tau => s!"{ppTau tau}*"
  | .array tau => s!"{ppTau tau}[]"
  | .struct name => s!"struct {name}"
  | .null => "null"

def ppArg (arg : Arg) : String :=
  let (tau, temp) := arg
  s!"{ppTau tau} {temp.name}"

partial def ppExpr : Expr → String
  -- TODO: print the type of the const?
  | .const _ val => toString val
  | .temp t => t.name

  -- TODO: pp the type
  | .binop op _ lhs rhs => s!"({ppExpr lhs} {ppBinOp op} {ppExpr rhs})"
  | .call fname args => s!"call {fname}({String.intercalate ", " (List.map ppExpr args)})"
  | .runtimeCall fn args => s!"runtime_call {Runtime.name fn}({String.intercalate ", " (List.map ppExpr args)})"
  | .null => "NULL"
  | .alloc tau => s!"alloc({ppTau tau})"
  | .allocArray tau size => s!"alloc_array({ppTau tau}, {ppExpr size})"
  | .deref ptr _ => s!"*({ppExpr ptr})"
  | .dot struct _ idx _ => s!"{ppExpr struct}.#{idx}"
  | .arrow structPtr _ idx _ => s!"{ppExpr structPtr}->#{idx}"
  | .arrAccess arr index _ => s!"{ppExpr arr}[{ppExpr index}]"

def ppCommand : Command → String
  | .declare dest tau => s!"{dest.name} : {ppTau tau};"
  | .move dest src => s!"{dest.name} <- {ppExpr src};"
  | .store dest src => s!"{ppExpr dest} <- {ppExpr src};"
  | .call fname args =>
      s!"call {fname}({String.intercalate ", " (List.map ppExpr args)});"
  | .runtimeCall fn args =>
      s!"runtime_call {Runtime.name fn}({String.intercalate ", " (List.map ppExpr args)});"
  | .ite test thenBranch elseBranch =>
      s!"if ({ppExpr test}) goto {thenBranch.name} else goto {elseBranch.name}"
  | .goto label => s!"goto {label.name};"
  | .label l => s!"{l.name}:"
  | .ret valOpt =>
      match valOpt with
      | some val => s!"return {ppExpr val};"
      | none => "return;"

def ppCommandIndented (cmd : Command) : String :=
  match cmd with
  | .label _ => ppCommand cmd
  | _ => "  " ++ ppCommand cmd

def ppFunctionDef (fdef : FunctionDef) : String :=
  let cmdsStr := String.intercalate "\n" (fdef.commands.map ppCommandIndented)
  if fdef.external then
    s!"external {ppTau fdef.tau} {fdef.fname}({String.intercalate ", " (List.map ppArg fdef.args)});"
  else
    s!"{ppTau fdef.tau} {fdef.fname}({String.intercalate ", " (List.map ppArg fdef.args)}) \{\n{cmdsStr}\n}"

def ppProgram (program : Program) : String :=
  String.intercalate "\n\n" (program.map ppFunctionDef)

mutual
partial def ppExprRaw (indentLevel : Nat) : Expr → String
  | .const tau val =>
      s!"{spaces indentLevel}Const({val}):{ppTau tau}"
  | .temp t =>
      s!"{spaces indentLevel}Temp({t.name})"
  -- TODO: pp the type
  | .binop op _ lhs rhs =>
      s!"{spaces indentLevel}Binop({ppBinOp op},\n{ppExprRaw (indentLevel + 1) lhs},\n{ppExprRaw (indentLevel + 1) rhs}\n{spaces indentLevel})"
  | .call fname args =>
      let argsStr := String.intercalate ",\n" (args.map (ppExprRaw (indentLevel + 1)))
      s!"{spaces indentLevel}Call({fname}, [\n{argsStr}\n{spaces indentLevel}])"
  | .runtimeCall fn args =>
      let argsStr := String.intercalate ",\n" (args.map (ppExprRaw (indentLevel + 1)))
      s!"{spaces indentLevel}RuntimeCall({Runtime.name fn}, [\n{argsStr}\n{spaces indentLevel}])"
  | .null =>
      s!"{spaces indentLevel}Null"
  | .alloc tau =>
      s!"{spaces indentLevel}Alloc({ppTau tau})"
  | .allocArray tau size =>
      s!"{spaces indentLevel}AllocArray({ppTau tau},\n{ppExprRaw (indentLevel + 1) size}\n{spaces indentLevel})"
  | .deref ptr tau =>
      s!"{spaces indentLevel}Deref({ppTau tau},\n{ppExprRaw (indentLevel + 1) ptr}\n{spaces indentLevel})"
  | .dot struct structName idx tau =>
      s!"{spaces indentLevel}Dot({structName}, {idx}, {ppTau tau},\n{ppExprRaw (indentLevel + 1) struct}\n{spaces indentLevel})"
  | .arrow structPtr structName idx tau =>
      s!"{spaces indentLevel}Arrow({structName}, {idx}, {ppTau tau},\n{ppExprRaw (indentLevel + 1) structPtr}\n{spaces indentLevel})"
  | .arrAccess arr index tau =>
      s!"{spaces indentLevel}ArrAccess({ppTau tau},\n{ppExprRaw (indentLevel + 1) arr},\n{ppExprRaw (indentLevel + 1) index}\n{spaces indentLevel})"

partial def ppCommandRaw (indentLevel : Nat) : Command → String
  | .declare dest tau =>
      s!"{spaces indentLevel}Declare({dest.name}, {ppTau tau})"
  | .move dest src =>
      s!"{spaces indentLevel}Move({dest.name},\n{ppExprRaw (indentLevel + 1) src}\n{spaces indentLevel})"
  | .store dest src =>
      s!"{spaces indentLevel}Store(\n{ppExprRaw (indentLevel + 1) dest},\n{ppExprRaw (indentLevel + 1) src}\n{spaces indentLevel})"
  | .call fname args =>
      let argsStr := String.intercalate ",\n" (args.map (ppExprRaw (indentLevel + 1)))
      s!"{spaces indentLevel}Call({fname}, [\n{argsStr}\n{spaces indentLevel}])"
  | .runtimeCall fn args =>
      let argsStr := String.intercalate ",\n" (args.map (ppExprRaw (indentLevel + 1)))
      s!"{spaces indentLevel}RuntimeCall({Runtime.name fn}, [\n{argsStr}\n{spaces indentLevel}])"
  | .ite test thenBranch elseBranch =>
      s!"{spaces indentLevel}Ite(\n{ppExprRaw (indentLevel + 1) test},\n{spaces (indentLevel + 1)}{thenBranch.name},\n{spaces (indentLevel + 1)}{elseBranch.name}\n{spaces indentLevel})"
  | .goto label =>
      s!"{spaces indentLevel}Goto({label.name})"
  | .label l =>
      s!"{spaces indentLevel}Label({l.name})"
  | .ret valOpt =>
      match valOpt with
      | some val =>
          s!"{spaces indentLevel}Ret(\n{ppExprRaw (indentLevel + 1) val}\n{spaces indentLevel})"
      | none =>
          s!"{spaces indentLevel}Ret(None)"
end

def ppFunctionDefRaw (fdef : FunctionDef) : String :=
  let argsStr := String.intercalate ", " (fdef.args.map ppArg)
  let cmdsStr := String.intercalate "\n" (fdef.commands.map (ppCommandRaw 1))
  s!"Fdefn({ppTau fdef.tau}, {fdef.fname}, external={fdef.external}, [{argsStr}], [\n{cmdsStr}\n])"

def ppProgramRaw (program : Program) : String :=
  s!"Program:\n{String.intercalate "\n" (program.map ppFunctionDefRaw)}"

end Print

instance : ToString BinOp where
  toString := Print.ppBinOp

instance : ToString Expr where
  toString := Print.ppExpr

instance : ToString Command where
  toString := Print.ppCommand

instance : ToString Program where
  toString := Print.ppProgram

end C0VC.LLVM.Tree
