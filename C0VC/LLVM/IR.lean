import C0VC.Utils.Label
import C0VC.Utils.Temp
open C0VC.Utils.Label
open C0VC.Utils.Temp

namespace C0VC.LLVM.IR

inductive Tau where
  | i1
  | i8
  | i32
  | void
  | ptr
  | struct (name : String)
deriving Inhabited

abbrev ValName := String
abbrev Arg := Tau × ValName

inductive Callee where
  | source (fname : String)
  | external (fname : String)
  | runtime (fname : String)
deriving Inhabited

inductive BinOp where
  | add
  | sub
  | mul
  | sdiv
  | srem
  | and
  | xor
  | or
  | shl
  | ashr
  | slt
  | sgt
  | sle
  | sge
  | eq
  | ne
deriving Inhabited

inductive Val where
  | void
  | var (t : Temp)
  | ptr (t : Temp)
  | null
  /-- Types are enforced upstream by typechecker. At this point, types are only needed for LLVM emitting,
  so treating (most) types as 32-bit bitvectors allows for the full range of Tau's to be represented
  conveniently. -/
  | bitVec (bitVec : BitVec 32)
deriving Inhabited

inductive Expr where
  | binop (op : BinOp) (tau : Tau) (lhs : Val) (rhs : Val)
  | call (tau : Tau) (callee : Callee) (args : List (Tau × Val))
deriving Inhabited

inductive Stm where
  | assign (dest : Val) (exp : Expr)
  | callVoid (callee : Callee) (args : List (Tau × Val))
  | label (l : Label)
  | brJump (l : Label)
  | brIte (val : Val) (thenBranch : Label) (elseBranch : Label)
  | ret (val : Val)
  | alloca (ptr : Val) (type : Tau)
  | store (tau : Tau) (val : Val) (ptr : Val)
  | load (dest : Val) (tau : Tau) (ptr : Val)
  | gep (dest : Val) (sourceType : Tau) (base : Val) (indices : List (Tau × Val))
deriving Inhabited

structure FunctionDef where
  fname : String
  tau : Tau
  args : List Arg
  stms : List Stm
  structs : List (String × List Tau) := []
  external : Bool := false

abbrev Program := List FunctionDef

namespace Print
private def spaces (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

def ppTau : Tau → String
  | .i1 => "i1"
  | .i8 => "i8"
  | .i32 => "i32"
  | .void => "void"
  | .ptr => "ptr"
  | .struct name => s!"%struct.{name}"

def ppBinOp : BinOp → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .sdiv => "sdiv"
  | .srem => "srem"
  | .and => "and"
  | .xor => "xor"
  | .or => "or"
  | .shl => "shl"
  | .ashr => "ashr"
  | .slt => "slt"
  | .sgt => "sgt"
  | .sle => "sle"
  | .sge => "sge"
  | .eq => "eq"
  | .ne => "ne"

def ppVal : Val → String
  | .void => "void"
  | .var t => t.name
  | .ptr t => s!"*{t.name}"
  | .null => "null"
  | .bitVec bitVec => toString (Int32.ofInt bitVec.toInt)

def ppArg (arg : Arg) : String :=
  let (tau, name) := arg
  s!"{ppTau tau} {name}"

def ppCallee : Callee → String
  | .source fname => s!"source {fname}"
  | .external fname => s!"external {fname}"
  | .runtime fname => s!"runtime {fname}"

def ppTypedVal (typedVal : Tau × Val) : String :=
  let (tau, val) := typedVal
  s!"{ppTau tau} {ppVal val}"

def ppExpr : Expr → String
  | .binop op tau lhs rhs => s!"{ppBinOp op} {ppTau tau} {ppVal lhs}, {ppVal rhs}"
  | .call tau callee args =>
      s!"call {ppTau tau} {ppCallee callee}({String.intercalate ", " (args.map ppTypedVal)})"

def ppStm : Stm → String
  | .assign dest exp => s!"{ppVal dest} <- {ppExpr exp};"
  | .callVoid callee args =>
      s!"call void {ppCallee callee}({String.intercalate ", " (args.map ppTypedVal)});"
  | .label l => s!"{l.name}:"
  | .brJump l => s!"br {l.name};"
  | .brIte val thenBranch elseBranch =>
      s!"br {ppVal val}, {thenBranch.name}, {elseBranch.name};"
  | .ret val => s!"ret {ppVal val};"
  | .alloca ptr tau => s!"alloca {ppVal ptr} : {ppTau tau};"
  | .store tau val ptr => s!"store {ppTau tau} {ppVal val} -> {ppVal ptr};"
  | .load dest tau ptr => s!"{ppVal dest} <- load {ppTau tau} {ppVal ptr};"
  | .gep dest sourceType base indices =>
      s!"{ppVal dest} <- gep {ppTau sourceType} {ppVal base}, {String.intercalate ", " (indices.map ppTypedVal)};"

def ppFunctionDef (fdef : FunctionDef) : String :=
  if fdef.external then
    s!"external {ppTau fdef.tau} {fdef.fname}({String.intercalate ", " (fdef.args.map ppArg)})"
  else
    s!"{ppTau fdef.tau} {fdef.fname}({String.intercalate ", " (fdef.args.map ppArg)})\n"
    ++ String.intercalate "\n" (fdef.stms.map ppStm)

def ppProgram (program : Program) : String :=
  String.intercalate "\n\n" (program.map ppFunctionDef)

def ppValRaw : Val → String
  | .void => "Void"
  | .var t => s!"Var({t.name})"
  | .ptr t => s!"Ptr({t.name})"
  | .null => "Null"
  | .bitVec bitVec => s!"BitVec32({Int32.ofInt bitVec.toInt})"

def ppTypedValRaw (typedVal : Tau × Val) : String :=
  let (tau, val) := typedVal
  s!"({ppTau tau}, {ppValRaw val})"

def ppCalleeRaw : Callee → String
  | .source fname => s!"Source({fname})"
  | .external fname => s!"External({fname})"
  | .runtime fname => s!"Runtime({fname})"

def ppExprRaw (indentLevel : Nat) : Expr → String
  | .binop op tau lhs rhs =>
      s!"{spaces indentLevel}Binop({ppBinOp op}, {ppTau tau},\n"
      ++ s!"{spaces (indentLevel + 1)}{ppValRaw lhs},\n"
      ++ s!"{spaces (indentLevel + 1)}{ppValRaw rhs}\n"
      ++ s!"{spaces indentLevel})"
  | .call tau callee args =>
      s!"{spaces indentLevel}Call({ppTau tau}, {ppCalleeRaw callee}, ["
      ++ String.intercalate ", " (args.map ppTypedValRaw)
      ++ "])"

def ppStmRaw (indentLevel : Nat) : Stm → String
  | .assign dest exp =>
      s!"{spaces indentLevel}Assign({ppValRaw dest},\n{ppExprRaw (indentLevel + 1) exp}\n{spaces indentLevel})"
  | .callVoid callee args =>
      s!"{spaces indentLevel}CallVoid({ppCalleeRaw callee}, [{String.intercalate ", " (args.map ppTypedValRaw)}])"
  | .label l =>
      s!"{spaces indentLevel}Label({l.name})"
  | .brJump l =>
      s!"{spaces indentLevel}BrJump({l.name})"
  | .brIte val thenBranch elseBranch =>
      s!"{spaces indentLevel}BrIte({ppValRaw val}, {thenBranch.name}, {elseBranch.name})"
  | .ret val =>
      s!"{spaces indentLevel}Ret({ppValRaw val})"
  | .alloca ptr tau =>
      s!"{spaces indentLevel}Alloca({ppValRaw ptr}, {ppTau tau})"
  | .store tau val ptr =>
      s!"{spaces indentLevel}Store({ppTau tau}, {ppValRaw val}, {ppValRaw ptr})"
  | .load dest tau ptr =>
      s!"{spaces indentLevel}Load({ppValRaw dest}, {ppTau tau}, {ppValRaw ptr})"
  | .gep dest sourceType base indices =>
      s!"{spaces indentLevel}Gep({ppValRaw dest}, {ppTau sourceType}, {ppValRaw base}, [{String.intercalate ", " (indices.map ppTypedValRaw)}])"

def ppFunctionDefRaw (fdef : FunctionDef) : String :=
  let argsStr := String.intercalate ", " (fdef.args.map ppArg)
  let stmsStr := String.intercalate "\n" (fdef.stms.map (ppStmRaw 1))
  s!"Fdefn({ppTau fdef.tau}, {fdef.fname}, external={fdef.external}, [{argsStr}], [\n{stmsStr}\n])"

def ppProgramRaw (program : Program) : String :=
  "Program:\n" ++ String.intercalate "\n\n" (program.map ppFunctionDefRaw)

end Print

instance : ToString BinOp where
  toString := Print.ppBinOp

instance : ToString Val where
  toString := Print.ppVal

instance : ToString Expr where
  toString := Print.ppExpr

instance : ToString Stm where
  toString := Print.ppStm

instance : ToString Program where
  toString := Print.ppProgram

end C0VC.LLVM.IR
