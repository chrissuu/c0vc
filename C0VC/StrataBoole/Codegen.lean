import C0VC.StrataBoole.IR

/-!
StrataBoole.Codegen

Renders the Boole IR as StrataBoole source text. Every compound expression is
parenthesized, so the output does not depend on Boole operator precedence.
C0 ints are rendered according to the program's `IntModel`.
-/

namespace C0VC.StrataBoole.Codegen

open C0VC.StrataBoole

abbrev ProgramText := String

private def spaces (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

private def indent (level : Nat) (s : String) : String :=
  spaces level ++ s

private def parens (s : String) : String :=
  "(" ++ s ++ ")"

private def commaSep (xs : List String) : String :=
  String.intercalate ", " xs

private def twoPow32 : Int := 4294967296

partial def ppTau (model : IntModel) : Tau → String
  | .int => if model == .bv32 then "bv W32" else "int"
  | .bool => "bool"
  | .ref | .math => "int"
  | .string => "C0String"
  | .map key val => s!"Map {ppTauArg model key} {ppTauArg model val}"
where
  ppTauArg (model : IntModel) (tau : Tau) : String :=
    let s := ppTau model tau
    if s.contains ' ' then parens s else s

private def ppMathLit (n : Int) : String :=
  if n < 0 then parens s!"-{n.natAbs}" else toString n

private def ppIntLit (model : IntModel) (n : Int) : String :=
  match model with
  | .bv32 => s!"bv\{32}({n % twoPow32})"
  | .checked => ppMathLit n

private def bvArithOp : ArithOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "sdiv"
  | .mod => "smod"
  | .bitAnd => "&"
  | .bitOr => "|"
  | .xor => "^"
  | .shl => "<<"
  | .shr => "ashr"

private def mathArithOp : ArithOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | _ => "div"

private def mathCmpOp : CmpOp → String
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="

private def bvCmpOp : CmpOp → String
  | .lt => "slt"
  | .le => "sle"
  | .gt => "sgt"
  | .ge => "sge"

private def binary (lhs op rhs : String) : String :=
  parens s!"{lhs} {op} {rhs}"

/-- C0 division truncates toward zero; Boole `div` on `int` is Euclidean. -/
private def truncDiv (x y : String) : String :=
  let neg (s : String) := parens s!"-{s}"
  s!"(if ({x} >= 0) then (if ({y} >= 0) then ({x} div {y}) else {neg s!"({x} div {neg y})"}) " ++
  s!"else (if ({y} >= 0) then {neg s!"({neg x} div {y})"} else ({neg x} div {neg y})))"

partial def ppExpr (model : IntModel) : Expr → String
  | .var name => name
  | .intLit n => ppIntLit model n
  | .mathLit n => ppMathLit n
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .null => "0"
  | .arith op lhs rhs =>
      let l := ppExpr model lhs
      let r := ppExpr model rhs
      match model, op with
      | .bv32, _ => binary l (bvArithOp op) r
      | .checked, .div => truncDiv l r
      | .checked, .mod => binary l "-" (binary r "*" (truncDiv l r))
      | .checked, .add | .checked, .sub | .checked, .mul => binary l (mathArithOp op) r
      | .checked, _ => s!"as_sint({binary s!"as_bv32({l})" (bvArithOp op) s!"as_bv32({r})"})"
  | .cmp op lhs rhs =>
      let opText := if model == .bv32 then bvCmpOp op else mathCmpOp op
      binary (ppExpr model lhs) opText (ppExpr model rhs)
  | .mathArith op lhs rhs => binary (ppExpr model lhs) (mathArithOp op) (ppExpr model rhs)
  | .mathCmp op lhs rhs => binary (ppExpr model lhs) (mathCmpOp op) (ppExpr model rhs)
  | .eq lhs rhs => binary (ppExpr model lhs) "==" (ppExpr model rhs)
  | .neq lhs rhs => binary (ppExpr model lhs) "!=" (ppExpr model rhs)
  | .and lhs rhs => binary (ppExpr model lhs) "&&" (ppExpr model rhs)
  | .or lhs rhs => binary (ppExpr model lhs) "||" (ppExpr model rhs)
  | .implies lhs rhs => binary (ppExpr model lhs) "==>" (ppExpr model rhs)
  -- `!` binds tighter than map indexing in Boole, so its operand is parenthesized.
  | .not e => parens s!"!({ppExpr model e})"
  | .ite test thenVal elseVal =>
      parens s!"if {ppExpr model test} then {ppExpr model thenVal} else {ppExpr model elseVal}"
  | .mapGet map key => s!"{ppExpr model map}[{ppExpr model key}]"
  | .old e => parens s!"old {ppExpr model e}"
  | .forall binders body =>
      let bs := commaSep (binders.map fun (name, tau) => s!"{name} : {ppTau model tau}")
      parens s!"forall {bs} :: {ppExpr model body}"

private def ppLValue (model : IntModel) : LValue → String
  | .var name => name
  | .mapSlot map key => s!"{ppExpr model map}[{ppExpr model key}]"

private def ppLabel : Option String → String
  | some label => s!"[{label}]: "
  | none => ""

partial def ppStm (model : IntModel) (level : Nat) : Stmt → List String
  | .declare name tau =>
      [indent level s!"var {name} : {ppTau model tau};"]
  | .assign lhs rhs =>
      [indent level s!"{ppLValue model lhs} := {ppExpr model rhs};"]
  | .check label expr =>
      let e := ppExpr model expr
      [indent level s!"assert [{label}]: {e};", indent level s!"assume {e};"]
  | .assume expr =>
      [indent level s!"assume {ppExpr model expr};"]
  | .havoc name =>
      [indent level s!"havoc {name};"]
  | .ifElse test thenBody elseBody =>
      let thenLines := thenBody.flatMap (ppStm model (level + 1))
      let elseLines := elseBody.flatMap (ppStm model (level + 1))
      let head := indent level s!"if ({ppExpr model test}) \{"
      if elseLines.isEmpty then
        [head] ++ thenLines ++ [indent level "}"]
      else
        [head] ++ thenLines ++ [indent level "} else {"] ++ elseLines ++ [indent level "}"]
  | .whileLoop test invariants body =>
      let invLines := invariants.map fun (label, inv) =>
        indent (level + 1) s!"invariant [{label}]: {ppExpr model inv}"
      let bodyLines := body.flatMap (ppStm model (level + 1))
      [indent level s!"while ({ppExpr model test})"] ++ invLines ++
        [indent level "{"] ++ bodyLines ++ [indent level "}"]
  | .call lhs fname args =>
      let target := match lhs with
        | some name => s!"{name} := "
        | none => ""
      [indent level s!"call {target}{fname}({commaSep (args.map (ppExpr model))});"]
  | .block label body =>
      [indent level s!"{label}: \{"] ++ body.flatMap (ppStm model (level + 1)) ++ [indent level "}"]
  | .exit label =>
      [indent level s!"exit {label};"]

private def ppSpec (model : IntModel) (spec : Spec) : String :=
  let free := if spec.free then "free " else ""
  let kind := match spec.kind with
    | .requires => "requires"
    | .ensures => "ensures"
  s!"  {free}{kind} {ppLabel spec.label}{ppExpr model spec.expr};"

private def ppParams (model : IntModel) (params : List (Tau × String)) : String :=
  commaSep (params.map fun (tau, name) => s!"{name} : {ppTau model tau}")

private def ppReturn (model : IntModel) : Option (Tau × String) → String
  | none => "returns ()"
  | some (tau, name) => s!"returns ({name} : {ppTau model tau})"

private def ppProcedure (model : IntModel) (proc : Procedure) : String :=
  let specLines := proc.specs.map (ppSpec model)
  let modifiesLines :=
    if proc.modifies.isEmpty then [] else [s!"  modifies {commaSep proc.modifies};"]
  let allSpecLines := specLines ++ modifiesLines
  let specBlock :=
    if allSpecLines.isEmpty then ""
    else "\nspec {\n" ++ String.intercalate "\n" allSpecLines ++ "\n}"
  let header := s!"procedure {proc.name}({ppParams model proc.params}) {ppReturn model proc.ret}{specBlock}"
  match proc.body with
  | none => header ++ ";"
  | some body =>
      let bodyText := String.intercalate "\n" (body.flatMap (ppStm model 1))
      s!"{header}\n\{\n{bodyText}\n};"

def run (program : Program) : ProgramText :=
  let model := program.intModel
  let typeDecls := if program.usesStrings then ["type C0String;", ""] else []
  let globals := program.globals.map fun (name, tau) => s!"var {name} : {ppTau model tau};"
  let header := ["program Boole;", ""] ++ typeDecls ++
    (if globals.isEmpty then [] else globals ++ [""])
  String.intercalate "\n" header ++ "\n" ++
    String.intercalate "\n\n" (program.procedures.map (ppProcedure model)) ++ "\n"

end C0VC.StrataBoole.Codegen
