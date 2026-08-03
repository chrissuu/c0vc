import C0VC.StrataBoole.IR

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

private def lines (xs : List String) : String :=
  String.intercalate "\n" xs

private def booleKeywords : List String :=
  [ "result"
  , "old"
  , "var"
  , "procedure"
  ]

private def isBooleKeyword (name : String) : Bool :=
  booleKeywords.contains name

private def ppIdent (name : String) : String :=
  if isBooleKeyword name then
    "_c0_" ++ name
  else
    name

private def boolePrelude : String :=
  lines
    [ "program Boole;"
    , ""
    ]

private def booleHeapPrelude : String :=
  lines
    [ "program Boole;"
    , ""
    , "type Ref := int;"
    , "type HeapInt := Map Ref (Map int int);"
    , "type HeapBool := Map Ref (Map int bool);"
    , "type HeapRef := Map Ref (Map int Ref);"
    , ""
    , "var alloc : Map int bool;"
    , "var len : Map int int;"
    , "var hInt : HeapInt;"
    , "var hBool : HeapBool;"
    , "var hRef : HeapRef;"
    , ""
    ]

private def heapGlobals : List String :=
  [ "alloc", "len", "hInt", "hBool", "hRef" ]

private def isHeapGlobal (name : String) : Bool :=
  heapGlobals.contains name

partial def tauNeedsHeapPrelude : Tau → Bool
  | .ref | .heapRef => true
  | .map key val => tauNeedsHeapPrelude key || tauNeedsHeapPrelude val
  | .int | .bool | .void => false

mutual
partial def exprNeedsHeapPrelude : Expr → Bool
  | .var name => isHeapGlobal name
  | .null => true
  | .intLit _ | .boolLit _ => false
  | .binop _ lhs rhs => exprNeedsHeapPrelude lhs || exprNeedsHeapPrelude rhs
  | .ite test thenVal elseVal =>
      exprNeedsHeapPrelude test || exprNeedsHeapPrelude thenVal || exprNeedsHeapPrelude elseVal
  | .call _ args => args.any exprNeedsHeapPrelude
  | .mapGet map key => exprNeedsHeapPrelude map || exprNeedsHeapPrelude key

partial def lvalueNeedsHeapPrelude : LValue → Bool
  | .var name => isHeapGlobal name
  | .mapSlot map key => exprNeedsHeapPrelude map || exprNeedsHeapPrelude key
end

partial def stmtNeedsHeapPrelude : Stmt → Bool
  | .declare _ tau => tauNeedsHeapPrelude tau
  | .assign lhs rhs => lvalueNeedsHeapPrelude lhs || exprNeedsHeapPrelude rhs
  | .assert expr => exprNeedsHeapPrelude expr
  | .ifElse test thenBody elseBody =>
      exprNeedsHeapPrelude test || thenBody.any stmtNeedsHeapPrelude || elseBody.any stmtNeedsHeapPrelude
  | .whileLoop test invariants body =>
      exprNeedsHeapPrelude test || invariants.any exprNeedsHeapPrelude || body.any stmtNeedsHeapPrelude

private def specNeedsHeapPrelude : Spec → Bool
  | .requires expr | .ensures expr => exprNeedsHeapPrelude expr

private def procNeedsHeapPrelude (proc : Procedure) : Bool :=
  proc.params.any (fun (tau, _) => tauNeedsHeapPrelude tau) ||
  proc.ret.any (fun (tau, _) => tauNeedsHeapPrelude tau) ||
  proc.specs.any specNeedsHeapPrelude ||
  proc.body.any (fun body => body.any stmtNeedsHeapPrelude)

private def programNeedsHeapPrelude (program : Program) : Bool :=
  program.procedures.any procNeedsHeapPrelude

partial def ppTau : Tau → String
  | .int => "int"
  | .bool => "bool"
  | .void => "void"
  | .ref => "Ref"
  | .heapRef => "HeapRef"
  | .map key val => s!"Map {ppTau key} {ppTau val}"

private def ppBinOp : BinOp → String
  | .plus => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "div"
  | .mod => "mod"
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

mutual
partial def ppExpr : Expr → String
  | .var name => ppIdent name
  | .intLit val => toString val
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .null => "0"
  | .binop op lhs rhs => parens s!"{ppExpr lhs} {ppBinOp op} {ppExpr rhs}"
  | .ite test thenVal elseVal => s!"(if {ppExpr test} then {ppExpr thenVal} else {ppExpr elseVal})"
  | .call fname args => s!"{ppIdent fname}({commaSep (args.map ppExpr)})"
  | .mapGet map key => s!"{ppExpr map}[{ppExpr key}]"

partial def ppLValue : LValue → String
  | .var name => ppIdent name
  | .mapSlot map key => s!"{ppExpr map}[{ppExpr key}]"
end

private def ppSpec : Spec → String
  | .requires e => s!"  requires {ppExpr e};"
  | .ensures e => s!"  ensures {ppExpr e};"

partial def ppStm (level : Nat) : Stmt → List String
  | .declare name tau =>
      [indent level s!"var {ppIdent name} : {ppTau tau};"]
  | .assign lhs rhs =>
      [indent level s!"{ppLValue lhs} := {ppExpr rhs};"]
  | .assert expr =>
      [indent level s!"assert {ppExpr expr};"]
  | .ifElse test thenBody elseBody =>
      let thenLines := List.flatten (thenBody.map (ppStm (level + 1)))
      let elseLines := List.flatten (elseBody.map (ppStm (level + 1)))
      let head := indent level s!"if ({ppExpr test}) \{"
      if elseLines.isEmpty then
        [head] ++ thenLines ++ [indent level "}"]
      else
        [head] ++ thenLines ++ [indent level "} else {"] ++ elseLines ++ [indent level "}"]
  | .whileLoop test invariants body =>
      let invText :=
        match invariants.map (fun inv => s!"invariant {ppExpr inv}") with
        | [] => ""
        | invs => " " ++ String.intercalate " " invs
      let bodyLines := List.flatten (body.map (ppStm (level + 1)))
      [indent level s!"while ({ppExpr test}){invText} \{"] ++ bodyLines ++ [indent level "}"]

private def ppParams (params : List (Tau × String)) : String :=
  commaSep (params.map fun (tau, name) => s!"{ppIdent name} : {ppTau tau}")

private def ppReturn : Option (Tau × String) → String
  | none => "returns ()"
  | some (tau, name) => s!"returns ({ppIdent name} : {ppTau tau})"

private def ppProcedure (proc : Procedure) : String :=
  let specBlock :=
    if proc.specs.isEmpty then
      ""
    else
      "\nspec {\n" ++ String.intercalate "\n" (proc.specs.map ppSpec) ++ "\n}"
  match proc.body with
  | none =>
      s!"procedure {ppIdent proc.name}({ppParams proc.params}) {ppReturn proc.ret}{specBlock};"
  | some body =>
      let bodyText := String.intercalate "\n" (List.flatten (body.map (ppStm 1)))
      s!"procedure {ppIdent proc.name}({ppParams proc.params}) {ppReturn proc.ret}{specBlock}\n\{\n{bodyText}\n};"

def run (program : Program) : ProgramText :=
  let prelude :=
    if programNeedsHeapPrelude program then
      booleHeapPrelude
    else
      boolePrelude
  prelude ++ "\n" ++ String.intercalate "\n\n" (program.procedures.map ppProcedure) ++ "\n"

end C0VC.StrataBoole.Codegen
