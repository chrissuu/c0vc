namespace C0VC.Utils.Literal

/-- The C0 escape sequence for a character, if it needs one inside `quote`. -/
private def escape (quote : Char) (c : Char) : String :=
  match c with
  | '\n' => "\\n"
  | '\t' => "\\t"
  | '\r' => "\\r"
  | '\u000B' => "\\v"
  | '\u0008' => "\\b"
  | '\u000C' => "\\f"
  | '\u0007' => "\\a"
  | '\u0000' => "\\0"
  | '\\' => "\\\\"
  | c => if c == quote then "\\" ++ c.toString else c.toString

/-- A string literal as C0 source. -/
def showString (s : String) : String :=
  "\"" ++ String.join (s.toList.map (escape '"')) ++ "\""

/-- A character literal as C0 source. -/
def showChar (c : Char) : String :=
  "'" ++ escape '\'' c ++ "'"

end C0VC.Utils.Literal
