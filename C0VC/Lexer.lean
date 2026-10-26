/-
Lexer

Author(s):
  ~ Chris Su <chrjs@cmu.edu>
-/
import Std
import C0VC.Token
import C0VC.Utils.SrcSpan
import Std.Data.HashSet

namespace C0VC.Lexer

open C0VC.Utils.SrcSpan

abbrev TokenKind := C0VC.Token.TokenKind
abbrev Token := C0VC.Token.Token

def tokenKindOptionOfString : String → Option TokenKind
  -- Static lexemes only. Dynamic lexemes (identifiers, literals) return `none`.
  | "int" => some .kwInt
  | "bool" => some .kwBool
  | "string" => some .kwString
  | "char" => some .kwChar
  | "void" => some .kwVoid
  | "struct" => some .kwStruct
  | "typedef" => some .kwTypedef
  | "if" => some .kwIf
  | "else" => some .kwElse
  | "while" => some .kwWhile
  | "for" => some .kwFor
  | "return" => some .kwReturn
  | "assert" => some .kwAssert
  | "error" => some .kwError
  | "true" => some .kwTrue
  | "false" => some .kwFalse
  | "NULL" => some .kwNull
  | "alloc" => some .kwAlloc
  | "alloc_array" => some .kwAllocArray
  | "continue" => some .kwContinue
  | "break" => some .kwBreak
  | "#use" => some .kwUse
  | "requires" => some .requires
  | "ensures" => some .ensures
  | "loop_invariant" => some .loopInvariant
  | "\\result" => some .result
  | "\\length" => some .length
  | "#" => some .hastag
  | "(" => some .lParen
  | ")" => some .rParen
  | "{" => some .lBrace
  | "}" => some .rBrace
  | "[" => some .lBracket
  | "]" => some .rBracket
  | ":" => some .colon
  | ";" => some .semicolon
  | "," => some .comma
  | "?" => some .question
  | "." => some .dot
  | "->" => some .arrow
  | "=" => some .assign
  | "+=" => some .plusEq
  | "-=" => some .subEq
  | "*=" => some .mulEq
  | "/=" => some .divEq
  | "%=" => some .modEq
  | "&=" => some .andEq
  | "^=" => some .xorEq
  | "|=" => some .orEq
  | "<<=" => some .shlEq
  | ">>=" => some .shrEq
  | "+" => some .plus
  | "-" => some .sub
  | "*" => some .mul
  | "/" => some .div
  | "%" => some .mod
  | "<" => some .lt
  | "<=" => some .lte
  | ">" => some .gt
  | ">=" => some .gte
  | "==" => some .eq
  | "!=" => some .neq
  | "&&" => some .land
  | "||" => some .lor
  | "&" => some .and
  | "^" => some .xor
  | "|" => some .or
  | "<<" => some .shl
  | ">>" => some .shr
  | "++" => some .incr
  | "--" => some .decr
  | "!" => some .bang
  | "~" => some .squiggly
  | "/*" => some .openMultilineComment
  | "*/" => some .closeMultilineComment
  | "//@" => some .annotation
  | "/*@" => some .openMultilineAnnotation
  | "@*/" => some .closeMultilineAnnotation
  | "//" => some .comment
  | _ => none

/--
Maximal Munch Lexer

A seed for some token T is any character c which prefixes T.
A character c may be a seed for more than one token T. For each
token T that c is a seed for, we try to munch that pattern maximally.
This returns the length of the matched string as well as the Token that we
retrieved. We take the argmax amongst this set w.r.t retrieved string length.
We then jump our character pointer to after the string length, ignoring whitespaces.
The SrcLoc ptr is updated in these instances: Tabs, Return, etc.

    ident       ::= ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*
    integer     ::= ("0" | ['1'-'9'](['0'-'9']*))
    hexadecimal ::= "0"['x' 'X']['0'-'9' 'a'-'f' 'A'-'F']+
    ws          ::= [' ' '\t' '\r' '\011' '\012']

-/

def isIdentSeed c := Char.isAlpha c || c == '_'

def isHexDigit (c : Char) : Bool :=
  Char.isDigit c
  || ('a' <= c && c <= 'f')
  || ('A' <= c && c <= 'F')

-- hexadecimal ::= "0"['x' 'X']['0'-'9' 'a'-'f' 'A'-'F']+
def matchHexLit (s : String.Slice) : Option String.Slice :=
  if !(s.startsWith "0x" || s.startsWith "0X") then
    none
  else
    let digits := (s.drop 2).takeWhile isHexDigit
    if digits.isEmpty then
      none
    else
      let consumed := 2 + digits.toString.length
      some (s.take consumed)

-- integer ::= ("0" | ['1'-'9'](['0'-'9']*))
def matchIntLit (s : String.Slice) : Option String.Slice :=
  let digits := s.takeWhile Char.isDigit
  if digits.isEmpty then none
  else
    match digits.front with
    | '0' => if digits.positions.length == 1 then digits else none
    | _ => digits

def isIdentChar (c : Char) : Bool :=
  c == '_' || c.isAlphanum

-- ident ::= ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*
def matchIdent (s : String.Slice) : Option String.Slice :=
  if s.startsWith Char.isDigit then none
  else
    let identChars := s.takeWhile isIdentChar
    if identChars.isEmpty then none
    else some identChars

-- Length (in chars) of a string literal body up to and including the closing
-- quote, or none if the literal is unterminated on its line.
private def stringLitLength : List Char → Nat → Option Nat
  | [], _ => none
  | '\n' :: _, _ => none
  | '\\' :: _ :: rest, n => stringLitLength rest (n + 2)
  | '"' :: _, n => some (n + 1)
  | _ :: rest, n => stringLitLength rest (n + 1)

/-- Escapes allowed in C0 character and string literals. -/
def isValidCharEscape (c : Char) : Bool :=
  "ntvbrfa\\'\"?0".contains c

private def escapesValid : List Char → Bool
  | [] => true
  | '\\' :: c :: rest => isValidCharEscape c && escapesValid rest
  | _ :: rest => escapesValid rest

-- string ::= '"' (char | escape)* '"'
def matchStringLit (s : String.Slice) : Option String.Slice :=
  if !s.startsWith "\"" then none
  else
    let body := (s.drop 1).takeWhile (fun c => c != '\n')
    match stringLitLength body.toString.toList 1 with
    | some n =>
        let lit := s.take n
        -- The body without its quotes must use only C0 escapes.
        if escapesValid ((lit.drop 1).dropEnd 1).toString.toList then some lit else none
    | none => none

def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\u000B' || c == '\u000C'

def matchCharLit (s : String.Slice) : Option String.Slice :=
  if !s.startsWith "'" then none
  else
    let body := s.drop 1
    if body.startsWith "\\" then
        let esc := (body.drop 1).take 1
        let close := (body.drop 2).take 1
        if esc.isEmpty || close.isEmpty then
          none
        else if close.toString != "'" then none
        else
          match esc.front? with
          | some c => if isValidCharEscape c
                      then some (s.take 4)
                      else none
          | none   => none
    else
      let ch := body.take 1
      let close := body.drop 1 |>.take 1
      if ch.isEmpty || close.isEmpty then none
      else if close.toString != "'" then none
      else some (s.take 3)

/--
Length of a nested block comment that starts after its opening delimiter, at
nesting `depth`, given `consumed` characters so far. Scans only the comment,
so lexing stays linear in the file size.
-/
def nestedCommentLength (opening closing : String) (s : String.Slice) (depth consumed : Nat)
    (fuel : Nat := 2 ^ 63) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
  if s.isEmpty then none
  else if s.startsWith opening then
    nestedCommentLength opening closing (s.drop opening.length) (depth + 1) (consumed + opening.length) fuel
  else if s.startsWith closing then
    if depth == 1 then some (consumed + closing.length)
    else nestedCommentLength opening closing (s.drop closing.length) (depth - 1) (consumed + closing.length) fuel
  else
    nestedCommentLength opening closing (s.drop 1) depth (consumed + 1) fuel

def startsWithWord (s : String.Slice) (word : String) : Bool :=
  s.startsWith word &&
  match (s.drop word.length).front? with
  | none => true
  | some c => !isIdentChar c

def startsWithAnnotationKeyword (s : String.Slice) : Bool :=
  let body := s.dropWhile isWhitespace
  startsWithWord body "requires"
  || startsWithWord body "ensures"
  || startsWithWord body "loop_invariant"
  || startsWithWord body "asserts"
  || startsWithWord body "assert"

/-- Matches comments:
`// ...` until first `\n`, and nested `/* ... */` block comments. -/
def matchComment (includeAnnotations : Bool) (s : String.Slice) : Option String.Slice :=
  if includeAnnotations && s.startsWith "//@" && startsWithAnnotationKeyword (s.drop 3) then
    none
  else if includeAnnotations && s.startsWith "/*@" && startsWithAnnotationKeyword (s.drop 3) then
    none
  else if s.startsWith "//" then
    let body := s.drop 2
    let commentBody := body.takeWhile (fun c => c != '\n')
    let consumed := 2 + commentBody.toString.length
    some (s.take consumed)
  else if s.startsWith "/*@" then
    match nestedCommentLength "/*@" "@*/" (s.drop 3) 1 3 with
    | some consumed =>
      some (s.take consumed)
    | none => none
  else if s.startsWith "/*" then
    match nestedCommentLength "/*" "*/" (s.drop 2) 1 2 with
    | some consumed =>
      some (s.take consumed)
    | none => none
  else
    none

def staticTokenLexemes : List String :=
  [
    "/*@", "//@", "@*/",
    "\\result", "\\length",
    "<<=", ">>=",
    "+=", "-=", "*=", "/=", "%=", "&=", "^=", "|=",
    "<=", ">=", "==", "!=", "&&", "||", "<<", ">>", "++", "--", "->",
    "(", ")", "{", "}", "[", "]", ":", ";", ",", "?",
    "=", "+", "-", "*", "/", "%", "<", ">", "&", "^", "|", "!", "~", "#", "."
  ]

def matchStaticToken (s : String.Slice) : Option String.Slice :=
  (staticTokenLexemes.find? (fun lex => s.startsWith lex)).map (fun lex => s.take lex.length)

/-- The longest token or comment at the start of `s`. -/
def maximalMatch (includeAnnotations : Bool) (s : String.Slice) : Option String.Slice :=
  [matchHexLit, matchIntLit, matchIdent, matchStringLit, matchCharLit, matchComment includeAnnotations, matchStaticToken]
    |>.filterMap (· s)
    |>.maxOn? (·.positions.length)

def decodeEscapedChar (c : Char) : Char :=
  match c with
  | 'n' => '\n'
  | 't' => '\t'
  | 'r' => '\r'
  | '\\' => '\\'
  | '\'' => '\''
  | '"' => '"'
  | 'v' => '\u000B'
  | 'b' => '\u0008'
  | 'f' => '\u000C'
  | 'a' => '\u0007'
  | '0' => '\u0000'
  | x => x

def decodeEscapes : List Char → String
  | [] => ""
  | '\\' :: c :: rest => (decodeEscapedChar c).toString ++ decodeEscapes rest
  | c :: rest => c.toString ++ decodeEscapes rest

-- Helper for tracking SrcLoc.
def advanceLocByChars : Nat → Nat → List Char → SrcLoc
  | line, col, [] => SrcLoc.mk line col

  -- \r\n, \r, \n, are all treated the same
  | line, _, '\r' :: '\n' :: rest => advanceLocByChars (line + 1) 1 rest
  | line, _, '\r' :: rest => advanceLocByChars (line + 1) 1 rest
  | line, _, '\n' :: rest => advanceLocByChars (line + 1) 1 rest

  -- see SrcSpan for tabWidth variable. TODO: move tabWidth somewhere more visible?
  | line, col, '\t' :: rest => advanceLocByChars line (col + tabWidth) rest
  | line, col, _ :: rest => advanceLocByChars line (col + 1) rest

def advanceLocBySlice (line col : Nat) (s : String.Slice) : SrcLoc :=
  advanceLocByChars line col s.toString.toList

-- Given some matched String Slice, this function will attempt to wrap it with the appropriate TokenKind
def toTokenKind? (matched : String.Slice) : Option TokenKind :=
  let lex := matched.toString
  if lex.startsWith "0x" || lex.startsWith "0X" then
    some (.hexLit lex)
  else if matched.startsWith "\"" then
    if lex.length < 2 then none
    else some (.stringLit (decodeEscapes ((matched.drop 1).dropEnd 1).toString.toList))
  else if matched.startsWith "'" then
    if lex.length == 3 then
      match (matched.drop 1).front? with
      | some ch => some (.charLit ch)
      | none => none
    else if lex.length == 4 then
      match ((matched.drop 2).take 1).front? with
      | some esc => some (.charLit (decodeEscapedChar esc))
      | none => none
    else
      none
  else if matched.startsWith Char.isDigit then
    match lex.toNat? with
    | some n => some (.intLit (Int.ofNat n))
    | none => none
  else if matched.startsWith isIdentSeed then
    match tokenKindOptionOfString lex with
    | some kw => some kw
    | none => some (.ident lex)
  else
    tokenKindOptionOfString lex

def classifyTypedefToken (typedefs : Std.HashSet String) (tok : Token) : Token :=
  match tok.kind with
  | .ident name =>
      if typedefs.contains name then
        { tok with kind := .typeIdent name }
      else
        tok
  | _ => tok

def finishTypedefTokens (typedefs : Std.HashSet String) (tokensRev : List Token) :
    List Token × Std.HashSet String :=
  let tokens := tokensRev.reverse
  let aliasTok? := tokensRev.find? (fun tok =>
    match tok.kind with
    | .ident _ => true
    | _ => false)
  let sameSpan (lhs rhs : Token) : Bool :=
    lhs.span == rhs.span
  let classify (tok : Token) : Token :=
    match aliasTok? with
    | some aliasTok =>
        if sameSpan tok aliasTok then
          tok
        else
          classifyTypedefToken typedefs tok
    | none => classifyTypedefToken typedefs tok
  let tokens' := tokens.map classify
  match aliasTok? with
  | some aliasTok =>
      match aliasTok.kind with
      | .ident alias => (tokens', typedefs.insert alias)
      | _ => (tokens', typedefs)
  | none => (tokens', typedefs)

def classifyTypedefsWith (initialTypedefs : List String) (tokens : List Token) : List Token :=
  -- Each step consumes at least one token, so `tokens.length + 1` steps suffice.
  let rec go (fuel : Nat) (typedefs : Std.HashSet String) (acc : List Token) (rest : List Token) : List Token :=
    match fuel, rest with
    | _, [] => acc.reverse
    | 0, _ => acc.reverse ++ rest
    | fuel + 1, tok :: toks =>
        match tok.kind with
        | .kwTypedef =>
            let rec collect (bufRev : List Token) : List Token → List Token × List Token
              | [] => (bufRev, [])
              | t :: ts =>
                  if t.kind == .semicolon then
                    (t :: bufRev, ts)
                  else
                    collect (t :: bufRev) ts
            let (typedefRev, rest') := collect [tok] toks
            let (typedefTokens, typedefs') := finishTypedefTokens typedefs typedefRev
            go fuel typedefs' (typedefTokens.reverse ++ acc) rest'
        | _ =>
            go fuel typedefs (classifyTypedefToken typedefs tok :: acc) toks
  go (tokens.length + 1) (Std.HashSet.ofList initialTypedefs) [] tokens

def classifyTypedefs (tokens : List Token) : List Token :=
  classifyTypedefsWith [] tokens

/-- Where the lexer is relative to annotations; `@` is whitespace inside one. -/
inductive AnnoState where
  | outside
  | line
  | block

def munchRaw (includeAnnotations : Bool) (fileName : String) (body : String) : Except String (List Token) :=
  -- Each step consumes at least one character, so `body.length + 1` steps suffice.
  let rec go (fuel : Nat) (s : String.Slice) (line col : Nat) (acc : List Token) (anno : AnnoState := .outside) :
      Except String (List Token) :=
    match fuel with
    | 0 => .error s!"internal error: lexer made no progress at {fileName}:{line}:{col}"
    | fuel + 1 =>
    if s.isEmpty then
      let loc := SrcLoc.mk line col
      let eof : Token := { kind := .eof, span := SrcSpan.mk loc loc fileName }
      .ok ((acc.reverse) ++ [eof])
    else
      let ws := s.takeWhile isWhitespace
      let inAnno := match anno with
        | .outside => false
        | _ => true
      if !ws.isEmpty then
        let nextLoc := advanceLocBySlice line col ws
        let anno := match anno with
          | .line => if ws.toString.contains '\n' then .outside else .line
          | other => other
        go fuel (s.drop ws.toString.length) nextLoc.line nextLoc.col acc anno
      else if inAnno && s.startsWith "@" && !s.startsWith "@*/" then
        -- "In annotations, the @ character is treated as whitespace." (C0 reference)
        go fuel (s.drop 1) line (col + 1) acc anno
      else if s.startsWith "/*" && !s.startsWith "/*@" && (matchComment includeAnnotations s).isNone then
        .error s!"lexical error at {fileName}:{line}:{col}: unterminated block comment"
      else
        match maximalMatch includeAnnotations s with
        | none =>
          match s.front? with
          | some '"' =>
            .error s!"lexical error at {fileName}:{line}:{col}: string literal is unterminated or has an invalid escape"
          | some '\'' =>
            .error s!"lexical error at {fileName}:{line}:{col}: malformed character literal"
          | some char =>
            .error s!"lexical error at {fileName}:{line}:{col}: unexpected character '{char}'"
          | none =>
            .error s!"lexical error at {fileName}:{line}:{col}: unexpected end of input"
        | some matched =>
          let consumed := matched.toString.length
          let nextLoc := advanceLocBySlice line col matched
          if (matchComment includeAnnotations s).isSome then
            go fuel (s.drop consumed) nextLoc.line nextLoc.col acc anno
          else
            match toTokenKind? matched with
            | some kind =>
              let tok : Token := {
                kind := kind
                span := SrcSpan.mk (SrcLoc.mk line col) (SrcLoc.mk nextLoc.line nextLoc.col) fileName
              }
              let anno := match kind with
                | .annotation => AnnoState.line
                | .openMultilineAnnotation => .block
                | .closeMultilineAnnotation => .outside
                | _ => anno
              go fuel (s.drop consumed) nextLoc.line nextLoc.col (tok :: acc) anno
            | none =>
              .error s!"lexical error at {fileName}:{line}:{col}: malformed token `{matched.toString}`"
  go (body.length + 1) body.toSlice 1 1 []

def munch (fileName : String) (body : String) : Except String (List Token) := do
  let tokens ← munchRaw true fileName body
  .ok (classifyTypedefs tokens)

def munchWithTypedefs (initialTypedefs : List String) (fileName : String) (body : String) :
    Except String (List Token) := do
  let tokens ← munchRaw true fileName body
  .ok (classifyTypedefsWith initialTypedefs tokens)

def munchWithoutAnnotationsWithTypedefs (initialTypedefs : List String) (fileName : String) (body : String) :
    Except String (List Token) := do
  let tokens ← munchRaw false fileName body
  .ok (classifyTypedefsWith initialTypedefs tokens)

end C0VC.Lexer
