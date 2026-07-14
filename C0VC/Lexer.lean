/-
Lexer & Tokens

We currently opt for a simple maximal munch lexer. It is mostly efficient enough to
handle modest programs, while also being simple enough to debug and iterate
quickly on. If Lean develops a lexer library, considering migrating this code
to the lexer library.

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

def isHexLitSeed c := c == '0'

def isIntLitSeed c := Char.isDigit c

def isIdentSeed c := Char.isAlpha c || c == '_'

def isStringLitSeed c := c == '\"'

def isCharLitSeed c := c == '\''

def isCommentSeed c := c == '/'

def isContractBuiltinSeed c := c == '\\'

def isSeed c :=
  isHexLitSeed c
  || isIntLitSeed c
  || isIdentSeed c
  || isStringLitSeed c
  || isCharLitSeed c
  || isCommentSeed c
  || isContractBuiltinSeed c

def isHexDigit (c : Char) : Bool :=
  Char.isDigit c
  || ('a' <= c && c <= 'f')
  || ('A' <= c && c <= 'F')

-- hexadecimal ::= "0"['x' 'X']['0'-'9' 'a'-'f' 'A'-'F']+
def matchHexLit (s : String.Slice) (sliceLength : Nat) : Option String.Slice :=
  if sliceLength < 3 then
    none
  else if !(s.startsWith "0x" || s.startsWith "0X") then
    none
  else
    let digits := (s.drop 2).takeWhile isHexDigit
    if digits.isEmpty then
      none
    else
      let consumed := 2 + digits.toString.length
      some (s.take consumed)

-- integer ::= ("0" | ['1'-'9'](['0'-'9']*))
def matchIntLit (s : String.Slice) (_ : Nat) : Option String.Slice :=
  let digits := s.takeWhile Char.isDigit
  if digits.isEmpty then none
  else
    match digits.front with
    | '0' => if digits.positions.length == 1 then digits else none
    | _ => digits

def isIdentChar (c : Char) : Bool :=
  c == '_' || c.isAlphanum

-- ident ::= ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*
def matchIdent (s : String.Slice) (_ : Nat) : Option String.Slice :=
  if s.startsWith Char.isDigit then none
  else
    let identChars := s.takeWhile isIdentChar
    if identChars.isEmpty then none
    else some identChars

def endsWithUnescapedQuote (s : String.Slice) : Bool :=
  if !s.endsWith "\"" then
    false
  else
    let beforeLast := s.dropEnd 1
    let trailingBackslashes := beforeLast.takeEndWhile (λ c => c == '\\')
    trailingBackslashes.toString.length % 2 == 0

def matchStringLit (s : String.Slice) (sliceLength : Nat) : Option String.Slice :=
  if sliceLength < 2 then none
  else if !(s.startsWith "\"" && endsWithUnescapedQuote s) then none
  else some s

def isValidCharEscape (c : Char) : Bool :=
  c == 'n' || c == 't' || c == 'r' || c == '\\' || c == '\'' || c == '"' || c == '0'

def matchCharLit (s : String.Slice) (sliceLength : Nat) : Option String.Slice :=
  if sliceLength < 3 then none
  else if !s.startsWith "'" then none
  else
    let body := s.drop 1
    if body.startsWith "\\" then
      if sliceLength < 4 then none
      else
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

partial def nestedBlockCommentLength : List Char → Nat → Nat → Option Nat
  | [], _, _ => none
  | '/' :: '*' :: rest, depth, consumed =>
      nestedBlockCommentLength rest (depth + 1) (consumed + 2)
  | '*' :: '/' :: rest, depth, consumed =>
      if depth == 1 then
        some (consumed + 2)
      else
        nestedBlockCommentLength rest (depth - 1) (consumed + 2)
  | _ :: rest, depth, consumed =>
      nestedBlockCommentLength rest depth (consumed + 1)

/-- Matches comments:
`// ...` until first `\n`, and nested `/* ... */` block comments. -/
def matchComment (s : String.Slice) (_ : Nat) : Option String.Slice :=
  if s.startsWith "//@" || s.startsWith "/*@" then
    none
  else if s.startsWith "//" then
    let body := s.drop 2
    let commentBody := body.takeWhile (fun c => c != '\n')
    let consumed := 2 + commentBody.toString.length
    some (s.take consumed)
  else if s.startsWith "/*" then
    match nestedBlockCommentLength (s.drop 2).toString.toList 1 2 with
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

def matchStaticToken (s : String.Slice) (_ : Nat) : Option String.Slice :=
  (staticTokenLexemes.find? (fun lex => s.startsWith lex)).map (fun lex => s.take lex.length)

def getMatchesAndMaximalMatch (s : String.Slice) : List String.Slice × Option String.Slice :=
  let len := s.positions.length
  let patternMatches := [matchHexLit, matchIntLit, matchIdent, matchStringLit, matchCharLit, matchComment, matchStaticToken]
  |> List.map (λ fn => fn s len)
  |> List.filterMap id
  let maximalMatch := List.maxOn? (λ x => x.positions.length) patternMatches
  (patternMatches, maximalMatch)

def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\u000B' || c == '\u000C'

def decodeEscapedChar (c : Char) : Char :=
  match c with
  | 'n' => '\n'
  | 't' => '\t'
  | 'r' => '\r'
  | '\\' => '\\'
  | '\'' => '\''
  | '"' => '"'
  | '0' => '\u0000'
  | x => x

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
    else some (.stringLit ((matched.drop 1).dropEnd 1).toString)
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

partial def classifyTypedefsWith (initialTypedefs : List String) (tokens : List Token) : List Token :=
  let rec go (typedefs : Std.HashSet String) (acc : List Token) (rest : List Token) : List Token :=
    match rest with
    | [] => acc.reverse
    | tok :: toks =>
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
            go typedefs' (typedefTokens.reverse ++ acc) rest'
        | _ =>
            go typedefs (classifyTypedefToken typedefs tok :: acc) toks
  go (Std.HashSet.ofList initialTypedefs) [] tokens

partial def classifyTypedefs (tokens : List Token) : List Token :=
  classifyTypedefsWith [] tokens

partial def munchRaw (fileName : String) (body : String) : Except String (List Token) :=
  let rec go (s : String.Slice) (line col : Nat) (acc : List Token) : Except String (List Token) :=
    if s.isEmpty then
      let loc := SrcLoc.mk line col
      let eof : Token := { kind := .eof, span := SrcSpan.mk loc loc fileName }
      .ok ((acc.reverse) ++ [eof])
    else
      let ws := s.takeWhile isWhitespace
      if !ws.isEmpty then
        let nextLoc := advanceLocBySlice line col ws
        go (s.drop ws.toString.length) nextLoc.line nextLoc.col acc
      else if s.startsWith "/*" && !s.startsWith "/*@" && (matchComment s s.positions.length).isNone then
        .error s!"lexical error at {fileName}:{line}:{col}: unterminated block comment"
      else
        let (_, maximalMatch?) := getMatchesAndMaximalMatch s
        match maximalMatch? with
        | none =>
          match s.front? with
          | some char =>
            .error s!"lexical error at {fileName}:{line}:{col}: unexpected character '{char}'"
          | none =>
            .error s!"lexical error at {fileName}:{line}:{col}: unexpected end of input"
        | some matched =>
          let consumed := matched.toString.length
          let nextLoc := advanceLocBySlice line col matched
          if (matchComment s s.positions.length).isSome then
            go (s.drop consumed) nextLoc.line nextLoc.col acc
          else
            match toTokenKind? matched with
            | some kind =>
              let tok : Token := {
                kind := kind
                span := SrcSpan.mk (SrcLoc.mk line col) (SrcLoc.mk nextLoc.line nextLoc.col) fileName
              }
              go (s.drop consumed) nextLoc.line nextLoc.col (tok :: acc)
            | none =>
              .error s!"lexical error at {fileName}:{line}:{col}: malformed token `{matched.toString}`"
  go body.toSlice 1 1 []

def munch (fileName : String) (body : String) : Except String (List Token) := do
  let tokens ← munchRaw fileName body
  .ok (classifyTypedefs tokens)

def munchWithTypedefs (initialTypedefs : List String) (fileName : String) (body : String) :
    Except String (List Token) := do
  let tokens ← munchRaw fileName body
  .ok (classifyTypedefsWith initialTypedefs tokens)

end C0VC.Lexer
