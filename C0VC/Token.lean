import C0VC.Utils.SrcSpan

open C0VC.Utils.SrcSpan

namespace C0VC.Token

inductive TokenKind where
  | ident (name : String)
  | typeIdent (name : String)
  | intLit (value : Int)
  | hexLit (value : String)
  | stringLit (value : String)
  | charLit (value : Char)

  -- Core Keywords
  -- The reserved keywords of the language are:
  -- int bool string char void struct typedef
  -- if else while for continue break return assert
  -- error true false NULL alloc alloc_array
  | kwInt | kwBool | kwString | kwChar | kwVoid | kwStruct | kwTypedef
  | kwIf | kwElse | kwWhile | kwFor | kwReturn | kwAssert
  | kwError | kwTrue | kwFalse | kwNull | kwAlloc | kwAllocArray
  | kwContinue | kwBreak -- Note: nice to haves
  | kwUse -- #use (for libraries (& headers?))

  -- Contracts / Annotations Keywords
  | requires
  | ensures
  | loopInvariant
  | result
  | length
  | hastag

  -- Syntax
  | lParen | rParen     -- ()
  | lBrace | rBrace     -- {}
  | lBracket | rBracket -- []
  | colon | semicolon   -- :;
  | comma | question    -- ,?
  | dot | arrow         -- . ->

  -- Assignment Operators
  | assign
  | plusEq
  | subEq
  | mulEq
  | divEq
  | modEq
  | andEq
  | xorEq
  | orEq
  | shlEq
  | shrEq

  -- Operators
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
  | land -- &&
  | lor  -- ||
  | and  -- &
  | xor
  | or   -- |
  | shl
  | shr

  | incr -- ++
  | decr -- --

  | bang     -- !
  | squiggly -- ~
  | negative -- -

  | int
  | bool
  | void
  | typedef

  | openMultilineComment -- /*
  | closeMultilineComment -- */
  | annotation -- //@
  | openMultilineAnnotation -- /*@
  | closeMultilineAnnotation -- @*/
  | comment -- //

  | eof
deriving Repr, BEq, DecidableEq

structure Token where
  kind : TokenKind
  span : SrcSpan
deriving Repr, BEq, DecidableEq

namespace Print

def ppTokenKind : TokenKind → String
  | .ident name => s!"ident({name})"
  | .typeIdent name => s!"typeIdent({name})"
  | .intLit value => s!"intLit({value})"
  | .hexLit value => s!"hexLit({value})"
  | .stringLit value => s!"stringLit(\"{value}\")"
  | .charLit value => s!"charLit('{value}')"
  | .kwInt => "kwInt"
  | .kwBool => "kwBool"
  | .kwString => "kwString"
  | .kwChar => "kwChar"
  | .kwVoid => "kwVoid"
  | .kwStruct => "kwStruct"
  | .kwTypedef => "kwTypedef"
  | .kwIf => "kwIf"
  | .kwElse => "kwElse"
  | .kwWhile => "kwWhile"
  | .kwFor => "kwFor"
  | .kwReturn => "kwReturn"
  | .kwAssert => "kwAssert"
  | .kwError => "kwError"
  | .kwTrue => "kwTrue"
  | .kwFalse => "kwFalse"
  | .kwNull => "kwNull"
  | .kwAlloc => "kwAlloc"
  | .kwAllocArray => "kwAllocArray"
  | .kwContinue => "kwContinue"
  | .kwBreak => "kwBreak"
  | .kwUse => "kwUse"
  | .requires => "requires"
  | .ensures => "ensures"
  | .loopInvariant => "loopInvariant"
  | .result => "result"
  | .length => "length"
  | .hastag => "hastag"
  | .lParen => "lParen"
  | .rParen => "rParen"
  | .lBrace => "lBrace"
  | .rBrace => "rBrace"
  | .lBracket => "lBracket"
  | .rBracket => "rBracket"
  | .colon => "colon"
  | .semicolon => "semicolon"
  | .comma => "comma"
  | .question => "question"
  | .dot => "dot"
  | .arrow => "arrow"
  | .assign=> "assign"
  | .plusEq => "plusEq"
  | .subEq => "subEq"
  | .mulEq => "mulEq"
  | .divEq => "divEq"
  | .modEq => "modEq"
  | .andEq => "andEq"
  | .xorEq => "xorEq"
  | .orEq => "orEq"
  | .shlEq => "shlEq"
  | .shrEq => "shrEq"
  | .plus => "plus"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"
  | .mod => "mod"
  | .lt => "lt"
  | .lte => "lte"
  | .gt => "gt"
  | .gte => "gte"
  | .eq => "eq"
  | .neq => "neq"
  | .land => "land"
  | .lor => "lor"
  | .and => "and"
  | .xor => "xor"
  | .or => "or"
  | .shl => "shl"
  | .shr => "shr"
  | .incr => "incr"
  | .decr => "decr"
  | .bang => "bang"
  | .squiggly => "squiggly"
  | .negative => "negative"
  | .int => "int"
  | .bool => "bool"
  | .void => "void"
  | .typedef => "typedef"
  | .openMultilineComment => "openMultilineComment"
  | .closeMultilineComment => "closeMultilineComment"
  | .annotation => "annotation"
  | .openMultilineAnnotation => "openMultilineAnnotation"
  | .closeMultilineAnnotation => "closeMultilineAnnotation"
  | .comment => "comment"
  | .eof => "eof"

def ppToken (t : Token) : String :=
  s!"{ppTokenKind t.kind} @ {t.span.show}"

def ppTokens (tokens : List Token) : String :=
  String.intercalate "\n" (tokens.map ppToken)

end Print

instance : ToString TokenKind where
  toString := Print.ppTokenKind

instance : ToString Token where
  toString := Print.ppToken

end C0VC.Token
