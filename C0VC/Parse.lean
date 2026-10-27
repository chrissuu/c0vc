/-
Parser

Author(s):
  ~ Chris Su <chrjs@cmu.edu>
-/

import C0VC.Parser
import C0VC.Ast.ParsedAst
import C0VC.Lexer
import C0VC.Utils.SrcSpan

namespace C0VC.Parse

open Parser
open C0VC
open C0VC.Ast
open C0VC.Utils.SrcSpan

abbrev Tok := C0VC.Lexer.Token
abbrev TokStream := Parser.Stream.OfList Tok
abbrev P := SimpleParser TokStream Tok

instance : Inhabited (P MarkedStm) where
  default := pure { node := .nop, span := none }

instance : Inhabited (P MarkedExpr) where
  default := pure { node := .trueLit, span := none }

instance : Inhabited (P BinOp) where
  default := pure .plus

instance : Inhabited (P UnOp) where
  default := pure .bang

instance : Inhabited (P AssignOp) where
  default := pure .assign

instance : Inhabited (P (MarkedExpr → MarkedExpr)) where
  default := pure id

def mkExpr (node : Expr) : MarkedExpr :=
  { node := node, span := none }

structure ParsedLValue where
  lvalue : MarkedLValue
  startsWithBareDeref : Bool

instance : Inhabited (P ParsedLValue) where
  default := pure { lvalue := { node := .var "", span := none }, startsWithBareDeref := false }

-- Consume one token and decode its `TokenKind` with `f`.
def satisfyKind (f : Lexer.TokenKind -> Option a) : P a :=
  tokenMap (fun tk => f tk.kind)

-- "Expect" primitive: consume and return the next token when `pred` matches.
def expectKindTok (pred : Lexer.TokenKind -> Bool) : P Tok :=
  tokenFilter (fun tk => pred tk.kind)

def expectKindTokMsg (pred : Lexer.TokenKind -> Bool) (msg : String) : P Tok :=
  withErrorMessage msg <| expectKindTok pred

-- Same as `expectKindTok` but discard the token payload.
def expectKind (pred : Lexer.TokenKind -> Bool) : P Unit := do
  let _ ← expectKindTok pred
  pure ()

def expectKindMsg (pred : Lexer.TokenKind -> Bool) (msg : String) : P Unit := do
  withErrorMessage msg <| expectKind pred

def only (tok : Lexer.TokenKind) := (fun t => t == tok)

def lParen : P Unit := expectKind (fun | .lParen => true | _ => false)
def rParen : P Unit := expectKind (fun | .rParen => true | _ => false)
def comma : P Unit := expectKind (fun | .comma => true | _ => false)
def semicolon : P Unit := expectKind (fun | .semicolon => true | _ => false)
def kwReturn : P Unit := expectKind (fun | .kwReturn => true | _ => false)
def eofTok : P Unit := expectKind (fun | .eof => true | _ => false)
def qmark : P Unit := expectKind (fun | .question => true | _ => false)
def colon : P Unit := expectKind (fun | .colon => true | _ => false)
def lBracket : P Unit := expectKind (fun | .lBracket => true | _ => false)
def rBracket : P Unit := expectKind (fun | .rBracket => true | _ => false)

def spanFromTokenBounds (startTok endTok : Tok) : SrcSpan :=
  { startLoc := startTok.span.startLoc
  , endLoc := endTok.span.endLoc
  , fileName := startTok.span.fileName
  }

def spanFromConsumed (consumed : List Tok) : Option SrcSpan :=
  match consumed with
  | [] => none
  | first :: rest =>
    let last := rest.foldl (fun _ tk => tk) first
    some (spanFromTokenBounds first last)

/-- Parse `p` and recover the span from consumed tokens. -/
def withConsumedSpan (p : P a) : P (a × Option SrcSpan) := do
  let before ← Parser.getStream
  let x ← p
  let after ← Parser.getStream
  -- `past` holds consumed tokens newest first. Compare the newest consumed
  -- token instead of list lengths, which would make parsing quadratic.
  let consumedAny := after.past.head?.map (·.span) != before.past.head?.map (·.span)
  match before.input.head?, after.past.head? with
  | some first, some last =>
      pure (x, if consumedAny then some (spanFromTokenBounds first last) else none)
  | _, _ => pure (x, none)

def parseIdent : P String :=
  satisfyKind (fun
    | .ident name => some name
    | _ => none)

def parseTypeIdent : P String :=
  satisfyKind (fun
    | .typeIdent name => some name
    | _ => none)

def parseStructName : P String :=
  satisfyKind (fun
    | .ident name => some name
    | .typeIdent name => some name
    | _ => none)

def parseFieldName : P String :=
  satisfyKind (fun
    | .ident name => some name
    | .typeIdent name => some name
    | _ => none)

def hexCharToNat (c : Char) : Nat :=
  if '0' <= c && c <= '9' then c.toNat - '0'.toNat
  else if 'a' <= c && c <= 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' <= c && c <= 'F' then c.toNat - 'A'.toNat + 10
  else 0

def hexStringToNat (s : String) : Nat :=
  let s := if s.startsWith "0x" || s.startsWith "0X" then s.drop 2 else s
  s.foldl (fun acc c => acc * 16 + hexCharToNat c) 0

def intOfHexLit (s : String) : Int :=
  let n := hexStringToNat s
  if n > 4294967295 then
    Int.ofNat n
  else if n < 2147483648 then
    Int.ofNat n
  else
    Int.ofNat n - 4294967296

def parseHexLit : P MarkedExpr :=
  satisfyKind (fun
    | .hexLit s => some (mkExpr (.intLit (intOfHexLit s)))
    | _ => none
  )

def parseIntLit : P MarkedExpr :=
  satisfyKind (fun
    | .intLit n => some (mkExpr (.intLit n))
    | _ => none)

def parseBoolLit : P MarkedExpr :=
  satisfyKind (fun
    | .kwTrue => some (mkExpr .trueLit)
    | .kwFalse => some (mkExpr .falseLit)
    | _ => none)

def parseCharLit : P MarkedExpr :=
  satisfyKind (fun
    | .charLit c => some (mkExpr (.charLit c))
    | _ => none)

def parseStringLit : P MarkedExpr :=
  satisfyKind (fun
    | .stringLit s => some (mkExpr (.stringLit s))
    | _ => none)

def parseNullLit : P MarkedExpr :=
  satisfyKind (fun
    | .kwNull => some (mkExpr .null)
    | _ => none)

def parseResultExpr : P MarkedExpr :=
  satisfyKind (fun
    | .result => some (mkExpr .result)
    | _ => none)

def parseHastagExpr : P MarkedExpr :=
  satisfyKind (fun
    | .hastag => some (mkExpr .hastag)
    | _ => none)

def parseVar : P MarkedExpr := do
  let (name, sp) ← withConsumedSpan parseIdent
  pure { node := .var name, span := sp }

instance : Inhabited (P (MarkedExpr → Expr)) where
  default := pure (fun base => base.node)

instance : Inhabited (P (MarkedLValue → LValue)) where
  default := pure (fun base => base.node)

mutual
partial def parseTauBase : P Tau :=
  (satisfyKind (fun
    | .kwInt => some .int
    | .kwBool => some .bool
    | .kwChar => some .char
    | .kwString => some .string
    | .kwVoid => some .void
    | _ => none))
  <|>
  (do
    let _ ← expectKindTokMsg (only .kwStruct) "expected 'struct'"
    let name ← parseStructName
    pure (.struct name))
  <|>
  (do
    let name ← parseTypeIdent
    pure (.typeName name))

partial def parseTauSuffix : P (Tau → Tau) :=
  (do
    let _ ← expectKindTokMsg (only .mul) "expected '*'"
    pure Tau.ptr)
  <|>
  (do
    let _ ← expectKindTokMsg (only .lBracket) "expected '['"
    let _ ← expectKindTokMsg (only .rBracket) "expected ']'"
    pure Tau.array)

partial def parseTau : P Tau := do
  let base ← parseTauBase
  let suffixesRev ← Parser.foldl (fun acc suffix => suffix :: acc) [] parseTauSuffix
  pure (suffixesRev.reverse.foldl (fun tau suffix => suffix tau) base)

partial def parseParenExpr : P MarkedExpr := do
  let lTok ← expectKindTokMsg (fun | .lParen => true | _ => false) "expected '('"
  let e ← parseExpr
  let rTok ← expectKindTokMsg (fun | .rParen => true | _ => false) "expected ')'"
  pure { e with
    span := some (spanFromTokenBounds lTok rTok)
  }

partial def parseAllocExpr : P MarkedExpr := do
  let startTok ← expectKindTokMsg (only .kwAlloc) "expected 'alloc'"
  let _ ← expectKindTokMsg (only .lParen) "expected '(' after alloc"
  let tau ← parseTau
  let endTok ← expectKindTokMsg (only .rParen) "expected ')' after alloc type"
  pure { node := .alloc tau, span := some (spanFromTokenBounds startTok endTok) }

partial def parseAllocArrayExpr : P MarkedExpr := do
  let startTok ← expectKindTokMsg (only .kwAllocArray) "expected 'alloc_array'"
  let _ ← expectKindTokMsg (only .lParen) "expected '(' after alloc_array"
  let tau ← parseTau
  let _ ← expectKindTokMsg (only .comma) "expected ',' after alloc_array type"
  let size ← parseExpr
  let endTok ← expectKindTokMsg (only .rParen) "expected ')' after alloc_array size"
  pure { node := .allocArray tau size, span := some (spanFromTokenBounds startTok endTok) }

partial def parseLengthExpr : P MarkedExpr := do
  let startTok ← expectKindTokMsg (only .length) "expected '\\length'"
  let _ ← expectKindTokMsg (only .lParen) "expected '(' after \\length"
  let arrayLike ← parseExpr
  let endTok ← expectKindTokMsg (only .rParen) "expected ')' after \\length argument"
  pure { node := .length arrayLike, span := some (spanFromTokenBounds startTok endTok) }

partial def parsePrimary : P MarkedExpr :=
  first [
    parseParenExpr,
    parseHexLit,
    parseIntLit,
    parseBoolLit,
    parseCharLit,
    parseStringLit,
    parseNullLit,
    parseResultExpr,
    parseHastagExpr,
    parseAllocArrayExpr,
    parseAllocExpr,
    parseLengthExpr,
    parseFCall,
    parseVar,
    throwUnexpectedWithMessage none "expected expression atom"
  ]

partial def parsePostfixOpCore : P (MarkedExpr → Expr) :=
  (do
    let _ ← expectKindTokMsg (only .dot) "expected '.'"
    let field ← parseFieldName
    pure (fun base => .dot base field))
  <|>
  (do
    let _ ← expectKindTokMsg (only .arrow) "expected '->'"
    let field ← parseFieldName
    pure (fun base => .arrow base field))
  <|>
  (do
    let _ ← expectKindTokMsg (only .lBracket) "expected '['"
    let index ← parseExpr
    let _ ← expectKindTokMsg (only .rBracket) "expected ']'"
    pure (fun base => .arrAccess base index))

partial def parsePostfixOp : P (MarkedExpr → MarkedExpr) := do
  let (mk, opSpan) ← withConsumedSpan parsePostfixOpCore
  pure (fun base => { node := mk base, span := spanCoverOpt base.span opSpan })

partial def parseAtom : P MarkedExpr := do
  let (base, baseSpan) ← withConsumedSpan parsePrimary
  let base := { base with span := base.span <|> baseSpan }
  let opsRev ← Parser.foldl (fun acc op => op :: acc) [] parsePostfixOp
  pure (opsRev.reverse.foldl (fun acc op => op acc) base)

partial def parseUnOp : P UnOp :=
  satisfyKind (fun
    | .bang => some .bang
    | .squiggly => some .bitNot
    | .sub => some .negative
    | .negative => some .negative
    | _ => none)

partial def parseMulOp : P BinOp :=
  satisfyKind (fun
    | .mul => some .mul
    | .div => some .div
    | .mod => some .mod
    | _ => none)

partial def parseAddOp : P BinOp :=
  satisfyKind (fun
    | .plus => some .plus
    | .sub  => some .sub
    | _ => none)

partial def parseShiftOp : P BinOp :=
  satisfyKind (fun
    | .shl => some .shl
    | .shr => some .shr
    | _ => none)

partial def parseCompOp : P BinOp :=
  satisfyKind (fun
    | .lt  => some .lt
    | .lte => some .lte
    | .gt  => some .gt
    | .gte => some .gte
    | _ => none)

partial def parseEqOp : P BinOp :=
  satisfyKind (fun
    | .eq  => some .eq
    | .neq => some .neq
    | _ => none)

partial def parseBitAndOp : P BinOp :=
  satisfyKind (fun
    | .and => some .bitAnd
    | _ => none)

partial def parseBitXorOp : P BinOp :=
  satisfyKind (fun
    | .xor => some .xor
    | _ => none)

partial def parseBitOrOp : P BinOp :=
  satisfyKind (fun
    | .or => some .bitOr
    | _ => none)

partial def parseLandOp : P BinOp :=
  satisfyKind (fun
    | .land => some .land
    | _ => none)

partial def parseLorOp : P BinOp :=
  satisfyKind (fun
    | .lor => some .lor
    | _ => none)

partial def parseAssignOp : P AssignOp :=
  satisfyKind (fun
    | .assign => some .assign
    | .plusEq => some .plusEq
    | .subEq  => some .subEq
    | .mulEq  => some .mulEq
    | .divEq  => some .divEq
    | .modEq  => some .modEq
    | .andEq  => some .bitAndEq
    | .xorEq  => some .xorEq
    | .orEq   => some .bitOrEq
    | .shlEq  => some .shlEq
    | .shrEq  => some .shrEq
    | _ => none)

partial def parseUnary : P MarkedExpr := do
  let opsRev ← Parser.foldl (fun acc op => op :: acc) [] <|
    (do
      let (op, opSpan) ← withConsumedSpan parseUnOp
      pure (fun (expr : MarkedExpr) => ({ node := .unop op expr, span := spanCoverOpt opSpan expr.span } : MarkedExpr)))
    <|>
    (do
      let (_, opSpan) ← withConsumedSpan (expectKindTokMsg (only .mul) "expected '*'")
      pure (fun (expr : MarkedExpr) => ({ node := .deref expr, span := spanCoverOpt opSpan expr.span } : MarkedExpr)))
  let ops := opsRev.reverse
  let base ← parseAtom
  pure <| List.foldr (fun op acc => op acc) base ops

partial def parseLeftAssoc (term : P MarkedExpr) (op : P BinOp) : P MarkedExpr := do
  let lhs ← term
  let restRev ← Parser.foldl (fun acc x => x :: acc) [] do
    let o ← op
    let rhs ← term
    pure (o, rhs)
  let rest := restRev.reverse
  pure <| List.foldl
    (fun acc (o, rhs) => { node := .binop o acc rhs, span := spanCoverOpt acc.span rhs.span }) lhs rest

-- These parsers build on each other through the precedence binding strength of C0.
partial def parseMulExpr : P MarkedExpr :=
  parseLeftAssoc parseUnary parseMulOp

partial def parseAddExpr : P MarkedExpr :=
  parseLeftAssoc parseMulExpr parseAddOp

partial def parseShiftExpr : P MarkedExpr :=
  parseLeftAssoc parseAddExpr parseShiftOp

partial def parseCompExpr : P MarkedExpr :=
  parseLeftAssoc parseShiftExpr parseCompOp

partial def parseEqExpr : P MarkedExpr :=
  parseLeftAssoc parseCompExpr parseEqOp

partial def parseBitAndExpr : P MarkedExpr :=
  parseLeftAssoc parseEqExpr parseBitAndOp

partial def parseBitXorExpr : P MarkedExpr :=
  parseLeftAssoc parseBitAndExpr parseBitXorOp

partial def parseBitOrExpr : P MarkedExpr :=
  parseLeftAssoc parseBitXorExpr parseBitOrOp

partial def parseLandExpr : P MarkedExpr :=
  parseLeftAssoc parseBitOrExpr parseLandOp

partial def parseLorExpr : P MarkedExpr :=
  parseLeftAssoc parseLandExpr parseLorOp

partial def parseCondExpr : P MarkedExpr := do
  let test ← parseLorExpr
  (do
    qmark
    let thenBranch ← parseCondExpr
    colon
    let elseBranch ← parseCondExpr
    pure { node := .ternary test thenBranch elseBranch, span := spanCoverOpt test.span elseBranch.span })
    <|>
    pure test

partial def parseArgs : P (List MarkedExpr) := do
  let firstOpt ← option? parseExpr
  match firstOpt with
  | none => pure []
  | some first =>
      let restRev ← Parser.foldl (fun acc p => p :: acc) [] do
        let _ ← expectKindTokMsg (only .comma) "expected ',' between arguments"
        parseExpr
      pure (first :: restRev.reverse)

partial def parseFCall : P MarkedExpr := do
  let idTok ← expectKindTokMsg (fun | .ident _ => true | _ => false) "expected function name"
  let fname :=
    match idTok.kind with
    | .ident name => name
    | _ => ""
  let _ ← expectKindTokMsg (only .lParen) "expected '('"
  let args ← parseArgs
  let rParen ← expectKindTokMsg (only .rParen) "expected ')'"
  pure ({ node := .call fname args, span := some (spanFromTokenBounds idTok rParen) })

partial def parseExpr : P MarkedExpr :=
  withErrorMessage "while parsing expression" parseCondExpr

end


mutual
partial def parseLValueBase : P ParsedLValue :=
  (do
    let (name, sp) ← withConsumedSpan parseIdent
    pure { lvalue := { node := .var name, span := sp }, startsWithBareDeref := false })
  <|>
  (do
    let _ ← expectKindTokMsg (only .lParen) "expected '('"
    let lhs ← parseLValueExpr
    let _ ← expectKindTokMsg (only .rParen) "expected ')'"
    pure { lvalue := lhs.lvalue, startsWithBareDeref := false })
  <|>
  (do
    let (_, starSpan) ← withConsumedSpan (expectKindTokMsg (only .mul) "expected '*'")
    let lhs ← parseLValueExpr
    pure { lvalue := { node := .deref lhs.lvalue, span := spanCoverOpt starSpan lhs.lvalue.span }, startsWithBareDeref := true })

partial def parseLValuePostfixOpCore : P (MarkedLValue → LValue) :=
  (do
    let _ ← expectKindTokMsg (only .dot) "expected '.'"
    let field ← parseFieldName
    pure (fun base => .dot base field))
  <|>
  (do
    let _ ← expectKindTokMsg (only .arrow) "expected '->'"
    let field ← parseFieldName
    pure (fun base => .arrow base field))
  <|>
  (do
    let _ ← expectKindTokMsg (only .lBracket) "expected '['"
    let index ← parseExpr
    let _ ← expectKindTokMsg (only .rBracket) "expected ']'"
    pure (fun base => .arrAccess base index))

partial def parseLValuePostfixOp : P (MarkedLValue → MarkedLValue) := do
  let (mk, opSpan) ← withConsumedSpan parseLValuePostfixOpCore
  pure (fun base => { node := mk base, span := spanCoverOpt base.span opSpan })

partial def parseLValueExpr : P ParsedLValue := do
  let base ← parseLValueBase
  let opsRev ← Parser.foldl (fun acc op => op :: acc) [] parseLValuePostfixOp
  pure { base with lvalue := opsRev.reverse.foldl (fun acc op => op acc) base.lvalue }
end

def parseLValue : P (ParsedLValue × Option SrcSpan) :=
  withConsumedSpan parseLValueExpr

def parseIncr : P MarkedStm := do
  let (lhs, varSpan) ← parseLValue
  if lhs.startsWithBareDeref then
    throwUnexpectedWithMessage none "'*x++' is not valid syntax; write '(*x)++' if the dereference is the lvalue"
  let incrTok ← expectKindTokMsg (only .incr) "expected '++' after identifier"

  let node :=
    .incr lhs.lvalue
  pure { node := node
       , span :=
          match varSpan with
          | some sp => some { startLoc := sp.startLoc, endLoc := incrTok.span.endLoc, fileName := sp.fileName }
          | none => some incrTok.span
       }

def parseDecr : P MarkedStm := do
  let (lhs, varSpan) ← parseLValue

  -- this *x-- (and its variations) is slightly ambiguous due to binding, so we reject this form
  if lhs.startsWithBareDeref then
    throwUnexpectedWithMessage none "'*x--' is not valid syntax; write '(*x)--' if the dereference is the lvalue"
  let decrTok ← expectKindTokMsg (only .decr) "expected '--' after identifier"
  let node :=
    .decr lhs.lvalue
  pure { node := node
       , span :=
          match varSpan with
          | some sp => some { startLoc := sp.startLoc, endLoc := decrTok.span.endLoc, fileName := sp.fileName }
          | none => some decrTok.span
       }

def parseReturnStm : P MarkedStm := do
  let kwTok ← expectKindTokMsg (only .kwReturn) "expected 'return'"
  let value? ← option? parseExpr
  let semiTok ← expectKindTokMsg (only .semicolon) "expected ';' after return statement"
  pure { node := .ret value?
       , span := some (spanFromTokenBounds kwTok semiTok)
       }

def parseAssignCore : P MarkedStm := do
  let (lhs, varSpan) ← parseLValue
  let op ← parseAssignOp
  let rhs ← parseExpr
  match op with
  | .assign =>
      pure { node := .assign lhs.lvalue rhs, span := varSpan }
  | _ =>
      pure { node := .asop lhs.lvalue op rhs, span := varSpan }

def parseExprCore : P MarkedStm := do
  let (e, exprSpan) ← withConsumedSpan parseExpr
  pure { node := .expr e, span := exprSpan }

def parseVarDefnCore : P MarkedStm := do
  let (tau, tauSpan) ← withConsumedSpan parseTau
  let varName ← parseIdent
  pure { node := .declare varName tau none { node := .nop, span := none }, span := tauSpan }

def parseVarDeclCore : P MarkedStm := do
  let (tau, tauSpan) ← withConsumedSpan parseTau
  let varName ← parseIdent
  let _ ← expectKindTokMsg (only .assign) "expected '=' in variable declaration"
  let initExpr ← parseExpr
  pure { node := .declare varName tau (some initExpr) { node := .nop, span := none }, span := tauSpan }

def parseSimpleCore : P MarkedStm :=
  withErrorMessage "while parsing simple statement" <|
    (parseVarDeclCore
    <|> parseVarDefnCore
    <|> parseAssignCore
    <|> parseIncr
    <|> parseDecr
    <|> parseExprCore)

def parseForUpdateCore : P MarkedStm :=
  withErrorMessage "while parsing for update statement" <|
    (parseAssignCore
    <|> parseIncr
    <|> parseDecr
    <|> parseExprCore)


def parseSimpleStm : P MarkedStm := do
  let (s, coreSpan) ← withConsumedSpan parseSimpleCore
  let semiTok ← expectKindTokMsg (only .semicolon) "expected ';' after simple statement"
  let span :=
    match coreSpan with
    | some sp => some { startLoc := sp.startLoc, endLoc := semiTok.span.endLoc, fileName := sp.fileName }
    | none => some semiTok.span
  pure { node := s.node, span := span }

def foldStms (stms : List MarkedStm) (span : Option SrcSpan := none) : MarkedStm :=
  match stms with
  | [] => { node := .nop, span := span }
  | [s] => s
  | s :: rest =>
    let restStm := foldStms rest span
    match s.node with
    | .declare varName varType init body =>
      { node := .declare varName varType init { node := .seq body restStm, span := span }, span := s.span }
    | _ =>
      { node := .seq s restStm, span := span }

mutual

partial def parseContractKind : P (MarkedExpr → Anno) :=
  satisfyKind (fun
    | .requires => some Anno.requires
    | .ensures => some Anno.ensures
    | .loopInvariant => some Anno.loopInvariant
    | .kwAssert => some Anno.asserts
    | .ident "asserts" => some Anno.asserts
    | _ => none)

partial def parseSingleAnnotation : P MarkedAnno :=
  let parseLineAnnotation : P MarkedAnno := do
    let startTok ← expectKindTokMsg (only .annotation) "expected '//@'"
    let (annoNode, _) ← withConsumedSpan do
      let contractCtor ← parseContractKind
      let contractExpr ← parseExpr
      pure (contractCtor contractExpr)
    let semiTok ← expectKindTokMsg (only .semicolon) "expected ';' after annotation contract"
    let endLoc := semiTok.span.endLoc
    pure { node := annoNode
         , span := some { startLoc := startTok.span.startLoc
                        , endLoc := endLoc
                        , fileName := startTok.span.fileName
                        }
         }

  let parseMultilineAnnotation : P MarkedAnno := do
    let startTok ← expectKindTokMsg (only .openMultilineAnnotation) "expected '/*@'"
    let (annoNode, _) ← withConsumedSpan do
      let contractCtor ← parseContractKind
      let contractExpr ← parseExpr
      pure (contractCtor contractExpr)
    let _ ← expectKindTokMsg (only .semicolon) "expected ';' after annotation contract"
    let closeTok ← expectKindTokMsg (only .closeMultilineAnnotation) "expected '@*/' to close multiline annotation"
    let endLoc := closeTok.span.endLoc
    pure { node := annoNode
         , span := some { startLoc := startTok.span.startLoc
                        , endLoc := endLoc
                        , fileName := startTok.span.fileName
                        }
         }

  parseLineAnnotation <|> parseMultilineAnnotation

/--
Parse statements up to the closing `}` of a block. A statement that fails to
parse reports its own error, instead of the loop backtracking over it and
reporting a missing `}`.
-/
partial def parseStmsUntilRBrace (acc : List MarkedStm := []) : P (List MarkedStm) := do
  let st ← Parser.getStream
  let kind? : Option Lexer.TokenKind := st.input.head?.map (·.kind)
  match kind? with
  | some .rBrace | some .eof | none => pure acc.reverse
  | some _ => parseStmsUntilRBrace ((← parseStm) :: acc)

partial def parseBlockStm : P MarkedStm := do
  let lTok ← expectKindTokMsg (only .lBrace) "expected '{'"
  let body ← parseStmsUntilRBrace
  let rTok ← expectKindTokMsg (only .rBrace) "expected '}'"
  let span := some (spanFromTokenBounds lTok rTok)
  let body := foldStms body span
  pure { node := .seq { node := .nop, span := span } body, span := span }

partial def parseIfStm : P MarkedStm := do
  let ifTok ← expectKindTokMsg (only .kwIf) "expected 'if'"
  let _ ← expectKindTokMsg (only .lParen) "expected '(' after if"
  let cond ← parseExpr
  let _ ← expectKindTokMsg (only .rParen) "expected ')' after if condition"
  let thenBranch ← parseStm
  let elseBranch ←
    (do
      let _ ← expectKindTok (only .kwElse)
      parseStm)
    <|>
    pure { node := .nop, span := none }
  pure { node := .ifLit cond thenBranch elseBranch, span := some ifTok.span }

-- C0 places loop invariants between the loop header and the loop body:
--   while (e) //@loop_invariant I; { ... }
-- They are kept as leading annotation statements of the loop body.
partial def parseLoopBody : P MarkedStm := do
  let invsRev ← Parser.foldl (fun acc anno => anno :: acc) [] parseSingleAnnotation
  let body ← parseStm
  pure <| invsRev.foldl
    (fun acc anno => { node := .seq { node := .annotation anno, span := anno.span } acc, span := body.span })
    body

partial def parseWhileStm : P MarkedStm := do
  let whileTok ← expectKindTokMsg (only .kwWhile) "expected 'while'"
  let _ ← expectKindTokMsg (only .lParen) "expected '(' after while"
  let cond ← parseExpr
  let _ ← expectKindTokMsg (only .rParen) "expected ')' after while condition"
  let body ← parseLoopBody
  pure { node := .whileLit cond body, span := some whileTok.span }

partial def parseForStm : P MarkedStm := do
  let forTok ← expectKindTokMsg (only .kwFor) "expected 'for'"
  let _ ← expectKindTokMsg (only .lParen) "expected '(' after for"
  let init ← (option? parseSimpleCore)
  let _ ← expectKindTokMsg (only .semicolon) "expected ';' after for init"
  let test ← parseExpr
  let _ ← expectKindTokMsg (only .semicolon) "expected ';' after for test"
  let update ← (option? parseForUpdateCore)
  let _ ← expectKindTokMsg (only .rParen) "expected ')' after for update"
  let body ← parseLoopBody
  let initStm := init.getD { node := .nop, span := none }
  let updateStm := update.getD { node := .nop, span := none }
  pure { node := .forLit initStm test updateStm body, span := some forTok.span }

partial def parseAssertStm : P MarkedStm := do
  let kwTok ← expectKindTokMsg (only .kwAssert) "expected 'assert'"
  let _ ← expectKindTokMsg (only .lParen) "expected '(' after assert"
  let e ← parseExpr
  let _ ← expectKindTokMsg (only .rParen) "expected ')' after assert expression"
  let semiTok ← expectKindTokMsg (only .semicolon) "expected ';' after assert statement"
  pure { node := .assert e, span := some (spanFromTokenBounds kwTok semiTok) }

partial def parseAnnotationStm : P MarkedStm := do
  let a ← parseSingleAnnotation
  pure { node := .annotation a, span := a.span }

partial def parseErrorStm : P MarkedStm := do
  let kwTok ← expectKindTokMsg (only .kwError) "expected 'error'"
  let _ ← expectKindTokMsg (only .lParen) "expected '(' after error"
  let e ← parseExpr
  let _ ← expectKindTokMsg (only .rParen) "expected ')' after error expression"
  let semiTok ← expectKindTokMsg (only .semicolon) "expected ';' after error statement"
  pure { node := .error e, span := some (spanFromTokenBounds kwTok semiTok) }

/--
A statement, chosen by its first token. Committing to one alternative means a
syntax error is reported by the statement it occurs in, at the token where it
occurs.
-/
partial def parseStm : P MarkedStm := do
  let st ← Parser.getStream
  let kind? : Option Lexer.TokenKind := st.input.head?.map (·.kind)
  match kind? with
  | some .kwIf => parseIfStm
  | some .kwWhile => parseWhileStm
  | some .kwFor => parseForStm
  | some .kwReturn => parseReturnStm
  | some .lBrace => parseBlockStm
  | some .kwAssert => parseAssertStm
  | some .kwError => parseErrorStm
  | some .annotation | some .openMultilineAnnotation => parseAnnotationStm
  | _ => parseSimpleStm
end

def parseTypedef : P GDecl := do
  let _ ← expectKindTokMsg (only .kwTypedef) "expected 'typedef'"
  let tau ← parseTau
  let aliasIdent ← parseIdent
  let _ ← expectKindTokMsg (only .semicolon) "expected ';' after typedef declaration"
  pure (.typedef tau aliasIdent)

def parseField : P Field := do
  let tau ← parseTau
  let fieldName ← parseFieldName
  let _ ← expectKindTokMsg (only .semicolon) "expected ';' after struct field"
  pure (tau, fieldName)

def parseStructDecl : P GDecl := do
  let _ ← expectKindTokMsg (only .kwStruct) "expected 'struct'"
  let name ← parseStructName
  (do
    let _ ← expectKindTokMsg (only .lBrace) "expected '{' in struct definition"
    let fieldsRev ← Parser.foldl (fun acc field => field :: acc) [] parseField
    let _ ← expectKindTokMsg (only .rBrace) "expected '}' after struct fields"
    let _ ← expectKindTokMsg (only .semicolon) "expected ';' after struct definition"
    pure (.sdefn name fieldsRev.reverse))
  <|>
  (do
    let _ ← expectKindTokMsg (only .semicolon) "expected ';' after struct declaration"
    pure (.sdecl name))

def parseParam : P Param := do
  let tau ← parseTau
  let paramName ← parseIdent
  pure (tau, paramName)

def parseParams : P (List Param) := do
  let firstOpt ← option? parseParam
  match firstOpt with
  | none => pure []
  | some first =>
      let restRev ← Parser.foldl (fun acc p => p :: acc) [] do
        let _ ← expectKindTokMsg (only .comma) "expected ',' between parameters"
        parseParam
      pure (first :: restRev.reverse)

/-- A function declaration or definition; the shared header is parsed once. -/
def parseFunction : P GDecl := do
  let prefixAnnosRev ← Parser.foldl (fun acc anno => anno :: acc) [] parseSingleAnnotation
  let tau ← parseTau
  let fname ← parseIdent
  let _ ← expectKindTokMsg (only .lParen) "expected '(' after the function name"
  let params := (← option? parseParams).getD []
  let _ ← expectKindTokMsg (only .rParen) "expected ')' after the function parameters"
  let suffixAnnosRev ← Parser.foldl (fun acc anno => anno :: acc) [] parseSingleAnnotation
  let annotations := prefixAnnosRev.reverse ++ suffixAnnosRev.reverse
  let declaration := do
    let _ ← expectKindTok (only .semicolon)
    pure (GDecl.fdecl tau fname params annotations)
  let definition := do
    let _ ← expectKindTokMsg (only .lBrace) "expected ';' or '{' after the function signature"
    let stms ← parseStmsUntilRBrace
    let _ ← expectKindTokMsg (only .rBrace) "expected '}' to close the function body"
    pure (GDecl.fdefn tau fname params [foldStms stms] annotations)
  declaration <|> definition

def parseGdecl : P GDecl :=
  withErrorMessage "while parsing global declaration" <|
    (parseTypedef <|> parseStructDecl <|> parseFunction)

def runParser {a : Type} (p : P a) (tokens : List Tok) : Except String a :=
  -- Accept optional lexer-emitted EOF token, then require end of token stream.
  match Parser.run (p <* optional eofTok <* endOfInput) (Parser.Stream.mkOfList tokens) with
  | .ok _ x => .ok x
  | .error _ err => .error s!"parse error: {err}"

private def streamLocation (s : TokStream) : String :=
  match s.input.head? with
  | some tok =>
      let span := tok.span
      s!"{span.fileName}:{span.startLoc.line}:{span.startLoc.col}: parse error near {C0VC.Token.Print.ppTokenKind tok.kind}"
  | none => "parse error at end of input"

def parseProgramFromTokens (tokens : List Tok) : Except String Program := do
  let decls := Parser.foldl (fun acc decl => decl :: acc) [] parseGdecl
  match runParser decls tokens with
  | .ok program => .ok (List.reverse program)
  | .error e =>
      -- The declaration loop backtracks over the declaration that failed, so
      -- parse that declaration again to report its own error and position.
      match Parser.run decls (Parser.Stream.mkOfList tokens) with
      | .ok rest _ =>
          match Parser.run parseGdecl rest with
          | .error failed err => .error s!"{streamLocation failed}: {err}"
          | .ok _ _ => .error s!"{streamLocation rest}: {e}"
      | .error failed err => .error s!"{streamLocation failed}: {err}"
