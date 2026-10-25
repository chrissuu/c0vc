namespace C0VC.Utils.SrcSpan

def tabWidth : Nat := 4

/-- Location in a source file. -/
structure SrcLoc where
  line : Nat
  col  : Nat
deriving Repr, BEq, DecidableEq

/-- Span in a source file. -/
structure SrcSpan where
  startLoc : SrcLoc
  endLoc   : SrcLoc
  fileName : String
deriving Repr, BEq, DecidableEq

def SrcSpan.show (s : SrcSpan) : String :=
  s!"{s.fileName}:{s.startLoc.line}:{s.startLoc.col}-{s.endLoc.line}:{s.endLoc.col}"

def spanCover (startSpan endSpan : SrcSpan) : SrcSpan :=
  { startLoc := startSpan.startLoc
  , endLoc := endSpan.endLoc
  , fileName := startSpan.fileName
  }

def spanCoverOpt (startSpan? endSpan? : Option SrcSpan) : Option SrcSpan :=
  match startSpan?, endSpan? with
  | some startSpan, some endSpan => some (spanCover startSpan endSpan)
  | some startSpan, none => some startSpan
  | none, some endSpan => some endSpan
  | none, none => none

end C0VC.Utils.SrcSpan
