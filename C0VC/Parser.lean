namespace Parser

namespace Stream

structure OfList (τ : Type) where
  input : List τ
  past : List τ := []
  /-- How many tokens have been consumed. -/
  pos : Nat := 0
deriving Repr

def mkOfList (tokens : List τ) : OfList τ :=
  { input := tokens, past := [] }

end Stream

namespace Error

abbrev Simple (_σ _τ : Type) := String

end Error

protected inductive Result (ε σ α : Type) where
  | ok : σ → α → Parser.Result ε σ α
  | error : σ → ε → Parser.Result ε σ α
deriving Repr

abbrev ParserT (ε σ τ : Type) (_m : Type → Type) (α : Type) : Type :=
  (τ → τ) → σ → Parser.Result ε σ α

abbrev Parser (ε σ τ : Type) (α : Type) : Type :=
  ParserT ε σ τ Id α

abbrev SimpleParser (σ τ : Type) (α : Type) : Type :=
  Parser (Error.Simple σ τ) σ τ α

namespace Parser

protected def run {ε σ τ α : Type} (p : Parser ε σ τ α) (s : σ) :
    Parser.Result ε σ α :=
  p id s

end Parser

instance {ε σ τ : Type} : Monad (Parser ε σ τ) where
  pure x := fun _ s => .ok s x
  bind p f := fun ph s =>
    match p ph s with
    | .ok s' x => f x ph s'
    | .error s' e => .error s' e
  map f p := fun ph s =>
    match p ph s with
    | .ok s' x => .ok s' (f x)
    | .error s' e => .error s' e
  seq f x := fun ph s =>
    match f ph s with
    | .ok s' f' =>
        match x () ph s' with
        | .ok s'' x' => .ok s'' (f' x')
        | .error s'' e => .error s'' e
    | .error s' e => .error s' e
  seqLeft x y := fun ph s =>
    match x ph s with
    | .ok s' x' =>
        match y () ph s' with
        | .ok s'' _ => .ok s'' x'
        | .error s'' e => .error s'' e
    | .error s' e => .error s' e
  seqRight x y := fun ph s =>
    match x ph s with
    | .ok s' _ => y () ph s'
    | .error s' e => .error s' e

instance {ε σ τ : Type} : MonadExceptOf ε (Parser ε σ τ) where
  throw e := fun _ s => .error s e
  tryCatch p h := fun ph s =>
    match p ph s with
    | .ok s' x => .ok s' x
    | .error s' e => h e ph s'

instance {ε τ α : Type} : OrElse (Parser ε (Stream.OfList τ) τ α) where
  orElse p q := fun ph s =>
    match p ph s with
    | .ok s' x => .ok s' x
    | .error _ _ => q () ph s

def unexpectedMsg : Option τ → String
  | none => "unexpected end of input"
  | some _ => "unexpected token"

def getStream {ε τ : Type} : ParserT ε (Stream.OfList τ) τ Id (Stream.OfList τ) :=
  fun _ s => .ok s s

def setStream {ε τ : Type} (s : Stream.OfList τ) :
    ParserT ε (Stream.OfList τ) τ Id Unit :=
  fun _ _ => .ok s ()

def throwUnexpectedWithMessage {τ α : Type} (input : Option τ := none) (msg : String) :
    SimpleParser (Stream.OfList τ) τ α :=
  fun _ s => .error s s!"{unexpectedMsg input}: {msg}"

def withErrorMessage {τ α : Type} (msg : String)
    (p : SimpleParser (Stream.OfList τ) τ α) :
    SimpleParser (Stream.OfList τ) τ α :=
  fun ph s =>
    match p ph s with
    | .ok s' x => .ok s' x
    | .error s' e => .error s' s!"{e}; {msg}"

def tokenMap {τ α : Type} (test : τ → Option α) :
    SimpleParser (Stream.OfList τ) τ α :=
  fun _ s =>
    match s.input with
    | [] => .error s (unexpectedMsg (τ := τ) none)
    | tok :: rest =>
        match test tok with
        | some x => .ok { input := rest, past := tok :: s.past, pos := s.pos + 1 } x
        | none => .error s (unexpectedMsg (some tok))

def tokenFilter {τ : Type} (test : τ → Bool) :
    SimpleParser (Stream.OfList τ) τ τ :=
  tokenMap fun tok => if test tok then some tok else none

def endOfInput {τ : Type} : SimpleParser (Stream.OfList τ) τ Unit :=
  fun _ s =>
    match s.input with
    | [] => .ok s ()
    | tok :: _ => .error s (unexpectedMsg (some tok))

def option? {τ α : Type} (p : SimpleParser (Stream.OfList τ) τ α) :
    SimpleParser (Stream.OfList τ) τ (Option α) :=
  fun ph s =>
    match p ph s with
    | .ok s' x => .ok s' (some x)
    | .error _ _ => .ok s none

def optional {τ α : Type} (p : SimpleParser (Stream.OfList τ) τ α) :
    SimpleParser (Stream.OfList τ) τ Unit :=
  fun ph s =>
    match option? p ph s with
    | .ok s' _ => .ok s' ()
    | .error s' e => .error s' e

/--
Apply `p` until it fails, folding the results. A success that consumes no
input also ends the loop, which would otherwise never terminate. Every other
iteration consumes a token, so the fuel is never the limiting factor.
-/
def foldl {τ α β : Type} (f : β → α → β) (init : β)
    (p : SimpleParser (Stream.OfList τ) τ α) :
    SimpleParser (Stream.OfList τ) τ β :=
  fun ph s =>
    let rec go : Nat → β → Stream.OfList τ → Parser.Result (Error.Simple (Stream.OfList τ) τ) (Stream.OfList τ) β
      | 0, acc, s => .ok s acc
      | fuel + 1, acc, s =>
          match p ph s with
          | .ok s' x => if s'.pos > s.pos then go fuel (f acc x) s' else .ok s' (f acc x)
          | .error _ _ => .ok s acc
    go (2 ^ 63) init s

def first {τ α : Type} :
    List (SimpleParser (Stream.OfList τ) τ α) → SimpleParser (Stream.OfList τ) τ α
  | [] => fun _ s => .error s "no parser alternatives"
  | p :: ps => ps.foldl (fun acc next => acc <|> next) p

end Parser
