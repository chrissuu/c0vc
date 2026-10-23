import StrataBoole
import C0VC.StrataBoole.DDM

/-!
StrataBoole.Verify

Runs the Strata Boole verifier on a lowered program and reports each proof
obligation at the C0 source location that produced it.
-/

namespace C0VC.StrataBoole.Verify

open C0VC.StrataBoole

inductive Status where
  | proved
  | failed
  | unknown
  | error (msg : String)
deriving Inhabited, BEq

structure Outcome where
  obligation : String
  status : Status
  info : Option LabelInfo
deriving Inhabited

private def containsInfix (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Find the C0 label an obligation was generated from. Strata prefixes and suffixes labels. -/
def findLabel (labels : Array LabelInfo) (obligation : String) : Option LabelInfo :=
  let padded := "_" ++ obligation ++ "_"
  labels.foldl
    (fun best info =>
      if containsInfix padded ("_" ++ info.label ++ "_") then
        match best with
        | some b => if info.label.length > b.label.length then some info else best
        | none => some info
      else best)
    none

private def describe (obligation : String) (info? : Option LabelInfo) : String :=
  let base := match info? with
    | some info => info.message
    | none => s!"generated obligation {obligation} may not hold"
  if containsInfix obligation "entry_invariant" then
    s!"{base} (on loop entry)"
  else if containsInfix obligation "maintain_invariant" then
    s!"{base} (after a loop iteration)"
  else
    base

def location (fileName : String) (info? : Option LabelInfo) : String :=
  match info? >>= (·.span) with
  | some span => s!"{span.fileName}:{span.startLoc.line}:{span.startLoc.col}"
  | none =>
      match info? with
      | some info => s!"{fileName}: in {info.procedure}"
      | none => fileName

def Outcome.render (fileName : String) (o : Outcome) : Option String :=
  let loc := location fileName o.info
  match o.status with
  | .proved => none
  | .failed => some s!"{loc}: error: {describe o.obligation o.info} [{o.obligation}]"
  | .unknown => some s!"{loc}: error: {describe o.obligation o.info} (not proven: solver returned unknown) [{o.obligation}]"
  | .error msg => some s!"{loc}: error: solver error on {o.obligation}: {msg}"

/-- Verify a lowered program with the given SMT solver executable. -/
def run (fileName : String) (program : Program) (solver : String) (timeout : Nat := 10) :
    IO (Array Outcome) := do
  let source := Codegen.run program
  let ddm ← DDM.booleTextToDDMProgram s!"{fileName}.boole.st" source
  -- Native SMT arrays decide read-over-write chains that the default
  -- axiomatized map encoding leaves unknown. Boole drops quantifier triggers,
  -- so z3 needs model-based instantiation to use quantified facts such as
  -- heap well-formedness and spec-function bodies.
  let isZ3 := (solver.splitOn "/").getLast!.startsWith "z3"
  let options : Core.VerifyOptions :=
    { Core.VerifyOptions.quiet with
      solverTimeout := timeout
      useArrayTheory := true
      solverOptions := if isZ3 then #[("smt.mbqi", "true")] else #[] }
  let results ← Strata.Boole.verify solver ddm (options := options)
  pure <| results.map fun r =>
    let status :=
      if r.isSuccess then Status.proved
      else if r.isFailure then .failed
      else match r.outcome with
        | .error e => .error (toString e)
        | .ok _ => .unknown
    { obligation := r.obligation.label, status, info := findLabel program.labels r.obligation.label }

end C0VC.StrataBoole.Verify
