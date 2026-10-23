import C0VC.Embed
import StrataBoole
import StrataDDM.Integration.Lean.HashCommands
import StrataDDM.Integration.Lean.ToExpr

open Lean
open Lean.Elab.Term (TermElab)
open Lean.Parser (InputContext)
open StrataDDM.Lean (arrayToExpr)

namespace C0VC.Embed.Lean

meta section

private def throwC0Error (msg : String) : Lean.Elab.Term.TermElabM α := do
  throwError s!"C0 embedding failed: {msg}"

private def logDDMErrors
    (_fullInputCtx booleInputCtx : InputContext)
    (_snippetStart : String.Pos.Raw)
    (errors : Array Lean.Message)
    : Lean.Elab.Term.TermElabM Unit := do
  for err in errors do
    let msg ← err.data.toString
    logErrorAt (← getRef)
      m!"C0 embedding produced invalid Boole/Strata at generated Boole \
         {booleInputCtx.fileName}:{err.pos.line}:{err.pos.column}: {msg}"

declare_tagged_region term c0Program "#c0" "#end"

/--
Inline a C0 translation unit into Lean as a `StrataDDM.SourcedProgram`.

The C0 source is parsed and typechecked by C0VC, lowered to Boole text, then
elaborated through Strata's DDM pipeline. The returned value has the same shape
as `#strata`: it can be passed to `Strata.Boole.getProgram`, verification
helpers, or any API accepting `StrataDDM.Program` via coercion.
-/
@[term_elab c0Program]
meta def c0ProgramImpl : TermElab := fun stx _tp => do
  let .atom inputInfo _ := stx[1]
    | throwError s!"Bad {stx[1]}"
  let .original _ snippetStart _ snippetStop := inputInfo
    | throwError s!"Expected input context"

  let fullInputCtx ← (StrataDDM.HasInputContext.getInputContext : CoreM _)
  let c0Source := String.Pos.Raw.extract fullInputCtx.inputString snippetStart snippetStop
  let booleSource ←
    match C0VC.Embed.compileC0ToBooleStringWithHeaders fullInputCtx.fileName [] c0Source with
    | .ok source => pure source
    | .error err => throwC0Error err

  let booleInputCtx : InputContext := {
    inputString := booleSource
    fileName := s!"{fullInputCtx.fileName}.generated.boole.st"
    fileMap := FileMap.ofString booleSource
  }

  let dialectState := StrataDDM.dialectExt.getState (← getEnv)
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match StrataDDM.Elab.elabProgram dialectState.loaded leanEnv booleInputCtx 0 booleInputCtx.endPos with
  | .error errors =>
      logDDMErrors fullInputCtx booleInputCtx snippetStart errors
      return mkApp2 (mkConst ``sorryAx [1]) (toTypeExpr StrataDDM.SourcedProgram) (toExpr true)
  | .ok pgm =>
      let some (.str name root) := dialectState.nameMap[pgm.dialect]?
        | throwError s!"Unknown dialect {pgm.dialect}"
      let operationType := mkConst ``StrataDDM.Operation
      let commandExprs ← monadLift <| pgm.commands.mapM fun cmd => do
        let n ← mkFreshUserName `c0Command
        StrataDDM.addDefn n operationType (toExpr cmd)
        pure (mkConst n)
      let pgmExpr : Lean.Expr :=
        astExpr! StrataDDM.Program.create
          (mkConst (name |>.str s!"{root}_map"))
          (toExpr pgm.dialect)
          (arrayToExpr .zero operationType commandExprs)
      let baseLine : Nat := (fullInputCtx.fileMap.toPosition snippetStart).line
      return mkApp5 (mkConst ``StrataDDM.SourcedProgram.mk)
        pgmExpr
        (toExpr c0Source)
        (toExpr (snippetStart.byteIdx : Nat))
        (toExpr baseLine)
        (toExpr fullInputCtx.fileName)

end

end C0VC.Embed.Lean
