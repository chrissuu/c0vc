import StrataBoole
import C0VC.Ast.Dce
import C0VC.StrataBoole.Trans
import C0VC.StrataBoole.Codegen

namespace C0VC.StrataBoole.DDM

open Lean.Parser

def booleTextToDDMProgram
    (fileName : String)
    (source : String)
    : IO StrataDDM.Program := do
  let loaded := StrataDDM.Elab.LoadedDialects.ofDialects! Strata.Boole_map.toList.toArray
  let inputContext := StrataDDM.Parser.stringInputContext fileName source
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match StrataDDM.Elab.elabProgram loaded leanEnv inputContext 0 inputContext.endPos with
  | .ok program => pure program
  | .error errors =>
      let errMsg ← errors.foldlM (init := "Parse errors:\n") fun msg e =>
        return s!"{msg}  {e.pos.line}:{e.pos.column}: {← e.data.toString}\n"
      throw (IO.userError errMsg)

def programToBooleText (program : C0VC.StrataBoole.Program) : String :=
  C0VC.StrataBoole.Codegen.run program

def programToDDMProgram
    (fileName : String)
    (program : C0VC.StrataBoole.Program)
    : IO StrataDDM.Program :=
  booleTextToDDMProgram fileName (programToBooleText program)

def typedProgramToBooleProgram
    (program : C0VC.TypedAst.Program)
    : Except String C0VC.StrataBoole.Program :=
  C0VC.StrataBoole.Trans.run (C0VC.Dce.run program)

def typedProgramToBooleText
    (program : C0VC.TypedAst.Program)
    : Except String String := do
  pure (programToBooleText (← typedProgramToBooleProgram program))

def typedProgramToDDMProgram
    (fileName : String)
    (program : C0VC.TypedAst.Program)
    : IO (Except String StrataDDM.Program) := do
  match typedProgramToBooleText program with
  | .error err => pure (.error err)
  | .ok source =>
      try
        pure (.ok (← booleTextToDDMProgram fileName source))
      catch err =>
        pure (.error err.toString)

end C0VC.StrataBoole.DDM
