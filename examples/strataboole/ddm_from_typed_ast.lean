import C0VC.StrataBoole.DDM
import StrataBoole

open C0VC.TypedAst

private def mainFn : FunctionDef :=
  { retType := .int
    fname := "main"
    params := []
    body := [.ret (some { node := .intLit 0, tau := .int })]
    annotations := [] }

#eval do
  let result ← C0VC.StrataBoole.DDM.typedProgramToDDMProgram "typed-main.boole.st" [mainFn]
  match result with
  | .error err =>
      IO.println s!"error: {err}"
  | .ok program =>
      match Strata.Boole.getProgram program with
      | .error err => IO.println s!"boole error: {err}"
      | .ok _ => IO.println "ok"
