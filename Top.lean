/-
Top

Author(s):
  ~ Chris Su <chrjs@cmu.edu>
-/
import C0VC

inductive EmitTarget where
  | exe
  | llvm
  | boole
deriving Repr, BEq

structure CliConfig where
  infile        : Option String := none
  typecheckOnly : Bool := false
  emit          : EmitTarget := .llvm
  optLevel      : Nat := 0
  libs          : List String := []
  unsafeMode    : Bool := false
  dumpTokens    : Bool := false
  dumpAst       : Bool := false
  dumpElab      : Bool := false
  dumpElabRaw   : Bool := false
  dumpType      : Bool := false
  dumpTypeRaw   : Bool := false
  dumpDce       : Bool := false
  dumpDceRaw    : Bool := false
  dumpTree      : Bool := false
  dumpTreeRaw   : Bool := false
  dumpIrRaw     : Bool := false
  devNoRuntime  : Bool := false
  verify        : Bool := false
  solver        : String := "z3"
  solverTimeout : Nat := 10
  intModel      : C0VC.StrataBoole.IntModel := .bv32
  outFile       : Option String := none

private def usage : String :=
  String.intercalate "\n"
    [ "usage: bin/c0vc [options] infile.c0"
    , ""
    , "  --emit=llvm|exe|boole  output to produce (default: llvm)"
    , "  -o FILE                write the output to FILE"
    , "  -l, --lib HEADER       use a library header (.h0)"
    , "  -t, --typecheck-only   stop after typechecking"
    , "  -O LEVEL, --opt=LEVEL  optimization level"
    , "  --unsafe               omit runtime safety checks (LLVM)"
    , ""
    , "verification (StrataBoole):"
    , "  --verify               verify the program and report failed obligations"
    , "  --solver=NAME          SMT solver executable, z3 or cvc5 (default: z3)"
    , "  --timeout=SECONDS      solver timeout per obligation (default: 10)"
    , "  --int-model=bv32|checked"
    , "                         bv32: exact 32-bit C0 arithmetic (default)"
    , "                         checked: unbounded ints, overflow is an obligation"
    , ""
    , "debugging:"
    , "  --dump-tokens --dump-ast --dump-elab --dump-elab-raw --dump-type --dump-type-raw"
    , "  --dump-dce --dump-dce-raw --dump-tree --dump-tree-raw --dump-ir-raw --dev-no-runtime"
    ]

private def parseNat (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some n => .ok n
  | none => .error s!"{flag} expects a number, got `{value}`"

private def parseEmit (s : String) : Except String EmitTarget :=
  match s with
  | "exe" => .ok .exe
  | "llvm" => .ok .llvm
  | "boole" => .ok .boole
  | _ => .error s!"unknown emit target `{s}` (expected llvm, exe or boole)"

private def parseIntModel (s : String) : Except String C0VC.StrataBoole.IntModel :=
  match s with
  | "bv32" => .ok .bv32
  | "checked" => .ok .checked
  | _ => .error s!"unknown int model `{s}` (expected bv32 or checked)"

private def outputPath (cfg : CliConfig) (infile : String) (ext : String) : String :=
  match cfg.outFile with
  | some file => file
  | none =>
      let parts := infile.splitOn "/"
      let basename := parts.getLast?.getD infile
      basename ++ ext

private def parseProgramFile (file : String) : IO (Except String C0VC.Ast.Program) := do
  let source ← IO.FS.readFile file
  match C0VC.Lexer.munch file source with
  | .error err => pure (.error err)
  | .ok tokens => pure (C0VC.Parse.parseProgramFromTokens tokens)

private def parseProgramFiles : List String → IO (Except String C0VC.Ast.Program)
  | [] => pure (.ok [])
  | file :: rest => do
      match ← parseProgramFile file with
      | .error err => pure (.error err)
      | .ok program =>
          match ← parseProgramFiles rest with
          | .error err => pure (.error err)
          | .ok programs => pure (.ok (program ++ programs))

private def typedefAliases (program : C0VC.Ast.Program) : List String :=
  program.filterMap (fun
    | .typedef _ name => some name
    | _ => none)

mutual
private partial def stripParsedAnnotationsStm (stm : C0VC.Ast.MarkedStm) : C0VC.Ast.MarkedStm :=
  let node :=
    match stm.node with
    | .assign lhs val => .assign lhs val
    | .ifLit test thenBranch elseBranch =>
        .ifLit test (stripParsedAnnotationsStm thenBranch) (stripParsedAnnotationsStm elseBranch)
    | .whileLit test body step =>
        .whileLit test (stripParsedAnnotationsStm body) (stripParsedAnnotationsStm step)
    | .ret valOpt => .ret valOpt
    | .seq first rest =>
        .seq (stripParsedAnnotationsStm first) (stripParsedAnnotationsStm rest)
    | .declare varName type init body =>
        .declare varName type init (stripParsedAnnotationsStm body)
    | .asop lhs op value => .asop lhs op value
    | .forLit init test update body =>
        .forLit
          (stripParsedAnnotationsStm init)
          test
          (stripParsedAnnotationsStm update)
          (stripParsedAnnotationsStm body)
    | .expr e => .expr e
    | .assert test => .assert test
    | .error e => .error e
    | .nop => .nop
    | .annotation _ => .nop
    | .incr lhs => .incr lhs
    | .decr lhs => .decr lhs
  { stm with node := node }
end

private def stripParsedAnnotationsGDecl : C0VC.Ast.GDecl → C0VC.Ast.GDecl
  | .fdecl retType fname params _ =>
      .fdecl retType fname params []
  | .fdefn retType fname params body _ =>
      .fdefn retType fname params (body.map stripParsedAnnotationsStm) []
  | decl => decl

private def stripParsedAnnotations (program : C0VC.Ast.Program) : C0VC.Ast.Program :=
  program.map stripParsedAnnotationsGDecl

private def parseArgs : List String → CliConfig → Except String CliConfig
  | [], cfg => .ok cfg
  | "-t" :: rest, cfg => parseArgs rest { cfg with typecheckOnly := true }
  | "--typecheck-only" :: rest, cfg => parseArgs rest { cfg with typecheckOnly := true }
  | "--unsafe" :: rest, cfg => parseArgs rest { cfg with unsafeMode := true }
  | "--verify" :: rest, cfg => parseArgs rest { cfg with verify := true }
  | "--dump-tokens" :: rest, cfg => parseArgs rest { cfg with dumpTokens := true }
  | "--dump-ast" :: rest, cfg => parseArgs rest { cfg with dumpAst := true }
  | "--dump-elab" :: rest, cfg => parseArgs rest { cfg with dumpElab := true }
  | "--dump-elab-raw" :: rest, cfg => parseArgs rest { cfg with dumpElabRaw := true }
  | "--dump-type" :: rest, cfg => parseArgs rest { cfg with dumpType := true }
  | "--dump-type-raw" :: rest, cfg => parseArgs rest { cfg with dumpTypeRaw := true }
  | "--dump-dce" :: rest, cfg => parseArgs rest { cfg with dumpDce := true }
  | "--dump-dce-raw" :: rest, cfg => parseArgs rest { cfg with dumpDceRaw := true }
  | "--dump-tree" :: rest, cfg => parseArgs rest { cfg with dumpTree := true }
  | "--dump-tree-raw" :: rest, cfg => parseArgs rest { cfg with dumpTreeRaw := true }
  | "--dump-ir-raw" :: rest, cfg => parseArgs rest { cfg with dumpIrRaw := true }
  | "--dev-no-runtime" :: rest, cfg => parseArgs rest { cfg with devNoRuntime := true }
  | "-l" :: lib :: rest, cfg => parseArgs rest { cfg with libs := cfg.libs.concat lib }
  | "--lib" :: lib :: rest, cfg => parseArgs rest { cfg with libs := cfg.libs.concat lib }
  | "-o" :: file :: rest, cfg => parseArgs rest { cfg with outFile := some file }
  | "-O" :: level :: rest, cfg => do
      parseArgs rest { cfg with optLevel := ← parseNat "-O" level }
  | arg :: rest, cfg => do
      let valueOf (flag : String) := (arg.drop flag.length).toString
      if arg.startsWith "--emit=" then
        parseArgs rest { cfg with emit := ← parseEmit (valueOf "--emit=") }
      else if arg.startsWith "--solver=" then
        parseArgs rest { cfg with solver := valueOf "--solver=" }
      else if arg.startsWith "--timeout=" then
        parseArgs rest { cfg with solverTimeout := ← parseNat "--timeout" (valueOf "--timeout=") }
      else if arg.startsWith "--int-model=" then
        parseArgs rest { cfg with intModel := ← parseIntModel (valueOf "--int-model=") }
      else if arg.startsWith "--opt=" then
        parseArgs rest { cfg with optLevel := ← parseNat "--opt" (valueOf "--opt=") }
      else if arg.startsWith "--lib=" then
        parseArgs rest { cfg with libs := cfg.libs.concat (valueOf "--lib=") }
      else if arg.startsWith "-e" && arg.length > 2 then
        parseArgs rest { cfg with emit := ← parseEmit (valueOf "-e") }
      else if arg.startsWith "-O" && arg.length > 2 then
        parseArgs rest { cfg with optLevel := ← parseNat "-O" (valueOf "-O") }
      else if arg.startsWith "-l" && arg.length > 2 then
        parseArgs rest { cfg with libs := cfg.libs.concat (valueOf "-l") }
      else if arg.startsWith "-" then
        .error s!"unknown option `{arg}`"
      else
        match cfg.infile with
        | none => parseArgs rest { cfg with infile := some arg }
        | some _ => .error s!"multiple input files provided: {arg}"

private inductive FrontendOutput where
  | llvm (program : C0VC.LLVM.IR.Program)
  | boole (program : C0VC.StrataBoole.Program)

private def runFrontend (cfg : CliConfig) (infile : String) :
    IO (Except String (Option FrontendOutput)) := do
  let headersResult ← parseProgramFiles cfg.libs
  match headersResult with
  | .error err => pure (.error err)
  | .ok headers =>
      let source ← IO.FS.readFile infile
      let toBoole := cfg.emit == .boole
      let lex :=
        if toBoole then
          C0VC.Lexer.munchWithTypedefs
        else
          C0VC.Lexer.munchWithoutAnnotationsWithTypedefs
      match lex (typedefAliases headers) infile source with
      | .error err => pure (.error err)
      | .ok tokens =>
          if cfg.dumpTokens then
            IO.println (C0VC.Token.Print.ppTokens tokens)
          let parsed := C0VC.Parse.parseProgramFromTokens tokens
          match parsed with
          | .error err => pure (.error err)
          | .ok program =>
              let program :=
                if toBoole then
                  program
                else
                  stripParsedAnnotations program
              if cfg.dumpAst then
                IO.println (C0VC.Ast.Print.ppProgram program)
              match C0VC.Elab.run headers program with
              | .error err => pure (.error err)
              | .ok elabbedAst =>
                  if cfg.dumpElab then
                    IO.println (C0VC.ElabbedAst.Print.ppProgram elabbedAst)
                  if cfg.dumpElabRaw then
                    IO.println (C0VC.ElabbedAst.Print.ppProgramRaw elabbedAst)
                  match C0VC.Typechecker.run elabbedAst (requireMain := !toBoole) with
                  | .error err => pure (.error err)
                  | .ok typedAst =>
                      if cfg.dumpType then
                        IO.println (C0VC.TypedAst.Print.ppProgram typedAst)
                      if cfg.dumpTypeRaw then
                        IO.println (C0VC.TypedAst.Print.ppProgramRaw typedAst)
                      if cfg.typecheckOnly then
                        pure (.ok none)
                      else
                        let dceProgram :=
                          match cfg.emit with
                          | .boole => C0VC.Dce.run typedAst
                          | .llvm | .exe =>
                              C0VC.Dce.run (C0VC.LowerAnnotations.run typedAst)
                        if cfg.dumpDce then
                          IO.println (C0VC.TypedAst.Print.ppProgram dceProgram)
                        if cfg.dumpDceRaw then
                          IO.println (C0VC.TypedAst.Print.ppProgramRaw dceProgram)
                        match cfg.emit with
                        | .boole =>
                            match C0VC.StrataBoole.Trans.runWithConfig { intModel := cfg.intModel } dceProgram with
                            | .ok booleIR => pure (.ok (some (.boole booleIR)))
                            | .error err => pure (.error err)
                        | .llvm | .exe =>
                            let treeProgram := C0VC.LLVM.Tree.Trans.run dceProgram
                            if cfg.dumpTree then
                              IO.println (C0VC.LLVM.Tree.Print.ppProgram treeProgram)
                            if cfg.dumpTreeRaw then
                              IO.println (C0VC.LLVM.Tree.Print.ppProgramRaw treeProgram)
                            let llvmIR := C0VC.LLVM.Codegen.runWithConfig { safetyChecks := not cfg.unsafeMode } treeProgram
                            if cfg.dumpIrRaw then
                              IO.println (C0VC.LLVM.IR.Print.ppProgramRaw llvmIR)
                            pure (.ok (some (.llvm llvmIR)))

private def solverAvailable (solver : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd := solver, args := #["--version"] }
    pure (out.exitCode == 0)
  catch _ =>
    pure false

private def runVerifier (cfg : CliConfig) (infile : String) (program : C0VC.StrataBoole.Program) :
    IO UInt32 := do
  if !(← solverAvailable cfg.solver) then
    IO.eprintln s!"{infile}: cannot run SMT solver `{cfg.solver}`; install it or pass --solver=PATH"
    return 2
  let outcomes ← match ← (C0VC.StrataBoole.Verify.run infile program cfg.solver cfg.solverTimeout).toBaseIO with
    | .ok outcomes => pure outcomes
    | .error err =>
        IO.eprintln s!"{infile}: verification failed to run: {err}"
        return 2
  let failures := outcomes.filterMap (·.render infile)
  for line in failures do
    IO.println line
  let proved := outcomes.size - failures.size
  IO.println s!"{infile}: {proved} of {outcomes.size} proof obligations verified"
  return if failures.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 := do
  let cfgE := parseArgs args {}
  let cfg ← match cfgE with
    | .error err =>
        IO.eprintln s!"{err}\n{usage}"
        return 1
    | .ok cfg => pure cfg

  let infile ← match cfg.infile with
    | none =>
        IO.eprintln usage
        return 1
    | some file => pure file

  let cfg := if cfg.verify then { cfg with emit := .boole } else cfg
  let frontendResult ← runFrontend cfg infile
  match frontendResult with
  | .error err =>
      IO.eprintln err
      return 1
  | .ok none =>
      return 0
  | .ok (some output) =>
        match cfg.emit with
        | .llvm =>
            match output with
            | .llvm llvmIR => C0VC.LLVM.EmitLlvm.run llvmIR (outputPath cfg infile ".ll")
            | .boole _ => IO.eprintln "internal error: expected LLVM output"; return 1
        | .exe =>
            let llvmIR ← match output with
              | .llvm llvmIR => pure llvmIR
              | .boole _ =>
                  IO.eprintln "internal error: expected LLVM output"
                  return 1
            let exe := outputPath cfg infile ".exe"
            let ll := exe ++ ".tmp.ll"
            C0VC.LLVM.EmitLlvm.run llvmIR ll
            let runtimeArgs :=
              if cfg.devNoRuntime then
                #[]
              else if cfg.libs.isEmpty then
                #["rt/c0vc.c"]
              else
                #["-DC0VC_WITH_15411_LIB", "rt/c0vc.c"]
            let clangArgs :=
              #[ll] ++ runtimeArgs ++ #["-o", exe]
            let out ← IO.Process.output {
              cmd := "clang-15",
              args := clangArgs
            }
            IO.FS.removeFile ll
            if out.exitCode != 0 then
              IO.eprintln out.stderr
              return 1
        | .boole =>
            match output with
            | .boole booleIR =>
                if !cfg.verify || cfg.outFile.isSome then
                  IO.FS.writeFile (outputPath cfg infile ".boole.st") (C0VC.StrataBoole.Codegen.run booleIR)
                if cfg.verify then
                  return ← runVerifier cfg infile booleIR
            | .llvm _ =>
                IO.eprintln "internal error: expected Boole output"
                return 1
        return 0
