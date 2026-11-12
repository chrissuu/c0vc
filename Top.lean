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
  optLevel      : Nat := 1
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
  dynCheck      : Bool := false
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
    , "  -O LEVEL, --opt=LEVEL  optimization level for --emit=exe, 0-3 (default: 1)"
    , "  --unsafe               omit runtime safety checks (LLVM)"
    , "  -d, --dyn-check        check contracts at run time (LLVM), like cc0 -d"
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
    , ""
    , "--emit=exe compiles with $CC if it is set (it must accept LLVM IR, e.g. clang),"
    , "otherwise with the first clang found on PATH."
    ]

private def parseNat (flag value : String) : Except String Nat :=
  match value.toNat? with
  | some n => .ok n
  | none => .error s!"{flag} expects a number, got `{value}`"

private def parseOptLevel (flag value : String) : Except String Nat := do
  let level ← parseNat flag value
  if level ≤ 3 then .ok level else .error s!"{flag} expects a level from 0 to 3, got `{value}`"

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

/-- A frontend stage: either the stage's result or an error message. -/
private abbrev Stage := ExceptT String IO

private def stage (result : Except String α) : Stage α :=
  ExceptT.mk (pure result)

private def dumpIf (flag : Bool) (text : Unit → String) : Stage Unit :=
  if flag then IO.println (text ()) else pure ()

private def parseProgramFile (file : String) : Stage C0VC.Ast.Program := do
  let source ← IO.FS.readFile file
  let tokens ← stage (C0VC.Lexer.munch file source)
  stage (C0VC.Parse.parseProgramFromTokens tokens)

private def typedefAliases (program : C0VC.Ast.Program) : List String :=
  program.filterMap (fun
    | .typedef _ name => some name
    | _ => none)

private def parseArgs : List String → CliConfig → Except String CliConfig
  | [], cfg => .ok cfg
  | "-t" :: rest, cfg => parseArgs rest { cfg with typecheckOnly := true }
  | "--typecheck-only" :: rest, cfg => parseArgs rest { cfg with typecheckOnly := true }
  | "--unsafe" :: rest, cfg => parseArgs rest { cfg with unsafeMode := true }
  | "--verify" :: rest, cfg => parseArgs rest { cfg with verify := true }
  | "-d" :: rest, cfg => parseArgs rest { cfg with dynCheck := true }
  | "--dyn-check" :: rest, cfg => parseArgs rest { cfg with dynCheck := true }
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
      parseArgs rest { cfg with optLevel := ← parseOptLevel "-O" level }
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
        parseArgs rest { cfg with optLevel := ← parseOptLevel "--opt" (valueOf "--opt=") }
      else if arg.startsWith "--lib=" then
        parseArgs rest { cfg with libs := cfg.libs.concat (valueOf "--lib=") }
      else if arg.startsWith "-e" && arg.length > 2 then
        parseArgs rest { cfg with emit := ← parseEmit (valueOf "-e") }
      else if arg.startsWith "-O" && arg.length > 2 then
        parseArgs rest { cfg with optLevel := ← parseOptLevel "-O" (valueOf "-O") }
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

private def runFrontend (cfg : CliConfig) (infile : String) : Stage (Option FrontendOutput) := do
  let headers := (← cfg.libs.mapM parseProgramFile).flatten
  let source ← IO.FS.readFile infile
  let toBoole := cfg.emit == .boole
  -- Contracts are used by the Boole backend and by LLVM with --dyn-check;
  -- otherwise annotations are comments.
  let keepAnnotations := toBoole || cfg.dynCheck
  let lex := if keepAnnotations then C0VC.Lexer.munchWithTypedefs else C0VC.Lexer.munchWithoutAnnotationsWithTypedefs
  let tokens ← stage (lex (typedefAliases headers) infile source)
  dumpIf cfg.dumpTokens fun _ => C0VC.Token.Print.ppTokens tokens
  let program ← stage (C0VC.Parse.parseProgramFromTokens tokens)
  dumpIf cfg.dumpAst fun _ => C0VC.Ast.Print.ppProgram program
  let elabbed ← stage (C0VC.Elab.run headers program)
  dumpIf cfg.dumpElab fun _ => C0VC.ElabbedAst.Print.ppProgram elabbed
  dumpIf cfg.dumpElabRaw fun _ => C0VC.ElabbedAst.Print.ppProgramRaw elabbed
  let typed ← stage (C0VC.Typechecker.run elabbed (requireMain := !toBoole))
  dumpIf cfg.dumpType fun _ => C0VC.TypedAst.Print.ppProgram typed
  dumpIf cfg.dumpTypeRaw fun _ => C0VC.TypedAst.Print.ppProgramRaw typed
  if cfg.typecheckOnly then
    return none
  let dce := C0VC.Dce.run typed
  dumpIf cfg.dumpDce fun _ => C0VC.TypedAst.Print.ppProgram dce
  dumpIf cfg.dumpDceRaw fun _ => C0VC.TypedAst.Print.ppProgramRaw dce
  if toBoole then
    let booleIR ← stage (C0VC.StrataBoole.Trans.runWithConfig { intModel := cfg.intModel } dce)
    return some (.boole booleIR)
  let tree := C0VC.LLVM.Tree.Trans.run dce
  dumpIf cfg.dumpTree fun _ => C0VC.LLVM.Tree.Print.ppProgram tree
  dumpIf cfg.dumpTreeRaw fun _ => C0VC.LLVM.Tree.Print.ppProgramRaw tree
  let llvmIR := C0VC.LLVM.Codegen.runWithConfig { safetyChecks := !cfg.unsafeMode } tree
  dumpIf cfg.dumpIrRaw fun _ => C0VC.LLVM.IR.Print.ppProgramRaw llvmIR
  return some (.llvm llvmIR)

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

/--
The C runtime linked into executables: `$C0VC_RUNTIME` if set, otherwise
`rt/c0vc.c` next to the compiler checkout, found from the executable's location
(`bin/c0vc` or `.lake/build/bin/c0vc`), otherwise relative to the current
directory.
-/
private def findRuntime : IO (Option String) := do
  if let some path ← IO.getEnv "C0VC_RUNTIME" then
    return some path
  let binDir := (← IO.appPath).parent.getD "."
  let candidates : List System.FilePath :=
    [ binDir / ".." / "rt" / "c0vc.c"
    , binDir / ".." / ".." / ".." / "rt" / "c0vc.c"
    , "rt" / "c0vc.c" ]
  for candidate in candidates do
    if ← candidate.pathExists then
      return some candidate.toString
  return none

/-- The C compiler for --emit=exe, as a command and leading arguments: `$CC`
(split on spaces, as make does), else the first clang on PATH. -/
private def findCC : IO (Option (String × Array String)) := do
  if let some cc ← IO.getEnv "CC" then
    match (cc.splitOn " ").filter (· ≠ "") with
    | cmd :: args => return some (cmd, args.toArray)
    | [] => pure ()
  let dirs := ((← IO.getEnv "PATH").getD "").splitOn ":" |>.filter (· ≠ "")
  let names := "clang" :: ((List.range 11).map fun i => s!"clang-{24 - i}")
  for name in names do
    for dir in dirs do
      let candidate := System.FilePath.mk dir / name
      if ← candidate.pathExists then
        return some (candidate.toString, #[])
  return none

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
  match ← (runFrontend cfg infile).run with
  | .error err =>
      IO.eprintln err
      return 1
  | .ok none => return 0
  | .ok (some (.boole booleIR)) =>
      if !cfg.verify || cfg.outFile.isSome then
        IO.FS.writeFile (outputPath cfg infile ".boole.st") (C0VC.StrataBoole.Codegen.run booleIR)
      if cfg.verify then
        return ← runVerifier cfg infile booleIR
      return 0
  | .ok (some (.llvm llvmIR)) =>
      if cfg.emit == .llvm then
        C0VC.LLVM.EmitLlvm.run llvmIR (outputPath cfg infile ".ll")
        return 0
      let some (cc, ccArgs) ← findCC
        | IO.eprintln "cannot find clang to build the executable; install clang or set CC"
          return 1
      let exe := outputPath cfg infile ".exe"
      let ll := exe ++ ".tmp.ll"
      C0VC.LLVM.EmitLlvm.run llvmIR ll
      let runtimeArgs ←
        if cfg.devNoRuntime then
          pure #[]
        else
          let some runtime ← findRuntime
            | IO.eprintln "cannot find the c0vc runtime rt/c0vc.c; set C0VC_RUNTIME to its path"
              return 1
          pure (if cfg.libs.isEmpty then #[runtime] else #["-DC0VC_WITH_15411_LIB", runtime])
      let out ← IO.Process.output
        { cmd := cc, args := ccArgs ++ #[s!"-O{cfg.optLevel}", ll] ++ runtimeArgs ++ #["-o", exe] }
      IO.FS.removeFile ll
      if out.exitCode != 0 then
        IO.eprintln out.stderr
        return 1
      return 0
