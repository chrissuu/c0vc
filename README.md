# c0vc

`c0vc` is a Lean 4 implementation of a C0/C1 frontend with two current
backends:

- an LLVM IR backend used for executable testing, and
- a StrataBoole backend used for verification-oriented output.

C0 is a safer subset of C developed at CMU for teaching foundational data
structures, algorithms, and imperative programming. Its emphasis on memory
safety, contracts, and local reasoning makes it a good fit for translation into
an imperative verification language.

## Installation

This project is built with Lean 4 and Lake. Install Lean using
[`elan`](https://github.com/leanprover/elan), then build the compiler:

```sh
lake update
lake build c0vc
```

### C0 Syntax Highlighting
Consider installing the C0 syntax highlighting Visual Studio Code extension, available [here](https://marketplace.visualstudio.com/items?itemName=15122staff.c0-lsp).


## Backends

The LLVM backend exists primarily as a validation path for the frontend. It lets
the compiler run generated programs, which is useful for testing a substantial part of the translation while the verified path is still being built.

The StrataBoole backend lowers typed C0/C1 programs into Boole and can run the
Strata verifier on the result. C0 runtime checks (null dereferences, array
bounds, division by zero, shifts, `assert`, `error`) and contracts
(`//@requires`, `//@ensures`, `//@loop_invariant`, `//@assert`) become proof
obligations, and failures are reported at the C0 source location. See
[`C0VC/StrataBoole/README.md`](C0VC/StrataBoole/README.md) for the translation
and memory model.

## Usage

Build the compiler with Lake:

```sh
lake build c0vc
```

Emit LLVM IR:

```sh
lake exe c0vc --emit=llvm path/to/program.c0
```

Emit StrataBoole:

```sh
lake exe c0vc --emit=boole path/to/program.c0
```

The Boole target writes `<input-basename>.boole.st` in the current working
directory, or the file given with `-o`. A `main` function is not required.

Verify a program (needs `z3` on `PATH`, or `--solver=cvc5`):

```sh
lake exe c0vc --verify path/to/program.c0
```

```text
program.c0:12:10: error: array index may be out of bounds [bounds_L12C10]
program.c0: 7 of 8 proof obligations verified
```

`--int-model=bv32` (the default) uses exact 32-bit C0 arithmetic;
`--int-model=checked` uses unbounded integers and adds an overflow obligation to
every arithmetic operation. Run `c0vc` with no arguments for all options.

## Tests

`tests/boole/` holds C0 programs with the expected `--verify` output:

```sh
lake build c0vc
tests/boole/run.sh            # compare
tests/boole/run.sh --update   # regenerate the expected output
```

## Repository Layout

- `C0VC/Ast/` contains the parsed, elaborated, and typed AST passes.
- `C0VC/LLVM/` contains the LLVM IR backend.
- `C0VC/StrataBoole/` contains the Boole IR, C0-to-Boole lowering, struct
  layout model, and text renderer.
- `Top.lean` wires the command-line frontend and emit targets together.
- `LANGUAGE.md` records C0/C1 language notes that affect this compiler.
- `WORKLOG.md` tracks design notes and implementation progress.

Both LLVM and StrataBoole backends share the modules in `Ast/` up through
`TypedAst`.

## Gaps
Known StrataBoole gaps include:

- calls inside contracts (specification functions such as `is_sorted`)
- framing finer than one heap map per cell type
- `\hastag` and C1 `void*`
- string contents (strings are opaque values)
- slow symbolic execution for long runs of straight-line heap writes.
