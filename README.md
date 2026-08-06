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

The StrataBoole backend lowers typed C0/C1 programs into a small Boole-facing IR
and then renders StrataBoole source text. Its memory model is a map-backed
logical heap with generated safety assertions for null checks, allocation
checks, and array bounds checks. See
[`C0VC/StrataBoole/README.md`](C0VC/StrataBoole/README.md) for the backend
design.

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
directory.

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

- effectful procedure-call lowering
- callee-based framing
- allocation in loop conditions
- first-class array-of-struct element values outside field access
- strings
- `hastag`
- non-tail returns.
