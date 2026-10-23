# Worklog

## GENERAL GOALS
1. The programmer should be able to read C0/C1 programs and emit a new Boole file translation
2. The programmer should be able to inline C0/C1 programs in Lean files and emit a Boole translation
3. The programmer should be able to inline C0/C1 programs in Lean files, then reason about the Boole program
4. Not sure how this would work in its entirety, but maybe the programmer can inline C0/C1 programs in Lean files, and then reason directly about the annotations, which translate back down to Boole (?) In other words, goals are lifted up to C0, proved under C0 semantics, and then projected back down to Boole.
5. Since there is no dedicated compiler for C0, it may be worthwhile emitting LLVM IR such that programs can be tested and ran.
6. One of the end goals may be: prove the translations hold! I.e., obligations/annotations proven to be true in Boole => these hold also in C0
    -  this means we can do pretty interesting things, no? We can make proving obligations easier by having our elaboration stage elaborate away unrelated proof material, which makes it easier for statements to be shown true/false in Boole, and the translation correctness theorem gives you Boole Correctness => Elaborated C0 correctness => C0 correctness for free

## WORKLOG
---
10/23: Per-field framing
    - One heap map per struct leaf field and per array element type, all
      indexed by (object, element). modifies and loop havocs are per field.
    - Spec functions take only the heap maps they read, closed over calls.
    - bigstruct.l4 now verifies in seconds (was a timeout).

---
10/23: Spec functions
    - Contracts can call pure functions. They become Boole functions over the
      heap maps: definitional for expression-form bodies and the standard
      search loop (forall / exists), uninterpreted otherwise.
    - Header @ensures are trusted (free); prototype contracts are renamed to
      the definition's parameter names.
    - Lexer treats @ as whitespace inside annotations; parse errors report a
      location and the failing declaration's own message.
    - TODO: allocating functions in contracts, recursive spec functions
      (needs termination), induction lemmas.

---
10/17: Boole pipeline end to end
    - Rewrote StrataBoole lowering around a single expression pass that keeps
      C0 evaluation order: calls become `call` statements with call-site
      precondition checks, checks under && / || / ?: are guarded, non-tail
      returns exit a labelled block, loop invariants are read from their C0
      position, locals get unique names, assigned parameters are copied.
    - Typechecker enforces the C0 rule that a function may not assign a
      variable occurring in its @ensures clauses.
    - New heap model: no alloc map, heap well-formedness as free specs,
      zero-initialized allocation, cells addressed by (object, element, field),
      `len` is the element count.
    - Integer models: exact bv32 (default) and checked unbounded ints.
      Division truncates, div/mod/shift checks in both.
    - `c0vc --verify` runs Strata and reports obligations at C0 source lines.
    - Frontend: string literals lex, loop invariants parse after the loop
      header, parser and typechecker keep source spans, prototype contracts
      are kept, `main` is optional for Boole.
    - tests/boole has golden verification tests.
    - TODO: calls in contracts (pure spec functions), finer framing.

---
8/5: Modifies and Nested Allocations
    - Finished up nested allocations path. See StrataBoole::Trans.lean
    - Finished the "Modifies" spec for StrataBoole
    - TODO: I'd like to go through panics/errors and homogeonize errors to one style

---
8/3: Structs 
    - Array of struct field accesses are properly lowered now, instead of having 
      the placeholder code.

    - Safe memory accesses are also lowered as assertions / proof obligations.

    - Added some additional fields to the booleKeywords array so that we don't get
      naming conflicts between StrataBoole keywords and vars / internal stuff. 
      TODO: Maybe we can consider throwing an error instead for vars that are named the
      same as keywords? (instead of renaming)

---
8/2: Structs Semantics
    - Added the translation module for TypedAst Struct to the the struct model of StrataBoole.

---
7/30: StrataBoole
    - Added StrataBoole as a proper dependency to this repo. Created an IR to 
      house it, and the respective translation modules.

    - TODO: need to implement the formal translation for contracts

    - Currently, it rejects non-tail returns, instead of emitting Boole.
      It seems quite annoying to have to work with tail returns, and translating
      an arbitrary C0/C1 program to tail return style might make it too verbose 
      especially for code with nested if statements...

---
7/13: Contracts
    - TODO: implement a flag for the compiler which will turn on dynamic contracts 
      when lowering to LLVM.

---
6/4: Memory 
    - AST:
        - lvalue definitions
        - struct definitions
    - parser should now have:
        - lvalue
        - struct handling
    - handle ambiguities in lexer 
    - lowering to tree (by tree IR, memory should be abstracted away)

---
5/..: Change compiler /project name to: c0vc (C0 verified compiler).