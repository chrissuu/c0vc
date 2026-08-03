

GENERAL GOALS::
1. The programmer should be able to read C0/C1 programs and emit a new Boole file translation
2. The programmer should be able to inline C0/C1 programs in Lean files and emit a Boole translation
3. The programmer should be able to inline C0/C1 programs in Lean files, then reason about the Boole program
4. Not sure how this would work in its entirety, but maybe the programmer can inline C0/C1 programs in Lean files, and then reason directly about the annotations, which translate back down to Boole (?) In other words, goals are lifted up to C0, proved under C0 semantics, and then projected back down to Boole.
5. Since there is no dedicated compiler for C0, it may be worthwhile emitting LLVM IR such that programs can be tested and ran.
6. One of the end goals may be: prove the translations hold! I.e., obligations/annotations proven to be true in Boole => these hold also in C0
    -  this means we can do pretty interesting things, no? We can make proving obligations easier by having our elaboration stage elaborate away unrelated proof material, which makes it easier for statements to be shown true/false in Boole, and the translation correctness theorem gives you Boole Correctness => Elaborated C0 correctness => C0 correctness for free

8/2: Structs Semantics
    - Added the translation module for TypedAst Struct to the the struct model of StrataBoole.

7/30: StrataBoole
    - Added StrataBoole as a proper dependency to this repo. Created an IR to house it, and the
      respective translation modules.

    - TODO: need to implement the formal translation for contracts

    - Currently, it rejects non-tail returns, instead of emitting Boole.
      It seems quite annoying to have to work with tail returns, and translating
      an arbitrary C0/C1 program to tail return style might make it too verbose 
      especially for code with nested if statements...
     

7/13: Contracts
    - TODO: implement a flag for the compiler which will turn on dynamic contracts 
      when lowering to LLVM.

6/4: Memory 
    - AST:
        - lvalue definitions
        - struct definitions
    - parser should now have:
        - lvalue
        - struct handling
    - handle ambiguities in lexer 
    - lowering to tree (by tree IR, memory should be abstracted away)

5/..: Change compiler /project name to: c0vc (C0 verified compiler).