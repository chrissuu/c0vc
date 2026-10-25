# StrataBoole Backend

This directory contains the C0VC backend that lowers typed C0/C1 programs into a
small Boole-oriented IR, prints StrataBoole source text, and optionally runs the
Strata verifier on it.

- `IR.lean` defines the Boole-facing AST, including the labels that tie each
  proof obligation back to a C0 source location.
- `Struct.lean` computes the flattened field layout of C0 structs.
- `Trans.lean` lowers the typed C0 AST into the IR.
- `Codegen.lean` renders the IR as Boole text.
- `DDM.lean` parses Boole text into a `StrataDDM.Program`.
- `Verify.lean` runs the Strata verifier and maps results back to C0.

```sh
c0vc --emit=boole prog.c0          # writes prog.c0.boole.st
c0vc --verify prog.c0              # verifies and reports failed obligations
c0vc --verify --int-model=checked prog.c0
```

`--verify` needs an SMT solver on `PATH` (`z3` by default, `--solver=cvc5` to
switch). Output looks like:

```text
prog.c0:12:10: error: array index may be out of bounds [bounds_L12C10]
prog.c0: 7 of 8 proof obligations verified
```

The exit code is 0 when every obligation is proved, 1 otherwise. A result that
the solver reports as unknown, typically a loop invariant or quantifier it could
not decide, is printed with "(not proven: solver returned unknown)".

With z3, `--verify` enables model-based quantifier instantiation
(`smt.mbqi=true`). Boole drops quantifier triggers, and without it z3 cannot use
the quantified heap facts and spec-function bodies.

## Lowering

Expressions are lowered to a list of prerequisites followed by a pure Boole
expression. Prerequisites are statements that must run first (procedure calls,
allocations, havocs for string literals) and proof obligations (C0 runtime
checks). They appear in C0's left-to-right evaluation order; when a later
operand contains a call, earlier operands that read memory are saved in
temporaries first.

`&&`, `||` and `!` are elaborated into `?:`. Obligations inside the branches of
`?:` are guarded by the branch condition, so `p != NULL && p->x > 0` produces
the check `p != 0 ==> p != 0`, not an unconditional null check. Branches that
contain calls or allocations are lowered to `if` statements.

Each runtime check becomes

```boole
assert [null_L5C7]: (p != 0);
assume (p != 0);
```

C0 aborts when a check fails, so execution only continues when it holds.

### Statements

- Locals get unique Boole names. Names that clash with Boole keywords, the heap
  model, or procedure names are renamed (`len` becomes `len_1`).
- Boole parameters are immutable. A parameter the body assigns is copied into a
  local at entry. C0 forbids assigning to a variable that occurs in an
  `@ensures` clause, so such a parameter never appears in a postcondition.
- A non-tail `return` assigns `__result` and exits the labelled `__body` block.
- Loop invariants are written where C0 puts them,
  `while (c) //@loop_invariant I; { ... }`, and the same for `for`.
  A condition without prerequisites becomes `while (c) invariant I { ... }`. A
  condition with checks or calls is evaluated at the top of the body:
  `__loop: { while (true) invariant I { pre; if (!c) { exit __loop; } ... } }`,
  which matches C0's order of checking the invariant and then the condition.
- `assert(e)`, `//@assert e` and `error(msg)` are checks; `error` checks `false`.
- Calls become `call` statements. The callee's preconditions are asserted at
  the call site, so a failure points at the call.

### Contracts

`//@requires` and `//@ensures` become `requires` and `ensures` clauses; a
parameter in a postcondition means its value on entry, which is also its value
on return because the body may not assign it. Runtime
checks inside a contract, such as the bounds check in `//@requires A[0] > 0`,
become extra clauses before it. Contracts on prototypes and header declarations
are merged into the function's contract, with the prototype's parameter names
renamed to the definition's. A header function's `@ensures` is trusted (it is a
free `ensures`), since there is no body to check it against. Allocation and
string literals are rejected inside contracts.

### Spec functions

Contracts can call pure functions: functions that neither write memory nor
allocate, directly or through calls. Each pure function that a contract uses
gets a Boole function that takes the heap maps as extra arguments,

```boole
function is_sorted_fn(__len : ..., __aInt : ..., A : int, lo : bv W32, hi : bv W32) : bool { ... }
```

and a call in a contract applies it to the current heap. The function only
takes the heap maps its C0 body reads, directly or through calls, so its value
survives writes to other maps. The callee's
preconditions become obligations at the contract's call site. The function's
procedure gets the free postcondition `\result == is_sorted_fn(heap, args)`, so
the result of a call in code agrees with the same call in a contract.

The function body is
- the body itself when it is in expression form: returns, `if`/`else`, local
  declarations and assignments;
- a quantifier for the standard search loop. `for (int i = lo; i < hi; i++)
  if (c) return false; return true;` becomes `forall i :: lo <= i < hi ==> !c`,
  and the dual returning `true` from the loop becomes `exists`. Both `<` and `<=`
  bounds are recognized, and loop invariants are ignored;
- uninterpreted otherwise. Recursive functions stay uninterpreted: a
  definitional equation for a function that does not terminate could be
  inconsistent, and termination is not checked.

## Integers

`--int-model` selects how C0 `int` and `char` are represented:

- `bv32` (default): 32-bit bitvectors. `+`, `-` and `*` wrap exactly as in C0,
  `/` and `%` truncate toward zero, `>>` is arithmetic. A program verified in
  this mode is verified under the real C0 semantics.
- `checked`: unbounded integers. Every `+`, `-` and `*` in code gets an overflow
  obligation, so a verified program never overflows and behaves the same as
  under `bv32`. Contracts are read over mathematical integers. Division is
  encoded as truncating division; bitwise operators go through `as_bv32`.

In both modes `/` and `%` check for a zero divisor and for `INT_MIN / -1`, and
shifts check that the shift amount is in `[0, 32)`.

## Memory Model

The heap is split into one map per kind of memory location (Burstall-Bornat):

```boole
var nextRef : int;
var len : Map int C0Int;
var aInt : Map int (Map C0Int C0Int);    // and aBool, aRef, aStr
var h_node_next : Map int (Map C0Int int);   // one map per struct leaf field
var zeroInt : Map C0Int C0Int;            // and zeroBool, zeroRef
```

`C0Int` is `bv W32` or `int` depending on the int model. `aStr` and the opaque
type `C0String` are added when the program uses strings.

References are object ids: `0` is NULL and the allocated objects are exactly
`0 < r < nextRef`. C0 has no pointer arithmetic, casts or deallocation, so a
reference held by a C0 program is always NULL or allocated, and an object is
only ever accessed at its own type. Cells are addressed by map, object and
element index:

```text
*p          => aT[p][0]
a[i]        => aT[a][i]
p->f        => h_S_f[p][0]
a[i].f      => h_S_f[a][i]
p->in.a     => h_S_in_a[p][0]      (nested value structs are flattened)
\length(a)  => len[a]
```

`aT` is chosen by the element type: `aInt` for `int` and `char`, `aBool` for
`bool`, `aRef` for pointers and arrays, `aStr` for strings. Each scalar leaf
field of each struct `S` has its own map `h_S_path`. The default array is NULL
with length 0.

Checks: dereferences and field accesses through pointers check `p != 0`; array
accesses check `0 <= i && i < len[a]` (this also rejects the NULL array).

Allocation takes a fresh id and zero-initializes the maps of its cells:

```boole
__alloc := nextRef;
nextRef := (nextRef + 1);
len[__alloc] := n;
h_node_val[__alloc] := zeroInt;
h_node_next[__alloc] := zeroRef;
```

### Well-formedness and framing

Every procedure assumes, through free `requires`, that the heap is well formed:
`nextRef > 0`, `len[0] == 0`, lengths of allocated objects are non-negative,
references stored in reference-valued maps are NULL or allocated, and the zero
rows are zero. Reference parameters are NULL or allocated. Procedures that
change the heap re-establish these facts through free `ensures`, together with
`nextRef >= old nextRef`. Loops that touch the heap assume them again at the
top of the body and after the loop. These are assumptions rather than
obligations because they hold in every reachable C0 state.

`modifies` clauses are computed per procedure and closed over the call graph.
Since each field has its own map, a callee that writes `p->count` changes only
`h_node_count`: the caller keeps what it knows about every other field, every
array, and every spec function that does not read `count`. Within one map,
framing is still coarse: writing `p->count` forgets `q->count` for every `q`,
because C0 contracts cannot say which objects a function changes.

## Current Limitations

- Contracts cannot call functions that allocate, such as one that returns a new
  struct, because they cannot be Boole functions.
- Spec functions that are recursive or use loops other than the search loop
  are uninterpreted, so their meaning is only available through the procedure's
  link to calls in code.
- SMT solvers do not do induction: from `is_sorted(A, 0, n)` they get
  `A[i] <= A[i+1]` for each `i`, but not `A[0] <= A[n-1]`.
- Framing within one map is per map, not per object (see above).
- `\hastag` and C1 `void*` tags are not supported.
- Strings are opaque: string literals are havocked values and string library
  functions are uninterpreted.
- Long runs of straight-line writes into the same map (for example hundreds of
  writes to one array) make Strata's symbolic execution slow.
