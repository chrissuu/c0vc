# StrataBoole Backend

This directory contains the C0VC backend that lowers typed C0/C1 programs into a
small Boole-oriented IR and then prints StrataBoole source text.

The backend is intentionally split into a few small layers:

- `IR.lean` defines the Boole-facing AST used by this backend.
- `Struct.lean` computes the flattened layout used for C0 structs.
- `Trans.lean` lowers the typed C0 AST into the Boole-facing IR.
- `Codegen.lean` renders that IR as Boole text.

`--emit=boole` is wired through `Top.lean` and emits a `.boole.st` file.

## Logical Heap Model

Boole does not provide C0 memory semantics directly. Instead, this backend
models memory with global maps and emits proof obligations as Boole assertions.

The generated heap prelude is:

```boole
program Boole;

type Ref := int;
type HeapInt := Map Ref (Map int int);
type HeapBool := Map Ref (Map int bool);
type HeapRef := Map Ref (Map int Ref);

var nextRef : Ref;
var alloc : Map int bool;
var len : Map int int;
var hInt : HeapInt;
var hBool : HeapBool;
var hRef : HeapRef;
```

References are abstract object IDs. `0` is `NULL`. `alloc[p]` records whether an
object is allocated, and `len[p]` records the logical object length. Singleton
allocations have length `1`; array allocations have the requested length, or the
flattened slot length for arrays of structs.

Heap contents are split by value type:

- `hInt[p][i]` stores `int` and `char` slots.
- `hBool[p][i]` stores `bool` slots.
- `hRef[p][i]` stores pointer, array, null, and struct-reference slots.

This typed-heap split is necessary because Boole maps are monomorphic: one map
cannot store both `int` and `bool` values. C0 has no pointer arithmetic, so an
object ID plus an integer slot is enough to model the memory accesses this
backend lowers.

## Memory Lowering

Memory reads lower to heap lookups:

```text
NULL       => 0
\length(a) => len[a]
*p         => hT[p][0]
a[i]       => hT[a][i]
p->f       => hT[p][fieldIndex(S, f)]
```

`hT` is selected from the accessed C0 type: `hInt` for integer-like values,
`hBool` for booleans, and `hRef` for references.

Writes use the same address calculation on the left-hand side:

```text
*p = v    => hT[p][0] := v
a[i] = v  => hT[a][i] := v
p->f = v  => hT[p][fieldIndex(S, f)] := v
```

Allocations are statement-level effects. Allocation expressions are hoisted into
fresh temporaries before expression translation:

```text
alloc(T):
  assert nextRef != 0;
  assert alloc[nextRef] == false;
  tmp := nextRef;
  alloc[tmp] := true;
  len[tmp] := width(T);
  nextRef := nextRef + 1;

alloc_array(T, n):
  assert n >= 0;
  assert nextRef != 0;
  assert alloc[nextRef] == false;
  tmp := nextRef;
  alloc[tmp] := true;
  len[tmp] := n * width(T);
  nextRef := nextRef + 1;
```

For non-struct element types, `width(T)` is `1`. For struct values, it is the
number of flattened leaf fields.

## Structs

Boole has no direct C0 struct value model in this backend. Structs are laid out
as flattened slots inside the object that stores them.

For example:

```c
struct S {
  int x;
  bool y;
};
```

An allocated `struct S* p` uses one object ID, but its fields live in different
typed heaps:

```text
p->x => hInt[p][0]
p->y => hBool[p][1]
```

Nested value structs are flattened recursively. Arrays of structs use the same
layout with a per-element stride:

```text
a[i].f => hT[a][i * width(S) + fieldIndex(S, f)]
```

Whole-struct assignment is not lowered because C0/C1 does not define assigning
struct values directly. The backend expects code to pass and mutate structs
through pointers or arrays.

## Safety Obligations

Memory safety checks become Boole assertions immediately before the operation
that depends on them:

```boole
assert p != 0;
assert alloc[p];
```

Array access additionally emits bounds checks:

```boole
assert 0 <= i;
assert i < len[a];
```

These assertions are verification obligations. They correspond to the runtime
checks the executable backend would need to perform.

## Modifies Clauses

The translator computes a conservative `modifies` clause for each lowered
procedure body. Heap writes add the touched heap global, and allocation adds
`alloc`, `len`, and `nextRef`.

For example, a procedure that writes `p->x` may get:

```boole
spec {
  modifies hInt;
}
```

A procedure that allocates may get:

```boole
spec {
  modifies alloc, len, nextRef;
}
```

This matters because Boole uses modifies clauses to frame procedure effects:
globals not listed in `modifies` are assumed unchanged by the procedure.

## Current Limitations

- Procedure calls are still represented as expression calls; effectful call
  lowering and callee-based framing are not complete.
- Allocation in `while` conditions is rejected. Conditions are evaluated before
  the loop and after each iteration, so allocation there needs repeated hoisting
  semantics rather than a one-time prefix.
- Allocation inside loop invariants is rejected.
- Whole array-of-struct values are rejected unless immediately used as a field
  access base.
- Strings and `hastag` expressions are not supported.
- Non-tail returns are rejected.
