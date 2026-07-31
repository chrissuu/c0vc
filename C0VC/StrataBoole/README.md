# C0 Memory in Boole

Boole does not give us C0 memory semantics directly. But, it gives us the pieces we
need to build one: maps, globals, assertions, specifications, loop invariants,
and modifies clauses. The StrataBoole backend therefore lowers C0 memory into a
map-backed logical heap.

## Heap Model

The intended Boole prelude is:

```boole
type Ref := int;
type HeapInt := Map int (Map int int);
type HeapBool := Map int (Map int bool);
type HeapRef := Map int (Map int int);

var nextRef : int;
var alloc : Map int bool;
var len : Map int int;
var hInt : HeapInt;
var hBool : HeapBool;
var hRef : HeapRef;
```

References are abstract object IDs. Reference `0` represents `NULL`.
`alloc[p]` records whether object `p` is allocated. `len[p]` records the length
of array-like allocations, and is `1` for singleton allocations. Heap maps store
object slots by type:

- `hInt[p][i]` stores an integer slot.
- `hBool[p][i]` stores a boolean slot.
- `hRef[p][i]` stores a reference slot.

C0 has no pointer arithmetic, so this object-and-slot model is enough for the
source language we need to lower. It also keeps aliasing explicit: two C0
references alias exactly when they are equal Boole `Ref` values.

## Lowering

Basic memory expressions lower as follows:

```text
NULL        => 0
\length(a)  => len[a]
*p          => hT[p][0]
a[i]        => hT[a][i]
s.f         => hT[s][fieldIndex(S, f)]
p->f        => hT[p][fieldIndex(S, f)]
```

Here `hT` means the heap map selected from the accessed C0 type:

```text
int / char fields and elements => hInt
bool fields and elements       => hBool
pointer / array values         => hRef
```

Writes use the same slot selection on the left-hand side:

```text
*p = v    => hT[p][0] := v
a[i] = v  => hT[a][i] := v
s.f = v   => hT[s][fieldIndex(S, f)] := v
p->f = v  => hT[p][fieldIndex(S, f)] := v
```

Allocation introduces a fresh object ID:

```text
alloc(T):
  p := nextRef;
  nextRef := nextRef + 1;
  alloc[p] := true;
  len[p] := 1;

alloc_array(T, n):
  assert n >= 0;
  p := nextRef;
  nextRef := nextRef + 1;
  alloc[p] := true;
  len[p] := n;
```

## Safety Obligations

C0 memory safety checks become Boole assertions before the operation that needs
them:

```boole
assert p != 0;
assert alloc[p];
```

Array access additionally checks bounds:

```boole
assert 0 <= i;
assert i < len[a];
```

These assertions are verification obligations in Boole. They correspond to the
runtime checks emitted by the LLVM backend.
