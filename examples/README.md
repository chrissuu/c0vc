# Examples

This directory contains small C0/C1 programs that document backend behavior.

## StrataBoole

- `strataboole/array_struct_fields.c0` shows the supported case for arrays of
  structs: selecting a field from an array element, such as `a[i].x`.
- `strataboole/array_struct_whole_value.c0` documents unsupported whole-struct
  value patterns. The unsupported lines are commented out because C0/C1 does
  not allow first-class struct values in assignments or function calls.
- `strataboole/ddm_from_typed_ast.lean` shows the current direct Lean bridge
  from a typed C0 AST to `StrataDDM.Program`.
- `strataboole/c0_inline_embedding.lean` shows the inline Lean syntax:
  `#c0 ... #end`.

To emit Boole for a supported example:

```sh
lake exe c0vc --emit=boole examples/strataboole/array_struct_fields.c0
```

This writes `array_struct_fields.c0.boole.st` in the current working directory.

To verify it (needs `z3` on `PATH`):

```sh
lake exe c0vc --verify examples/strataboole/array_struct_fields.c0
```

To check the DDM bridge example:

```sh
lake env lean examples/strataboole/ddm_from_typed_ast.lean
```

To check inline C0 embedding:

```sh
lake env lean examples/strataboole/c0_inline_embedding.lean
```
