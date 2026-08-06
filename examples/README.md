# Examples

This directory contains small C0/C1 programs that document backend behavior.

## StrataBoole

- `strataboole/array_struct_fields.c0` shows the supported case for arrays of
  structs: selecting a field from an array element, such as `a[i].x`.
- `strataboole/array_struct_whole_value.c0` documents unsupported whole-struct
  value patterns. The unsupported lines are commented out because C0/C1 does
  not allow first-class struct values in assignments or function calls.

To emit Boole for a supported example:

```sh
lake exe c0vc --emit=boole examples/strataboole/array_struct_fields.c0
```

This writes `array_struct_fields.c0.boole.st` in the current working directory.
