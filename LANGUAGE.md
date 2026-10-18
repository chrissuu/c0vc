# C0/C1 Language Reference (Abridged)

This document notes the main quirks of the C0 language. Some parts are quoted explicitly from the original C0/C1 reference. We will also note the intentional design branches from the original C0/C1 languages here.

1.  "Structures are allocated in memory. Unlike the elements of other types, structures cannot be assigned to variables or passed as function arguments because they can have arbitrary size. Instead, we pass pointers to structs or arrays of structs."

2.  Postconditions and assigned parameters. When a function assigns one of its parameters, C0 tools differ on whether `//@ensures` sees the parameter's value on entry or at return. The StrataBoole backend rejects a postcondition that mentions an assigned parameter; copy the parameter into a local and assign the local instead.

3.  `\length` may only appear in contracts, as in C0.
