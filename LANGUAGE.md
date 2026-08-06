# C0/C1 Language Reference (Abridged)

This document notes the main quirks of the C0 language. Some parts are quoted explicitly from the original C0/C1 reference. We will also note the intentional design branches from the original C0/C1 languages here.

1.  "Structures are allocated in memory. Unlike the elements of other types, structures cannot be assigned to variables or passed as function arguments because they can have arbitrary size. Instead, we pass pointers to structs or arrays of structs."
