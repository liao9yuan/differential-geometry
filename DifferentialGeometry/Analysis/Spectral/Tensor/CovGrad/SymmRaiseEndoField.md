# SymmRaiseEndoField

## Role

This module is the public fixed-background bridge from a smooth covariant
two-tensor to the tangent endomorphism obtained by raising one slot.  It avoids
representing the low-regularity principal coefficient by a passenger-slot
extension, which acts in the wrong rank-four slot.

## Status

The public field and its smoothness theorem are complete.  The intended
consumer is `PrincipalPerturbH2.lean`, where the rank-four coefficient is a
direct leading-slot `slotInsertEndoCc`.

Focused verification and the named producer refresh passed.  The module
contains no `sorry`.
