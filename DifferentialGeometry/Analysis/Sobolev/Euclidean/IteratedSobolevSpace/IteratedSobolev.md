# Iterated Sobolev space

## `MemWkp.two_of_wit`

- Route: unfold the order-two `MemWkp` recursion, compare the supplied weak
  gradient with the canonical chosen witness by weak-gradient uniqueness, and
  transport each component's `W^{1,2}` membership across that a.e. equality.
  The zero-dimensional case is discharged directly, so no unnecessary
  `NeZero d` assumption is added to the public theorem.
- Verification: focused verification passed without warnings.
