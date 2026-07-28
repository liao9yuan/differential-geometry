# NonautonomousL2

## Result

This module replaces the false uniform-in-time assumption on the first-order
coefficient by its natural `L2_t` operator norm.  The zero-initial Duhamel
representative supplies the bounded `H^(a+1)` path.

The current source defines the first-order arm `a1L2Term`, proves exact
subtraction and its norm bound, and combines it with the existing bounded
top-order arm in `nonautL2Map`.

## Smallness constant

The mixed map has candidate Lipschitz constant

`C2 * (1 + T) + 2 * sqrt (1 + T) * ||A1||_L2`.

This can become small because the first-order coefficient is measured on the
shrinking time interval; no `L-infinity_t H^(a+1)` coefficient hypothesis is
introduced.

The map estimate, `nonautL2_contract`, and `nonautL2_forced` passed focused
verification.  The latter two declarations supply the Banach fixed-point and
affine-forcing wiring.  They are generic analytic machinery; they do not
construct the rough metric-dependent Ricci--DeTurck coefficient family.
