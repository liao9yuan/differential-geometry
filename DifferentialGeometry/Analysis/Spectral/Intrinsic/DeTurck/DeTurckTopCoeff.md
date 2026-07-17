# DeTurckTopCoeff

## Role

This module is the canonical home of `deTurckPhiMetTotal`, the complete
second-order coefficient for the combined Ricci--DeTurck path derivative.  It
was moved out of `DeTurckRemainderTameLipschitz.lean` so low-regularity work can
use the cancellation without importing or extending that oversized assembly
file.

## Current state

- `deTurckPhiMetTotal` combines the DeTurck principal coefficient, the trace
  Hessian coefficient, and both Ricci principal coefficients.
- `phi_realized_eq` exposes its exact value along `realizedFam` as the DeTurck
  top coefficient minus the two Lichnerowicz-form Ricci coefficients.
- The statement has no high-order metric assumption; it is an algebraic
  principal-part identity.

The extracted module and its named target build both pass without local
warnings or `sorry`s.
