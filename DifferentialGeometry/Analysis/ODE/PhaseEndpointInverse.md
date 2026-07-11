# PhaseEndpointInverse

## Current state

- `freeDiagInv_pos` proves positivity of the reciprocal inverse norm of the free
  retained-endpoint equivalence on a nontrivial phase space.
- `exists_quant_inv` turns an `ApproximatesLinearOn` estimate on a positive closed
  ball into an `OpenPartialHomeomorph` with exactly that open-ball source and an
  explicit positive closed ball in its target.
- Focused verification and the targeted module build passed without local
  warnings or placeholders.

## Scope

This is a generic analysis-layer inverse theorem.  It contains no geometric
endpoint identification and does not prove the HCG moving inverse by itself.

