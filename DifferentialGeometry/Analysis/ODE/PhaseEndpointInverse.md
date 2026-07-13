# PhaseEndpointInverse

## Current state

- `freeDiagInv_pos` proves positivity of the reciprocal inverse norm of the free
  retained-endpoint equivalence on a nontrivial phase space.
- `exists_quant_inv` turns an `ApproximatesLinearOn` estimate on a positive closed
  ball into an `OpenPartialHomeomorph` with exactly that open-ball source and an
  explicit positive closed ball in its target.
- `inv_smooth_of_approx` proves the reusable same-branch regularity theorem for
  any supplied `OpenPartialHomeomorph` whose source and forward function agree
  with the quantitative construction. `quantInv_smooth` remains the wrapper
  for `ApproximatesLinearOn.toOpenPartialHomeomorph`. The proof bounds the derivative residual by
  the approximation constant, obtains derivative injectivity from the same
  strict inverse threshold, upgrades it to bijectivity in finite dimension, and
  applies `OpenPartialHomeomorph.contDiffAt_symm`.
- Focused verification and downstream consumption by the normal endpoint
  passed without local warnings or placeholders.

## Scope

This is a generic analysis-layer inverse theorem.  It contains no geometric
endpoint identification and does not prove the HCG moving inverse by itself.
The normal-phase consumer now supplies the required forward smoothness.  The
remaining frontier is transporting that exact branch into the HCG readout
layer, not inverse regularity.
