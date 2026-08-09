# LowRegRhsOne

## Source result

`rhs1_h2_of_conv` is the canonical assembly theorem.  It takes fixed
nonnegative constants `C2`, `C3` and the exact convex-path `H2`/`H3` jet
certificates, then combines the concrete dimension-three affine bounds for
`linearizedRicciConnDiffOrder1CoeffField` and `deTurckLieArm1Coeff` through
`rhs1_h2_of_aux`.  The endpoint spectral `H2` radius `R` remains independent
from the endpoint spectral `H3` radius `A`, and the conclusion has the exact
tame form `(B0 R + B1 R * A)^2`.

`rhs1_h2_tame` is the compatibility wrapper: it chooses `convex_h2_jet` and
`convex_h3_jet` for the current metric and delegates to `rhs1_h2_of_conv`.
This split lets a class-first producer supply uniform path certificates
without changing the existing public endpoint.  No fourth metric derivative
or high-Sobolev input enters.  The final two-arm addition is bounded by the
explicit affine envelope `4 * Ric + 2 * Lie`.

`rhs1_path_tame` applies `path_jetL2_le` to transfer this uniform
pointwise-in-path estimate unchanged to the through-second-covariant-
derivative `L2` jet of `rhsLow1PathIntegral`.  No auxiliary analytic
hypothesis, replacement producer, axiom, `sorry`, or `admit` was introduced.

## Verification and frontier

The core/wrapper extraction was source-only by instruction.  Verification is
pending and is not counted as passed until a focused check succeeds.

Together with `rhs0_h1_tame`, this supplies the two affine lower-path
coefficient estimates needed by `rem_h1_of_jets` at source level.  The next
producer is the consumer-shaped smooth-core three-arm remainder/nonlinearity
estimate, followed by dense extension and the maximal-regularity solver.
`ricci_flow_unif_existence` remains theorem-level 0% until its exact statement
is proved and verified.
