# NormalPhaseInverse

## Current state

- `exists_normal_q` chooses one positive phase radius satisfying the common
  normal-box bound, the acceleration fence, and the strict inverse threshold.
- `exists_normal_inv` combines that choice with `exists_normalFlow` and
  `PhaseFlow.exists_quant_inv`.  It exports the exact trajectory equation,
  phase-box confinement, the quantitative model inverse branch, and a positive
  closed target ball.
- Focused verification passed without warnings or placeholders.

The intrinsic moving-inverse theorem and `StepB1RawInput` producer remain
unstated and therefore 0%.  This file is dedicated model-side machinery only.

## Frontier

Cross-model geodesic naturality and endpoint identification are now closed in
`PullbackCross.lean`, `NormalMetricLocal.lean`, `IntrinsicExp.lean`, and
`NormalPhaseEndpoint.lean`.  In particular, `exists_normal_diag` packages the
quantitative branch together with its exact `diagExp` commutative square, and
`normal_inv_eq` proves compatibility with the existing `diagExpInv` under the
concrete branch-domain and `expDiffeoRadius` hypotheses.

The next target is to prove those domain/smallness hypotheses uniformly on the
selected phase ball, then transport the explicit target ball into the existing
readout domain.  See `NormalPhaseEndpoint.md`; do not restart the naturality
audit or expose a second consumer-facing inverse.
