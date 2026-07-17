# Operators.lean - scalar operator algebra

## 2026-06-23

Step C needed the finite-sum algebra behind the center-of-mass gradient
characterization. The reusable result belongs here, below the pointwise
`gradientFun` API, not in the HCG file.

What landed:

- `gradientFun_sum`: the gradient of a finite function sum is the finite sum of
  the gradients.
- `gradientFun_sum_smul`: the gradient of a finite weighted function sum is the
  weighted sum of the gradients.

The proof uses the native function-sum form `sum i in s, f i`, because
Mathlib's `MDifferentiableAt.sum` is stated in that form. Callers with
pointwise lambdas can bridge using `Finset.sum_apply`.

Verification status: focused Lean check and targeted module build passed. Axiom
print for `gradientFun_sum` and `gradientFun_sum_smul` is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by these
declarations. The targeted build replayed existing upstream warnings outside
this file.

## 2026-06-24

Added `gradientFun_eq_zero_of_isLocalMin`: at a local minimum of a differentiable
scalar function on a boundaryless manifold, the realized gradient vanishes.

This theorem belongs in the lower scalar-operator API because
`Comparison/CenterOfMass.lean` needs the first-order gradient fact but should
not import the Laplacian minimum-principle file. The proof is the chart-level
first-order part of the existing Laplacian minimum route, packaged directly for
`gradientFun`.

Verification status: focused Lean check and targeted module build passed.
Axiom print for `gradientFun_eq_zero_of_isLocalMin` is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by this
declaration.

Added `gradientFun_eq_of_flat`: if `(mfderiv f x).toLinearMap` is the
metric-flat covector of a tangent vector `v`, then the realized gradient is
`v`. This is the pure musical-map bridge needed by Step C so the remaining
distance-squared first-variation theorem can be stated as a covector identity,
not as a gradient identity.

Verification status: focused Lean check and targeted module build passed.
Axiom print for `gradientFun_eq_of_flat` is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by this
declaration.

## 2026-07-16

Added the intrinsic logarithm producers needed by the entropy potential lane:

- `gradientFun_log` proves the pointwise gradient chain rule at a positive
  value. Its proof follows the existing `gradientFun_rpow` scalar normal form:
  evaluate through `extDerivFun` and `fromTangentSpace`, then recover the
  tangent vector with metric-flat injectivity. This avoids asking the realized
  scalar tangent fiber to synthesize a ring instance.
- `laplacian_log` proves
  `Delta (log f) = f^-1 Delta f - (f^2)^-1 |grad f|^2` from differentiability,
  positivity, and the existing differentiability of `grad f`. It uses
  `divergence_smul`, the real-power derivative at exponent `-1`, and the exact
  `Real.rpow_two` bridge between real and natural powers.

No chart-selection, compactness, boundary, or new consumer-side convergence
assumption was added. Focused verification passed with no local `sorry`.

Accounting: both named producer theorems are complete (100%).  The downstream
`potential_pde` theorem is separately complete in `PotentialEvolution.lean`;
these producer proofs are not double-counted as completion of that consumer or
of the still-open W-monotonicity and noncollapsing endpoints.
