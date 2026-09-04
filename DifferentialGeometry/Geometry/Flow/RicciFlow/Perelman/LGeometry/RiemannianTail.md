# RiemannianTail

## Status

The first focused check stopped at the manifold instance binder because the
open `ENNReal` scope made bare `∞` parse as `ℝ≥0∞`.  The binder now uses the
notation-independent `((⊤ : ℕ∞) : WithTop ℕ∞)` type explicitly.  All reported
`M` and tangent-bundle errors were downstream of that first mismatch.

The second focused check reached the local `IsManifold.of_le` construction and
found the same overloaded `∞` in its smoothness grade and comparison target.
Both remaining occurrences now use `((⊤ : ℕ∞) : WithTop ℕ∞)`, while the
proof still states the intended `1 ≤` smoothness grade.

The third focused check is warning-free green after these notation-only
repairs.  The theorem body and public assumptions required no change.

The first named refresh did not reach this module because its dirty dependency
cone rebuilt `RadialSurjectivity.lean` and `Variation/JacobiField.lean`.
The latter was protected only by a stale claim; after exact owner/PID
verification it was reclaimed, minimally repaired, focused-check GREEN, and
exact-refresh GREEN (3707/3707).  `RadialSurjectivity.lean` and
`Exponential/JacobiVariation.lean` were then repaired and are warning-free
focused GREEN and exact-refresh GREEN (3803/3803 and 3822/3822).  The next
required volume-consumer refresh reached three further source-local blockers:
`SegmentDomain.lean`, `MinimalGeodesicNoConjugate.lean`, and
`SegmentDensity.lean`, followed by one stale `omit` binder in
`SegmentPolar.lean`.  Each dependency is now warning-free focused green and
exact-refresh green, as is the required Euclidean volume consumer.  The final
`RiemannianTail` exact refresh is green (3998/3998), and the unified P2 axiom
audit verifies `riem_gauss_tail` with only the standard three logical axioms.

## Native route

The theorem installs the metric instances through the native
`ContinuousRiemannianMetric -> RiemannianBundle -> EMetricSpace` chain, then
uses the supplied Riemannian completeness package.  It specializes
`segBall_vol_le_euclidean` to model curvature `q = 0`, rewrites
`hypRadVol_zero` as the degree-`n` Euclidean power, and supplies that intrinsic
ball-growth estimate to `Analysis.Measure.gauss_tail_of_ball`.  The final
statement is returned to the stable `riemannianEDistOf` interface.

The continuous metric is bound once and is also the source of the registered
Riemannian bundle, so the fiber norm and continuity structures do not arise
from parallel hand-built instances.

## Static review

- The instance order now matches the native tangent-metric route: continuous
  metric, its Riemannian bundle, extended metric space, completeness, then the
  finite-distance metric space.
- The `q = 0` Ricci specialization and `hypRadVol_zero` normalization follow the
  existing `segBall_vol_pow` rewrite exactly, including the positive-finrank
  cast needed for the inverse dimension factor.
- The metric-ball set is rewritten before applying the volume estimate; after
  the generic Gaussian theorem, both the exterior set and integrand are returned
  to `riemannianEDistOf`.  Thus the exported statement does not expose a locally
  chosen `MetricSpace` instance.
- Static inspection found no extra public declaration, unused proof hypothesis,
  import cycle, or measure/coercion mismatch.  Both focused failures were
  confined to the overloaded infinity notation, and the repaired file is
  warning-free focused green.

No Comparison declaration was changed and no new frontier hypothesis, class, or
notation was introduced.  The only public declaration in this file is
`riem_gauss_tail`.

## Scope and remaining frontier

This adapter covers only the complete, nonnegative-Ricci polynomial-volume step
and its resulting fixed-center exterior Gaussian integral bound.  It does not
prove the two-point reduced-length coercivity, uniform moving-center decay,
compact-test convergence, or no-mass-loss needed by the book12 Gaussian-
tightness argument.

`riem_gauss_tail` is 100% for its stated fixed-center complete-manifold
Gaussian-tail bound, and its dedicated machinery is 100%.  The book12
moving-center Gaussian-tightness endpoint remains unstated and therefore 0%;
its dedicated native infrastructure is roughly 30--40%.  Across the full P0--P9
program, checked/source-written infrastructure remains approximately 15--25%,
while the final Poincare theorem is still 0%.
