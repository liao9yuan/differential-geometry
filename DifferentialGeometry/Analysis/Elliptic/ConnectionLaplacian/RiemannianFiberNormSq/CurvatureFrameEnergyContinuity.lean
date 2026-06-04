import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.ChartRiemannDataUniformBound
import Mathlib.Topology.Order.Compact

/-!
# Continuous frame-energy bound for the tensor curvature operator

For a smooth Riemannian metric `g` on a *closed* manifold `M` and any covariant rank `t`,
this file posits the genuinely-deep DG/analysis primitive underlying the *continuous*
proportional curvature-operator fibre bound: a **continuous** nonnegative envelope
`Ccurv : M → ℝ` bounding, at every base point `x` and for any `g`-orthonormal frame `e` of
`T_x M`, the **frame energy** of the bundled tensor curvature operator
`R_x = riemannOp (tensorCov g 0 t) x` acting on a `(0, t)`-tensor `T`:

```
∑_{i, j} riemannianFiberNormSq g 0 t x (R_x(e_i, e_j) T) ≤ Ccurv x · riemannianFiberNormSq g 0 t x T.
```

The frame energy `∑_{i, j} ‖R_x(e_i, e_j) T‖²_g` is the squared Hilbert–Schmidt norm of the
linear map `T ↦ R_x(·, ·) T` measured against the `g`-orthonormal frame pair `(e_i, e_j)`; it is
**frame-independent** (a `g`-orthonormal change of frame is an orthogonal substitution under
which the double sum is invariant), so its least proportional bound is the intrinsic
curvature-operator Hilbert–Schmidt norm squared `‖R_x‖²_HS`, a base-point function of `g` alone.

This is the sole genuinely-irreducible analytic content (continuity of the curvature-operator
Hilbert–Schmidt norm) feeding
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`; the `(v, w)`-factor
`riemannianFiberNormSq_riemannOp_tensorCovS_vw_factor_le` and the uniformisation over the compact
`M` are proved on top of it.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Posited continuous frame-energy bound for the tensor curvature operator.** For a smooth
Riemannian metric `g` on a closed manifold `M` and any covariant rank `t`, there is a
*continuous* nonnegative function `Ccurv : M → ℝ` such that, at every base point `x` and for any
`g`-orthonormal frame `e` of `T_x M` representing `riemannianFiberNormSq` as its frame double
sum, the curvature **frame energy** is bounded proportionally to the source fibre norm:

```
∑_{i, j} riemannianFiberNormSq g 0 t x (R_x(e_i, e_j) T)
  ≤ Ccurv x · riemannianFiberNormSq g 0 t x T,
```

where `R = riemannOp (tensorCov g 0 t)` is the bundled tensor curvature operator and the frame
`e` (with size `n`) satisfies `g`-orthonormality `g.inner x (e i) (e j) = δ_{ij}` and the
`riemannianFiberNormSq` frame representation `hrepr`.

**Why this is TRUE.** Fix `x`. The frame energy `∑_{i, j} ‖R_x(e_i, e_j) T‖²_g` is the squared
Hilbert–Schmidt norm of the bilinear curvature action `(u, u') ↦ R_x(u, u') T` evaluated against
the `g`-orthonormal frame pair `(e_i, e_j)`; under a `g`-orthonormal change of frame the double
sum transforms by an orthogonal substitution in each tangent slot and is therefore **invariant**,
so the least proportional constant for the displayed bound equals the intrinsic
curvature-operator Hilbert–Schmidt norm squared `‖R_x‖²_HS`, a function of the base point `x`
through `g` alone (independent of which orthonormal frame is chosen). This intrinsic
curvature-operator norm is **continuous** in `x` because the curvature operator is assembled from
the smooth metric `g` and the smooth Levi-Civita Riemann tensor: in any chart at `α` the
chart-coordinate Riemann coefficients `chartRiemannTensor g α i j k l (ϕ_α b)` are `C^∞`
(polynomial in the chart Christoffel symbols and their first partials) and *uniformly bounded* on
the compact chart-`α` partition-of-unity support by `exists_chartRiemannData_uniform_bound_compact`;
the intrinsic fibre norm of the curvature action is controlled, through the forward chart-frame
Gram Rayleigh route and its reverse companion, by these bounded smooth chart-data, yielding a
continuous (indeed locally Lipschitz) envelope `Ccurv` on the finitely-many compact chart supports
that cover `M`, patched to a global continuous function by the partition of unity. This is the
chart-locality-free route (no `HasLocallyConstantChartAt`, no chart-trivialisation operator-norm
scalar); the only chart objects are the bounded chart Christoffel / Riemann data and the
positive-definite chart Gram matrix.

**Non-vacuity.** A degenerate witness `Ccurv ≡ 0` is rejected on any non-flat manifold: at a point
`x` where the curvature operator is nonzero there is a `g`-orthonormal frame pair `(e_i, e_j)` and
a tensor `T` with `R_x(e_i, e_j) T ≠ 0`, hence the frame energy
`∑_{i, j} riemannianFiberNormSq g 0 t x (R_x(e_i, e_j) T) > 0` (a sum of squared fibre norms with a
strictly positive term) while the right-hand side `0 · riemannianFiberNormSq g 0 t x T = 0`,
contradicting the bound. So the envelope must carry the genuine curvature magnitude — it cannot be
the trivial zero function. -/
theorem exists_continuous_riemannOp_tensorCovS_frameEnergy_bound
    (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ Ccurv : M → ℝ, Continuous Ccurv ∧ (∀ x : M, 0 ≤ Ccurv x) ∧
      ∀ (x : M) {n : ℕ} (e : Fin n → TangentSpace I x),
        (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) →
        (∀ S : TensorRSSpace 0 t I x,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x S =
            ∑ K : Fin 0 → Fin n, ∑ J : Fin t → Fin n,
              fiberNormSqSummand (I := I) (M := M) g x 0 t S n e K J) →
        ∀ T : TensorRSSpace 0 t I x,
          (∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 t x
                (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T)) ≤
            Ccurv x * riemannianFiberNormSq (I := I) (M := M) g 0 t x T := by
  sorry

end Connection
end Integral
end DifferentialGeometry

end
