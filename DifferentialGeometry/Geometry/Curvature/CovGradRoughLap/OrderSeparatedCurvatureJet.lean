import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.GenuineBracketSectionSplit
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm

/-!
# The order-`m` order-separated moving-frame curvature-jet field decomposition

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` this file isolates the
deepest **order-`m` order-separated section-field split** of the `m`-fold iterated covariant
gradient of the rank-generic order-`2` commutator defect

```
Curv T := Δ_∇(∇T) − ∇(Δ_∇ T)
```

(`pointwiseTensorCurv g s T`, a `(0, s + 1)`-tensor field). It is the genuine order-`m` lift of the
`m = 0` section-field split `exists_pointwiseTensorCurv_orderSeparated_field`
(`Geometry/Curvature/CovGradRoughLap/PointwiseTensorCurvL2Bound.lean`): applying `∇^m` to the
order-separated field split of `Curv T` and re-Leibniz-ing the curvature contractions, the iterated
Ricci identity (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`) cancels the top-order
`∇^{m + 3}T` terms, leaving — at every rank `s`, gradient order `m`, smooth compactly-supported
`(0, s)`-tensor `T` and point `x` — three fields `Gcurv, GcurvDeriv, Grem` summing to
`∇^m(Curv T)(x)` with the three order-separated proportional fibre bounds: the differentiated-Riemann
jet `Gcurv` bounded by `∑_{i < m + 1} rfns(∇^{i + 1}T)` (orders `1 … m + 1`), the iterated
differentiated-curvature jet `GcurvDeriv` by `∑_{i < m + 1} rfns(∇^i T)` (orders `0 … m`), and the
moving-frame remainder `Grem` by `rfns(∇^{m + 2}T)` (the single top order).

This is the strictly-upstream curvature primitive that the assembly-ready order-`m` two-term split
`exists_iteratedCovGrad_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound`
(`Geometry/Curvature/CovGradRoughLap/PointwiseTensorCurvL2Bound.lean`) is *proved* on top of, by
merging the two genuine jets `Ggen := Gcurv + GcurvDeriv` through the two-term fibre subadditivity
`riemannianFiberNormSq_add_le`, dominating both order-separated sub-sums by the full low sum
`∑_{i < m + 2} rfns(∇^i T)` via `Finset.sum_le_sum_of_subset_of_nonneg` and the index shift
`Finset.sum_range_succ'` — exactly as the `m = 0` model
`exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound` merges its two genuine pieces. The
file lives upstream of `PointwiseTensorCurvL2Bound` (it does not import it) so that file can cite this
order-`m` child without an import cycle.

## What is proved vs. posited

The order-separated primitive `exists_iteratedCovGrad_pointwiseTensorCurv_orderSeparated_field` is
the genuine rank/order-generic moving-frame third-order Bochner–Weitzenböck curvature-jet content;
its construction is the iterated Ricci identity (`secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`)
producing, per Leibniz step, one further contraction of a covariant derivative of curvature against a
one-higher iterated gradient of `T`, all sup-bounded on the compact manifold by the uniform
curvature / differentiated-curvature sups (`exists_uniform_riemannianFiberNormSq_riemannOp_bound`,
`exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`). The top-order `∇^{m + 3}T` terms
cancel between the two summands `∇^m(Δ_∇∇T)` and `∇^m(∇Δ_∇T)` of the defect, so the genuine jet lands
at order `m + 1` (not `m + 2`) and the remainder at order `m + 2` (not `m + 3`). The body is `sorry`;
consumers transitively depend on `sorryAx` through this order-`m` curvature primitive.

The degenerate witness is rejected: at `m = 0` the merged split reads `Curv T (x) = Ggen + Grem` with
`rfns(Ggen)(x) ≤ (Cgr s 0)²·(rfns(T) + rfns(∇T))(x)` and `rfns(Grem)(x) ≤ (Cgr s 0)²·rfns(∇²T)(x)`,
which is *false* with `Cper s 0 = 0` on a non-flat manifold (the defect carries the genuine curvature
contraction of `T`).

## Sign / order conventions

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace) for the rough Laplacian. The covariant
gradient `covGrad g 0 s` raises the tensor rank from `(0, s)` to `(0, s + 1)`; `iteratedCovGrad
g 0 s j` is its `j`-fold iterate. All fibre norms are the intrinsic `riemannianFiberNormSq`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Posited deepest order-`m` curvature primitive: the order-`m` order-separated section-field
decomposition of the iterated commutator defect (rank/order-generic).** The direct order-`m` lift of
the `m = 0` section-field split `exists_pointwiseTensorCurv_orderSeparated_field`. For a closed smooth
Riemannian manifold `(M, g)` there is a *valence/order-dependent* nonnegative constant
`Cper : ℕ → ℕ → ℝ` such that, at every covariant rank `s`, gradient order `m`, smooth
compactly-supported `(0, s)`-tensor `T`, and *every point* `x`, the fibre value of the `m`-fold
iterated covariant gradient of the order-`2` commutator defect `Curv T := pointwiseTensorCurv g s T`
splits as `∇^m(Curv T)(x) = Gcurv + GcurvDeriv + Grem`, with:

* the **differentiated-Riemann jet** `Gcurv` (the `∇^m` Leibniz expansion of the pure-Riemann
  contraction `R(∇T)` — `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen`, each Leibniz term a
  covariant derivative of curvature against `∇^{i + 1}T`, `i ≤ m`) fibre-bounded by
  `∑_{i < m + 1} rfns(∇^{i + 1}T)` (orders `1 … m + 1`);
* the **iterated differentiated-curvature jet** `GcurvDeriv` (the `∇^m` Leibniz expansion of the
  differentiated-curvature contraction `(∇R) T` — `covGradCurvatureContraction`, each term a
  covariant derivative of curvature against `∇^i T`, `i ≤ m`) fibre-bounded by
  `∑_{i < m + 1} rfns(∇^i T)` (orders `0 … m`);
* the **moving-frame remainder** `Grem` fibre-bounded by `rfns(∇^{m + 2}T)` (the single top order),
  the moving-frame/frame-bracket discrepancy after the iterated Ricci cancellation of the top-order
  `∇^{m + 3}T` terms.

Each fibre bound is by `(Cper s m)²`, uniformly in `T`, all coefficients (covariant derivatives of
curvature) sup-bounded on the compact manifold by `exists_uniform_riemannianFiberNormSq_riemannOp_bound`
/ `exists_uniform_riemannianFiberNormSq_covGrad_riemannOp_bound`. The constant is
valence/order-dependent because the tensor-bundle curvature endomorphism is an `O(s + m)`-slot
derivation and the curvature-derivative term count grows with `m` (a single scalar uniform over all
`s, m` is unsatisfiable on a non-flat closed manifold).

The degenerate witness is rejected: at `m = 0` the split reads `Curv T (x) = Gcurv + GcurvDeriv +
Grem` with `Gcurv` bounded by `rfns(∇T)`, `GcurvDeriv` by `rfns(T)`, `Grem` by `rfns(∇²T)`, which —
merged — is the `m = 0` two-term split `exists_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound`,
*false* with `Cper s 0 = 0` on a non-flat manifold (the defect carries the genuine curvature
contraction of `T`). The assembly-ready two-term split
`exists_iteratedCovGrad_pointwiseTensorCurv_genuineRemainder_fiberNormSq_bound`
(`Geometry/Curvature/CovGradRoughLap/PointwiseTensorCurvL2Bound.lean`) is *proved* on top of this by
merging the two genuine jets through `riemannianFiberNormSq_add_le`. -/
theorem exists_iteratedCovGrad_pointwiseTensorCurv_orderSeparated_field
    (g : SmoothRiemannianMetric I M) :
    ∃ Cper : ℕ → ℕ → ℝ, (∀ s m, 0 ≤ Cper s m) ∧
      ∀ (s m : ℕ) (T : SmoothCcTensor g 0 s) (x : M),
        ∃ Gcurv GcurvDeriv Grem : TensorRSSpace 0 (s + 1 + m) I x,
          (iteratedCovGrad g 0 (s + 1) m
              (pointwiseTensorCurv (I := I) (M := M) g s T)).toSection x =
              Gcurv + GcurvDeriv + Grem ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x Gcurv ≤
            Cper s m ^ 2 * ∑ i ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (i + 1)) x
                ((iteratedCovGrad g 0 s (i + 1) T).toSection x) ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x GcurvDeriv ≤
            Cper s m ^ 2 * ∑ i ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
                ((iteratedCovGrad g 0 s i T).toSection x) ∧
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + m) x Grem ≤
            Cper s m ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g 0 (s + (m + 2)) x
                ((iteratedCovGrad g 0 s (m + 2) T).toSection x) := by
  sorry

end Connection
end Integral
end DifferentialGeometry
