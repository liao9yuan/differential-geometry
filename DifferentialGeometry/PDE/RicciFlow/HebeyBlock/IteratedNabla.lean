import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.NablaTensorFormula
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChristoffelCkBound
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.GramTwist

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- Two-sided norm equivalence between the iterated-covariant-derivative
chart-Sobolev norm `(tensorPouSobolevHsNorm g k T).toReal` (in which the
iterated derivatives are computed in a Hilbert-Schmidt aggregation against
the chart-frame basis) and the iterated-partial-derivative chart-Sobolev
norm `(tensorPouSobolevNorm g k T).toReal` (in which the iterated
derivatives are aggregated by their operator norms).

# Blueprint intent

By `nabla_tensor_iterated_Hk_formula` the iterated covariant derivative
`∇^k T` differs from the iterated partial derivative `∂^k T` (computed on
the chart-frame scalar components) by a sum of lower-order
partial-derivative terms multiplied by Christoffel-symbol products. The
Christoffel-symbol `C^{k-1}` bound `christoffel_Ck_bound_from_metric_Ck1`
controls these lower-order terms uniformly, and the fibrewise Gram-twist
estimate `fibrewise_gram_twist_estimate` controls the index-raising /
lowering performed by the chart-frame component reconstruction. The
resulting equivalence
```
c · (tensorPouSobolevNorm g k T).toReal ≤
    (tensorPouSobolevHsNorm g k T).toReal ≤
  C · (tensorPouSobolevNorm g k T).toReal,
```
valid for every smooth compactly-supported `(r, s)`-tensor section `T`,
with `0 < c ≤ C` absorbing all chart-dependence into a single absolute
constant via `uniform_chart_bounds_from_compactness`. The `_H1` suffix
of the theorem name refers to the prototypical `k = 1` instance that
feeds directly into the `H^1` Hilbert-space comparison in
`assemble_pou_h1_iso_intrinsic_h1`. -/
-- Status by regularity order:
--   * `k = 0` is substantively PROVEN by direct delegation to
--     `fibrewise_gram_twist_estimate`, which establishes the two-sided
--     comparison (in fact with constants `c = C = 1`) by reducing both norms
--     to a common single-term expression at order zero.
--   * `k ≥ 1` remains open. The forward direction
--     `HsNorm ≤ C · Norm` can in principle be assembled from
--     `nabla_tensor_iterated_Hk_formula`, the `C^{k-1}` Christoffel bound
--     `christoffel_Ck_bound_from_metric_Ck1`, and the one-sided
--     `uniform_chart_bounds_from_compactness`. The reverse direction
--     `c · Norm ≤ HsNorm` requires inverting the lower-order
--     Christoffel-correction expansion at order `≥ 1`, for which no upstream
--     witness exists in the current codebase. A substantive proof at general
--     `k` is therefore blocked on building that lower-bound infrastructure.
theorem iterated_nabla_vs_iterated_partial_equivalence_H1
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        c * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal ≤
            (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ∧
          (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
            C * (tensorPouSobolevNorm (I := I) (M := M) g k T).toReal := by
  match k with
  | 0 =>
    -- Substantive: at order `k = 0` the two norms agree on the nose, so the
    -- two-sided bound holds with `c = C = 1` via `fibrewise_gram_twist_estimate`.
    exact fibrewise_gram_twist_estimate (I := I) (M := M) g r s
  | _ + 1 =>
    -- Open at order `k ≥ 1`: see the comment block above.  The reverse
    -- direction `c · tensorPouSobolevNorm ≤ tensorPouSobolevHsNorm` at
    -- order `≥ 1` has no upstream witness in the current codebase.
    sorry

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
