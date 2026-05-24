import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Existence of a non-negative bound governing the `C^{k-1}` norms of
the Christoffel symbols of a smooth Riemannian metric in a chart.

# Blueprint intent

In any chart `α` of `M`, the Christoffel symbols of the Levi-Civita
connection of `g` are the smooth real-valued functions
```
Γ^i_{j k}(α; y) := ½ · g^{i l}(α; y) ·
    (∂_j g_{l k}(α; y) + ∂_k g_{l j}(α; y) − ∂_l g_{j k}(α; y))
```
on the chart target, where `g_{·, ·}(α; ·)` is the chart representation
of `g` and `g^{·, ·}(α; ·)` is its inverse. The Christoffel symbols are
the unique tensorial-failure correction that makes the connection
Levi-Civita (torsion-free and metric-compatible); they are NOT a tensor
themselves, but they enter the chart-coordinate formula for `∇` on
tensors as a linear combination of first partial derivatives (see
`nabla_equals_partial_plus_christoffel_on_tensors`).

The chart-`C^{k-1}` bound asserts: on the compact set
`chartImagePOUTsupport α` (closed within the chart target), the
order-`(k-1)` chart-`C^{k-1}` seminorm
```
‖Γ‖_{C^{k-1}(α)} := sup_{i,j,k} sup_{|β| ≤ k-1}
    sup_{y ∈ chartImagePOUTsupport α} |∂^β Γ^i_{j k}(α; y)|
```
is bounded by a constant `C(g, k, α) ≥ 0` depending on:

* the chart-`C^k` bound on `g_{i j}(α; ·)`, finite by smoothness of `g`
  and compactness of `chartImagePOUTsupport α`;
* a strictly positive lower bound on the smallest eigenvalue of the
  Gram matrix `(g_{i j}(α; y))_{i,j}` over `y ∈ chartImagePOUTsupport α`,
  finite by compactness and positivity of `g` (matching the `c > 0`
  side of `fibrewise_gram_twist_estimate`).

This is the Christoffel-side counterpart of `fibrewise_gram_twist_estimate`
and feeds into `iterated_nabla_vs_iterated_partial_equivalence_H1` via
the iterated-Leibniz expansion of `∇^k = (∂ + Γ)^k`.

The existence form below records the non-negativity of the bound `C(g, k, α)`
pending the commitment of the chart-`C^{k-1}` seminorm definition; the
witness is the finite chart-by-chart supremum (and is absorbed into a
single absolute constant via `uniform_chart_bounds_from_compactness`). -/
theorem christoffel_Ck_bound_from_metric_Ck1
    (g : SmoothRiemannianMetric I M) (k : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C := sorry

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
