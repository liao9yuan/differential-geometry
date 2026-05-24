import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.Integral.Connection.LeviCivitaChartLocal
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.FDerivDecomp
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Existence of a non-negative chart-`C^{k-1}` operator-norm bound on
the Christoffel symbols of a smooth Riemannian metric.

# Blueprint intent

In any chart `α` of `M`, the chart Christoffel object is the
continuous bilinear operator
```
y ↦ chartChristoffelBilin g α ((extChartAt I α).symm (toEuclidean.symm y))
    : EuclideanSpace ℝ (Fin n) → (E →L[ℝ] E →L[ℝ] E),
```
where `n = Module.finrank ℝ E` and `chartChristoffelBilin g α b : E →L[ℝ] E →L[ℝ] E`
is the iterated continuous-linear-map packaging of the chart Christoffel
symbols
`Γ^i_{j k}(α; b) := ½ · g^{i l}(α; b) ·
    (∂_j g_{l k}(α; b) + ∂_k g_{l j}(α; b) − ∂_l g_{j k}(α; b))`
(see `chartChristoffelBilin` and `chartChristoffel`). The Christoffel
symbols are the unique tensorial-failure correction that makes the
connection Levi-Civita (torsion-free and metric-compatible); they are
NOT a tensor themselves, but they enter the chart-coordinate formula
for `∇` on tensors as a linear combination of first partial derivatives
(see `nabla_equals_partial_plus_christoffel_on_tensors`).

The **chart-`C^{k-1}` operator-norm bound** on the chart Christoffel
object on the entire `chartTargetEuclid α` asserts: for every iterated
Fréchet-derivative order `j ≤ k - 1` (i.e. `j ∈ Finset.range k`) and
every `y ∈ chartTargetEuclid α`, the iterated Fréchet derivative
operator norm is bounded by `C`:
```
‖iteratedFDeriv ℝ j
    (fun y => chartChristoffelBilin g α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) y‖ ≤ C.
```
The constant `C(g, k, α) ≥ 0` depends on:

* the chart-`C^k` bound on `g_{i j}(α; ·)`, finite by smoothness of `g`
  and compactness of the closure of `chartImagePOUTsupport α`;
* a strictly positive lower bound on the smallest eigenvalue of the
  Gram matrix `(g_{i j}(α; y))_{i,j}` (matching the `c > 0` side of
  `fibrewise_gram_twist_estimate`).

This is the Christoffel-side counterpart of `fibrewise_gram_twist_estimate`
and feeds into `iterated_nabla_vs_iterated_partial_equivalence_H1` via
the iterated-Leibniz expansion of `∇^k = (∂ + Γ)^k`. The constant `C`
absorbs into a single absolute constant across the chart atlas via
`uniform_chart_bounds_from_compactness`.

The non-negativity of `C` follows since the LHS — an operator norm — is
non-negative. -/
theorem christoffel_Ck_bound_from_metric_Ck1
    (g : SmoothRiemannianMetric I M) (k : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j ∈ Finset.range k,
        ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          ‖iteratedFDeriv ℝ j
              (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
                chartChristoffelBilin (I := I) (M := M) g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
              y‖ ≤ C := sorry

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
