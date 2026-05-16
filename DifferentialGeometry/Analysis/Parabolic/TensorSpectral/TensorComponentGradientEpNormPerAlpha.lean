import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.GradNormChartBoundPouWeighted
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientL2CovariantAtoms
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientL2ChristoffelAtoms
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientL2RawAtoms
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientL2AtomMeasurability
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProjBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartTwistUniformBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.GradNormChartBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovAndSlotChartSourceContinuity
import DifferentialGeometry.Analysis.Laplacian.MetricBounds

/-!
# Per-`α` `eLpNorm` bound on the metric self-inner-product square-root of the
gradient of the chart-frame scalar component

For a closed Riemannian manifold `(M, g)` admitting a locally constant chart
selection, a chart base point `α : M`, and ranks `(r, s)`, this file collects
the file-local elementary inequalities used to assemble the per-`α` `L²`
bound

```
eLpNorm (b ↦ √ g.inner b (∇ u_α b) (∇ u_α b)) 2 (riemannianVolumeMeasure g) ≤
  ENNReal.ofReal C * ‖S‖₊
```

where `u_α := tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx`, the
metric `g.inner` is the Riemannian fibre inner product on the tangent bundle,
and the constant `C` depends only on `(g, r, s, α)` and the locality
hypothesis.

## Strategy

The complete proof combines:

* the pointwise `ρ_α²`-weighted gradient bound
  (`g_inner_gradFun_le_pou_weighted_atoms_on_pouTsupport_h1`) and the
  vanishing of the gradient off `tsupport ρ_α`
  (`sqrt_g_inner_gradFun_tensorChartComponentScalar_eq_zero_outside_pouTsupport`),
  giving, after taking square roots,
  `√ g.inner b (∇u) (∇u) ≤ √A · |raw|_indicator
                          + √B · ρ · √Tcov_sum + √B · ρ · √Tchr_sum`
  globally on `M`;
* the per-`α` `L²`-bound on the raw indicator
  (`exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq`, G4);
* the per-`α` `L²`-bound on the chart-covariant-derivative atom sum
  (`exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq`, G2);
* the per-`α` per-direction `L²`-bound on the chart-Christoffel-correction
  atom (`exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq`,
  G3), bridged to the `G1` per-direction trivialised Christoffel correction
  via the chart-twist inverse uniform operator-norm bound
  (`chartRSTwistInv_pointwise_opNorm_isBounded_on_compact`) combined with a
  square-of-sum bound;
* `AEStronglyMeasurable` of each summand from the atom measurability
  headlines (`aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov`,
  `aestronglyMeasurable_pou_mul_sqrt_sum_christoffel_correction_per_k`,
  `aestronglyMeasurable_indicator_tsupp_abs_raw`).

Three Minkowski applications (`eLpNorm_add_le`) glue the three `eLpNorm`
bounds into the headline.

This module currently ships the elementary algebraic ingredients used in the
final assembly. The remaining structural bridge between the trivialised
Christoffel correction sum `Tchr_k = ‖triv(−Σ inputs + Σ outputs)‖²` and the
non-trivialised slot-correction Euclidean square `(Σ ‖input‖² + Σ ‖output‖²)`,
followed by the three-way Minkowski assembly, will land in a follow-up step
in the same module.

## File-local helper lemmas

* `sqrt_add_le_sqrt_add_sqrt` — `√(a + b) ≤ √a + √b` for non-negative reals.
* `sqrt_add3_le_sum` — `√(a + b + c) ≤ √a + √b + √c` for non-negative reals.
* `coe_nnnorm_eq_ofReal_norm` — `(‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 2400000
set_option maxHeartbeats 2400000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Elementary `Real.sqrt` inequalities

`√(a + b) ≤ √a + √b` and `√(a + b + c) ≤ √a + √b + √c` for non-negative
reals. These are used in the headline-assembly step to split the pointwise
gradient bound into three summands after taking square roots, prior to the
three-way Minkowski application. -/

/-- For non-negative reals `a`, `b`, `√(a + b) ≤ √a + √b`. -/
lemma sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h_sum_nn : 0 ≤ a + b := add_nonneg ha hb
  have h_sa_nn : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have h_sb_nn : 0 ≤ Real.sqrt b := Real.sqrt_nonneg _
  have h_sum_sq_nn : 0 ≤ Real.sqrt a + Real.sqrt b := add_nonneg h_sa_nn h_sb_nn
  have h_lhs_sq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt h_sum_nn
  have h_rhs_sq : (Real.sqrt a + Real.sqrt b) ^ 2 =
      a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
    rw [add_pow_two, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  have h_cross_nn : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
  have h_sq_le : Real.sqrt (a + b) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [h_lhs_sq, h_rhs_sq]; linarith
  exact (abs_le_of_sq_le_sq' h_sq_le h_sum_sq_nn).2

/-- For non-negative reals `a`, `b`, `c`, `√(a + b + c) ≤ √a + √b + √c`. -/
lemma sqrt_add3_le_sum {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  have h_ab_nn : 0 ≤ a + b := add_nonneg ha hb
  have h_step1 : Real.sqrt (a + b + c) ≤ Real.sqrt (a + b) + Real.sqrt c :=
    sqrt_add_le_sqrt_add_sqrt h_ab_nn hc
  have h_step2 : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b :=
    sqrt_add_le_sqrt_add_sqrt ha hb
  linarith

/-! ## Coercion helper -/

/-- For any element of a `SeminormedAddCommGroup`,
`(‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖`. -/
lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_add_le_sqrt_add_sqrt
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_add3_le_sum
#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.coe_nnnorm_eq_ofReal_norm
end Sanity
