import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ComponentWkpNormBoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentEpNormUniform
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorComponentGradientEpNormUniform

/-!
# Unconditional uniform chart-Sobolev `W^{1,2}` bound

For a closed Riemannian manifold `(M, g)` with locally constant chart
selection, this file delivers the unconditional uniform chart-Sobolev
`W^{1,2}` bound: a single non-negative real constant `C` such that for
every smooth compactly-supported `H¹` tensor section
`S : SmoothCcTensorH1 g r s`, every chart base point `α : M`, and every
chart-frame multi-index pair `(Idx, Jdx)`, the chart-based Sobolev
`W^{1,2}` norm of the chart-frame scalar component
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx` is bounded by
`ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)`.

## Strategy

We invoke the per-`α` headline
`tensorChartComponentScalar_wkpNormChart_le_const_mul_h1Norm`
(in `ComponentWkpNormBoundFromH1.lean`) for each `α` in the active
partition-of-unity finset, feeding in the `α`-uniform gradient `L²` bound
from `tensorChartComponentScalar_grad_eLpNorm_le`
(`TensorComponentGradientEpNormUniform.lean`, γ2.5.D). This gives, for each
active `α`, a per-`α` constant `Cα` such that the chart-Sobolev `W^{1,2}`
norm of the scalar component is bounded by `ENNReal.ofReal Cα * ‖S‖₊`.

We sum the per-`α` constants over the (finite) active set:
`C_total := ∑ α ∈ chartAtlasPOU_activeFinset, Cα α`.
For `α` outside the active finset, the scalar component vanishes
identically (because the partition-of-unity weight `POU α` does), hence
`wkpNormChart g 1 2 (tensorChartComponentScalar ... α ...) = 0`, which is
trivially `≤ ENNReal.ofReal C_total * ‖S‖₊`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Per-`α` `wkpNormChart` existence statement

For each chart base point `α : M`, the conditional headline
`tensorChartComponentScalar_wkpNormChart_le_const_mul_h1Norm`, fed with the
`α`-uniform gradient `L²` bound from γ2.5.D, produces a constant `C(α)` that
controls the chart-Sobolev `W^{1,2}` norm of the scalar component
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx`, uniformly in
`(S, Idx, Jdx)`. We package this as a single existence statement (for the
fixed `α`) and then extract the constant once via `Classical.choose`. -/

private lemma exists_perAlphaSobolevConstant
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  -- `[CompleteSpace E]` follows from finite-dimensionality.
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- Extract the `α`-uniform gradient `L²` constant (γ2.5.D).
  obtain ⟨C_grad, hC_grad_nn, hC_grad_bound⟩ :=
    tensorChartComponentScalar_grad_eLpNorm_le
      (I := I) (M := M) h_atlas g r s
  -- Specialise to the fixed `α`.
  exact tensorChartComponentScalar_wkpNormChart_le_const_mul_h1Norm
    (I := I) (M := M) g r s α hC_grad_nn
    (fun S Idx Jdx => hC_grad_bound S α Idx Jdx)

private noncomputable def perAlphaSobolevConstant
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) : ℝ :=
  Classical.choose
    (exists_perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s α)

private lemma perAlphaSobolevConstant_nonneg
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    0 ≤ perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s α :=
  (Classical.choose_spec
    (exists_perAlphaSobolevConstant
      (I := I) (M := M) h_atlas g r s α)).1

private lemma perAlphaSobolevConstant_bound
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNormChart (I := I) (M := M) g 1 2
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) ≤
      ENNReal.ofReal
          (perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s α) *
        (‖S‖₊ : ℝ≥0∞) :=
  (Classical.choose_spec
    (exists_perAlphaSobolevConstant
      (I := I) (M := M) h_atlas g r s α)).2 S Idx Jdx

/-! ## Vanishing of `wkpNormChart` on inactive centres

When `α : M` is not in `chartAtlasPOU_activeFinset`, the scalar component
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx` is identically
zero, so its chart-based Sobolev `W^{1,2}` norm vanishes. -/

private lemma wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNormChart (I := I) (M := M) g 1 2
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx) = 0 := by
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  rw [h_scalar_zero]
  exact wkpNormChart_zero_fun (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/-! ## Total active constant -/

private noncomputable def totalActiveSobolevConstant
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  ∑ α ∈ chartAtlasPOU_activeFinset I M,
    perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s α

private lemma totalActiveSobolevConstant_nonneg
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActiveSobolevConstant (I := I) (M := M) h_atlas g r s := by
  classical
  unfold totalActiveSobolevConstant
  exact Finset.sum_nonneg (fun α _ =>
    perAlphaSobolevConstant_nonneg (I := I) (M := M) h_atlas g r s α)

private lemma perAlphaSobolevConstant_le_totalActiveSobolevConstant
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {α : M}
    (hα : α ∈ chartAtlasPOU_activeFinset I M) :
    perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s α ≤
      totalActiveSobolevConstant (I := I) (M := M) h_atlas g r s := by
  classical
  unfold totalActiveSobolevConstant
  have h_split :
      ∑ β ∈ chartAtlasPOU_activeFinset I M,
        perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s β =
        perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s α +
        ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
          perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s β := by
    rw [← Finset.sum_erase_add _ _ hα, add_comm]
  rw [h_split]
  have h_rest_nn :
      0 ≤ ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
            perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s β :=
    Finset.sum_nonneg (fun β _ =>
      perAlphaSobolevConstant_nonneg (I := I) (M := M) h_atlas g r s β)
  linarith

/-! ## Headline -/

/-- **Headline (unconditional uniform chart-Sobolev `W^{1,2}` bound).** For a
closed Riemannian manifold `(M, g)` with locally constant chart selection
and ranks `(r, s)`, there exists a single non-negative real constant `C`
such that for every smooth compactly-supported `H¹` tensor section
`S : SmoothCcTensorH1 g r s`, every chart base point `α : M`, and every
chart-frame multi-index pair `(Idx, Jdx)`, the chart-based Sobolev `W^{1,2}`
norm of the chart-frame scalar component
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx` is bounded by
`ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)`. -/
theorem tensorChartComponent_wkpNormChart_le
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  refine ⟨totalActiveSobolevConstant (I := I) (M := M) h_atlas g r s,
    totalActiveSobolevConstant_nonneg (I := I) (M := M) h_atlas g r s, ?_⟩
  intro S α Idx Jdx
  by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
  · -- Active: chain per-`α` bound through `perAlphaSobolevConstant ≤ total`.
    have h_per :
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal
              (perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s α) *
            (‖S‖₊ : ℝ≥0∞) :=
      perAlphaSobolevConstant_bound
        (I := I) (M := M) h_atlas g r s α S Idx Jdx
    have h_const_le :
        ENNReal.ofReal
            (perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s α) ≤
          ENNReal.ofReal
            (totalActiveSobolevConstant (I := I) (M := M) h_atlas g r s) :=
      ENNReal.ofReal_le_ofReal
        (perAlphaSobolevConstant_le_totalActiveSobolevConstant
          (I := I) (M := M) h_atlas g r s hα)
    have h_envelope_le :
        ENNReal.ofReal
              (perAlphaSobolevConstant (I := I) (M := M) h_atlas g r s α) *
              (‖S‖₊ : ℝ≥0∞) ≤
          ENNReal.ofReal
              (totalActiveSobolevConstant (I := I) (M := M) h_atlas g r s) *
              (‖S‖₊ : ℝ≥0∞) :=
      mul_le_mul_of_nonneg_right h_const_le (by exact zero_le _)
    exact h_per.trans h_envelope_le
  · -- Inactive: the scalar component is identically zero, so wkpNormChart = 0.
    rw [wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive
      (I := I) (M := M) g r s hα S.toCcTensor Idx Jdx]
    exact zero_le _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_wkpNormChart_le

end Sanity
