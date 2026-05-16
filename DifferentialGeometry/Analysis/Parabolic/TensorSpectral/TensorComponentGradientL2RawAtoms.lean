import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SectionNormFromTensorInner
import DifferentialGeometry.Geometry.LocalChartConsistency

/-!
# Per-`α` `L²` bound on the `raw²` chart-component indicator over POU support

For a closed Riemannian manifold `(M, g)` and a smooth compactly-supported
`H¹` tensor section `S`, this file ships the `L²` bound

```
eLpNorm (fun b ↦ (tsupport ρ_α).indicator
    (fun b' ↦ scalarOnE α (tensorChartComponentRaw g r s S α Idx Jdx)
                (extChartAt I α b')) b) 2 (riemannianVolumeMeasure g)
  ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)
```

with `C ≥ 0` depending only on `(g, r, s, α)` and on the locality hypothesis,
independent of `S` and of the multi-indices `(Idx, Jdx)`.

The proof reduces the chart-pullback to `raw b` on `tsupport(POU_α)` via
`scalarOnE α f (extChartAt I α b) = f b`, then combines the uniform
multi-index projection operator-norm bound with the chart-frame quadratic-
form upper bound `‖tensorTrivProj S α b‖² ≤ K · tensorInnerPointwise(...)`
and integrates against `riemannianVolumeMeasure g`, converting from
`eLpNorm` to `Real.sqrt` of the `L²` integral. The L²–H¹ comparison
`SmoothCcTensorH1.l2Norm_le_h1Norm` upgrades the bound to `‖S‖₊`.
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

private lemma scalarOnE_raw_eq_raw_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b) =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have hb_chart : b ∈ (chartAt H α).source := hb_base
  have hb_ext : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hb_chart
  exact scalarOnE_extChartAt (I := I) α
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hb_ext

/-- **Pointwise quadratic upper bound on the chart-pullback raw scalar.**

On `tsupport(POU_α)`, the squared chart-pullback raw chart-frame scalar
component at `b` is bounded by `C_pt · tensorInnerPointwise g r s b
(S.toFun b) (S.toFun b)`, with `C_pt ≥ 0` depending only on
`(g, r, s, α)`. -/
private lemma scalarOnE_raw_sq_le_const_mul_tensorInner_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        {b : M}, b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          (scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
              (extChartAt I α b)) ^ 2 ≤
            C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    tensorTrivProj_norm_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b hb
  -- Reduce chart-pullback to `tensorChartComponentRaw b`.
  rw [scalarOnE_raw_eq_raw_on_pouTsupport (I := I) (M := M) g r s α S Idx Jdx hb]
  -- Unfold `tensorChartComponentRaw` to `P_IJ (tensorTrivProj S α b)`.
  unfold tensorChartComponentRaw
  set T : TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α b
  set P_IJ : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx
  -- `|P_IJ T| ≤ C_proj · ‖T‖`.
  have h_proj_le : ‖P_IJ T‖ ≤ C_proj * ‖T‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
        (norm_nonneg _))
  -- Square: `(P_IJ T)² ≤ C_proj² · ‖T‖²`.
  have h_proj_sq_le : (P_IJ T) ^ 2 ≤ C_proj ^ 2 * ‖T‖ ^ 2 := by
    have h_abs : (P_IJ T) ^ 2 = ‖P_IJ T‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_abs]
    have hsq := mul_self_le_mul_self (norm_nonneg _) h_proj_le
    have h_rhs : (C_proj * ‖T‖) * (C_proj * ‖T‖) = C_proj ^ 2 * ‖T‖ ^ 2 := by
      ring
    have h_lhs : ‖P_IJ T‖ * ‖P_IJ T‖ = ‖P_IJ T‖ ^ 2 := by rw [sq]
    linarith [hsq, h_lhs.symm.le, h_rhs.symm.le, h_lhs.le, h_rhs.le]
  -- `‖T‖² ≤ K · tensorInner(S.toFun, S.toFun)`.
  have h_triv_sq_le : ‖T‖ ^ 2 ≤ K *
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := h_norm S b hb
  -- Combine: `(P_IJ T)² ≤ C_proj² · K · tensorInner`.
  have hC_proj_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
  have h_chain_sq : (P_IJ T) ^ 2 ≤
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) := by
    have h_mul := mul_le_mul_of_nonneg_left h_triv_sq_le hC_proj_sq_nn
    exact h_proj_sq_le.trans h_mul
  have h_reassoc :
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) =
        C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by ring
  linarith [h_chain_sq, h_reassoc.le, h_reassoc.symm.le]

private lemma indicator_scalarOnE_raw_sq_le_const_mul_tensorInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
          ((tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
              (extChartAt I α b')) b) ^ 2 ≤
            C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    scalarOnE_raw_sq_le_const_mul_tensorInner_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx b
  set ρSet : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  set F : M → ℝ := fun b' : M => scalarOnE (I := I) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      (extChartAt I α b')
  by_cases hb : b ∈ ρSet
  · -- Inside `tsupport(POU_α)`: indicator equals `F b`.
    have h_ind_eq : ρSet.indicator F b = F b := Set.indicator_of_mem hb _
    rw [h_ind_eq]
    exact h_pt S Idx Jdx hb
  · -- Outside: indicator is zero, and the RHS is non-negative.
    have h_ind_eq : ρSet.indicator F b = 0 := Set.indicator_of_notMem hb _
    rw [h_ind_eq]
    have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) :=
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
    have h_RHS_nn : 0 ≤ C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := mul_nonneg hC_nn hQ_nn
    have hzero_sq : (0 : ℝ) ^ 2 = 0 := by ring
    rw [hzero_sq]
    exact h_RHS_nn

private lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

private lemma sqrt_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
      (ENNReal.ofReal (Real.sqrt S)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

private lemma eLpNorm_two_le_ofReal_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {S : ℝ} (hS : 0 ≤ S)
    (h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have h_pow := le_sqrt_of_sq_le h_sq
  rw [sqrt_ofReal_eq_ofReal_sqrt hS] at h_pow
  exact h_pow

private lemma sq_eLpNorm_indicator_raw_le_const_mul_tensorL2Inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal (C *
            tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    indicator_scalarOnE_raw_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  set f : M → ℝ := fun b : M =>
    (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
      (fun b' : M => scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b')) b
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  -- Pointwise ENNReal bound.
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorInnerPointwise (I := I) (M := M)
          g r s b (S.toFun b) (S.toFun b)) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt S Idx Jdx b)
  -- Integrability of the RHS integrand.
  have h_inner_int := SmoothCcTensor.integrable_inner_cross
    (I := I) (M := M) (g := g) (r := r) (s := s) S S
  have h_C_smul_int :
      Integrable (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b)) μ :=
    h_inner_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    exact mul_nonneg hC_nn
      (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  -- Convert `(eLpNorm f 2 μ)^2` and bound the lintegral.
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
  have h_lint_le :
      ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
        ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards with b using h_pt_enn b
  have h_lint_eq :
      ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ =
        ENNReal.ofReal (∫ b, C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b) ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      h_C_smul_int h_C_smul_nn).symm
  rw [h_lint_eq] at h_lint_le
  have h_int_const_mul :
      ∫ b, C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) ∂μ =
        C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    rw [integral_const_mul]
  rw [h_int_const_mul] at h_lint_le
  exact h_lint_le

private theorem indicator_eLpNorm_raw_le_const_mul_tensorL2Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_sq⟩ :=
    sq_eLpNorm_indicator_raw_le_const_mul_tensorL2Inner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S Idx Jdx
  -- `tensorL2Inner S S = (tensorL2Norm S.toFun)²` since the inner is non-negative.
  have h_inner_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    refine integral_nonneg ?_
    intro b
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have h_norm_sq :
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun =
        (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 := by
    unfold tensorL2Norm
    rw [sq, Real.mul_self_sqrt h_inner_nn]
  set S_total : ℝ := C *
    tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun with hS_total_def
  have hS_total_nn : 0 ≤ S_total := mul_nonneg hC_nn h_inner_nn
  have h_eLpNorm_le :=
    eLpNorm_two_le_ofReal_sqrt hS_total_nn (h_sq S Idx Jdx)
  -- `√(C · ‖S‖²) = √C · ‖S‖`.
  have h_sqrt_factor :
      Real.sqrt S_total = Real.sqrt C *
        tensorL2Norm (I := I) (M := M) g r s S.toFun := by
    rw [hS_total_def, h_norm_sq, Real.sqrt_mul hC_nn,
      show (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 =
        tensorL2Norm (I := I) (M := M) g r s S.toFun *
          tensorL2Norm (I := I) (M := M) g r s S.toFun from by ring,
      Real.sqrt_mul_self
        (tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun)]
  rw [h_sqrt_factor,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLpNorm_le
  exact h_eLpNorm_le

private lemma tensorL2Norm_eq_norm_toCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
      ‖S.toCcTensor‖ := by
  have h_sq := SmoothCcTensor.norm_sq_eq_inner_self
    (I := I) (M := M) (g := g) (r := r) (s := s) S.toCcTensor
  have h_l2_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
        S.toCcTensor.toFun S.toCcTensor.toFun := by
    unfold tensorL2Inner
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have h_norm_nn : 0 ≤ ‖S.toCcTensor‖ := norm_nonneg _
  have h_lhs :
      tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
        Real.sqrt (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := rfl
  rw [h_lhs]
  have h_rhs :
      ‖S.toCcTensor‖ = Real.sqrt
        (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := by
    rw [← Real.sqrt_sq h_norm_nn, h_sq]
  rw [h_rhs]

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

private lemma ofReal_tensorL2Norm_le_norm_ennreal
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ENNReal.ofReal
        (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
      (‖S‖₊ : ℝ≥0∞) := by
  rw [tensorL2Norm_eq_norm_toCcTensor (I := I) (M := M) g r s S]
  have h_l2_le_h1 :
      ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  rw [coe_nnnorm_eq_ofReal_norm S]
  exact ENNReal.ofReal_le_ofReal h_l2_le_h1

/-- **Per-`α` `L²` bound on the `raw²` chart-component indicator over POU
support.** For a closed Riemannian manifold `(M, g)` with locally constant
chart selection, there is `C ≥ 0` (depending only on `(g, r, s, α)` and the
locality hypothesis) such that for every smooth compactly-supported H¹
tensor section `S` and every multi-index pair `(Idx, Jdx)`, the indicator
over `tsupport(POU_α)` of the chart-pullback of the raw chart-frame scalar
component has `L²` norm bounded by `ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)`. -/
theorem exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq
    (_h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
          (fun b : M => (tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M =>
              scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C, hC_nn, h_smoothCc⟩ :=
    indicator_eLpNorm_raw_le_const_mul_tensorL2Norm
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  have h_smoothCc' :
      eLpNorm (fun b : M =>
          (tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)
              (extChartAt I α b')) b) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s
              S.toCcTensor.toFun) :=
    h_smoothCc S.toCcTensor Idx Jdx
  have h_rhs_le :
      ENNReal.ofReal C *
        ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
        ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
    mul_le_mul_of_nonneg_left
      (ofReal_tensorL2Norm_le_norm_ennreal (I := I) (M := M) g r s S)
      (by exact zero_le _)
  exact h_smoothCc'.trans h_rhs_le

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq

end Sanity
