import DifferentialGeometry.Analysis.Integration.Holder.Weighted
import DifferentialGeometry.Analysis.Parabolic.Moser.Iteration
import DifferentialGeometry.Analysis.Parabolic.Moser.LogTail
import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.Moser

variable {α : Type*} [MeasurableSpace α]

theorem integral_rpow_le_of_log_superlevel
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    {p q level tail : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≤ q)
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hfq : Integrable (fun x => f x ^ q) μ)
    (htail : μ.real {x | level < Real.log (f x)} ≤ tail) :
    (∫ x, f x ^ p ∂μ) ≤
      Real.exp (p * level) * μ.real Set.univ +
        (∫ x, f x ^ q ∂μ) ^ (p / q) * tail ^ (1 - p / q) := by
  let S : Set α := {x | level < Real.log (f x)}
  let ν : Measure α := μ.restrict S
  letI : IsFiniteMeasure ν := by
    dsimp only [ν]
    infer_instance
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf.log
  have hf_nonneg : 0 ≤ᵐ[μ] f := ae_of_all μ fun x => (hf_pos x).le
  have hfp := DifferentialGeometry.Integral.integrable_rpow_of_integrable_rpow
    hp hpq hf.aemeasurable hf_nonneg hfq
  have hratio_nonneg : 0 ≤ p / q := div_nonneg hp hq.le
  have htail_exp_nonneg : 0 ≤ 1 - p / q := sub_nonneg.mpr ((div_le_one hq).2 hpq)
  have hhigh := DifferentialGeometry.Integral.integral_rpow_le_integral_rpow_mul_measure
    (μ := ν) hp hq hpq
    (ae_of_all ν fun x => (hf_pos x).le)
    (hfq.mono_measure Measure.restrict_le_self)
  have hq_mono : (∫ x, f x ^ q ∂ν) ≤ ∫ x, f x ^ q ∂μ := by
    exact integral_mono_measure Measure.restrict_le_self
      (ae_of_all μ fun x => Real.rpow_nonneg (hf_pos x).le q) hfq
  have hmeasure : ν.real Set.univ ≤ tail := by
    simpa only [ν, measureReal_restrict_apply_univ, S] using htail
  have hhigh' : (∫ x in S, f x ^ p ∂μ) ≤
      (∫ x, f x ^ q ∂μ) ^ (p / q) * tail ^ (1 - p / q) := by
    have hq_int_nonneg : 0 ≤ ∫ x, f x ^ q ∂μ :=
      integral_nonneg fun x => Real.rpow_nonneg (hf_pos x).le q
    have hnu_int_nonneg : 0 ≤ ∫ x, f x ^ q ∂ν :=
      integral_nonneg fun x => Real.rpow_nonneg (hf_pos x).le q
    calc
      (∫ x in S, f x ^ p ∂μ) ≤
          (∫ x, f x ^ q ∂ν) ^ (p / q) * ν.real Set.univ ^ (1 - p / q) := by
            simpa only [ν] using hhigh
      _ ≤ (∫ x, f x ^ q ∂μ) ^ (p / q) * tail ^ (1 - p / q) := by
        exact mul_le_mul
          (Real.rpow_le_rpow hnu_int_nonneg hq_mono hratio_nonneg)
          (Real.rpow_le_rpow ENNReal.toReal_nonneg hmeasure htail_exp_nonneg)
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          (Real.rpow_nonneg hq_int_nonneg _)
  have hlow_point : ∀ᵐ x ∂μ.restrict Sᶜ,
      f x ^ p ≤ Real.exp (p * level) := by
    filter_upwards [ae_restrict_mem hS.compl] with x hx
    have hxlog : Real.log (f x) ≤ level := by
      exact le_of_not_gt (by simpa only [S, Set.mem_setOf_eq, Set.mem_compl_iff] using hx)
    rw [Real.rpow_def_of_pos (hf_pos x)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlow : (∫ x in Sᶜ, f x ^ p ∂μ) ≤
      Real.exp (p * level) * μ.real Set.univ := by
    calc
      (∫ x in Sᶜ, f x ^ p ∂μ) ≤ ∫ _x in Sᶜ, Real.exp (p * level) ∂μ := by
        exact integral_mono_ae
          (hfp.mono_measure Measure.restrict_le_self)
          (integrable_const _)
          hlow_point
      _ = μ.real Sᶜ * Real.exp (p * level) := by simp
      _ ≤ μ.real Set.univ * Real.exp (p * level) := by
        exact mul_le_mul_of_nonneg_right
          (measureReal_mono (μ := μ) (Set.subset_univ _) (measure_ne_top μ _))
          (Real.exp_pos _).le
      _ = Real.exp (p * level) * μ.real Set.univ := mul_comm _ _
  rw [← integral_add_compl hS hfp]
  exact add_le_add hhigh' hlow |>.trans_eq (add_comm _ _)

theorem integral_neg_rpow_le_of_log_sublevel
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    {p q level tail : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≤ q)
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hfq : Integrable (fun x => f x ^ (-q)) μ)
    (htail : μ.real {x | level < -(Real.log (f x))} ≤ tail) :
    (∫ x, f x ^ (-p) ∂μ) ≤
      Real.exp (p * level) * μ.real Set.univ +
        (∫ x, f x ^ (-q) ∂μ) ^ (p / q) * tail ^ (1 - p / q) := by
  have hinv_q : Integrable (fun x => (f x)⁻¹ ^ q) μ := by
    simpa only [Real.inv_rpow (hf_pos _).le, ← Real.rpow_neg (hf_pos _).le] using hfq
  have h := integral_rpow_le_of_log_superlevel μ (fun x => (f x)⁻¹)
    hp hq hpq hf.inv (fun x => inv_pos.mpr (hf_pos x)) hinv_q
    (by simpa only [Real.log_inv] using htail)
  simpa only [Real.inv_rpow (hf_pos _).le, ← Real.rpow_neg (hf_pos _).le] using h

open Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem early_localizedSpacetimeMeasure_log_superlevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {a τ r : ℝ} (haτ : a ≤ τ) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun q => u q x) t) :
    (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff a τ).real
        {z | r < Real.log
          (exponentialTimeRescale
            (logCenterDrift (I := I) (M := M) g averagingCutoff)
            (shiftedLogCenter (I := I) (M := M) g averagingCutoff
              u hu hpos τ) u z.1 z.2)} ≤
      2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ
  let rescaled := exponentialTimeRescale rate center u
  have hrescaled := contMDiff_exponentialTimeRescale rate center u hu
  have hrescaled_pos := exponentialTimeRescale_pos rate center u hpos
  let hlog := contMDiff_log_of_pos hrescaled hrescaled_pos
  rw [localizedSpacetimeMeasure_real_superlevel
    (I := I) (M := M) deviationCutoff haτ
      (fun z => Real.log (rescaled z.1 z.2)) hlog.continuous]
  simpa only [localizedSuperlevelMass, smoothScalarSlice_toFun, rescaled,
    rate, center, hlog] using
    integrated_early_centered_log_superlevel_tail_of_supersolution
      (I := I) (M := M) g deviationCutoff averagingCutoff C hC hP
        u hu hpos haτ hr hmass hpde

theorem late_localizedSpacetimeMeasure_neg_log_superlevel_tail_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {τ b r : ℝ} (hτb : τ ≤ b) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun q => u q x) t) :
    (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b).real
        {z | r < -Real.log
          (exponentialTimeRescale
            (logCenterDrift (I := I) (M := M) g averagingCutoff)
            (shiftedLogCenter (I := I) (M := M) g averagingCutoff
              u hu hpos τ) u z.1 z.2)} ≤
      2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ
  let rescaled := exponentialTimeRescale rate center u
  have hrescaled := contMDiff_exponentialTimeRescale rate center u hu
  have hrescaled_pos := exponentialTimeRescale_pos rate center u hpos
  let hlog := contMDiff_log_of_pos hrescaled hrescaled_pos
  change (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b).real
      {z | r < -Real.log (rescaled z.1 z.2)} ≤
    2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r
  have hset : {z : ℝ × M | r < -Real.log (rescaled z.1 z.2)} =
      {z : ℝ × M | Real.log (rescaled z.1 z.2) < -r} := by
    apply Set.ext
    intro z
    simp only [mem_setOf_eq]
    constructor <;> intro hz <;> linarith
  rw [hset]
  rw [localizedSpacetimeMeasure_real_sublevel
    (I := I) (M := M) deviationCutoff hτb
      (fun z => Real.log (rescaled z.1 z.2)) hlog.continuous]
  simpa only [localizedSublevelMass, smoothScalarSlice_toFun, rescaled,
    rate, center, hlog] using
    integrated_late_centered_log_sublevel_tail_of_supersolution
      (I := I) (M := M) g deviationCutoff averagingCutoff C hC hP
        u hu hpos hτb hr hmass hpde

theorem early_integral_rpow_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q r a τ : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≤ q)
    (haτ : a ≤ τ) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc a τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hq_int :
      let v := exponentialTimeRescale
        (logCenterDrift (I := I) (M := M) g averagingCutoff)
        (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u
      Integrable (fun z : ℝ × M => v z.1 z.2 ^ q)
        (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff a τ)) :
    let v := exponentialTimeRescale
      (logCenterDrift (I := I) (M := M) g averagingCutoff)
      (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u
    let ν := localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff a τ
    (∫ z, v z.1 z.2 ^ p ∂ν) ≤
      Real.exp (p * r) * ν.real Set.univ +
        (∫ z, v z.1 z.2 ^ q ∂ν) ^ (p / q) *
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r) ^
            (1 - p / q) := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ
  let v := exponentialTimeRescale rate center u
  let ν := localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff a τ
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hv_pos := exponentialTimeRescale_pos rate center u hpos
  have htail := early_localizedSpacetimeMeasure_log_superlevel_tail_of_supersolution
    (I := I) (M := M) g deviationCutoff averagingCutoff C hC hP
      u hu hpos haτ hr hmass hpde
  simpa only [v, ν, rate, center] using
    integral_rpow_le_of_log_superlevel ν (fun z : ℝ × M => v z.1 z.2)
      hp hq hpq hv.continuous.measurable (fun z => hv_pos z.1 z.2) hq_int htail

theorem late_integral_neg_rpow_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (deviationCutoff averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 ≤ C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      deviationCutoff averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q r τ b : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) (hpq : p ≤ q)
    (hτb : τ ≤ b) (hr : 0 < r)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).smooth x ≤
        deriv (fun s => u s x) t)
    (hq_int :
      let v := exponentialTimeRescale
        (logCenterDrift (I := I) (M := M) g averagingCutoff)
        (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u
      Integrable (fun z : ℝ × M => v z.1 z.2 ^ (-q))
        (localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b)) :
    let v := exponentialTimeRescale
      (logCenterDrift (I := I) (M := M) g averagingCutoff)
      (shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ) u
    let ν := localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b
    (∫ z, v z.1 z.2 ^ (-p) ∂ν) ≤
      Real.exp (p * r) * ν.real Set.univ +
        (∫ z, v z.1 z.2 ^ (-q) ∂ν) ^ (p / q) *
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff / r) ^
            (1 - p / q) := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff u hu hpos τ
  let v := exponentialTimeRescale rate center u
  let ν := localizedSpacetimeMeasure (I := I) (M := M) deviationCutoff τ b
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hv_pos := exponentialTimeRescale_pos rate center u hpos
  have htail := late_localizedSpacetimeMeasure_neg_log_superlevel_tail_of_supersolution
    (I := I) (M := M) g deviationCutoff averagingCutoff C hC hP
      u hu hpos hτb hr hmass hpde
  simpa only [v, ν, rate, center] using
    integral_neg_rpow_le_of_log_sublevel ν (fun z : ℝ × M => v z.1 z.2)
      hp hq hpq hv.continuous.measurable (fun z => hv_pos z.1 z.2) hq_int htail

end DifferentialGeometry.Analysis.Parabolic.Moser

end
