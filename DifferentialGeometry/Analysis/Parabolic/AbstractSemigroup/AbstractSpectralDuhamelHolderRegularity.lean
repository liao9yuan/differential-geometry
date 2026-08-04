import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralDuhamel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.TimeDeriv
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Topology.MetricSpace.HolderNorm

noncomputable section

open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace InnerProductSpace BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} {X : Type*} [NormedAddCommGroup X]
  [InnerProductSpace ℝ X] [CompleteSpace X]

def abstractSpectralDuhamelHolderCorrection
    (b : HilbertBasis ι ℝ X) (lam : ι → ℝ) (F : ℝ → X) (t : ℝ) : X :=
  ∫ s in (0 : ℝ)..t,
    if s < t then
      abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)
    else 0

theorem abstractSpectralDuhamelHolderCorrection_intervalIntegrable
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {F : ℝ → X} {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable
      (fun s : ℝ => if s < t then
        abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)
        else 0) volume 0 t := by
  let G : ℝ → X := fun s =>
    if s < t then
      abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)
    else 0
  let Graw : ℝ → X := fun s =>
    abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)
  have hFcont : Continuous F := hF.continuous hα
  have hinner : Continuous (fun s : ℝ => (t - s, F s - F t)) :=
    (continuous_const.sub continuous_id).prodMk
      (hFcont.sub continuous_const)
  have hGraw : ContinuousOn Graw (Set.Iio t) := by
    simpa only [Graw, Function.comp_apply] using
      (abstractSpectralSemigroupDeriv_continuousOn_uncurry b hlam).comp
        hinner.continuousOn
        (fun s hs => ⟨by
          simpa using sub_pos.mpr (Set.mem_Iio.mp hs), Set.mem_univ _⟩)
  have hGmeas : AEStronglyMeasurable G volume := by
    have hp : AEStronglyMeasurable
        ((Set.Iio t).piecewise Graw (0 : ℝ → X)) volume :=
      AEStronglyMeasurable.piecewise (μ := volume) measurableSet_Iio
      (hGraw.aestronglyMeasurable measurableSet_Iio)
      aestronglyMeasurable_zero
    simpa only [G, Set.piecewise, Set.mem_Iio, Pi.zero_apply] using hp
  have hpow : IntervalIntegrable
      (fun s : ℝ => (t - s) ^ ((α : ℝ) - 1)) volume 0 t := by
    have hbase : IntervalIntegrable
        (fun q : ℝ => q ^ ((α : ℝ) - 1)) volume 0 t :=
      intervalIntegral.intervalIntegrable_rpow' (by
        have hαR : 0 < (α : ℝ) := NNReal.coe_pos.mpr hα
        linarith)
    simpa using (hbase.comp_sub_left t).symm
  have hdom : IntervalIntegrable
      (fun s : ℝ => ((K : ℝ) / Real.exp 1) *
        (t - s) ^ ((α : ℝ) - 1)) volume 0 t :=
    hpow.const_mul ((K : ℝ) / Real.exp 1)
  rw [intervalIntegrable_iff, Set.uIoc_of_le ht.le] at hdom ⊢
  refine hdom.mono' hGmeas.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  by_cases hst : s < t
  · have hτ : 0 < t - s := sub_pos.mpr hst
    have hholder := hF.dist_le s t
    have hdist : dist s t = t - s := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
      ring
    rw [dist_eq_norm, hdist] at hholder
    simp only [if_pos hst]
    change ‖abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)‖ ≤
      ((K : ℝ) / Real.exp 1) *
      (t - s) ^ ((α : ℝ) - 1)
    calc
      ‖abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)‖ ≤
          (1 / (Real.exp 1 * (t - s))) * ‖F s - F t‖ :=
        norm_abstractSpectralSemigroupDeriv_le b hlam hτ (F s - F t)
      _ ≤ (1 / (Real.exp 1 * (t - s))) *
          ((K : ℝ) * (t - s) ^ (α : ℝ)) :=
        mul_le_mul_of_nonneg_left hholder (by positivity)
      _ = ((K : ℝ) / Real.exp 1) *
          (t - s) ^ ((α : ℝ) - 1) := by
        rw [Real.rpow_sub_one hτ.ne']
        field_simp [hτ.ne', (Real.exp_pos 1).ne']
  · have hst' : s = t := le_antisymm hs.2 (le_of_not_gt hst)
    subst s
    simp only [lt_self_iff_false, ↓reduceIte, norm_zero]
    exact mul_nonneg (div_nonneg K.coe_nonneg (Real.exp_pos 1).le)
      (Real.rpow_nonneg (sub_nonneg.mpr le_rfl) _)

theorem abstractSpectralDuhamelHolderCorrection_repr_apply
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {F : ℝ → X} {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    {t : ℝ} (ht : 0 < t) (i : ι) :
    (b.repr (abstractSpectralDuhamelHolderCorrection b lam F t) : ι → ℝ) i =
      ∫ s in (0 : ℝ)..t,
        -(lam i) * Real.exp (-(lam i) * (t - s)) *
          ((b.repr (F s) : ι → ℝ) i - (b.repr (F t) : ι → ℝ) i) := by
  let ℓ : X →L[ℝ] ℝ := innerSL (𝕜 := ℝ) (E := X) (b i)
  have hint := abstractSpectralDuhamelHolderCorrection_intervalIntegrable
    b hlam hα hF ht
  have hcomm := ℓ.intervalIntegral_comp_comm hint
  rw [b.repr_apply_apply]
  change ℓ (abstractSpectralDuhamelHolderCorrection b lam F t) = _
  rw [abstractSpectralDuhamelHolderCorrection, ← hcomm]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht.le] at hs
  by_cases hst : s < t
  · simp only [if_pos hst]
    change ℓ (abstractSpectralSemigroupDeriv b lam (t - s) (F s - F t)) = _
    simp only [ℓ, innerSL_apply_apply, ← b.repr_apply_apply]
    rw [abstractSpectralSemigroupDeriv_repr_apply b hlam (sub_pos.mpr hst), map_sub]
    rfl
  · have hst' : s = t := le_antisymm hs.2 (le_of_not_gt hst)
    subst s
    simp

def abstractSpectralDuhamelHolderDeriv
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) (F : ℝ → X) (t : ℝ) : X :=
  abstractSpectralSemigroupDeriv b lam t u₀ +
    abstractSpectralSemigroup b hlam t (F t) +
    abstractSpectralDuhamelHolderCorrection b lam F t

theorem abstractSpectralDuhamelHolderDeriv_repr_apply
    (b : HilbertBasis ι ℝ X) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (u₀ : X) {F : ℝ → X} {K α : NNReal} (hα : 0 < α)
    (hF : HolderWith K α F) {t : ℝ} (ht : 0 < t) (i : ι) :
    (b.repr (abstractSpectralDuhamelHolderDeriv b hlam u₀ F t) : ι → ℝ) i =
      -(lam i) *
          (b.repr (abstractSpectralDuhamel b hlam u₀ F t) : ι → ℝ) i +
        (b.repr (F t) : ι → ℝ) i := by
  have hFcont : Continuous F := hF.continuous hα
  have hduhamel := abstractSpectralDuhamel_repr_apply b hlam u₀ hFcont ht.le i
  have hcorrection := abstractSpectralDuhamelHolderCorrection_repr_apply
    b hlam hα hF ht i
  have hkernel := kernelIntegral_space (lam i) t
  have hkernel' :
      (∫ s in (0 : ℝ)..t, lam i * Real.exp (-lam i * (t - s))) =
        1 - Real.exp (-lam i * t) := by
    simpa only [neg_mul] using hkernel
  simp only [abstractSpectralDuhamelHolderDeriv]
  rw [map_add, map_add]
  change
    (b.repr (abstractSpectralSemigroupDeriv b lam t u₀) : ι → ℝ) i +
        (b.repr (abstractSpectralSemigroup b hlam t (F t)) : ι → ℝ) i +
        (b.repr (abstractSpectralDuhamelHolderCorrection b lam F t) : ι → ℝ) i = _
  rw [abstractSpectralSemigroupDeriv_repr_apply b hlam ht,
    abstractSpectralSemigroup_repr_apply b hlam ht.le, hcorrection, hduhamel]
  simp only [heatDerivCoeff_def, heatCoeff_def]
  have hsplit :
      (∫ s in (0 : ℝ)..t,
        -(lam i) * Real.exp (-(lam i) * (t - s)) *
          ((b.repr (F s) : ι → ℝ) i - (b.repr (F t) : ι → ℝ) i)) =
      -(lam i) * (∫ s in (0 : ℝ)..t,
        Real.exp (-(lam i) * (t - s)) * (b.repr (F s) : ι → ℝ) i) +
      (1 - Real.exp (-(lam i) * t)) * (b.repr (F t) : ι → ℝ) i := by
    have hmode : Continuous (fun s : ℝ => (b.repr (F s) : ι → ℝ) i) := by
      simpa only [b.repr_apply_apply] using
        (innerSL (𝕜 := ℝ) (E := X) (b i)).continuous.comp hFcont
    rw [show (fun s : ℝ =>
        -(lam i) * Real.exp (-(lam i) * (t - s)) *
          ((b.repr (F s) : ι → ℝ) i - (b.repr (F t) : ι → ℝ) i)) =
      fun s => -(lam i) *
          (Real.exp (-(lam i) * (t - s)) * (b.repr (F s) : ι → ℝ) i) +
        (lam i * Real.exp (-(lam i) * (t - s))) *
          (b.repr (F t) : ι → ℝ) i from by
        funext s
        ring]
    rw [intervalIntegral.integral_add
      ((Continuous.intervalIntegrable (by fun_prop)) 0 t)
      ((Continuous.intervalIntegrable (by fun_prop)) 0 t),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, hkernel']
  rw [hsplit]
  ring

end Parabolic
end Analysis
end DifferentialGeometry

end
