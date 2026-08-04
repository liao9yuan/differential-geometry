import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Topology.Morse.Taylor
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace DifferentialGeometry.Topology.Morse

open QuadraticForm
open MeasureTheory
open scoped Interval Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def morseNormalFormWeights (morseIndex : ℕ) : Fin (Module.finrank ℝ E) → ℝ :=
  fun i => if (i : ℕ) < morseIndex then -1 else 1

theorem chartHessian_weightedSumSquares_normalForm (g : E → ℝ)
    (hnd : (QuadraticMap.associated (R := ℝ) (chartHessian g)).SeparatingLeft) :
    ∃ w : Fin (Module.finrank ℝ E) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧
        QuadraticMap.Equivalent (chartHessian g) (QuadraticMap.weightedSumSquares ℝ w) ∧
          {i : Fin (Module.finrank ℝ E) | w i < 0}.ncard = sigNeg (chartHessian g) := by
  rcases QuadraticForm.equivalent_one_neg_one_weighted_sum_squared (chartHessian g) hnd with
    ⟨w, hw, hEq⟩
  refine ⟨w, hw, hEq, ?_⟩
  exact (QuadraticForm.sigNeg_of_equiv_weightedSumSquares hEq).symm

omit [FiniteDimensional ℝ E] in
noncomputable def morseTaylorBilin (g : E → ℝ) (x : E) : E →L[ℝ] (E →L[ℝ] ℝ) :=
  ∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)

omit [FiniteDimensional ℝ E] in
private theorem continuousOn_morseTaylorIntegrand (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) :
    ContinuousOn (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) Set.univ := by
  have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ g)) Set.univ := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ g)) Set.univ := h0.continuousOn
  have hsmul : Continuous (fun t : ℝ => t • x) := continuous_id.smul continuous_const
  have hcomp : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (t • x)) Set.univ := by
    intro t ht
    have hcAt : ContinuousAt (fderiv ℝ (fderiv ℝ g)) (t • x) :=
      (hcont (t • x) (Set.mem_univ _)).continuousAt Filter.univ_mem
    exact (ContinuousAt.comp (f := fun t : ℝ => t • x) (x := t) hcAt hsmul.continuousAt).continuousWithinAt
  exact (continuous_const.sub continuous_id).continuousOn.smul hcomp

omit [FiniteDimensional ℝ E] in
theorem second_order_taylor_bilin (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) :
    g x - g 0 = (fderiv ℝ g 0) x + (morseTaylorBilin g x) x x := by
  rw [second_order_taylor_integral g hg x]
  congr 1
  symm
  change (∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) x x =
    ∫ t in (0 : ℝ)..1, (1 - t) * ((fderiv ℝ (fderiv ℝ g) (t • x)) x) x
  have hBint : IntervalIntegrable (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) volume
      (0 : ℝ) 1 := by
    exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
      ((continuousOn_morseTaylorIntegrand g hg x).mono (by intro t ht; exact Set.mem_univ t))
  have hBvCont : ContinuousOn (fun t : ℝ => ((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) x) Set.univ := by
    have hMain : ContinuousOn (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) Set.univ :=
      continuousOn_morseTaylorIntegrand g hg x
    have hc : ContinuousOn (fun _ : ℝ => x) Set.univ := continuous_const.continuousOn
    exact ContinuousOn.clm_apply hMain hc
  have hBv : IntervalIntegrable (fun t : ℝ => ((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) x) volume
      (0 : ℝ) 1 := by
    exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
      (hBvCont.mono (by intro t ht; exact Set.mem_univ t))
  rw [ContinuousLinearMap.intervalIntegral_apply hBint x]
  rw [ContinuousLinearMap.intervalIntegral_apply hBv x]
  rfl

omit [FiniteDimensional ℝ E] in
theorem second_order_taylor_bilin_of_fderiv_eq_zero (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E)
    (hx₀ : fderiv ℝ g 0 = 0) :
    g x - g 0 = (morseTaylorBilin g x) x x := by
  rw [second_order_taylor_bilin g hg x, hx₀]
  simp

omit [FiniteDimensional ℝ E] in
theorem morseTaylorBilin_zero (g : E → ℝ) :
    morseTaylorBilin g 0 = (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ g) 0 := by
  dsimp [morseTaylorBilin]
  have hrewrite : (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • (0 : E))) =
      fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) 0 := by
    funext t
    rw [smul_zero]
  rw [hrewrite]
  have hInt : ∫ t in (0 : ℝ)..1, (1 - t) = 1 / 2 := by
    have hMain := intervalIntegral.integral_sub (μ := volume) (a := (0 : ℝ)) (b := 1)
      (f := fun _ : ℝ => (1 : ℝ)) (g := id)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (0 : ℝ) 1)
      (continuous_id.continuousOn.intervalIntegrable : IntervalIntegrable id volume (0 : ℝ) 1)
    calc
      ∫ t in (0 : ℝ)..1, (1 - t) = 1 - 2⁻¹ := by
        simpa [intervalIntegral.integral_const, integral_pow] using hMain
      _ = 1 / 2 := by norm_num
  rw [intervalIntegral.integral_smul_const (fun t : ℝ => 1 - t) (fderiv ℝ (fderiv ℝ g) 0), hInt]

end DifferentialGeometry.Topology.Morse
