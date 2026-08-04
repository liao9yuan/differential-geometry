import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Topology.Morse.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace DifferentialGeometry.Topology.Morse

open Filter QuadraticForm
open MeasureTheory
open scoped Filter Interval Topology

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

omit [FiniteDimensional ℝ E] in
private theorem hasFDerivAt_third_morse (g : E → ℝ) (hg : ContDiff ℝ 3 g) (x : E) (t : ℝ) :
    HasFDerivAt (fun x : E => fderiv ℝ (fderiv ℝ g) (t • x))
      ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp (t • (1 : E →L[ℝ] E))) x := by
  have hsmul : HasFDerivAt (fun x : E => t • x) (t • (1 : E →L[ℝ] E)) x := by
    exact (hasFDerivAt_id x).const_smul t
  have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
    hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
    h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ g)) (t • x) :=
    ((h1 _ (Set.mem_univ _)).differentiableWithinAt (by decide : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
      Filter.univ_mem
  exact HasFDerivAt.comp x (g := fderiv ℝ (fderiv ℝ g))
    (g' := fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)) (f := fun x : E => t • x)
    (f' := t • (1 : E →L[ℝ] E)) (hg := hd.hasFDerivAt) (hf := hsmul)

omit [FiniteDimensional ℝ E] in
private theorem continuousOn_morseTaylorDerivIntegrand (g : E → ℝ) (hg : ContDiff ℝ 3 g) (x : E) :
    ContinuousOn (fun t : ℝ => (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
      (t • (1 : E →L[ℝ] E)))) Set.univ := by
  have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ := by
    have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
      h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
  have hcont : ContinuousOn (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ := h0.continuousOn
  have hsmul : Continuous (fun t : ℝ => t • x) := continuous_id.smul continuous_const
  have hcomp : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)) Set.univ := by
    intro t ht
    have hcAt : ContinuousAt (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) (t • x) :=
      (hcont (t • x) (Set.mem_univ _)).continuousAt Filter.univ_mem
    exact (ContinuousAt.comp (f := fun t : ℝ => t • x) (x := t) hcAt hsmul.continuousAt).continuousWithinAt
  have hcompCLM : ContinuousOn (fun t : ℝ => (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
      (t • (1 : E →L[ℝ] E))) Set.univ := by
    have hL : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)) Set.univ := hcomp
    have hM : ContinuousOn (fun t : ℝ => t • (1 : E →L[ℝ] E)) Set.univ :=
      continuous_id.smul continuous_const |>.continuousOn
    intro t ht
    exact ContinuousOn.clm_comp hL hM t ht
  exact (continuous_const.sub continuous_id).continuousOn.smul hcompCLM

theorem hasFDerivAt_morseTaylorBilin (g : E → ℝ) (hg : ContDiff ℝ 3 g) (x₀ : E) :
    HasFDerivAt (fun x : E => morseTaylorBilin g x)
      (∫ t in (0 : ℝ)..1, (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x₀)).comp
        (t • (1 : E →L[ℝ] E)))) x₀ := by
  let F : E → ℝ → E →L[ℝ] (E →L[ℝ] ℝ) :=
    fun x t => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)
  let F' : E → ℝ → E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    fun x t => (1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
      (t • (1 : E →L[ℝ] E)))
  let s : Set E := Metric.ball x₀ 1
  have hs : s ∈ nhds x₀ := Metric.ball_mem_nhds x₀ (by norm_num)
  have hFcont : ∀ x : E, Continuous (F x) := by
    intro x
    have hg2 : ContDiff ℝ 2 g :=
      hg.of_le (by decide : (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))
    exact continuousOn_univ.mp (continuousOn_morseTaylorIntegrand g hg2 x)
  have hF'_cont : ∀ x : E, Continuous (F' x) := by
    intro x
    exact continuousOn_univ.mp (continuousOn_morseTaylorDerivIntegrand g hg x)
  have hF_meas : ∀ᶠ x in nhds x₀,
      AEStronglyMeasurable (F x) (volume.restrict (Ι (0 : ℝ) 1)) := by
    exact Eventually.of_forall fun x => (hFcont x).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Ι (0 : ℝ) 1)) :=
    (hF'_cont x₀).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F x₀) volume (0 : ℝ) 1 := by
    exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
      ((continuousOn_morseTaylorIntegrand g (by
        exact hg.of_le (by decide : (2 : WithTop ℕ∞) ≤ (3 : WithTop ℕ∞))) x₀).mono
        (by intro t ht; exact Set.mem_univ t))
  have h0 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) Set.univ := by
    have h2 : ContDiffOn ℝ 2 (fderiv ℝ g) Set.univ :=
      hg.contDiffOn.fderiv_of_isOpen isOpen_univ (by decide : (2 : WithTop ℕ∞) + 1 ≤ (3 : WithTop ℕ∞))
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ g)) Set.univ :=
      h2.fderiv_of_isOpen isOpen_univ (by decide : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact h1.fderiv_of_isOpen isOpen_univ (by decide : (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞))
  let R : ℝ := ‖x₀‖ + 2
  have hC : ∃ C : ℝ, ∀ y ∈ Metric.closedBall (0 : E) R, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y‖ ≤ C :=
    IsCompact.exists_bound_of_continuousOn (isCompact_closedBall (x := (0 : E)) (r := R))
      (h0.continuousOn.mono (by intro y hy; exact Set.mem_univ y))
  rcases hC with ⟨C, hCbound⟩
  have hbound_aux : ∀ x ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖F' x t‖ ≤ C := by
    intro x hx t ht
    have htx_mem : t • x ∈ Metric.closedBall (0 : E) R := by
      have hxnorm : ‖x‖ < ‖x₀‖ + 1 := by
        have hdist : dist x x₀ < 1 := (Metric.mem_ball.mp hx)
        calc
          ‖x‖ = dist x 0 := by rw [dist_zero_right]
          _ ≤ dist x x₀ + dist x₀ 0 := dist_triangle x x₀ 0
          _ = ‖x - x₀‖ + ‖x₀‖ := by rw [dist_eq_norm, dist_zero_right]
          _ < ‖x₀‖ + 1 := by
            have hnorm : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hdist
            linarith
      have htxnorm : ‖t • x‖ ≤ ‖x‖ := by
        calc
          ‖t • x‖ = |t| * ‖x‖ := norm_smul _ _
          _ ≤ 1 * ‖x‖ := by
            gcongr
            exact abs_le.mpr ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) ht.1, ht.2⟩
          _ = ‖x‖ := by rw [one_mul]
      exact Metric.mem_closedBall.mpr (by
        calc
          dist (t • x) 0 = ‖t • x‖ := by rw [dist_zero_right]
          _ ≤ ‖x‖ := htxnorm
          _ ≤ ‖x₀‖ + 2 := by linarith
          _ = R := rfl)
    have hnormcomp : ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp (t • (1 : E →L[ℝ] E))‖ ≤
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * |t| := by
      calc
        ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp (t • (1 : E →L[ℝ] E))‖ ≤
            ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * ‖t • (1 : E →L[ℝ] E)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * (‖t‖ * ‖(1 : E →L[ℝ] E)‖) := by
          rw [norm_smul]
        _ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * (|t| * ‖(1 : E →L[ℝ] E)‖) := by
          rw [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * |t| := by
          have hnorm1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
          have hinner : |t| * ‖(1 : E →L[ℝ] E)‖ ≤ |t| := by
            calc
              |t| * ‖(1 : E →L[ℝ] E)‖ ≤ |t| * 1 :=
                mul_le_mul_of_nonneg_left hnorm1 (abs_nonneg _)
              _ = |t| := by rw [mul_one]
          exact mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    calc
      ‖F' x t‖ = ‖(1 - t) • ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
          (t • (1 : E →L[ℝ] E)))‖ := rfl
      _ = ‖(1 - t)‖ * ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
          (t • (1 : E →L[ℝ] E))‖ := norm_smul _ _
      _ = |1 - t| * ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp
          (t • (1 : E →L[ℝ] E))‖ := by rw [Real.norm_eq_abs]
      _ ≤ |1 - t| * (‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * |t|) := by
        exact mul_le_mul_of_nonneg_left hnormcomp (abs_nonneg _)
      _ ≤ 1 * (C * 1) := by
        have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hCbound (0 : E) (by
          suffices 0 ≤ R from Metric.mem_closedBall.mpr (by simpa using this)
          positivity))
        have hleD : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ ≤ C := hCbound (t • x) htx_mem
        have hle1 : |t| ≤ 1 := abs_le.mpr ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) ht.1, ht.2⟩
        have hleDmul : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * |t| ≤ C * 1 :=
          mul_le_mul hleD hle1 (abs_nonneg t) hC0
        have hle0 : |1 - t| ≤ 1 := abs_le.mpr
          ⟨le_trans (by norm_num : (-1 : ℝ) ≤ 0) (sub_nonneg.mpr ht.2), sub_le_self 1 ht.1⟩
        calc
          |1 - t| * (‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)‖ * |t|) ≤
              |1 - t| * (C * 1) :=
            mul_le_mul le_rfl hleDmul (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (abs_nonneg _)
          _ ≤ 1 * (C * 1) := mul_le_mul hle0 le_rfl (by simpa using hC0) (zero_le_one)
      _ = C := by ring
  have h_bound : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ x ∈ s, ‖F' x t‖ ≤ (fun _ : ℝ => C) t := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    intro x hx
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      have : t ∈ Ι (0 : ℝ) 1 := ht
      exact ⟨by simpa using (le_of_lt this.1), by simpa using this.2⟩
    exact hbound_aux x hx t htIcc
  have h_diff : ∀ᵐ t ∂volume.restrict (Ι (0 : ℝ) 1), ∀ x ∈ s, HasFDerivAt (F · t) (F' x t) x := by
    exact Eventually.of_forall (by
      intro t x hx
      have hderiv : HasFDerivAt (fun x : E => fderiv ℝ (fderiv ℝ g) (t • x))
          ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (t • x)).comp (t • (1 : E →L[ℝ] E))) x :=
        hasFDerivAt_third_morse g hg x t
      simpa [F, F'] using hderiv.const_smul (1 - t))
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (a := (0 : ℝ)) (b := 1)
    (s := s) (x₀ := x₀) (F := F) (F' := F') (bound := fun _ : ℝ => C) hs hF_meas hF_int hF'_meas
    h_bound (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume (0 : ℝ) 1) h_diff
  simpa [morseTaylorBilin, F, F'] using hmain

end DifferentialGeometry.Topology.Morse
