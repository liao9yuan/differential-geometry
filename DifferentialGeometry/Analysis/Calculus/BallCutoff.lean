import DifferentialGeometry.Analysis.Calculus.CutoffProfile
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis

open Set
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E]

def ballCutoffArgument (center : E) (r R : ℝ) (x : E) : ℝ :=
  1 + (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2)

def ballCutoff (center : E) (r R : ℝ) (x : E) : ℝ :=
  CutoffProfile.value (ballCutoffArgument center r R x)

def ballCutoffArgumentFDeriv [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) : E →L[ℝ] ℝ :=
  (R ^ 2 - r ^ 2)⁻¹ • ((2 : ℕ) • innerSL ℝ (x - center))

def ballCutoffArgumentFDeriv2 [InnerProductSpace ℝ E]
    (r R : ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (R ^ 2 - r ^ 2)⁻¹ • ((2 : ℕ) • innerSL ℝ)

def ballCutoffFDeriv [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) : E →L[ℝ] ℝ :=
  deriv CutoffProfile.value (ballCutoffArgument center r R x) •
    ballCutoffArgumentFDeriv center r R x

def ballCutoffFDerivBound (r R : ℝ) : ℝ :=
  CutoffProfile.derivBound * (2 * R / (R ^ 2 - r ^ 2))

theorem hasFDerivAt_ballCutoffArgument [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) :
    HasFDerivAt (ballCutoffArgument center r R)
      (ballCutoffArgumentFDeriv center r R x) x := by
  have hnorm := ((hasFDerivAt_id x).sub_const center).norm_sq
  have h := (hnorm.sub_const (r ^ 2)).mul_const (R ^ 2 - r ^ 2)⁻¹
  have h' := (hasFDerivAt_const (x := x) (c := (1 : ℝ))).add h
  simpa [ballCutoffArgument, ballCutoffArgumentFDeriv] using h'

theorem hasFDerivAt_ballCutoffArgumentFDeriv [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) :
    HasFDerivAt (ballCutoffArgumentFDeriv center r R)
      (ballCutoffArgumentFDeriv2 r R) x := by
  simpa [ballCutoffArgumentFDeriv, ballCutoffArgumentFDeriv2] using
    (((R ^ 2 - r ^ 2)⁻¹ • ((2 : ℕ) • (innerSL ℝ (E := E)))).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const center))

theorem hasFDerivAt_ballCutoff [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) (x : E) :
    HasFDerivAt (ballCutoff center r R)
      (ballCutoffFDeriv center r R x) x := by
  have hprofile : HasDerivAt CutoffProfile.value
      (deriv CutoffProfile.value (ballCutoffArgument center r R x))
      (ballCutoffArgument center r R x) :=
    (CutoffProfile.contDiff.differentiable (by simp)
      (ballCutoffArgument center r R x)).hasDerivAt
  simpa only [ballCutoff, ballCutoffFDeriv, Function.comp_def] using
    hprofile.comp_hasFDerivAt x
      (hasFDerivAt_ballCutoffArgument center r R x)

theorem ballCutoffFDerivBound_nonneg
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    0 ≤ ballCutoffFDerivBound r R := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  exact mul_nonneg CutoffProfile.derivBound_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (hr.trans hrR.le)) hden.le)

theorem norm_ballCutoffArgumentFDeriv_le
    [InnerProductSpace ℝ E] {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) {x : E}
    (hx : dist x center ≤ R) :
    ‖ballCutoffArgumentFDeriv center r R x‖ ≤
      2 * R / (R ^ 2 - r ^ 2) := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hdist : ‖x - center‖ ≤ R := by
    simpa [dist_eq_norm] using hx
  rw [ballCutoffArgumentFDeriv, norm_smul, RCLike.norm_nsmul ℝ,
    innerSL_apply_norm, nsmul_eq_mul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hden]
  rw [div_eq_mul_inv]
  nlinarith [inv_pos.mpr hden, norm_nonneg (x - center)]

theorem norm_ballCutoffFDeriv_le
    [InnerProductSpace ℝ E] {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (x : E) :
    ‖ballCutoffFDeriv center r R x‖ ≤ ballCutoffFDerivBound r R := by
  by_cases hx : dist x center ≤ R
  · rw [ballCutoffFDeriv, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul
      (CutoffProfile.abs_deriv_le_derivBound _)
      (norm_ballCutoffArgumentFDeriv_le hr hrR hx)
      (norm_nonneg _) CutoffProfile.derivBound_nonneg
  · have harg : 2 ≤ ballCutoffArgument center r R x := by
      have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
      have hR : 0 ≤ R := hr.trans hrR.le
      have hdist : R ≤ ‖x - center‖ := by
        simpa [dist_eq_norm] using (not_le.mp hx).le
      have hsq : R ^ 2 ≤ ‖x - center‖ ^ 2 :=
        (sq_le_sq₀ hR (norm_nonneg _)).2 hdist
      have hquot : 1 ≤
          (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2) := by
        rw [le_div_iff₀ hden]
        linarith
      simp only [ballCutoffArgument]
      linarith
    rw [ballCutoffFDeriv, CutoffProfile.deriv_zero_of_ge harg, zero_smul,
      norm_zero]
    exact ballCutoffFDerivBound_nonneg hr hrR

theorem ballCutoff_contDiff [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) :
    ContDiff ℝ ∞ (ballCutoff center r R) := by
  have hnorm : ContDiff ℝ ∞ (fun x : E ↦ ‖x - center‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have harg : ContDiff ℝ ∞ (ballCutoffArgument center r R) := by
    simpa [ballCutoffArgument] using
      (contDiff_const.add ((hnorm.sub contDiff_const).div_const (R ^ 2 - r ^ 2)))
  simpa [ballCutoffArgument, ballCutoff] using
    CutoffProfile.contDiff.comp harg

theorem ballCutoff_mem_Icc (center : E) (r R : ℝ) (x : E) :
    ballCutoff center r R x ∈ Set.Icc (0 : ℝ) 1 :=
  CutoffProfile.mem_Icc _

theorem ballCutoff_eq_one_of_mem_closedBall
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {x : E} (hx : x ∈ Metric.closedBall center r) :
    ballCutoff center r R x = 1 := by
  apply CutoffProfile.one_of_le_one
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hdist : ‖x - center‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hsq : ‖x - center‖ ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hr).2 hdist
  have hquot : (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsq) hden.le
  simp only [ballCutoffArgument]
  linarith

theorem ballCutoff_eq_zero_of_le_dist
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {x : E} (hx : R ≤ dist x center) :
    ballCutoff center r R x = 0 := by
  apply CutoffProfile.zero_of_two_le
  have hR : 0 ≤ R := hr.trans hrR.le
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hdist : R ≤ ‖x - center‖ := by
    simpa [dist_eq_norm] using hx
  have hsq : R ^ 2 ≤ ‖x - center‖ ^ 2 :=
    (sq_le_sq₀ hR (norm_nonneg _)).2 hdist
  have hquot : 1 ≤ (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2) := by
    rw [le_div_iff₀ hden]
    linarith
  simp only [ballCutoffArgument]
  linarith

theorem ballCutoff_eq_zero_of_not_mem_ball
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {x : E} (hx : x ∉ Metric.ball center R) :
    ballCutoff center r R x = 0 :=
  ballCutoff_eq_zero_of_le_dist hr hrR (by simpa [Metric.mem_ball, dist_comm] using hx)

theorem ballCutoff_support_subset_ball
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    Function.support (ballCutoff center r R) ⊆ Metric.ball center R := by
  intro x hx
  by_contra hxball
  exact hx (ballCutoff_eq_zero_of_not_mem_ball hr hrR hxball)

theorem ballCutoff_tsupport_subset_closedBall
    {center : E} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    tsupport (ballCutoff center r R) ⊆ Metric.closedBall center R := by
  exact (closure_mono (ballCutoff_support_subset_ball hr hrR)).trans
    Metric.closure_ball_subset_closedBall

theorem ballCutoff_hasCompactSupport
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {center : E} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    HasCompactSupport (ballCutoff center r R) := by
  exact (isCompact_closedBall center R).of_isClosed_subset
    isClosed_closure (ballCutoff_tsupport_subset_closedBall hr hrR)

end DifferentialGeometry.Analysis

end
