import DifferentialGeometry.Analysis.Calculus.CutoffProfile
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis

open Set
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E]

def ballCutoff (center : E) (r R : ℝ) (x : E) : ℝ :=
  CutoffProfile.value
    (1 + (‖x - center‖ ^ 2 - r ^ 2) / (R ^ 2 - r ^ 2))

theorem ballCutoff_contDiff [InnerProductSpace ℝ E]
    (center : E) (r R : ℝ) :
    ContDiff ℝ ∞ (ballCutoff center r R) := by
  apply CutoffProfile.contDiff.comp
  have hnorm : ContDiff ℝ ∞ (fun x : E ↦ ‖x - center‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  exact contDiff_const.add ((hnorm.sub contDiff_const).div_const _)

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
