import DifferentialGeometry.Analysis.ODE.PhaseFlowSmallness
import DifferentialGeometry.Analysis.ODE.PhaseEndpointInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.MetricCompactnessInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhase

set_option autoImplicit false

/-!
# Small-radius normal phase error

The normal-coordinate acceleration Lipschitz coefficient is polynomial in the
velocity radius and vanishes at radius zero.  Consequently the quantitative
time-one phase error can be made smaller than any prescribed positive
threshold.
-/

noncomputable section

universe u uE uH

open Filter Set Topology
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace NormalRadiusProfile

/-- A fixed-distance normal phase radius lying one quarter below the common
metric/exponential radius profile. -/
def phaseRadius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real) : Real :=
  h.ratio * hd.mu R / 4

/-- The fixed-distance normal phase radius is positive. -/
theorem phaseRadius_pos
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real) : 0 < h.phaseRadius R := by
  dsimp only [phaseRadius]
  exact div_pos (h.floor_pos R) (by norm_num)

/-- On a fixed distance sublevel, the phase ball lies inside the metric-control
ball. -/
theorem phaseRadius_metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    Metric.ball (0 : E) (h.phaseRadius R) ⊆
      Metric.ball (0 : E) (hb.radius k x) := by
  apply Metric.ball_subset_ball
  calc
    h.phaseRadius R ≤ h.ratio * hd.mu R := by
      dsimp only [phaseRadius]
      nlinarith [h.floor_pos R]
    _ ≤ hb.radius k x := h.floor_le_radius hx

/-- On a fixed distance sublevel, the phase ball also lies inside one quarter
of the named smooth exponential radius. -/
theorem phaseRadius_exp
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) {k : Nat} {x : (X.obj k).M} {R : Real}
    (hx : hd.dist k x (X.obj k).basepoint ≤ R) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    Metric.ball (0 : E) (h.phaseRadius R) ⊆ Metric.ball (0 : E)
      (Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x / 4) := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  apply Metric.ball_subset_ball
  dsimp only [phaseRadius]
  exact div_le_div_of_nonneg_right (h.floor_le_exp hx) (by norm_num)

end NormalRadiusProfile

/-- The normal acceleration Lipschitz coefficient vanishes at zero velocity
radius. -/
@[simp] theorem normalPhaseK_zero
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) : normalPhaseK h 0 = 0 := by
  apply NNReal.eq
  simp [normalPhaseK]
  rfl

/-- The normal acceleration Lipschitz coefficient is continuous in the
velocity radius. -/
theorem normalPhaseK_cont
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) :
    Continuous (normalPhaseK h) := by
  unfold normalPhaseK
  apply Continuous.subtype_mk
  fun_prop

/-- The normal acceleration Lipschitz coefficient tends to zero with the
velocity radius. -/
theorem normalPhaseK_lim
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) :
    Tendsto (normalPhaseK h) (nhds 0) (nhds 0) := by
  have hcont : Tendsto (normalPhaseK h) (nhds (0 : NNReal))
      (nhds (normalPhaseK h 0)) := (normalPhaseK_cont h).continuousAt
  simpa using hcont

/-- The normal-coordinate time-one phase error tends to zero with the velocity
radius. -/
theorem normalPhaseErr_lim
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X) :
    Tendsto (fun R ↦ PhaseFlow.phaseErr (normalPhaseK h R))
      (nhds 0) (nhds 0) :=
  PhaseFlow.phaseErr_tendsto.comp (normalPhaseK_lim h)

/-- Every positive inverse-function threshold eventually dominates the normal
phase endpoint error. -/
theorem normalPhaseErr_lt_ev
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    {eps : NNReal} (heps : 0 < eps) :
    ∀ᶠ R in nhds 0, PhaseFlow.phaseErr (normalPhaseK h R) < eps :=
  normalPhaseErr_lim h (Iio_mem_nhds heps)

/-- Given any positive ordinary radius and endpoint-error threshold, one can
choose a positive phase radius satisfying exactly the two numerical fence
conditions consumed by `exists_normalFlow`, while also meeting the requested
error bound. -/
theorem exists_normal_q_lt
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    {r : Real} (hr : 0 < r) {eps : NNReal} (heps : 0 < eps) :
    ∃ q : NNReal, 0 < q ∧
      4 * (q : Real) < r ∧
      3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real) ∧
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < eps := by
  have htwo : Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < eps :=
    htwo (normalPhaseErr_lt_ev (I := I) h heps)
  obtain ⟨δ, hδ, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := h.metricC 1
  have hC : 0 ≤ C := h.metricC_nonneg 1
  let accelBound : Real := 1 / (24 * (C + 1))
  have hden : 0 < 24 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccelBound : 0 < accelBound := one_div_pos.mpr hden
  let qReal : Real := min (δ / 4) (min (r / 8) accelBound)
  have hqReal : 0 < qReal := by
    dsimp only [qReal]
    exact lt_min (div_pos hδ (by norm_num))
      (lt_min (div_pos hr (by norm_num)) haccelBound)
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have hqδ : qReal ≤ δ / 4 := min_le_left _ _
  have hqRadius : qReal ≤ r / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hqAccel : qReal ≤ accelBound :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqBall : q ∈ Metric.ball (0 : NNReal) δ := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < δ
    rw [sub_zero, abs_of_pos hqReal]
    exact hqδ.trans_lt (div_lt_self hδ (by norm_num))
  have herrQ : PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < eps :=
    herr q hqBall
  have hqRadius' : 4 * qReal < r := by
    nlinarith
  have hqProd : qReal * (24 * (C + 1)) ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [accelBound, one_div] using hqAccel
  have hlinear : 12 * C * qReal ≤ 1 := by
    nlinarith
  have hmul : 0 ≤ qReal * (1 - 12 * C * qReal) :=
    mul_nonneg hqReal.le (sub_nonneg.mpr hlinear)
  refine ⟨q, ?_, ?_, ?_, herrQ⟩
  · exact_mod_cast hqReal
  · simpa only [q, NNReal.coe_mk] using hqRadius'
  · change 3 * C * (2 * qReal) ^ 2 ≤ qReal
    nlinarith

namespace NormalRadiusProfile

/-- The relative normal-radius profile supplies an admissible phase radius for
every positive endpoint-error threshold.  Together with `phaseRadius_metric`
and `phaseRadius_exp`, this gives all radius and numerical inputs to
`exists_normalFlow` on a fixed distance sublevel. -/
theorem exists_phase_q
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) (R : Real)
    {eps : NNReal} (heps : 0 < eps) :
    ∃ q : NNReal, 0 < q ∧
      4 * (q : Real) < h.phaseRadius R ∧
      3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real) ∧
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < eps :=
  exists_normal_q_lt (I := I) hb (h.phaseRadius_pos R) heps

/-- The normal phase radius can be selected at one fixed positive fraction of
the sequence-relative scale.  The accompanying target-radius coefficient is
also uniform in the exhaustion radius. -/
theorem exists_phase_scale
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb) :
    let T : NNReal :=
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹
    ∃ aq aδ : Real,
      0 < aq ∧ 0 < aδ ∧
      ∀ R, 0 ≤ R →
        ∃ q : NNReal,
          (q : Real) = aq * hd.mu R ∧
          6 * (q : Real) < h.phaseRadius R ∧
          3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
            (2 / 3 : Real) * (q : Real) ∧
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T ∧
          aδ * hd.mu R ≤
            ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
              ((q : Real) / 2) := by
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let T : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊⁻¹
  have hT : 0 < T := PhaseFlow.freeDiagInv_pos (E := E)
  have hTReal : (0 : Real) < T := by exact_mod_cast hT
  have hhalfT : 0 < T / 2 := div_pos hT (by norm_num)
  have htwo : Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T / 2 :=
    htwo (normalPhaseErr_lt_ev (I := I) hb hhalfT)
  obtain ⟨eps, heps, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := hb.metricC 1
  have hC : 0 ≤ C := hb.metricC_nonneg 1
  have hμ0 : 0 < hd.mu 0 := hd.mu_pos 0
  let accelBound : Real := 1 / (36 * (C + 1))
  have hden : 0 < 36 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccel : 0 < accelBound := one_div_pos.mpr hden
  let aq : Real := min (h.ratio / 48)
    (min (eps / (2 * hd.mu 0)) (accelBound / hd.mu 0))
  have haq : 0 < aq := by
    dsimp only [aq]
    exact lt_min (div_pos h.ratio_pos (by norm_num))
      (lt_min (div_pos heps (mul_pos (by norm_num) hμ0))
        (div_pos haccel hμ0))
  let aδ : Real := (T : Real) * aq / 4
  have haδ : 0 < aδ := by
    dsimp only [aδ]
    exact div_pos (mul_pos hTReal haq) (by norm_num)
  refine ⟨aq, aδ, haq, haδ, ?_⟩
  intro R hR
  have hμR : 0 < hd.mu R := hd.mu_pos R
  have hμle : hd.mu R ≤ hd.mu 0 := hd.mu_antitone hR
  let qReal : Real := aq * hd.mu R
  have hqReal : 0 < qReal := mul_pos haq hμR
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have haqRatio : aq ≤ h.ratio / 48 := min_le_left _ _
  have haqEps : aq ≤ eps / (2 * hd.mu 0) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have haqAccel : aq ≤ accelBound / hd.mu 0 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqEps : qReal ≤ eps / 2 := by
    calc
      qReal = aq * hd.mu R := rfl
      _ ≤ aq * hd.mu 0 := mul_le_mul_of_nonneg_left hμle haq.le
      _ ≤ (eps / (2 * hd.mu 0)) * hd.mu 0 :=
        mul_le_mul_of_nonneg_right haqEps hμ0.le
      _ = eps / 2 := by field_simp [ne_of_gt hμ0]
  have hqAccel : qReal ≤ accelBound := by
    calc
      qReal = aq * hd.mu R := rfl
      _ ≤ aq * hd.mu 0 := mul_le_mul_of_nonneg_left hμle haq.le
      _ ≤ (accelBound / hd.mu 0) * hd.mu 0 :=
        mul_le_mul_of_nonneg_right haqAccel hμ0.le
      _ = accelBound := by field_simp [ne_of_gt hμ0]
  have hqBall : q ∈ Metric.ball (0 : NNReal) eps := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < eps
    rw [sub_zero, abs_of_pos hqReal]
    exact hqEps.trans_lt (half_lt_self heps)
  have herrQ : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T / 2 :=
    herr q hqBall
  have hqRadius : 6 * (q : Real) < h.phaseRadius R := by
    have haRatio : 6 * aq < h.ratio / 4 := by
      nlinarith [h.ratio_pos]
    calc
      6 * (q : Real) = (6 * aq) * hd.mu R := by
        change 6 * qReal = _
        dsimp only [qReal]
        ring
      _ < (h.ratio / 4) * hd.mu R := mul_lt_mul_of_pos_right haRatio hμR
      _ = h.phaseRadius R := by
        dsimp only [phaseRadius]
        ring
  have hqProd : qReal * (36 * (C + 1)) ≤ 1 := by
    calc
      qReal * (36 * (C + 1)) ≤ accelBound * (36 * (C + 1)) :=
        mul_le_mul_of_nonneg_right hqAccel hden.le
      _ = 1 := by
        dsimp only [accelBound]
        field_simp [ne_of_gt hden]
  have hlinear : 18 * C * qReal ≤ 1 := by
    nlinarith [mul_nonneg hC hqReal.le]
  have hmul : 0 ≤ qReal * (1 - 18 * C * qReal) :=
    mul_nonneg hqReal.le (sub_nonneg.mpr hlinear)
  have hqAcc : 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real) := by
    change 3 * C * (2 * qReal) ^ 2 ≤ (2 / 3 : Real) * qReal
    nlinarith
  have herrOut : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T := by
    calc
      PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) < T / 2 := herrQ
      _ < T := by exact_mod_cast (half_lt_self hTReal)
  have herrReal :
      (PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : Real) < (T : Real) / 2 := by
    exact_mod_cast herrQ
  have hmargin : (T : Real) / 2 ≤
      ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) := by
    rw [NNReal.coe_sub herrOut.le]
    linarith
  have hδlower : aδ * hd.mu R ≤
      ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) := by
    calc
      aδ * hd.mu R = ((T : Real) / 2) * (qReal / 2) := by
        dsimp only [aδ, qReal]
        ring
      _ ≤ ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
          (qReal / 2) :=
        mul_le_mul_of_nonneg_right hmargin (div_nonneg hqReal.le (by norm_num))
      _ = ((T - PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
          ((q : Real) / 2) := rfl
  exact ⟨q, rfl, hqRadius, hqAcc, herrOut, hδlower⟩

end NormalRadiusProfile

end HCGCompactness
end DifferentialGeometry
