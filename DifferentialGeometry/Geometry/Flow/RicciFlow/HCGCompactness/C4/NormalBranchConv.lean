import DifferentialGeometry.Analysis.Calculus.MovingInverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalLimitPhase

set_option autoImplicit false

/-!
# Exact inverse convergence for selected normal branches

This file is the HCG-facing adapter from full normal-metric and endpoint
convergence to the generic moving exact-inverse theorem.  The limiting phase
and its endpoint branch remain explicit producer data.
-/

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace NormalRadiusProfile

/-- Exact inverse branches of selected normal diagonal maps converge on a
smaller common target ball once a confined limiting phase and endpoint branch
have been produced. -/
theorem exists_diagInv_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    (qStage qInf : NNReal) (hqInf : 0 < qInf)
    (hqInf_lt : qInf < qStage) (delta deltaInf : Real)
    (hdelta : 0 < delta) (hdeltaInf : 0 < deltaInf)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (h.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (h.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (h.phaseRadius R))
      (fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)) gInf)
    {Φ : Nat → (E × E) → Real → E × E}
    {ΦInf : (E × E) → Real → E × E}
    {e : Nat → OpenPartialHomeomorph (E × E) (E × E)}
    {eInf : OpenPartialHomeomorph (E × E) (E × E)}
    (hΦ : ∀ n z, z ∈ Metric.closedBall (0 : E × E) qStage →
      Φ n z 0 = z ∧
      IsIntegralCurveOn (Φ n z)
        (fun _ ↦ MetricKoszul.metricSpray
          (normalCoordMetric (I := I) (X.obj n) (c n))) (Icc 0 1))
    (hΦInf : ∀ z, z ∈ Metric.closedBall (0 : E × E) qInf →
      ΦInf z 0 = z ∧
      IsIntegralCurveOn (ΦInf z)
        (fun _ ↦ MetricKoszul.metricSpray gInf) (Icc 0 1))
    (hstay : ∀ n z, z ∈ Metric.closedBall (0 : E × E) qStage →
      ∀ t ∈ Icc (0 : Real) 1,
        (Φ n z t).1 ∈ Metric.ball 0 (h.phaseRadius R))
    (hstayInf : ∀ z, z ∈ Metric.closedBall (0 : E × E) qInf →
      ∀ t ∈ Icc (0 : Real) 1,
        (ΦInf z t).1 ∈ Metric.ball 0 (h.phaseRadius R))
    (he : ∀ n, (e n : E × E → E × E) =
      fun z ↦ (z.1, (Φ n z 1).1))
    (heInf : (eInf : E × E → E × E) =
      fun z ↦ (z.1, (ΦInf z 1).1))
    (hdiag : ∀ n, IsNormalDiag (I := I) (X.obj n)
      (hcomplete.complete n) (hconn n) (c n) qStage delta (e n))
    (hInf_source : eInf.source = Metric.ball (0 : E × E) qInf)
    (hInf_zero : eInf 0 = 0)
    (hInf_cd : ContDiffOn Real ∞ (eInf : E × E → E × E)
      eInf.source)
    (hInf_target : Metric.closedBall (0 : E × E) deltaInf ⊆
      eInf.target)
    (hInf_symm_cd : ContDiffOn Real ∞ eInf.symm eInf.target) :
    MapCInfConvOnCompacts (Metric.ball (0 : E × E) qInf)
        (fun n ↦ (e n : E × E → E × E)) eInf ∧
      ∃ delta₀ : Real,
        0 < delta₀ ∧ delta₀ < min delta deltaInf ∧
        eInf.symm '' Metric.closedBall 0 delta₀ ⊆
          Metric.ball 0 qInf ∧
        Filter.Eventually
          (fun n : Nat ↦ Set.MapsTo (e n).symm
            (Metric.closedBall 0 delta₀)
            (Metric.ball 0 qInf)) Filter.atTop ∧
        MapCInfConvOnCompacts (Metric.ball 0 delta₀)
          (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm := by
  let Q : Set (E × E) := Metric.ball 0 qInf
  have hqInfReal : (0 : Real) < qInf := by exact_mod_cast hqInf
  have hqInfStage : (qInf : Real) < qStage := by exact_mod_cast hqInf_lt
  have hQStage : Q ⊆ Metric.closedBall (0 : E × E) qStage := by
    intro z hz
    change dist z 0 < (qInf : Real) at hz
    change dist z 0 ≤ (qStage : Real)
    linarith
  have hQInf : Q ⊆ Metric.closedBall (0 : E × E) qInf := by
    intro z hz
    exact Metric.ball_subset_closedBall hz
  have hforwardFormula := h.diag_end_conv R c hc Metric.isOpen_ball
    hgInf_cd hgInf_lo hg_conv
    (fun n z hz ↦ hΦ n z (hQStage hz))
    (fun z hz ↦ hΦInf z (hQInf hz))
    (fun n z hz ↦ hstay n z (hQStage hz))
    (fun z hz ↦ hstayInf z (hQInf hz)) he
  have hforward : MapCInfConvOnCompacts Q
      (fun n ↦ (e n : E × E → E × E)) eInf :=
    hforwardFormula.congr Metric.isOpen_ball
      (fun _n _z _hz ↦ rfl)
      (fun z _hz ↦ congrFun heInf z)
  have hclosureQ : closure Q ⊆ Metric.ball (0 : E × E) qStage := by
    change closure (Metric.ball (0 : E × E) qInf) ⊆
      Metric.ball 0 qStage
    rw [closure_ball 0 hqInfReal.ne']
    intro z hz
    rw [Metric.mem_closedBall, Metric.mem_ball] at *
    linarith
  have hsource : ∀ᶠ n in Filter.atTop, closure Q ⊆ (e n).source :=
    Filter.Eventually.of_forall fun n ↦ by
      rw [(hdiag n).1]
      exact hclosureQ
  have hstage_cd : ∀ n,
      ContDiffOn Real ∞ (e n : E × E → E × E) Q := by
    intro n
    exact (hdiag n).2.2.1.mono fun z hz ↦ by
      rw [(hdiag n).1]
      exact hclosureQ (subset_closure hz)
  have htarget : ∀ n,
      Metric.closedBall (0 : E × E) (min delta deltaInf) ⊆
        (e n).target := by
    intro n
    exact (Metric.closedBall_subset_closedBall (min_le_left delta deltaInf)).trans
      (hdiag n).2.2.2.1
  have htargetInf : Metric.closedBall (0 : E × E)
      (min delta deltaInf) ⊆ eInf.target :=
    (Metric.closedBall_subset_closedBall (min_le_right delta deltaInf)).trans hInf_target
  have hInf_cd' : ContDiffOn Real ∞
      (eInf : E × E → E × E) (interior eInf.source) :=
    hInf_cd.mono interior_subset
  have hInf_symm_cd' : ContDiffOn Real ∞ eInf.symm
      (Metric.ball (0 : E × E) (min delta deltaInf)) :=
    hInf_symm_cd.mono <|
      Metric.ball_subset_closedBall.trans <|
        (Metric.closedBall_subset_closedBall
          (min_le_right delta deltaInf)).trans hInf_target
  have hzero_source : (0 : E × E) ∈ eInf.source := by
    rw [hInf_source]
    simpa only [Metric.mem_ball, dist_self] using hqInfReal
  have hbase_eq : eInf.symm 0 = 0 := by
    have hleft := eInf.left_inv hzero_source
    simpa only [hInf_zero] using hleft
  have hbase : eInf.symm 0 ∈ Q := by
    change dist (eInf.symm 0) 0 < (qInf : Real)
    rw [hbase_eq]
    simpa only [dist_self] using hqInfReal
  refine ⟨hforward, ?_⟩
  exact Analysis.OpenPartialHomeomorph.exists_symm_convOn_ball Metric.isOpen_ball
    hforward hsource hstage_cd (lt_min hdelta hdeltaInf) htarget
    htargetInf hInf_cd' hInf_symm_cd' hbase

/-- A convergent normal-coordinate metric family admits matched stage and
limit diagonal branches whose forward and exact inverse maps converge on
common balls. -/
theorem exists_diagPair_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) (c : ∀ n : Nat, (X.obj n).M)
    (hc : ∀ n, hd.dist n (c n) (X.obj n).basepoint ≤ R)
    {gInf : E → E →L[Real] E →L[Real] Real}
    (hgInf_cd : ContDiffOn Real ∞ gInf
      (Metric.ball 0 (h.phaseRadius R)))
    (hgInf_lo : ∀ z ∈ Metric.ball (0 : E) (h.phaseRadius R), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z v v)
    (hg_conv : MapCInfConvOnCompacts
      (Metric.ball 0 (h.phaseRadius R))
      (fun n ↦ normalCoordMetric (I := I) (X.obj n) (c n)) gInf) :
    ∃ (qStage qInf : NNReal) (deltaStage deltaInf : Real)
        (e : Nat → OpenPartialHomeomorph (E × E) (E × E))
        (eInf : OpenPartialHomeomorph (E × E) (E × E)),
      0 < qStage ∧ 0 < qInf ∧ qInf < qStage ∧
      0 < deltaStage ∧ 0 < deltaInf ∧
      (∀ n, IsNormalDiag (I := I) (X.obj n)
        (hcomplete.complete n) (hconn n) (c n) qStage deltaStage (e n)) ∧
      eInf.source = Metric.ball (0 : E × E) qInf ∧
      eInf 0 = 0 ∧
      Metric.closedBall (0 : E × E) deltaInf ⊆ eInf.target ∧
      ContDiffOn Real ∞ (eInf : E × E → E × E) eInf.source ∧
      ContDiffOn Real ∞ eInf.symm eInf.target ∧
      MapCInfConvOnCompacts (Metric.ball (0 : E × E) qInf)
        (fun n ↦ (e n : E × E → E × E)) eInf ∧
      ∃ delta₀ : Real,
        0 < delta₀ ∧ delta₀ < min deltaStage deltaInf ∧
        eInf.symm '' Metric.closedBall 0 delta₀ ⊆
          Metric.ball 0 qInf ∧
        Filter.Eventually
          (fun n : Nat ↦ Set.MapsTo (e n).symm
            (Metric.closedBall 0 delta₀) (Metric.ball 0 qInf))
          Filter.atTop ∧
      MapCInfConvOnCompacts (Metric.ball 0 delta₀)
          (fun n ↦ ((e n).symm : E × E → E × E)) eInf.symm := by
  classical
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  obtain ⟨qStage, deltaStage, hqStage, _hqStageRadius, hdeltaStage,
      _hdeltaStageEq, hflow⟩ := h.exists_uniform_flow hcomplete hconn R
  choose Φ e hΦ0 hΦcurve hΦstay he hdiag using
    fun n ↦ hflow n (c n) (hc n)
  let eps : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊⁻¹
  have heps : 0 < eps := PhaseFlow.freeDiagInv_pos (E := E)
  have hfourStage : (0 : Real) < 4 * (qStage : Real) := by positivity
  have hr : 0 < min (h.phaseRadius R) (4 * (qStage : Real)) :=
    lt_min (h.phaseRadius_pos R) hfourStage
  obtain ⟨qInf, hqInf, hqInfSmall, hqInfAcc, hqInfErr⟩ :=
    exists_normal_q_lt (I := I) hb hr heps
  have hqInfRadius : 4 * (qInf : Real) < h.phaseRadius R :=
    hqInfSmall.trans_le (min_le_left _ _)
  have hqInfStageReal : (qInf : Real) < qStage := by
    have hsmall : 4 * (qInf : Real) < 4 * (qStage : Real) :=
      hqInfSmall.trans_le (min_le_right _ _)
    linarith
  have hqInfStage : qInf < qStage := by exact_mod_cast hqInfStageReal
  obtain ⟨ΦInf, eInf, deltaInf, hdeltaInf, hΦInf0, hΦInfCurve,
      hΦInfStay, hInfSource, hInfZero, heInf, hInfTarget,
      hInfSmooth, hInfSymmSmooth⟩ :=
    h.exists_limit_diag R c hc hgInf_cd hgInf_lo hg_conv qInf hqInf
      hqInfRadius hqInfAcc hqInfErr
  obtain ⟨hforward, delta₀, hdelta₀, hdelta₀lt, hInfMaps,
      hstageMaps, hinverse⟩ :=
    h.exists_diagInv_conv hcomplete hconn R c hc qStage qInf hqInf
      hqInfStage deltaStage deltaInf hdeltaStage hdeltaInf
      hgInf_cd hgInf_lo hg_conv
      (fun n z hz ↦ ⟨hΦ0 n z hz, hΦcurve n z hz⟩)
      (fun z hz ↦ ⟨hΦInf0 z hz, hΦInfCurve z hz⟩)
      hΦstay hΦInfStay he heInf hdiag hInfSource hInfZero
      hInfSmooth hInfTarget hInfSymmSmooth
  exact ⟨qStage, qInf, deltaStage, deltaInf, e, eInf, hqStage, hqInf,
    hqInfStage, hdeltaStage, hdeltaInf, hdiag, hInfSource, hInfZero,
    hInfTarget, hInfSmooth, hInfSymmSmooth, hforward, delta₀, hdelta₀,
    hdelta₀lt, hInfMaps, hstageMaps, hinverse⟩

end NormalRadiusProfile
end HCGCompactness
end DifferentialGeometry
