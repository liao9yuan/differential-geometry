import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalPhase

set_option autoImplicit false

/-!
# Bilateral normal-coordinate phase flow

This file retains the symmetric time interval supplied by the normalized
Picard argument.  The quantitative endpoint estimate still uses the forward
half, while the negative-time half makes the launch time an interior point for
geodesic realization and uniqueness.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Metric
open scoped Manifold ContDiff NNReal

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- A sufficiently small normal phase ball has one common exact flow on
`[-1, 1]`.  Its forward endpoint retains the same quantitative approximation
to the free diagonal map. -/
theorem exists_normal_biflow
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBoundInput (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (Geometry.Riemannian.expMapC2Radius (I := I) (X.obj k).metric x / 4))
    (q : NNReal) (hq : 0 < q)
    (hqPos : 4 * (q : Real) < r)
    (hqAcc : 3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤ (q : Real)) :
    ∃ Φ : (E × E) → Real → E × E,
      (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ContinuousOn (Φ z) (Icc (-1) 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
        HasDerivWithinAt (Φ z)
          (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
          (Icc (-1) 1) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ioo (-1) 1,
        HasDerivAt (Φ z)
          (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t)) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
        Φ z t ∈ normalPhaseBox r (2 * q)) ∧
      ApproximatesLinearOn (fun z ↦ (z.1, (Φ z 1).1)) PhaseFlow.freeDiag
        (Metric.closedBall (0 : E × E) q)
        (PhaseFlow.phaseErr (normalPhaseK h (2 * q))) := by
  let P : NNReal := 4 * q
  let V : NNReal := 2 * q
  let half : NNReal := 1 / 2
  let A : NNReal :=
    ⟨3 * h.metricC 1 * (V : Real) ^ 2,
      mul_nonneg (mul_nonneg (by norm_num) (h.metricC_nonneg 1)) (sq_nonneg _)⟩
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have hV : 0 < V := by
    dsimp only [V]
    positivity
  have hbox : PhaseFlow.phaseBox (E := E) P V ⊆ normalPhaseBox r V := by
    intro z hz
    refine ⟨?_, hz.2⟩
    rw [mem_ball_zero_iff]
    exact hz.1.trans_lt
      (by simpa only [P, NNReal.coe_mul, NNReal.coe_natCast] using hqPos)
  have haLip : LipschitzOnWith (normalPhaseK h V)
      (normalAccel (I := I) (X.obj k) x) (PhaseFlow.phaseBox P V) :=
    (normalAccel_lip (I := I) h k x hrMetric hrQuarter V).mono hbox
  have haNorm : ∀ z ∈ PhaseFlow.phaseBox (E := E) P V,
      ‖normalAccel (I := I) (X.obj k) x z‖ ≤ (A : Real) := by
    intro z hz
    simpa only [A, NNReal.coe_mk] using
      normalAccel_norm (I := I) h k x hrMetric hrQuarter V z (hbox hz)
  have hVP : V ≤ half * P := by
    rw [← NNReal.coe_le_coe]
    change (2 : Real) * (q : Real) ≤ (1 / 2 : Real) * (4 * (q : Real))
    nlinarith
  have hAV : A ≤ half * V := by
    rw [← NNReal.coe_le_coe]
    change 3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (1 / 2 : Real) * (2 * (q : Real))
    simpa using hqAcc
  have hhalf : (half : Real) ≤ 1 - (half : Real) := by
    norm_num [half]
  obtain ⟨Φ, hΦ⟩ := PhaseFlow.exists_fenced_sym (E := E)
    hP hV haLip haNorm hVP hAV hhalf
  have hqP : q ≤ half * P := by
    rw [← NNReal.coe_le_coe]
    change (q : Real) ≤ (1 / 2 : Real) * (4 * (q : Real))
    nlinarith [q.coe_nonneg]
  have hqV : q ≤ half * V := by
    rw [← NNReal.coe_le_coe]
    change (q : Real) ≤ (1 / 2 : Real) * (2 * (q : Real))
    nlinarith
  have hscale := PhaseFlow.scale_maps_ball (E := E) hP hV hqP hqV
  have hspec : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      Φ z 0 = z ∧
      ContinuousOn (Φ z) (Icc (-1) 1) ∧
      (∀ t ∈ Icc (-1) 1, HasDerivWithinAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
        (Icc (-1) 1) t) ∧
      (∀ t ∈ Ioo (-1) 1, HasDerivAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t)) t) ∧
      ∀ t ∈ Icc (-1) 1, Φ z t ∈ normalPhaseBox r V := by
    intro z hz
    obtain ⟨hΦ0, hΦcont, hΦwithin, hΦat, hΦmem⟩ := hΦ z (hscale hz)
    exact ⟨hΦ0, hΦcont, hΦwithin, hΦat, fun t ht ↦ hbox (hΦmem t ht)⟩
  have hinit : ∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z :=
    fun z hz ↦ (hspec z hz).1
  have hcont : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ContinuousOn (Φ z) (Icc (-1) 1) := fun z hz ↦ (hspec z hz).2.1
  have hwithin : ∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
      HasDerivWithinAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
        (Icc (-1) 1) t := fun z hz ↦ (hspec z hz).2.2.1
  have hderiv : ∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ioo (-1) 1,
      HasDerivAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t)) t :=
    fun z hz ↦ (hspec z hz).2.2.2.1
  have hmem : ∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
      Φ z t ∈ normalPhaseBox r V := fun z hz ↦ (hspec z hz).2.2.2.2
  have hcont01 : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ContinuousOn (Φ z) (Icc 0 1) := by
    intro z hz
    exact (hcont z hz).mono (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
  have hderiv01 : ∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ico 0 1,
      HasDerivWithinAt (Φ z)
        (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
        (Ici t) t := by
    intro z hz t ht
    exact (hderiv z hz t ⟨by linarith [ht.1], ht.2⟩).hasDerivWithinAt
  have happ := normalDiag_approx (I := I) h k x hrMetric hrQuarter V
    hinit hcont01 hderiv01
      (fun z hz t ht ↦ hmem z hz t ⟨by linarith [ht.1], ht.2.le⟩)
  simpa only [V] using
    ⟨Φ, hinit, hcont, hwithin, hderiv, hmem, happ⟩

end HCGCompactness
end DifferentialGeometry
