import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchCage
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBLocalMetrics

set_option autoImplicit false

/-!
# Common live-slot normal-metric convergence

The finite live cage has one common basepoint-distance tail.  On that tail the
normal-radius profile supplies a single phase ball for every live center, so
the finite-Pi local metric compactness theorem extracts all full metric fields
on one shared subsequence.
-/

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace MetricCompactnessInputs

/-- Full normal-coordinate metric fields at all live centers converge on one
common phase ball after one shared subsequence. -/
theorem exists_live_metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) (r : Real) :
    let R := 2 * inp.decay.lambda inp.D 0 * (inp.pack.A r : Real)
    ∃ (psi : Nat → Nat)
        (gInf : E →
          (LiveSlot L inp.pack r → (E →L[Real] E →L[Real] Real))),
      StrictMono psi ∧
      (∀ k (alpha : LiveSlot L inp.pack r),
        inp.decay.dist (L.φ (psi k))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat))
          (X.obj (L.φ (psi k))).basepoint ≤ R) ∧
      ContDiffOn Real (∞ : WithTop ℕ∞) gInf
        (Metric.ball 0 (inp.normalRadius.phaseRadius R)) ∧
      MapCInfConvOnCompacts
        (Metric.ball 0 (inp.normalRadius.phaseRadius R))
        (fun k z alpha ↦ normalCoordMetric (I := I)
          (X.obj (L.φ (psi k)))
          (seqCenterD inp.decay P L (psi k) (alpha.1 : Nat)) z)
        gInf ∧
      ∀ z ∈ Metric.ball (0 : E) (inp.normalRadius.phaseRadius R),
        ∀ alpha v,
          (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf z alpha v v ∧
            gInf z alpha v v ≤ 2 * ‖v‖ ^ 2 := by
  classical
  let R : Real := 2 * inp.decay.lambda inp.D 0 * (inp.pack.A r : Real)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (liveCenters_cage inp.decay inp.hD P inp.realizes L inp.pack r)
  let shift : Nat → Nat := fun k ↦ k + N
  have hshift : StrictMono shift := by
    simpa only [shift] using strictMono_id.add_const N
  let index : Nat → Nat := fun k ↦ L.φ (shift k)
  let X' : PointedRiemannianSeq.{u, uE, uH} (I := I) := X.subseq index
  let input' : NormalCoordMetricBoundInput (I := I) X' :=
    inp.normalBounds.subseq index
  let c : LiveSlot L inp.pack r → ∀ k : Nat, (X'.obj k).M :=
    fun alpha k ↦ seqCenterD inp.decay P L (shift k) (alpha.1 : Nat)
  have hcenter : ∀ k alpha,
      inp.decay.dist (index k) (c alpha k) (X'.obj k).basepoint ≤ R := by
    intro k alpha
    exact hN (shift k) (by simp only [shift]; omega) alpha
  have hdom : ∀ k alpha,
      Metric.ball (0 : E) (inp.normalRadius.phaseRadius R) ⊆
        Metric.ball 0 (input'.radius k (c alpha k)) := by
    intro k alpha
    simpa only [input', X', index, c, PointedRiemannianSeq.subseq] using
      inp.normalRadius.phaseRadius_metric (hcenter k alpha)
  have hsub : ∀ k alpha,
      letI : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
      letI : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
      letI : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
      letI : T2Space (TangentBundle I (X'.obj k).M) :=
        (X'.obj k).t2TangentBundle
      Metric.ball (0 : E) (inp.normalRadius.phaseRadius R) ⊆
        Metric.ball 0
        (Geometry.Riemannian.expMapC2Radius
            (I := I) (X'.obj k).metric (c alpha k)) := by
    intro k alpha
    letI : TopologicalSpace (X'.obj k).M := (X'.obj k).topology
    letI : ChartedSpace H (X'.obj k).M := (X'.obj k).charted
    letI : IsManifold I ∞ (X'.obj k).M := (X'.obj k).smooth
    letI : T2Space (TangentBundle I (X'.obj k).M) :=
      (X'.obj k).t2TangentBundle
    have hquarter := inp.normalRadius.phaseRadius_exp (hcenter k alpha)
    have hquarter' : Metric.ball (0 : E) (inp.normalRadius.phaseRadius R) ⊆
        Metric.ball 0 (Geometry.Riemannian.expMapC2Radius
          (I := I) (X'.obj k).metric (c alpha k) / 4) := by
      simpa only [X', PointedRiemannianSeq.subseq] using hquarter
    exact hquarter'.trans (Metric.ball_subset_ball (by
      nlinarith [Geometry.Riemannian.expMapC2Radius_pos
        (I := I) (X'.obj k).metric (c alpha k)]))
  obtain ⟨phi, gInf, hphi, hgInf, hconv, hequiv⟩ :=
    exists_metric_lim_pi (I := I) input' c Metric.isOpen_ball hdom hsub
  let psi : Nat → Nat := fun k ↦ shift (phi k)
  have hpsi : StrictMono psi := hshift.comp hphi
  refine ⟨psi, gInf, hpsi, ?_, hgInf, ?_, hequiv⟩
  · intro k alpha
    simpa only [psi, c, index, X', PointedRiemannianSeq.subseq] using
      hcenter (phi k) alpha
  · simpa only [psi, X', input', index, c, PointedRiemannianSeq.subseq] using hconv

end MetricCompactnessInputs
end HCGCompactness
end DifferentialGeometry
