import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchCage
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAveragePOU

set_option autoImplicit false

/-!
# Finite-hat readout on the selected normal branch

This file joins the sequence tail of selected minimizing branches to the
pair-index tail of the finite POU average.  The geometric strict-convexity
input remains explicit; no endpoint radius hypothesis is introduced.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- A finite-hat configuration has a selected live branch whose readout
vanishes at its center of mass. -/
def HasHatCmEqn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (n : Nat)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (q : LiveSlot L pb r → NNReal) (δ : LiveSlot L pb r → Real)
    (mu : Fin (pb.A r) → Real)
    (pts : Fin (pb.A r) → (X.obj (L.φ n)).M)
    (join : (X.obj (L.φ n)).M → (X.obj (L.φ n)).M → Real →
      (X.obj (L.φ n)).M)
    (x : (X.obj (L.φ n)).M) (rad : Real)
    (hcm :
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
        (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
      letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
        Manifold.metrizableSpace I (X.obj (L.φ n)).M
      letI : T3Space (X.obj (L.φ n)).M := inferInstance
      letI : RiemannianBundle
          (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
        (X.obj (L.φ n)).riemBundle (I := I)
      letI : (z : (X.obj (L.φ n)).M) →
          InnerProductSpace Real (TangentSpace I z) :=
        (X.obj (L.φ n)).riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
        (X.obj (L.φ n)).riemBundle_cont (I := I)
      letI : EMetricSpace (X.obj (L.φ n)).M :=
        (X.obj (L.φ n)).emetricSpace (I := I)
      letI : CompleteSpace (X.obj (L.φ n)).M :=
        MetricComplete.complete (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n))
      letI : MetricSpace (X.obj (L.φ n)).M :=
        HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
      CenterInput (I := I) (X.obj (L.φ n)).metric mu pts join x rad) : Prop :=
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle (I := I)
  letI : (z : (X.obj (L.φ n)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ n)).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj (L.φ n)).M :=
    (X.obj (L.φ n)).emetricSpace (I := I)
  letI : CompleteSpace (X.obj (L.φ n)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ n))
      (hcomplete.complete (L.φ n))
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  ∃ gamma : LiveSlot L pb r,
    ∃ (hq : 0 < q gamma)
        (e : OpenPartialHomeomorph (E × E) (E × E))
        (he : IsNormalDiag (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n)) (hconn (L.φ n))
          (seqCenterD hd P L n (gamma.1 : Nat)) (q gamma) (δ gamma) e),
      NormalDiagFence (I := I) (X.obj (L.φ n))
          (seqCenterD hd P L n (gamma.1 : Nat)) (q gamma) e ∧
        let x0 := seqCenterD hd P L n (gamma.1 : Nat)
        let B := IsNormalDiag.toBranch (I := I) (X.obj (L.φ n))
          (hcomplete.complete (L.φ n)) (hconn (L.φ n)) x0 hq he
        let c := centerOfMass (I := I) (X.obj (L.φ n)).metric
          mu pts join x rad hcm
        let xi : Fin (pb.A r) → E := fun i =>
          NormalCoordinates.normalChartAt
            (I := I) (X.obj (L.φ n)).metric x0 (pts i)
        chartCmEqnB (I := I) (X.obj (L.φ n)).metric
          (normal_enorm (I := I) (X.obj (L.φ n))) x0 B
          (NormalCoordinates.normalChartAt
            (I := I) (X.obj (L.φ n)).metric x0 c)
          (mu, xi) = 0

/-- Select one minimizing scale before `D`, then join the sequence tail of its
live branches with the pair-index tail of the actual finite-hat POU average.

The final `StrictDistInput` is deliberately a continuation parameter: it is
the independent Hessian/convexity frontier, whereas every radius and branch
condition in this statement is produced internally. -/
theorem exists_hat_cm_tail
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (hprof : NormalRadiusProfile hd hb)
    (hre : hd.RealizesEdist)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    ∃ aMin : Real, 0 < aMin ∧
      ∀ {D : Real} (_hD : 0 < D)
        (_hphys : 8 * Real.exp hd.C < aMin * D)
        (P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j))
        (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real),
        ∃ q : LiveSlot L pb r → NNReal,
          ∃ δ : LiveSlot L pb r → Real,
            (∀ gamma : LiveSlot L pb r,
              let Rgamma := L.rInf (gamma.1 : Nat) + 1
              let rhoMin := aMin * hd.mu Rgamma
              0 < q gamma ∧ 0 < δ gamma ∧ 0 < rhoMin ∧
                2 * rhoMin < (q gamma : Real)) ∧
            ∀ᶠ n in Filter.atTop,
              letI : TopologicalSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).topology
              letI : ChartedSpace H (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).charted
              letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).smooth
              letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
                (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
              letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).sigmaCompact
              letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
              letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
              letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                (X.obj (L.φ n)).t2TangentBundle
              letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
                Manifold.metrizableSpace I (X.obj (L.φ n)).M
              letI : T3Space (X.obj (L.φ n)).M := inferInstance
              letI : RiemannianBundle
                  (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                (X.obj (L.φ n)).riemBundle (I := I)
              letI : (x : (X.obj (L.φ n)).M) →
                  InnerProductSpace Real (TangentSpace I x) :=
                (X.obj (L.φ n)).riemInner (I := I)
              letI : IsContinuousRiemannianBundle E
                  (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                (X.obj (L.φ n)).riemBundle_cont (I := I)
              letI : EMetricSpace (X.obj (L.φ n)).M :=
                (X.obj (L.φ n)).emetricSpace (I := I)
              letI : CompleteSpace (X.obj (L.φ n)).M :=
                MetricComplete.complete (I := I) (X.obj (L.φ n))
                  (hcomplete.complete (L.φ n))
              letI : MetricSpace (X.obj (L.φ n)).M :=
                HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
              (∀ gamma : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
                seqCenter hd D P (L.φ n) (gamma : Nat) = some c →
                  c = seqCenterD hd P L n (gamma : Nat) ∧
                    4 * L.lamInf (gamma : Nat) <
                      expRadiusGp (I := I) (X.obj (L.φ n)).metric c) ∧
              ∀ (rho :
                  letI : TopologicalSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).topology
                  letI : ChartedSpace H (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).charted
                  letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).smooth
                  letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).sigmaCompact
                  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
                  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
                  SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ n)).M
                    (Metric.closedBall (X.obj (L.φ n)).basepoint r))
                (_hrho :
                  letI : TopologicalSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).topology
                  letI : ChartedSpace H (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).charted
                  letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).smooth
                  letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).sigmaCompact
                  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
                  letI : MetricSpace (X.obj (L.φ n)).M := (P (L.φ n)).ms
                  rho.IsSubordinate (fun gamma : Fin (pb.A r) =>
                    (NetLimitData.hatBall (I := I) (X := X) hd D P L pb r n gamma :
                      Set (X.obj (L.φ n)).M)))
                (ptsSeq : Nat → Nat → (X.obj (L.φ n)).M → Fin (pb.A r) →
                  (X.obj (L.φ n)).M)
                (_hpts :
                  letI : TopologicalSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).topology
                  letI : ChartedSpace H (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).charted
                  letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).smooth
                  letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).sigmaCompact
                  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
                  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                    (X.obj (L.φ n)).t2TangentBundle
                  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
                  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
                    Manifold.metrizableSpace I (X.obj (L.φ n)).M
                  letI : T3Space (X.obj (L.φ n)).M := inferInstance
                  letI : RiemannianBundle
                      (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                    (X.obj (L.φ n)).riemBundle (I := I)
                  letI : (x : (X.obj (L.φ n)).M) →
                      InnerProductSpace Real (TangentSpace I x) :=
                    (X.obj (L.φ n)).riemInner (I := I)
                  letI : IsContinuousRiemannianBundle E
                      (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                    (X.obj (L.φ n)).riemBundle_cont (I := I)
                  letI : EMetricSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).emetricSpace (I := I)
                  letI : CompleteSpace (X.obj (L.φ n)).M :=
                    MetricComplete.complete (I := I) (X.obj (L.φ n))
                      (hcomplete.complete (L.φ n))
                  letI : MetricSpace (X.obj (L.φ n)).M :=
                    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
                  ∀ gamma : Fin (pb.A r), ∀ eps : Real, eps > 0 → ∃ N : Nat,
                    ∀ a ≥ N, ∀ b ≥ N, ∀ x : (X.obj (L.φ n)).M,
                      x ∈ NetLimitData.hatSourceBall (I := I) hd P L r n →
                        x ∈ (NetLimitData.hatBall
                          (I := I) (X := X) hd D P L pb r n gamma :
                            Set (X.obj (L.φ n)).M) →
                          dist x (ptsSeq a b x gamma) < eps),
                  letI : TopologicalSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).topology
                  letI : ChartedSpace H (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).charted
                  letI : IsManifold I ∞ (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).smooth
                  letI : SigmaCompactSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).sigmaCompact
                  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
                  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
                    (X.obj (L.φ n)).t2TangentBundle
                  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
                  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
                    Manifold.metrizableSpace I (X.obj (L.φ n)).M
                  letI : T3Space (X.obj (L.φ n)).M := inferInstance
                  letI : RiemannianBundle
                      (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                    (X.obj (L.φ n)).riemBundle (I := I)
                  letI : (x : (X.obj (L.φ n)).M) →
                      InnerProductSpace Real (TangentSpace I x) :=
                    (X.obj (L.φ n)).riemInner (I := I)
                  letI : IsContinuousRiemannianBundle E
                      (fun x : (X.obj (L.φ n)).M ↦ TangentSpace I x) :=
                    (X.obj (L.φ n)).riemBundle_cont (I := I)
                  letI : EMetricSpace (X.obj (L.φ n)).M :=
                    (X.obj (L.φ n)).emetricSpace (I := I)
                  letI : CompleteSpace (X.obj (L.φ n)).M :=
                    MetricComplete.complete (I := I) (X.obj (L.φ n))
                      (hcomplete.complete (L.φ n))
                  letI : MetricSpace (X.obj (L.φ n)).M :=
                    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
                  ∃ radSeq : Nat → Nat → (X.obj (L.φ n)).M → Real,
                    (∀ a b x,
                      x ∈ NetLimitData.hatSourceBall (I := I) hd P L r n →
                        0 < radSeq a b x) ∧
                    (∀ a b x,
                      x ∈ NetLimitData.hatSourceBall (I := I) hd P L r n →
                        ∀ gamma : Fin (pb.A r), rho gamma x ≠ 0 →
                          dist x (ptsSeq a b x gamma) < radSeq a b x) ∧
                    (∀ eps : Real, eps > 0 → ∃ N : Nat,
                      ∀ a ≥ N, ∀ b ≥ N, ∀ x : (X.obj (L.φ n)).M,
                        x ∈ NetLimitData.hatSourceBall (I := I) hd P L r n →
                          radSeq a b x < eps) ∧
                    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ N,
                      ∀ x : (X.obj (L.φ n)).M,
                        x ∈ NetLimitData.hatSourceBall (I := I) hd P L r n →
                          ∀ (join : (X.obj (L.φ n)).M → (X.obj (L.φ n)).M →
                            Real → (X.obj (L.φ n)).M),
                            StrictDistInput (I := I) (X.obj (L.φ n)).metric
                              (centerAverage.activeFill
                                (fun y gamma ↦ rho gamma y) (ptsSeq a b)
                                (fun y ↦ y) x)
                              join x (radSeq a b x) →
                              ∃ hcm : CenterInput (I := I)
                                (X.obj (L.φ n)).metric (fun gamma ↦ rho gamma x)
                                (centerAverage.activeFill
                                  (fun y gamma ↦ rho gamma y) (ptsSeq a b)
                                  (fun y ↦ y) x)
                                join x (radSeq a b x),
                                HasHatCmEqn (I := I) hd P L pb r n hcomplete hconn
                                  q δ (fun gamma ↦ rho gamma x)
                                  (centerAverage.activeFill
                                    (fun y gamma ↦ rho gamma y) (ptsSeq a b)
                                    (fun y ↦ y) x)
                                  join x (radSeq a b x) hcm := by
  classical
  obtain ⟨aMin, haMin, hmin⟩ :=
    exists_slot_min (I := I) hprof hre hcomplete hconn
  refine ⟨aMin, haMin, ?_⟩
  intro D _hD _hphys P L pb r
  obtain ⟨q, δ, hqdata, hbranch⟩ := hmin P L pb r
  refine ⟨q, δ, hqdata, ?_⟩
  filter_upwards [hbranch, aliveSlots_tail hd P L pb r] with n hn hstable
  letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
  letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
  letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
  letI : IsManifold I 1 (X.obj (L.φ n)).M := IsManifold.of_le
    (I := I) (M := (X.obj (L.φ n)).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).sigmaCompact
  letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
  letI : ConnectedSpace (X.obj (L.φ n)).M := hconn (L.φ n)
  letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
    (X.obj (L.φ n)).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj (L.φ n)).M :=
    Manifold.metrizableSpace I (X.obj (L.φ n)).M
  letI : T3Space (X.obj (L.φ n)).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle (I := I)
  letI : (z : (X.obj (L.φ n)).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj (L.φ n)).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj (L.φ n)).M ↦ TangentSpace I z) :=
    (X.obj (L.φ n)).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj (L.φ n)).M :=
    (X.obj (L.φ n)).emetricSpace (I := I)
  letI : CompleteSpace (X.obj (L.φ n)).M :=
    MetricComplete.complete (I := I) (X.obj (L.φ n))
      (hcomplete.complete (L.φ n))
  letI : MetricSpace (X.obj (L.φ n)).M :=
    HopfRinow.riemMetricSpace (I := I) (M := (X.obj (L.φ n)).M)
  constructor
  · intro gamma c hc
    have halive : L.alive (gamma : Nat) = true := by
      simpa [hc] using (hstable gamma).symm
    let gammaLive : LiveSlot L pb r := ⟨gamma, halive⟩
    have hcD : c = seqCenterD hd P L n (gamma : Nat) := by
      simp [seqCenterD, hc]
    refine ⟨hcD, ?_⟩
    have hfloor := (hn gammaLive).2.2
    rw [hcD]
    exact (lamInf_lt_halfMin hd _hD _hphys P L (gamma : Nat)).trans_le
      (by simpa only [gammaLive] using hfloor)
  · intro rho _hrho ptsSeq _hpts
    obtain ⟨radSeq, hpos, hactive, htail⟩ :=
      NetLimitData.exists_hat_radius (I := I) hd P L pb r n rho _hrho ptsSeq
        (hconn (L.φ n)) _hpts
    refine ⟨radSeq, hpos, hactive, htail, ?_⟩
    obtain ⟨N, hN⟩ := exists_rad_cage hd _hD haMin _hphys P L pb r n
      (NetLimitData.hatSourceBall (I := I) hd P L r n) radSeq htail
    refine ⟨N, ?_⟩
    intro a ha b hbN x hx join hstrict
    let weights : (X.obj (L.φ n)).M → Fin (pb.A r) → Real :=
      fun y gamma ↦ rho gamma y
    let pts := centerAverage.activeFill weights (ptsSeq a b) (fun y ↦ y) x
    let hcomplete' :=
      NetLimitData.sourceComplete (I := I) hd P L n hcomplete (hconn (L.φ n))
    have hdata := NetLimitData.hatPOUDataTwo
      (I := I) hd P L pb r n rho _hrho a b hx
    have hcm : CenterInput (I := I) (X.obj (L.φ n)).metric
        (fun gamma ↦ rho gamma x) pts join x (radSeq a b x) := by
      simpa only [weights, pts] using
        centerAverage.inputOfFillSelf (I := I)
          (g := (X.obj (L.φ n)).metric) (μ := weights)
          (pts := ptsSeq a b) (join := join) (r := radSeq a b)
          (qstar := fun y ↦ y) x hcomplete' (hpos a b x hx)
          (hactive a b x hx) hdata.1.1 hdata.1.2.1 hstrict
    refine ⟨hcm, ?_⟩
    have hout := exists_hat_cm_eqn (I := I) hd P hre L pb r n hcomplete hconn
      q δ hstable hqdata hn (fun gamma ↦ rho gamma x) pts join x
      (radSeq a b x) hcm hdata.2 (hN a ha b hbN x hx)
    simpa only [HasHatCmEqn] using hout

end HCGCompactness
end DifferentialGeometry
