import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalDiagBranch
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.NormalBranchScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCAtomConv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCSmoothness

set_option autoImplicit false

/-!
# Finite-configuration containment in the quantitative normal branch

This file joins the center-of-mass distance ledger to the selected quantitative
normal branch. It contains no new geometric hypothesis.
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

/-- A stabilized live center eventually obeys the explicit ordered-net
basepoint-distance bound. -/
theorem seqCenterD_dist_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (gamma : Nat) (hgamma : L.alive gamma = true) :
    ∀ᶠ k in Filter.atTop,
      hd.dist (L.φ k) (seqCenterD hd P L k gamma)
          (X.obj (L.φ k)).basepoint ≤
        2 * hd.lambda D 0 * (gamma : Real) := by
  filter_upwards [seqCenterD_live hd P L gamma hgamma] with k hk
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  haveI : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  rw [← ProperMetricOn.dist_eq hd hre P (L.φ k)]
  have hr : seqRadius hd D P (L.φ k) gamma =
      dist (seqCenterD hd P L k gamma) (X.obj (L.φ k)).basepoint := by
    unfold seqRadius
    exact OrderedNet.netRadius_of_center _ _ _ gamma hk
  rw [← hr]
  exact (seqRadius_mem hd hD P (L.φ k) gamma).2

/-- All stabilized live centers obey their ordered-net bounds on one common
tail. -/
theorem liveCenters_dist_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
      hd.dist (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat))
          (X.obj (L.φ k)).basepoint ≤
        2 * hd.lambda D 0 * (gamma.1 : Real) :=
  Filter.eventually_all.mpr fun gamma =>
    seqCenterD_dist_le hd hD P hre L (gamma.1 : Nat) gamma.2

/-- On one common tail, every live center lies in the fixed packing-cage
sublevel. -/
theorem liveCenters_cage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) :
    ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
      hd.dist (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat))
          (X.obj (L.φ k)).basepoint ≤
        2 * hd.lambda D 0 * (pb.A r : Real) := by
  filter_upwards [liveCenters_dist_le hd hD P hre L pb r] with k hk
  intro gamma
  refine (hk gamma).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast Nat.le_of_lt gamma.1.isLt
  · exact (mul_pos (by norm_num) (hd.lambda_pos hD 0)).le

/-- The relative normal-radius profile supplies one selected quantitative branch
domain for every live center on a common tail. -/
theorem exists_live_dom
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (hre : hd.RealizesEdist) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real)
    {hb : NormalCoordMetricBoundInput (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    ∃ aρ : Real, 0 < aρ ∧ ∃ (q : NNReal) (δ : Real),
      ∀ᶠ k in Filter.atTop, ∀ gamma : LiveSlot L pb r,
        HasNormalBranchDom (I := I) (X.obj (L.φ k))
          (hcomplete.complete (L.φ k)) (hconn (L.φ k))
          (seqCenterD hd P L k (gamma.1 : Nat)) q δ
          (aρ * hd.mu (2 * hd.lambda D 0 * (pb.A r : Real))) := by
  obtain ⟨aq, aδ, aρ, haq, haδ, haρ, hscale⟩ :=
    normalBrScale (I := I) h hcomplete hconn
  have hR : 0 ≤ 2 * hd.lambda D 0 * (pb.A r : Real) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (hd.lambda_pos hD 0).le) (by positivity)
  obtain ⟨q, δ, hq, hδ, hqeq, hδlower, hqWide, hdom⟩ :=
    hscale (2 * hd.lambda D 0 * (pb.A r : Real)) hR
  refine ⟨aρ, haρ, q, δ, ?_⟩
  filter_upwards [liveCenters_cage hd hD P hre L pb r] with k hk
  exact fun gamma => hdom (L.φ k) (seqCenterD hd P L k (gamma.1 : Nat)) (hk gamma)

/-- A center-of-mass configuration satisfying the standard cage ledger uses
one selected quantitative readout domain for every center/point pair. -/
theorem exists_cm_branch
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hb : NormalCoordMetricBoundInput (I := I) X) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x : (X.obj k).M) {q : NNReal} {δ ρ : Real}
    (hdom : HasNormalBranchDom (I := I) (X.obj k) hcomplete hconn x q δ ρ)
    {ι : Type} [Fintype ι] (μ : ι → Real) (pts : ι → (X.obj k).M)
    (join : (X.obj k).M → (X.obj k).M → Real → (X.obj k).M)
    (p : (X.obj k).M) (r R : Real) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    ∀ h : CenterInput (I := I) (X.obj k).metric μ pts join p r,
      (letI : MetricSpace (X.obj k).M :=
          HopfRinow.riemMetricSpace (I := I) (M := (X.obj k).M);
        dist p x ≤ R) →
      ENNReal.ofReal (R + 2 * r) < ENNReal.ofReal (ρ / 2) →
      0 < ρ →
      ρ / 2 < expRadiusGp (I := I) (X.obj k).metric x →
      ∃ B : DiagInvBranch (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k)) x,
        ∀ i, (centerOfMass (I := I) (ι := ι) (X.obj k).metric μ pts join p r h,
          pts i) ∈ B.readDom := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : ConnectedSpace (X.obj k).M := hconn
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  intro h hpq hscale hρ hρExp
  have hpairs : ∀ i,
      max
        (riemannianEDist I
          (centerOfMass (I := I) (ι := ι) (X.obj k).metric μ pts join p r h) x)
        (riemannianEDist I (pts i) x) < ENNReal.ofReal (ρ / 2) :=
    centerPairs_lt_le (I := I) (X.obj k).metric μ pts join p r h x R hpq hscale
  exact HasNormalBranchDom.exists_pair_readout (I := I) hb k hcomplete hconn x hdom
    (fun _ ↦ centerOfMass (I := I) (ι := ι) (X.obj k).metric μ pts join p r h) pts
    hρ hρExp (by simpa [riemannianEDist_comm] using hpairs)

end HCGCompactness
end DifferentialGeometry
