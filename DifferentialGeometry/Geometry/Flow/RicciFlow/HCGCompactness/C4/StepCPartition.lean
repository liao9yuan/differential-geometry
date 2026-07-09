import Mathlib.Geometry.Manifold.PartitionOfUnity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.GoodCoveringSeq

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Chapter 4 Step C finite hat covers

This file starts the Step-C partition layer at the exact point where the Step-A
good-covering data is already available.  It packages the finite `γ < A r`
hat-ball family and the cover theorem that a later partition-of-unity producer
will consume.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set
open scoped Topology Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

namespace NetLimitData

/-- The finite Step-C hat ball indexed by `γ < A r` at sequence index `k`.

If the ordered net center is absent at this index, the corresponding hat is
empty.  The large-`k` cover theorem below shows that absent hats do not matter
on the covered ball. -/
noncomputable def hatBall (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (γ : Fin (pb.A r)) :
    Set ((X.obj (L.φ k)).M) :=
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  match seqCenter hd D P (L.φ k) (γ : Nat) with
  | some c => Metric.ball c (4 * L.lamInf (γ : Nat))
  | none => ∅

@[simp] theorem hatBall_subseq (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (γ : Fin (pb.A r))
    {ψ : Nat -> Nat} (hψ : StrictMono ψ) :
    (L.subseq hψ).hatBall hd D P pb r k γ =
      L.hatBall hd D P pb r (ψ k) γ := by
  cases hcenter : seqCenter hd D P (L.φ (ψ k)) (γ : Nat) with
  | none =>
      simp [hatBall, NetLimitData.subseq, Function.comp_apply, hcenter]
      rfl
  | some c =>
      simp [hatBall, NetLimitData.subseq, NetLimitData.lamInf, Function.comp_apply,
        hcenter]
      rfl

/-- Each finite Step-C hat ball is open in the realized metric. -/
theorem hatBall_open (hd : InjRadiusDecayInput (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (L : NetLimitData hd D P)
    (pb : hd.PackingBound D) (r : Real) (k : Nat) (γ : Fin (pb.A r)) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    IsOpen (L.hatBall hd D P pb r k γ) := by
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  unfold hatBall
  split
  · exact Metric.isOpen_ball
  · exact isOpen_empty

/-- MSM135 Step-C finite cover input extracted from Step A item 4: for every
fixed radius `r`, once `k` is large, the base ball `B(O_k,r)` is covered by the
finite family of hats indexed by `γ : Fin (A r)`. -/
theorem hatBall_cover (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r : Real) :
    ∀ᶠ k in atTop,
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      Metric.closedBall (X.obj (L.φ k)).basepoint r ⊆
        ⋃ γ : Fin (pb.A r), L.hatBall hd D P pb r k γ := by
  filter_upwards [L.hat_cover hd hD P hre pb r] with k hk
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  intro p hp
  have hpdist : dist p (X.obj (L.φ k)).basepoint ≤ r := by
    simpa [Metric.mem_closedBall] using hp
  obtain ⟨γ, hγ, c, hc, hpc⟩ := hk p hpdist
  refine mem_iUnion.mpr ⟨⟨γ, hγ⟩, ?_⟩
  simp [hatBall, hc, Metric.mem_ball, hpc]

/-- Smooth partition of unity subordinate to the finite Step-C hat cover at one
large sequence index. -/
theorem hatPOU_of_cover (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hcover :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      Metric.closedBall (X.obj (L.φ k)).basepoint r ⊆
        ⋃ γ : Fin (pb.A r), L.hatBall hd D P pb r k γ) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    ∃ ρ : SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r),
      ρ.IsSubordinate (fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ) := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  have htop := ProperMetricOn.top_eq (X.obj (L.φ k)) (P (L.φ k))
  have hs :
      @IsClosed (X.obj (L.φ k)).M (X.obj (L.φ k)).topology
        (Metric.closedBall (X.obj (L.φ k)).basepoint r) := by
    have hs_metric :
        @IsClosed (X.obj (L.φ k)).M
          (P (L.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (Metric.closedBall (X.obj (L.φ k)).basepoint r) :=
      by simpa using
        (Metric.isClosed_closedBall :
          @IsClosed (X.obj (L.φ k)).M
            (P (L.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
            (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    rw [← htop]
    exact hs_metric
  have ho :
      ∀ γ : Fin (pb.A r),
        @IsOpen (X.obj (L.φ k)).M (X.obj (L.φ k)).topology
          (L.hatBall hd D P pb r k γ) := by
    intro γ
    have ho_metric :
        @IsOpen (X.obj (L.φ k)).M
          (P (L.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (L.hatBall hd D P pb r k γ) :=
      by simpa using
        (L.hatBall_open hd D P pb r k γ :
          @IsOpen (X.obj (L.φ k)).M
            (P (L.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
            (L.hatBall hd D P pb r k γ))
    rw [← htop]
    exact ho_metric
  exact SmoothPartitionOfUnity.exists_isSubordinate
    (I := I)
    (s := Metric.closedBall (X.obj (L.φ k)).basepoint r)
    (U := fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ)
    hs
    ho
    hcover

/-- Eventual smooth partition-of-unity subordinate to the Step-C hats. -/
theorem hatPOU_eventually (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r : Real) :
    ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      ∃ ρ : SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
          (Metric.closedBall (X.obj (L.φ k)).basepoint r),
        ρ.IsSubordinate (fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ) := by
  filter_upwards [L.hatBall_cover hd hD P hre pb r] with k hcover
  exact L.hatPOU_of_cover hd P pb r k hcover

/-- The Step-C hat POU weights are nonnegative. -/
theorem hatPOU_nonneg (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    (γ : Fin (pb.A r)) (x : (X.obj (L.φ k)).M) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    0 ≤ ρ γ x := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  exact ρ.nonneg γ x

/-- The Step-C hat POU weights add to one on the covered base ball. -/
theorem hatPOU_sum_one (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    {x : (X.obj (L.φ k)).M}
    (hx :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      x ∈ Metric.closedBall (X.obj (L.φ k)).basepoint r) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    ∑ γ : Fin (pb.A r), ρ γ x = 1 := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  have hsum := ρ.sum_eq_one hx
  rw [finsum_eq_sum (fun γ : Fin (pb.A r) => ρ γ x)
    (Finite.subset finite_univ (subset_univ (Function.support fun γ : Fin (pb.A r) => ρ γ x)))] at hsum
  rwa [Fintype.sum_subset (by simp)] at hsum

/-- At each point of the covered base ball, at least one Step-C hat POU weight
is positive. -/
theorem hatPOU_pos (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    {x : (X.obj (L.φ k)).M}
    (hx :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      x ∈ Metric.closedBall (X.obj (L.φ k)).basepoint r) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    ∃ γ : Fin (pb.A r), 0 < ρ γ x := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  exact ρ.exists_pos_of_mem hx

/-- Nonzero Step-C hat POU weights occur only inside the subordinate hat. -/
theorem hatPOU_active_mem (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    (hρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      ρ.IsSubordinate (fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ))
    {γ : Fin (pb.A r)} {x : (X.obj (L.φ k)).M}
    (hγx :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      ρ γ x ≠ 0) :
    x ∈ L.hatBall hd D P pb r k γ := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  have hx_support : x ∈ Function.support fun y => ρ γ y := by
    simpa [Function.mem_support] using hγx
  exact hρ γ (subset_tsupport (ρ γ) hx_support)

/-- Bundled Step-C hat POU weight facts at a point of the covered base ball:
nonnegativity, a positive weight, and finite sum one. -/
theorem hatPOU_weights (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    {x : (X.obj (L.φ k)).M}
    (hx :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      x ∈ Metric.closedBall (X.obj (L.φ k)).basepoint r) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    (∀ γ : Fin (pb.A r), 0 ≤ ρ γ x) ∧
      (∃ γ : Fin (pb.A r), 0 < ρ γ x) ∧
        ∑ γ : Fin (pb.A r), ρ γ x = 1 := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  exact ⟨fun γ => L.hatPOU_nonneg hd P pb r k ρ γ x,
    L.hatPOU_pos hd P pb r k ρ hx,
    L.hatPOU_sum_one hd P pb r k ρ hx⟩

/-- Bundled Step-C POU data at a covered point: normalized weights together
with the active-support-to-hat bridge. -/
theorem hatPOU_active_data (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (ρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      SmoothPartitionOfUnity (Fin (pb.A r)) I (X.obj (L.φ k)).M
        (Metric.closedBall (X.obj (L.φ k)).basepoint r))
    (hρ :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
      letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      ρ.IsSubordinate (fun γ : Fin (pb.A r) => L.hatBall hd D P pb r k γ))
    {x : (X.obj (L.φ k)).M}
    (hx :
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      x ∈ Metric.closedBall (X.obj (L.φ k)).basepoint r) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    ((∀ γ : Fin (pb.A r), 0 ≤ ρ γ x) ∧
      (∃ γ : Fin (pb.A r), 0 < ρ γ x) ∧
        ∑ γ : Fin (pb.A r), ρ γ x = 1) ∧
      ∀ γ : Fin (pb.A r), ρ γ x ≠ 0 →
        x ∈ L.hatBall hd D P pb r k γ := by
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : SigmaCompactSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).sigmaCompact
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  exact ⟨L.hatPOU_weights hd P pb r k ρ hx,
    fun γ hγx => L.hatPOU_active_mem hd P pb r k ρ hρ hγx⟩

end NetLimitData

end HCGCompactness
end DifferentialGeometry
