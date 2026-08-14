import DifferentialGeometry.Geometry.Comparison.IntrinsicInjectivityRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PointedEmetric

set_option autoImplicit false









noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

open Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]










attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic framed injectivity radius of a complete pointed Riemannian
manifold. -/
noncomputable def PointedRiemannianManifold.intrInjRadius
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) X)
    (x : X.M) : ENNReal := by
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : IsManifold I 1 X.M :=
    IsManifold.of_le (I := I) (M := X.M) (n := ∞) (by decide)
  letI : T2Space X.M := X.t2
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  letI : RiemannianBundle (fun y : X.M => TangentSpace I y) :=
    X.riemBundle (I := I)
  letI : (y : X.M) → InnerProductSpace Real (TangentSpace I y) :=
    X.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : X.M => TangentSpace I y) := X.riemBundle_cont (I := I)
  letI : EMetricSpace X.M := X.emetricSpace (I := I)
  letI : CompleteSpace X.M := MetricComplete.complete (I := I) X hcomplete
  let hEnorm : ∀ (y : X.M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (X.metric.inner y w w)) := by
    intro y w
    simpa using
      (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) X.metric y w)
  exact Geometry.Riemannian.NormalCoordinates.intrInjRadius
    (I := I) X.metric hEnorm x

/-- The injectivity radius of `X` at `x` is at least `rho`, measured by the
complete intrinsic framed exponential whenever the supplied metric is complete
Uniform sequence lower bounds are recorded by `BaseInjBound`. -/
def HasInjRadiusAt
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M)
    (rho : Real) : Prop :=
  0 < rho ∧ ∀ hcomplete : MetricComplete (I := I) X,
    ENNReal.ofReal rho ≤ X.intrInjRadius (I := I) hcomplete x

/-- The HCG pointwise injectivity-radius predicate unfolds to a positive,
intrinsic framed injectivity-radius lower bound. -/
theorem hasInjRadiusAt_iff
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M)
    (rho : Real) :
    HasInjRadiusAt (I := I) X x rho ↔
      (0 < rho ∧ ∀ hcomplete : MetricComplete (I := I) X,
        ENNReal.ofReal rho ≤ X.intrInjRadius (I := I) hcomplete x) :=
  Iff.rfl

/-- A positive radius uniformly bounded by the intrinsic framed injectivity
radius gives the HCG pointwise lower bound. -/
theorem hasInjRadiusAt_of_le
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho : Real} (hpos : 0 < rho)
    (h : ∀ hcomplete : MetricComplete (I := I) X,
      ENNReal.ofReal rho ≤ X.intrInjRadius (I := I) hcomplete x) :
    HasInjRadiusAt (I := I) X x rho :=
  ⟨hpos, h⟩

/-- Project an intrinsic injectivity-radius lower bound at a chosen complete
realization of the pointed manifold. -/
theorem HasInjRadiusAt.le_intr
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho : Real} (h : HasInjRadiusAt (I := I) X x rho)
    (hcomplete : MetricComplete (I := I) X) :
    ENNReal.ofReal rho ≤ X.intrInjRadius (I := I) hcomplete x :=
  h.2 hcomplete

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A strict subradius of an HCG injectivity lower bound is an injectivity ball
for the complete intrinsic framed exponential. -/
theorem HasInjRadiusAt.injOn_ball
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho r : Real} (h : HasInjRadiusAt (I := I) X x rho)
    (hcomplete : MetricComplete (I := I) X) (hr : r < rho) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : IsManifold I 1 X.M :=
      IsManifold.of_le (I := I) (M := X.M) (n := ∞) (by decide)
    letI : T2Space X.M := X.t2
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
    letI : RiemannianBundle (fun y : X.M => TangentSpace I y) :=
      X.riemBundle (I := I)
    letI : (y : X.M) → InnerProductSpace Real (TangentSpace I y) :=
      X.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : X.M => TangentSpace I y) := X.riemBundle_cont (I := I)
    letI : EMetricSpace X.M := X.emetricSpace (I := I)
    letI : CompleteSpace X.M := MetricComplete.complete (I := I) X hcomplete
    let hEnorm : ∀ (y : X.M) (w : TangentSpace I y),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (X.metric.inner y w w)) := by
      intro y w
      simpa using
        (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) X.metric y w)
    Set.InjOn (intrinsicFramedExp (I := I) X.metric hEnorm x)
      (Metric.ball (0 : E) r) := by
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : IsManifold I 1 X.M :=
    IsManifold.of_le (I := I) (M := X.M) (n := ∞) (by decide)
  letI : T2Space X.M := X.t2
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space (TangentBundle I X.M) := X.t2TangentBundle
  letI : RiemannianBundle (fun y : X.M => TangentSpace I y) :=
    X.riemBundle (I := I)
  letI : (y : X.M) → InnerProductSpace Real (TangentSpace I y) :=
    X.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : X.M => TangentSpace I y) := X.riemBundle_cont (I := I)
  letI : EMetricSpace X.M := X.emetricSpace (I := I)
  letI : CompleteSpace X.M := MetricComplete.complete (I := I) X hcomplete
  let hEnorm : ∀ (y : X.M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (X.metric.inner y w w)) := by
    intro y w
    simpa using
      (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) X.metric y w)
  apply intrInjOn_ball (I := I) X.metric hEnorm x
  exact ((ENNReal.ofReal_lt_ofReal_iff h.1).2 hr).trans_le <| by
    simpa only [PointedRiemannianManifold.intrInjRadius] using
      h.le_intr hcomplete

/-- A smaller positive radius inherits an injectivity-radius lower bound. -/
theorem HasInjRadiusAt.mono
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : X.M}
    {rho rho' : Real} (h : HasInjRadiusAt (I := I) X x rho)
    (hpos : 0 < rho') (hle : rho' <= rho) :
    HasInjRadiusAt (I := I) X x rho' := by
  rw [hasInjRadiusAt_iff] at h ⊢
  refine ⟨hpos, ?_⟩
  intro hcomplete
  exact (ENNReal.ofReal_le_ofReal hle).trans (h.2 hcomplete)

/-- Uniform injectivity-radius lower bound at the basepoints of a pointed
metric sequence. -/

structure BaseInjBound
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  ρ : Real
  pos : 0 < ρ
  bound : forall i : Nat, HasInjRadiusAt (I := I) (X.obj i) (X.obj i).basepoint ρ

namespace BaseInjBound


def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : BaseInjBound (I := I) X) (f : Nat -> Nat) :
    BaseInjBound (I := I) (X.subseq f) where
  ρ := h.ρ
  pos := h.pos
  bound := by
    intro i
    simpa [PointedRiemannianSeq.subseq] using h.bound (f i)

end BaseInjBound


abbrev FlowBaseInjBound
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) :=
  BaseInjBound (I := I) (X.atZero (I := I))

end HCGCompactness
end DifferentialGeometry
