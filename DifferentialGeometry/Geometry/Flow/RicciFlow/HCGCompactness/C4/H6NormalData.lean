import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.H6NormalCoord
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.H6MetricJet

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# H6 normal-coordinate data

This file assembles the intrinsic H6 radius and whole-ball chart selected by
the Cheeger--Gromov--Taylor injectivity profile and the uniform intrinsic
Jacobi estimates.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Set
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

namespace InjRadiusDecayInput

/-- The fixed H6 ratio obtained by comparing the uniform Jacobi radius with
the largest value `mu 0` of the injectivity profile. -/
def h6Ratio {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (r₀ : Real) : Real :=
  min (1 / 2) (r₀ / (2 * hd.mu 0))

/-- The center-dependent H6 radius selected from the CGT profile. -/
def h6Radius {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (r₀ : Real)
    (k : Nat) (x : (X.obj k).M) : Real :=
  hd.h6Ratio r₀ * hd.mu (hd.dist k x (X.obj k).basepoint)

/-- The H6 ratio is positive when the uniform Jacobi radius is positive. -/
theorem h6Ratio_pos {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {r₀ : Real} (hr₀ : 0 < r₀) :
    0 < hd.h6Ratio r₀ := by
  rw [h6Ratio]
  exact lt_min (by norm_num)
    (div_pos hr₀ (mul_pos (by norm_num) (hd.mu_pos 0)))

/-- The H6 ratio is strictly smaller than one. -/
theorem h6Ratio_lt_one {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (r₀ : Real) :
    hd.h6Ratio r₀ < 1 :=
  lt_of_le_of_lt (min_le_left _ _) (by norm_num)

/-- Every selected H6 radius is positive. -/
theorem h6Radius_pos {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) {r₀ : Real} (hr₀ : 0 < r₀)
    (k : Nat) (x : (X.obj k).M) :
    0 < hd.h6Radius r₀ k x :=
  mul_pos (hd.h6Ratio_pos hr₀)
    (hd.mu_pos (hd.dist k x (X.obj k).basepoint))

/-- Every selected H6 radius is a strict subradius of the local-diffeomorphism
radius used to define its global ratio. -/
theorem h6Radius_lt_r0 {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (hreal : hd.RealizesEdist)
    {r₀ : Real} (hr₀ : 0 < r₀) (k : Nat) (x : (X.obj k).M) :
    hd.h6Radius r₀ k x < r₀ := by
  have hmu₀ : 0 < hd.mu 0 := hd.mu_pos 0
  have hmu :
      hd.mu (hd.dist k x (X.obj k).basepoint) ≤ hd.mu 0 :=
    hd.mu_antitone (hreal.dist_nonneg k x (X.obj k).basepoint)
  calc
    hd.h6Radius r₀ k x
        ≤ hd.h6Ratio r₀ * hd.mu 0 :=
      mul_le_mul_of_nonneg_left hmu (hd.h6Ratio_pos hr₀).le
    _ ≤ (r₀ / (2 * hd.mu 0)) * hd.mu 0 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hmu₀.le
    _ = r₀ / 2 := by field_simp [ne_of_gt hmu₀]
    _ < r₀ := by linarith

/-- Every selected H6 radius is a strict subradius of the CGT injectivity
lower bound at the same center. -/
theorem h6Radius_lt_mu {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjRadiusDecayInput (I := I) X) (r₀ : Real)
    (k : Nat) (x : (X.obj k).M) :
    hd.h6Radius r₀ k x <
      hd.mu (hd.dist k x (X.obj k).basepoint) := by
  rw [h6Radius]
  simpa only [one_mul] using
    mul_lt_mul_of_pos_right (hd.h6Ratio_lt_one r₀)
      (hd.mu_pos (hd.dist k x (X.obj k).basepoint))

end InjRadiusDecayInput

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The controlled radius and whole-ball intrinsic branches constructed before
the independent all-order metric-jet estimates. -/
structure H6BallData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjRadiusDecayInput (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) where
  ratio : Real
  ratio_pos : 0 < ratio
  chart : ∀ (k : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M :=
      IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    letI : ConnectedSpace (X.obj k).M := hconn k
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    IntrinsicBallChart (I := I) (X.obj k).metric hEnorm x
      (ratio * hd.mu (hd.dist k x (X.obj k).basepoint))
  intr_equiv : ∀ (k : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M :=
      IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    letI : ConnectedSpace (X.obj k).M := hconn k
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    ∀ z ∈ Metric.ball (0 : E)
        (ratio * hd.mu (hd.dist k x (X.obj k).basepoint)), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
          intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ∧
        intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ≤
          2 * ‖v‖ ^ 2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic H6 branch viewed through the branch-parametric consumer
interface. -/
noncomputable def H6BallData.normalChart
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    (d : H6BallData (I := I) X hd hcomplete hconn)
    (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M :=
      IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    letI : ConnectedSpace (X.obj k).M := hconn k
    NormalBallChart (I := I) x := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M :=
    IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  letI : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  letI : ConnectedSpace (X.obj k).M := hconn k
  let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    simpa using
      (tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj k).metric y w)
  exact IntrinsicBallChart.toNormalBallChart
    (I := I) (X.obj k).metric hEnorm x (d.chart k x)
    (mul_pos d.ratio_pos
      (hd.mu_pos (hd.dist k x (X.obj k).basepoint)))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
@[simp] theorem H6BallData.normalChart_radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    (d : H6BallData (I := I) X hd hcomplete hconn)
    (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M :=
      IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    letI : ConnectedSpace (X.obj k).M := hconn k
    (d.normalChart k x).radius =
      d.ratio * hd.mu (hd.dist k x (X.obj k).basepoint) := by
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Proof-independent branch data presented to normal-coordinate consumers.
Completeness and connectedness are needed to construct this package, not to
use it. -/
structure H6ChartData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjRadiusDecayInput (I := I) X) where
  ratio : Real
  ratio_pos : 0 < ratio
  chart : ∀ (k : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    NormalBallChart (I := I) x
  radius_eq : ∀ (k : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (chart k x).radius =
      ratio * hd.mu (hd.dist k x (X.obj k).basepoint)
  hom_eq : ∀ (k : Nat) (x : (X.obj k).M)
      (hcomplete : MetricComplete (I := I) (X.obj k)),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    EqOn (chart k x).hom
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
      (Metric.ball (0 : E) (chart k x).radius)

namespace H6ChartData

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every H6 chart radius is bounded by one fixed launch radius. -/
theorem radius_le_global
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : H6ChartData (I := I) X hd) (hreal : hd.RealizesEdist)
    (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (d.chart k x).radius ≤ d.ratio * hd.mu 0 := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  rw [d.radius_eq k x]
  exact mul_le_mul_of_nonneg_left
    (hd.mu_antitone (hreal.dist_nonneg k x (X.obj k).basepoint))
    d.ratio_pos.le

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On its controlled ball, the metric pulled back by an H6 chart is the
intrinsic framed pullback metric. -/
theorem metric_eq_intr
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : H6ChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    EqOn ((d.chart k x).metric (X.obj k).metric)
      (intrFrameMetric (I := I) (X.obj k).metric hEnorm x)
      (Metric.ball (0 : E) (d.chart k x).radius) := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  letI : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
    intro y w
    simpa using
      (tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj k).metric y w)
  change EqOn ((d.chart k x).metric (X.obj k).metric)
    (intrFrameMetric (I := I) (X.obj k).metric hEnorm x)
    (Metric.ball (0 : E) (d.chart k x).radius)
  intro z hz
  have hev : Filter.EventuallyEq (nhds z)
      (d.chart k x).hom
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x) :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
      fun q hq => d.hom_eq k x hcomplete hq
  have hD : mfderiv (modelWithCornersSelf Real E) I
      (d.chart k x).hom z =
      mfderiv (modelWithCornersSelf Real E) I
        (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x) z :=
    Filter.EventuallyEq.mfderiv_eq
      (I := modelWithCornersSelf Real E) (I' := I) hev
  ext v w
  rw [NormalBallChart.metric_apply, intrFrameMetric_apply,
    d.hom_eq k x hcomplete hz, hD]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every point in the intrinsic ball controlled by an H6 chart lies in its
whole-ball image, and its inverse coordinate has norm equal to the intrinsic
distance from the center. -/
theorem readout_mem
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : H6ChartData (I := I) X hd) (k : Nat)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn : letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (x y : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun z : (X.obj k).M => TangentSpace I z) :=
      (X.obj k).riemBundle (I := I)
    letI : (z : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I z) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun z : (X.obj k).M => TangentSpace I z) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    Manifold.riemannianEDist I x y <
        ENNReal.ofReal (d.chart k x).radius →
      y ∈ (d.chart k x).hom '' Metric.ball (0 : E) (d.chart k x).radius ∧
        ‖(d.chart k x).inv y‖ =
          (Manifold.riemannianEDist I x y).toReal := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle
      (fun z : (X.obj k).M => TangentSpace I z) :=
    (X.obj k).riemBundle (I := I)
  letI : (z : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I z) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun z : (X.obj k).M => TangentSpace I z) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  letI : ConnectedSpace (X.obj k).M := hconn
  let hEnorm : ∀ (z : (X.obj k).M) (w : TangentSpace I z),
      ‖w‖ₑ =
        ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner z w w)) := by
    intro z w
    simpa using
      (tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (X.obj k).metric z w)
  intro hy
  obtain ⟨v, hvExp, hvLen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) (X.obj k).metric hEnorm x y
  let z : E := (normalFrame (I := I) (X.obj k).metric x).symm v
  have hzFrame : normalFrame (I := I) (X.obj k).metric x z = v := by
    exact (normalFrame (I := I) (X.obj k).metric x).apply_symm_apply v
  have hzNorm :
      ‖z‖ = Real.sqrt ((X.obj k).metric.inner x v v) := by
    have h := normalFrame_sqrt (I := I) (X.obj k).metric x z
    rw [hzFrame] at h
    exact h.symm
  have hyFin : Manifold.riemannianEDist I x y ≠ (⊤ : ENNReal) :=
    ne_of_lt (hy.trans ENNReal.ofReal_lt_top)
  have hyReal :
      (Manifold.riemannianEDist I x y).toReal < (d.chart k x).radius :=
    (ENNReal.lt_ofReal_iff_toReal_lt hyFin).mp hy
  have hzBall : z ∈ Metric.ball (0 : E) (d.chart k x).radius := by
    rw [Metric.mem_ball, dist_zero_right, hzNorm, hvLen]
    exact hyReal
  have hmap : (d.chart k x).hom z = y := by
    calc
      (d.chart k x).hom z =
          intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x z :=
        d.hom_eq k x hcomplete hzBall
      _ = expMapIntrinsic (I := I) (X.obj k).metric hEnorm x
          (normalFrame (I := I) (X.obj k).metric x z) := by
        rw [intrFrame_apply]
      _ = expMapIntrinsic (I := I) (X.obj k).metric hEnorm x v := by
        rw [hzFrame]
      _ = y := hvExp
  refine ⟨⟨z, hzBall, hmap⟩, ?_⟩
  change ‖(d.chart k x).hom.symm y‖ =
    (Manifold.riemannianEDist I x y).toReal
  have hinv : (d.chart k x).hom.symm y = z := by
    rw [← hmap]
    exact (d.chart k x).hom.left_inv
      ((d.chart k x).ball_subset hzBall)
  rw [hinv, hzNorm, hvLen]

end H6ChartData

set_option synthInstance.maxHeartbeats 800000 in
/-- The final H6 normal-coordinate package: one intrinsic branch provider,
uniform Euclidean metric comparison, and all-order metric-jet bounds. -/
structure H6NormalData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjRadiusDecayInput (I := I) X)
    extends H6ChartData (I := I) X hd where
  metricC : Nat → Real
  metricC_nonneg : ∀ p : Nat, 0 ≤ metricC p
  metric_equiv : ∀ (k : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (chart k x).MetricEquivOn (X.obj k).metric
      (Metric.ball (0 : E) (chart k x).radius)
  metric_deriv : ∀ (k p : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (chart k x).MetricDerivBound (X.obj k).metric
      (Metric.ball (0 : E) (chart k x).radius) p (metricC p)

namespace H6NormalData

/-- The metric at stage `k` pulled back through the H6 chart centered at `x`.
This is the branch-independent replacement for the legacy
`normalCoordMetric`. -/
def chartMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : H6NormalData (I := I) X hd) (k : Nat) (x : (X.obj k).M) :
    E → E →L[Real] E →L[Real] Real :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).metric (X.obj k).metric

/-- The H6 metric estimates presented through the common controlled-chart
metric interface. -/
def metricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : H6NormalData (I := I) X hd) (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (d.chart k x).MetricBounds (X.obj k).metric := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  exact
    { C := d.metricC
      C_nonneg := d.metricC_nonneg
      radius := (d.chart k x).radius
      radius_pos := (d.chart k x).radius_pos
      equiv := d.metric_equiv k x
      deriv := fun p => d.metric_deriv k p x }

/-- The transition between two H6 charts at the same sequence stage. -/
def chartTransition
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : H6NormalData (I := I) X hd) (k : Nat)
    (x y : (X.obj k).M) : E → E :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).transition (d.chart k y)

/-- Controlled overlap of two H6 charts at one sequence stage. -/
def ChartOverlapOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : H6NormalData (I := I) X hd) (k : Nat)
    (x y : (X.obj k).M) (U : Set E) : Prop :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (d.chart k x).OverlapOn (d.chart k y) U

end H6NormalData

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Forget construction-only completeness data from an intrinsic H6 ball
package. -/
noncomputable def H6BallData.toChartData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    (d : H6BallData (I := I) X hd hcomplete hconn) :
    H6ChartData (I := I) X hd where
  ratio := d.ratio
  ratio_pos := d.ratio_pos
  chart := fun k x => d.normalChart k x
  radius_eq := fun k x => d.normalChart_radius k x
  hom_eq := fun k x hcomplete' => by
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete'
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    change EqOn (d.normalChart k x).hom
      (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
      (Metric.ball (0 : E) (d.normalChart k x).radius)
    intro z hz
    exact (d.chart k x).hom_eq hz

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The intrinsic half/two estimate retained by the construction package,
transported to its common branch-parametric chart. -/
theorem H6BallData.normal_equiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hcomplete : SeqMetricComplete (I := I) X}
    {hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M}
    (d : H6BallData (I := I) X hd hcomplete hconn)
    (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M :=
      IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    letI : ConnectedSpace (X.obj k).M := hconn k
    (d.normalChart k x).MetricEquivOn (X.obj k).metric
      (Metric.ball (0 : E) (d.normalChart k x).radius) := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : IsManifold I 1 (X.obj k).M :=
    IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  letI : T2Space (X.obj k).M := (X.obj k).t2
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  letI : T3Space (X.obj k).M := inferInstance
  letI : RiemannianBundle
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  letI : (y : (X.obj k).M) →
      InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M => TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  letI : EMetricSpace (X.obj k).M :=
    (X.obj k).emetricSpace (I := I)
  letI : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  letI : ConnectedSpace (X.obj k).M := hconn k
  change (d.toChartData.chart k x).MetricEquivOn (X.obj k).metric
    (Metric.ball (0 : E) (d.toChartData.chart k x).radius)
  intro z hz v
  rw [(d.toChartData.metric_eq_intr k (hcomplete.complete k) x) hz]
  change z ∈ Metric.ball (0 : E) (d.normalChart k x).radius at hz
  rw [d.normalChart_radius k x] at hz
  exact d.intr_equiv k x z hz v

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Completeness, bounded geometry, and the CGT injectivity profile construct
one positive global ratio and a controlled intrinsic whole-ball chart at every
sequence center. -/
theorem exists_h6BallData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hd : InjRadiusDecayInput (I := I) X)
    (hreal : hd.RealizesEdist) :
    Nonempty (H6BallData (I := I) X hd hcomplete hconn) := by
  obtain ⟨r₀, hr₀, hcontrol⟩ :=
    exists_intr_control (I := I) X hcomplete hconn hgeom
  refine ⟨{
    ratio := hd.h6Ratio r₀
    ratio_pos := hd.h6Ratio_pos hr₀
    chart := ?_
    intr_equiv := ?_ }⟩
  · intro k x
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M :=
      IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    letI : ConnectedSpace (X.obj k).M := hconn k
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    let r : Real := hd.h6Radius r₀ k x
    have hr : 0 < r := hd.h6Radius_pos hr₀ k x
    have hr₀' : r < r₀ := hd.h6Radius_lt_r0 hreal hr₀ k x
    have hsub : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) r₀ :=
      Metric.ball_subset_ball hr₀'.le
    have hloc :
        IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞
          (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
          (Metric.ball (0 : E) r) := by
      intro z
      exact (hcontrol k x).2 ⟨z, hsub z.2⟩
    have hdecay :
        HasInjRadiusAt (I := I) (X.obj k) x
          (hd.mu (hd.dist k x (X.obj k).basepoint)) := by
      simpa only [InjRadiusDecayInput.mu] using hd.decay k x
    have hinj :
        InjOn (intrinsicFramedExp (I := I) (X.obj k).metric hEnorm x)
          (Metric.ball (0 : E) r) := by
      exact hdecay.injOn_ball (hcomplete.complete k)
        (hd.h6Radius_lt_mu r₀ k x)
    exact Classical.choice <| by
      simpa only [r, InjRadiusDecayInput.h6Radius] using
        exists_intrBallChart (I := I) (X.obj k).metric hEnorm x hloc hinj
  · intro k x
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M :=
      IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    letI : ConnectedSpace (X.obj k).M := hconn k
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    change ∀ z ∈ Metric.ball (0 : E) (hd.h6Radius r₀ k x), ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤
          intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ∧
        intrFrameMetric (I := I) (X.obj k).metric hEnorm x z v v ≤
          2 * ‖v‖ ^ 2
    intro z hz v
    have hr₀' :
        hd.h6Radius r₀ k x < r₀ :=
      hd.h6Radius_lt_r0 hreal hr₀ k x
    exact (hcontrol k x).1 z
      (Metric.ball_subset_ball hr₀'.le hz) v

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Completeness, bounded geometry, and the CGT profile construct one
proof-independent branch provider for the whole sequence. -/
theorem exists_h6ChartData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hd : InjRadiusDecayInput (I := I) X)
    (hreal : hd.RealizesEdist) :
    Nonempty (H6ChartData (I := I) X hd) := by
  obtain ⟨d⟩ :=
    exists_h6BallData (I := I) X hcomplete hconn hgeom hd hreal
  exact ⟨d.toChartData⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Completeness, connectedness, sequence bounded geometry, and the CGT
injectivity profile construct the full H6 normal-coordinate package. -/
theorem exists_h6NormalData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hd : InjRadiusDecayInput (I := I) X)
    (hreal : hd.RealizesEdist) :
    Nonempty (H6NormalData (I := I) X hd) := by
  obtain ⟨d⟩ :=
    exists_h6BallData (I := I) X hcomplete hconn hgeom hd hreal
  let U : Real := d.ratio * hd.mu 0
  let metricC : Nat → Real := fun n =>
    ContinuousMultilinearMap.polarConst n *
      (2 * (2 ^ n * jetCap hgeom.C U 1 n ^ 2))
  refine ⟨{
    toH6ChartData := d.toChartData
    metricC := metricC
    metricC_nonneg := ?_
    metric_equiv := ?_
    metric_deriv := ?_ }⟩
  · intro n
    exact mul_nonneg (ContinuousMultilinearMap.polarConst_nonneg n)
      (mul_nonneg (by norm_num)
        (mul_nonneg (by positivity) (sq_nonneg _)))
  · intro k x
    exact d.normal_equiv k x
  · intro k n x
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M :=
      IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) →
        InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M => TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M :=
      (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
    letI : ConnectedSpace (X.obj k).M := hconn k
    let hEnorm : ∀ (y : (X.obj k).M) (w : TangentSpace I y),
        ‖w‖ₑ =
          ENNReal.ofReal (Real.sqrt ((X.obj k).metric.inner y w w)) := by
      intro y w
      simpa using
        (tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (X.obj k).metric y w)
    let hPk : BoundedGeometry (I := I) (X.obj k) :=
      { C := hgeom.C
        nonneg := hgeom.nonneg
        bound := hgeom.bound k }
    refine NormalBallChart.MetricDerivBound.of_eqOn
      (g := (X.obj k).metric) Metric.isOpen_ball
      (d.toChartData.metric_eq_intr k (hcomplete.complete k) x) ?_
    intro z hz
    have hzU : ‖z‖ ≤ U := by
      have hzRadius :
          ‖z‖ < (d.toChartData.chart k x).radius := by
        simpa [dist_zero_right] using Metric.mem_ball.mp hz
      exact hzRadius.le.trans
        (d.toChartData.radius_le_global hreal k x)
    have hchartSmooth :
        ContDiffAt Real ∞
          ((d.toChartData.chart k x).metric (X.obj k).metric) z :=
      ((d.toChartData.chart k x).metric_contDiffOn
        (X.obj k).metric Metric.isOpen_ball
        (d.toChartData.chart k x).smooth_to).contDiffAt
          (Metric.isOpen_ball.mem_nhds hz)
    have heq :
        ((d.toChartData.chart k x).metric (X.obj k).metric) =ᶠ[nhds z]
          intrFrameMetric (I := I) (X.obj k).metric hEnorm x :=
      Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz)
        fun q hq =>
          d.toChartData.metric_eq_intr k (hcomplete.complete k) x hq
    have hintrSmooth :
        ContDiffAt Real ∞
          (intrFrameMetric (I := I) (X.obj k).metric hEnorm x) z :=
      hchartSmooth.congr_of_eventuallyEq heq.symm
    exact intrMetric_deriv_le (I := I) (X.obj k)
      (hcomplete.complete k) (hconn k) hPk x z n U hzU hintrSmooth

end HCGCompactness
end DifferentialGeometry
