import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1RawProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDAssembly

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# H6-provider Chapter-4 endpoint assembly

This module feeds the provider-native Step-B1 raw producer into the existing
Step-D construction.  It records a conditional endpoint on
`MetricCompactBase` together with its native `H6NormalData`; it does not claim
that the unconditional geometric inputs have already been assembled.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace MetricCompactSeed

/-- The canonical Step-D construction driven by one native H6 chart package. -/
def metricCanonH6
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : H6NormalData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    StepDCanonData (I := I) X := by
  let P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j) :=
    fun j => properMetricOn (I := I) (X.obj j)
      (hcomplete.complete j) (hconn j)
  let hraw := b.exists_b1_raw_h6 d hcomplete hconn
  let psi : Nat → Nat := Classical.choose hraw
  have hraw_spec := Classical.choose_spec hraw
  have hpsi : StrictMono psi := hraw_spec.1
  have B := hraw_spec.2
  let Ppsi : ∀ k : Nat, ProperMetricOn (I := I) ((X.subseq psi).obj k) :=
    fun k => P (psi k)
  let canon : StepDCanonData (I := I) (X.subseq psi) :=
    compactness_canon Ppsi B
  exact canon.ofSeqSubseq psi hpsi

/-- Conditional metric compactness using the provider-native H6 route. -/
def metricCompactH6
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : H6NormalData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactnessConclusion (I := I) X :=
  (b.metricCanonH6 d hcomplete hconn).mc

/-- The H6-provider canonical limit is connected. -/
theorem metricCanonH6_conn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : H6NormalData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let C := b.metricCanonH6 d hcomplete hconn
    letI : TopologicalSpace C.mc.limit.M := C.mc.limit.topology
    ConnectedSpace C.mc.limit.M := by
  classical
  dsimp only [metricCanonH6, StepDCanonData.ofSeqSubseq,
    MetricCompactnessConclusion.ofSeqSubseq]
  exact compactness_conn (I := I) _ _

end MetricCompactSeed

namespace MetricCompactBase

/-- Compatibility wrapper for the legacy normal-coordinate base. -/
def metricCanonH6
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : H6NormalData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    StepDCanonData (I := I) X :=
  b.toSeed.metricCanonH6 d hcomplete hconn

/-- Compatibility wrapper for the legacy normal-coordinate base. -/
def metricCompactH6
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : H6NormalData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactnessConclusion (I := I) X :=
  b.toSeed.metricCompactH6 d hcomplete hconn

/-- The compatibility H6-provider canonical limit is connected. -/
theorem metricCanonH6_conn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : H6NormalData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let C := b.metricCanonH6 d hcomplete hconn
    letI : TopologicalSpace C.mc.limit.M := C.mc.limit.topology
    ConnectedSpace C.mc.limit.M := by
  simpa only [metricCanonH6] using
    b.toSeed.metricCanonH6_conn d hcomplete hconn

end MetricCompactBase
end HCGCompactness
end DifferentialGeometry
