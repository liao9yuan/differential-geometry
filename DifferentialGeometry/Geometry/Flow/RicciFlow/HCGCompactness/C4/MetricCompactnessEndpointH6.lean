import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1RawProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDAssembly

set_option autoImplicit false

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

def metricCanonH6
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : H6NormalData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    StepDCanon (I := I) X := by
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
  let canon : StepDCanon (I := I) (X.subseq psi) :=
    compactness_canon Ppsi B
  exact canon.ofSeqSubseq psi hpsi

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
  dsimp only [metricCanonH6, StepDCanon.ofSeqSubseq,
    MetricCompactnessConclusion.ofSeqSubseq]
  exact compactness_conn (I := I) _ _

end MetricCompactSeed

namespace MetricCompactBase

def metricCanonH6
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : H6NormalData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    StepDCanon (I := I) X :=
  b.toSeed.metricCanonH6 d hcomplete hconn

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
