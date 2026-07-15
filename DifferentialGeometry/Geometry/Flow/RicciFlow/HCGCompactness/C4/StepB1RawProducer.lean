import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCStageFill

set_option autoImplicit false

/-!
# Concrete Step-B1 raw producer

This final assembly layer deliberately states the real `StepB1RawInput`
producer early.  Its proof is filled from the stage comparison map and the
Route-A local configurations as those producers become available; no parallel
endpoint record is introduced.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

/-- A metric-compactness base has a master subsequence carrying the concrete
raw Step-B1 comparison data.  The target is stated at its final interface so
the radius diagonal, stage-map geometry, and metric-error bridges can be filled
in place rather than hidden behind another input structure. -/
theorem MetricCompactBase.exists_b1_raw
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M) :
    let P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j) :=
      fun j => properMetricOn (I := I) (X.obj j)
        (hcomplete.complete j) (hconn j)
    ∃ psi : Nat → Nat, StrictMono psi ∧
      let Xpsi := X.subseq psi
      let Ppsi : ∀ k : Nat, ProperMetricOn (I := I) (Xpsi.obj k) :=
        fun k => P (psi k)
      StepB1RawInput (I := I) (X := Xpsi) Ppsi := by
  classical
  dsimp only
  -- Honest current frontier: construct the integer-radius master diagonal;
  -- then refine the witness through `{ comparison := ... }` and fill its
  -- stage-map fields from the checked Route-A configuration API.
  sorry

end HCGCompactness
end DifferentialGeometry
