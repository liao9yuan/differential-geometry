import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.InjectivityRadius
-- Step A honest inputs (`PointedSeqDistance`, `InjRadiusDecayInput`,
-- `VolumeComparisonInput`) were relocated to `StepAInputs.lean` so they build
-- independently of the S6 exp⁻¹ machinery below.
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.StepAInputs

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Chapter 4 Geometric Inputs For HCG Compactness

This file pins down the theorem-facing black-box boundary for the deep
geometric inputs used in MSM135 Chapter 4's proof of Hamilton--Cheeger--Gromov
compactness.  The records below contain constants and estimate fields only; the
hard geometry is intentionally carried as a field to be produced later.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology ENNReal Bundle

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

-- `PointedSeqDistance` relocated to `StepAInputs.lean` (re-exported via the
-- import above).

/-- Normal-chart data for one pointed Riemannian manifold, with the local
instances unpacked from the stored HCG object. -/
structure NormalChartFor
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M) :
    Type _ where
  vb :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I (∞ : WithTop ℕ∞) X.M := X.smooth
    VectorBundle Real E (TangentSpace I : X.M -> Type _)
  data :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I (∞ : WithTop ℕ∞) X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    letI : VectorBundle Real E (TangentSpace I : X.M -> Type _) := vb
    RicciFlower.Coordinates.NormalChartData (I := I) X.metric x

/-- The model-coordinate transition map
`normal_y ∘ exp_x`, i.e. the form of `exp_y⁻¹ ∘ exp_x` consumed by the
Step B/C approximate-isometry estimates. -/
noncomputable def normalTransitionMap
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {x y : X.M}
    (Nx : NormalChartFor (I := I) X x)
    (Ny : NormalChartFor (I := I) X y) :
    E -> E :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I (∞ : WithTop ℕ∞) X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  letI : VectorBundle Real E (TangentSpace I : X.M -> Type _) := Nx.vb
  fun z : E =>
    Ny.data.localChart.ext
      (Nx.data.exp ((RicciFlower.Coordinates.normalCoordLinearEquiv (I := I) x).symm z))

/-- Derivative bound for one normal-coordinate transition map. -/
def NormalTransitionDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {x y : X.M}
    (Nx : NormalChartFor (I := I) X x)
    (Ny : NormalChartFor (I := I) X y)
    (p : Nat) (C : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I (∞ : WithTop ℕ∞) X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  letI : VectorBundle Real E (TangentSpace I : X.M -> Type _) := Nx.vb
  forall z : E,
    z ∈ Metric.ball (0 : E) Nx.data.radius ->
      Nx.data.exp ((RicciFlower.Coordinates.normalCoordLinearEquiv (I := I) x).symm z) ∈
          Ny.data.localChart.source ->
        ‖iteratedFDeriv Real p (normalTransitionMap (I := I) X Nx Ny) z‖ <= C

-- `InjRadiusDecayInput` (A0) and `VolumeComparisonInput` (A0') relocated to
-- `StepAInputs.lean` (re-exported via the import above).

/-- MSM135 Chapter 4, section `lbl-2103`:
Jacobi/Rauch comparison bounds for derivatives of normal-coordinate transition
maps `exp_y⁻¹ ∘ exp_x`.

The field `exp_inv_deriv` is the deep external theorem.  It is phrased in model
coordinates using `NormalChartData`, matching the Step B/C maps built from
local exponential charts. -/
structure ExpInverseDerivBoundInput
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  derivC : Nat -> Real
  derivC_nonneg : forall p : Nat, 0 <= derivC p
  /-- Consumed by Steps B/C: uniform `C^p` bounds for the normal-coordinate
  transition map on the overlap of two injectivity charts. -/
  exp_inv_deriv :
    forall k p : Nat,
      forall x y : (X.obj k).M,
        forall Nx : NormalChartFor (I := I) (X.obj k) x,
          forall Ny : NormalChartFor (I := I) (X.obj k) y,
            NormalTransitionDerivBound (I := I) (X.obj k) Nx Ny p (derivC p)

end HCGCompactness
end DifferentialGeometry
