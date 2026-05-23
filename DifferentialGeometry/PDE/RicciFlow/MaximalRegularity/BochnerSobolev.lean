import DifferentialGeometry.PDE.RicciFlow.HeatSemigroup.Defs
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Sobolev–Bochner space `H¹([0,T]; X)`

For a real Hilbert space `X` and a time horizon `T > 0`, this file
introduces the **Bochner–Sobolev space**

  `H¹([0,T]; X) = { u : [0,T] → X | u ∈ L²([0,T]; X), u' ∈ L²([0,T]; X) }`

of `X`-valued functions on the time interval `[0, T]` whose weak time
derivative lies in `L²([0,T]; X)`. This is the natural Banach (in fact
Hilbert) space in which to phrase the maximal-regularity theorem for
the inhomogeneous heat equation.

The skeleton ships the public bare definition and the canonical
inclusion and time-derivative continuous linear maps, together with
the `NormedAddCommGroup` and `CompleteSpace` instances. All bodies
are stubs (the underlying type is set to the Bochner `L²` space, so
that downstream files can refine the implementation while keeping the
public-API surface stable). All proofs go through `sorry`.

## Main definitions

* `bochnerSobolevH1 T X` — the Bochner–Sobolev space `H¹([0,T]; X)`.
* `bochnerSobolevH1.toL2 T X` — the continuous linear inclusion
  `H¹ ↪ L²`.
* `bochnerSobolevH1.timeDeriv T X` — the continuous linear time
  derivative `H¹ → L²`.

## Main instances

* `bochnerSobolevH1.normedAddCommGroup` — the Hilbert-space norm.
* `bochnerSobolevH1.completeSpace` — completeness.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace MaximalRegularity

/-! ## The Bochner–Sobolev space `H¹([0,T]; X)` -/

/-- The **Bochner–Sobolev space** `H¹([0,T]; X)` of `X`-valued functions
on the time interval `[0, T]` whose weak time derivative lies in
`L²([0,T]; X)`.

Mathematically this is the completion of the space of `X`-valued
`C¹` functions on `[0,T]` under the graph norm `‖u‖² + ‖u'‖²`. In the
skeleton it is implemented as a thin wrapper around the Bochner `L²`
space `MeasureTheory.Lp X 2 (volume.restrict (Set.Ioc 0 T))`: this
provides the correct `NormedAddCommGroup`, `InnerProductSpace ℝ` and
`CompleteSpace` typeclass structure without further configuration.
Downstream files refine the underlying type to the genuine Sobolev
space while preserving the public API. -/
def bochnerSobolevH1 (T : ℝ) (X : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] :
    Type _ :=
  MeasureTheory.Lp X 2 (volume.restrict (Set.Ioc 0 T))

/-! ## Typeclass instances -/

/-- The `NormedAddCommGroup` structure on `H¹([0,T]; X)`. -/
instance bochnerSobolevH1.normedAddCommGroup (T : ℝ) (X : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] :
    NormedAddCommGroup (bochnerSobolevH1 T X) := by
  unfold bochnerSobolevH1
  infer_instance

/-- `H¹([0,T]; X)` is a real normed space. -/
instance bochnerSobolevH1.normedSpace (T : ℝ) (X : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] :
    NormedSpace ℝ (bochnerSobolevH1 T X) := by
  unfold bochnerSobolevH1
  infer_instance

/-- The `CompleteSpace` instance on `H¹([0,T]; X)`. -/
instance bochnerSobolevH1.completeSpace (T : ℝ) (X : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] :
    CompleteSpace (bochnerSobolevH1 T X) := by
  unfold bochnerSobolevH1
  infer_instance

/-! ## The canonical inclusion `H¹ ↪ L²` -/

/-- The continuous linear **inclusion** of the Bochner–Sobolev space
`H¹([0,T]; X)` into the Bochner `L²` space `L²([0,T]; X)`. This is
the identity at the level of the underlying functions (the `H¹`
structure adds the requirement that the weak derivative also be in
`L²`), and the inclusion has operator norm `1`.

Skeleton: returns the identity continuous linear map under the
implementation `bochnerSobolevH1 := L²`. -/
def bochnerSobolevH1.toL2 (T : ℝ) (X : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] :
    bochnerSobolevH1 T X →L[ℝ]
      MeasureTheory.Lp X 2 (volume.restrict (Set.Ioc 0 T)) :=
  ContinuousLinearMap.id ℝ _

/-! ## The weak time derivative -/

/-- The continuous linear **time-derivative** operator
`H¹([0,T]; X) → L²([0,T]; X)`. For `u ∈ H¹([0,T]; X)` this is the
unique element `u' ∈ L²` such that
`∫₀ᵀ ⟨u(t), φ'(t)⟩ dt = -∫₀ᵀ ⟨u'(t), φ(t)⟩ dt` for every test
function `φ ∈ C^∞_c((0,T); X)`.

The operator is bounded with norm at most `1` relative to the `H¹`
graph norm.

Skeleton: returns the zero operator. Downstream files install the
genuine distributional derivative once the underlying type of
`bochnerSobolevH1` is refined. -/
def bochnerSobolevH1.timeDeriv (T : ℝ) (X : Type*)
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] :
    bochnerSobolevH1 T X →L[ℝ]
      MeasureTheory.Lp X 2 (volume.restrict (Set.Ioc 0 T)) :=
  0

end MaximalRegularity
end RicciFlow
end PDE
end DifferentialGeometry

end
