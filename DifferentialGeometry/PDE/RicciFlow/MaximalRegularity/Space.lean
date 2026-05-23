import DifferentialGeometry.PDE.RicciFlow.MaximalRegularity.BochnerSobolev
import DifferentialGeometry.PDE.RicciFlow.HeatSemigroup.Defs

/-!
# The maximal-regularity space for the connection-Laplacian heat equation

For the connection-Laplacian heat equation on `(r, s)`-tensor fields
of a closed Riemannian manifold `(M, g)`, this file introduces the
**maximal-regularity space**

  `MaxReg([0,T]; r, s, g) := L²([0,T]; Dom(Δ_∇^F)) ∩ H¹([0,T]; TensorL2)`

of `TensorL2 r s g`-valued functions on the time interval `[0, T]`
whose values lie in the operator domain of the Friedrichs self-adjoint
extension `Δ_∇^F` (so that the spatial operator acts on the solution
for almost every time) and whose weak time derivative lies in
`L²([0,T]; TensorL2)`.

This is the natural Banach (Hilbert) space in which to phrase the
**maximal-regularity theorem** for the inhomogeneous heat equation:
for forcing `F ∈ L²([0,T]; TensorL2)` and initial data
`u₀ ∈ TensorL2`, the unique strong solution `u` lies in
`MaxReg([0,T]; r, s, g)`, with
`‖u‖_{MaxReg} ≲ ‖F‖_{L²} + ‖u₀‖_{TensorL2}` (the De Simon estimate).

## Main definitions

* `maxRegSpace g r s T` — the maximal-regularity space.

## Main instances

* `maxRegSpace.normedAddCommGroup` — the Hilbert-space norm.
* `maxRegSpace.completeSpace` — completeness.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace MaximalRegularity

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian
open DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension
open DifferentialGeometry.PDE.RicciFlow.HeatSemigroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The maximal-regularity space -/

set_option linter.unusedSectionVars false in
/-- The **maximal-regularity space** for the inhomogeneous heat
equation on `(r, s)`-tensor fields over the time interval `[0, T]`:

  `MaxReg([0,T]; r, s, g) := L²([0,T]; Dom(Δ_∇^F)) ∩ H¹([0,T]; TensorL2)`.

Elements `u` are `TensorL2 r s g`-valued functions on `[0, T]`
satisfying:

* for almost every `t ∈ [0, T]`, `u(t) ∈ Dom(Δ_∇^F)`, and
  `t ↦ Δ_∇^F u(t)` lies in `L²([0,T]; TensorL2)` (spatial regularity);
* `u` has a weak time derivative `∂_t u ∈ L²([0,T]; TensorL2)`
  (temporal regularity).

The norm is the natural graph norm
`‖u‖² := ‖u‖_{L²([0,T]; TensorL2)}² + ‖Δ_∇^F u‖_{L²([0,T]; TensorL2)}²
            + ‖∂_t u‖_{L²([0,T]; TensorL2)}²`.

This is a Hilbert space (the inner product is the one underlying the
graph norm); the maximal-regularity theorem produces the unique
solution of the inhomogeneous heat equation as an element of this
space.

In the skeleton the underlying type is the Bochner–Sobolev space
`bochnerSobolevH1 T (TensorL2 r s g)`: this provides the correct
typeclass structure and a stable public API. Downstream files refine
the underlying type to the genuine intersection space while keeping
the public-API surface unchanged. -/
def maxRegSpace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : ℝ) : Type _ :=
  bochnerSobolevH1 T (TensorL2 r s g)

/-! ## Typeclass instances -/

set_option linter.unusedSectionVars false in
/-- The `NormedAddCommGroup` structure on the maximal-regularity space. -/
instance maxRegSpace.normedAddCommGroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : ℝ) :
    NormedAddCommGroup (maxRegSpace (I := I) g r s T) := by
  unfold maxRegSpace
  infer_instance

set_option linter.unusedSectionVars false in
/-- The maximal-regularity space is a real normed space. -/
instance maxRegSpace.normedSpace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : ℝ) :
    NormedSpace ℝ (maxRegSpace (I := I) g r s T) := by
  unfold maxRegSpace
  infer_instance

set_option linter.unusedSectionVars false in
/-- The maximal-regularity space is complete. -/
instance maxRegSpace.completeSpace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : ℝ) :
    CompleteSpace (maxRegSpace (I := I) g r s T) := by
  unfold maxRegSpace
  infer_instance

end MaximalRegularity
end RicciFlow
end PDE
end DifferentialGeometry

end
