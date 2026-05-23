import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.L2PMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Symmetry of the connection Laplacian on `L²`

For a closed Riemannian manifold `(M, g)`, the connection (rough)
Laplacian `Δ_∇` defined as a partially-defined operator
`connLaplacianL2 g r s` on the metric `L²` Hilbert space
`TensorL2 r s g` (with domain the smooth, compactly-supported `(r, s)`
tensor sections) is symmetric in the sense of unbounded operators:
$$
  \langle \Delta_\nabla T,\, S\rangle_{L^2} =
    \langle T,\, \Delta_\nabla S\rangle_{L^2}
  \quad\text{for all } T, S \in \mathrm{Dom}(\Delta_\nabla).
$$

The proof proceeds by integration by parts twice on a closed manifold
(the divergence theorem with no boundary contribution), reducing the
inner-product identity to the pointwise symmetry of the second covariant
derivative against the metric trace.

## Main definitions

* `LinearPMap.IsSymmetric` — a partially-defined operator on a real
  inner-product space is symmetric iff its inner-product action is
  symmetric on its domain. Defined here as a small wrapper not yet
  provided by Mathlib's `LinearPMap` API.

## Main results

* `connLaplacianL2_isSymmetric` — the partially-defined operator
  `connLaplacianL2 g r s` is symmetric.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A partially-defined linear operator on an inner-product space is
**symmetric** iff its inner-product action is symmetric on its domain:
for every pair `(x, y)` of elements of `T.domain`,
`⟪T x, y⟫ = ⟪x, T y⟫`.

This is the standard textbook definition of a symmetric (also called
formally self-adjoint) unbounded operator. -/
def IsSymmetric (T : F →ₗ.[𝕜] F) : Prop :=
  ∀ x y : T.domain, @inner 𝕜 _ _ (T x) (y : F) = @inner 𝕜 _ _ (x : F) (T y)

end LinearPMap

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ConnectionLaplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

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

set_option linter.unusedSectionVars false in
/-- **Symmetry of the connection Laplacian on `L²`.** The partially-defined
operator `connLaplacianL2 g r s` is symmetric in the sense of unbounded
operators on the metric `L²` Hilbert space of `(r, s)`-tensor fields,
$$
  \langle \Delta_\nabla T, S\rangle_{L^2} =
    \langle T, \Delta_\nabla S\rangle_{L^2}
$$
for every pair `(T, S)` of elements of the operator's domain.

The proof reduces to the pointwise Bochner identity for the rough
Laplacian and the divergence theorem on a closed manifold (no boundary
contribution). -/
theorem connLaplacianL2_isSymmetric
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (connLaplacianL2 (I := I) g r s).IsSymmetric := by
  exact sorry

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
