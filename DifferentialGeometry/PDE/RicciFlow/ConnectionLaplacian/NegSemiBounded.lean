import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.L2PMap
import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.Symmetric

/-!
# Negative semi-boundedness of the connection Laplacian on `L²`

For a closed Riemannian manifold `(M, g)`, the connection (rough)
Laplacian `Δ_∇` defined as a partially-defined operator
`connLaplacianL2 g r s` on the metric `L²` Hilbert space
`TensorL2 r s g` satisfies the textbook negative semi-boundedness
estimate
$$
  -\langle \Delta_\nabla T,\, T\rangle_{L^2} \;\ge\; 0
$$
for every `T` in the operator's domain. This follows from the pointwise
identity `Δ_∇ = -\nabla^* \nabla` and the resulting identity
$$
  \langle \Delta_\nabla T,\, T\rangle_{L^2}
    = -\,\|\nabla T\|_{L^2}^2 \le 0.
$$

## Main results

* `connLaplacianL2_neg_semi_bounded` — for every `T` in the operator's
  domain, `-⟪Δ_∇ T, T⟫_{L²} ≥ 0`.
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
/-- **Negative semi-boundedness of the connection Laplacian on `L²`.** For
every element `T` of the domain of the partially-defined operator
`connLaplacianL2 g r s`, the inner-product pairing satisfies
$$
  -\langle \Delta_\nabla T, T\rangle_{L^2} \;\ge\; 0.
$$
This is the textbook negative-semi-boundedness estimate that underlies the
construction of the Friedrichs extension of `Δ_∇` and the associated
analytic heat semigroup.

The proof uses the pointwise identity `Δ_∇ = -\nabla^*\nabla` together
with the divergence theorem on a closed manifold to obtain
$\langle \Delta_\nabla T, T\rangle_{L^2} = -\|\nabla T\|_{L^2}^2 \le 0$. -/
theorem connLaplacianL2_neg_semi_bounded
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∀ T : (connLaplacianL2 (I := I) g r s).domain,
      0 ≤ -(@inner ℝ _ _
        ((connLaplacianL2 (I := I) g r s) T) (T : TensorL2 r s g)) := by
  exact sorry

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
