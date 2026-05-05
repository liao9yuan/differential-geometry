import DifferentialGeometry.Analysis.Laplacian.DirichletForm
import DifferentialGeometry.Analysis.Laplacian.MetricBounds
import DifferentialGeometry.Integral.DivergenceTheorem.Gradient

/-!
# Smooth-function inclusion into the intrinsic `H¹` space

For a smooth function `f : M → ℝ` on a closed Riemannian manifold `(M, g)`,
the gradient `gradFun g f` is a smooth tangent section. This file packages
the L² class of `f` together with the L² class of `gradFun g f` as an
element of the intrinsic `H¹` space `H1Intrinsic g`.

The construction is delivered via `smoothInclude`: given `f` and a smoothness
hypothesis, it produces an `H¹` element whose `toLp` equals the L² class of
`f` and whose `gradL2` equals the L² class of `gradFun g f`.

The verification of the joint AESM pairing clause `PairAEMeasurable` for the
smooth witness is performed at this point. We use the fact that for smooth
functions, the gradient is continuous and so the pairing
`x ↦ g.inner x (gradFun g f x) (V x)` against any AESM `V` reduces — via a
chart-by-chart bilinear-form decomposition — to AESM operations on AESM
inputs.

## Main definitions

* (forthcoming) `smoothInclude g f hf` : the `H¹` element associated to a
  smooth function.

This file lays the groundwork for the smooth bridge; the full construction
including the joint AESM verification depends on chart-localized
infrastructure that is beyond the immediate scope.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

end Laplacian
end Analysis
end DifferentialGeometry

end
