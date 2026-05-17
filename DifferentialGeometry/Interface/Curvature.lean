import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Realized.CurvatureTensor

/-!
# Public curvature adapters

This file is a consumption-facing facade gathering the project's smooth
Riemann / Ricci curvature surface under one namespace. A downstream user
who needs only the pointwise bilinear / multilinear curvature vocabulary
on a closed Riemannian manifold can import this single file.

The headline scalar adapters expose the canonical smooth Ricci tensor as
a plain function `M → T_x M → T_x M → ℝ` together with its symmetry and
the trace identity that defines it.

The remaining definitions re-export the bundled tensor-section types
(`Tensor02Section`, `Tensor04Section`, `Tensor13Section`), their fiber
counterparts (`Tensor02At`, `Tensor04At`, `Tensor13At`), and the field
helpers (`tensor02ToField`, `tensor04ToField`), along with the smooth
Ricci tensor as a continuous bilinear form `ricciTensor`, the
endomorphism form `ricciEndo`, and the standard structural theorems
`ricciTensor_apply`, `ricciTensor_symm`, `ricciTensor_contMDiff`.
-/

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Interface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Realized

/-! ## Scalar curvature adapters

The following convenience adapters expose the canonical smooth Ricci
tensor as a plain function of two tangent vectors at a point. -/

set_option linter.unusedSectionVars false in
/-- One-line adapter packaging the bundled smooth Ricci tensor
`ricciTensor g x : T_x M →L T_x M →L ℝ` as a plain real-valued function
of two tangent vectors. -/
noncomputable def ricciBilinear (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) : ℝ :=
  ricciTensor (I := I) g x v w

set_option linter.unusedSectionVars false in
/-- **Symmetry of the Ricci tensor.** `Ric(v, w) = Ric(w, v)` for every pair
of tangent vectors at every point. Restatement of `ricciTensor_symm`. -/
theorem ricciBilinear_symm (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciBilinear (I := I) (M := M) g x v w =
      ricciBilinear (I := I) (M := M) g x w v :=
  ricciTensor_symm (I := I) g x v w

set_option linter.unusedSectionVars false in
/-- **Trace identity for the Ricci tensor.** `Ric(v, w)` is the trace of the
endomorphism `Z ↦ R(Z, v) w` of `T_x M`. Restatement of `ricciTensor_apply`. -/
theorem ricciBilinear_eq_trace (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciBilinear (I := I) (M := M) g x v w =
      LinearMap.trace ℝ (TangentSpace I x) (ricciEndo (I := I) g x v w) :=
  ricciTensor_apply (I := I) g x v w

end Interface
end DifferentialGeometry

/-! ## Re-exports

The following `export` declarations make the smooth-Ricci and bundled
tensor-section primitives available directly under
`DifferentialGeometry.Interface`. After
`open DifferentialGeometry.Interface`, names such as `ricciTensor`,
`ricciTensor_apply`, `ricciTensor_symm`, `ricciTensor_contMDiff`,
`ricciEndo`, `Tensor02Section`, `Tensor04Section`, `Tensor13Section`,
`Tensor02At`, `Tensor04At`, `Tensor13At`, `tensor02ToField`, and
`tensor04ToField` resolve without further qualification. -/

namespace DifferentialGeometry.Interface

export DifferentialGeometry.Integral.Connection
  (ricciTensor ricciTensor_apply ricciTensor_symm ricciTensor_contMDiff
   ricciEndo)

export DifferentialGeometry.Realized
  (Tensor02Section Tensor04Section Tensor13Section
   Tensor02At Tensor04At Tensor13At
   tensor02ToField tensor04ToField)

end DifferentialGeometry.Interface

end
