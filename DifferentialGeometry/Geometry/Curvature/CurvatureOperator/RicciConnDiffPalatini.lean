import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifferenceCurvature
import DifferentialGeometry.Geometry.Flow.ConnectionDifference

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- The connection-difference tensor `connDiff g₁ g₀` is the difference one-form
`CovariantDerivative.difference (LeviCivita g₁) (LeviCivita g₀)`, the object the curvature-difference
machinery of `ConnectionDifferenceCurvature.lean` is phrased in.  This is a definitional identity
(`connDiff` unfolds to exactly this `CovariantDerivative.difference`), recorded as a named bridge so
the Palatini identity can be cited in the project's primary `connDiff` vocabulary. -/
theorem connDiff_eq_difference (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiff (I := I) g₁ g₀ =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- The **directional covariant derivative of the connection-difference tensor** `A = connDiff g₁ g₀`
under the `g₀`-Levi-Civita connection:
`(∇₀_X A)(Y, Z) (x) = ∇₀_X(A(Y, Z)) (x) - A(∇₀_X Y, Z)(x) - A(Y, ∇₀_X Z)(x)`.

This is the `connDiff`-native packaging of `covDerivDiff (LeviCivita g₀) (LeviCivita g₁)`; it is the
first-order, divergence-type (`div(∇A)`) term of the intrinsic Palatini identity, the part that feeds
the principal symbol of the Ricci–DeTurck `C₂` linearization. -/
def covDerivConnDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) X Y Z x

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- Unfolding of `covDerivConnDiff` to the underlying `covDerivDiff` of the Levi-Civita pair. -/
theorem covDerivConnDiff_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    covDerivConnDiff (I := I) g₀ g₁ X Y Z x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) X Y Z x := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_sub_eq_connDiff_palatini (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w) x
              - covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x w) x)
            + (connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x v)
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x v x))) i :=
  ricciTensor_sub_eq_basisSum_difference (I := I) g₀ g₁ x v w

end Connection
end Integral
end DifferentialGeometry
