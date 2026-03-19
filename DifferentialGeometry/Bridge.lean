/- import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Tensor.RSTensor.LieDerivative

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Bridge: Connecting Analytic and Synthetic Geometry

This file bridges the analytic layer (concrete manifolds and coordinates in `DifferentialGeometry/Tensor`) and the synthetic layer (abstract algebra and geometry in `DifferentialGeometry/Algebra` and `DifferentialGeometry/Geometry`).

-/

namespace DifferentialGeometry.Bridge

-- 1. Topology Variables
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ⊤ M]

open TensorLieDeriv
open scoped Manifold

-- 2. Ring R and Module V
abbrev R := smoothScalarField (𝕜 := 𝕜) (M := M)
abbrev V := vectorField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)

noncomputable instance : CommRing (R (𝕜 := 𝕜) (M := M)) := Pi.commRing
noncomputable instance : AddCommGroup (V (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) := Pi.addCommGroup

noncomputable instance bridgeModule : Module (R (𝕜 := 𝕜) (M := M)) (V (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) where
  smul f X := fun x => f x • X x
  smul_zero f := funext fun x => smul_zero (f x)
  zero_smul X := funext fun x => zero_smul 𝕜 (X x)
  smul_add f X Y := funext fun x => smul_add (f x) (X x) (Y x)
  add_smul f g X := funext fun x => add_smul (f x) (g x) (X x)
  mul_smul f g X := funext fun x => mul_smul (f x) (g x) (X x)
  one_smul X := funext fun x => one_smul 𝕜 (X x)


/--
Analytic side: `directionalDerivScalar` in `Tensor/RSTensor/LieDerivative.lean`.
Synthetic side: `AbstractDerivationAction` in `Algebra/Basic.lean`.
-/
noncomputable instance bridgeDerivAction : AbstractDerivationAction (R (𝕜 := 𝕜) (M := M)) (V (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) where
  action X f := directionalDerivScalar f X


/--
Analytic side: `VectorField.mlieBracket` in `Tensor/RSTensor/LieDerivative.lean`.
Synthetic side: `AbstractLieBracket` in `Algebra/Basic.lean`.
-/
noncomputable instance bridgeLieBracket : AbstractLieBracket (V (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) where
  bracket X Y := VectorField.mlieBracket I X Y


/--
Analytic side: `SmoothRiemannianMetric` in `Tensor/RSTensor/LieDerivative.lean`.
Synthetic side: `AbstractMetricTensor` in `Algebra/Metric.lean`.
-/
noncomputable instance bridgeMetricTensor (analyticMetric : SmoothRiemannianMetric (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    AbstractMetricTensor (R (𝕜 := 𝕜) (M := M)) (V (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) where
  g X Y := metricProduct analyticMetric X Y
  symm := sorry
  bilinear_add_left := sorry
  bilinear_smul_left := sorry


/--
Analytic side: `LeviCivitaConnection` in `Tensor/RSTensor/LieDerivative.lean`.
Synthetic side: `AbstractLeviCivitaConnection` in `Geometry/Connection.lean`.
-/
noncomputable instance bridgeAffineConnection (analyticNabla : LeviCivitaConnection (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    AbstractLeviCivitaConnection (bridgeMetricTensor analyticNabla.metric) where
  nabla X Y := analyticNabla.covDeriv X Y
  nabla_add_left := sorry
  nabla_add_right := sorry
  nabla_smul_left := sorry
  leibniz := sorry
  compat := sorry
  torsion_zero := sorry


/--
The concrete directional derivative and Lie bracket on a manifold satisfy the abstract
derivation rules. Fields that require global smoothness/differentiability hypotheses
(not carried by the abstract class) are left as sorry.
-/
noncomputable instance bridgeDerivationRules :
    DerivationRules (R (𝕜 := 𝕜) (M := M)) (V (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) where
  action_add_left X Y f := by
    funext x
    exact map_add (mfderiv I 𝓘(𝕜) f x) (X x) (Y x)
  action_add_right X f g := sorry
  action_smul_left c X f := by
    funext x
    exact map_smul (mfderiv I 𝓘(𝕜) f x) (c x) (X x)
  action_smul_right X c f := sorry
  bracket_add_left X Y Z := sorry
  bracket_add_right X Y Z := sorry
  bracket_smul_left c X Y := sorry
  bracket_smul_right c X Y := sorry
  bracket_antisymm X Y := VectorField.mlieBracket_swap (I := I)

class GeneralTensorContractionRules (metric : AbstractMetricTensor (R (𝕜 := 𝕜) (M := M)) (V (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))) where
  /-- Trace commutes with covariant derivatives: tr_g(∇ T) = ∇(tr_g(T)) -/
  trace_cov_commute : sorry
  /-- Metric trace of Ricci variation equals Laplacian of scalar curvature: tr_g(∂_t Rc) = Δ R -/
  metric_trace_ricci_var : sorry

end DifferentialGeometry.Bridge
-/
