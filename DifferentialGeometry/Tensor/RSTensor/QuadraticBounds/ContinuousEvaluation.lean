import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

private local instance tensor02NormedAddCommGroup (x : M) :
    NormedAddCommGroup
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  Tensor0SBundle.tensor0SSpace_normedAddCommGroup 2 x

private local instance tensor02NormedSpace (x : M) :
    NormedSpace Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  Tensor0SBundle.tensor0SSpace_normedSpace 2 x

private local instance tensor02AddCommGroup (x : M) :
    AddCommGroup
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  @NormedAddCommGroup.toAddCommGroup _ (tensor02NormedAddCommGroup (I := I) x)

private local instance tensor02Module (x : M) :
    Module Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  @NormedSpace.toModule _ _ _ _ (tensor02NormedSpace (I := I) x)

private local instance tensor02TopologicalSpace (x : M) :
    TopologicalSpace
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _
        (@NormedAddCommGroup.toMetricSpace _ (tensor02NormedAddCommGroup (I := I) x))))

noncomputable def tensor02EvalCLM {x : M} (v w : TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x →L[Real] Real :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A ↦ eval02 (I := I) (M := M) A v w
    map_add' := by
      intro A B
      rfl
    map_smul' := by
      intro c A
      rfl }

@[simp]
theorem tensor02EvalCLM_apply {x : M} (v w : TangentSpace I x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    tensor02EvalCLM (I := I) (M := M) v w A = eval02 (I := I) (M := M) A v w :=
  rfl

noncomputable def tensor02EvalSelfCLM {x : M} (v : TangentSpace I x) :
    StrongDual Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A ↦ quad02 (I := I) (M := M) A v
    map_add' := by
      intro A B
      rfl
    map_smul' := by
      intro c A
      rfl }

@[simp]
theorem tensor02EvalSelfCLM_apply {x : M} (v : TangentSpace I x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    tensor02EvalSelfCLM (I := I) (M := M) v A = quad02 (I := I) (M := M) A v :=
  rfl

end DifferentialGeometry
