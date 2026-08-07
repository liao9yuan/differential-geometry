import DifferentialGeometry.Tensor.Exterior.Exact
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

noncomputable section

open Bundle Set ContinuousAlternatingMap Function Filter
open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry
namespace DifferentialForm

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]

noncomputable def deRhamCochainComplex [BoundarylessManifold IM M] :
    CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of
    (fun n : ℕ => ModuleCat.of ℝ (DifferentialForm IM M n))
    (fun n : ℕ => ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n))
    (fun n : ℕ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [ModuleCat.ofHom, exteriorDerivativeLinearMap]
      simpa using (exteriorDerivative_extDeriv x))

@[simp] theorem deRhamCochainComplex_X [BoundarylessManifold IM M] (n : ℕ) :
    (deRhamCochainComplex (IM := IM) (M := M)).X n = ModuleCat.of ℝ (DifferentialForm IM M n) := by
  change (CochainComplex.of (fun n : ℕ => ModuleCat.of ℝ (DifferentialForm IM M n))
    (fun n : ℕ => ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n))
    (fun n : ℕ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [ModuleCat.ofHom, exteriorDerivativeLinearMap]
      simpa using (exteriorDerivative_extDeriv x))).X n = ModuleCat.of ℝ (DifferentialForm IM M n)
  exact CochainComplex.of_x (X := fun n : ℕ => ModuleCat.of ℝ (DifferentialForm IM M n))
    (d := fun n : ℕ => ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n))
    (sq := fun n : ℕ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [ModuleCat.ofHom, exteriorDerivativeLinearMap]
      simpa using (exteriorDerivative_extDeriv x)) n

@[simp] theorem deRhamCochainComplex_d [BoundarylessManifold IM M] (n : ℕ) :
    (deRhamCochainComplex (IM := IM) (M := M)).d n (n + 1) =
      ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n) := by
  change (CochainComplex.of (fun n : ℕ => ModuleCat.of ℝ (DifferentialForm IM M n))
    (fun n : ℕ => ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n))
    (fun n : ℕ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [ModuleCat.ofHom, exteriorDerivativeLinearMap]
      simpa using (exteriorDerivative_extDeriv x))).d n (n + 1) =
      ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n)
  exact CochainComplex.of_d (X := fun n : ℕ => ModuleCat.of ℝ (DifferentialForm IM M n))
    (d := fun n : ℕ => ModuleCat.ofHom (exteriorDerivativeLinearMap (IM := IM) (M := M) n))
    (sq := fun n : ℕ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [ModuleCat.ofHom, exteriorDerivativeLinearMap]
      simpa using (exteriorDerivative_extDeriv x)) n

end DifferentialForm
end DifferentialGeometry

end
