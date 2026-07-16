import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.EigenvectorTensorHsToWtwokTwo
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion

/-!
# Smooth tensors in the spectral Sobolev scale

This file packages the generic spectral embedding of smooth covariant tensors
as a linear map and proves that its range is dense at every nonnegative order.
-/

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The generic spectral embedding of smooth covariant tensors, as a linear map. -/
noncomputable def ccToHsLin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ) :
    SmoothCcTensor g 0 s →ₗ[ℝ] tensorHs (I := I) (M := M) g 0 s σ where
  toFun := ccTensorToHs (I := I) (M := M) g s σ
  map_add' := ccTensorToHs_add (I := I) (M := M) g s σ
  map_smul' := ccTensorToHs_smul (I := I) (M := M) g s σ

/-- Applying `ccToHsLin` is the existing generic spectral embedding. -/
@[simp] theorem ccToHsLin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : ℝ)
    (S : SmoothCcTensor g 0 s) :
    ccToHsLin (I := I) (M := M) g s σ S =
      ccTensorToHs (I := I) (M := M) g s σ S :=
  rfl

/-- The smooth representative of a finitely supported spectral vector maps
back to that vector at every nonnegative order. -/
theorem ccToHsLin_repr
    (g : SmoothRiemannianMetric I M) (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (v : tensorHs (I := I) (M := M) g 0 s σ)
    (hv : (Function.support v.coeff).Finite) :
    ccToHsLin (I := I) (M := M) g s σ
        (tensorHsSmoothRepr (I := I) (M := M) v hv) = v := by
  apply tensorHs.ext
  funext i
  simp only [ccToHsLin_apply, ccTensorToHs_coeff]
  rw [SmoothCcTensor.toL2_apply,
    tensorHsSmoothRepr_toL2 (I := I) (M := M) hσ v hv,
    tensorHsToL2_tensorL2Coeff (I := I) (M := M) hσ]

/-- For nonnegative order, smooth covariant tensors are dense in the spectral
Sobolev space. -/
theorem ccToHsLin_dense
    (g : SmoothRiemannianMetric I M) (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    DenseRange (ccToHsLin (I := I) (M := M) g s σ) := by
  classical
  refine (tensorHsFiniteSupportSubmodule_dense
    (I := I) (M := M) (g := g) (r := 0) (s := s) (σ := σ)).mono ?_
  intro v hv
  have hvfs : (Function.support v.coeff).Finite :=
    (tensorHs.mem_finiteSupportSubmodule (I := I) (M := M) v).mp hv
  exact ⟨tensorHsSmoothRepr (I := I) (M := M) v hvfs,
    ccToHsLin_repr (I := I) (M := M) g s hσ v hvfs⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
