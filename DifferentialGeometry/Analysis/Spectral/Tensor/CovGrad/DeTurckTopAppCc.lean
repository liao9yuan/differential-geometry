import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Tensor.Multilinear.DomDomCongrSection

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def deTurckLieArm2DivSlotPermA : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (2 : Fin 4) 3 * Equiv.swap (3 : Fin 4) 1

def deTurckLieArm2DivSlotPermAT : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 3 * Equiv.swap (3 : Fin 4) 1

theorem deTurckLieArm2DivSlotPermA_apply :
    deTurckLieArm2DivSlotPermA 0 = 2 ∧ deTurckLieArm2DivSlotPermA 1 = 0 ∧
      deTurckLieArm2DivSlotPermA 2 = 3 ∧ deTurckLieArm2DivSlotPermA 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem deTurckLieArm2DivSlotPermAT_apply :
    deTurckLieArm2DivSlotPermAT 0 = 3 ∧ deTurckLieArm2DivSlotPermAT 1 = 0 ∧
      deTurckLieArm2DivSlotPermAT 2 = 2 ∧ deTurckLieArm2DivSlotPermAT 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

noncomputable def domDomCongrFibPerm (σ : Equiv.Perm (Fin 4)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          σ).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

theorem domDomCongrFibPerm_apply (σ : Equiv.Perm (Fin 4)) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    domDomCongrFibPerm (I := I) σ x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [domDomCongrFibPerm]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

noncomputable def deTurckLieTraceFib (g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (domDomCongrFibPerm (I := I) σ x)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem deTurckLieTraceFib_contMDiff (g₁ : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin 4)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (deTurckLieTraceFib (I := I) g₁ σ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => deTurckLieTraceFib (I := I) g₁ σ x)
  intro Y
  let Ys : MultilinearSection ℝ E I (TangentSpace I) ∞ 4 :=
    ⟨fun x => Y x, Y.contMDiff⟩
  have hYρ := (MultilinearSection.domDomCongr (IB := I) ∞ σ Ys).contMDiff
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hYρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [deTurckLieTraceFib, ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply]
  rfl

noncomputable def deTurckLieTraceCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) : SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x)
      contMDiff_toFun := deTurckLieTraceFib_contMDiff (I := I) g₁ σ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem deTurckLieTraceCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x) := rfl

set_option linter.unusedVariables false in

def deTurckLieArm2PrincipalCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermA
    + deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ deTurckLieArm2DivSlotPermAT
    - traceHessianCoeff (I := I) (M := M) g₀ g₁

set_option linter.unusedSectionVars false in

private lemma appCc_sub_left_local (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (Φ₁ - Φ₂) W =
      appCc (I := I) (M := M) g r s Φ₁ W - appCc (I := I) (M := M) g r s Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g r s Φ₁ W - appCc (I := I) (M := M) g r s Φ₂ W).toSection x) =
      (appCc (I := I) (M := M) g r s Φ₁ W).toSection x -
        (appCc (I := I) (M := M) g r s Φ₂ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((Φ₁ - Φ₂).toSection x : TensorRSSpace r s I x) = Φ₁.toSection x - Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]

set_option linter.unusedSectionVars false in

private lemma unitModel_add2_apply_local (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v + unitModel (I := I) (M := M) g₀ 2 S' x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]

set_option linter.unusedSectionVars false in

private lemma unitModel_sub2_apply_local (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (S - S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v - unitModel (I := I) (M := M) g₀ 2 S' x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]

set_option linter.unusedSectionVars false in

theorem deTurckLieTraceCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (D : SmoothCcTensor g₀ 0 4) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ) D) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g₀ 4 D x)
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (deTurckLieTraceCoeff (I := I) (M := M) g₀ g₁ σ).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieTraceCoeff_toSection]
  rw [show (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from deTurckLieTraceFib (I := I) g₁ σ x))
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) =
      deTurckLieTraceFib (I := I) g₁ σ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          D.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieTraceFib, ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply,
    cometricDoubleTraceFib_toModel, Tensor0SSpace.toModel_ofModel, modelDoubleTrace_apply]
  simp only [unitModel]

set_option linter.unusedSectionVars false in

theorem deTurckLieArm2PrincipalCoeff_appCc_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (D : SmoothCcTensor g₀ 0 4) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (deTurckLieArm2PrincipalCoeff (I := I) g₀ g₁ g_bg) D) x v =
      ((∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 4 D x
            ![v 0,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              v 1, (Module.finBasis ℝ E) k])
        + ∑ k : Fin (Module.finrank ℝ E),
            unitModel (I := I) (M := M) g₀ 4 D x
              ![v 1,
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)),
                v 0, (Module.finBasis ℝ E) k])
      - ∑ k : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 4 D x
            ![v 0, v 1,
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)),
              (Module.finBasis ℝ E) k] := by
  rw [deTurckLieArm2PrincipalCoeff, appCc_sub_left_local, appCc_add_left,
    unitModel_sub2_apply_local, unitModel_add2_apply_local,
    deTurckLieTraceCoeff_appCc_eq, deTurckLieTraceCoeff_appCc_eq,
    traceHessianCoeff_appCc_eq]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t)
        (by funext i; fin_cases i <;> rfl)
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t)
        (by funext i; fin_cases i <;> rfl)
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg (fun t : Fin 4 → E => unitModel (I := I) (M := M) g₀ 4 D x t)
      (by funext i; fin_cases i <;> rfl)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
