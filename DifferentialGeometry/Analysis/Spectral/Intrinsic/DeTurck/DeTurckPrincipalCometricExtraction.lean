import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RoughLaplacianCometricDoubleTrace
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldDifferentiatedTowerNormalForm
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculusRS

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
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in

private lemma g1_inner_injective (g₁ : SmoothRiemannianMetric I M) (x : M)
    {a b : TangentSpace I x} (hab : ∀ u : TangentSpace I x, g₁.inner x a u = g₁.inner x b u) :
    a = b := by
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g₁.pos x (a - b) hsub
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    have hsplit : g₁.inner x (a - b) (a - b)
        = g₁.inner x (a - b) a - g₁.inner x (a - b) b := by rw [← map_sub]
    rw [hsplit, g₁.symm x (a - b) a, g₁.symm x (a - b) b, hab (a - b)]
    ring
  exact absurd hzero (ne_of_gt hpos)

set_option linter.unusedSectionVars false in

private lemma cometricLmodel_covectorOfCLM_inner_loc (g₁ : SmoothRiemannianMetric I M) (y : M)
    (φ : E →L[ℝ] ℝ) (u : TangentSpace I y) :
    g₁.inner y (cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) u = φ (u : E) := by
  have h1 : cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ) =
      inverseMetricSharpFib (I := I) g₁ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₁ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  change (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)
      (fun _ : Fin 1 => (u : E)) = φ (u : E)
  rw [Tensor0SBundle.model_covectorOfCLM_apply]

set_option linter.unusedSectionVars false in

theorem cometricLmodel_sub_eq_gInvDiffRaisedEndo
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (φ : E →L[ℝ] ℝ) :
    cometricLmodel (I := I) g₁ x (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)
        - cometricLmodel (I := I) g₀ x (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ) =
      gInvDiffRaisedEndo (I := I) g₀ g₁ x
        (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) := by
  set α : Tensor0SSpace 1 I x :=
    Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ with hα
  set w₀ : TangentSpace I x := cometricLmodel (I := I) g₀ x α with hw₀
  set w₁ : TangentSpace I x := cometricLmodel (I := I) g₁ x α with hw₁
  apply g1_inner_injective (I := I) g₁ x
  intro u
  have hLHS : g₁.inner x (w₁ - w₀) u = g₁.inner x w₁ u - g₁.inner x w₀ u := by
    rw [map_sub (g₁.inner x), ContinuousLinearMap.sub_apply]
  have hg1w1 : g₁.inner x w₁ u = φ (u : E) := by
    rw [hw₁, hα]; exact cometricLmodel_covectorOfCLM_inner_loc (I := I) g₁ x φ u
  have hg0w0 : g₀.inner x w₀ u = φ (u : E) := by
    rw [hw₀, hα]; exact cometricLmodel_covectorOfCLM_inner_loc (I := I) g₀ x φ u
  have hRHS : g₁.inner x (gInvDiffRaisedEndo (I := I) g₀ g₁ x w₀) u
      = g₀.inner x w₀ u - g₁.inner x w₀ u :=
    inner_g1_gInvDiffRaisedEndo (I := I) g₀ g₁ x w₀ u
  rw [hLHS, hRHS, hg1w1, hg0w0]

set_option linter.unusedSectionVars false in

theorem ricciArmPrincipalCoeffPure_appCc_sub_eq_gInvDiffContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) W) x v
      - unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          (Fin.cons
            (gInvDiffRaisedEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  classical
  rw [ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian (I := I) (M := M) g₀ g₁ W x v,
    ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian (I := I) (M := M) g₀ g₀ W x v]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  set rest : Fin 3 → E := Fin.cons (((Module.finBasis ℝ E) k : TangentSpace I x) : E)
    (fun j : Fin 2 => ((v j : TangentSpace I x) : E)) with hrest
  set f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ :=
    unitModel (I := I) (M := M) g₀ 4 W x with hf
  have hcons : ∀ z : TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 W x
        (Fin.cons (z : E) (Fin.cons (((Module.finBasis ℝ E) k : TangentSpace I x) : E)
          (fun j : Fin 2 => ((v j : TangentSpace I x) : E))))
        = f (Fin.cons (z : E) rest) := fun z => rfl
  have hslot0 : ∀ a b : TangentSpace I x,
      f (Fin.cons ((a : E)) rest) - f (Fin.cons ((b : E)) rest)
        = f (Fin.cons (((a - b : TangentSpace I x) : E)) rest) := by
    intro a b
    have hcurry : ∀ z : TangentSpace I x,
        f (Fin.cons ((z : E)) rest)
          = ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => E) ℝ) f
              ((z : TangentSpace I x) : E)) rest := by
      intro z; rw [continuousMultilinearCurryLeftEquiv_apply]
    rw [hcurry a, hcurry b, hcurry (a - b)]
    rw [show (((a - b : TangentSpace I x) : E)) = ((a : E)) - ((b : E)) from rfl]
    rw [map_sub, ContinuousMultilinearMap.sub_apply]
  have hkey : unitModel (I := I) (M := M) g₀ 4 W x
        (Fin.cons (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) v))
        - unitModel (I := I) (M := M) g₀ 4 W x
          (Fin.cons (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v))
      = unitModel (I := I) (M := M) g₀ 4 W x
          (Fin.cons
            (gInvDiffRaisedEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
    rw [hcons (cometricLmodel (I := I) g₁ x _), hcons (cometricLmodel (I := I) g₀ x _),
      hcons (gInvDiffRaisedEndo (I := I) g₀ g₁ x _), hslot0]
    congr 2
    rw [show (((gInvDiffRaisedEndo (I := I) g₀ g₁ x
            (cometricLmodel (I := I) g₀ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) : TangentSpace I x) : E)) =
        ((cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))
          - cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) : TangentSpace I x) : E) from by
      rw [cometricLmodel_sub_eq_gInvDiffRaisedEndo (I := I) g₀ g₁ x
        ((Module.finBasis ℝ E).cDualBasis k)]]
  exact hkey

set_option linter.unusedSectionVars false in

theorem connLapCometric_g1_sub_g0_eq_gInvDiffContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v
      - unitModel (I := I) (M := M) g₀ 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
          (Fin.cons
            (gInvDiffRaisedEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace (I := I) g₀ S x v]
  exact ricciArmPrincipalCoeffPure_appCc_sub_eq_gInvDiffContraction (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v

def deTurckPrincipalCometricCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁
    - ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀

def deTurckPrincipalCometricArm (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 2 :=
  appCc (I := I) (M := M) g₀ 4 2
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
    (iteratedCovGrad (I := I) g₀ 0 2 2 S)

set_option linter.unusedSectionVars false in

private lemma unitModel_appCc_sub_distrib
    (g₀ : SmoothRiemannianMetric I M) (Φ₁ Φ₂ : SmoothCcTensor g₀ 4 2)
    (W : SmoothCcTensor g₀ 0 4) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (Φ₁ - Φ₂) W) x v =
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 Φ₁ W) x v
        - unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 Φ₂ W) x v := by
  rw [appCc_sub_left (I := I) (M := M) g₀ 4 2]
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]

set_option linter.unusedSectionVars false in

theorem deTurckPrincipalCometricArm_unitModel_eq_gInvDiffContraction
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
          (Fin.cons
            (gInvDiffRaisedEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  classical
  rw [deTurckPrincipalCometricArm, deTurckPrincipalCometricCoeff,
    unitModel_appCc_sub_distrib (I := I) (M := M) g₀
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)
      (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v]
  have hg0 : unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v
      = unitModel (I := I) (M := M) g₀ 2 (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v :=
    (rawTensorConnLapSmooth_eq_appCc_cometricDoubleTrace (I := I) g₀ S x v).symm
  rw [hg0]
  exact connLapCometric_g1_sub_g0_eq_gInvDiffContraction (I := I) (M := M) g₀ g₁ S x v

set_option linter.unusedSectionVars false in

theorem riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ h δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 := by
  sorry

set_option linter.unusedSectionVars false in

theorem riemannianFiberNormSq_deTurckPrincipalCometricArm_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ h δ) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (δ / (1 - δ)) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x) := by
  have hcomp := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 4 2 x
    (show TensorRSSpace 4 2 I x from
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x)
    (show TensorRSSpace 0 4 I x from
      (iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x)
  have harm_sec : (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ S).toSection x =
      (show TensorRSSpace 0 2 I x from
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x)) := by
    rw [deTurckPrincipalCometricArm,
      appCc_toSection (I := I) (M := M) g₀ 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 2 S) x]
  rw [harm_sec]
  refine hcomp.trans ?_
  have hcoeff := riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le
    (I := I) (M := M) g₀ g₁ h htie hδ_lt hδ_nn hδ x
  have hW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
      ((iteratedCovGrad (I := I) g₀ 0 2 2 S).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 4 x _
  exact mul_le_mul_of_nonneg_right hcoeff hW_nn

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
