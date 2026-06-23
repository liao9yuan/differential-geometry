import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricDiffCovGradKoszul
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.ConnDiffCovGradBridge
import DifferentialGeometry.Geometry.Metric.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.InverseMetricFieldParallel
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradSlotPermutationNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def covGradEval (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x)
      (unitZeroSec (I := I) (M := M) x))
    (Fin.cons (X x) (Fin.cons (Y x) ![Z x]))

set_option linter.unusedSectionVars false in

theorem connDiff_inner_eq_half_covGradKoszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w =
        g₁.inner b u w - g₀.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    2 * g₁.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x)) (Z x) =
      covGradEval (I := I) (M := M) g₀ S X Y Z x
        + covGradEval (I := I) (M := M) g₀ S Y X Z x
        - covGradEval (I := I) (M := M) g₀ S Z X Y x := by
  
  
  have hzero : ∀ (P Q R : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      metricDiffCovDeriv (I := I) g₀ g₀ (fun b => P b) (fun b => Q b) (fun b => R b) x = 0 := by
    intro P Q R
    unfold metricDiffCovDeriv
    rw [sub_self]
  
  have hXYZ : covGradEval (I := I) (M := M) g₀ S X Y Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ (fun b => X b) (fun b => Y b) (fun b => Z b) x := by
    rw [covGradEval, covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
      (I := I) (M := M) g₀ g₁ g₀ S hbil X Y Z x, hzero X Y Z, sub_zero]
  have hYXZ : covGradEval (I := I) (M := M) g₀ S Y X Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ (fun b => Y b) (fun b => X b) (fun b => Z b) x := by
    rw [covGradEval, covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
      (I := I) (M := M) g₀ g₁ g₀ S hbil Y X Z x, hzero Y X Z, sub_zero]
  have hZXY : covGradEval (I := I) (M := M) g₀ S Z X Y x =
      metricDiffCovDeriv (I := I) g₁ g₀ (fun b => Z b) (fun b => X b) (fun b => Y b) x := by
    rw [covGradEval, covGrad02_unitModel_eval_eq_metricDiffCovDeriv'
      (I := I) (M := M) g₀ g₁ g₀ S hbil Z X Y x, hzero Z X Y, sub_zero]
  rw [hXYZ, hYXZ, hZXY]
  
  
  exact connDiff_koszul_metricDiff (I := I) g₁ g₀
    X.mdifferentiableAt Y.mdifferentiableAt Z.mdifferentiableAt

def koszulCovGradCovec (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    Tensor0SSpace 1 I x :=
  dualToCotangent (I := I)
    ((g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x))).toLinearMap)

set_option linter.unusedSectionVars false in

@[simp] theorem koszulCovGradCovec_dual_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) ζ =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x)) ζ := by
  rw [koszulCovGradCovec, cotangentToDual_dualToCotangent]
  rfl

set_option linter.unusedSectionVars false in

theorem koszulCovGradCovec_dual_apply_covGrad
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w =
        g₁.inner b u w - g₀.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) (Z x) =
      (1 / 2 : ℝ) *
        (covGradEval (I := I) (M := M) g₀ S X Y Z x
          + covGradEval (I := I) (M := M) g₀ S Y X Z x
          - covGradEval (I := I) (M := M) g₀ S Z X Y x) := by
  rw [koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ X Y x (Z x)]
  have h := connDiff_inner_eq_half_covGradKoszul (I := I) (M := M) g₀ g₁ S hbil X Y Z x
  linarith [h]

set_option linter.unusedSectionVars false in

theorem connDiff_eq_appCc_invGram_covGrad
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x) =
      inverseMetricSharpFib (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) := by
  
  refine (SmoothRiemannianMetric.eq_of_inner_eq g₁ (fun ζ => ?_)).symm
  
  
  rw [inverseMetricSharpFib_inner (I := I) g₁ x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) ζ,
      cotangentToDualLinear_apply,
      koszulCovGradCovec_dual_apply (I := I) (M := M) g₀ g₁ X Y x ζ]

set_option linter.unusedSectionVars false in

theorem cotangentCov_leviCivita_diff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    {θ : Π b : M, TangentSpace I b →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent (I := I) θ x)
    (v w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w -
        ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) w =
      -θ x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v) := by
  classical
  
  set X : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXdef
  set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hYdef
  have hX := smoothExtensionTangent_mdiff (I := I) x v x
  have hY := smoothExtensionTangent_mdiff (I := I) x w x
  have hXx : X x = v := smoothExtensionTangent_eq (I := I) x v
  have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w
  
  have h₁ : ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w =
      cotangentScalar ((LeviCivita (I := I) g₁).toFun) θ x X Y := by
    rw [cotangentCov_toFun, cotangentCovFun_apply,
        show v = X x from hXx.symm, show w = Y x from hYx.symm,
        cotangentCovAt_apply_of_diff (LeviCivita (I := I) g₁) hθ hX hY]
  have h₀ : ((cotangentCov (LeviCivita (I := I) g₀)).toFun θ x v) w =
      cotangentScalar ((LeviCivita (I := I) g₀).toFun) θ x X Y := by
    rw [cotangentCov_toFun, cotangentCovFun_apply,
        show v = X x from hXx.symm, show w = Y x from hYx.symm,
        cotangentCovAt_apply_of_diff (LeviCivita (I := I) g₀) hθ hX hY]
  rw [h₁, h₀, cotangentScalar_def, cotangentScalar_def]
  
  have hconn : PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v =
      (LeviCivita (I := I) g₁).toFun Y x v - (LeviCivita (I := I) g₀).toFun Y x v := by
    have := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
    rw [hYx] at this
    exact this
  rw [hconn, hXx]
  rw [map_sub]
  ring

set_option linter.unusedSectionVars false in

theorem cotangentToCLM_koszulCovGradCovec
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b) =
      g₁.inner b (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b)) := by
  rw [koszulCovGradCovec]
  apply ContinuousLinearMap.ext
  intro w
  exact cotangentToDual_dualToCotangent (I := I)
    ((g₁.inner b (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b))).toLinearMap) ▸
      (rfl : cotangentToDual (I := I) (dualToCotangent (I := I)
        ((g₁.inner b (PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b))).toLinearMap)) w =
        cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b) w)

set_option linter.unusedSectionVars false in

theorem koszulCovGradCovecCLM_mdiffAtCotangent
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtCotangent (I := I)
      (fun b : M => cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x := by
  have hflat : (fun b : M => cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) =
      metricFlat (I := I) g₁
        (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b)) := by
    funext b
    rw [cotangentToCLM_koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b]
    rfl
  rw [hflat]
  
  
  have hconn_sm := PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ Y.contMDiff Z.contMDiff
  have hconn_at := (hconn_sm x).mdifferentiableAt (by simp)
  exact metricFlat_mdiff (I := I) g₁ hconn_at

set_option linter.unusedSectionVars false in

theorem covDerivConnDiff_principal_align
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
        (fun b : M => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) w =
      ((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b : M => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) w
        - cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w (X x)) := by
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ g₁ Z Y x
  have hbridge := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁ hθ (X x) w
  
  
  linarith [hbridge]

set_option linter.unusedSectionVars false in

theorem covDerivConnDiff_eq_invGramSharp_graded
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x =
      inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (inverseMetricSharpFib (I := I) g₁ x
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x)
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x) := by
  classical
  
  set K : Π b : M, Tensor0SSpace 1 I b :=
    fun b => koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b with hKdef
  
  have hWeq : (fun b : M => inverseMetricSharpFib (I := I) g₁ b (K b)) =
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b)) := by
    funext b
    exact (connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ Z Y b).symm
  set W : Π b : M, TangentSpace I b :=
    fun b => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (Y b) (Z b) with hWdef
  
  have hW_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (W b)) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ Y.contMDiff Z.contMDiff
  have hW_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (W b)) x :=
    (hW_sm x).mdifferentiableAt (by simp)
  
  have hWsharp_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (inverseMetricSharpFib (I := I) g₁ b (K b))) x := by
    have hfun : (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (inverseMetricSharpFib (I := I) g₁ b (K b))) =
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (W b)) := by
      funext b; rw [congrFun hWeq b]
    rw [hfun]; exact hW_at
  
  have hswap : (LeviCivita (I := I) g₀).toFun (fun b => W b) x (X x) =
      (LeviCivita (I := I) g₁).toFun (fun b => W b) x (X x) -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x (W x) (X x) := by
    have h := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := fun b => W b) (x := x) hW_at (X x)
    rw [h]; abel
  
  have hpar := inverseMetricSharpField_covGrad_eq_zero (I := I) g₁ K hWsharp_at (X x)
  
  have hW1 : (LeviCivita (I := I) g₁).toFun (fun b => W b) x (X x) =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₁)).toFun
            (fun b : M => cotangentToCLM (I := I) (K b)) x (X x))) := by
    rw [show (fun b => W b) =
        (fun b : M => inverseMetricSharpFib (I := I) g₁ b (K b)) from hWeq.symm]
    exact hpar
  
  have hWx : W x = inverseMetricSharpFib (I := I) g₁ x (K x) := by
    have := congrFun hWeq x
    rw [hWdef]; exact this.symm
  
  have hexpand : covDerivConnDiff (I := I) g₀ g₁
        (fun b => X b) (fun b => Z b) (fun b => Y b) x =
      (LeviCivita (I := I) g₀).toFun (fun b => W b) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x)
            ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x) := rfl
  rw [hexpand, hswap, hW1, hWx]

set_option linter.unusedSectionVars false in

theorem covDerivConnDiff_diff_endpoint_graded
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x
        - covDerivConnDiff (I := I) g₀ g₁' (fun b => X b) (fun b => Z b) (fun b => Y b) x =
      (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)))
          - inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x (X x))))
        + (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x (X x)))
            - inverseMetricSharpFib (I := I) g₁' x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x (X x))))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (inverseMetricSharpFib (I := I) g₁ x
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) (X x)
            - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (inverseMetricSharpFib (I := I) g₁' x
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y x)) (X x))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x)
              ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x))
            - PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Y x)
                ((LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x)))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)
            - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)) (Z x)) := by
  rw [covDerivConnDiff_eq_invGramSharp_graded (I := I) (M := M) g₀ g₁ X Y Z x,
      covDerivConnDiff_eq_invGramSharp_graded (I := I) (M := M) g₀ g₁' X Y Z x]
  abel

def koszulSlotPerm : Equiv.Perm (Fin 4) :=
  Equiv.Perm.decomposeFin.symm (0, finRotate 3)

set_option linter.unusedSectionVars false in

private theorem koszulSlotPerm_apply :
    koszulSlotPerm 0 = 0 ∧ koszulSlotPerm 1 = 2 ∧ koszulSlotPerm 2 = 3 ∧ koszulSlotPerm 3 = 1 := by
  unfold koszulSlotPerm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

noncomputable def combinedTrace42Model
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel 4 ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel 2 ℝ E :=
  (1 / 2 : ℝ) •
    ((modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            koszulSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap)
      + (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            (Equiv.swap (0 : Fin 2) 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((modelDoubleTrace (E := E) 2 L).comp
            ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
              koszulSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap))
      - modelDoubleTrace (E := E) 2 L)

set_option linter.unusedSectionVars false in

theorem combinedTrace42Model_apply
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    combinedTrace42Model (E := E) L D m =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![m 0, m 1, (Module.finBasis ℝ E) k])
            + D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![m 1, m 0, (Module.finBasis ℝ E) k])
            - D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) m))) := by
  classical
  obtain ⟨hp0, hp1, hp2, hp3⟩ := koszulSlotPerm_apply
  
  have hcongr_eq : ∀ (D' : Tensor0SBundle.Tensor0SModel 4 ℝ E),
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          koszulSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap D' =
        ContinuousMultilinearMap.domDomCongr koszulSlotPerm D' := by
    intro D'
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  have hswap_eq : ∀ (T : Tensor0SBundle.Tensor0SModel 2 ℝ E),
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          (Equiv.swap (0 : Fin 2) 1)).toContinuousLinearEquiv.toContinuousLinearMap T =
        ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1) T := by
    intro T
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  
  have hT03 : ∀ (mm : Fin 2 → E),
      modelDoubleTrace (E := E) 2 L
          (ContinuousMultilinearMap.domDomCongr koszulSlotPerm D) mm =
        ∑ k : Fin (Module.finrank ℝ E),
          D (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
              ![mm 0, mm 1, (Module.finBasis ℝ E) k]) := by
    intro mm
    rw [modelDoubleTrace_apply (E := E) 2 L _ mm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext j
    have hperm : koszulSlotPerm j = ![(0 : Fin 4), 2, 3, 1] j := by
      fin_cases j
      · exact hp0
      · exact hp1
      · exact hp2
      · exact hp3
    rw [hperm]
    fin_cases j <;> rfl
  rw [combinedTrace42Model]
  rw [ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply]
  
  rw [modelDoubleTrace_apply (E := E) 2 L D m]
  
  rw [ContinuousLinearMap.comp_apply, hcongr_eq, hT03 m]
  
  rw [ContinuousLinearMap.comp_apply, hswap_eq, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousLinearMap.comp_apply, hcongr_eq, hT03 (fun i => m (Equiv.swap (0 : Fin 2) 1 i))]
  
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  
  have htuple : (![m (Equiv.swap (0 : Fin 2) 1 0), m (Equiv.swap (0 : Fin 2) 1 1),
        (Module.finBasis ℝ E) k] : Fin 3 → E) = ![m 1, m 0, (Module.finBasis ℝ E) k] := by
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [htuple]

noncomputable def ricciArmPrincipalCoeffFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 2 x).symm.toContinuousLinearMap.comp
    ((combinedTrace42Model (E := E) (cometricLmodel (I := I) g₁ x)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmPrincipalCoeffFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciArmPrincipalCoeffFib (I := I) g₁ x D) =
      combinedTrace42Model (E := E) (cometricLmodel (I := I) g₁ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem ricciArmPrincipalCoeffFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (ricciArmPrincipalCoeffFib (I := I) g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => ricciArmPrincipalCoeffFib (I := I) g₁ x)
  intro Y
  
  let κ : Equiv.Perm (Fin 4) := koszulSlotPerm
  
  
  
  
  have hreindex : ∀ {d : ℕ} (ρ : Equiv.Perm (Fin d))
      (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
      (_hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr ρ
              (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
    intro d ρ Z hZ
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
            Tensor0SBundle.Tensor0SSpace d I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Z x)).mp hZ
    intro τ x₀
    refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr ρ
        (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  
  have hYκ := hreindex κ (fun x => Y x) Y.contMDiff
  
  have hT03field := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hYκ
  
  have hCDTfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) Y.contMDiff
  
  have hswapfield := hreindex (Equiv.swap (0 : Fin 2) 1)
    (fun x => (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        cometricDoubleTraceFib (I := I) g₁ 2 x)
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr κ (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))
    hT03field
  
  have hcomb := ((hT03field.add_section hswapfield).sub_section hCDTfield).const_smul_section
    (a := (1 / 2 : ℝ))
  refine hcomb.congr (fun x => ?_)
  
  have hfib : ricciArmPrincipalCoeffFib (I := I) g₁ x (Y x) =
      (1 / 2 : ℝ) •
        ((((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
                cometricDoubleTraceFib (I := I) g₁ 2 x)
              (Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr κ
                  (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))
            + Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
                  (Tensor0SBundle.Tensor0SSpace.toModel
                    ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ]
                          Tensor0SBundle.Tensor0SSpace 2 I x from
                        cometricDoubleTraceFib (I := I) g₁ 2 x)
                      (Tensor0SBundle.Tensor0SSpace.ofModel
                        (ContinuousMultilinearMap.domDomCongr κ
                          (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))))))
          - (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              cometricDoubleTraceFib (I := I) g₁ 2 x) (Y x)) := by
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    beta_reduce
    rw [ricciArmPrincipalCoeffFib_toModel]
    simp only [Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_sub,
      Tensor0SBundle.Tensor0SSpace.toModel_add, cometricDoubleTraceFib_toModel,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [combinedTrace42Model]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) hfib.symm

noncomputable def ricciArmPrincipalCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffFib (I := I) g₁ x)
      contMDiff_toFun := ricciArmPrincipalCoeffFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmPrincipalCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffFib (I := I) g₁ x) := rfl

set_option linter.unusedSectionVars false in

theorem ricciArmPrincipalCoeff_appCc_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁) W) x v =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4 W x
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![v 0, v 1, (Module.finBasis ℝ E) k])
            + unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 1, v 0, (Module.finBasis ℝ E) k])
            - unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  (Fin.cons ((Module.finBasis ℝ E) k) v))) := by
  
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmPrincipalCoeff_toSection, ricciArmPrincipalCoeffFib_toModel,
    combinedTrace42Model_apply (E := E) (cometricLmodel (I := I) g₁ x)]
  rfl

set_option linter.unusedSectionVars false in

noncomputable def ricciArmPrincipalCoeffPure (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ 2 }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmPrincipalCoeffPure_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) := rfl

set_option linter.unusedSectionVars false in

theorem ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmPrincipalCoeffPure_toSection, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  rfl

set_option linter.unusedSectionVars false in

theorem covDerivConnDiff_tracedPrincipal_eq_appCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![v 0, v 1, (Module.finBasis ℝ E) k])
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 1, v 0, (Module.finBasis ℝ E) k])
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  (Fin.cons ((Module.finBasis ℝ E) k) v))) :=
  ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) x v

private def triEvalFn (V : Π b : M, Tensor0SSpace 3 I b)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun b => Tensor0SSpace.toModel (V b) (Fin.cons (A b) (Fin.cons (B b) ![C b]))

set_option linter.unusedSectionVars false in

private lemma triMDiffAt_curried
    (s : ℕ) (W : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) s
      (fun y : M => Tensor0SNabla.curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SModel s ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => Tensor0SNabla.curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

set_option linter.unusedSectionVars false in

private theorem tensor0SCovariantDerivative03_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 3 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 3 V x)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)).toFun V x v)
        (Fin.cons (A x) (Fin.cons (B x) ![C x])) =
      directionalDeriv (I := I) (triEvalFn (I := I) (M := M) V A B C) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => A b) x v) (Fin.cons (B x) ![C x]))
        - Tensor0SSpace.toModel (V x)
            (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x]))
        - Tensor0SSpace.toModel (V x)
            (Fin.cons (A x) (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v])) := by
  classical
  set W₂ : Π b : M, Tensor0SSpace 2 I b :=
    fun b => Tensor0SNabla.curriedSection I M V b (A b) with hW₂
  have hW₂_mdiff : TensorSectionMDiffAt (I := I) 2 W₂ x :=
    triMDiffAt_curried (I := I) (M := M) 2 V hV A
  set W₁ : Π b : M, Tensor0SSpace 1 I b :=
    fun b => Tensor0SNabla.curriedSection I M W₂ b (B b) with hW₁
  have hW₁_mdiff : TensorSectionMDiffAt (I := I) 1 W₁ x :=
    triMDiffAt_curried (I := I) (M := M) 1 W₂ hW₂_mdiff B
  
  have hpeel1 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 2 V hV A v (Fin.cons (B x) ![C x])
  
  have hpeel2 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 1 W₂ hW₂_mdiff B v ![C x]
  
  have hpeel3 := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 W₁ hW₁_mdiff C v (fun i => Fin.elim0 i)
  
  have hbase : Tensor0SSpace.toModel
      ((Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)).toFun
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) x v)
      (fun i => Fin.elim0 i) =
      directionalDeriv (I := I) (triEvalFn (I := I) (M := M) V A B C) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) x v]
    have hscalar : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M W₁ b (C b)) =
        triEvalFn (I := I) (M := M) V A B C := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0)
            (T := W₁)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := W₁ b) (v0 := C b) (vs := (fun i => Fin.elim0 i))]
      change Tensor0SSpace.toModel (W₁ b) (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
      rw [hW₁]
      change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₂ b (B b))
        (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
      rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := W₂ b) (v0 := B b) (vs := Fin.cons (C b) (fun i => Fin.elim0 i))]
      rw [hW₂]
      change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V b (A b))
        (Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i))) = _
      rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := V b) (v0 := A b) (vs := Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i)))]
      rw [triEvalFn]
      apply congrArg
      funext k
      fin_cases k <;> rfl
    rw [hscalar]
  
  have hcorrC : Tensor0SSpace.toModel (W₁ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel (V x)
        (Fin.cons (A x) (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v])) := by
    rw [hW₁]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₂ x (B x))
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₂ x) (v0 := B x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v) (fun i => Fin.elim0 i))]
    rw [hW₂]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V x (A x))
      (Fin.cons (B x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := A x)
      (vs := Fin.cons (B x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v)
        (fun i => Fin.elim0 i)))]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  
  have hcorrB : Tensor0SSpace.toModel (W₂ x)
        (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
          (Fin.cons (C x) (fun i => Fin.elim0 i))) =
      Tensor0SSpace.toModel (V x)
        (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x])) := by
    rw [hW₂]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V x (A x))
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
        (Fin.cons (C x) (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V x) (v0 := A x)
      (vs := Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v)
        (Fin.cons (C x) (fun i => Fin.elim0 i)))]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  
  rw [hpeel1]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M V y (A y)) = W₂ from rfl]
  rw [hpeel2]
  rw [show (fun y : M => Tensor0SNabla.curriedSection I M W₂ y (B y)) = W₁ from rfl]
  rw [show (![C x] : Fin 1 → E) = Fin.cons (C x) (fun i => Fin.elim0 i) from by
    funext k; refine Fin.cases rfl (fun j => j.elim0) k]
  rw [hpeel3, hbase, hcorrC, hcorrB]
  have hfin1 : ∀ (u : TangentSpace I x), (![u] : Fin 1 → TangentSpace I x) =
      Fin.cons u (fun i => Fin.elim0 i) := by
    intro u; funext k; refine Fin.cases rfl (fun j => j.elim0) k
  rw [hfin1 ((LeviCivita (I := I) g₀).toFun (fun b => C b) x v),
      hfin1 (C x)]
  ring

set_option linter.unusedSectionVars false in

private def covGrad2UnitV (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) :
    Π b : M, Tensor0SSpace 3 I b :=
  unitEvalSection (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S)

set_option linter.unusedSectionVars false in

private lemma covGradEval_eq_triEvalFn (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) =
      triEvalFn (I := I) (M := M) (covGrad2UnitV (I := I) (M := M) g₀ S) A B C := rfl

set_option linter.unusedSectionVars false in

private lemma covGrad2UnitV_mdiff (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M) :
    TensorSectionMDiffAt (I := I) 3 (covGrad2UnitV (I := I) (M := M) g₀ S) x := by
  have h := contMDiff_unitEvalSection (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S)
  exact (h x).mdifferentiableAt (by simp)

set_option linter.unusedSectionVars false in

private lemma covGrad2UnitV_nabla3_eq_iteratedCovGrad
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (x : M) (v : TangentSpace I x) (m : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)).toFun
          (covGrad2UnitV (I := I) (M := M) g₀ S) x v) m =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x (Fin.cons v m) := by
  classical
  have hiter : iteratedCovGrad (I := I) g₀ 0 2 2 S =
      covGrad (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 S) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_zero]
  have hunit : unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x := rfl
  rw [unitModel, hunit, hiter,
    covGrad_apply_unit_eval_genVal (I := I) (M := M) g₀ 3
      (covGrad (I := I) (M := M) g₀ 0 2 S) x (Fin.cons v m)]
  have hvt : Matrix.vecTail (Fin.cons v m) = m := by
    funext k; simp only [Matrix.vecTail, Function.comp]; rw [Fin.cons_succ]
  have h0 : (Fin.cons v m : Fin 4 → TangentSpace I x) 0 = v := rfl
  rw [h0, hvt, tensorCovDerivAt_def (I := I) (M := M) g₀ 0 3
      (covGrad (I := I) (M := M) g₀ 0 2 S) x v,
    covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ 3
      (covGrad (I := I) (M := M) g₀ 0 2 S).toSection x v]
  rfl

set_option linter.unusedSectionVars false in

private lemma covGradEval_directionalDeriv
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    directionalDeriv (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) x v =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
          (Fin.cons v (Fin.cons (A x) (Fin.cons (B x) ![C x])))
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(LeviCivita (I := I) g₀).toFun (fun b => A b) x v, B x, C x]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![A x, (LeviCivita (I := I) g₀).toFun (fun b => B b) x v, C x]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![A x, B x, (LeviCivita (I := I) g₀).toFun (fun b => C b) x v] := by
  classical
  have hpeel := tensor0SCovariantDerivative03_consEval_leibnizDefect (I := I) (M := M) g₀
    (covGrad2UnitV (I := I) (M := M) g₀ S) (covGrad2UnitV_mdiff (I := I) (M := M) g₀ S x) A B C v
  have hprin := covGrad2UnitV_nabla3_eq_iteratedCovGrad (I := I) (M := M) g₀ S x v
    (Fin.cons (A x) (Fin.cons (B x) ![C x]))
  rw [covGradEval_eq_triEvalFn (I := I) (M := M) g₀ S A B C]
  rw [show directionalDeriv (I := I) (triEvalFn (I := I) (M := M)
        (covGrad2UnitV (I := I) (M := M) g₀ S) A B C) x v =
      Tensor0SSpace.toModel
        ((Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g₀)).toFun
          (covGrad2UnitV (I := I) (M := M) g₀ S) x v)
        (Fin.cons (A x) (Fin.cons (B x) ![C x]))
        + Tensor0SSpace.toModel (covGrad2UnitV (I := I) (M := M) g₀ S x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => A b) x v) (Fin.cons (B x) ![C x]))
        + Tensor0SSpace.toModel (covGrad2UnitV (I := I) (M := M) g₀ S x)
            (Fin.cons (A x) (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => B b) x v) ![C x]))
        + Tensor0SSpace.toModel (covGrad2UnitV (I := I) (M := M) g₀ S x)
            (Fin.cons (A x) (Fin.cons (B x) ![(LeviCivita (I := I) g₀).toFun (fun b => C b) x v]))
      from by rw [hpeel]; ring]
  rw [hprin]
  rfl

set_option linter.unusedSectionVars false in

private lemma covGradEval_mdifferentiableAt
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (A B C : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) x := by
  classical
  have h3 := covGrad2UnitV_mdiff (I := I) (M := M) g₀ S x
  have h2 := triMDiffAt_curried (I := I) (M := M) 2 (covGrad2UnitV (I := I) (M := M) g₀ S) h3 A
  have h1 := triMDiffAt_curried (I := I) (M := M) 1
    (fun y : M => Tensor0SNabla.curriedSection I M (covGrad2UnitV (I := I) (M := M) g₀ S) y (A y))
    h2 B
  have h0 := triMDiffAt_curried (I := I) (M := M) 0
    (fun y : M => Tensor0SNabla.curriedSection I M
      (fun z : M => Tensor0SNabla.curriedSection I M (covGrad2UnitV (I := I) (M := M) g₀ S) z (A z))
      y (B y)) h1 C
  have hscalar := (Tensor0SNabla.mdifferentiableAt_scalarFn_iff_section (I := I) (M := M)
    (fun y : M => Tensor0SNabla.curriedSection I M
      (fun z : M => Tensor0SNabla.curriedSection I M
        (fun w : M => Tensor0SNabla.curriedSection I M
          (covGrad2UnitV (I := I) (M := M) g₀ S) w (A w)) z (B z)) y (C y)) (x := x)).mpr h0
  have hfun : Tensor0SNabla.scalarFn I M
      (fun y : M => Tensor0SNabla.curriedSection I M
        (fun z : M => Tensor0SNabla.curriedSection I M
          (fun w : M => Tensor0SNabla.curriedSection I M
            (covGrad2UnitV (I := I) (M := M) g₀ S) w (A w)) z (B z)) y (C y)) =
      (fun b : M => covGradEval (I := I) (M := M) g₀ S A B C b) := by
    funext b
    set V₃ : Π y : M, Tensor0SSpace 3 I y := covGrad2UnitV (I := I) (M := M) g₀ S with hV₃
    set W₂ : Π y : M, Tensor0SSpace 2 I y :=
      fun z : M => Tensor0SNabla.curriedSection I M V₃ z (A z) with hW₂
    set W₁ : Π y : M, Tensor0SSpace 1 I y :=
      fun z : M => Tensor0SNabla.curriedSection I M W₂ z (B z) with hW₁
    rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
    rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := W₁)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₁ b) (v0 := C b) (vs := (fun i => Fin.elim0 i))]
    rw [hW₁]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M W₂ b (B b))
      (Fin.cons (C b) (fun i => Fin.elim0 i)) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 1) (T := W₂)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := W₂ b) (v0 := B b) (vs := Fin.cons (C b) (fun i => Fin.elim0 i))]
    rw [hW₂]
    change Tensor0SSpace.toModel (Tensor0SNabla.curriedSection I M V₃ b (A b))
      (Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i))) = _
    rw [Tensor0SNabla.curriedSection_apply (s := 2) (T := V₃)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := V₃ b) (v0 := A b) (vs := Fin.cons (B b) (Fin.cons (C b) (fun i => Fin.elim0 i)))]
    rw [hV₃, covGradEval, covGrad2UnitV, unitEvalSection]
    apply congrArg
    funext k
    fin_cases k <;> rfl
  rw [hfun] at hscalar
  exact hscalar

set_option linter.unusedSectionVars false in

theorem koszulCovGradCovec_covDeriv_eq_secondCovGrad
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    cotangentToDual (I := I)
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x))) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![X x, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![X x, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![X x, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x), Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x), ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x), Z x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x), ζ]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x (X x), Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x (X x)]) := by
  classical
  rw [cotangentToDual_apply, dualToCotangent_apply]
  
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ g₁ Z Y x
  
  let ζf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩
  let Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩
  have hζfx : ζf x = ζ := smoothExtensionTangent_eq (I := I) x ζ
  have hXfx : Xf x = X x := smoothExtensionTangent_eq (I := I) x (X x)
  have hXfmd := smoothExtensionTangent_mdiff (I := I) x (X x) x
  have hζfmd := smoothExtensionTangent_mdiff (I := I) x ζ x
  
  have hcov : ((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (X x)) ζ =
      cotangentScalar ((LeviCivita (I := I) g₀).toFun)
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (fun b => Xf b) (fun b => ζf b) := by
    rw [cotangentCov_toFun, cotangentCovFun_apply, ← hXfx, ← hζfx]
    exact cotangentCovAt_apply_of_diff (LeviCivita (I := I) g₀) hθ hXfmd hζfmd
  rw [ContinuousLinearMap.coe_coe, hcov, cotangentScalar_def]
  
  have hpairfun : (fun b : M => (cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) =
      (fun b : M => (1 / 2 : ℝ) *
        (covGradEval (I := I) (M := M) g₀ S Z Y ζf b
          + covGradEval (I := I) (M := M) g₀ S Y Z ζf b
          - covGradEval (I := I) (M := M) g₀ S ζf Z Y b)) := by
    funext b
    have h := koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁ S hbil Z Y ζf b
    rw [show (cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b) =
        cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b) (ζf b) from rfl]
    rw [h]
  
  have hext : extDerivFun (I := I)
        (fun b : M => (cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) x (Xf x) =
      (1 / 2 : ℝ) *
        (directionalDeriv (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S Z Y ζf b) x (Xf x)
          + directionalDeriv (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S Y Z ζf b) x (Xf x)
          - directionalDeriv (I := I) (fun b : M => covGradEval (I := I) (M := M) g₀ S ζf Z Y b) x (Xf x)) := by
    have hf := covGradEval_mdifferentiableAt (I := I) (M := M) g₀ S Z Y ζf x
    have hg := covGradEval_mdifferentiableAt (I := I) (M := M) g₀ S Y Z ζf x
    have hh := covGradEval_mdifferentiableAt (I := I) (M := M) g₀ S ζf Z Y x
    
    have hmf0 := (((hf.hasMFDerivAt.add hg.hasMFDerivAt).sub hh.hasMFDerivAt).const_smul
      (1 / 2 : ℝ))
    have heq : (fun b : M => (cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) =ᶠ[nhds x]
        ((1 / 2 : ℝ) • (fun b : M =>
          covGradEval (I := I) (M := M) g₀ S Z Y ζf b
            + covGradEval (I := I) (M := M) g₀ S Y Z ζf b
            - covGradEval (I := I) (M := M) g₀ S ζf Z Y b)) := by
      filter_upwards [Filter.univ_mem] with b _
      rw [Pi.smul_apply, smul_eq_mul]
      exact congrFun hpairfun b
    have hmf := hmf0.congr_of_eventuallyEq heq
    change mfderiv I 𝓘(ℝ, ℝ)
        (fun b : M => (cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) (ζf b)) x (Xf x) = _
    rw [hmf.mfderiv]
    rfl
  rw [hext, hXfx]
  
  have hθext : (cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x))
        ((LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x)) =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![Z x, Y x, (LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x)]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![Y x, Z x, (LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x)]
          - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x), Z x, Y x]) := by
    set w : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun b => ζf b) x (X x) with hw
    
    let wf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x w, smoothExtensionTangent_contMDiff (I := I) x w⟩
    have hwfx : wf x = w := smoothExtensionTangent_eq (I := I) x w
    have h := koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁ S hbil Z Y wf x
    rw [show (cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)) w =
        cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x) (wf x) from by
      rw [hwfx]; rfl]
    rw [h]
    
    have hcg : ∀ (A B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
        covGradEval (I := I) (M := M) g₀ S A B wf x =
          unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x ![A x, B x, w] := by
      intro A B
      rw [covGradEval, unitModel, hwfx]; rfl
    have hcg2 : covGradEval (I := I) (M := M) g₀ S wf Z Y x =
        unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x ![w, Z x, Y x] := by
      rw [covGradEval, unitModel, hwfx]; rfl
    rw [hcg Z Y, hcg Y Z, hcg2]
  rw [hθext]
  
  rw [covGradEval_directionalDeriv (I := I) (M := M) g₀ S Z Y ζf x (X x),
      covGradEval_directionalDeriv (I := I) (M := M) g₀ S Y Z ζf x (X x),
      covGradEval_directionalDeriv (I := I) (M := M) g₀ S ζf Z Y x (X x)]
  rw [hζfx]
  
  have ht1 : (Fin.cons (X x) (Fin.cons (Z x) (Fin.cons (Y x) ![ζ])) : Fin 4 → TangentSpace I x) =
      ![X x, Z x, Y x, ζ] := by funext k; fin_cases k <;> rfl
  have ht2 : (Fin.cons (X x) (Fin.cons (Y x) (Fin.cons (Z x) ![ζ])) : Fin 4 → TangentSpace I x) =
      ![X x, Y x, Z x, ζ] := by funext k; fin_cases k <;> rfl
  have ht3 : (Fin.cons (X x) (Fin.cons ζ (Fin.cons (Z x) ![Y x])) : Fin 4 → TangentSpace I x) =
      ![X x, ζ, Z x, Y x] := by funext k; fin_cases k <;> rfl
  rw [ht1, ht2, ht3]
  ring

set_option linter.unusedSectionVars false in
private theorem traceViaBasis_c (G : E →ₗ[ℝ] E) :
    ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr (G ((chartModelBasis E) i)) i =
      LinearMap.trace ℝ E G := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (chartModelBasis E), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]

set_option linter.unusedSectionVars false in
private theorem cometric_finBasis_biorth_c (g₁ : SmoothRiemannianMetric I M) (x : M)
    (j k : Fin (Module.finrank ℝ E)) :
    g₁.inner x
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        ((Module.finBasis ℝ E) j) =
      if j = k then 1 else 0 := by
  classical
  have h1 : cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₁ x
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₁ x _ ((Module.finBasis ℝ E) j),
    cotangentToDualLinear_apply, cotangentToDual_apply]
  have h2 : (((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (fun _ : Fin 1 => (Module.finBasis ℝ E) j) : ℝ) =
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k) (fun _ : Fin 1 => ((Module.finBasis ℝ E) j : E)) := rfl
  rw [h2, Tensor0SBundle.model_covectorOfCLM_apply]
  rw [show ((Module.finBasis ℝ E).cDualBasis k) =
      LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
  rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, Module.Basis.repr_self]
  rw [Finsupp.single_apply]

private theorem traceViaCometric_c (g₁ : SmoothRiemannianMetric I M) (x : M) (G : E →ₗ[ℝ] E) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x
          (G (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k) =
      LinearMap.trace ℝ E G := by
  classical
  set d : Fin (Module.finrank ℝ E) → E := fun k =>
    cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)) with hd
  set ε : Fin (Module.finrank ℝ E) → Module.Dual ℝ E := fun k =>
    ((g₁.inner x).flip ((Module.finBasis ℝ E) k)).toLinearMap with hε
  have hev_same : ∀ k, ε k (d k) = 1 := by
    intro k
    rw [hε, hd]
    change g₁.inner x (d k) ((Module.finBasis ℝ E) k) = 1
    rw [hd, cometric_finBasis_biorth_c (I := I) g₁ x k k, if_pos rfl]
  have hev_ne : Pairwise fun i j => ε i (d j) = 0 := by
    intro i j hij
    rw [hε, hd]
    change g₁.inner x (d j) ((Module.finBasis ℝ E) i) = 0
    rw [hd, cometric_finBasis_biorth_c (I := I) g₁ x i j, if_neg hij]
  have htot : ∀ {m₁ m₂ : E}, (∀ k, ε k m₁ = ε k m₂) → m₁ = m₂ := by
    intro m₁ m₂ hm
    apply SmoothRiemannianMetric.eq_of_inner_eq g₁ (x := x)
    intro ζ
    have hζ : ζ = ∑ k : Fin (Module.finrank ℝ E), (Module.finBasis ℝ E).repr ζ k • (Module.finBasis ℝ E) k :=
      ((Module.finBasis ℝ E).sum_repr ζ).symm
    rw [hζ]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hm k
    change (Module.finBasis ℝ E).repr ζ k * g₁.inner x m₁ ((Module.finBasis ℝ E) k) =
      (Module.finBasis ℝ E).repr ζ k * g₁.inner x m₂ ((Module.finBasis ℝ E) k)
    rw [g₁.symm x m₁, g₁.symm x m₂]
    have hk' : g₁.inner x m₁ ((Module.finBasis ℝ E) k) = g₁.inner x m₂ ((Module.finBasis ℝ E) k) := by
      have e1 : ε k m₁ = g₁.inner x m₁ ((Module.finBasis ℝ E) k) := by rw [hε]; rfl
      have e2 : ε k m₂ = g₁.inner x m₂ ((Module.finBasis ℝ E) k) := by rw [hε]; rfl
      rw [← e1, ← e2, hk]
    rw [g₁.symm x ((Module.finBasis ℝ E) k) m₁, g₁.symm x ((Module.finBasis ℝ E) k) m₂, hk']
  have hdual : Module.DualBases d ε :=
    { eval_same := hev_same, eval_of_ne := hev_ne, total := htot }
  rw [LinearMap.trace_eq_matrix_trace ℝ hdual.basis, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [Module.DualBases.coe_basis]
  have hrepr : hdual.basis.repr (G (d k)) k = ε k (G (d k)) := by
    rw [Module.DualBases.basis_repr_apply, Module.DualBases.coeffs_apply]
  rw [hrepr, hε]
  rfl

set_option linter.unusedSectionVars false in
private lemma dualToCotangent_addC {x : M} (α β : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (α + β)
      = dualToCotangent (I := I) (x := x) α + dualToCotangent (I := I) (x := x) β := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_add, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDualLinear_apply, cotangentToDual_dualToCotangent,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

set_option linter.unusedSectionVars false in
private lemma dualToCotangent_smulC {x : M} (c : ℝ) (α : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (c • α)
      = c • dualToCotangent (I := I) (x := x) α := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_smul, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

set_option linter.unusedSectionVars false in
private lemma dualToCotangent_subC {x : M} (α β : Module.Dual ℝ (TangentSpace I x)) :
    dualToCotangent (I := I) (x := x) (α - β)
      = dualToCotangent (I := I) (x := x) α - dualToCotangent (I := I) (x := x) β := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [map_sub, cotangentToDualLinear_apply, cotangentToDualLinear_apply,
    cotangentToDualLinear_apply, cotangentToDual_dualToCotangent,
    cotangentToDual_dualToCotangent, cotangentToDual_dualToCotangent]

private def alignedPrincipalEndoC (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : E →ₗ[ℝ] E where
  toFun := fun v => inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
  map_add' := fun v v' => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (v + v') :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) +
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v' :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_add]]
    rw [dualToCotangent_addC]
    rw [map_add]
  map_smul' := fun c v => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x (c • v) :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      c • (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_smul]]
    rw [dualToCotangent_smulC]
    rw [map_smul]; rfl

private def g1PrincipalVecC (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) g₁)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))

private def alignCorrVecC (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      (-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v +
                PDE.DeTurck.connDiff (I := I) g₁ g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ)))

@[simp] private lemma alignedPrincipalEndoC_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x v =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))) := rfl

private lemma g1Principal_splitC
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    g1PrincipalVecC (I := I) (M := M) g₀ g₁ Z Y x v =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
        + alignCorrVecC (I := I) (M := M) g₀ g₁ Z Y x v := by
  classical
  rw [g1PrincipalVecC, alignCorrVecC]
  rw [← map_add]
  congr 1
  rw [← dualToCotangent_addC]
  congr 1
  ext w
  rw [LinearMap.add_apply]
  set Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩ with hXfdef
  have hXfx : Xf x = v := smoothExtensionTangent_eq (I := I) x v
  have halign := covDerivConnDiff_principal_align (I := I) (M := M) g₀ g₁ Xf Y Z x w
  rw [hXfx] at halign
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, halign]
  rw [show ((-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v +
                PDE.DeTurck.connDiff (I := I) g₁ g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) w) =
      -(cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y x)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v)) from rfl]
  ring

private lemma alignedPrincipalEndoC_inner_secondKoszul
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v ζ : TangentSpace I x) :
    g₁.inner x (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x v) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![v, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![v, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![v, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, Z x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, ζ]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![ζ, Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v]) := by
  classical
  let Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩
  have hXfx : Xf x = v := smoothExtensionTangent_eq (I := I) x v
  rw [alignedPrincipalEndoC_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x _ ζ, cotangentToDualLinear_apply]
  rw [← hXfx]
  have hbridge := koszulCovGradCovec_covDeriv_eq_secondCovGrad (I := I) (M := M) g₀ g₁ S hbil Xf Y Z x ζ
  rw [hXfx]
  rw [hXfx] at hbridge
  rw [hbridge]

def secondKoszulFrameRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ k : Fin (Module.finrank ℝ E),
      (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
          ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x
              (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))), Y x, (Module.finBasis ℝ E) k]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), Z x, (Module.finBasis ℝ E) k]
        + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
        - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(Module.finBasis ℝ E) k, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))), Y x]
        - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(Module.finBasis ℝ E) k, Z x,
              (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))])

private lemma alignedPrincipalEndoC_trace_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    LinearMap.trace ℝ E (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![Z x, Y x]
        + secondKoszulFrameRemainder (I := I) (M := M) g₀ g₁ S Z Y x := by
  classical
  rw [← traceViaCometric_c (I := I) (M := M) g₁ x (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x)]
  rw [covDerivConnDiff_tracedPrincipal_eq_appCc (I := I) (M := M) g₀ g₁ S x ![Z x, Y x]]
  rw [secondKoszulFrameRemainder]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        g₁.inner x
          (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x
            (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), Z x, Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), Y x, Z x, (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
                ![cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                  (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k))), Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Z x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(Module.finBasis ℝ E) k, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
                ![(Module.finBasis ℝ E) k, Z x,
                  (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))])) from by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact alignedPrincipalEndoC_inner_secondKoszul (I := I) (M := M) g₀ g₁ S hbil Z Y x
        (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1

def alignmentTraceRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignCorrVecC (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)) i

def palatiniTracedPrincipalRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  secondKoszulFrameRemainder (I := I) (M := M) g₀ g₁ S Z Y x
    + alignmentTraceRemainder (I := I) (M := M) g₀ g₁ Z Y x

theorem palatini_tracedPrincipal_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![Z x, Y x]
        + palatiniTracedPrincipalRemainder (I := I) (M := M) g₀ g₁ S Z Y x := by
  classical
  
  have hsumeq : (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
            (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignCorrVecC (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsplit := g1Principal_splitC (I := I) (M := M) g₀ g₁ Z Y x ((chartModelBasis E) i)
    rw [g1PrincipalVecC] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply]
    rw [← alignedPrincipalEndoC_apply]
  rw [hsumeq, Finset.sum_add_distrib]
  rw [traceViaBasis_c (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ Z Y x)]
  rw [alignedPrincipalEndoC_trace_eq (I := I) (M := M) g₀ g₁ S hbil Z Y x]
  rw [palatiniTracedPrincipalRemainder, alignmentTraceRemainder]
  ring

def zSlotPerm1 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2).trans ((Equiv.swap (0 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1))

def zSlotPerm2 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (1 : Fin 4) 3)

def zSlotPerm3 : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2

set_option linter.unusedSectionVars false in

private theorem zSlotPerm_apply :
    (zSlotPerm1 0 = 2 ∧ zSlotPerm1 1 = 0 ∧ zSlotPerm1 2 = 3 ∧ zSlotPerm1 3 = 1) ∧
    (zSlotPerm2 0 = 2 ∧ zSlotPerm2 1 = 3 ∧ zSlotPerm2 2 = 0 ∧ zSlotPerm2 3 = 1) ∧
    (zSlotPerm3 0 = 2 ∧ zSlotPerm3 1 = 1 ∧ zSlotPerm3 2 = 0 ∧ zSlotPerm3 3 = 3) := by
  unfold zSlotPerm1 zSlotPerm2 zSlotPerm3
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> decide

noncomputable def combinedTrace42ModelZ
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E) :
    Tensor0SBundle.Tensor0SModel 4 ℝ E →L[ℝ] Tensor0SBundle.Tensor0SModel 2 ℝ E :=
  (1 / 2 : ℝ) •
    ((modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            zSlotPerm1).toContinuousLinearEquiv.toContinuousLinearMap)
      + (modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            zSlotPerm2).toContinuousLinearEquiv.toContinuousLinearMap)
      - (modelDoubleTrace (E := E) 2 L).comp
          ((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            zSlotPerm3).toContinuousLinearEquiv.toContinuousLinearMap))

set_option linter.unusedSectionVars false in

theorem combinedTrace42ModelZ_apply
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    combinedTrace42ModelZ (E := E) L D m =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (D ![m 0, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)), m 1, (Module.finBasis ℝ E) k]
            + D ![m 0, m 1, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
            - D ![m 0, (Module.finBasis ℝ E) k, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), m 1]) := by
  classical
  have hcongr_eq : ∀ (σ : Equiv.Perm (Fin 4)) (D' : Tensor0SBundle.Tensor0SModel 4 ℝ E),
      (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          σ).toContinuousLinearEquiv.toContinuousLinearMap D' =
        ContinuousMultilinearMap.domDomCongr σ D' := by
    intro σ D'
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  
  have htrace : ∀ (σ : Equiv.Perm (Fin 4)) (tup : Fin (Module.finrank ℝ E) → Fin 4 → E)
      (_htup : ∀ k, (fun j =>
        (![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, m 0, m 1] :
          Fin 4 → E) (σ j)) = tup k),
      modelDoubleTrace (E := E) 2 L
          (ContinuousMultilinearMap.domDomCongr σ D) m =
        ∑ k : Fin (Module.finrank ℝ E), D (tup k) := by
    intro σ tup htup
    rw [modelDoubleTrace_apply (E := E) 2 L _ m]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (Fin.cons (L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) m) : Fin 4 → E) =
        ![L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, m 0, m 1] from by
      funext j; fin_cases j <;> rfl]
    rw [← htup k]
  rw [combinedTrace42ModelZ]
  rw [ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousMultilinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hcongr_eq, hcongr_eq, hcongr_eq]
  rw [htrace zSlotPerm1 (fun k => ![m 0, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)), m 1, (Module.finBasis ℝ E) k]) (by
        intro k
        funext j
        fin_cases j <;>
          simp only [zSlotPerm1, Fin.isValue, Equiv.trans_apply, Equiv.swap_apply_def] <;> rfl)]
  rw [htrace zSlotPerm2 (fun k => ![m 0, m 1, L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]) (by
        intro k
        funext j
        fin_cases j <;>
          simp only [zSlotPerm2, Fin.isValue, Equiv.trans_apply, Equiv.swap_apply_def] <;> rfl)]
  rw [htrace zSlotPerm3 (fun k => ![m 0, (Module.finBasis ℝ E) k,
        L (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)), m 1]) (by
        intro k
        funext j
        fin_cases j <;>
          simp only [zSlotPerm3, Fin.isValue, Equiv.swap_apply_def] <;> rfl)]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

noncomputable def ricciArmPrincipalCoeffZFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 2 x).symm.toContinuousLinearMap.comp
    ((combinedTrace42ModelZ (E := E) (cometricLmodel (I := I) g₁ x)).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmPrincipalCoeffZFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciArmPrincipalCoeffZFib (I := I) g₁ x D) =
      combinedTrace42ModelZ (E := E) (cometricLmodel (I := I) g₁ x)
        (Tensor0SBundle.Tensor0SSpace.toModel D) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem ricciArmPrincipalCoeffZFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (ricciArmPrincipalCoeffZFib (I := I) g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => ricciArmPrincipalCoeffZFib (I := I) g₁ x)
  intro Y
  
  have hreindex : ∀ (ρ : Equiv.Perm (Fin 4))
      (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace 4 I x)
      (_hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x (Z x))),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr ρ
              (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
    intro ρ Z hZ
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))) :
            Tensor0SBundle.Tensor0SSpace 4 I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Z x)).mp hZ
    intro τ x₀
    refine (hZcoord (τ ∘ ρ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr ρ
        (Tensor0SBundle.Tensor0SSpace.toModel (Z x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  
  have hcdt : ∀ (ρ : Equiv.Perm (Fin 4)),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
          ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              cometricDoubleTraceFib (I := I) g₁ 2 x)
            (Tensor0SBundle.Tensor0SSpace.ofModel
              (ContinuousMultilinearMap.domDomCongr ρ
                (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))) := by
    intro ρ
    exact ContMDiff.clm_bundle_apply (b := id)
      (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) (hreindex ρ (fun x => Y x) Y.contMDiff)
  
  have hcomb := (((hcdt zSlotPerm1).add_section (hcdt zSlotPerm2)).sub_section
    (hcdt zSlotPerm3)).const_smul_section (a := (1 / 2 : ℝ))
  refine hcomb.congr (fun x => ?_)
  have hfib : ricciArmPrincipalCoeffZFib (I := I) g₁ x (Y x) =
      (1 / 2 : ℝ) •
        (((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
                cometricDoubleTraceFib (I := I) g₁ 2 x)
              (Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr zSlotPerm1
                  (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))
            + (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
                cometricDoubleTraceFib (I := I) g₁ 2 x)
                (Tensor0SBundle.Tensor0SSpace.ofModel
                  (ContinuousMultilinearMap.domDomCongr zSlotPerm2
                    (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))))
          - (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              cometricDoubleTraceFib (I := I) g₁ 2 x)
              (Tensor0SBundle.Tensor0SSpace.ofModel
                (ContinuousMultilinearMap.domDomCongr zSlotPerm3
                  (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    beta_reduce
    rw [ricciArmPrincipalCoeffZFib_toModel]
    simp only [Tensor0SBundle.Tensor0SSpace.toModel_smul, Tensor0SBundle.Tensor0SSpace.toModel_sub,
      Tensor0SBundle.Tensor0SSpace.toModel_add, cometricDoubleTraceFib_toModel,
      Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    rw [combinedTrace42ModelZ]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) hfib.symm

noncomputable def ricciArmPrincipalCoeffZ (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffZFib (I := I) g₁ x)
      contMDiff_toFun := ricciArmPrincipalCoeffZFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmPrincipalCoeffZ_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from ricciArmPrincipalCoeffZFib (I := I) g₁ x) := rfl

set_option linter.unusedSectionVars false in

theorem ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁) W) x v =
      (1 / 2 : ℝ) *
        ∑ k : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4 W x
              ![v 0, cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 4 W x
                ![v 0, v 1, cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 4 W x
                ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), v 1]) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmPrincipalCoeffZ_toSection, ricciArmPrincipalCoeffZFib_toModel,
    combinedTrace42ModelZ_apply (E := E) (cometricLmodel (I := I) g₁ x)]
  rfl

private def zPrincipalCovec (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e : TangentSpace I x) :
    TangentSpace I x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ζ => (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x])
      map_add' := by
        intro ζ ζ'
        have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, e, W x, ζ + ζ'] =
            unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ'] := by
          rw [show (![V x, e, W x, ζ + ζ'] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, e, W x, ζ] 3 (ζ + ζ') from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
            show (Function.update ![V x, e, W x, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
              funext j; fin_cases j <;> rfl,
            show (Function.update ![V x, e, W x, ζ] 3 ζ' : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ'] from by
              funext j; fin_cases j <;> rfl]
        have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, W x, e, ζ + ζ'] =
            unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ'] := by
          rw [show (![V x, W x, e, ζ + ζ'] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, W x, e, ζ] 3 (ζ + ζ') from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
            show (Function.update ![V x, W x, e, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
              funext j; fin_cases j <;> rfl,
            show (Function.update ![V x, W x, e, ζ] 3 ζ' : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ'] from by
              funext j; fin_cases j <;> rfl]
        have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, ζ + ζ', e, W x] =
            unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]
              + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ', e, W x] := by
          rw [show (![V x, ζ + ζ', e, W x] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, ζ, e, W x] 1 (ζ + ζ') from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
            show (Function.update ![V x, ζ, e, W x] 1 ζ : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
              funext j; fin_cases j <;> rfl,
            show (Function.update ![V x, ζ, e, W x] 1 ζ' : Fin 4 → TangentSpace I x) = ![V x, ζ', e, W x] from by
              funext j; fin_cases j <;> rfl]
        rw [h1, h2, h3]; ring
      map_smul' := by
        intro c ζ
        have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, e, W x, c • ζ] =
            c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ] := by
          rw [show (![V x, e, W x, c • ζ] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, e, W x, ζ] 3 (c • ζ) from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
            show (Function.update ![V x, e, W x, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
              funext j; fin_cases j <;> rfl]
        have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, W x, e, c • ζ] =
            c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ] := by
          rw [show (![V x, W x, e, c • ζ] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, W x, e, ζ] 3 (c • ζ) from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
            show (Function.update ![V x, W x, e, ζ] 3 ζ : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
              funext j; fin_cases j <;> rfl]
        have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
              ![V x, c • ζ, e, W x] =
            c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x] := by
          rw [show (![V x, c • ζ, e, W x] : Fin 4 → TangentSpace I x) =
              Function.update ![V x, ζ, e, W x] 1 (c • ζ) from by funext j; fin_cases j <;> rfl,
            (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
            show (Function.update ![V x, ζ, e, W x] 1 ζ : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
              funext j; fin_cases j <;> rfl]
        rw [h1, h2, h3]
        simp only [smul_eq_mul, RingHom.id_apply]
        ring }

set_option linter.unusedSectionVars false in

private lemma zPrincipalCovec_apply (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e ζ : TangentSpace I x) :
    zPrincipalCovec (I := I) (M := M) g₀ S V W x e ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]) := rfl

set_option linter.unusedSectionVars false in

private lemma zPrincipalCovec_add (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e e' : TangentSpace I x) :
    zPrincipalCovec (I := I) (M := M) g₀ S V W x (e + e') =
      zPrincipalCovec (I := I) (M := M) g₀ S V W x e
        + zPrincipalCovec (I := I) (M := M) g₀ S V W x e' := by
  ext ζ
  rw [ContinuousLinearMap.add_apply, zPrincipalCovec_apply, zPrincipalCovec_apply,
    zPrincipalCovec_apply]
  have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, e + e', W x, ζ] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
        + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e', W x, ζ] := by
    rw [show (![V x, e + e', W x, ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, e, W x, ζ] 1 (e + e') from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
      show (Function.update ![V x, e, W x, ζ] 1 e : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
        funext j; fin_cases j <;> rfl,
      show (Function.update ![V x, e, W x, ζ] 1 e' : Fin 4 → TangentSpace I x) = ![V x, e', W x, ζ] from by
        funext j; fin_cases j <;> rfl]
  have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, W x, e + e', ζ] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
        + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e', ζ] := by
    rw [show (![V x, W x, e + e', ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, W x, e, ζ] 2 (e + e') from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
      show (Function.update ![V x, W x, e, ζ] 2 e : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
        funext j; fin_cases j <;> rfl,
      show (Function.update ![V x, W x, e, ζ] 2 e' : Fin 4 → TangentSpace I x) = ![V x, W x, e', ζ] from by
        funext j; fin_cases j <;> rfl]
  have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, ζ, e + e', W x] =
      unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]
        + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e', W x] := by
    rw [show (![V x, ζ, e + e', W x] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, ζ, e, W x] 2 (e + e') from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_add,
      show (Function.update ![V x, ζ, e, W x] 2 e : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
        funext j; fin_cases j <;> rfl,
      show (Function.update ![V x, ζ, e, W x] 2 e' : Fin 4 → TangentSpace I x) = ![V x, ζ, e', W x] from by
        funext j; fin_cases j <;> rfl]
  rw [h1, h2, h3]; ring

set_option linter.unusedSectionVars false in

private lemma zPrincipalCovec_smul (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (c : ℝ) (e : TangentSpace I x) :
    zPrincipalCovec (I := I) (M := M) g₀ S V W x (c • e) =
      c • zPrincipalCovec (I := I) (M := M) g₀ S V W x e := by
  ext ζ
  rw [ContinuousLinearMap.smul_apply, zPrincipalCovec_apply, zPrincipalCovec_apply]
  have h1 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, c • e, W x, ζ] =
      c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ] := by
    rw [show (![V x, c • e, W x, ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, e, W x, ζ] 1 (c • e) from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
      show (Function.update ![V x, e, W x, ζ] 1 e : Fin 4 → TangentSpace I x) = ![V x, e, W x, ζ] from by
        funext j; fin_cases j <;> rfl]
  have h2 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, W x, c • e, ζ] =
      c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ] := by
    rw [show (![V x, W x, c • e, ζ] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, W x, e, ζ] 2 (c • e) from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
      show (Function.update ![V x, W x, e, ζ] 2 e : Fin 4 → TangentSpace I x) = ![V x, W x, e, ζ] from by
        funext j; fin_cases j <;> rfl]
  have h3 : unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x
        ![V x, ζ, c • e, W x] =
      c • unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x] := by
    rw [show (![V x, ζ, c • e, W x] : Fin 4 → TangentSpace I x) =
        Function.update ![V x, ζ, e, W x] 2 (c • e) from by funext j; fin_cases j <;> rfl,
      (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x).map_update_smul,
      show (Function.update ![V x, ζ, e, W x] 2 e : Fin 4 → TangentSpace I x) = ![V x, ζ, e, W x] from by
        funext j; fin_cases j <;> rfl]
  rw [h1, h2, h3]
  simp only [smul_eq_mul]; ring

private def alignedPrincipalEndoCZ (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : E →ₗ[ℝ] E where
  toFun := fun e => inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      ((zPrincipalCovec (I := I) (M := M) g₀ S V W x e :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
  map_add' := fun e e' => by
    rw [show ((zPrincipalCovec (I := I) (M := M) g₀ S V W x (e + e') :
          TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
        ((zPrincipalCovec (I := I) (M := M) g₀ S V W x e :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) +
          ((zPrincipalCovec (I := I) (M := M) g₀ S V W x e' :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w
      rw [LinearMap.add_apply]
      change zPrincipalCovec (I := I) (M := M) g₀ S V W x (e + e') w =
        zPrincipalCovec (I := I) (M := M) g₀ S V W x e w
          + zPrincipalCovec (I := I) (M := M) g₀ S V W x e' w
      rw [zPrincipalCovec_add]; rfl]
    rw [dualToCotangent_addC, map_add]
  map_smul' := fun c e => by
    rw [show ((zPrincipalCovec (I := I) (M := M) g₀ S V W x (c • e) :
          TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
        c • ((zPrincipalCovec (I := I) (M := M) g₀ S V W x e :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w
      rw [LinearMap.smul_apply]
      change zPrincipalCovec (I := I) (M := M) g₀ S V W x (c • e) w =
        c • zPrincipalCovec (I := I) (M := M) g₀ S V W x e w
      rw [zPrincipalCovec_smul]; rfl]
    rw [dualToCotangent_smulC, map_smul]; rfl

set_option linter.unusedSectionVars false in

private lemma alignedPrincipalEndoCZ_inner (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e ζ : TangentSpace I x) :
    g₁.inner x (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x e) ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, e, W x, ζ]
          + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x, e, ζ]
          - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, ζ, e, W x]) := by
  change g₁.inner x (inverseMetricSharpFib (I := I) g₁ x
    (dualToCotangent (I := I)
      ((zPrincipalCovec (I := I) (M := M) g₀ S V W x e :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) ζ = _
  rw [inverseMetricSharpFib_inner (I := I) g₁ x _ ζ, cotangentToDualLinear_apply,
    cotangentToDual_dualToCotangent]
  exact zPrincipalCovec_apply (I := I) (M := M) g₀ S V W x e ζ

set_option linter.unusedSectionVars false in

private lemma alignedPrincipalEndoCZ_trace_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    LinearMap.trace ℝ E (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![V x, W x] := by
  classical
  rw [← traceViaCometric_c (I := I) (M := M) g₁ x (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x)]
  rw [ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁
    (iteratedCovGrad (I := I) g₀ 0 2 2 S) x ![V x, W x]]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [alignedPrincipalEndoCZ_inner (I := I) (M := M) g₀ g₁ S V W x
    (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k)]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

set_option linter.unusedSectionVars false in

theorem alignedPrincipalEndoC_sub_endoCZ_inner (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (e ζ : TangentSpace I x) :
    g₁.inner x
        (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁
            (⟨smoothExtensionTangent (I := I) x e, smoothExtensionTangent_contMDiff (I := I) x e⟩) W x (V x)
          - alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x e) ζ =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
            ![(LeviCivita (I := I) g₀).toFun
                (fun b => (⟨smoothExtensionTangent (I := I) x e,
                  smoothExtensionTangent_contMDiff (I := I) x e⟩ :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x (V x), W x, ζ]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![e, (LeviCivita (I := I) g₀).toFun (fun b => W b) x (V x), ζ]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![(LeviCivita (I := I) g₀).toFun (fun b => W b) x (V x), e, ζ]
          + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![W x, (LeviCivita (I := I) g₀).toFun
                (fun b => (⟨smoothExtensionTangent (I := I) x e,
                  smoothExtensionTangent_contMDiff (I := I) x e⟩ :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x (V x), ζ]
          - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![ζ, (LeviCivita (I := I) g₀).toFun
                (fun b => (⟨smoothExtensionTangent (I := I) x e,
                  smoothExtensionTangent_contMDiff (I := I) x e⟩ :
                    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x (V x), W x]
          - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S) x
              ![ζ, e, (LeviCivita (I := I) g₀).toFun (fun b => W b) x (V x)]) := by
  classical
  set ei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x e, smoothExtensionTangent_contMDiff (I := I) x e⟩ with hei
  have heix : ei x = e := smoothExtensionTangent_eq (I := I) x e
  rw [map_sub, ContinuousLinearMap.sub_apply]
  rw [alignedPrincipalEndoC_inner_secondKoszul (I := I) (M := M) g₀ g₁ S hbil ei W x (V x) ζ]
  rw [alignedPrincipalEndoCZ_inner (I := I) (M := M) g₀ g₁ S V W x e ζ]
  rw [heix]
  ring

def palatiniTracedPrincipalZRemainder (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)
        - alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i)
  + (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignCorrVecC (I := I) (M := M) g₀ g₁
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)) i)

set_option linter.unusedSectionVars false in

theorem palatini_tracedPrincipal_Zslot_eq_combinedTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x ![V x, W x]
        + palatiniTracedPrincipalZRemainder (I := I) (M := M) g₀ g₁ S V W x := by
  classical
  rw [← alignedPrincipalEndoCZ_trace_eq (I := I) (M := M) g₀ g₁ S V W x]
  rw [← traceViaBasis_c (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x)]
  rw [palatiniTracedPrincipalZRemainder]
  
  have hsumeq : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i
          + ((chartModelBasis E).repr
              (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)
                - alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i
            + (chartModelBasis E).repr
                (alignCorrVecC (I := I) (M := M) g₀ g₁
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)) i) := by
    intro i
    set ei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ with hei
    have hsplit := g1Principal_splitC (I := I) (M := M) g₀ g₁ ei W x (V x)
    rw [g1PrincipalVecC] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply, ← alignedPrincipalEndoC_apply]
    rw [show (chartModelBasis E).repr
          (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ ei W x (V x)) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignedPrincipalEndoC (I := I) (M := M) g₀ g₁ ei W x (V x)
                - alignedPrincipalEndoCZ (I := I) (M := M) g₀ g₁ S V W x ((chartModelBasis E) i)) i from by
      rw [map_sub, Finsupp.sub_apply]; ring]
    rw [add_assoc]
  rw [Finset.sum_congr rfl fun i _ => hsumeq i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

noncomputable def symmS (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 2 :=
  (1 / 2 : ℝ) • (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)

set_option linter.unusedSectionVars false in

private lemma unitModel_add2 (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x =
      unitModel (I := I) (M := M) g₀ 2 S x + unitModel (I := I) (M := M) g₀ 2 S' x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in

private lemma unitModel_eq_ccTensorBilin (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = ccTensorBilin (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option linter.unusedSectionVars false in

private lemma ccTensorBilin_domDomCongrSection_swap (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) b u w =
      ccTensorBilin (I := I) g₀ T b w u := by
  rw [← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ _ b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ T b w u]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T b,
      ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  fin_cases k <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

set_option linter.unusedSectionVars false in

private lemma ccTensorBilin_add (g₀ : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g₀ (S + T) b u w =
      ccTensorBilin (I := I) g₀ S b u w + ccTensorBilin (I := I) g₀ T b u w := by
  rw [← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ (S + T) b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ S b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ T b u w]
  rw [unitModel_add2 (I := I) (M := M) g₀ S T b, ContinuousMultilinearMap.add_apply]

set_option linter.unusedSectionVars false in

private lemma ccTensorBilin_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g₀ (c • S) b u w =
      c * ccTensorBilin (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in

theorem ccTensorBilin_symmS (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T) b u w =
      ccTensorBilinSymm (I := I) g₀ T b u w := by
  rw [symmS, ccTensorBilin_smul, ccTensorBilin_add,
    ccTensorBilin_domDomCongrSection_swap (I := I) (M := M) g₀ T b u w,
    ccTensorBilinSymm_apply]

set_option linter.unusedSectionVars false in

theorem symmS_hbil_of_realize (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T) b u w =
      g₁.inner b u w - g₀.inner b u w := by
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T b u w, hg₁ b u w]
  ring

set_option linter.unusedSectionVars false in

private lemma unitModel_domDomCongrSection_swap_add (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) (T + T')) x =
      unitModel (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x +
        unitModel (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T') x := by
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    unitModel_add2]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in

private lemma unitModel_domDomCongrSection_swap_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) (c • T)) x =
      c • unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x := by
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  have hsmul : unitModel (I := I) (M := M) g₀ 2 (c • T) x =
      c • unitModel (I := I) (M := M) g₀ 2 T x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]
  rw [hsmul]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in

private lemma unitModel_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (c • T) x =
      c • unitModel (I := I) (M := M) g₀ 2 T x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]

theorem symmS_add (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ (T + T') =
      symmS (I := I) (M := M) g₀ T + symmS (I := I) (M := M) g₀ T' := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  simp only [symmS, unitModel_smul, unitModel_add2, unitModel_domDomCongrSection_swap_add]
  module

theorem symmS_smul (g₀ : SmoothRiemannianMetric I M) (c : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ (c • T) = c • symmS (I := I) (M := M) g₀ T := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  simp only [symmS, unitModel_smul, unitModel_add2, unitModel_domDomCongrSection_swap_smul]
  module

theorem symmS_neg (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ (-T) = -symmS (I := I) (M := M) g₀ T := by
  have h := symmS_smul (I := I) (M := M) g₀ (-1 : ℝ) T
  rw [neg_one_smul, neg_one_smul] at h
  exact h

theorem symmS_sub (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ (T - T') =
      symmS (I := I) (M := M) g₀ T - symmS (I := I) (M := M) g₀ T' := by
  rw [sub_eq_add_neg, symmS_add, symmS_neg, sub_eq_add_neg]

private def alignedPrincipalEndoCcross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : E →ₗ[ℝ] E where
  toFun := fun v => inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
  map_add' := fun v v' => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x (v + v') :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) +
      (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v' :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_add]]
    rw [dualToCotangent_addC]
    rw [map_add]
  map_smul' := fun c v => by
    rw [show (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x (c • v) :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) =
      c • (((cotangentCov (LeviCivita (I := I) g₀)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) from by
      ext w; simp [map_smul]]
    rw [dualToCotangent_smulC]
    rw [map_smul]; rfl

@[simp] private lemma alignedPrincipalEndoCcross_apply (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x v =
      inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))) := rfl

private def g1PrincipalVecCcross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) gop)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))

private def alignCorrVecCcross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connDiff (I := I) gop g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) gop g₀ x w v +
                PDE.DeTurck.connDiff (I := I) gop g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) gop g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ)))

private lemma g1Principal_splitCcross
    (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    g1PrincipalVecCcross (I := I) (M := M) g₀ gop gcov Z Y x v =
      inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
        + alignCorrVecCcross (I := I) (M := M) g₀ gop gcov Z Y x v := by
  classical
  rw [g1PrincipalVecCcross, alignCorrVecCcross]
  rw [← map_add]
  congr 1
  rw [← dualToCotangent_addC]
  congr 1
  ext w
  rw [LinearMap.add_apply]
  
  
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ gcov Z Y x
  have halign := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ gop hθ v w
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]
  rw [show ((cotangentCov (LeviCivita (I := I) gop)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v) w =
      ((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v) w
        - cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connDiff (I := I) gop g₀ x w v) from by linarith [halign]]
  rw [show ((-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connDiff (I := I) gop g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (w + w') v =
              PDE.DeTurck.connDiff (I := I) gop g₀ x w v +
                PDE.DeTurck.connDiff (I := I) gop g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connDiff (I := I) gop g₀ x (c • w) v =
              c • PDE.DeTurck.connDiff (I := I) gop g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) w) =
      -(cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
        (PDE.DeTurck.connDiff (I := I) gop g₀ x w v)) from rfl]
  ring

private lemma alignedPrincipalEndoCcross_inner_secondKoszul
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v ζ : TangentSpace I x) :
    gop.inner x (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x v) ζ =
      (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
              ![v, Z x, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![v, Y x, Z x, ζ]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![v, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, Z x, ζ]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, ζ]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![ζ, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![ζ, Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v]) := by
  classical
  let Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩
  have hXfx : Xf x = v := smoothExtensionTangent_eq (I := I) x v
  rw [alignedPrincipalEndoCcross_apply]
  rw [inverseMetricSharpFib_inner (I := I) gop x _ ζ, cotangentToDualLinear_apply]
  rw [← hXfx]
  have hbridge := koszulCovGradCovec_covDeriv_eq_secondCovGrad (I := I) (M := M) g₀ gcov S' hbil Xf Y Z x ζ
  rw [hXfx]
  rw [hXfx] at hbridge
  rw [hbridge]

private lemma alignedPrincipalEndoCcross_trace_eq
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    LinearMap.trace ℝ E (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x ![Z x, Y x]
        + secondKoszulFrameRemainder (I := I) (M := M) g₀ gop S' Z Y x := by
  classical
  rw [← traceViaCometric_c (I := I) (M := M) gop x
    (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x)]
  rw [covDerivConnDiff_tracedPrincipal_eq_appCc (I := I) (M := M) g₀ gop S' x ![Z x, Y x]]
  rw [secondKoszulFrameRemainder]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        gop.inner x
          (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x
            (cometricLmodel (I := I) gop x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))))
          ((Module.finBasis ℝ E) k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
              ![cometricLmodel (I := I) gop x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)), Z x, Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![cometricLmodel (I := I) gop x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), Y x, Z x, (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 S') x
                ![cometricLmodel (I := I) gop x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k, Z x, Y x])
        + (1 / 2 : ℝ) *
          (unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                  (cometricLmodel (I := I) gop x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k))), Y x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Z x, (Module.finBasis ℝ E) k]
            + unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), (Module.finBasis ℝ E) k]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(Module.finBasis ℝ E) k, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k))), Y x]
            - unitModel (I := I) (M := M) g₀ 3 (covGrad (I := I) (M := M) g₀ 0 2 S') x
                ![(Module.finBasis ℝ E) k, Z x,
                  (LeviCivita (I := I) g₀).toFun (fun b => Y b) x
                    (cometricLmodel (I := I) gop x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))])) from by
      refine Finset.sum_congr rfl fun k _ => ?_
      exact alignedPrincipalEndoCcross_inner_secondKoszul (I := I) (M := M) g₀ gop gcov S' hbil Z Y x
        (cometricLmodel (I := I) gop x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1

def alignmentTraceRemainderCross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignCorrVecCcross (I := I) (M := M) g₀ gop gcov Z Y x ((chartModelBasis E) i)) i

def palatiniTracedPrincipalRemainderCross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (S' : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  secondKoszulFrameRemainder (I := I) (M := M) g₀ gop S' Z Y x
    + alignmentTraceRemainderCross (I := I) (M := M) g₀ gop gcov Z Y x

set_option linter.unusedSectionVars false in

theorem palatini_tracedPrincipal_cross_eq_combinedTrace
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x ![Z x, Y x]
        + palatiniTracedPrincipalRemainderCross (I := I) (M := M) g₀ gop gcov S' Z Y x := by
  classical
  have hsumeq : (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
                  ((chartModelBasis E) i) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr
            (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x
              ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignCorrVecCcross (I := I) (M := M) g₀ gop gcov Z Y x
                ((chartModelBasis E) i)) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsplit := g1Principal_splitCcross (I := I) (M := M) g₀ gop gcov Z Y x ((chartModelBasis E) i)
    rw [g1PrincipalVecCcross] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply]
    rw [← alignedPrincipalEndoCcross_apply]
  rw [hsumeq, Finset.sum_add_distrib]
  rw [traceViaBasis_c (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov Z Y x)]
  rw [alignedPrincipalEndoCcross_trace_eq (I := I) (M := M) g₀ gop gcov S' hbil Z Y x]
  rw [palatiniTracedPrincipalRemainderCross, alignmentTraceRemainderCross]
  ring

def palatiniTracedPrincipalDiffRemainder (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  palatiniTracedPrincipalRemainder (I := I) (M := M) g₀ g₁ S Z Y x
    - palatiniTracedPrincipalRemainderCross (I := I) (M := M) g₀ g₁ g₁' S' Z Y x

set_option linter.unusedSectionVars false in

theorem palatini_tracedPrincipalDiff_covector_eq_combinedTrace
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x
                    ((chartModelBasis E) i) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
      - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x
                    ((chartModelBasis E) i) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x ![Z x, Y x]
        + palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
            (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') Z Y x := by
  classical
  have hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T) b u w =
        g₁.inner b u w - g₀.inner b u w :=
    symmS_hbil_of_realize (I := I) (M := M) g₀ g₁ T hg₁
  have hbil' : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T') b u w =
        g₁'.inner b u w - g₀.inner b u w :=
    symmS_hbil_of_realize (I := I) (M := M) g₀ g₁' T' hg₁'
  rw [palatini_tracedPrincipal_eq_combinedTrace (I := I) (M := M) g₀ g₁
        (symmS (I := I) (M := M) g₀ T) hbil Z Y x]
  rw [palatini_tracedPrincipal_cross_eq_combinedTrace (I := I) (M := M) g₀ g₁ g₁'
        (symmS (I := I) (M := M) g₀ T') hbil' Z Y x]
  rw [palatiniTracedPrincipalDiffRemainder]
  rw [symmS_sub (I := I) (M := M) g₀ T T']
  rw [iteratedCovGrad_sub (I := I) g₀ 0 2 2
        (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T')]
  
  have happCc_sub : appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) =
      appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T))
        - appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) =
        iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          + (-1 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T') from by
      rw [neg_one_smul]; abel]
    rw [appCc_add_right, appCc_smul_right, neg_one_smul]
    abel
  rw [happCc_sub]
  have hsub : ∀ (a b : SmoothCcTensor g₀ 0 2),
      unitModel (I := I) (M := M) g₀ 2 (a - b) x ![Z x, Y x] =
        unitModel (I := I) (M := M) g₀ 2 a x ![Z x, Y x]
          - unitModel (I := I) (M := M) g₀ 2 b x ![Z x, Y x] := by
    intro a b
    rw [show a - b = a + (-1 : ℝ) • b from by rw [neg_one_smul]; abel,
        unitModel_add2, unitModel_smul]
    rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [hsub]
  ring

def palatiniTracedPrincipalZRemainderCross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (S' : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)
        - alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i)
  + (∑ i : Fin (Module.finrank ℝ E),
    (chartModelBasis E).repr
      (alignCorrVecCcross (I := I) (M := M) g₀ gop gcov
          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
          W x (V x)) i)

set_option linter.unusedSectionVars false in

theorem palatini_tracedPrincipal_Zslot_cross_eq_combinedTrace
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x ![V x, W x]
        + palatiniTracedPrincipalZRemainderCross (I := I) (M := M) g₀ gop gcov S' V W x := by
  classical
  rw [← alignedPrincipalEndoCZ_trace_eq (I := I) (M := M) g₀ gop S' V W x]
  rw [← traceViaBasis_c (alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x)]
  rw [palatiniTracedPrincipalZRemainderCross]
  have hsumeq : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E).repr
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) gop)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i
          + ((chartModelBasis E).repr
              (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)
                - alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i
            + (chartModelBasis E).repr
                (alignCorrVecCcross (I := I) (M := M) g₀ gop gcov
                  (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                    smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W x (V x)) i) := by
    intro i
    set ei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ with hei
    have hsplit := g1Principal_splitCcross (I := I) (M := M) g₀ gop gcov ei W x (V x)
    rw [g1PrincipalVecCcross] at hsplit
    rw [hsplit]
    rw [map_add, Finsupp.add_apply, ← alignedPrincipalEndoCcross_apply]
    rw [show (chartModelBasis E).repr
          (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov ei W x (V x)) i =
        (chartModelBasis E).repr
            (alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i
          + (chartModelBasis E).repr
              (alignedPrincipalEndoCcross (I := I) (M := M) g₀ gop gcov ei W x (V x)
                - alignedPrincipalEndoCZ (I := I) (M := M) g₀ gop S' V W x ((chartModelBasis E) i)) i from by
      rw [map_sub, Finsupp.sub_apply]; ring]
    rw [add_assoc]
  rw [Finset.sum_congr rfl fun i _ => hsumeq i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

def palatiniTracedPrincipalZDiffRemainder (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  palatiniTracedPrincipalZRemainder (I := I) (M := M) g₀ g₁ S V W x
    - palatiniTracedPrincipalZRemainderCross (I := I) (M := M) g₀ g₁ g₁' S' V W x

set_option linter.unusedSectionVars false in

theorem palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                    (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                      smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
      - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                    (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                      smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) W b)) x (V x) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x ![V x, W x]
        + palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
            (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') V W x := by
  classical
  rw [palatini_tracedPrincipal_Zslot_eq_combinedTrace (I := I) (M := M) g₀ g₁
        (symmS (I := I) (M := M) g₀ T) V W x]
  rw [palatini_tracedPrincipal_Zslot_cross_eq_combinedTrace (I := I) (M := M) g₀ g₁ g₁'
        (symmS (I := I) (M := M) g₀ T') V W x]
  rw [palatiniTracedPrincipalZDiffRemainder]
  rw [symmS_sub (I := I) (M := M) g₀ T T']
  rw [iteratedCovGrad_sub (I := I) g₀ 0 2 2
        (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T')]
  have happCc_sub : appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) =
      appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T))
        - appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T')) =
        iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T)
          + (-1 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ T') from by
      rw [neg_one_smul]; abel]
    rw [appCc_add_right, appCc_smul_right, neg_one_smul]
    abel
  rw [happCc_sub]
  have hsub : ∀ (a b : SmoothCcTensor g₀ 0 2),
      unitModel (I := I) (M := M) g₀ 2 (a - b) x ![V x, W x] =
        unitModel (I := I) (M := M) g₀ 2 a x ![V x, W x]
          - unitModel (I := I) (M := M) g₀ 2 b x ![V x, W x] := by
    intro a b
    rw [show a - b = a + (-1 : ℝ) • b from by rw [neg_one_smul]; abel,
        unitModel_add2, unitModel_smul]
    rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [hsub]
  ring

noncomputable def reindexCoeffFib (σ' : Equiv.Perm (Fin 4)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  A.comp
    ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).symm.toContinuousLinearMap.comp
      (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            σ').toContinuousLinearEquiv.toContinuousLinearMap).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap))

set_option linter.unusedSectionVars false in

theorem reindexCoeffFib_apply (σ' : Equiv.Perm (Fin 4)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    reindexCoeffFib (I := I) σ' x A D =
      A (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel D))) := by
  rw [reindexCoeffFib, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

set_option linter.unusedSectionVars false in

private theorem reindexCoeffFib_add (σ' : Equiv.Perm (Fin 4)) (x : M)
    (A B : Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    reindexCoeffFib (I := I) σ' x (A + B) D =
      reindexCoeffFib (I := I) σ' x A D + reindexCoeffFib (I := I) σ' x B D := by
  rw [reindexCoeffFib_apply, reindexCoeffFib_apply, reindexCoeffFib_apply,
    ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem reindexCoeffFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (reindexCoeffFib (I := I) σ' x
          (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
            R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => reindexCoeffFib (I := I) σ' x
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        R.toSection x))
  intro Y
  
  
  have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
            Tensor0SBundle.Tensor0SSpace 4 I x))).mpr ?_
    have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Y x)).mp Y.contMDiff
    intro τ x₀
    refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  have hRY := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff hYσ
  refine hRY.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t)
    (reindexCoeffFib_apply (I := I) σ' x
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        R.toSection x) (Y x)).symm

noncomputable def reindexCoeff (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from
          reindexCoeffFib (I := I) σ' x
            (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
              R.toSection x))
      contMDiff_toFun := reindexCoeffFib_contMDiff (I := I) (M := M) g₀ R σ' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem reindexCoeff_toSection (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4)) (x : M) :
    (reindexCoeff (I := I) (M := M) g₀ R σ').toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from
        reindexCoeffFib (I := I) σ' x
          (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
            R.toSection x)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem reindexCoeff_appCc_eq (g₀ : SmoothRiemannianMetric I M)
    (R : SmoothCcTensor g₀ 4 2) (σ' : Equiv.Perm (Fin 4))
    (W W' : SmoothCcTensor g₀ 0 4)
    (hWW' : ∀ x : M, unitModel (I := I) (M := M) g₀ 4 W' x =
      ContinuousMultilinearMap.domDomCongr σ' (unitModel (I := I) (M := M) g₀ 4 W x))
    (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (reindexCoeff (I := I) (M := M) g₀ R σ') W) x =
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 R W') x := by
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [reindexCoeff_toSection]
  
  rw [reindexCoeffFib_apply (I := I) σ' x
    (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      R.toSection x)
    ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
      W.toSection x) (unitTensor (I := I) (M := M) x))]
  
  have hWu : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 4 W x := rfl
  have hW'u : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
        W'.toSection x) (unitTensor (I := I) (M := M) x) =
      Tensor0SBundle.Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g₀ 4 W' x) := by
    rw [show unitModel (I := I) (M := M) g₀ 4 W' x =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
            W'.toSection x) (unitTensor (I := I) (M := M) x)) from rfl,
      Tensor0SBundle.Tensor0SSpace.ofModel_toModel]
  rw [hWu, ← hWW' x, hW'u]

set_option linter.unusedSectionVars false in

private theorem iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in

theorem iteratedCovGrad_symmS_eq (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) (M := M) g₀ T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) := by
  rw [symmS, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in

private theorem appCc_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (Φ : SmoothCcTensor g r s) (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (c • Φ) W =
      c • appCc (I := I) (M := M) g r s Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((c • appCc (I := I) (M := M) g r s Φ W).toSection x) =
      c • (appCc (I := I) (M := M) g r s Φ W).toSection x from rfl]
  rw [appCc_toSection, appCc_toSection]
  rw [show ((c • Φ).toSection x : TensorRSSpace r s I x) = c • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option linter.unusedSectionVars false in

theorem symmAbsorbedPrincipalCoeff_appCc_eq
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (R₂ : SmoothCcTensor g₀ 4 2) :
    ∃ R₂' : SmoothCcTensor g₀ 4 2, ∀ (x : M) (v : Fin 2 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 R₂'
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 R₂
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S))) x v := by
  classical
  
  obtain ⟨σ', hσ'⟩ := exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) S 2
  refine ⟨(1 / 2 : ℝ) • R₂ + (1 / 2 : ℝ) • reindexCoeff (I := I) (M := M) g₀ R₂ σ', fun x v => ?_⟩
  
  have hsymm : iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 S +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S) := by
    rw [symmS, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]
  
  set uR : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v with huR
  set uRein : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ 4 2 (reindexCoeff (I := I) (M := M) g₀ R₂ σ')
      (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v with huRein
  
  have hLHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2
        ((1 / 2 : ℝ) • R₂ + (1 / 2 : ℝ) • reindexCoeff (I := I) (M := M) g₀ R₂ σ')
        (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [appCc_add_left, appCc_smul_left, appCc_smul_left, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, huRein]
    simp only [smul_eq_mul]
  
  have hSwap : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2 R₂
        (iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))) x v = uRein := by
    rw [huRein]
    exact congrFun (congrArg _
      (reindexCoeff_appCc_eq (I := I) (M := M) g₀ R₂ σ'
        (iteratedCovGrad (I := I) g₀ 0 2 2 S)
        (iteratedCovGrad (I := I) g₀ 0 2 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))
        hσ' x).symm) v
  have hRHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ 4 2 R₂
        (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S))) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [hsymm, appCc_add_right, appCc_smul_right, appCc_smul_right, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, hSwap]
    simp only [smul_eq_mul]
  rw [hLHS, hRHS]

noncomputable def reindexCoeffFibGen (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x) :
    Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x :=
  A.comp
    ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x).symm.toContinuousLinearMap.comp
      (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            σ').toContinuousLinearEquiv.toContinuousLinearMap).comp
        (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) r x).toContinuousLinearMap))

set_option linter.unusedSectionVars false in

theorem reindexCoeffFibGen_apply (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x)
    (D : Tensor0SBundle.Tensor0SSpace r I x) :
    reindexCoeffFibGen (I := I) r s σ' x A D =
      A (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel D))) := by
  rw [reindexCoeffFibGen, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem reindexCoeffFibGen_contMDiff (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x
        (reindexCoeffFibGen (I := I) r s σ' x
          (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace r I x)
    (F₂ := Tensor0SBundle.Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace s I x)
    (φ := fun x => reindexCoeffFibGen (I := I) r s σ' x
      (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
        R.toSection x))
  intro Y
  have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace r I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y x))) :
            Tensor0SBundle.Tensor0SSpace r I x))).mpr ?_
    have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Y x)).mp Y.contMDiff
    intro τ x₀
    refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SBundle.Tensor0SSpace.toModel (Y x)))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  have hRY := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff hYσ
  refine hRY.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x t)
    (reindexCoeffFibGen_apply (I := I) r s σ' x
      (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
        R.toSection x) (Y x)).symm

noncomputable def reindexCoeffGen (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    SmoothCcTensor g₀ r s where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace r s I x from
          reindexCoeffFibGen (I := I) r s σ' x
            (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
              R.toSection x))
      contMDiff_toFun := reindexCoeffFibGen_contMDiff (I := I) (M := M) g₀ r s R σ' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem reindexCoeffGen_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) (x : M) :
    (reindexCoeffGen (I := I) (M := M) g₀ r s R σ').toSection x =
      (show Tensor0SBundle.TensorRSSpace r s I x from
        reindexCoeffFibGen (I := I) r s σ' x
          (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            R.toSection x)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem reindexCoeffGen_appCc_eq (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (R : SmoothCcTensor g₀ r 2) (σ' : Equiv.Perm (Fin r))
    (W W' : SmoothCcTensor g₀ 0 r)
    (hWW' : ∀ x : M, unitModel (I := I) (M := M) g₀ r W' x =
      ContinuousMultilinearMap.domDomCongr σ' (unitModel (I := I) (M := M) g₀ r W x))
    (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ r 2 (reindexCoeffGen (I := I) (M := M) g₀ r 2 R σ') W) x =
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 R W') x := by
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [reindexCoeffGen_toSection]
  rw [reindexCoeffFibGen_apply (I := I) r 2 σ' x
    (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      R.toSection x)
    ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
      W.toSection x) (unitTensor (I := I) (M := M) x))]
  have hWu : Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ r W x := rfl
  have hW'u : (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
        W'.toSection x) (unitTensor (I := I) (M := M) x) =
      Tensor0SBundle.Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g₀ r W' x) := by
    rw [show unitModel (I := I) (M := M) g₀ r W' x =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace r I x from
            W'.toSection x) (unitTensor (I := I) (M := M) x)) from rfl,
      Tensor0SBundle.Tensor0SSpace.ofModel_toModel]
  rw [hWu, ← hWW' x, hW'u]

noncomputable def symmAbsorbedCoeff (g₀ : SmoothRiemannianMetric I M) (i : ℕ)
    (R : SmoothCcTensor g₀ (2 + i) 2)
    (σ' : Equiv.Perm (Fin (2 + i))) : SmoothCcTensor g₀ (2 + i) 2 :=
  (1 / 2 : ℝ) • R + (1 / 2 : ℝ) • reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ'

set_option linter.unusedSectionVars false in

theorem symmAbsorbedCoeff_appCc_eq (g₀ : SmoothRiemannianMetric I M) (i : ℕ)
    (S : SmoothCcTensor g₀ 0 2) (R : SmoothCcTensor g₀ (2 + i) 2)
    (σ' : Equiv.Perm (Fin (2 + i)))
    (hσ' : ∀ x : M, unitModel (I := I) (M := M) g₀ (2 + i)
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S)) x =
      ContinuousMultilinearMap.domDomCongr σ'
        (unitModel (I := I) (M := M) g₀ (2 + i)
          (iteratedCovGrad (I := I) g₀ 0 2 i S) x))
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ (2 + i) 2 (symmAbsorbedCoeff (I := I) (M := M) g₀ i R σ')
          (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ (2 + i) 2 R
          (iteratedCovGrad (I := I) g₀ 0 2 i (symmS (I := I) (M := M) g₀ S))) x v := by
  classical
  have hsymm : iteratedCovGrad (I := I) g₀ 0 2 i (symmS (I := I) (M := M) g₀ S) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 i S +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S) := by
    rw [symmS, iteratedCovGrad_smul, iteratedCovGrad_add, smul_add]
  set uR : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ (2 + i) 2 R (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v with huR
  set uRein : ℝ := unitModel (I := I) (M := M) g₀ 2
    (appCc (I := I) (M := M) g₀ (2 + i) 2
      (reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ')
      (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v with huRein
  have hLHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ (2 + i) 2
        ((1 / 2 : ℝ) • R + (1 / 2 : ℝ) • reindexCoeffGen (I := I) (M := M) g₀ (2 + i) 2 R σ')
        (iteratedCovGrad (I := I) g₀ 0 2 i S)) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [appCc_add_left, appCc_smul_left, appCc_smul_left, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, huRein]
    simp only [smul_eq_mul]
  have hSwap : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ (2 + i) 2 R
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))) x v = uRein := by
    rw [huRein]
    exact congrFun (congrArg _
      (reindexCoeffGen_appCc_eq (I := I) (M := M) g₀ (2 + i) R σ'
        (iteratedCovGrad (I := I) g₀ 0 2 i S)
        (iteratedCovGrad (I := I) g₀ 0 2 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S))
        hσ' x).symm) v
  have hRHS : unitModel (I := I) (M := M) g₀ 2
      (appCc (I := I) (M := M) g₀ (2 + i) 2 R
        (iteratedCovGrad (I := I) g₀ 0 2 i (symmS (I := I) (M := M) g₀ S))) x v =
      (1 / 2 : ℝ) * uR + (1 / 2 : ℝ) * uRein := by
    rw [hsymm, appCc_add_right, appCc_smul_right, appCc_smul_right, unitModel_add2,
      unitModel_smul, unitModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply]
    rw [huR, hSwap]
    simp only [smul_eq_mul]
  rw [symmAbsorbedCoeff, hLHS, hRHS]

set_option linter.unusedSectionVars false in

theorem inverseMetricSharpFib_sub_inner_g1
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g₁.inner x
        (inverseMetricSharpFib (I := I) g₁ x α
          - inverseMetricSharpFib (I := I) g₁' x α) w =
      cotangentToDualLinear (I := I) (x := x) α w
        - g₁.inner x (inverseMetricSharpFib (I := I) g₁' x α) w := by
  rw [map_sub, ContinuousLinearMap.sub_apply,
      inverseMetricSharpFib_inner (I := I) g₁ x α w]

set_option linter.unusedSectionVars false in

theorem inverseMetricSharpFib_sub_inner_g1_realize
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w)
    (x : M) (α : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    g₁.inner x
        (inverseMetricSharpFib (I := I) g₁ x α
          - inverseMetricSharpFib (I := I) g₁' x α) w =
      - ccTensorBilinSymm (I := I) g₀ (T - T') x
          (inverseMetricSharpFib (I := I) g₁' x α) w := by
  rw [inverseMetricSharpFib_sub_inner_g1 (I := I) g₁ g₁' x α w]
  rw [← inverseMetricSharpFib_inner (I := I) g₁' x α w]
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₁' x α with hu
  rw [hg₁' x u w, hg₁ x u w]
  have hbsub : ∀ (a c : TangentSpace I x),
      ccTensorBilin (I := I) g₀ (T - T') x a c =
        ccTensorBilin (I := I) g₀ T x a c - ccTensorBilin (I := I) g₀ T' x a c := by
    intro a c
    rw [show T - T' = T + (-1 : ℝ) • T' from by rw [neg_one_smul]; abel,
      ccTensorBilin_add (I := I) (M := M) g₀ T ((-1 : ℝ) • T') x a c,
      ccTensorBilin_smul (I := I) (M := M) g₀ (-1 : ℝ) T' x a c]
    ring
  have hsub : ccTensorBilinSymm (I := I) g₀ (T - T') x u w =
      ccTensorBilinSymm (I := I) g₀ T x u w - ccTensorBilinSymm (I := I) g₀ T' x u w := by
    rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, ccTensorBilinSymm_apply,
      hbsub u w, hbsub w u]
    ring
  rw [hsub]; ring

set_option linter.unusedSectionVars false in

theorem cotangentCov_leviCivita_diff_endpoint
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    {θ : Π b : M, TangentSpace I b →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent (I := I) θ x)
    (v w : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g₁)).toFun θ x v) w -
        ((cotangentCov (LeviCivita (I := I) g₁')).toFun θ x v) w =
      -θ x (PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v) := by
  have h1 := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁ hθ v w
  have h1' := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ g₁' hθ v w
  
  have hcocycle : PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x w v := by
    classical
    set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hYdef
    have hY := smoothExtensionTangent_mdiff (I := I) x w x
    have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w
    have e1 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₁' (σ := Y) hY v
    have e2 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
    have e3 := PDE.DeTurck.connDiff_apply (I := I) g₁' g₀ (σ := Y) hY v
    rw [hYx] at e1 e2 e3
    rw [e1, e2, e3]; abel
  rw [hcocycle, map_sub]
  linarith [h1, h1']

set_option linter.unusedSectionVars false in

theorem oArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (dir : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁)).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir))
        - inverseMetricSharpFib (I := I) g₁' x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)) =
      (inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                (fun b : M => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir))
          - inverseMetricSharpFib (I := I) g₁' x
              (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)))
        + inverseMetricSharpFib (I := I) g₁' x
            (dualToCotangent (I := I)
                ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b : M => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)
              - dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)) := by
  rw [map_sub]
  abel

set_option linter.unusedSectionVars false in

theorem oArm_leg_eq_connDiff (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (dir : TangentSpace I x) :
    dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₁)).toFun
            (fun b : M => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir)
        - dualToCotangent (I := I)
            ((cotangentCov (LeviCivita (I := I) g₁')).toFun
              (fun b : M => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x dir) =
      dualToCotangent (I := I)
        (-((cotangentToCLM (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y x)).comp
            ((PDE.DeTurck.connDiff (I := I) g₁ g₁' x).flip dir)).toLinearMap) := by
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ g₁' Z Y x
  rw [← dualToCotangent_subC]
  congr 1
  ext w
  have hbridge := cotangentCov_leviCivita_diff_endpoint (I := I) (M := M) g₀ g₁ g₁' hθ dir w
  rw [LinearMap.sub_apply]
  simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_coe]
  exact hbridge

set_option linter.unusedSectionVars false in

theorem connDiff_endpoint_cocycle (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (w v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x w v
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x w v =
      PDE.DeTurck.connDiff (I := I) g₁ g₁' x w v := by
  classical
  set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hYdef
  have hY := smoothExtensionTangent_mdiff (I := I) x w x
  have hYx : Y x = w := smoothExtensionTangent_eq (I := I) x w
  have e1 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₁' (σ := Y) hY v
  have e2 := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Y) hY v
  have e3 := PDE.DeTurck.connDiff_apply (I := I) g₁' g₀ (σ := Y) hY v
  rw [hYx] at e1 e2 e3
  rw [e1, e2, e3]; abel

set_option linter.unusedSectionVars false in

theorem csArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (a a' dir : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x a dir
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x a' dir =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (a - a') dir
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x a' dir := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x a' dir]
  rw [map_sub, ContinuousLinearMap.sub_apply]
  abel

set_option linter.unusedSectionVars false in

theorem quadArm_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (q q' dir : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x q dir
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x q' dir =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x (q - q') dir
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x q' dir := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x q' dir]
  rw [map_sub, ContinuousLinearMap.sub_apply]
  abel

set_option linter.unusedSectionVars false in

theorem combinedLowerArm_extension_free
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w) :
    ∃ R₂' : SmoothCcTensor g₀ 4 2,
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
      (
        ((∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (inverseMetricSharpFib (I := I) g₁ x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                        ((chartModelBasis E) i)))
                - inverseMetricSharpFib (I := I) g₁' x
                    (dualToCotangent (I := I)
                      ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                        (fun b : M => cotangentToCLM (I := I)
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                          ((chartModelBasis E) i)))) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (inverseMetricSharpFib (I := I) g₁ x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))
                - inverseMetricSharpFib (I := I) g₁' x
                    (dualToCotangent (I := I)
                      ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                        (fun b : M => cotangentToCLM (I := I)
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))) i))
          ) + (
        (∑ i : Fin (Module.finrank ℝ E),
              (chartModelBasis E).repr
                (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (inverseMetricSharpFib (I := I) g₁ x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (inverseMetricSharpFib (I := I) g₁' x
                            (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                              (⟨smoothExtensionTangent (I := I) x (v 0),
                                smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                              (⟨smoothExtensionTangent (I := I) x (v 1),
                                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (smoothExtensionTangent (I := I) x (v 1) x)
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                        (smoothExtensionTangent (I := I) x (v 0) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                          (smoothExtensionTangent (I := I) x (v 0) x))) i)
            - (∑ i : Fin (Module.finrank ℝ E),
              (chartModelBasis E).repr
                (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (inverseMetricSharpFib (I := I) g₁ x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x (v 0) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (inverseMetricSharpFib (I := I) g₁' x
                            (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                              (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                                smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                              (⟨smoothExtensionTangent (I := I) x (v 1),
                                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                            (smoothExtensionTangent (I := I) x (v 0) x))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          (smoothExtensionTangent (I := I) x (v 1) x)
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                              (smoothExtensionTangent (I := I) x (v 0) x)))
                  - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                          ((LeviCivita (I := I) g₀).toFun
                            (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                              (smoothExtensionTangent (I := I) x (v 0) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))) i)
          ) + (
        ((∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x)) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x)) i))
        + (palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
              (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T')
              (⟨smoothExtensionTangent (I := I) x (v 0),
                smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
              (⟨smoothExtensionTangent (I := I) x (v 1),
                smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x
            - palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T')
                (⟨smoothExtensionTangent (I := I) x (v 0),
                  smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                (⟨smoothExtensionTangent (I := I) x (v 1),
                  smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x)) =
        ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1)
          - unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 4 2 R₂'
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨R₂', hR₂'⟩ := symmAbsorbedPrincipalCoeff_appCc_eq (I := I) (M := M) g₀ (T - T')
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
      - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
  refine ⟨R₂', fun x v => ?_⟩
  set Zv : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 0), smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩
    with hZv
  set Yw : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (v 1), smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩
    with hYw
  have hZvx : Zv x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
  have hYwx : Yw x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
  have hcons : (![v 0, v 1] : Fin 2 → TangentSpace I x) = v := by
    funext k; fin_cases k <;> rfl
  
  have htel : ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
      (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x (v 1)) x
              - covDerivConnDiff (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 1)) x)
            + (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x (v 1)) x
              - covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x (v 0))
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x (v 1)) x)
            + (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x (v 0))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x (v 1)) x)
                  (smoothExtensionTangent (I := I) x (v 0) x))) i) := by
    have h₁ := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁ x (v 0) (v 1)
    have h₁' := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁' x (v 0) (v 1)
    rw [show ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
        (ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₀ x (v 0) (v 1))
          - (ricciTensor (I := I) g₁' x (v 0) (v 1) - ricciTensor (I := I) g₀ x (v 0) (v 1)) from by
      ring]
    rw [h₁, h₁']
  
  have hgradX : ∀ i : Fin (Module.finrank ℝ E),
      covDerivConnDiff (I := I) g₀ g₁ (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0)) (smoothExtensionTangent (I := I) x (v 1)) x =
      _ + covDerivConnDiff (I := I) g₀ g₁'
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 0)) (smoothExtensionTangent (I := I) x (v 1)) x :=
    fun i => eq_add_of_sub_eq
      (covDerivConnDiff_diff_endpoint_graded (I := I) (M := M) g₀ g₁ g₁'
        ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ Yw Zv x)
  have hgradZ : ∀ i : Fin (Module.finrank ℝ E),
      covDerivConnDiff (I := I) g₀ g₁ (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x =
      _ + covDerivConnDiff (I := I) g₀ g₁' (smoothExtensionTangent (I := I) x (v 0))
            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
            (smoothExtensionTangent (I := I) x (v 1)) x :=
    fun i => eq_add_of_sub_eq
      (covDerivConnDiff_diff_endpoint_graded (I := I) (M := M) g₀ g₁ g₁' Zv Yw
        ⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩ x)
  
  have hregroup :
      ricciTensor (I := I) g₁ x (v 0) (v 1) - ricciTensor (I := I) g₁' x (v 0) (v 1) =
      (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                        (⟨smoothExtensionTangent (I := I) x (v 0),
                          smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                        (⟨smoothExtensionTangent (I := I) x (v 1),
                          smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                      ((chartModelBasis E) i)))
              - inverseMetricSharpFib (I := I) g₁' x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x
                        ((chartModelBasis E) i)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
                (dualToCotangent (I := I)
                  ((cotangentCov (LeviCivita (I := I) g₁)).toFun
                    (fun b : M => cotangentToCLM (I := I)
                      (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                        (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                          smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                        (⟨smoothExtensionTangent (I := I) x (v 1),
                          smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))
              - inverseMetricSharpFib (I := I) g₁' x
                  (dualToCotangent (I := I)
                    ((cotangentCov (LeviCivita (I := I) g₁')).toFun
                      (fun b : M => cotangentToCLM (I := I)
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) b)) x (v 0)))) i))
        ) + (
      (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (inverseMetricSharpFib (I := I) g₁ x
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                          (⟨smoothExtensionTangent (I := I) x (v 0),
                            smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (inverseMetricSharpFib (I := I) g₁' x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x (v 0),
                              smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (smoothExtensionTangent (I := I) x (v 1) x)
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 0) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                      (smoothExtensionTangent (I := I) x (v 0) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))
                        (smoothExtensionTangent (I := I) x (v 0) x))) i)
          - (∑ i : Fin (Module.finrank ℝ E),
            (chartModelBasis E).repr
              (-(PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (inverseMetricSharpFib (I := I) g₁ x
                        (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                          (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                            smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                          (⟨smoothExtensionTangent (I := I) x (v 1),
                            smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                        (smoothExtensionTangent (I := I) x (v 0) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (inverseMetricSharpFib (I := I) g₁' x
                          (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                            (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                              smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩)
                            (⟨smoothExtensionTangent (I := I) x (v 1),
                              smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩) x))
                          (smoothExtensionTangent (I := I) x (v 0) x))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (smoothExtensionTangent (I := I) x (v 1) x)
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                          (smoothExtensionTangent (I := I) x (v 0) x))
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        (smoothExtensionTangent (I := I) x (v 1) x)
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x ((chartModelBasis E) i) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x)))
                - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      ((LeviCivita (I := I) g₀).toFun
                        (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                          (smoothExtensionTangent (I := I) x (v 0) x))
                      (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                    - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                        ((LeviCivita (I := I) g₀).toFun
                          (fun b => smoothExtensionTangent (I := I) x (v 1) b) x
                            (smoothExtensionTangent (I := I) x (v 0) x))
                        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x))) i)
        ) + (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
              - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x (v 0) x)) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
              - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
                (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                  (smoothExtensionTangent (I := I) x (v 1)) x)
                (smoothExtensionTangent (I := I) x (v 0) x)) i))
        ) + (
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
      - ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
        ) := by
    rw [htel]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [← Finsupp.sub_apply, ← Finsupp.add_apply, ← map_sub, ← map_add]
    refine congrArg (fun t => (chartModelBasis E).repr t i) ?_
    rw [hgradX i, hgradZ i]
    simp only [hZv, hYw, ContMDiffSection.coeFn_mk, smoothExtensionTangent_eq]
    abel
  
  
  have hPX := palatini_tracedPrincipalDiff_covector_eq_combinedTrace
    (I := I) (M := M) g₀ g₁ g₁' T T' hg₁ hg₁' Zv Yw x
  have hPZ := palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace
    (I := I) (M := M) g₀ g₁ g₁' T T' Zv Yw x
  have hR₂'v := hR₂' x v
  rw [hZvx, hYwx, hcons] at hPX hPZ
  have huXZ : unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x v
      - unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x v =
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2
            (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
              - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ (T - T')))) x v := by
    rw [show ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁ =
        ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          + (-1 : ℝ) • ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁ from by
      rw [neg_one_smul]; abel]
    rw [appCc_add_left, appCc_smul_left, unitModel_add2, unitModel_smul,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply]
    simp only [smul_eq_mul]
    ring
  
  
  have hP :
      ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Zv Yw b)) x
                      ((chartModelBasis E) i) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i))
      - ((∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
          (chartModelBasis E).repr
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                      (⟨smoothExtensionTangent (I := I) x ((chartModelBasis E) i),
                        smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)⟩) Yw b)) x
                        (v 0) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) i)) =
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 4 2 R₂'
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v
          + (palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') Zv Yw x
              - palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
                  (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') Zv Yw x) := by
    rw [hPX, hPZ, hR₂'v]
    linarith [huXZ]
  rw [hregroup]
  simp only [← hZv, ← hYw]
  linarith [hP]

set_option linter.unusedSectionVars false in

def lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] Tensor0SSpace 1 I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => dualToCotangent (I := I) (x := x) (g₁'.inner x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((g₁'.inner x (v + v')).toLinearMap : Module.Dual ℝ (TangentSpace I x))
            = (g₁'.inner x v).toLinearMap + (g₁'.inner x v').toLinearMap := by
          ext w; simp [map_add]
        rw [h, dualToCotangent_addC]
      map_smul' := fun c v => by
        have h : ((g₁'.inner x (c • v)).toLinearMap : Module.Dual ℝ (TangentSpace I x))
            = c • (g₁'.inner x v).toLinearMap := by
          ext w; simp [map_smul]
        rw [h, dualToCotangent_smulC]; rfl }

@[simp] lemma lowerFlatCLM_apply (g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    lowerFlatCLM (I := I) g₁' x v =
      dualToCotangent (I := I) (x := x) (g₁'.inner x v).toLinearMap := by
  rw [lowerFlatCLM, LinearMap.coe_toContinuousLinearMap']; rfl

set_option linter.unusedSectionVars false in

@[simp] lemma cotangentToDual_lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) (lowerFlatCLM (I := I) g₁' x v) w = g₁'.inner x v w := by
  rw [lowerFlatCLM_apply, cotangentToDual_dualToCotangent]; rfl

set_option linter.unusedSectionVars false in

lemma inverseMetricSharpFib_lowerFlatCLM (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁' x (lowerFlatCLM (I := I) g₁' x v) = v := by
  have hkey : (g₁'.inner x (inverseMetricSharpFib (I := I) g₁' x (lowerFlatCLM (I := I) g₁' x v)) :
        TangentSpace I x →L[ℝ] ℝ) = g₁'.inner x v := by
    ext w
    rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_lowerFlatCLM]
  
  have hinj : Function.Injective
      (fun u : TangentSpace I x => (g₁'.inner x u : TangentSpace I x →L[ℝ] ℝ)) := by
    intro a b hab
    have hval : ∀ w, g₁'.inner x a w = g₁'.inner x b w := fun w => by
      have := congrArg (fun (φ : TangentSpace I x →L[ℝ] ℝ) => φ w) hab
      simpa using this
    by_contra hne
    have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hpos := g₁'.pos x (a - b) hsub
    have hzero : g₁'.inner x (a - b) (a - b) = 0 := by
      have hsymm₁ : g₁'.inner x (a - b) (a - b)
          = g₁'.inner x (a - b) a - g₁'.inner x (a - b) b := by rw [← map_sub]
      rw [hsymm₁, g₁'.symm x (a - b) a, g₁'.symm x (a - b) b]
      have e1 : g₁'.inner x a (a - b) = g₁'.inner x b (a - b) := hval (a - b)
      rw [e1]; ring
    exact absurd hzero (ne_of_gt hpos)
  exact hinj hkey

set_option linter.unusedSectionVars false in

lemma inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    inverseMetricSharpFib (I := I) g₁ x (lowerFlatCLM (I := I) g₁' x v) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        (g₁'.inner x v).toLinearMap := by
  rw [inverseMetricSharpFib_apply, lowerFlatCLM_apply]
  rw [show cotangentToDualLinear (I := I)
        (dualToCotangent (I := I) (g₁'.inner x v).toLinearMap)
        = (g₁'.inner x v).toLinearMap from by
    rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]]

def combinedLowerRaisedEndo0 (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (inverseMetricSharpFib (I := I) g₁ x).comp (lowerFlatCLM (I := I) g₁' x)
    - ContinuousLinearMap.id ℝ (TangentSpace I x)

@[simp] lemma combinedLowerRaisedEndo0_apply (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁ g₁' x v =
      inverseMetricSharpFib (I := I) g₁ x (lowerFlatCLM (I := I) g₁' x v) - v := by
  rw [combinedLowerRaisedEndo0, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]

set_option linter.unusedSectionVars false in

@[simp] lemma combinedLowerRaisedEndo0_self (g₁' : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁' g₁' x v = 0 := by
  rw [combinedLowerRaisedEndo0_apply, inverseMetricSharpFib_lowerFlatCLM, sub_self]

set_option linter.unusedSectionVars false in

lemma combinedLowerRaisedEndo0_eq_metricSharp_flatDiff
    (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    combinedLowerRaisedEndo0 (I := I) g₁ g₁' x v =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        ((g₁'.inner x v).toLinearMap - (g₁.inner x v).toLinearMap) := by
  rw [combinedLowerRaisedEndo0_apply, inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp]
  have hv : DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        (g₁.inner x v).toLinearMap = v := by
    rw [← inverseMetricSharpFib_lowerFlatCLM_eq_metricSharp (I := I) g₁ g₁ x v]
    exact inverseMetricSharpFib_lowerFlatCLM (I := I) g₁ x v
  have hsharp_sub : DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
        ((g₁'.inner x v).toLinearMap - (g₁.inner x v).toLinearMap) =
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
          (g₁'.inner x v).toLinearMap
        - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
          (g₁.inner x v).toLinearMap := by
    rw [DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def,
      DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_def, map_sub]
  rw [hsharp_sub, hv]

set_option linter.unusedSectionVars false in

theorem metricFlat_chartComponent_contMDiffOn_local (g : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (g.inner b (Y b)).toLinearMap
        (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  have h_total : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => (⟨b, g.inner b (Y b)
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ)))
      (trivializationAt E (TangentSpace I) γ).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id)
      g.contMDiff.contMDiffOn Y.contMDiff.contMDiffOn
      (DifferentialGeometry.Integral.Measure.chartBasisVec_contMDiffOn (I := I) γ j)
  have hbase_eq :
      (trivializationAt E (TangentSpace I) γ).baseSet = (chartAt H γ).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I) γ
  rw [hbase_eq] at h_total
  intro b hb
  have hpb := h_total b hb
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
  exact hpb.2

set_option linter.unusedSectionVars false in

theorem metricFlatDiff_chartComponent_contMDiffOn_local (g₁ g₁' : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (γ : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => ((g₁'.inner b (Y b)).toLinearMap - (g₁.inner b (Y b)).toLinearMap)
        (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) γ j b))
      (chartAt H γ).source := by
  have h0 := metricFlat_chartComponent_contMDiffOn_local (I := I) g₁' Y γ j
  have h1 := metricFlat_chartComponent_contMDiffOn_local (I := I) g₁ Y γ j
  refine (h0.sub h1).congr ?_
  intro b hb
  rw [LinearMap.sub_apply]

set_option backward.isDefEq.respectTransparency false in

theorem combinedLowerRaisedEndo0_contMDiff (g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x => combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)
  intro Y
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) b
        (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ b
          ((g₁'.inner b (Y b)).toLinearMap - (g₁.inner b (Y b)).toLinearMap))) := by
    apply DifferentialGeometry.Integral.DivergenceTheorem.metricSharp_contMDiff_total (I := I) g₁
    intro γ j
    exact metricFlatDiff_chartComponent_contMDiffOn_local (I := I) g₁ g₁' Y γ j
  refine hsharpY.congr (fun x => ?_)
  rw [combinedLowerRaisedEndo0_eq_metricSharp_flatDiff (I := I) g₁ g₁' x (Y x)]

set_option backward.isDefEq.respectTransparency false in

def lowerSlotInsert0Fib (x : M) (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Tensor0SSpace.ofModel
        ((Tensor0SSpace.toModel A).compContinuousLinearMap
          (fun i : Fin 2 => if i = 0 then Λ else ContinuousLinearMap.id ℝ E))
      map_add' := fun A A' => by
        apply Tensor0SSpace.toModel_injective (I := I)
        simp only [Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_add]
        ext m
        simp
      map_smul' := fun c A => by
        apply Tensor0SSpace.toModel_injective (I := I)
        simp only [Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_smul,
          RingHom.id_apply]
        ext m
        simp }

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in

lemma lowerSlotInsert0Fib_apply_eval (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (lowerSlotInsert0Fib (I := I) (M := M) x Λ A) m =
      Tensor0SSpace.toModel A (Function.update m 0 (Λ (m 0))) := by
  rw [lowerSlotInsert0Fib, LinearMap.coe_toContinuousLinearMap']
  change (Tensor0SSpace.toModel ((Tensor0SSpace.ofModel
      ((Tensor0SSpace.toModel A).compContinuousLinearMap
        (fun i : Fin 2 => if i = 0 then Λ else ContinuousLinearMap.id ℝ E))) :
      Tensor0SSpace 2 I x)) m = _
  rw [Tensor0SSpace.toModel_ofModel]
  have hfam : (fun i : Fin 2 =>
      (if i = 0 then Λ else ContinuousLinearMap.id ℝ E) (m i)) =
      Function.update m 0 (Λ (m 0)) := by
    funext i
    by_cases h : i = 0
    · subst h; simp
    · rw [if_neg h, Function.update_of_ne h]; rfl
  exact congrArg (fun t => Tensor0SSpace.toModel A t) hfam

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in

lemma lowerSlotInsert0Fib_curry (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace 2 I x) :
    lowerSlotInsert0Fib (I := I) (M := M) x Λ A =
      (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x).symm
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) A).comp Λ) := by
  have hcurry : Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
      (lowerSlotInsert0Fib (I := I) (M := M) x Λ A) =
      ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) A).comp Λ := by
    apply ContinuousLinearMap.ext
    intro v0
    apply Tensor0SSpace.toModel_injective (I := I)
    ext vt
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M),
      lowerSlotInsert0Fib_apply_eval, ContinuousLinearMap.comp_apply,
      TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)]
    congr 1
    rw [Fin.cons_zero, Fin.update_cons_zero]
  rw [← hcurry, ContinuousLinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in

def combinedLowerCoeff0Fib (g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  lowerSlotInsert0Fib (I := I) (M := M) x (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x)

set_option linter.unusedSectionVars false in

lemma combinedLowerCoeff0Fib_apply_eval (g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 2 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel (combinedLowerCoeff0Fib (I := I) g₁ g₁' x A) m =
      Tensor0SSpace.toModel A
        (Function.update m 0 (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x (m 0))) := by
  rw [combinedLowerCoeff0Fib, lowerSlotInsert0Fib_apply_eval]

set_option backward.isDefEq.respectTransparency false in

theorem combinedLowerCoeff0Fib_contMDiff (g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (Tensor0SBundle.TensorRSSpace.ofCLM (combinedLowerCoeff0Fib (I := I) g₁ g₁' x))) := by
  set φ : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun x => combinedLowerRaisedEndo0 (I := I) g₁ g₁' x with hφdef
  have hφ := combinedLowerRaisedEndo0_contMDiff (I := I) g₁ g₁'
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x => combinedLowerCoeff0Fib (I := I) g₁ g₁' x)
  intro Y
  have heq : (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
      (combinedLowerCoeff0Fib (I := I) g₁ g₁' x (Y x))) =
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
      ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x).symm
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)))) := by
    funext x
    rw [combinedLowerCoeff0Fib, lowerSlotInsert0Fib_curry]
  rw [heq]
  have hcurriedY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x))) :=
    fun x => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
      (fun y : M => Y y) x (Y.contMDiff x)
  have hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SBundle.Tensor0SSpace 1 I z) x
        (((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x))) := by
    apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
      (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
      (F₂ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z)
      (φ := fun x => ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x))
    intro Z
    have heqZ : (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)) (Z x))) =
        (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x) (φ x (Z x)))) := by
      funext x; rfl
    rw [heqZ]
    have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E
          (E := fun z : M => TangentSpace I z) x (φ x (Z x))) :=
      ContMDiff.clm_bundle_apply (b := id) hφ Z.contMDiff
    exact ContMDiff.clm_bundle_apply (b := id) hcurriedY hinner
  exact contMDiff_uncurriedSection_of_contMDiff_homSection (I := I) (M := M)
    (fun x : M => ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (Y x)).comp (φ x)) hG

noncomputable def combinedLowerCoeff0 (g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from combinedLowerCoeff0Fib (I := I) g₁ g₁' x)
      contMDiff_toFun := combinedLowerCoeff0Fib_contMDiff (I := I) g₁ g₁' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem combinedLowerCoeff0_toSection (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from combinedLowerCoeff0Fib (I := I) g₁ g₁' x) := rfl

set_option linter.unusedSectionVars false in

theorem combinedLowerCoeff0_appCc_eq
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁') W) x v =
      unitModel (I := I) (M := M) g₀ 2 W x
        (Function.update v 0 (combinedLowerRaisedEndo0 (I := I) g₁ g₁' x (v 0))) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (combinedLowerCoeff0 (I := I) (M := M) g₀ g₁ g₁').toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [combinedLowerCoeff0_toSection]
  rw [combinedLowerCoeff0Fib_apply_eval]
  rfl

set_option linter.unusedSectionVars false in

theorem connDiff_g1g1'_order_split (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Y x) (X x) =
      (inverseMetricSharpFib (I := I) g₁ x
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x)
          - inverseMetricSharpFib (I := I) g₁' x
              (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x))
        + inverseMetricSharpFib (I := I) g₁' x
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
              - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) := by
  rw [← connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x (Y x) (X x)]
  rw [connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁ X Y x,
      connDiff_eq_appCc_invGram_covGrad (I := I) (M := M) g₀ g₁' X Y x]
  rw [map_sub (inverseMetricSharpFib (I := I) g₁' x)]
  abel

set_option linter.unusedSectionVars false in

theorem order1CocycleLeg_flat_eq_explicit
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (S S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (hbil' : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S' b u w = g₁'.inner b u w - g₀.inner b u w)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (ζ : TangentSpace I x) :
    g₁'.inner x
        (inverseMetricSharpFib (I := I) g₁' x
          (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
            - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x)) ζ =
      (1 / 2 : ℝ) *
        (covGradEval (I := I) (M := M) g₀ (S - S')
            (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
            (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
            (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩) x
          + covGradEval (I := I) (M := M) g₀ (S - S')
              (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
              (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
              (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩) x
          - covGradEval (I := I) (M := M) g₀ (S - S')
              (⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩)
              (⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩)
              (⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩)
              x) := by
  classical
  set Xe : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (X x), smoothExtensionTangent_contMDiff (I := I) x (X x)⟩ with hXe
  set Ye : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x (Y x), smoothExtensionTangent_contMDiff (I := I) x (Y x)⟩ with hYe
  set Ze : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x ζ, smoothExtensionTangent_contMDiff (I := I) x ζ⟩ with hZe
  have hXex : Xe x = X x := smoothExtensionTangent_eq (I := I) x (X x)
  have hYex : Ye x = Y x := smoothExtensionTangent_eq (I := I) x (Y x)
  have hZex : Ze x = ζ := smoothExtensionTangent_eq (I := I) x ζ
  
  rw [inverseMetricSharpFib_inner (I := I) g₁' x
        (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
          - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ,
      cotangentToDualLinear_apply,
      show cotangentToDual (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x
              - koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ =
          cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁ X Y x) ζ
            - cotangentToDual (I := I) (koszulCovGradCovec (I := I) (M := M) g₀ g₁' X Y x) ζ from by
        rw [← cotangentToDualLinear_apply, ← cotangentToDualLinear_apply,
            ← cotangentToDualLinear_apply, map_sub, LinearMap.sub_apply]]
  
  rw [show ζ = Ze x from hZex.symm]
  rw [koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁ S hbil X Y Ze x,
      koszulCovGradCovec_dual_apply_covGrad (I := I) (M := M) g₀ g₁' S' hbil' X Y Ze x]
  
  have hcg : ∀ (P Q R : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      covGradEval (I := I) (M := M) g₀ S P Q R x
          - covGradEval (I := I) (M := M) g₀ S' P Q R x =
        covGradEval (I := I) (M := M) g₀ (S - S') P Q R x := by
    intro P Q R
    simp only [covGradEval]
    rw [covGrad_sub (I := I) (M := M) g₀ 0 2 S S', SmoothCcTensor.toSection_sub]
    rw [ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply,
        Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  
  have hval : ∀ (W : SmoothCcTensor g₀ 0 2)
      (P₁ P₂ Q₁ Q₂ R₁ R₂ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      P₁ x = P₂ x → Q₁ x = Q₂ x → R₁ x = R₂ x →
        covGradEval (I := I) (M := M) g₀ W P₁ Q₁ R₁ x =
          covGradEval (I := I) (M := M) g₀ W P₂ Q₂ R₂ x := by
    intro W P₁ P₂ Q₁ Q₂ R₁ R₂ hP hQ hR
    simp only [covGradEval, hP, hQ, hR]
  
  
  have eXY := (hcg X Y Ze).trans (hval (S - S') X Xe Y Ye Ze Ze hXex.symm hYex.symm rfl)
  have eYX := (hcg Y X Ze).trans (hval (S - S') Y Ye X Xe Ze Ze hYex.symm hXex.symm rfl)
  have eZXY := (hcg Ze X Y).trans (hval (S - S') Ze Ze X Xe Y Ye rfl hXex.symm hYex.symm)
  linarith [eXY, eYX, eZXY]

noncomputable def ricciArmSubleadingCoeff (g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
      - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁)
    - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁'
        - ricciArmPrincipalCoeffZ (I := I) (M := M) g₀ g₁')

set_option linter.unusedSectionVars false in

theorem ricciArmSubleadingCoeff_appCc_eq
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
          (ricciArmSubleadingCoeff (I := I) (M := M) g₀ g₁ g₁') W) x v =
      ((1 / 2 : ℝ) *
          ∑ k : Fin (Module.finrank ℝ E),
            (unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁ x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 0, v 1, (Module.finBasis ℝ E) k])
              + unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    ![v 1, v 0, (Module.finBasis ℝ E) k])
              - unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    (Fin.cons ((Module.finBasis ℝ E) k) v)))
        - (1 / 2 : ℝ) *
            ∑ k : Fin (Module.finrank ℝ E),
              (unitModel (I := I) (M := M) g₀ 4 W x
                  ![v 0, cometricLmodel (I := I) g₁ x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
                + unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, v 1, cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
                - unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁ x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), v 1])) -
      ((1 / 2 : ℝ) *
          ∑ k : Fin (Module.finrank ℝ E),
            (unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (cometricLmodel (I := I) g₁' x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
                  ![v 0, v 1, (Module.finBasis ℝ E) k])
              + unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    ![v 1, v 0, (Module.finBasis ℝ E) k])
              - unitModel (I := I) (M := M) g₀ 4 W x
                  (Fin.cons (cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)))
                    (Fin.cons ((Module.finBasis ℝ E) k) v)))
        - (1 / 2 : ℝ) *
            ∑ k : Fin (Module.finrank ℝ E),
              (unitModel (I := I) (M := M) g₀ 4 W x
                  ![v 0, cometricLmodel (I := I) g₁' x
                      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                        ((Module.finBasis ℝ E).cDualBasis k)), v 1, (Module.finBasis ℝ E) k]
                + unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, v 1, cometricLmodel (I := I) g₁' x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), (Module.finBasis ℝ E) k]
                - unitModel (I := I) (M := M) g₀ 4 W x
                    ![v 0, (Module.finBasis ℝ E) k, cometricLmodel (I := I) g₁' x
                        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                          ((Module.finBasis ℝ E).cDualBasis k)), v 1])) := by
  classical
  have hsub : ∀ (A B : SmoothCcTensor g₀ 4 2),
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (A - B) W) x v =
        unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 A W) x v -
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 B W) x v := by
    intro A B
    rw [show A - B = A + (-1 : ℝ) • B from by rw [neg_one_smul]; abel,
      appCc_add_left, appCc_smul_left, unitModel_add2, unitModel_smul,
      ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.smul_apply, neg_one_smul]
    rw [← sub_eq_add_neg]
  rw [ricciArmSubleadingCoeff, hsub, hsub, hsub,
    ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁ W x v,
    ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁ W x v,
    ricciArmPrincipalCoeff_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁' W x v,
    ricciArmPrincipalCoeffZ_appCc_eq_combinedTrace (I := I) (M := M) g₀ g₁' W x v]

noncomputable def ricciArmOrder0CurvCoeffFibSlot (g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 k x (ricEndoRaisedFib (I := I) g₁ x)

noncomputable def ricciArmOrder0CurvCoeffFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  ricciArmOrder0CurvCoeffFibSlot (I := I) (M := M) g₁ 0 x +
    ricciArmOrder0CurvCoeffFibSlot (I := I) (M := M) g₁ 1 x

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmOrder0CurvCoeffFibSlot_toModel (g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel
        (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x D) v =
      Tensor0SBundle.Tensor0SSpace.toModel D
        (Function.update v k (ricEndoRaisedFib (I := I) g₁ x (v k))) := by
  rw [ricciArmOrder0CurvCoeffFibSlot]
  exact slotInsertEndoFib_apply_eval (I := I) (M := M) 2 k x
    (ricEndoRaisedFib (I := I) g₁ x) D v

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmOrder0CurvCoeffFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SBundle.Tensor0SSpace.toModel (ricciArmOrder0CurvCoeffFib (I := I) g₁ x D) v =
      Tensor0SBundle.Tensor0SSpace.toModel D
          (Function.update v 0 (ricEndoRaisedFib (I := I) g₁ x (v 0))) +
        Tensor0SBundle.Tensor0SSpace.toModel D
          (Function.update v 1 (ricEndoRaisedFib (I := I) g₁ x (v 1))) := by
  rw [ricciArmOrder0CurvCoeffFib, ContinuousLinearMap.add_apply,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    ricciArmOrder0CurvCoeffFibSlot_toModel, ricciArmOrder0CurvCoeffFibSlot_toModel]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem ricciArmOrder0CurvCoeffFibSlot_contMDiff (g₁ : SmoothRiemannianMetric I M) (k : Fin 2) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x))) := by
  exact slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 k
    (fun x : M => ricEndoRaisedFib (I := I) g₁ x)
    (ricEndoRaisedFib_contMDiff (I := I) g₁)

noncomputable def ricciArmOrder0CurvCoeffSlot (g₀ g₁ : SmoothRiemannianMetric I M) (k : Fin 2) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x))
      contMDiff_toFun := ricciArmOrder0CurvCoeffFibSlot_contMDiff (I := I) g₁ k }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmOrder0CurvCoeffSlot_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (k : Fin 2) (x : M) :
    (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ k).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ k x)) := rfl

noncomputable def ricciArmOrder0CurvCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0 +
    ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmOrder0CurvCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)) := by
  rw [ricciArmOrder0CurvCoeff, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply, ricciArmOrder0CurvCoeffSlot_toSection, ricciArmOrder0CurvCoeffSlot_toSection]
  rfl

set_option linter.unusedSectionVars false in

theorem ricciArmOrder0CurvCoeff_appCc_eq_curvatureAction
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) W) x v =
      unitModel (I := I) (M := M) g₀ 2 W x
          (Function.update v 0 (ricEndoRaisedFib (I := I) g₁ x (v 0))) +
        unitModel (I := I) (M := M) g₀ 2 W x
          (Function.update v 1 (ricEndoRaisedFib (I := I) g₁ x (v 1))) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0CurvCoeff_toSection]
  rw [show (show Tensor0SBundle.Tensor0SSpace 2 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (show Tensor0SBundle.TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)))
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) =
      ricciArmOrder0CurvCoeffFib (I := I) g₁ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0CurvCoeffFib_toModel]
  rfl

def riemannKernelBilin (g₁ : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => (g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q))
      map_add' := fun v0 v0' => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_add v0 v0',
          ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, map_add]
      map_smul' := fun c v0 => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_smul c v0,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul,
          RingHom.id_apply] }

@[simp] theorem riemannKernelBilin_apply (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    riemannKernelBilin (I := I) g₁ x p q v0 v1 =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [riemannKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

def riemannSummandFib (g₁ : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (riemannKernelBilin (I := I) g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

@[simp] theorem riemannSummandFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannSummandFib (I := I) g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) p q) (v 1) := by
  rw [riemannSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rfl

def riemannBiContrFibFixedFrame (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    riemannSummandFib (I := I) g₁ x (B a x) (B b x)

theorem riemannBiContrFibFixedFrame_toModel (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannBiContrFibFixedFrame (I := I) g₁ B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (B a x) (B b x)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [riemannBiContrFibFixedFrame, ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, riemannSummandFib_toModel]
  ring

def innerPairBilin (x : M) (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X : TangentSpace I x) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => (K X Y) • (Dd X)
      map_add' := fun Y Y' => by rw [map_add, add_smul]
      map_smul' := fun c Y => by rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_smul] }

theorem innerPairBilin_apply (x : M) (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Y' : TangentSpace I x) :
    innerPairBilin (I := I) x K Dd X Y Y' = K X Y * Dd X Y' := by
  rw [innerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

def outerPairBilin (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g x x k l * K X (chartModelBasis E k)) •
          (ContinuousLinearMap.flip Dd (chartModelBasis E l))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

theorem outerPairBilin_apply (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    outerPairBilin (I := I) g x K Dd X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (K X (chartModelBasis E k) * Dd X' (chartModelBasis E l)) := by
  rw [outerPairBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

theorem double_frame_bilin_trace_eq_fixed
    (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1:ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g x x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g x x k l *
          (K (chartModelBasis E m) (chartModelBasis E k) *
            Dd (chartModelBasis E n) (chartModelBasis E l))) := by
  classical
  
  have hinner : ∀ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      outerPairBilin (I := I) g x K Dd (B a) (B a) := by
    intro a
    rw [outerPairBilin_apply]
    have h := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
      (innerPairBilin (I := I) x K Dd (B a)) B hB
    simp only [innerPairBilin_apply] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  
  have hout := orthonormal_basis_bilin_trace (I := I) (M := M) g (x := x)
    (outerPairBilin (I := I) g x K Dd) B hB
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [outerPairBilin_apply]

theorem double_frame_bilin_trace_indep
    (g : SmoothRiemannianMetric I M) (x : M)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B C : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1:ℝ) else 0)
    (hC : ∀ i j, g.inner x (C i) (C j) = if i = j then (1:ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ a, ∑ b, K (C a) (C b) * Dd (C a) (C b) := by
  rw [double_frame_bilin_trace_eq_fixed (I := I) g x K Dd B hB,
    double_frame_bilin_trace_eq_fixed (I := I) g x K Dd C hC]

theorem contMDiff_bilinSection_of_chartScalar
    (Hb : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hscalar : ∀ (x₀ : M) (σ : Fin 2 → Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Hb x (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (bilinFormToModel (TangentSpace I x) (Hb x)))) := by
  classical
  let d := Module.finrank ℝ E
  let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b
    (fun x => Tensor0SSpace.ofModel (I := I) (x := x)
      (bilinFormToModel (TangentSpace I x) (Hb x)))).mpr fun σ x₀ => ?_
  have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Hb x (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x))
      (chartAt H x₀).source := hscalar x₀ σ
  have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
    (chartAt H x₀).open_source.mem_nhds hx₀_src
  refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
  have h_base_nhd : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
  filter_upwards [h_base_nhd] with x hx
  rw [continuousMultilinearMap_basis_repr]
  change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel (I := I) (x := x) (bilinFormToModel (TangentSpace I x) (Hb x)))
      (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x) (Hb x)
    (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j)))

theorem kernelScalar_global (g₁ : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g₁) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) g₁) hY hp hq
  have hcongr : (fun x : M => g₁.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => g₁.inner x (riemannSec (LeviCivita (I := I) g₁) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₁
    ⟨fun b => riemannSec (LeviCivita (I := I) g₁) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

theorem riemannKernelBilin_homSection_contMDiff (g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (riemannKernelBilin (I := I) g₁ x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => riemannKernelBilin (I := I) g₁ x (p x) (q x))
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => riemannKernelBilin (I := I) g₁ x (p x) (q x) (Y x))
  intro W
  have h_scalar := kernelScalar_global (I := I) g₁ Y.contMDiff W.contMDiff hp hq
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change riemannKernelBilin (I := I) g₁ y (p y) (q y) (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [riemannKernelBilin_apply]
  rfl

theorem contMDiff_bilinSection_of_homSection
    (Hb : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hHb : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x (Hb x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (Tensor0SSpace.ofModel (I := I) (x := x)
          (bilinFormToModel (TangentSpace I x) (Hb x)))) := by
  classical
  refine contMDiff_bilinSection_of_chartScalar (I := I) Hb (fun x₀ σ => ?_)
  have hcf_0 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => chartFrameVec (I := I) x₀ (σ 0) b))
      (trivializationAt E (TangentSpace I) x₀).baseSet := fun x hx =>
    chartBasisVec_contMDiffOn (I := I) x₀ (σ 0) x hx
  have hcf_1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => chartFrameVec (I := I) x₀ (σ 1) b))
      (trivializationAt E (TangentSpace I) x₀).baseSet := fun x hx =>
    chartBasisVec_contMDiffOn (I := I) x₀ (σ 1) x hx
  have happ1 := ContMDiffOn.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun z : M => TangentSpace I z →L[ℝ] ℝ)
    (b := id) hHb.contMDiffOn hcf_0
  have happ := ContMDiffOn.clm_bundle_apply (F₁ := E) (F₂ := ℝ)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun _ : M => ℝ)
    (b := id) happ1 hcf_1
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

theorem riemannBiContrFibFixedFrame_apply_section_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (riemannBiContrFibFixedFrame (I := I) g₁ B x (Y x))) := by
  classical
  
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (riemannSummandFib (I := I) g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => riemannKernelBilin (I := I) g₁ x (B a x) (B b x))
      (riemannKernelBilin_homSection_contMDiff (I := I) g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x) (riemannKernelBilin (I := I) g₁ x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => riemannSummandFib (I := I) g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [riemannBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

theorem riemannBiContrFibFixedFrame_contMDiff (g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFibFixedFrame (I := I) g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => riemannBiContrFibFixedFrame (I := I) g₁ B x)
  intro Y
  exact riemannBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₁ B hB Y

def frameRiemannKernel (g₁ : SmoothRiemannianMetric I M) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₁.inner x).flip v1 |>.comp
        ((riemannOp (LeviCivita (I := I) g₁) x v0 p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (LeviCivita (I := I) g₁) x v0).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (LeviCivita (I := I) g₁) x v0).map_smul c p, map_smul] }

theorem frameRiemannKernel_apply (g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameRiemannKernel (I := I) g₁ x v0 v1 p q =
      g₁.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [frameRiemannKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

def riemannBiContrFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x) x

theorem riemannBiContrFib_eq_fixedFrame_on_nbhd (g₁ : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    riemannBiContrFib (I := I) g₁ y =
      riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel,
    riemannBiContrFibFixedFrame_toModel]
  
  congr 1
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner y (riemannOp (LeviCivita (I := I) g₁) y (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRiemannKernel (I := I) g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRiemannKernel_apply (I := I) g₁ y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameRiemannKernel (I := I) g₁ y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem riemannBiContrFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannBiContrFibFixedFrame (I := I) g₁
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    riemannBiContrFibFixedFrame_contMDiff (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (riemannBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₁ x₀ hy))

def ricciArmOrder0RiemannCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
      contMDiff_toFun := riemannBiContrFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem ricciArmOrder0RiemannCoeffField_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) :=
  rfl

theorem exists_ricciArmOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ R_Rm : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R_Rm W) x v =
          2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₁.inner x
                (riemannOp (LeviCivita (I := I) g₁) x (v 0)
                  (smoothOrthoFrame (I := I) g₁ x a x)
                  (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
              unitModel (I := I) (M := M) g₀ 2 W x
                (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                  else smoothOrthoFrame (I := I) g₁ x b x) :=
  by
  classical
  refine ⟨ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁, fun W x v => ?_⟩
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0RiemannCoeffField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      riemannBiContrFib (I := I) g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

noncomputable def ricciArmOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₁

@[simp] theorem ricciArmOrder0RiemannCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) :=
  rfl

set_option linter.unusedSectionVars false in

theorem ricciArmOrder0RiemannCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) W) x v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x
            (riemannOp (LeviCivita (I := I) g₁) x (v 0)
              (smoothOrthoFrame (I := I) g₁ x a x)
              (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
              else smoothOrthoFrame (I := I) g₁ x b x) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0RiemannCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      riemannBiContrFib (I := I) g₁ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

noncomputable def symmAbsorbedPrincipalCoeffPure (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 4 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 2
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2))

set_option linter.unusedSectionVars false in

theorem symmAbsorbedPrincipalCoeffPure_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (symmAbsorbedPrincipalCoeffPure (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 2 S
    (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 2)) x v

noncomputable def symmAbsorbedOrder0CurvCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0CurvCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

noncomputable def symmAbsorbedOrder0RiemannCoeff (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0RiemannCoeff_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v

noncomputable def deTurckLieCovDerivA (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
    - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        ((LeviCivita (I := I) g₁).toFun (fun b => Y b) x (X x)) (Z x)
    - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x)
        ((LeviCivita (I := I) g₁).toFun (fun b => Z b) x (X x))

noncomputable def deTurckLieCovDerivW (g₁ g_bg : SmoothRiemannianMetric I M)
    (X : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b) x (X x)

theorem connDiffOp_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)
    (φ := fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b)
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun z : M => TangentSpace I z)
    (φ := fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b))
  intro Z
  exact PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg Y.contMDiff Z.contMDiff

theorem connDiffOp_mdiffAt (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b)) x :=
  (connDiffOp_homSection_contMDiff (I := I) g₁ g_bg).contMDiffAt.mdifferentiableAt (by simp)

theorem connDiff_pairing_mdiffAt (g₁ g_bg : SmoothRiemannianMetric I M)
    {Y Z : Π b : M, TangentSpace I b} {x : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Y b)) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Z b)) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b))) x := by
  have h1 : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun b => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) b
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b))) x :=
    MDifferentiableAt.clm_bundle_apply
      (F₁ := E) (F₂ := E →L[ℝ] E)
      (E₁ := fun z : M => TangentSpace I z)
      (E₂ := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)
      (b := fun b : M => b)
      (ϕ := fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b) (v := fun b => Y b)
      (connDiffOp_mdiffAt (I := I) g₁ g_bg x) hY
  exact MDifferentiableAt.clm_bundle_apply
    (F₁ := E) (F₂ := E)
    (E₁ := fun z : M => TangentSpace I z) (E₂ := fun z : M => TangentSpace I z)
    (b := fun b : M => b)
    (ϕ := fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b)) (v := fun b => Z b) h1 hZ

theorem deTurckLieCovDerivA_tensorialAt_Y (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Z : Π b : M, TangentSpace I b) (x : M)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Z b)) x) :
    TensorialAt I E
      (fun Y : Π b : M, TangentSpace I b =>
        deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x) x where
  smul {f Y} hf hY := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    set G : Π b : M, TangentSpace I b :=
      fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) with hG_def
    have hG : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (G b)) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hfYG : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((f • Y) b) (Z b)) = f • G := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (f b • Y b) (Z b) = f b • G b
      rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((f • Y) b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun (f • Y) x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((f • Y) x) (cov.toFun Z x (X x)) =
      f x • (cov.toFun G x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x)))
    rw [hfYG]
    rw [hcovOn.leibniz hG hf (Set.mem_univ x)]
    rw [hcovOn.leibniz hY hf (Set.mem_univ x)]
    have hfY_x : (f • Y) x = f x • Y x := rfl
    rw [hfY_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, hG_def]
    rw [smul_sub, smul_sub]
    abel
  add {Y Y'} hY hY' := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    have hGY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hGY' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY' hZ
    have hadd_fun : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((Y + Y') b) (Z b)) =
        (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) +
          (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b)) := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b + Y' b) (Z b) =
        PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) +
          PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b)
      rw [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b ((Y + Y') b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun (Y + Y') x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x ((Y + Y') x) (cov.toFun Z x (X x)) =
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x))) +
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y' b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y' x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y' x) (cov.toFun Z x (X x)))
    rw [hadd_fun, hcovOn.add hGY hGY' (Set.mem_univ x)]
    rw [hcovOn.add hY hY' (Set.mem_univ x)]
    have hYY'_x : (Y + Y') x = Y x + Y' x := rfl
    rw [hYY'_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

theorem deTurckLieCovDerivA_tensorialAt_Z (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (x : M)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Y b)) x) :
    TensorialAt I E
      (fun Z : Π b : M, TangentSpace I b =>
        deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x) x where
  smul {f Z} hf hZ := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    set G : Π b : M, TangentSpace I b :=
      fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) with hG_def
    have hG : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b (G b)) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hfZG : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((f • Z) b)) = f • G := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (f b • Z b) = f b • G b
      rw [ContinuousLinearMap.map_smul]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((f • Z) b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) ((f • Z) x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun (f • Z) x (X x)) =
      f x • (cov.toFun G x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x)))
    rw [hfZG]
    rw [hcovOn.leibniz hG hf (Set.mem_univ x)]
    rw [hcovOn.leibniz hZ hf (Set.mem_univ x)]
    have hfZ_x : (f • Z) x = f x • Z x := rfl
    rw [hfZ_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, hG_def]
    rw [smul_sub, smul_sub]
    abel
  add {Z Z'} hZ hZ' := by
    classical
    set cov := LeviCivita (I := I) g₁ with hcov_def
    have hcovOn := cov.isCovariantDerivativeOnUniv
    have hGZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ
    have hGZ' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b => TotalSpace.mk' E (E := TangentSpace I) b
          (PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b))) x :=
      connDiff_pairing_mdiffAt (I := I) g₁ g_bg hY hZ'
    have hadd_fun : (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((Z + Z') b)) =
        (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) +
          (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b)) := by
      funext b
      change PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b + Z' b) =
        PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b) +
          PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b)
      rw [ContinuousLinearMap.map_add]
    change cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) ((Z + Z') b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) ((Z + Z') x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun (Z + Z') x (X x)) =
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z x (X x))) +
      (cov.toFun (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (Y b) (Z' b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (cov.toFun Y x (X x)) (Z' x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (Y x) (cov.toFun Z' x (X x)))
    rw [hadd_fun, hcovOn.add hGZ hGZ' (Set.mem_univ x)]
    rw [hcovOn.add hZ hZ' (Set.mem_univ x)]
    have hZZ'_x : (Z + Z') x = Z x + Z' x := rfl
    rw [hZZ'_x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

noncomputable def dLaCovKernel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  TensorialAt.mkHom₂ (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (A := TangentSpace I x)
    (fun Y Z => deTurckLieCovDerivA (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x) x
    (fun Z hZ => deTurckLieCovDerivA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (fun Y hY => deTurckLieCovDerivA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)

theorem dLaCovKernel_apply_extend (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x v0 p q =
      deTurckLieCovDerivA (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x v0)
        (smoothExtensionTangent (I := I) x p)
        (smoothExtensionTangent (I := I) x q) x := by
  have hp := smoothExtensionTangent_mdiff (I := I) x p x
  have hq := smoothExtensionTangent_mdiff (I := I) x q x
  have h := TensorialAt.mkHom₂_apply (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (Φ := fun Y Z => deTurckLieCovDerivA (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x)
    (hΦ₁ := fun Z hZ => deTurckLieCovDerivA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (hΦ₂ := fun Y hY => deTurckLieCovDerivA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)
    (σ := smoothExtensionTangent (I := I) x p)
    (τ := smoothExtensionTangent (I := I) x q) hp hq
  rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq] at h
  exact h

theorem dLaCovKernel_apply_field (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) (V_field W_field : Π b : M, TangentSpace I b)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V_field b)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (W_field b)) x) :
    dLaCovKernel (I := I) g₁ g_bg x v0 (V_field x) (W_field x) =
      deTurckLieCovDerivA (I := I) g₁ g_bg
        (smoothExtensionTangent (I := I) x v0) V_field W_field x :=
  TensorialAt.mkHom₂_apply (F := E) (F' := E)
    (V := (TangentSpace I : M → Type _)) (V' := (TangentSpace I : M → Type _))
    (Φ := fun Y Z => deTurckLieCovDerivA (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y Z x)
    (hΦ₁ := fun Z hZ => deTurckLieCovDerivA_tensorialAt_Y (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Z x hZ)
    (hΦ₂ := fun Y hY => deTurckLieCovDerivA_tensorialAt_Z (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) Y x hY)
    (σ := V_field) (τ := W_field) hV hW

theorem deTurckLieCovDerivA_X_congr (g₁ g_bg : SmoothRiemannianMetric I M)
    (X X' Y Z : Π b : M, TangentSpace I b) (x : M) (hXX : X x = X' x) :
    deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x =
      deTurckLieCovDerivA (I := I) g₁ g_bg X' Y Z x := by
  rw [deTurckLieCovDerivA, deTurckLieCovDerivA, hXX]

theorem deTurckLieCovDerivA_X_add (g₁ g_bg : SmoothRiemannianMetric I M)
    (X X' Y Z : Π b : M, TangentSpace I b) (x : M) :
    deTurckLieCovDerivA (I := I) g₁ g_bg (X + X') Y Z x =
      deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x +
        deTurckLieCovDerivA (I := I) g₁ g_bg X' Y Z x := by
  have h : (X + X') x = X x + X' x := rfl
  unfold deTurckLieCovDerivA
  rw [h]
  simp only [map_add, ContinuousLinearMap.add_apply]
  abel

theorem deTurckLieCovDerivA_X_smul (g₁ g_bg : SmoothRiemannianMetric I M)
    (X Y Z cX : Π b : M, TangentSpace I b) (c : ℝ) (x : M) (hcX : cX x = c • X x) :
    deTurckLieCovDerivA (I := I) g₁ g_bg cX Y Z x =
      c • deTurckLieCovDerivA (I := I) g₁ g_bg X Y Z x := by
  unfold deTurckLieCovDerivA
  rw [hcX]
  simp only [map_smul, ContinuousLinearMap.smul_apply]
  rw [smul_sub, smul_sub]

theorem dLaCovKernel_add_left (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 v0' p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x (v0 + v0') p q =
      dLaCovKernel (I := I) g₁ g_bg x v0 p q + dLaCovKernel (I := I) g₁ g_bg x v0' p q := by
  rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend, dLaCovKernel_apply_extend]
  rw [deTurckLieCovDerivA_X_congr (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x (v0 + v0'))
      (smoothExtensionTangent (I := I) x v0 + smoothExtensionTangent (I := I) x v0')
      _ _ x (by
        change smoothExtensionTangent (I := I) x (v0 + v0') x =
          smoothExtensionTangent (I := I) x v0 x + smoothExtensionTangent (I := I) x v0' x
        rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq, smoothExtensionTangent_eq])]
  rw [deTurckLieCovDerivA_X_add]

theorem dLaCovKernel_smul_left (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (v0 p q : TangentSpace I x) :
    dLaCovKernel (I := I) g₁ g_bg x (c • v0) p q = c • dLaCovKernel (I := I) g₁ g_bg x v0 p q := by
  rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend]
  rw [deTurckLieCovDerivA_X_smul (I := I) g₁ g_bg
      (smoothExtensionTangent (I := I) x v0) _ _
      (smoothExtensionTangent (I := I) x (c • v0)) c x (by
        rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq])]

def dLaKernelBilin (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q)
      map_add' := fun v0 v0' => by
        rw [dLaCovKernel_add_left, map_add]
      map_smul' := fun c v0 => by
        rw [dLaCovKernel_smul_left, map_smul, RingHom.id_apply] }

@[simp] theorem dLaKernelBilin_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    dLaKernelBilin (I := I) g₁ g_bg x p q v0 v1 =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q) v1 := by
  rw [dLaKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

def dLaKernelBilinSym (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  dLaKernelBilin (I := I) g₁ g_bg x p q +
    ContinuousLinearMap.flip (dLaKernelBilin (I := I) g₁ g_bg x p q)

@[simp] theorem dLaKernelBilinSym_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    dLaKernelBilinSym (I := I) g₁ g_bg x p q v0 v1 =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q) v1 +
        g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v1 p q) v0 := by
  rw [dLaKernelBilinSym, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.flip_apply, dLaKernelBilin_apply, dLaKernelBilin_apply]

def dLaSummandFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (dLaKernelBilinSym (I := I) g₁ g_bg x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

@[simp] theorem dLaSummandFib_toModel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (dLaSummandFib (I := I) g₁ g_bg x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        (g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 0) p q) (v 1) +
          g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 1) p q) (v 0)) := by
  rw [dLaSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rw [dLaKernelBilinSym]
  rfl

def dLaBiContrFibFixedFrame (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (-1 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    dLaSummandFib (I := I) g₁ g_bg x (B a x) (B b x)

theorem dLaBiContrFibFixedFrame_toModel (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x D) v =
      (-1 : ℝ) * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 0) (B a x) (B b x)) (v 1) +
          g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x (v 1) (B a x) (B b x)) (v 0)) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [dLaBiContrFibFixedFrame, ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, dLaSummandFib_toModel]
  ring

theorem deTurckLieCovDerivA_section_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (V0 p q : Π b : M, TangentSpace I b)
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q b)) := by
  have hcd_pq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun y => PDE.DeTurck.connDiff (I := I) g₁ g_bg y (p y) (q y))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg hp hq
  have hterm1 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0
        (fun y => PDE.DeTurck.connDiff (I := I) g₁ g_bg y (p y) (q y)) b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hcd_pq
  have hcovV0p : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0 p b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hp
  have hcovV0q : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => covApply (LeviCivita (I := I) g₁) V0 q b)) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g₁) (X := V0) hV0 hq
  have hterm2 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b
        (covApply (LeviCivita (I := I) g₁) V0 p b) (q b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg hcovV0p hq
  have hterm3 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (p b)
        (covApply (LeviCivita (I := I) g₁) V0 q b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g_bg hp hcovV0q
  refine ((hterm1.sub_section hterm2).sub_section hterm3).congr (fun b => ?_)
  rfl

theorem dLaCovKernel_apply_field3 (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (V0 V_field W_field : Π b : M, TangentSpace I b)
    (_hV0 : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V0 b)) x)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (V_field b)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (W_field b)) x) :
    dLaCovKernel (I := I) g₁ g_bg x (V0 x) (V_field x) (W_field x) =
      deTurckLieCovDerivA (I := I) g₁ g_bg V0 V_field W_field x := by
  rw [dLaCovKernel_apply_field (I := I) g₁ g_bg x (V0 x) V_field W_field hV hW]
  exact deTurckLieCovDerivA_X_congr (I := I) g₁ g_bg
    (smoothExtensionTangent (I := I) x (V0 x)) V0 V_field W_field x
    (smoothExtensionTangent_eq (I := I) x (V0 x))

theorem dLaKernelScalar_global (g₁ g_bg : SmoothRiemannianMetric I M)
    {V0 W p q : Π b : M, TangentSpace I b}
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₁.inner x
        (dLaCovKernel (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) := by
  classical
  have hAsec := deTurckLieCovDerivA_section_contMDiff (I := I) g₁ g_bg V0 p q hV0 hp hq
  have hcongr : (fun x : M => g₁.inner x
        (dLaCovKernel (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) =
      (fun x : M => g₁.inner x (deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q x) (W x)) := by
    funext x
    rw [dLaCovKernel_apply_field3 (I := I) g₁ g_bg x V0 p q
      (hV0.contMDiffAt.mdifferentiableAt (by simp))
      (hp.contMDiffAt.mdifferentiableAt (by simp))
      (hq.contMDiffAt.mdifferentiableAt (by simp))]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₁
    ⟨fun b => deTurckLieCovDerivA (I := I) g₁ g_bg V0 p q b, hAsec⟩ ⟨fun b => W b, hW⟩

theorem dLaKernelBilinSym_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (dLaKernelBilinSym (I := I) g₁ g_bg x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => dLaKernelBilinSym (I := I) g₁ g_bg x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => dLaKernelBilinSym (I := I) g₁ g_bg x (p x) (q x) (V0 x))
  intro W
  have h_scalar0 := dLaKernelScalar_global (I := I) g₁ g_bg V0.contMDiff W.contMDiff hp hq
  have h_scalar1 := dLaKernelScalar_global (I := I) g₁ g_bg W.contMDiff V0.contMDiff hp hq
  have h_scalar := h_scalar0.add h_scalar1
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change dLaKernelBilinSym (I := I) g₁ g_bg y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [dLaKernelBilinSym_apply]
  rfl

theorem dLaBiContrFibFixedFrame_apply_section_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (dLaSummandFib (I := I) g₁ g_bg x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => dLaKernelBilinSym (I := I) g₁ g_bg x (B a x) (B b x))
      (dLaKernelBilinSym_homSection_contMDiff (I := I) g₁ g_bg (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x) (dLaKernelBilinSym (I := I) g₁ g_bg x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => dLaSummandFib (I := I) g₁ g_bg x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (-1 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [dLaBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

theorem dLaBiContrFibFixedFrame_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => dLaBiContrFibFixedFrame (I := I) g₁ g_bg B x)
  intro Y
  exact dLaBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₁ g_bg B hB Y

def frameDLaKernel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        ContinuousLinearMap.comp ((g₁.inner x).flip v1) (dLaCovKernel (I := I) g₁ g_bg x v0 p) +
        ContinuousLinearMap.comp ((g₁.inner x).flip v0) (dLaCovKernel (I := I) g₁ g_bg x v1 p)
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
          (dLaCovKernel (I := I) g₁ g_bg x v0).map_add p p',
          (dLaCovKernel (I := I) g₁ g_bg x v1).map_add p p', ContinuousLinearMap.add_apply,
          map_add]
        ring
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          RingHom.id_apply, (dLaCovKernel (I := I) g₁ g_bg x v0).map_smul c p,
          (dLaCovKernel (I := I) g₁ g_bg x v1).map_smul c p, map_smul,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring }

theorem frameDLaKernel_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameDLaKernel (I := I) g₁ g_bg x v0 v1 p q =
      g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v0 p q) v1 +
        g₁.inner x (dLaCovKernel (I := I) g₁ g_bg x v1 p q) v0 := by
  rw [frameDLaKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]

def dLaBiContrFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  dLaBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x

theorem dLaBiContrFib_eq_fixedFrame_on_nbhd (g₁ g_bg : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    dLaBiContrFib (I := I) g₁ g_bg y =
      dLaBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel, dLaBiContrFibFixedFrame_toModel]
  congr 1
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (g₁.inner y (dLaCovKernel (I := I) g₁ g_bg y (v 0) (Bf a) (Bf b)) (v 1) +
          g₁.inner y (dLaCovKernel (I := I) g₁ g_bg y (v 1) (Bf a) (Bf b)) (v 0)) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameDLaKernel (I := I) g₁ g_bg y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameDLaKernel_apply (I := I) g₁ g_bg y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₁ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₁ y
    (frameDLaKernel (I := I) g₁ g_bg y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₁ y a y)
    (fun a => smoothOrthoFrame (I := I) g₁ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)

theorem dLaBiContrFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (dLaBiContrFibFixedFrame (I := I) g₁ g_bg
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    dLaBiContrFibFixedFrame_contMDiff (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (dLaBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₁ g_bg x₀ hy))

def deTurckLieWEndo (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (LeviCivita (I := I) g₁).toFun
    (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b) x

theorem deTurckLieWEndo_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    deTurckLieWEndo (I := I) g₁ g_bg x v =
      deTurckLieCovDerivW (I := I) g₁ g_bg (smoothExtensionTangent (I := I) x v) x := by
  rw [deTurckLieWEndo, deTurckLieCovDerivW, smoothExtensionTangent_eq]

theorem deTurckLieWEndo_homSection_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (deTurckLieWEndo (I := I) g₁ g_bg x)) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x : M => deTurckLieWEndo (I := I) g₁ g_bg x)
  intro Y
  have hdvf : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg
        : Π b : M, TangentSpace I b) b)) :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff
  have hcov := covApply_contMDiff (cov := LeviCivita (I := I) g₁)
    (X := fun b => Y b)
    (T := fun b : M => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg
      : Π b : M, TangentSpace I b) b)
    Y.contMDiff hdvf
  exact hcov

def deTurckLieDLbFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  slotInsertEndoFib (I := I) (M := M) 2 0 x (deTurckLieWEndo (I := I) g₁ g_bg x) +
    slotInsertEndoFib (I := I) (M := M) 2 1 x (deTurckLieWEndo (I := I) g₁ g_bg x)

theorem deTurckLieDLbFib_toModel (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (deTurckLieDLbFib (I := I) g₁ g_bg x D) v =
      Tensor0SSpace.toModel D
          (Function.update v 0 (deTurckLieWEndo (I := I) g₁ g_bg x (v 0))) +
        Tensor0SSpace.toModel D
          (Function.update v 1 (deTurckLieWEndo (I := I) g₁ g_bg x (v 1))) := by
  rw [deTurckLieDLbFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]

theorem deTurckLieDLbFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x))) := by
  classical
  have h0 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 0
    (fun x => deTurckLieWEndo (I := I) g₁ g_bg x)
    (deTurckLieWEndo_homSection_contMDiff (I := I) g₁ g_bg)
  have h1 := slotInsertEndoFib_contMDiff (I := I) (M := M) g₁ 2 1
    (fun x => deTurckLieWEndo (I := I) g₁ g_bg x)
    (deTurckLieWEndo_homSection_contMDiff (I := I) g₁ g_bg)
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
        (deTurckLieWEndo (I := I) g₁ g_bg x))))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x
        (deTurckLieWEndo (I := I) g₁ g_bg x))))
    h0 h1
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [deTurckLieDLbFib]
  rfl

def deTurckLieFib (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  dLaBiContrFib (I := I) g₁ g_bg x + deTurckLieDLbFib (I := I) g₁ g_bg x

theorem deTurckLieFib_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x))) := by
  classical
  have hadd := ContMDiff.add_section
    (s := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x)))
    (t := fun x => (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x)))
    (dLaBiContrFib_contMDiff (I := I) g₁ g_bg)
    (deTurckLieDLbFib_contMDiff (I := I) g₁ g_bg)
  refine hadd.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) x) ?_
  rw [deTurckLieFib]
  rfl

def deTurckLieCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem deTurckLieCoeffField_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)) :=
  rfl

theorem exists_ricciArmOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ∃ R_Lie : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R_Lie W) x v =
          (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
              unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                    else smoothOrthoFrame (I := I) g₁ x b x) *
                (g₁.inner x
                    (deTurckLieCovDerivA (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 0))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
                  + g₁.inner x
                    (deTurckLieCovDerivA (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 1))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                      (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)))
            + (unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then
                    deTurckLieCovDerivW (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 0)) x
                    else v 1)
                + unitModel (I := I) (M := M) g₀ 2 W x
                  (fun j => if j = 0 then v 0
                    else deTurckLieCovDerivW (I := I) g₁ g_bg
                      (smoothExtensionTangent (I := I) x (v 1)) x)) := by
  classical
  refine ⟨deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg, fun W x v => ?_⟩
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [deTurckLieCoeffField_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      deTurckLieFib (I := I) g₁ g_bg x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  
  set D : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hD_def
  rw [deTurckLieFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]
  congr 1
  · change Tensor0SSpace.toModel (dLaBiContrFib (I := I) g₁ g_bg x D) v = _
    rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel, neg_one_mul]
    rw [show (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0))) =
        - ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)) from rfl]
    refine congrArg (fun t => -t) ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend, mul_comm]
    congr 1
    rw [unitModel]
    congr 1
    funext j
    fin_cases j <;> simp
  · change Tensor0SSpace.toModel (deTurckLieDLbFib (I := I) g₁ g_bg x D) v = _
    rw [deTurckLieDLbFib_toModel]
    rw [deTurckLieWEndo_apply, deTurckLieWEndo_apply]
    congr 1
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp

noncomputable def ricciArmOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg

@[simp] theorem ricciArmOrder0DeTurckLieCoeff_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)) :=
  rfl

set_option linter.unusedSectionVars false in

theorem ricciArmOrder0DeTurckLieCoeff_appCc_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg) W)
        x v =
      (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)))
        + (unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then
                deTurckLieCovDerivW (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0)) x
                else v 1)
            + unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then v 0
                else deTurckLieCovDerivW (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1)) x)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder0DeTurckLieCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (deTurckLieFib (I := I) g₁ g_bg x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      deTurckLieFib (I := I) g₁ g_bg x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  set D : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hD_def
  rw [deTurckLieFib, ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]
  congr 1
  · change Tensor0SSpace.toModel (dLaBiContrFib (I := I) g₁ g_bg x D) v = _
    rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel, neg_one_mul]
    rw [show (- ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0))) =
        - ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 2 W x
              (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a x
                else smoothOrthoFrame (I := I) g₁ x b x) *
            (g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 0))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 1)
              + g₁.inner x
                (deTurckLieCovDerivA (I := I) g₁ g_bg
                  (smoothExtensionTangent (I := I) x (v 1))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
                  (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) x) (v 0)) from rfl]
    refine congrArg (fun t => -t) ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [dLaCovKernel_apply_extend, dLaCovKernel_apply_extend, mul_comm]
    congr 1
    rw [unitModel]
    congr 1
    funext j
    fin_cases j <;> simp
  · change Tensor0SSpace.toModel (deTurckLieDLbFib (I := I) g₁ g_bg x D) v = _
    rw [deTurckLieDLbFib_toModel]
    rw [deTurckLieWEndo_apply, deTurckLieWEndo_apply]
    congr 1
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp
    · rw [unitModel]
      congr 1
      funext j
      fin_cases j <;> simp

noncomputable def symmAbsorbedOrder0DeTurckLieCoeff (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 2 2 :=
  symmAbsorbedCoeff (I := I) (M := M) g₀ 0
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0DeTurckLieCoeff_appCc_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg S)
          (iteratedCovGrad (I := I) g₀ 0 2 0 S)) x v =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (symmS (I := I) (M := M) g₀ S))) x v := by
  exact symmAbsorbedCoeff_appCc_eq (I := I) (M := M) g₀ 0 S
    (ricciArmOrder0DeTurckLieCoeff (I := I) (M := M) g₀ g₁ g_bg)
    (Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0))
    (Classical.choose_spec (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) S 0)) x v


set_option linter.unusedSectionVars false in

theorem connDiffQuad_telescope (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q r : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q) r
      - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) r
        + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
            (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r := by
  rw [csArm_split (I := I) g₀ g₁ g₁' x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p q)
        (PDE.DeTurck.connDiff (I := I) g₁' g₀ x p q) r]
  rw [connDiff_endpoint_cocycle (I := I) g₀ g₁ g₁' x p q]

set_option linter.unusedSectionVars false in

theorem block3LegSummand_telescope (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (Xv0 Xv1 Xei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Xv0 Xv1 x) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Xei Xv1 x) (Xv0 x))
      - (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁') Xv0 Xv1 x) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁') Xei Xv1 x) (Xv0 x)) =
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Xv1 x) (Xv0 x)) (Xei x)
          + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
              (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xv0 x)) (Xei x))
        - (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (Xv1 x) (Xei x)) (Xv0 x)
            + PDE.DeTurck.connDiff (I := I) g₁ g₁' x
                (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xei x)) (Xv0 x)) := by
  have h1 := connDiffQuad_telescope (I := I) g₀ g₁ g₁' x (Xv1 x) (Xv0 x) (Xei x)
  have h2 := connDiffQuad_telescope (I := I) g₀ g₁ g₁' x (Xv1 x) (Xei x) (Xv0 x)
  change (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Xv1 x) (Xv0 x)) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Xv1 x) (Xei x)) (Xv0 x))
      - (PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xv0 x)) (Xei x)
        - PDE.DeTurck.connDiff (I := I) g₁' g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁' g₀ x (Xv1 x) (Xei x)) (Xv0 x)) = _
  rw [sub_sub_sub_comm, h1, h2]

def connDiffBiKernelBilin (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (g₀.inner x).comp
    ((PDE.DeTurck.connDiff (I := I) gj g₀ x)
      (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q))

@[simp] theorem connDiffBiKernelBilin_apply (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x p q v0 v1 =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) v0) v1 := by
  rw [connDiffBiKernelBilin, ContinuousLinearMap.comp_apply]

def connDiffBiSummandFib (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

@[simp] theorem connDiffBiSummandFib_toModel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) (v 0)) (v 1) := by
  rw [connDiffBiSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, Tensor0SSpace.toModel_ofModel,
    bilinFormToModel_apply, smul_eq_mul]
  rfl

def connDiffBiContrFibFixedFrame (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x)

theorem connDiffBiContrFibFixedFrame_toModel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x D) v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (B a x) (B b x)) (v 0)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [connDiffBiContrFibFixedFrame, ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, connDiffBiSummandFib_toModel]
  ring

theorem connDiffBiKernelBilin_homSection_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (p x) (q x) (V0 x))
  intro W
  have hinner : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₁' hp hq
  have houter : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => PDE.DeTurck.connDiff (I := I) gj g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b)) (V0 b))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) gj g₀ hinner V0.contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (PDE.DeTurck.connDiff (I := I) gj g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x (p x) (q x)) (V0 x)) (W x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) g₀
      ⟨fun b => PDE.DeTurck.connDiff (I := I) gj g₀ b
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' b (p b) (q b)) (V0 b), houter⟩
      ⟨fun b => W b, W.contMDiff⟩
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' y (p y) (q y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [connDiffBiKernelBilin_apply]
  rfl

theorem connDiffBiContrFibFixedFrame_apply_section_contMDiff
    (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (B a x) (B b x))
      (connDiffBiKernelBilin_homSection_contMDiff (I := I) gj g₀ g₁ g₁' (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x)
          (connDiffBiKernelBilin (I := I) gj g₀ g₁ g₁' x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => connDiffBiSummandFib (I := I) gj g₀ g₁ g₁' x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [connDiffBiContrFibFixedFrame, hStot_def]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

theorem connDiffBiContrFibFixedFrame_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' B x)
  intro Y
  exact connDiffBiContrFibFixedFrame_apply_section_contMDiff (I := I) gj g₀ g₁ g₁' B hB Y

def frameConnDiffBiKernel (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₀.inner x).flip v1 |>.comp
        ((PDE.DeTurck.connDiff (I := I) gj g₀ x).flip v0 |>.comp
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (PDE.DeTurck.connDiff (I := I) g₁ g₁' x).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (PDE.DeTurck.connDiff (I := I) g₁ g₁' x).map_smul c p, map_smul] }

theorem frameConnDiffBiKernel_apply (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' x v0 v1 p q =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) gj g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g₁' x p q) v0) v1 := by
  rw [frameConnDiffBiKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]

def connDiffBiContrFib (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x) x

theorem connDiffBiContrFib_eq_fixedFrame_on_nbhd (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (x₀ : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    connDiffBiContrFib (I := I) gj g₀ g₁ g₁' y =
      connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [connDiffBiContrFib, connDiffBiContrFibFixedFrame_toModel,
    connDiffBiContrFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner y (PDE.DeTurck.connDiff (I := I) gj g₀ y
            (PDE.DeTurck.connDiff (I := I) g₁ g₁' y (Bf a) (Bf b)) (v 0)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameConnDiffBiKernel_apply (I := I) gj g₀ g₁ g₁' y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₀ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₀ y
    (frameConnDiffBiKernel (I := I) gj g₀ g₁ g₁' y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₀ y a y)
    (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₀ x₀ hy i j)

theorem connDiffBiContrFib_contMDiff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (connDiffBiContrFibFixedFrame (I := I) gj g₀ g₁ g₁'
          (smoothOrthoFrame (I := I) g₀ x₀) x))) x₀ :=
    connDiffBiContrFibFixedFrame_contMDiff (I := I) gj g₀ g₁ g₁' (smoothOrthoFrame (I := I) g₀ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₀ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (connDiffBiContrFib_eq_fixedFrame_on_nbhd (I := I) gj g₀ g₁ g₁' x₀ hy))

def connDiffBiContrCoeffField (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x))
      contMDiff_toFun := connDiffBiContrFib_contMDiff (I := I) gj g₀ g₁ g₁' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

@[simp] theorem connDiffBiContrCoeffField_toSection (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (x : M) :
    (connDiffBiContrCoeffField (I := I) (M := M) gj g₀ g₁ g₁').toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)) :=
  rfl

noncomputable def connDiffBiContrCoeff (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 :=
  connDiffBiContrCoeffField (I := I) (M := M) gj g₀ g₁ g₁'

@[simp] theorem connDiffBiContrCoeff_toSection (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) :
    (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)) :=
  rfl

set_option linter.unusedSectionVars false in

theorem connDiffBiContrCoeff_appCc_eq (gj g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁') W)
        x v =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x
            (PDE.DeTurck.connDiff (I := I) gj g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₁' x
                (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₀ x b x)) (v 0)) (v 1) *
          unitModel (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₀ x a x
              else smoothOrthoFrame (I := I) g₀ x b x) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x))
        (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffBiContrCoeff (I := I) (M := M) gj g₀ g₁ g₁').toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [connDiffBiContrCoeff_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x)))
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) =
      connDiffBiContrFib (I := I) gj g₀ g₁ g₁' x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [connDiffBiContrFib, connDiffBiContrFibFixedFrame_toModel]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [unitModel]
  congr 1
  funext j
  fin_cases j <;> simp

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
