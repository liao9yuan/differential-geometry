import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartRicciDeriv
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamLinearizedChristoffel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.SecondCovGradChartHessian
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Sobolev.Embedding.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Geometry.Curvature.RealizedFamCurvatureJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

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
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in

private lemma appCc_smul_left_local (g : SmoothRiemannianMetric I M) (r s : ℕ)
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

private lemma unitModel_smul_local (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (c • T) x =
      c • unitModel (I := I) (M := M) g₀ 2 T x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul]

set_option linter.unusedSectionVars false in

private lemma unitModel_add2_local (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x =
      unitModel (I := I) (M := M) g₀ 2 S x + unitModel (I := I) (M := M) g₀ 2 S' x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in

private lemma unitModel_add2_apply (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (S + S') x v =
      unitModel (I := I) (M := M) g₀ 2 S x v + unitModel (I := I) (M := M) g₀ 2 S' x v := by
  rw [unitModel_add2_local, ContinuousMultilinearMap.add_apply]

set_option linter.unusedSectionVars false in

lemma cmm_two_basis_expand
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ)
    (v : Fin 2 → E) :
    f v =
      ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
          f ![(chartModelBasis E) k, (chartModelBasis E) i] := by
  classical
  have hexpand : ∀ k : Fin 2,
      v k = ∑ i : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v k)) i • chartModelBasis E i := by
    intro k; exact ((chartModelBasis E).sum_repr (v k)).symm
  have h_v_eq : v =
      fun k : Fin 2 => ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v k)) i • chartModelBasis E i := by
    funext k; exact hexpand k
  rw [show f v = f (fun k : Fin 2 =>
        ∑ i : Fin (Module.finrank ℝ E),
          ((chartModelBasis E).repr (v k)) i • chartModelBasis E i) from
    congrArg f h_v_eq]
  rw [ContinuousMultilinearMap.map_sum
    (f := f)
    (g := fun (k : Fin 2) (i : Fin (Module.finrank ℝ E)) =>
      ((chartModelBasis E).repr (v k)) i • chartModelBasis E i)]
  have h_pull : ∀ Jdx : Fin 2 → Fin (Module.finrank ℝ E),
      f (fun k : Fin 2 =>
          ((chartModelBasis E).repr (v k)) (Jdx k) • chartModelBasis E (Jdx k)) =
        (∏ k : Fin 2, ((chartModelBasis E).repr (v k)) (Jdx k)) *
          f (fun k : Fin 2 => chartModelBasis E (Jdx k)) := by
    intro Jdx
    have hpull := f.toMultilinearMap.map_smul_univ
      (c := fun k : Fin 2 => ((chartModelBasis E).repr (v k)) (Jdx k))
      (m := fun k : Fin 2 => chartModelBasis E (Jdx k))
    have hpull' :
        f (fun k : Fin 2 => ((chartModelBasis E).repr (v k)) (Jdx k) •
            chartModelBasis E (Jdx k)) =
        (∏ k : Fin 2, ((chartModelBasis E).repr (v k)) (Jdx k)) •
          f (fun k : Fin 2 => chartModelBasis E (Jdx k)) := hpull
    rw [hpull']; rfl
  rw [Finset.sum_congr rfl (fun Jdx _ => h_pull Jdx)]
  rw [← (finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm.sum_comp
    (fun Jdx : Fin 2 → Fin (Module.finrank ℝ E) =>
      (∏ k : Fin 2, ((chartModelBasis E).repr (v k)) (Jdx k)) *
        f (fun k : Fin 2 => chartModelBasis E (Jdx k)))]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
  have hbasis : (fun j : Fin 2 =>
        chartModelBasis E (((finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm (k, i)) j)) =
      ![(chartModelBasis E) k, (chartModelBasis E) i] := by
    funext j; fin_cases j <;> rfl
  have hprod : (∏ k' : Fin 2,
        ((chartModelBasis E).repr (v k'))
          (((finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm (k, i)) k')) =
      ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i := by
    rw [Fin.prod_univ_two]; rfl
  rw [hbasis, hprod]

set_option linter.unusedSectionVars false in

lemma unitModel_basis_expand_two (g₀ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
          unitModel (I := I) (M := M) g₀ 2 W x
            ![(chartModelBasis E) k, (chartModelBasis E) i]) =
      unitModel (I := I) (M := M) g₀ 2 W x v := by
  classical
  rw [Finset.sum_comm]
  exact (cmm_two_basis_expand (unitModel (I := I) (M := M) g₀ 2 W x) v).symm

def linearizedRicciThreeArmHjoint (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ} : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r 2 ℝ E)) ∞
    (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 ((Φ p.2).toSection p.1))
    ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ'))

def linearizedRicciThreeArmHcont (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ} : Prop :=
  ∀ x : M, ContinuousOn
    (fun t : ℝ => Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x))
    (realizedSmallSet (δ := δ) (δ' := δ'))

set_option linter.unusedSectionVars false in

private lemma threeArm_unitModel_appCc_intervalIntegrable
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) (W : SmoothCcTensor g₀ 0 r)
    {δ δ' : ℝ} (hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ'))
    (hcont : linearizedRicciThreeArmHcont (I := I) (M := M) g₀ r Φ (δ := δ) (δ' := δ'))
    (x : M) (v : Fin 2 → TangentSpace I x) :
    IntervalIntegrable
      (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Φ s) W) x v)
      MeasureTheory.volume 0 1 := by
  set u : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hu
  have hkey : ∀ s : ℝ,
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Φ s) W) x v =
        ((Tensor0SBundle.TensorRSSpace.toModel ((Φ s).toSection x))
          (Tensor0SSpace.toModel u)) v := by
    intro s
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      toModel_tensorRS_apply (I := I) r 2 x ((Φ s).toSection x) u]
  have hcontApp : ContinuousOn (fun s : ℝ =>
      ((Tensor0SBundle.TensorRSSpace.toModel ((Φ s).toSection x))
        (Tensor0SSpace.toModel u)) v) (realizedSmallSet (δ := δ) (δ' := δ')) := by
    have hstep : ContinuousOn (fun s : ℝ =>
        (Tensor0SBundle.TensorRSSpace.toModel ((Φ s).toSection x)) (Tensor0SSpace.toModel u))
        (realizedSmallSet (δ := δ) (δ' := δ')) :=
      (ContinuousLinearMap.apply ℝ (Tensor0SModel 2 ℝ E)
        (Tensor0SSpace.toModel u)).continuous.comp_continuousOn (hcont x)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ v).continuous.comp_continuousOn
      hstep
  have hcontFinal : ContinuousOn (fun s : ℝ =>
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Φ s) W) x v)
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine hcontApp.congr (fun s _ => ?_)
    exact (hkey s).symm
  exact (hcontFinal.mono hSI).intervalIntegrable

def linearizedRicciArm2Field (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  (-(1 : ℝ) / 2) •
    ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

def linearizedRicciArm0BaseCoeff (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
    - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

noncomputable def linearizedRicciArm1Fib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
      raisedKoszulFib (I := I) g₀ g₁ x).comp
    (cometricDoubleTraceFib (I := I) g₁ 1 x)

set_option linter.unusedSectionVars false in

@[simp] theorem linearizedRicciArm1Fib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 3 I x) :
    linearizedRicciArm1Fib (I := I) g₀ g₁ x D =
      (show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
          raisedKoszulFib (I := I) g₀ g₁ x)
        (cometricDoubleTraceFib (I := I) g₁ 1 x D) := by
  rw [linearizedRicciArm1Fib, ContinuousLinearMap.comp_apply]

theorem linearizedRicciArm1Fib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) x
        (linearizedRicciArm1Fib (I := I) g₀ g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x : M => linearizedRicciArm1Fib (I := I) g₀ g₁ x)
  intro Y
  have hdt : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) x
        (cometricDoubleTraceFib (I := I) g₁ 1 x (Y x))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (cometricDoubleTraceFib_contMDiff (I := I) g₁ 1) Y.contMDiff
  have hkos : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x
        ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
            raisedKoszulFib (I := I) g₀ g₁ x)
          (cometricDoubleTraceFib (I := I) g₁ 1 x (Y x)))) :=
    ContMDiff.clm_bundle_apply (b := id)
      (raisedKoszulFib_contMDiff (I := I) g₀ g₁) hdt
  refine hkos.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [linearizedRicciArm1Fib, ContinuousLinearMap.comp_apply]

noncomputable def ricciArmOrder1KoszulCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 2 I x from linearizedRicciArm1Fib (I := I) g₀ g₁ x)
      contMDiff_toFun := linearizedRicciArm1Fib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem ricciArmOrder1KoszulCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from linearizedRicciArm1Fib (I := I) g₀ g₁ x) := rfl

def linearizedRicciArm1BaseCoeff (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 3 2 :=
  ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

def traceHessianSlotPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3

noncomputable def domDomCongrFib (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x :=
  (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).symm.toContinuousLinearMap.comp
    (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
          traceHessianSlotPerm).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (I := I) 4 x).toContinuousLinearMap)

set_option linter.unusedSectionVars false in

theorem domDomCongrFib_apply (x : M) (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    domDomCongrFib (I := I) x D =
      Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
        (ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [domDomCongrFib]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rfl

noncomputable def traceHessianFib (g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x :=
  (cometricDoubleTraceFib (I := I) g₁ 2 x).comp (domDomCongrFib (I := I) x)

set_option linter.unusedSectionVars false in

@[simp] theorem traceHessianFib_toModel (g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SBundle.Tensor0SSpace 4 I x) :
    Tensor0SBundle.Tensor0SSpace.toModel (traceHessianFib (I := I) g₁ x D) =
      modelDoubleTrace (E := E) 2 (cometricLmodel (I := I) g₁ x)
        (ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
          (Tensor0SBundle.Tensor0SSpace.toModel D)) := by
  rw [traceHessianFib, ContinuousLinearMap.comp_apply, cometricDoubleTraceFib_toModel,
    domDomCongrFib_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem domDomCongr_section_contMDiff {d : ℕ} (ρ : Equiv.Perm (Fin d))
    (Z : ∀ x : M, Tensor0SBundle.Tensor0SSpace d I x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x (Z x))) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x
        (Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr ρ
            (Tensor0SBundle.Tensor0SSpace.toModel (Z x))))) := by
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

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

theorem traceHessianFib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (traceHessianFib (I := I) g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun x => traceHessianFib (I := I) g₁ x)
  intro Y
  have hYρ := domDomCongr_section_contMDiff (I := I) traceHessianSlotPerm (fun x => Y x) Y.contMDiff
  have hfield := ContMDiff.clm_bundle_apply (b := id)
    (cometricDoubleTraceFib_contMDiff (I := I) g₁ 2) hYρ
  refine hfield.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) ?_
  rw [traceHessianFib, ContinuousLinearMap.comp_apply, domDomCongrFib_apply]
  rfl

noncomputable def traceHessianCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x)
      contMDiff_toFun := traceHessianFib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in

@[simp] theorem traceHessianCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x) := rfl

theorem traceHessianCoeff_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((traceHessianCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => traceHessianFib (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hYρ := domDomCongrField_jointContMDiffOn (I := I) traceHessianSlotPerm
    (S := realizedSmallSet (δ := δ) (δ' := δ')) (fun p : M × ℝ => Y p.1) hYjoint
  have hCDT := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
    (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := p.1)
      (ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))) hYρ
  refine hCDT.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t) ?_
  change traceHessianFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1) = _
  rw [traceHessianFib, ContinuousLinearMap.comp_apply, domDomCongrFib_apply]

private theorem jointTotalSpace_const_smul_local {d : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact ((e.linear ℝ hx).map_smul a (A p)).symm
  · exact ((e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)).symm

theorem linearizedRicci_arm2Field_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (linearizedRicciArm2Field (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      ((-(1 : ℝ) / 2) • cometricDoubleTraceFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 2 p.1 :
        Tensor0SBundle.Tensor0SSpace 4 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => by
      have hfib := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
        (fun q : M × ℝ => Y q.1) (Y.contMDiff.comp_contMDiffOn contMDiffOn_fst)
      have hsmul := jointTotalSpace_const_smul_local (I := I) (d := 2) (-(1 : ℝ) / 2)
        (fun q : M × ℝ => cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' q.2) 2 q.1 (Y q.1)) hfib
      refine hsmul.congr (fun q _ => ?_)
      rfl)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [linearizedRicciArm2Field, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
    Pi.smul_apply, ricciArmPrincipalCoeffPure_toSection]

private theorem jointTotalSpaceRS_sub_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

private theorem jointTotalSpaceRS_const_smul_local {r s : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul a (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)

theorem realizedFam_chartRiemannTensor_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartRiemannTensor (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α i j k l (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_riemann (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG i j k l hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartRiemannTensor (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j k l r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr
    (fun q _ => rfl) rfl

theorem realizedFam_chartChristoffel_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartChristoffel (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_christoffel (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG i j k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartChristoffel (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr
    (fun q _ => rfl) rfl

private noncomputable def outerPairBilinChartα (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g α x k l * K X (chartBasisVecFiber (I := I) α k x)) •
          (ContinuousLinearMap.flip Dd (chartBasisVecFiber (I := I) α l x))
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

private lemma outerPairBilinChartα_apply (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    outerPairBilinChartα (I := I) g α K Dd X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x k l *
          (K X (chartBasisVecFiber (I := I) α k x) *
            Dd X' (chartBasisVecFiber (I := I) α l x)) := by
  rw [outerPairBilinChartα, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

private lemma double_frame_bilin_trace_chartα
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (K (chartBasisVecFiber (I := I) α m x) (chartBasisVecFiber (I := I) α k x) *
            Dd (chartBasisVecFiber (I := I) α n x) (chartBasisVecFiber (I := I) α l x))) := by
  classical
  have hinner : ∀ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      outerPairBilinChartα (I := I) g α K Dd (B a) (B a) := by
    intro a
    rw [outerPairBilinChartα_apply]
    have h := orthonormal_basis_bilin_trace_chartα (I := I) g α hxbase
      (innerPairBilin (I := I) x K Dd (B a)) B hB
    simp only [innerPairBilin_apply, smul_eq_mul] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have hout := orthonormal_basis_bilin_trace_chartα (I := I) g α hxbase
    (outerPairBilinChartα (I := I) g α K Dd) B hB
  simp only [smul_eq_mul] at hout
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [outerPairBilinChartα_apply]

private lemma riemannBiContrFib_toModel_chartα
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannBiContrFib (I := I) g x D) v =
      2 * ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (g.inner x (riemannOp (LeviCivita (I := I) g) x (v 0)
              (chartBasisVecFiber (I := I) α m x) (chartBasisVecFiber (I := I) α k x)) (v 1) *
            Tensor0SSpace.toModel D
              ![(chartBasisVecFiber (I := I) α n x : E),
                (chartBasisVecFiber (I := I) α l x : E)])) := by
  classical
  set Bf : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with hBf
  have hBf_on : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (Bf i) (Bf j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (riemannOp (LeviCivita (I := I) g) x (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
        frameRiemannKernel (I := I) g x (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I x)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) :=
    fun a b => by
      rw [frameRiemannKernel_apply (I := I) g x (v 0) (v 1) (Bf a) (Bf b),
        bilinFormToModel_symm_apply (TangentSpace I x) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
      rfl
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsummand a b))]
  rw [double_frame_bilin_trace_chartα (I := I) g α hxbase
    (frameRiemannKernel (I := I) g x (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I x)).symm (Tensor0SSpace.toModel D)) Bf hBf_on]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  refine congrArg (fun t => chartInvGramMatrix (I := I) g α x m n * t) ?_
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [frameRiemannKernel_apply,
    bilinFormToModel_symm_apply (TangentSpace I x) (Tensor0SSpace.toModel D)
      (chartBasisVecFiber (I := I) α n x) (chartBasisVecFiber (I := I) α l x)]
  rfl

private lemma realizedFam_chartGramMatrix_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartGramMatrix (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := hG.1 i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartGramOnE (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartGramOnE_def, (extChartAt I α).left_inv hxsrc]

private lemma riemannChartLoweredScalar_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
        (riemannOp (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)) p.1
          (chartBasisVecFiber (I := I) α i p.1)
          (chartBasisVecFiber (I := I) α j p.1)
          (chartBasisVecFiber (I := I) α k p.1))
        (chartBasisVecFiber (I := I) α l p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hRm : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ m : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α k i j m
            (extChartAt I α p.1) *
          chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m l)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine contMDiffOn_finset_sum (fun m _ => ?_)
    have hriem := realizedFam_chartRiemannTensor_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α k i j m
    have hgram := realizedFam_chartGramMatrix_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α m l
    exact hriem.mul hgram
  refine hRm.congr (fun p hp => ?_)
  obtain ⟨hx, _hs⟩ := hp
  have hxgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hx
  set gs := realizedFam (I := I) g₀ T T' hδ hδ' p.2 with hgs
  rw [riemannOp_chartBasisVec_alpha_eq (I := I) gs α k i j hxgood]
  rw [map_sum]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [g_inner_eq_chartGramMatrix_basis (I := I) gs α p.1 m l, mul_comm]

private lemma riemannBiContrFibAppY_chartCoord_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 2 ℝ E, fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x⟯)
    (α : M) (σ : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => Tensor0SSpace.toModel
        (riemannBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1))
        ![(chartBasisVecFiber (I := I) α (σ 0) p.1 : E),
          (chartBasisVecFiber (I := I) α (σ 1) p.1 : E)])
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hYbasis : ∀ n l : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Tensor0SSpace.toModel (Y p.1)
          ![(chartBasisVecFiber (I := I) α n p.1 : E), (chartBasisVecFiber (I := I) α l p.1 : E)])
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro n l p₀ hp₀
    have hYon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      (Y.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hYmdiff := hYon p₀ hp₀
    have hvbasis : ∀ i : Fin 2, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
          (![fun b : M => chartBasisVecFiber (I := I) α n b,
              fun b : M => chartBasisVecFiber (I := I) α l b] i p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p₀ := by
      intro i
      fin_cases i
      · exact (chartBasisVec_jointContMDiffOn (I := I) α n p₀
          ⟨hp₀.1, Set.mem_univ _⟩).mono
          (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
      · exact (chartBasisVec_jointContMDiffOn (I := I) α l p₀
          ⟨hp₀.1, Set.mem_univ _⟩).mono
          (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
    have happly := TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 2
      (s := (chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) (p₀ := p₀)
      (fun b : M => Y b) hYmdiff
      (![fun b : M => chartBasisVecFiber (I := I) α n b,
          fun b : M => chartBasisVecFiber (I := I) α l b]) hvbasis
    refine happly.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      congr 1
      funext i; fin_cases i <;> rfl
    · congr 1; funext i; fin_cases i <;> rfl
  have hcomb : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => 2 * ∑ m, ∑ n, chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
          ((realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
              (riemannOp (LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2)) p.1
                ((![(chartBasisVecFiber (I := I) α (σ 0) p.1 : E),
                    (chartBasisVecFiber (I := I) α (σ 1) p.1 : E)] : Fin 2 → E) 0)
                (chartBasisVecFiber (I := I) α m p.1) (chartBasisVecFiber (I := I) α k p.1))
              ((![(chartBasisVecFiber (I := I) α (σ 0) p.1 : E),
                    (chartBasisVecFiber (I := I) α (σ 1) p.1 : E)] : Fin 2 → E) 1) *
            Tensor0SSpace.toModel (Y p.1)
              ![(chartBasisVecFiber (I := I) α n p.1 : E),
                (chartBasisVecFiber (I := I) α l p.1 : E)])))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine (contMDiffOn_const (c := (2 : ℝ))).mul ?_
    refine contMDiffOn_finset_sum (fun m _ => contMDiffOn_finset_sum (fun n _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T T' hδ hδ' α m n).mul ?_
    refine contMDiffOn_finset_sum (fun k _ => contMDiffOn_finset_sum (fun l _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T T' hδ hδ' α k l).mul ?_
    refine (riemannChartLoweredScalar_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
      α (σ 0) m k (σ 1)).mul ?_
    exact hYbasis n l
  refine hcomb.congr (fun p hp => ?_)
  obtain ⟨hx, _hs⟩ := hp
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hx
  rw [riemannBiContrFib_toModel_chartα (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α hxbase]

private lemma riemannBiContrFibAppY_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 2 ℝ E, fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (riemannBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  set gfam : ℝ → SmoothRiemannianMetric I M := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s
    with hgfam
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  intro p₀ hp₀
  set α := p₀.1 with hα
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) α with he
  set Bcmm := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBcmm
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hαbaseT : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) α
  have hαbase : α ∈ e.baseSet := by
    rw [he]; exact mem_baseSet_trivializationAt _ _ α
  have hnhd : (chartAt H α).source ×ˢ S ∈ nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H α).source ×ˢ S,
      (chartAt H α).open_source.prod realizedSmallSet_isOpen, ⟨hαsrc, hp₀.2⟩, fun q hq => hq.1⟩
  have hcoordEach : ∀ σ : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Bcmm.repr
          (e ⟨p.1, riemannBiContrFib (I := I) (gfam p.2) p.1 (Y p.1)⟩).2 σ)
        ((Set.univ : Set M) ×ˢ S) p₀ := by
    intro σ
    have hscal := riemannBiContrFibAppY_chartCoord_jointContMDiffOn (I := I) g₀ T T' hδ hδ' Y α σ
    have hscalAt := (hscal p₀ ⟨hαsrc, hp₀.2⟩).mono_of_mem_nhdsWithin hnhd
    have hreadout : ∀ {q : M × ℝ}, q.1 ∈ e.baseSet →
        Bcmm.repr (e ⟨q.1, riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1)⟩).2 σ =
          Tensor0SSpace.toModel (riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1))
            ![(chartBasisVecFiber (I := I) α (σ 0) q.1 : E),
              (chartBasisVecFiber (I := I) α (σ 1) q.1 : E)] := by
      intro q hqbase
      rw [continuousMultilinearMap_basis_repr]
      have hcoe : (e ⟨q.1,
          riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1)⟩).2 =
          (e.linearMapAt ℝ q.1) (riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1)) :=
        (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) _).symm
      rw [hcoe]
      have happly := TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem (I := I) α q.1 hqbase
        (riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1))
        (fun j => (chartModelBasis E) (σ j))
      rw [tensor0SSpace_continuousLinearEquiv_symm_apply] at happly
      rw [happly]
      change Tensor0SSpace.toModel (riemannBiContrFib (I := I) (gfam q.2) q.1 (Y q.1))
          (fun j => (trivializationAt E (TangentSpace I) α).symmL ℝ q.1
            ((chartModelBasis E) (σ j))) = _
      congr 1
      funext j
      fin_cases j <;> rfl
    refine hscalAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hnhd] with q hq
      have hqbaseT : q.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hq.1
      have hqbase : q.1 ∈ e.baseSet := by rw [he]; exact hqbaseT
      exact hreadout hqbase
    · exact hreadout hαbase
  have hcoordVec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => fun σ : Fin 2 → Fin (Module.finrank ℝ E) =>
        Bcmm.repr (e ⟨p.1, riemannBiContrFib (I := I) (gfam p.2) p.1 (Y p.1)⟩).2 σ)
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    contMDiffWithinAt_pi_space.mpr (fun σ => hcoordEach σ)
  have hfinal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ => (e ⟨p.1,
        riemannBiContrFib (I := I) (gfam p.2) p.1 (Y p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hequiv := (Bcmm.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt
      (x := Bcmm.equivFun
        (e ⟨p₀.1, riemannBiContrFib (I := I) (gfam p₀.2) p₀.1 (Y p₀.1)⟩).2)).comp_contMDiffWithinAt
      p₀ hcoordVec
    refine hequiv.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      exact (Bcmm.equivFun.symm_apply_apply _).symm
    · exact (Bcmm.equivFun.symm_apply_apply _).symm
  exact hfinal

private lemma raisedKoszulVec_realizedFam_chartα
    (g₀ : SmoothRiemannianMetric I M) (g₁ : SmoothRiemannianMetric I M) (α : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (j k : Fin (Module.finrank ℝ E)) :
    raisedKoszulVec (I := I) g₀ g₁ x
        (chartBasisVecFiber (I := I) α j x)
        (chartBasisVecFiber (I := I) α k x) =
      ∑ p : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₀ α x p l *
            (∑ q : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) g₁ α k j q (extChartAt I α x) -
                chartChristoffel (I := I) g₀ α k j q (extChartAt I α x)) *
                chartGramMatrix (I := I) g₁ α x q l)) •
          chartBasisVecFiber (I := I) α p x := by
  classical
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  set W : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x
    (chartBasisVecFiber (I := I) α j x) (chartBasisVecFiber (I := I) α k x) with hW
  set cvx : TangentSpace I x →ₗ[ℝ] ℝ := (g₁.inner x W).toLinearMap with hcvx
  have hraisedeq : raisedKoszulVec (I := I) g₀ g₁ x
        (chartBasisVecFiber (I := I) α j x) (chartBasisVecFiber (I := I) α k x) =
      metricSharp (I := I) g₀ x cvx := by
    rw [raisedKoszulVec_apply, inverseMetricSharpFib_apply]
    refine congrArg (fun t => metricSharp (I := I) g₀ x t) ?_
    ext w
    rw [cotangentToDualLinear_apply,
      DifferentialGeometry.Analysis.Sobolev.TensorHilbert.cotangentToDual_g0FlatCLM]
    rfl
  rw [hraisedeq]
  have hlocal := metricSharpChartLocal_eq_metricSharp (I := I) g₀ α (fun _ : M => cvx) hxbase
  rw [← hlocal]
  rw [metricSharpChartLocal]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 1
  rw [metricSharpChartCoeff_def]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  congr 1
  show cvx (chartBasisVecFiber (I := I) α l x) = _
  rw [hcvx]
  change g₁.inner x W (chartBasisVecFiber (I := I) α l x) = _
  rw [hW, DifferentialGeometry.PDE.DeTurck.connDiff_chartBasis_pair_eq_sum (I := I) g₁ g₀ α hx j k]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [g_inner_eq_chartGramMatrix_basis (I := I) g₁ α x q l]

private lemma genJointGram_const_g0
    (g₀ : SmoothRiemannianMetric I M) (α : M) {S : Set ℝ} :
    GenJointGram (I := I) (fun _ : ℝ => g₀) α S := by
  refine ⟨?_, ?_⟩
  · intro a b s₀ y₀ _hs hy
    have hsnd : ContDiffAt ℝ ∞ (Prod.snd : ℝ × E → E) (s₀, y₀) := contDiffAt_snd
    exact (((chartGramOnE_contDiffOn (I := I) g₀ α a b).mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hy)).comp (s₀, y₀) hsnd
  · intro s₀ _ x hx
    exact chartGramMatrix_det_pos (I := I) g₀ α hx

private lemma chartChristoffel_g0_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (α : M) (i j k : Fin (Module.finrank ℝ E)) {S : Set ℝ} :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartChristoffel (I := I) g₀ α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
  classical
  have hG := genJointGram_const_g0 (I := I) g₀ α (S := S)
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_christoffel (I := I) (fun _ : ℝ => g₀) α hG i j k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartChristoffel (I := I) g₀ α i j k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr (fun q _ => rfl) rfl

private lemma chartInvGramMatrix_g0_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E)) {S : Set ℝ} :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartInvGramMatrix (I := I) g₀ α p.1 i j)
      ((chartAt H α).source ×ˢ S) := by
  classical
  have hG := genJointGram_const_g0 (I := I) g₀ α (S := S)
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun p hp => hp.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_invGram (I := I) (fun _ : ℝ => g₀) α hG i j hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartInvGramOnE (I := I) g₀ α i j r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  refine (hentryM.comp_contMDiffWithinAt p hmoveAt).congr ?_ ?_
  · intro q hq
    have hqx : q.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hq.1
    rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hqx]
  · rw [Function.comp_apply, chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc]

private lemma omAppChartBasisVec_jointContMDiffOn
    (om : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E, fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x⟯)
    (α : M) (p : Fin (Module.finrank ℝ E)) {S : Set ℝ} :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun q : M × ℝ => (om q.1) (fun _ : Fin 1 => chartBasisVecFiber (I := I) α p q.1))
      ((chartAt H α).source ×ˢ S) := by
  classical
  intro p₀ hp₀
  have hOmon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 1 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 1 I z) q.1 (om q.1))
      ((chartAt H α).source ×ˢ S) :=
    (om.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
  have hOmAt := hOmon p₀ hp₀
  have hvbasis : ∀ i : Fin 1, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) q.1
        (![fun b : M => chartBasisVecFiber (I := I) α p b] i q.1))
      ((chartAt H α).source ×ˢ S) p₀ := by
    intro i
    fin_cases i
    exact (chartBasisVec_jointContMDiffOn (I := I) α p p₀
      ⟨hp₀.1, Set.mem_univ _⟩).mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
  have happly := TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 1
    (s := (chartAt H α).source ×ˢ S) (p₀ := p₀)
    (fun b : M => om b) hOmAt
    (![fun b : M => chartBasisVecFiber (I := I) α p b]) hvbasis
  have hcoe : ∀ q : M × ℝ,
      Tensor0SBundle.Tensor0SSpace.toModel (om q.1)
          (fun i : Fin 1 => ![fun b : M => chartBasisVecFiber (I := I) α p b] i q.1) =
        (om q.1) (fun _ : Fin 1 => chartBasisVecFiber (I := I) α p q.1) := by
    intro q
    rw [Tensor0SBundle.Tensor0SSpace.toModel]
    rw [tensor0SSpace_continuousLinearEquiv_apply]
    refine congrArg (fun w : Fin 1 → TangentSpace I q.1 => (om q.1) w) ?_
    funext i
    fin_cases i
    rfl
  refine happly.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q _
    exact (hcoe q).symm
  · exact (hcoe p₀).symm

private lemma raisedKoszulFibAppOm_chartCoord_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (om : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E, fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x⟯)
    (α : M) (σ : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => (om p.1) (fun _ : Fin 1 =>
        raisedKoszulVec (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1
          (chartBasisVecFiber (I := I) α (σ 0) p.1)
          (chartBasisVecFiber (I := I) α (σ 1) p.1)))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hcomb : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ r : Fin (Module.finrank ℝ E),
        (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₀ α p.1 r l *
            (∑ q : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α (σ 1) (σ 0) q
                  (extChartAt I α p.1) -
                chartChristoffel (I := I) g₀ α (σ 1) (σ 0) q (extChartAt I α p.1)) *
                chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 q l)) *
          (om p.1) (fun _ : Fin 1 => chartBasisVecFiber (I := I) α r p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine contMDiffOn_finset_sum (fun r _ => ?_)
    refine ContMDiffOn.mul ?_ (omAppChartBasisVec_jointContMDiffOn (I := I) om α r)
    refine contMDiffOn_finset_sum (fun l _ => ?_)
    refine (chartInvGramMatrix_g0_jointContMDiffOn (I := I) g₀ α r l).mul ?_
    refine contMDiffOn_finset_sum (fun q _ => ?_)
    refine ContMDiffOn.mul ?_ (realizedFam_chartGramMatrix_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α q l)
    refine ContMDiffOn.sub ?_ ?_
    · have hΓs := realizedFam_chartChristoffel_jointContMDiffOn (I := I) g₀ T T' hδ hδ'
        α (σ 1) (σ 0) q
      exact hΓs.mono (fun z hz => ⟨hz.1, hz.2⟩)
    · exact chartChristoffel_g0_jointContMDiffOn (I := I) g₀ α (σ 1) (σ 0) q
  refine hcomb.congr (fun p hp => ?_)
  obtain ⟨hx, _hs⟩ := hp
  have hxgood : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hx
  rw [raisedKoszulVec_realizedFam_chartα (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2)
    α hxgood (σ 0) (σ 1)]
  set φ : TangentSpace I p.1 →L[ℝ] ℝ :=
    continuousMultilinearCurryFin1 ℝ (TangentSpace I p.1) ℝ (om p.1) with hφ
  have hφapply : ∀ v : TangentSpace I p.1, (om p.1) (fun _ : Fin 1 => v) = φ v := by
    intro v; rw [hφ, continuousMultilinearCurryFin1_apply]; rfl
  rw [hφapply]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [map_smul, smul_eq_mul, hφapply, mul_comm]

private lemma raisedKoszulFibAppOm_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (om : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 1 ℝ E, fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
            raisedKoszulFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1) (om p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  set gfam : ℝ → SmoothRiemannianMetric I M := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s
    with hgfam
  set S := realizedSmallSet (δ := δ) (δ' := δ') with hS
  intro p₀ hp₀
  set α := p₀.1 with hα
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) α with he
  set Bcmm := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBcmm
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hαbaseT : α ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) α
  have hαbase : α ∈ e.baseSet := by
    rw [he]; exact mem_baseSet_trivializationAt _ _ α
  have hnhd : (chartAt H α).source ×ˢ S ∈ nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H α).source ×ˢ S,
      (chartAt H α).open_source.prod realizedSmallSet_isOpen, ⟨hαsrc, hp₀.2⟩, fun q hq => hq.1⟩
  have hcoordEach : ∀ σ : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Bcmm.repr
          (e ⟨p.1, (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I p.1 from
            raisedKoszulFib (I := I) g₀ (gfam p.2) p.1) (om p.1)⟩).2 σ)
        ((Set.univ : Set M) ×ˢ S) p₀ := by
    intro σ
    have hscal := raisedKoszulFibAppOm_chartCoord_jointContMDiffOn (I := I) g₀ T T' hδ hδ' om α σ
    have hscalAt := (hscal p₀ ⟨hαsrc, hp₀.2⟩).mono_of_mem_nhdsWithin hnhd
    have hreadout : ∀ {q : M × ℝ}, q.1 ∈ e.baseSet →
        Bcmm.repr (e ⟨q.1, (show Tensor0SBundle.Tensor0SSpace 1 I q.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I q.1 from
          raisedKoszulFib (I := I) g₀ (gfam q.2) q.1) (om q.1)⟩).2 σ =
          (om q.1) (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ (gfam q.2) q.1
            (chartBasisVecFiber (I := I) α (σ 0) q.1)
            (chartBasisVecFiber (I := I) α (σ 1) q.1)) := by
      intro q hqbase
      rw [continuousMultilinearMap_basis_repr]
      have hcoe : (e ⟨q.1, (show Tensor0SBundle.Tensor0SSpace 1 I q.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I q.1 from
          raisedKoszulFib (I := I) g₀ (gfam q.2) q.1) (om q.1)⟩).2 =
          (e.linearMapAt ℝ q.1) ((show Tensor0SBundle.Tensor0SSpace 1 I q.1 →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 2 I q.1 from
            raisedKoszulFib (I := I) g₀ (gfam q.2) q.1) (om q.1)) :=
        (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) _).symm
      rw [hcoe]
      have happly := TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem (I := I) α q.1 hqbase
        ((show Tensor0SBundle.Tensor0SSpace 1 I q.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I q.1 from
          raisedKoszulFib (I := I) g₀ (gfam q.2) q.1) (om q.1))
        (fun j => (chartModelBasis E) (σ j))
      rw [tensor0SSpace_continuousLinearEquiv_symm_apply] at happly
      rw [happly]
      rw [raisedKoszulFib_apply]
      rw [show (fun j => (trivializationAt E (TangentSpace I) α).symmL ℝ q.1
            ((chartModelBasis E) (σ j))) =
          (fun j => chartBasisVecFiber (I := I) α (σ j) q.1) from by
        funext j; rfl]
      rfl
    refine hscalAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hnhd] with q hq
      have hqbaseT : q.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hq.1
      have hqbase : q.1 ∈ e.baseSet := by rw [he]; exact hqbaseT
      exact hreadout hqbase
    · exact hreadout hαbase
  have hcoordVec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => fun σ : Fin 2 → Fin (Module.finrank ℝ E) =>
        Bcmm.repr (e ⟨p.1, (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I p.1 from
          raisedKoszulFib (I := I) g₀ (gfam p.2) p.1) (om p.1)⟩).2 σ)
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    contMDiffWithinAt_pi_space.mpr (fun σ => hcoordEach σ)
  have hfinal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ => (e ⟨p.1, (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        raisedKoszulFib (I := I) g₀ (gfam p.2) p.1) (om p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hequiv := (Bcmm.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt
      (x := Bcmm.equivFun
        (e ⟨p₀.1, (show Tensor0SBundle.Tensor0SSpace 1 I p₀.1 →L[ℝ]
            Tensor0SBundle.Tensor0SSpace 2 I p₀.1 from
          raisedKoszulFib (I := I) g₀ (gfam p₀.2) p₀.1) (om p₀.1)⟩).2)).comp_contMDiffWithinAt
      p₀ hcoordVec
    refine hequiv.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      exact (Bcmm.equivFun.symm_apply_apply _).symm
    · exact (Bcmm.equivFun.symm_apply_apply _).symm
  exact hfinal

theorem ricciArmOrder0RiemannCoeff_realizedFam_jointContMDiff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((ricciArmOrder0RiemannCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => riemannBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => riemannBiContrFibAppY_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' Y)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 t) ?_
  rw [ricciArmOrder0RiemannCoeff_toSection]
  rfl

theorem linearizedRicci_arm0BaseCoeff_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') := by
  have hRm := ricciArmOrder0RiemannCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  have hCurv := ricciArmOrder0CurvCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  have hsub := jointTotalSpaceRS_sub_local (I := I) (r := 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (ricciArmOrder0RiemannCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
    (fun p : M × ℝ => (ricciArmOrder0CurvCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
    hRm hCurv
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 t) ?_
  rw [linearizedRicciArm0BaseCoeff, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply]

theorem raisedKoszulFib_realizedFam_jointContMDiffOn (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 1 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 1 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 1 2 I z) p.1
        ((show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
          raisedKoszulFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 1 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SBundle.Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        raisedKoszulFib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro om
  exact raisedKoszulFibAppOm_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ' om

theorem linearizedRicci_arm1BaseCoeff_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 3 I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SBundle.Tensor0SSpace 3 I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        linearizedRicciArm1Fib (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1))
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun Y => by
      have hZ := cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 1) g₀ T T' hδ hδ'
        (fun q : M × ℝ => Y q.1) (Y.contMDiff.comp_contMDiffOn contMDiffOn_fst)
      have hkos := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
        (raisedKoszulFib_realizedFam_jointContMDiffOn (I := I) g₀ T T' hδ hδ') hZ
      refine hkos.congr (fun q _ => ?_)
      refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) q.1 t) ?_
      rw [linearizedRicciArm1Fib_apply])
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 t) ?_
  rw [linearizedRicciArm1BaseCoeff, ricciArmOrder1KoszulCoeff_toSection]

def linearizedRicciArm2FieldLichnerowicz (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
    - (1 / 2 : ℝ) • traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)

theorem linearizedRicci_arm2FieldLichnerowicz_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') := by
  have hPrin := ricciArmPrincipalCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  have hTH := traceHessianCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  have hsmul := jointTotalSpaceRS_const_smul_local (I := I) (r := 4) (s := 2) (1 / 2 : ℝ)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (traceHessianCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
    hTH
  have hsub := jointTotalSpaceRS_sub_local (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (ricciArmPrincipalCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
    (fun p : M × ℝ => (1 / 2 : ℝ) • (traceHessianCoeff (I := I) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1)
    hPrin hsmul
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [linearizedRicciArm2FieldLichnerowicz, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
    Pi.sub_apply, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]

set_option linter.unusedSectionVars false in

private lemma riemannianFiberNormSq_smul_value_appCc
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (c : ℝ)
    (v : Tensor0SBundle.TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedSectionVars false in
private lemma gFibreOpBound_mono_local
    (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    {δ δ' : ℝ} (hle : δ ≤ δ') (hδ : gFibreOpBound (I := I) (M := M) g₀ h δ) :
    gFibreOpBound (I := I) (M := M) g₀ h δ' := by
  intro x v w
  refine le_trans (hδ x v w) ?_
  have hsv : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hprod : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv hsw
  nlinarith [hle, hprod]

set_option linter.unusedSectionVars false in
private theorem exists_orthoFrame_basis_local (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
      (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)),
      (∀ i : Fin (Module.finrank ℝ E), bse i = e i) ∧
      (∀ a b : Fin (Module.finrank ℝ E),
        g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) := by
  classical
  obtain ⟨n, e0, hn, horth0, _hpars, _hrepr⟩ :=
    DifferentialGeometry.Integral.Connection.exists_orthonormal_frame_riemannianFiberNormSq
      (I := I) (M := M) g 0 0 x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  subst hnE
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x := e0 with he_def
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := horth0
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  refine ⟨e, basisOfLinearIndependentOfCardEqFinrank he_li hcard, fun i => ?_, horth⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

set_option linter.unusedSectionVars false in
private theorem rfns_le_of_Ksum_sq_le
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    (C : ℝ)
    (hKsum : ∀ (e : Fin (Module.finrank ℝ E) → TangentSpace I x),
      (∀ a b : Fin (Module.finrank ℝ E),
        g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) →
      ∀ (K : Fin r → Fin (Module.finrank ℝ E)),
        (∑ J : Fin s → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x r s S (Module.finrank ℝ E) e K J) ^ 2)
          ≤ C ^ 2) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x S
      ≤ ((Module.finrank ℝ E : ℝ) ^ r) * C ^ 2 := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis_local (I := I) (M := M) g₀ x
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ r s x S e bse rfl hbse horth]
  calc (∑ K : Fin r → Fin (Module.finrank ℝ E), ∑ J : Fin s → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x r s S (Module.finrank ℝ E) e K J) ^ 2)
      ≤ ∑ _K : Fin r → Fin (Module.finrank ℝ E), C ^ 2 :=
        Finset.sum_le_sum (fun K _ => hKsum e horth K)
    _ = ((Module.finrank ℝ E : ℝ) ^ r) * C ^ 2 := by
        rw [Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_pow]

set_option linter.unusedSectionVars false in
private lemma metricInner_injective_local (g₁ : SmoothRiemannianMetric I M) (x : M)
    {a b : TangentSpace I x}
    (hab : ∀ w : TangentSpace I x, g₁.inner x a w = g₁.inner x b w) : a = b := by
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g₁.pos x (a - b) hsub
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    have hsymm₁ : g₁.inner x (a - b) (a - b) =
        g₁.inner x (a - b) a - g₁.inner x (a - b) b := by rw [← map_sub]
    rw [hsymm₁, g₁.symm x (a - b) a, g₁.symm x (a - b) b]
    have e1 : g₁.inner x a (a - b) = g₁.inner x b (a - b) := hab (a - b)
    rw [e1]; ring
  exact absurd hzero (ne_of_gt hpos)

set_option linter.unusedSectionVars false in
private lemma cometric_sum_eq_invSharp (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (b : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x b ((Module.finBasis ℝ E) k) •
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x b) := by
  classical
  apply metricInner_injective_local (I := I) g₁ x
  intro w
  have hcoord : ∀ k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).cDualBasis k (w : E) =
        (Module.finBasis ℝ E).repr (w : E) k := by
    intro k
    rw [show ((Module.finBasis ℝ E).cDualBasis k) =
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
      rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
      congr 1
      exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
    rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  have hlhs : ∀ k : Fin (Module.finrank ℝ E),
      (g₁.inner x (g₀.inner x b ((Module.finBasis ℝ E) k) •
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))) w =
        g₀.inner x b ((Module.finBasis ℝ E) k) *
          (Module.finBasis ℝ E).repr (w : E) k := by
    intro k
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr 1
    have hinner : g₁.inner x (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) w =
        (Module.finBasis ℝ E).cDualBasis k (w : E) := by
      have h1 : cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) =
          inverseMetricSharpFib (I := I) g₁ x
            ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) := rfl
      rw [h1, inverseMetricSharpFib_inner (I := I) g₁ x _ w, cotangentToDualLinear_apply,
        cotangentToDual_apply]
      change (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) (fun _ : Fin 1 => (w : E)) = _
      rw [Tensor0SBundle.model_covectorOfCLM_apply]
    rw [hinner, hcoord k]
  rw [Finset.sum_congr rfl (fun k _ => hlhs k)]
  rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  have hwexp : (w : TangentSpace I x) =
      ∑ k : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).repr (w : E) k • ((Module.finBasis ℝ E) k : TangentSpace I x) := by
    have h := (Module.finBasis ℝ E).sum_repr (w : E)
    exact h.symm
  conv_rhs => rw [hwexp, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.map_smul, smul_eq_mul, mul_comm]

set_option linter.unusedSectionVars false in
private lemma abs_g0_inner_invSharp_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ h δ) (x : M)
    (a b : TangentSpace I x)
    (hua : g₀.inner x a a ≤ 1) (hub : g₀.inner x b b ≤ 1) :
    |g₀.inner x a (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x b))| ≤
      1 / (1 - δ) := by
  set f : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x b) with hf
  have hcs := DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
    (I := I) (M := M) g₀ x a f
  have hfbound := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le (I := I) g₀ g₁ h htie
    hδ_lt hδ_nn hδ x b
  rw [← hf] at hfbound
  have hsa_nn : 0 ≤ Real.sqrt (g₀.inner x a a) := Real.sqrt_nonneg _
  have hsb_le : Real.sqrt (g₀.inner x b b) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hub
  have hsa_le : Real.sqrt (g₀.inner x a a) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hua
  have hcoeff : 0 < 1 - δ := by linarith
  have hinv_nn : 0 ≤ 1 / (1 - δ) := by positivity
  have hsf_nn : 0 ≤ Real.sqrt (g₀.inner x f f) := Real.sqrt_nonneg _
  calc |g₀.inner x a f|
      ≤ Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x f f) := hcs
    _ ≤ Real.sqrt (g₀.inner x a a) * ((1 / (1 - δ)) * Real.sqrt (g₀.inner x b b)) :=
        mul_le_mul_of_nonneg_left hfbound hsa_nn
    _ ≤ 1 * ((1 / (1 - δ)) * 1) := by
        apply mul_le_mul hsa_le _ (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_left hsb_le hinv_nn
    _ = 1 / (1 - δ) := by ring

set_option linter.unusedSectionVars false in
private lemma cometric_dualsum_inner_collapse (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a c : TangentSpace I x) :
    (∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x c ((Module.finBasis ℝ E) k) *
          g₀.inner x a (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))) =
      g₀.inner x a (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x c)) := by
  classical
  have hsumeq := cometric_sum_eq_invSharp (I := I) g₀ g₁ x c
  calc (∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x c ((Module.finBasis ℝ E) k) *
          g₀.inner x a (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))
      = ∑ k : Fin (Module.finrank ℝ E), g₀.inner x a
          (g₀.inner x c ((Module.finBasis ℝ E) k) •
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    _ = g₀.inner x a
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x c ((Module.finBasis ℝ E) k) •
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) := (map_sum (g₀.inner x a) _ _).symm
    _ = g₀.inner x a (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x c)) := by
        rw [hsumeq]

private lemma ricciArm_compSq_le_indicator {A C R : ℝ} (hAbound : |A| ≤ R) (hCbound : |C| ≤ R)
    {nn : ℕ} (K : Fin 4 → Fin nn) (J : Fin 2 → Fin nn) :
    ((1 / 2 : ℝ) *
        (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
          + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
          - C * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)))) ^ 2
      ≤ (3 / 4 : ℝ) * R ^ 2 *
          ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0)
            + (if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0)
            + (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
  classical
  set χa : ℝ := (if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0) with hχa
  set χb : ℝ := (if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0) with hχb
  set χc : ℝ := (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0) with hχc
  have hχa01 : χa = 0 ∨ χa = 1 := by
    rw [hχa]; by_cases h1 : K 1 = J 0 <;> by_cases h2 : K 2 = J 1 <;> simp [h1, h2]
  have hχb01 : χb = 0 ∨ χb = 1 := by
    rw [hχb]; by_cases h1 : K 1 = J 1 <;> by_cases h2 : K 2 = J 0 <;> simp [h1, h2]
  have hχc01 : χc = 0 ∨ χc = 1 := by
    rw [hχc]; by_cases h1 : K 2 = J 0 <;> by_cases h2 : K 3 = J 1 <;> simp [h1, h2]
  have hA2 : A ^ 2 ≤ R ^ 2 := by
    have := sq_abs A; nlinarith [hAbound, abs_nonneg A]
  have hC2 : C ^ 2 ≤ R ^ 2 := by
    have := sq_abs C; nlinarith [hCbound, abs_nonneg C]
  have hR2nn : 0 ≤ R ^ 2 := sq_nonneg R
  rcases hχa01 with ha | ha <;> rcases hχb01 with hb | hb <;> rcases hχc01 with hc | hc <;>
    rw [ha, hb, hc] <;> nlinarith [hA2, hC2, hR2nn, sq_nonneg (A - C),
      sq_nonneg (A + A), sq_nonneg (A + A - C), sq_nonneg A, sq_nonneg C]

private lemma ricciArm_indicatorSum_le {nn : ℕ} (K : Fin 4 → Fin nn) (R : ℝ) :
    (∑ J : Fin 2 → Fin nn,
        (3 / 4 : ℝ) * R ^ 2 *
          ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0)
            + (if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0)
            + (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)))
      ≤ (9 / 4 : ℝ) * R ^ 2 := by
  classical
  have hpair : ∀ (a b : Fin nn),
      (∑ J : Fin 2 → Fin nn,
        (if a = J 0 then (1 : ℝ) else 0) * (if b = J 1 then (1 : ℝ) else 0)) = 1 := by
    intro a b
    rw [← (finTwoArrowEquiv (Fin nn)).symm.sum_comp
      (fun J : Fin 2 → Fin nn =>
        (if a = J 0 then (1 : ℝ) else 0) * (if b = J 1 then (1 : ℝ) else 0))]
    rw [Fintype.sum_prod_type]
    simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hin : ∀ j0 : Fin nn,
        (∑ j1 : Fin nn, (if a = j0 then (1 : ℝ) else 0) * (if b = j1 then (1 : ℝ) else 0))
          = (if a = j0 then (1 : ℝ) else 0) := by
      intro j0
      rw [← Finset.mul_sum, Finset.sum_ite_eq Finset.univ b (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun j0 _ => hin j0)]
    rw [Finset.sum_ite_eq Finset.univ a (fun _ => (1 : ℝ))]; simp
  have hpairSwap : ∀ (a b : Fin nn),
      (∑ J : Fin 2 → Fin nn,
        (if a = J 1 then (1 : ℝ) else 0) * (if b = J 0 then (1 : ℝ) else 0)) = 1 := by
    intro a b
    rw [← (finTwoArrowEquiv (Fin nn)).symm.sum_comp
      (fun J : Fin 2 → Fin nn =>
        (if a = J 1 then (1 : ℝ) else 0) * (if b = J 0 then (1 : ℝ) else 0))]
    rw [Fintype.sum_prod_type]
    simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hin : ∀ j0 : Fin nn,
        (∑ j1 : Fin nn, (if a = j1 then (1 : ℝ) else 0) * (if b = j0 then (1 : ℝ) else 0))
          = (if b = j0 then (1 : ℝ) else 0) := by
      intro j0
      rw [← Finset.sum_mul, Finset.sum_ite_eq Finset.univ a (fun _ => (1 : ℝ))]; simp
    rw [Finset.sum_congr rfl (fun j0 _ => hin j0)]
    rw [Finset.sum_ite_eq Finset.univ b (fun _ => (1 : ℝ))]; simp
  rw [← Finset.mul_sum]
  have hsum3 : (∑ J : Fin 2 → Fin nn,
        ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0)
          + (if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0)
          + (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) = 3 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hpair (K 1) (K 2), hpairSwap (K 1) (K 2), hpair (K 2) (K 3)]; norm_num
  rw [hsum3]
  have hfinal : (9 / 4 : ℝ) * R ^ 2 = (3 / 4 : ℝ) * R ^ 2 * 3 := by ring
  rw [hfinal]

private lemma ricciArm_dim1_compSq_le {A C R : ℝ} (hAbound : |A| ≤ R)
    (hAeqC : A = C)
    (hfr : Module.finrank ℝ E = 1) (K : Fin 4 → Fin (Module.finrank ℝ E)) :
    (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
            + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
            - C * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)))) ^ 2)
      ≤ R ^ 2 := by
  classical
  have hAR : 0 ≤ R := le_trans (abs_nonneg A) hAbound
  have hsub : Subsingleton (Fin (Module.finrank ℝ E)) := by
    rw [hfr]; infer_instance
  have hKJ : ∀ (a b : Fin (Module.finrank ℝ E)), (if a = b then (1 : ℝ) else 0) = 1 := by
    intro a b; rw [if_pos (Subsingleton.elim a b)]
  have hcard : Fintype.card (Fin 2 → Fin (Module.finrank ℝ E)) = 1 := by
    rw [Fintype.card_fun, Fintype.card_fin, hfr]; norm_num
  have hACeq : (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
            + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
            - C * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)))) ^ 2)
      = ∑ _J : Fin 2 → Fin (Module.finrank ℝ E), ((1 / 2 : ℝ) * A) ^ 2 := by
    refine Finset.sum_congr rfl (fun J _ => ?_)
    simp only [hKJ]
    rw [← hAeqC]
    ring_nf
  rw [hACeq, Finset.sum_const]
  simp only [Finset.card_univ, hcard, one_smul]
  have hA2 : A ^ 2 ≤ R ^ 2 := by
    have := sq_abs A; nlinarith [hAbound, abs_nonneg A]
  nlinarith [hA2, sq_nonneg A]

set_option linter.unusedSectionVars false in
theorem ricciArmPrincipalCoeffFib_fiberComponent_Ksum_sq_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ h δ) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 4 → Fin (Module.finrank ℝ E)) :
    (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM (ricciArmPrincipalCoeffFib (I := I) g₁ x))
        (Module.finrank ℝ E) e K J) ^ 2)
      ≤ ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ))) ^ 2 := by
  classical
  set R : ℝ := 1 / (1 - δ) with hR
  have hcoeff : 0 < 1 - δ := by linarith
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  set fA : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 3))) with hfA
  set fC : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1))) with hfC
  set A : ℝ := g₀.inner x (e (K 0)) fA with hA
  set C : ℝ := g₀.inner x (e (K 0)) fC with hC
  have hAbound : |A| ≤ R := by
    rw [hA, hR, hfA]
    refine abs_g0_inner_invSharp_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (e (K 0)) (e (K 3)) ?_ ?_
    · rw [horth (K 0) (K 0)]; simp
    · rw [horth (K 3) (K 3)]; simp
  have hCbound : |C| ≤ R := by
    rw [hC, hR, hfC]
    refine abs_g0_inner_invSharp_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (e (K 0)) (e (K 1)) ?_ ?_
    · rw [horth (K 0) (K 0)]; simp
    · rw [horth (K 1) (K 1)]; simp
  have hcomp : ∀ J : Fin 2 → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM (ricciArmPrincipalCoeffFib (I := I) g₁ x))
        (Module.finrank ℝ E) e K J =
      (1 / 2 : ℝ) *
        (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
          + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
          - C * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) := by
    intro J
    have hread : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM (ricciArmPrincipalCoeffFib (I := I) g₁ x))
        (Module.finrank ℝ E) e K J =
        Tensor0SSpace.toModel
          ((ricciArmPrincipalCoeffFib (I := I) g₁ x) (coframeS (I := I) (M := M) g₀ x 4 e K))
          (fun k => e (J k)) := by
      unfold fiberNormSqComponent coframeS; rfl
    rw [hread, ricciArmPrincipalCoeffFib_toModel,
      combinedTrace42Model_apply (E := E) (cometricLmodel (I := I) g₁ x) _ (fun k => e (J k))]
    have hev : ∀ (v : Fin 4 → E),
        Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K) v =
          ∏ i : Fin 4, g₀.inner x (e (K i)) (v i) :=
      fun v => coframeS_apply (I := I) (M := M) g₀ x 4 e K v
    have hterm : ∀ k : Fin (Module.finrank ℝ E),
        (Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)
            (Fin.cons (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![e (J 0), e (J 1), (Module.finBasis ℝ E) k])
          + Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![e (J 1), e (J 0), (Module.finBasis ℝ E) k])
          - Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (J l))))) =
          g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 1)) (e (J 0)) * g₀.inner x (e (K 2)) (e (J 1))))
          + g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 1)) (e (J 1)) * g₀.inner x (e (K 2)) (e (J 0))))
          - g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 2)) (e (J 0)) * g₀.inner x (e (K 3)) (e (J 1)))) := by
      intro k
      have hthird : (Fin.cons ((Module.finBasis ℝ E) k) (fun l : Fin 2 => e (J l)) :
          Fin 3 → E) = ![(Module.finBasis ℝ E) k, e (J 0), e (J 1)] := by
        funext i; fin_cases i <;> rfl
      rw [hev, hev, hev, hthird, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_four]
      have hcons4 : ∀ (c : E) (a b d : E),
          (Fin.cons c ![a, b, d] : Fin 4 → E) 0 = c ∧
          (Fin.cons c ![a, b, d] : Fin 4 → E) 1 = a ∧
          (Fin.cons c ![a, b, d] : Fin 4 → E) 2 = b ∧
          (Fin.cons c ![a, b, d] : Fin 4 → E) 3 = d := by
        intro c a b d
        refine ⟨rfl, ?_, ?_, ?_⟩ <;> rfl
      obtain ⟨t1_0, t1_1, t1_2, t1_3⟩ := hcons4 (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (e (J 0)) (e (J 1)) ((Module.finBasis ℝ E) k)
      obtain ⟨t2_0, t2_1, t2_2, t2_3⟩ := hcons4 (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (e (J 1)) (e (J 0)) ((Module.finBasis ℝ E) k)
      obtain ⟨t3_0, t3_1, t3_2, t3_3⟩ := hcons4 (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k) (e (J 0)) (e (J 1))
      rw [t1_0, t1_1, t1_2, t1_3, t2_0, t2_1, t2_2, t2_3, t3_0, t3_1, t3_2, t3_3]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hcolA : (∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
            (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) *
              (g₀.inner x (e (K 1)) (e (J 0)) * g₀.inner x (e (K 2)) (e (J 1)))))
        = A * (g₀.inner x (e (K 1)) (e (J 0)) * g₀.inner x (e (K 2)) (e (J 1))) := by
      rw [show (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 1)) (e (J 0)) * g₀.inner x (e (K 2)) (e (J 1))))) =
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))) *
            (g₀.inner x (e (K 1)) (e (J 0)) * g₀.inner x (e (K 2)) (e (J 1))) from by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); ring]
      rw [cometric_dualsum_inner_collapse (I := I) g₀ g₁ x (e (K 0)) (e (K 3)), ← hfA, ← hA]
    have hcolB : (∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
            (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) *
              (g₀.inner x (e (K 1)) (e (J 1)) * g₀.inner x (e (K 2)) (e (J 0)))))
        = A * (g₀.inner x (e (K 1)) (e (J 1)) * g₀.inner x (e (K 2)) (e (J 0))) := by
      rw [show (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 1)) (e (J 1)) * g₀.inner x (e (K 2)) (e (J 0))))) =
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))) *
            (g₀.inner x (e (K 1)) (e (J 1)) * g₀.inner x (e (K 2)) (e (J 0))) from by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); ring]
      rw [cometric_dualsum_inner_collapse (I := I) g₀ g₁ x (e (K 0)) (e (K 3)), ← hfA, ← hA]
    have hcolC : (∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
            (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) *
              (g₀.inner x (e (K 2)) (e (J 0)) * g₀.inner x (e (K 3)) (e (J 1)))))
        = C * (g₀.inner x (e (K 2)) (e (J 0)) * g₀.inner x (e (K 3)) (e (J 1))) := by
      rw [show (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 2)) (e (J 0)) * g₀.inner x (e (K 3)) (e (J 1))))) =
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
              g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))) *
            (g₀.inner x (e (K 2)) (e (J 0)) * g₀.inner x (e (K 3)) (e (J 1))) from by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); ring]
      rw [cometric_dualsum_inner_collapse (I := I) g₀ g₁ x (e (K 0)) (e (K 1)), ← hfC, ← hC]
    rw [hcolA, hcolB, hcolC, horth (K 1) (J 0), horth (K 2) (J 1), horth (K 1) (J 1),
      horth (K 2) (J 0), horth (K 3) (J 1)]
  rw [Finset.sum_congr rfl (fun J _ => by rw [hcomp J])]
  have hbound9 : (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
            + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
            - C * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)))) ^ 2)
      ≤ ((Module.finrank ℝ E : ℝ) * R) ^ 2 := by
    rcases Nat.lt_or_ge (Module.finrank ℝ E) 2 with hlt2 | hge2
    · have hfr : Module.finrank ℝ E = 1 := by
        have h1 : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
        omega
      have hAeqC : A = C := by
        have hsub : Subsingleton (Fin (Module.finrank ℝ E)) := by rw [hfr]; infer_instance
        have hK13 : K 1 = K 3 := Subsingleton.elim _ _
        rw [hA, hC, hfA, hfC, hK13]
      refine (ricciArm_dim1_compSq_le (A := A) (C := C) (R := R) hAbound hAeqC hfr
        (K := K)).trans ?_
      have hfrR : (Module.finrank ℝ E : ℝ) = 1 := by rw [hfr]; norm_num
      rw [hfrR]; rw [one_mul]
    · have hstep : (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
            ((1 / 2 : ℝ) *
              (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
                + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
                - C * ((if K 2 = J 0 then (1 : ℝ) else 0) *
                  (if K 3 = J 1 then (1 : ℝ) else 0)))) ^ 2)
          ≤ (9 / 4 : ℝ) * R ^ 2 :=
        (Finset.sum_le_sum (fun J _ =>
          ricciArm_compSq_le_indicator (A := A) (C := C) (R := R) hAbound hCbound
            (K := K) (J := J))).trans (ricciArm_indicatorSum_le (K := K) (R := R))
      refine hstep.trans ?_
      have hge2R : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hge2
      have hfin2 : (4 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by nlinarith [hge2R]
      nlinarith [hfin2, hRnn, sq_nonneg R, mul_le_mul_of_nonneg_right hfin2 (sq_nonneg R)]
  exact hbound9

set_option linter.unusedSectionVars false in
theorem riemannianFiberNormSq_ricciArmPrincipalCoeffFib_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ h δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM (ricciArmPrincipalCoeffFib (I := I) g₁ x))
      ≤ ((Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ))) ^ 2 := by
  have hbound := rfns_le_of_Ksum_sq_le (I := I) (M := M) g₀ 4 2 x
    (show TensorRSSpace 4 2 I x from
      TensorRSSpace.ofCLM (ricciArmPrincipalCoeffFib (I := I) g₁ x))
    ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ)))
    (fun e horth K =>
      ricciArmPrincipalCoeffFib_fiberComponent_Ksum_sq_le (I := I) (M := M) g₀ g₁ h htie hδ_lt
        hδ_nn hδ x e horth K)
  refine hbound.trans (le_of_eq ?_)
  ring

set_option linter.unusedSectionVars false in
theorem traceHessianFib_fiberComponent_Ksum_sq_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ h δ) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 4 → Fin (Module.finrank ℝ E)) :
    (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x)
        (Module.finrank ℝ E) e K J) ^ 2)
      ≤ ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ))) ^ 2 := by
  classical
  set R : ℝ := 1 / (1 - δ) with hR
  set fK3 : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 3))) with hfK3
  have hcomp : ∀ J : Fin 2 → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x) (Module.finrank ℝ E) e K J =
      (if K 0 = J 0 then (1 : ℝ) else 0) * (if K 1 = J 1 then (1 : ℝ) else 0) *
        g₀.inner x (e (K 2)) fK3 := by
    intro J
    have hread : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x) (Module.finrank ℝ E) e K J =
        Tensor0SSpace.toModel
          ((traceHessianFib (I := I) g₁ x) (coframeS (I := I) (M := M) g₀ x 4 e K))
          (fun k => e (J k)) := by
      unfold fiberNormSqComponent coframeS; rfl
    rw [hread, traceHessianFib_toModel]
    rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x) _ (fun k => e (J k))]
    have hterm : ∀ k : Fin (Module.finrank ℝ E),
        (ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
            (Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)))
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (J l)))) =
          g₀.inner x (e (K 0)) (e (J 0)) * g₀.inner x (e (K 1)) (e (J 1)) *
            (g₀.inner x (e (K 2)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) *
              g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k)) := by
      intro k
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      set base : Fin 4 → E :=
        Fin.cons (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (J l))) with hbase
      have hcfeval : Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)
            (fun i => base (traceHessianSlotPerm i)) =
          ∏ i : Fin 4, g₀.inner x (e (K i)) (base (traceHessianSlotPerm i)) :=
        coframeS_apply (I := I) (M := M) g₀ x 4 e K (fun i => base (traceHessianSlotPerm i))
      rw [hcfeval, Fin.prod_univ_four]
      have hp0 : traceHessianSlotPerm 0 = 2 := by decide
      have hp1 : traceHessianSlotPerm 1 = 3 := by decide
      have hp2 : traceHessianSlotPerm 2 = 0 := by decide
      have hp3 : traceHessianSlotPerm 3 = 1 := by decide
      have hb0 : base 0 = cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)) := by rw [hbase, Fin.cons_zero]
      have hb1 : base 1 = (Module.finBasis ℝ E) k := by
        rw [hbase]
        rw [show (1 : Fin 4) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
      have hb2 : base 2 = e (J 0) := by
        rw [hbase]
        rw [show (2 : Fin 4) = Fin.succ 1 from rfl, Fin.cons_succ,
          show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ]
      have hb3 : base 3 = e (J 1) := by
        rw [hbase]
        rw [show (3 : Fin 4) = Fin.succ 2 from rfl, Fin.cons_succ,
          show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]
      rw [hp0, hp1, hp2, hp3, hb0, hb1, hb2, hb3]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x (e (K 0)) (e (J 0)) * g₀.inner x (e (K 1)) (e (J 1)) *
          (g₀.inner x (e (K 2)) (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) *
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k))) =
        g₀.inner x (e (K 0)) (e (J 0)) * g₀.inner x (e (K 1)) (e (J 1)) *
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              g₀.inner x (e (K 2)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_); ring]
    have hcollapse : (∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
            g₀.inner x (e (K 2)) (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))) =
        g₀.inner x (e (K 2)) fK3 := by
      have hsumeq : (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) •
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) = fK3 := by
        rw [hfK3]; exact cometric_sum_eq_invSharp (I := I) g₀ g₁ x (e (K 3))
      calc (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              g₀.inner x (e (K 2)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
          = ∑ k : Fin (Module.finrank ℝ E), g₀.inner x (e (K 2))
              (g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) •
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [ContinuousLinearMap.map_smul, smul_eq_mul]
        _ = g₀.inner x (e (K 2))
              (∑ k : Fin (Module.finrank ℝ E), g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) •
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) := (map_sum (g₀.inner x (e (K 2))) _ _).symm
        _ = g₀.inner x (e (K 2)) fK3 := by rw [hsumeq]
    rw [hcollapse, horth (K 0) (J 0), horth (K 1) (J 1)]
  rw [Finset.sum_congr rfl (fun J _ => by rw [hcomp J])]
  have hKbound : |g₀.inner x (e (K 2)) fK3| ≤ R := by
    rw [hR, hfK3]
    refine abs_g0_inner_invSharp_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (e (K 2)) (e (K 3)) ?_ ?_
    · rw [horth (K 2) (K 2)]; simp
    · rw [horth (K 3) (K 3)]; simp
  have hsingle : (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        ((if K 0 = J 0 then (1 : ℝ) else 0) * (if K 1 = J 1 then (1 : ℝ) else 0) *
          g₀.inner x (e (K 2)) fK3) ^ 2)
      ≤ g₀.inner x (e (K 2)) fK3 ^ 2 := by
    have hbij : (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          ((if K 0 = J 0 then (1 : ℝ) else 0) * (if K 1 = J 1 then (1 : ℝ) else 0) *
            g₀.inner x (e (K 2)) fK3) ^ 2)
        = ∑ j0 : Fin (Module.finrank ℝ E), ∑ j1 : Fin (Module.finrank ℝ E),
            ((if K 0 = j0 then (1 : ℝ) else 0) * (if K 1 = j1 then (1 : ℝ) else 0) *
              g₀.inner x (e (K 2)) fK3) ^ 2 := by
      rw [← (finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm.sum_comp
        (fun J : Fin 2 → Fin (Module.finrank ℝ E) =>
          ((if K 0 = J 0 then (1 : ℝ) else 0) * (if K 1 = J 1 then (1 : ℝ) else 0) *
            g₀.inner x (e (K 2)) fK3) ^ 2)]
      rw [Fintype.sum_prod_type]; rfl
    rw [hbij]
    have hcollapse2 : ∀ j0 j1 : Fin (Module.finrank ℝ E),
        ((if K 0 = j0 then (1 : ℝ) else 0) * (if K 1 = j1 then (1 : ℝ) else 0) *
          g₀.inner x (e (K 2)) fK3) ^ 2 =
        (if K 0 = j0 then (1 : ℝ) else 0) * (if K 1 = j1 then (1 : ℝ) else 0) *
          g₀.inner x (e (K 2)) fK3 ^ 2 := by
      intro j0 j1
      by_cases h0 : K 0 = j0 <;> by_cases h1 : K 1 = j1 <;> simp [h0, h1]
    rw [Finset.sum_congr rfl (fun j0 _ => Finset.sum_congr rfl (fun j1 _ => hcollapse2 j0 j1))]
    have hinner : ∀ j0 : Fin (Module.finrank ℝ E),
        (∑ j1 : Fin (Module.finrank ℝ E),
          (if K 0 = j0 then (1 : ℝ) else 0) * (if K 1 = j1 then (1 : ℝ) else 0) *
            g₀.inner x (e (K 2)) fK3 ^ 2)
        = (if K 0 = j0 then (1 : ℝ) else 0) * (g₀.inner x (e (K 2)) fK3 ^ 2) := by
      intro j0
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [Finset.sum_ite_eq Finset.univ (K 1) (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun j0 _ => hinner j0)]
    rw [← Finset.sum_mul, Finset.sum_ite_eq Finset.univ (K 0) (fun _ => (1 : ℝ))]
    simp
  refine hsingle.trans ?_
  have hcoeff : 0 < 1 - δ := by linarith
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  have hKsq : g₀.inner x (e (K 2)) fK3 ^ 2 ≤ R ^ 2 := by
    have habs := sq_abs (g₀.inner x (e (K 2)) fK3)
    nlinarith [hKbound, abs_nonneg (g₀.inner x (e (K 2)) fK3)]
  refine hKsq.trans ?_
  have hn_ge : (1 : ℝ) ≤ ((Module.finrank ℝ E : ℝ)) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
  have hRle : R ≤ ((Module.finrank ℝ E : ℝ)) * R := by
    nlinarith [mul_le_mul_of_nonneg_right hn_ge hRnn]
  have hfinR_nn : 0 ≤ ((Module.finrank ℝ E : ℝ)) * R := by positivity
  nlinarith [hRle, hRnn, hfinR_nn, mul_le_mul hRle hRle hRnn hfinR_nn]

set_option linter.unusedSectionVars false in
theorem riemannianFiberNormSq_traceHessianFib_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ h δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x)
      ≤ ((Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ))) ^ 2 := by
  have hbound := rfns_le_of_Ksum_sq_le (I := I) (M := M) g₀ 4 2 x
    (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x)
    ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ)))
    (fun e horth K =>
      traceHessianFib_fiberComponent_Ksum_sq_le (I := I) (M := M) g₀ g₁ h htie hδ_lt
        hδ_nn hδ x e horth K)
  refine hbound.trans (le_of_eq ?_)
  ring

set_option linter.unusedSectionVars false in
private lemma cometricDoubleTraceFib_fiberComponent_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 3 → Fin (Module.finrank ℝ E)) (J : Fin 1 → Fin (Module.finrank ℝ E)) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 3 1
        (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
        (Module.finrank ℝ E) e K J =
      (if K 2 = J 0 then (1 : ℝ) else 0) *
        g₀.inner x (e (K 0))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1)))) := by
  classical
  have hread : fiberNormSqComponent (I := I) (M := M) g₀ x 3 1
        (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
        (Module.finrank ℝ E) e K J =
      Tensor0SSpace.toModel
        ((cometricDoubleTraceFib (I := I) g₁ 1 x) (coframeS (I := I) (M := M) g₀ x 3 e K))
        (fun k => e (J k)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hread, cometricDoubleTraceFib_toModel]
  rw [modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g₁ x) _ (fun k => e (J k))]
  have hterm : ∀ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
        (Fin.cons (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (J l)))) =
        g₀.inner x (e (K 2)) (e (J 0)) *
          (g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
            g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))) := by
    intro k
    set base : Fin 3 → E :=
      Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (J l))) with hbase
    have hcfeval : Tensor0SBundle.Tensor0SSpace.toModel
          (coframeS (I := I) (M := M) g₀ x 3 e K) base =
        ∏ i : Fin 3, g₀.inner x (e (K i)) (base i) :=
      coframeS_apply (I := I) (M := M) g₀ x 3 e K base
    rw [hcfeval, Fin.prod_univ_three]
    have hb0 : base 0 = cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) := by rw [hbase, Fin.cons_zero]
    have hb1 : base 1 = (Module.finBasis ℝ E) k := by
      rw [hbase, show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
    have hb2 : base 2 = e (J 0) := by
      rw [hbase, show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ,
        show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
    rw [hb0, hb1, hb2]; ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hpull : (∑ k : Fin (Module.finrank ℝ E),
      g₀.inner x (e (K 2)) (e (J 0)) *
        (g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
          g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))) =
      g₀.inner x (e (K 2)) (e (J 0)) *
        (∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
            g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))) := by
    rw [Finset.mul_sum]
  rw [hpull, cometric_dualsum_inner_collapse (I := I) g₀ g₁ x (e (K 0)) (e (K 1)),
    horth (K 2) (J 0)]

set_option linter.unusedSectionVars false in
private lemma cometricDoubleTraceFib_fiberComponent_Ksum_sq_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ h δ) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 3 → Fin (Module.finrank ℝ E)) :
    (∑ J : Fin 1 → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 3 1
        (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
        (Module.finrank ℝ E) e K J) ^ 2)
      ≤ (1 / (1 - δ)) ^ 2 := by
  classical
  set R : ℝ := 1 / (1 - δ) with hR
  set q : ℝ := g₀.inner x (e (K 0))
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1)))) with hq
  have hqbound : |q| ≤ R := by
    rw [hR, hq]
    refine abs_g0_inner_invSharp_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x
      (e (K 0)) (e (K 1)) ?_ ?_
    · rw [horth (K 0) (K 0)]; simp
    · rw [horth (K 1) (K 1)]; simp
  have hcomp : ∀ J : Fin 1 → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 3 1
        (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
        (Module.finrank ℝ E) e K J =
      (if K 2 = J 0 then (1 : ℝ) else 0) * q := by
    intro J
    rw [cometricDoubleTraceFib_fiberComponent_eq (I := I) g₀ g₁ x e horth K J, hq]
  rw [Finset.sum_congr rfl (fun J _ => by rw [hcomp J])]
  have hsingle : (∑ J : Fin 1 → Fin (Module.finrank ℝ E),
        ((if K 2 = J 0 then (1 : ℝ) else 0) * q) ^ 2) ≤ q ^ 2 := by
    have hbij : (∑ J : Fin 1 → Fin (Module.finrank ℝ E),
          ((if K 2 = J 0 then (1 : ℝ) else 0) * q) ^ 2)
        = ∑ j0 : Fin (Module.finrank ℝ E),
            ((if K 2 = j0 then (1 : ℝ) else 0) * q) ^ 2 := by
      apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (Module.finrank ℝ E)))
      intro J; rfl
    rw [hbij]
    have hcollapse : ∀ j0 : Fin (Module.finrank ℝ E),
        ((if K 2 = j0 then (1 : ℝ) else 0) * q) ^ 2 =
        (if K 2 = j0 then (1 : ℝ) else 0) * q ^ 2 := by
      intro j0
      by_cases h0 : K 2 = j0 <;> simp [h0]
    rw [Finset.sum_congr rfl (fun j0 _ => hcollapse j0)]
    rw [← Finset.sum_mul, Finset.sum_ite_eq Finset.univ (K 2) (fun _ => (1 : ℝ))]
    simp
  refine hsingle.trans ?_
  have hcoeff : 0 < 1 - δ := by linarith
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  have hqsq : q ^ 2 ≤ R ^ 2 := by
    have habs := sq_abs q
    nlinarith [hqbound, abs_nonneg q]
  exact hqsq

set_option linter.unusedSectionVars false in
private lemma riemannianFiberNormSq_cometricDoubleTraceFib_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ h δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
        (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
      ≤ ((Module.finrank ℝ E : ℝ) ^ 3) * (1 / (1 - δ)) ^ 2 := by
  exact rfns_le_of_Ksum_sq_le (I := I) (M := M) g₀ 3 1 x
    (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
    (1 / (1 - δ))
    (fun e horth K =>
      cometricDoubleTraceFib_fiberComponent_Ksum_sq_le (I := I) g₀ g₁ h htie hδ_lt
        hδ_nn hδ x e horth K)

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private lemma jetEnvelope_covGrad_one_le (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (x : M) (B : ℝ)
    (henv : (∑ j ∈ Finset.range 3,
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B) :
    (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
    ‖(iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x‖) ≤ B := by
  refine le_trans ?_ henv
  exact Finset.single_le_sum (f := fun j =>
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)
      (fun j _ =>
        letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
        norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x))
      (by simp : (1 : ℕ) ∈ Finset.range 3)

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_perMetric_linearizedRicciArm1Fib_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ max δ₀ 0)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              (show TensorRSSpace 3 2 I x from
                linearizedRicciArm1Fib (I := I) g₀ g₁ x) ≤ Λ := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ (by norm_num)
  obtain ⟨Ckos, hCkos_nn, hKos⟩ :=
    rfns_raisedKoszul_le_of_lt_one (I := I) (M := M) g₀ hδ₁_nn hδ₁_lt
  refine ⟨Ckos ^ 2 * B ^ 2 * ((Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ₁)) ^ 2),
    by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv
  set δ' : ℝ := max δ 0 with hδ'_def
  have hδ'_nn : 0 ≤ δ' := le_max_right _ _
  have hδ'_le_δ₁ : δ' ≤ δ₁ := by
    rw [hδ'_def]
    exact (max_le_max hδ_le (le_refl 0)).trans (le_of_eq (max_eq_left hδ₁_nn))
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le_δ₁ hδ₁_lt
  have hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ' :=
    gFibreOpBound_mono_local (I := I) g₀ _ (le_max_left _ _) hδ
  have hcoeff₁ : 0 < 1 - δ₁ := by linarith
  have hcoeff' : 0 < 1 - δ' := by linarith
  have hcomp := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 3 1 2 x
    (raisedKoszulFib (I := I) g₀ g₁ x) (cometricDoubleTraceFib (I := I) g₁ 1 x)
  have hlin_eq : (show TensorRSSpace 3 2 I x from linearizedRicciArm1Fib (I := I) g₀ g₁ x) =
      (show TensorRSSpace 3 2 I x from
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            raisedKoszulFib (I := I) g₀ g₁ x).comp
          (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 1 I x from
            cometricDoubleTraceFib (I := I) g₁ 1 x)) := rfl
  rw [hlin_eq]
  refine hcomp.trans ?_
  letI instTens12 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  set N : ℝ := ‖(iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  have hnorm_le : N ≤ B := jetEnvelope_covGrad_one_le (I := I) g₀ P x B henv
  have hsq : N ^ 2 ≤ B ^ 2 := by nlinarith [hnorm_le, hN_nn, hB]
  have hkosB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
      (raisedKoszulFib (I := I) g₀ g₁ x) ≤ Ckos ^ 2 * B ^ 2 := by
    have hKosx := hKos g₁ P htie hδ'_le_δ₁ hδ'_nn hδ' x
    rw [raisedKoszul_toSection] at hKosx
    refine hKosx.trans ?_
    have hCkos_sq_nn : 0 ≤ Ckos ^ 2 := sq_nonneg _
    have hgoal : Ckos ^ 2 * N ^ 2 ≤ Ckos ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hCkos_sq_nn
    exact hgoal
  have hcometB : riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
      (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ₁)) ^ 2 := by
    have hcm := riemannianFiberNormSq_cometricDoubleTraceFib_le (I := I) g₀ g₁
      (ccTensorBilinSymm (I := I) g₀ P) htie hδ'_lt hδ'_nn hδ' x
    refine hcm.trans ?_
    have hmono : 1 / (1 - δ') ≤ 1 / (1 - δ₁) :=
      div_le_div_of_nonneg_left (by norm_num) hcoeff₁ (by linarith)
    have hinv_nn : 0 ≤ 1 / (1 - δ') := by positivity
    have hsq_le : (1 / (1 - δ')) ^ 2 ≤ (1 / (1 - δ₁)) ^ 2 := by
      have hinv₁_nn : 0 ≤ 1 / (1 - δ₁) := by positivity
      nlinarith [hmono, hinv_nn, hinv₁_nn]
    have hfin_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_left hsq_le hfin_nn
  have hrfns_kos_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
      (raisedKoszulFib (I := I) g₀ g₁ x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 2 x _
  have hrfns_com_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
      (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 1 x _
  have hCkosB_nn : 0 ≤ Ckos ^ 2 * B ^ 2 := by positivity
  have hfinal : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        (raisedKoszulFib (I := I) g₀ g₁ x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
          (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
      ≤ Ckos ^ 2 * B ^ 2 *
          ((Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ₁)) ^ 2) :=
    mul_le_mul hkosB hcometB hrfns_com_nn hCkosB_nn
  exact hfinal

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_rfns_linearizedRicciArm1Fib_realizedFam_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              (show TensorRSSpace 3 2 I x from
                linearizedRicciArm1Fib (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) x) ≤ Λ := by
  classical
  obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
    exists_perMetric_linearizedRicciArm1Fib_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨Λ, hΛ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w := by
    intro y v w
    rw [hg₁, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w]
  have hδs_raw : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      (|1 - s| * δ' + |s| * δ) :=
    convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ' + |s| * δ = (1 - s) * δ' + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ' + s * δ ≤ δ₁ := by
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ :=
      mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ :=
      mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ δ₁ := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have hδs : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) δ₁ := by
    intro y v w
    refine le_trans (hδs_raw y v w) ?_
    have hsv : 0 ≤ Real.sqrt (g₀.inner y v v) := Real.sqrt_nonneg _
    have hsw : 0 ≤ Real.sqrt (g₀.inner y w w) := Real.sqrt_nonneg _
    have hprod : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) :=
      mul_nonneg hsv hsw
    have hle' : |1 - s| * δ' + |s| * δ ≤ δ₁ := by rw [habs_eq]; exact hsmall_le
    nlinarith [hle', hprod]
  exact hΛ g₁ (convexPerturbation (I := I) g₀ T T' s) (le_of_eq hδ₁_def) hδs htie x henv

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_arm1Koszul_realizedFam_pointwise_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λarm1 : ℝ, 0 ≤ Λarm1 ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λarm1 := by
  classical
  obtain ⟨Λarm1, hΛarm1_nn, hΛarm1⟩ :=
    exists_rfns_linearizedRicciArm1Fib_realizedFam_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨Λarm1, hΛarm1_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  rw [ricciArmOrder1KoszulCoeff_toSection]
  exact hΛarm1 T T' hδ_le hδ hδ'_le hδ' s hs x henv

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in

theorem exists_arm1Koszul_realizedFam_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λarm1 : ℝ, 0 ≤ Λarm1 ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λarm1 := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_Csob_convexPerturbation_pointwise_C2_le
      (I := I) (M := M) g₀ a ha_super
  obtain ⟨Λarm1, hΛarm1_nn, hΛarm1⟩ :=
    exists_arm1Koszul_realizedFam_pointwise_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀
      (Csob * R) (by positivity)
  refine ⟨Λarm1, hΛarm1_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  refine hΛarm1 T T' hδ_le hδ hδ'_le hδ' s hs x ?_
  exact hCsob T T' hR hTball hT'ball s hs x

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannArm0_curvCoeff_realizedFam_pointwise_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ Λcurv : ℝ, 0 ≤ Λcurv ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j
                (convexPerturbation (I := I) g₀ T T' s)).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcurv ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcurv := by
  classical
  obtain ⟨Λ1, hΛ1_nn, hΛ1⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_rfns_riemannBiContrFib_realizedFam_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  obtain ⟨Λ2, hΛ2_nn, hΛ2⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_rfns_ricciArmOrder0CurvCoeffFib_realizedFam_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨max Λ1 Λ2, le_trans hΛ1_nn (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' s hs x henv
  refine ⟨?_, ?_⟩
  · rw [ricciArmOrder0RiemannCoeff_toSection]
    exact le_trans (hΛ1 T T' hδ_le hδ hδ'_le hδ' s hs x henv) (le_max_left _ _)
  · rw [ricciArmOrder0CurvCoeff_toSection]
    exact le_trans (hΛ2 T T' hδ_le hδ hδ'_le hδ' s hs x henv) (le_max_right _ _)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in

theorem exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λcurv : ℝ, 0 ≤ Λcurv ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcurv ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcurv := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_Csob_convexPerturbation_pointwise_C2_le
      (I := I) (M := M) g₀ a ha_super
  obtain ⟨Λcurv, hΛcurv_nn, hΛcurv⟩ :=
    exists_riemannArm0_curvCoeff_realizedFam_pointwise_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀
      (Csob * R) (by positivity)
  refine ⟨Λcurv, hΛcurv_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  refine hΛcurv T T' hδ_le hδ hδ'_le hδ' s hs x ?_
  exact hCsob T T' hR hTball hT'ball s hs x

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in

theorem exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λcom : ℝ, 0 ≤ Λcom ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcom ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((traceHessianCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λcom := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  have hcoeff : 0 < 1 - δ₁ := by linarith
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ₁))) ^ 2, sq_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  set hpert : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    fun y => ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y with hpert_def
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + hpert y v w := by
    intro y v w
    rw [hg₁, realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w]
  have hδs_raw : gFibreOpBound (I := I) (M := M) g₀ hpert (|1 - s| * δ' + |s| * δ) :=
    convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ' + |s| * δ = (1 - s) * δ' + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ' + s * δ ≤ δ₁ := by
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ :=
      mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ :=
      mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ δ₁ := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have hδs : gFibreOpBound (I := I) (M := M) g₀ hpert δ₁ := by
    refine gFibreOpBound_mono_local (I := I) g₀ hpert ?_ hδs_raw
    rw [habs_eq]; exact hsmall_le
  have hbP := riemannianFiberNormSq_ricciArmPrincipalCoeffFib_le
    (I := I) g₀ g₁ hpert htie hδ₁_lt hδ₁_nn hδs x
  have hbH := riemannianFiberNormSq_traceHessianFib_le
    (I := I) g₀ g₁ hpert htie hδ₁_lt hδ₁_nn hδs x
  refine ⟨?_, ?_⟩
  · rw [ricciArmPrincipalCoeff_toSection]; exact hbP
  · rw [traceHessianCoeff_toSection]; exact hbH

set_option linter.unusedVariables false in
def chartRicciTraceChristoffelSlope (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) j
        (fun y' => deriv (fun s : ℝ =>
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k j y') s₀) y -
      partialDeriv (E := E) k
        (fun y' => deriv (fun s : ℝ =>
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j j y') s₀) y +
      (∑ m : Fin (Module.finrank ℝ E),
        (deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j m j y) s₀ *
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i k m y +
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j m j y *
            deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k m y) s₀ -
          deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k m j y) s₀ *
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j m y -
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k m j y *
            deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j m y) s₀)))

theorem hasDerivAt_realizedFam_chartRiemannTensor_chartSlope (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun s : ℝ => chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k l y)
      (partialDeriv (E := E) j
          (fun y' => deriv (fun s : ℝ =>
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k l y') s₀) y -
        partialDeriv (E := E) k
          (fun y' => deriv (fun s : ℝ =>
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j l y') s₀) y +
        (∑ m : Fin (Module.finrank ℝ E),
          (deriv (fun s : ℝ =>
                chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j m l y) s₀ *
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i k m y +
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j m l y *
              deriv (fun s : ℝ =>
                chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k m y) s₀ -
            deriv (fun s : ℝ =>
                chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k m l y) s₀ *
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j m y -
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k m l y *
              deriv (fun s : ℝ =>
                chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j m y) s₀))) s₀ := by
  classical
  have heq : (fun s : ℝ =>
        chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k l y) =
      (fun s : ℝ =>
        partialDeriv (E := E) j
            (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k l) y -
          partialDeriv (E := E) k
            (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j l) y +
          (∑ m : Fin (Module.finrank ℝ E),
            (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j m l y *
                chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k m y -
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k m l y *
                chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j m y))) := by
    funext s; rw [chartRiemannTensor_def]
  rw [heq]
  have hPj := hasDerivAt_realizedFam_partial_chartChristoffel
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j i k l hy hs₀
  have hPk := hasDerivAt_realizedFam_partial_chartChristoffel
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x k i j l hy hs₀
  have hQuad : HasDerivAt
      (fun s : ℝ => ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j m l y *
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k m y -
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k m l y *
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j m y))
      (∑ m : Fin (Module.finrank ℝ E),
        (deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j m l y) s₀ *
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i k m y +
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j m l y *
            deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k m y) s₀ -
          deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k m l y) s₀ *
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j m y -
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k m l y *
            deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j m y) s₀)) s₀ := by
    refine HasDerivAt.fun_sum (fun m _ => ?_)
    have hC_jml := hasDerivAt_realizedFam_chartChristoffel
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x j m l hy hs₀
    have hC_ikm := hasDerivAt_realizedFam_chartChristoffel
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k m hy hs₀
    have hC_kml := hasDerivAt_realizedFam_chartChristoffel
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x k m l hy hs₀
    have hC_ijm := hasDerivAt_realizedFam_chartChristoffel
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j m hy hs₀
    have hprod1 := hC_jml.mul hC_ikm
    have hprod2 := hC_kml.mul hC_ijm
    have hsub := hprod1.sub hprod2
    refine hsub.congr_deriv ?_
    rw [hC_jml.deriv, hC_ikm.deriv, hC_kml.deriv, hC_ijm.deriv]
    ring
  exact (hPj.sub hPk).add hQuad

theorem deriv_chartRicciTrace_realizedFam_eq_chartSlope (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i k : Fin (Module.finrank ℝ E)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (∑ j : Fin (Module.finrank ℝ E),
        deriv (fun s' : ℝ =>
          chartRiemannTensor (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s') x i j k j (extChartAt I x x)) s₀) =
      chartRicciTraceChristoffelSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
        (extChartAt I x x) s₀ := by
  classical
  have hmem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  rw [chartRicciTraceChristoffelSlope]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact (hasDerivAt_realizedFam_chartRiemannTensor_chartSlope
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j k j hy hmem).deriv

set_option linter.unusedSectionVars false in
lemma unitModel_eq_ccTensorBilin_local (g₀ : SmoothRiemannianMetric I M)
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
theorem unitModel_basisChart_eq_tensorChartComponentRaw (g : SmoothRiemannianMetric I M)
    (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g s W x (fun k => chartModelBasis E (Jdx k)) =
      tensorChartComponentRaw (I := I) (M := M) g 0 s W x ![] Jdx x := by
  rw [tensorChartComponentRaw_def, tensorChartComponentProjection_apply]
  unfold tensorTrivProj
  rw [DifferentialGeometry.Tensor.tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
        (I := I) (M := M) 0 s x (b := x) rfl (mem_chart_source H x)
        (W.toSection x) (dualCovariantCMM (E := E) 0 ![])]
  unfold unitModel
  congr 2

set_option linter.unusedSectionVars false in
theorem unitModel_basisChart_eq_tensorChartComponent (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 2) (x : M) (k i : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g 2 W x ![chartModelBasis E k, chartModelBasis E i] =
      tensorChartComponentRaw (I := I) (M := M) g 0 2 W x ![] ![k, i] x := by
  have h := unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g 2 W x ![k, i]
  have hfun : (fun j : Fin 2 => chartModelBasis E (![k, i] j)) =
      ![chartModelBasis E k, chartModelBasis E i] := by
    funext j; fin_cases j <;> rfl
  rwa [hfun] at h

set_option linter.unusedSectionVars false in
theorem unitModel_basisChart_eq_tensorChartComponent4 (g : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g 0 4) (x : M) (Jdx : Fin 4 → Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g 4 W x
        ![chartModelBasis E (Jdx 0), chartModelBasis E (Jdx 1),
          chartModelBasis E (Jdx 2), chartModelBasis E (Jdx 3)] =
      tensorChartComponentRaw (I := I) (M := M) g 0 4 W x ![] Jdx x := by
  have h := unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g 4 W x Jdx
  have hfun : (fun j : Fin 4 => chartModelBasis E (Jdx j)) =
      ![chartModelBasis E (Jdx 0), chartModelBasis E (Jdx 1),
        chartModelBasis E (Jdx 2), chartModelBasis E (Jdx 3)] := by
    funext j; fin_cases j <;> rfl
  rwa [hfun] at h

set_option linter.unusedSectionVars false in
theorem cometricLmodel_covectorOfCLM_inner (g₁ : SmoothRiemannianMetric I M) (y : M)
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
theorem cometricLmodel_covectorOfCLM_cDualBasis_eq_chartBasis_sum
    (g₁ : SmoothRiemannianMetric I M) (x : M) (k : Fin (Module.finrank ℝ E)) :
    cometricLmodel (I := I) g₁ x (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((chartModelBasis E).cDualBasis k)) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k l • (chartModelBasis E l : TangentSpace I x) := by
  classical
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hself : ∀ t : Fin (Module.finrank ℝ E),
      chartBasisVecFiber (I := I) x t x = chartModelBasis E t := fun t =>
    chartBasisVecFiber_self (I := I) x t
  apply metricFlatLinear_injective (I := I) g₁ x
  ext u
  change g₁.inner x (cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) ((chartModelBasis E).cDualBasis k))) u =
    g₁.inner x (∑ l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₁ x x k l • (chartModelBasis E l : TangentSpace I x)) u
  rw [cometricLmodel_covectorOfCLM_inner (I := I) g₁ x ((chartModelBasis E).cDualBasis k) u]
  have hu : u = ∑ m : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u)) m •
        chartBasisVecFiber (I := I) x m x :=
    chartBasisVecFiber_recompose (I := I) x hxbase u
  set c : Fin (Module.finrank ℝ E) → ℝ := fun m =>
    ((chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u)) m with hc_def
  have hRHS_inner :
      g₁.inner x (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k l • (chartModelBasis E l : TangentSpace I x)) u =
        ∑ m : Fin (Module.finrank ℝ E),
          c m * (if k = m then (1 : ℝ) else 0) := by
    rw [map_sum, ContinuousLinearMap.sum_apply]
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            (g₁.inner x (chartInvGramMatrix (I := I) g₁ x x k l •
                (chartModelBasis E l : TangentSpace I x))) u =
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x) u from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x) u =
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x)
                (∑ m : Fin (Module.finrank ℝ E), c m • chartBasisVecFiber (I := I) x m x) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      refine congrArg (fun t : TangentSpace I x => chartInvGramMatrix (I := I) g₁ x x k l *
        g₁.inner x (chartModelBasis E l : TangentSpace I x) t) ?_
      exact hu
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x k l *
              g₁.inner x (chartModelBasis E l : TangentSpace I x)
                (∑ m : Fin (Module.finrank ℝ E), c m • chartBasisVecFiber (I := I) x m x) =
          ∑ l : Fin (Module.finrank ℝ E),
            (∑ m : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l * (c m *
                g₁.inner x (chartModelBasis E l : TangentSpace I x)
                  (chartBasisVecFiber (I := I) x m x))) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    rw [show ∑ m : Fin (Module.finrank ℝ E),
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l * (c m *
                g₁.inner x (chartModelBasis E l : TangentSpace I x)
                  (chartBasisVecFiber (I := I) x m x))) =
          ∑ m : Fin (Module.finrank ℝ E), c m *
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x k l *
                chartGramMatrix (I := I) g₁ x x l m) from ?_]
    swap
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [show g₁.inner x (chartModelBasis E l : TangentSpace I x)
              (chartBasisVecFiber (I := I) x m x) =
            chartGramMatrix (I := I) g₁ x x l m from ?_]
      · ring
      · rw [show (chartModelBasis E l : TangentSpace I x) =
            chartBasisVecFiber (I := I) x l x from (hself l).symm]
        rw [g_inner_eq_chartGramMatrix_basis (I := I) g₁ x x l m]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    refine congrArg (fun t : ℝ => c m * t) ?_
    have hkron : (∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k l *
            chartGramMatrix (I := I) g₁ x x l m) =
        (chartInvGramMatrix (I := I) g₁ x x * chartGramMatrix (I := I) g₁ x x) k m := by
      rw [Matrix.mul_apply]
    rw [hkron, chartInvGramMatrix_mul_chartGramMatrix (I := I) g₁ x hxbase, Matrix.one_apply]
  rw [hRHS_inner]
  rw [show (chartModelBasis E).cDualBasis k (u : E) =
        ∑ m : Fin (Module.finrank ℝ E), c m *
          (chartModelBasis E).cDualBasis k (chartBasisVecFiber (I := I) x m x : E) from ?_]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    refine congrArg (fun t : ℝ => c m * t) ?_
    rw [show (chartBasisVecFiber (I := I) x m x : E) = (chartModelBasis E m : E) from
        congrArg (fun v : TangentSpace I x => (v : E)) (hself m)]
    rw [Module.Basis.cDualBasis_apply_self (chartModelBasis E) k m]
  · conv_lhs => rw [show (u : E) = ((∑ m : Fin (Module.finrank ℝ E),
          c m • chartBasisVecFiber (I := I) x m x : TangentSpace I x) : E) from
        congrArg (fun v : TangentSpace I x => (v : E)) hu]
    rw [show ((∑ m : Fin (Module.finrank ℝ E),
            c m • chartBasisVecFiber (I := I) x m x : TangentSpace I x) : E) =
          ∑ m : Fin (Module.finrank ℝ E),
            c m • (chartBasisVecFiber (I := I) x m x : E) from ?_]
    · rw [map_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [map_smul, smul_eq_mul]
    · rfl

set_option linter.unusedSectionVars false in
theorem iteratedCovGrad2_chartComponent_readout (g₀ : SmoothRiemannianMetric I M)
    (h : SmoothCcTensor g₀ 0 2) (x : M)
    (Jdx : Fin (2 + 2) → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] Jdx
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm (toEuclidean (E := E) (extChartAt I x x)))) =
      euclidPartial (E := E) (Jdx 0)
          (fun y' =>
            euclidPartial (E := E) ((Matrix.vecTail Jdx) 0)
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
                  h x ![] (Matrix.vecTail (Matrix.vecTail Jdx)))) y'
              + covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x
                  ((Matrix.vecTail Jdx) 0) ![]
                  (Matrix.vecTail (Matrix.vecTail Jdx)) y')
          (toEuclidean (E := E) (extChartAt I x x))
        + covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2 h) x (Jdx 0) ![]
            (Matrix.vecTail Jdx) (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hy : toEuclidean (E := E) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x hmemsrc
  exact chartCovariantSecondGrad_chartHessian_sub_correction (I := I) (M := M) g₀ h x
    ![] Jdx hy

set_option linter.unusedSectionVars false in
lemma appCc_zero_left_local (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g 0 r) :
    appCc (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) W =
      (0 : SmoothCcTensor g 0 s) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCc_toSection]
  rw [show ((0 : SmoothCcTensor g r s).toSection x : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) =
      (0 : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) from rfl]
  rw [ContinuousLinearMap.zero_comp]
  rw [show ((0 : SmoothCcTensor g 0 s).toSection x : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) =
      (0 : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) from rfl]

set_option linter.unusedSectionVars false in
lemma linearizedRicciThreeArmHjoint_zero (g₀ : SmoothRiemannianMetric I M)
    {δ δ' : ℝ} :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun _ : ℝ => (0 : SmoothCcTensor g₀ 3 2)) (δ := δ) (δ' := δ') := by
  rw [linearizedRicciThreeArmHjoint]
  have heq : (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
        (((fun _ : ℝ => (0 : SmoothCcTensor g₀ 3 2)) p.2).toSection p.1)) =
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
          (0 : Tensor0SBundle.TensorRSSpace 3 2 I p.1)) := by
    funext p
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1 t) ?_
    rw [show ((0 : SmoothCcTensor g₀ 3 2).toSection : ContMDiffSection I _ ∞ _) = 0 from rfl]
    rfl
  rw [heq]
  have hzero : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (Bundle.zeroSection (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z)) :=
    Bundle.contMDiff_zeroSection ℝ (fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z)
  exact (hzero.comp contMDiff_fst).contMDiffOn

set_option linter.unusedSectionVars false in
private lemma partialDeriv_chartGramOnE_differentiableAt_local
    (g : SmoothRiemannianMetric I M) (α : M)
    (p l b : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (partialDeriv (E := E) p (chartGramOnE (I := I) g α l b)) y₀ := by
  have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b) (extChartAt I α).target :=
    chartGramOnE_contDiffOn (I := I) g α l b
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b)
      (interior (extChartAt I α).target) := hcd.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) g α l b))
      (interior (extChartAt I α).target) :=
    hcd_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hpd : ContDiffOn ℝ ∞ (partialDeriv (E := E) p (chartGramOnE (I := I) g α l b))
      (interior (extChartAt I α).target) := by
    unfold partialDeriv
    exact hfderiv.clm_apply contDiffOn_const
  exact (hpd.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

set_option linter.unusedSectionVars false in
private lemma chartGramOnE_differentiableAt_local
    (g : SmoothRiemannianMetric I M) (α : M)
    (l b : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α l b) y₀ := by
  have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b) (extChartAt I α).target :=
    chartGramOnE_contDiffOn (I := I) g α l b
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b)
      (interior (extChartAt I α).target) := hcd.mono interior_subset
  exact (hcd_int.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

set_option linter.unusedSectionVars false in
private lemma partialDeriv_realizedGramDeriv_differentiableAt_local
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (p a b : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I x).target) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) p
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)) y₀ := by
  have heq : (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) =
      fun y => chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x a b y -
        chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x a b y := rfl
  rw [heq]
  have hsub : (partialDeriv (E := E) p
        (fun y => chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x a b y -
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x a b y))
        =ᶠ[nhds y₀]
      fun y => partialDeriv (E := E) p
            (chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x a b) y -
          partialDeriv (E := E) p
            (chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x a b) y := by
    filter_upwards [isOpen_interior.mem_nhds hy] with y hyy
    rw [partialDeriv_sub
        (chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x a b)
        (chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x a b)
        (chartGramOnE_differentiableAt_local (I := I) _ x a b hyy)
        (chartGramOnE_differentiableAt_local (I := I) _ x a b hyy)]
  refine (Filter.EventuallyEq.differentiableAt_iff hsub).mpr ?_
  exact (partialDeriv_chartGramOnE_differentiableAt_local (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x p a b hy).sub
    (partialDeriv_chartGramOnE_differentiableAt_local (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x p a b hy)

set_option linter.unusedSectionVars false in
private lemma realizedLinearizedChristoffelPrincipal_differentiableAt_local
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I x).target) {s₀ : ℝ} :
    DifferentiableAt ℝ
      (fun y => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        x i j k y s₀) y₀ := by
  classical
  have hrw : (fun y => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        x i j k y s₀) =
      fun y => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k l y *
          (partialDeriv (E := E) i
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j) y +
            partialDeriv (E := E) j
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i) y -
            partialDeriv (E := E) l
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) y) := by
    funext y; rw [realizedLinearizedChristoffelPrincipal]
  rw [hrw]
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.fun_sum (fun l _ => ?_)
  refine DifferentiableAt.mul
    (chartInvGramOnE_differentiableAt_interior (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k l hy) ?_
  exact ((partialDeriv_realizedGramDeriv_differentiableAt_local (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x i l j hy).add
      (partialDeriv_realizedGramDeriv_differentiableAt_local (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x j l i hy)).sub
    (partialDeriv_realizedGramDeriv_differentiableAt_local (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x l i j hy)

set_option linter.unusedSectionVars false in
private lemma christoffelSlope_differentiableAt_local
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    DifferentiableAt ℝ
      (fun y => deriv (fun s : ℝ =>
        chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k y) s₀) y₀ := by
  classical
  set Φ : ℝ × E → ℝ := fun r =>
    chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) x i j k r.2 with hΦ
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hjoint : ContDiffAt ℝ ∞ Φ (s₀, y₀) :=
    gen_joint_christoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') x hG i j k hs₀ hy
  have hΦ_dfderiv : ContDiffAt ℝ ∞ (fderiv ℝ Φ) (s₀, y₀) := hjoint.fderiv_right (by simp)
  have get_diff_nhd : ∀ᶠ p : ℝ × E in nhds (s₀, y₀), DifferentiableAt ℝ Φ p := by
    obtain ⟨f', u, hu, _, hfu⟩ :=
      contDiffAt_one_iff.mp (hjoint.of_le (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ∞))
    exact Filter.eventually_of_mem hu fun p hp => (hfu p hp).differentiableAt
  have hΦ_y : ∀ᶠ y : E in nhds y₀, DifferentiableAt ℝ Φ (s₀, y) :=
    (continuous_const (y := s₀) |>.prodMk continuous_id).continuousAt get_diff_nhd
  have h_eq : (fun y => deriv (fun s : ℝ => Φ (s, y)) s₀) =ᶠ[nhds y₀]
      (fun y => fderiv ℝ Φ (s₀, y) ((1 : ℝ), (0 : E))) := by
    filter_upwards [hΦ_y] with y hy
    have := hy.hasFDerivAt.comp_hasDerivAt (s₀ : ℝ)
      (hasFDerivAt_prodMk_left s₀ y).hasDerivAt
    exact this.deriv
  have hdiff_rhs : DifferentiableAt ℝ
      (fun y => fderiv ℝ Φ (s₀, y) ((1 : ℝ), (0 : E))) y₀ := by
    have h_chain : HasFDerivAt (fun y => fderiv ℝ Φ (s₀, y) ((1 : ℝ), (0 : E)))
        ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).comp
          ((fderiv ℝ (fderiv ℝ Φ) (s₀, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ E))) y₀ :=
      (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : E))).hasFDerivAt.comp y₀
        ((hΦ_dfderiv.differentiableAt (by norm_num)).hasFDerivAt.comp y₀
          (hasFDerivAt_prodMk_right s₀ y₀))
    exact h_chain.differentiableAt
  exact (Filter.EventuallyEq.differentiableAt_iff h_eq).mpr hdiff_rhs

set_option linter.unusedSectionVars false in
private lemma realizedChristoffelNonPrincipal_differentiableAt_local
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    DifferentiableAt ℝ
      (fun y => realizedChristoffelNonPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        x i j k y s₀) y₀ := by
  classical
  have hNPeq : (fun y => realizedChristoffelNonPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
        x i j k y s₀) =ᶠ[nhds y₀]
      (fun y => deriv (fun s : ℝ =>
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k y) s₀ -
        realizedLinearizedChristoffelPrincipal (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
          x i j k y s₀) := by
    have hopen : IsOpen (interior (extChartAt I x).target) := isOpen_interior
    filter_upwards [hopen.mem_nhds hy] with y hyy
    rw [linearizedChristoffel_eq_principal_add_nonPrincipal (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x i j k hyy hs₀]
    ring
  refine (Filter.EventuallyEq.differentiableAt_iff hNPeq).mpr ?_
  exact (christoffelSlope_differentiableAt_local (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x i j k hy hs₀).sub
    (realizedLinearizedChristoffelPrincipal_differentiableAt_local (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x i j k hy)

def chartSlopeSecondOrderContribution (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) j
        (fun y' => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
          hδ_lt hδ hδ'_lt hδ' x i k j y' s₀) y -
      partialDeriv (E := E) k
        (fun y' => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
          hδ_lt hδ hδ'_lt hδ' x i j j y' s₀) y)

def chartSlopeOrder0Contribution (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    (partialDeriv (E := E) j
        (fun y' => realizedChristoffelNonPrincipal (I := I) g₀ T T'
          hδ_lt hδ hδ'_lt hδ' x i k j y' s₀) y -
      partialDeriv (E := E) k
        (fun y' => realizedChristoffelNonPrincipal (I := I) g₀ T T'
          hδ_lt hδ hδ'_lt hδ' x i j j y' s₀) y +
      (∑ m : Fin (Module.finrank ℝ E),
        (deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j m j y) s₀ *
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i k m y +
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j m j y *
            deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k m y) s₀ -
          deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k m j y) s₀ *
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j m y -
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k m j y *
            deriv (fun s : ℝ =>
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j m y) s₀)))

set_option linter.unusedSectionVars false in
theorem chartRicciTraceChristoffelSlope_eq_secondOrder_add_order0
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    chartRicciTraceChristoffelSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k y s₀ =
      chartSlopeSecondOrderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k y s₀ +
        chartSlopeOrder0Contribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k y s₀ := by
  classical
  rw [chartRicciTraceChristoffelSlope, chartSlopeSecondOrderContribution,
    chartSlopeOrder0Contribution]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hsplit : ∀ (c a b : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) c
          (fun y' => deriv (fun s : ℝ =>
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i b a y') s₀) y =
        partialDeriv (E := E) c
            (fun y' => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
              hδ_lt hδ hδ'_lt hδ' x i b a y' s₀) y +
          partialDeriv (E := E) c
            (fun y' => realizedChristoffelNonPrincipal (I := I) g₀ T T'
              hδ_lt hδ hδ'_lt hδ' x i b a y' s₀) y := by
    intro c a b
    have hfun : (fun y' => deriv (fun s : ℝ =>
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i b a y') s₀) =ᶠ[nhds y]
        (fun y' => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
            hδ_lt hδ hδ'_lt hδ' x i b a y' s₀ +
          realizedChristoffelNonPrincipal (I := I) g₀ T T'
            hδ_lt hδ hδ'_lt hδ' x i b a y' s₀) := by
      filter_upwards [isOpen_interior.mem_nhds hy] with y' hyy
      exact linearizedChristoffel_eq_principal_add_nonPrincipal (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x i b a hyy hs₀
    have hpartialeq : partialDeriv (E := E) c
          (fun y' => deriv (fun s : ℝ =>
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i b a y') s₀) y =
        partialDeriv (E := E) c
          (fun y' => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
              hδ_lt hδ hδ'_lt hδ' x i b a y' s₀ +
            realizedChristoffelNonPrincipal (I := I) g₀ T T'
              hδ_lt hδ hδ'_lt hδ' x i b a y' s₀) y := by
      unfold partialDeriv
      rw [Filter.EventuallyEq.fderiv_eq hfun]
    rw [hpartialeq]
    rw [partialDeriv_add
        (fun y' => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
          hδ_lt hδ hδ'_lt hδ' x i b a y' s₀)
        (fun y' => realizedChristoffelNonPrincipal (I := I) g₀ T T'
          hδ_lt hδ hδ'_lt hδ' x i b a y' s₀)
        (realizedLinearizedChristoffelPrincipal_differentiableAt_local (I := I) g₀ T T'
          hδ_lt hδ hδ'_lt hδ' x i b a hy)
        (realizedChristoffelNonPrincipal_differentiableAt_local (I := I) g₀ T T'
          hδ_lt hδ hδ'_lt hδ' x i b a hy hs₀)]
  rw [hsplit j j k, hsplit k j j]
  ring

def chartSlopePrincipalSymbolContribution (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l y *
        (partialDeriv (E := E) j
            (partialDeriv (E := E) i
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k)) y +
         partialDeriv (E := E) j
            (partialDeriv (E := E) k
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i)) y -
         partialDeriv (E := E) j
            (partialDeriv (E := E) l
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k)) y) -
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l y *
        (partialDeriv (E := E) k
            (partialDeriv (E := E) i
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j)) y +
         partialDeriv (E := E) k
            (partialDeriv (E := E) j
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i)) y -
         partialDeriv (E := E) k
            (partialDeriv (E := E) l
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j)) y)

def chartSlopeFirstOrderRemainderContribution (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i k : Fin (Module.finrank ℝ E)) (y : E) (s₀ : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j
          (chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l) y *
        (partialDeriv (E := E) i
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k) y +
         partialDeriv (E := E) k
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i) y -
         partialDeriv (E := E) l
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k) y) -
  (1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
    ∑ l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k
          (chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l) y *
        (partialDeriv (E := E) i
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j) y +
         partialDeriv (E := E) j
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i) y -
         partialDeriv (E := E) l
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) y)

private lemma partialDeriv_realizedLinearizedChristoffelPrincipal
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b j d : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ} :
    partialDeriv (E := E) d
        (fun y' => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
          hδ_lt hδ hδ'_lt hδ' x a b j y' s₀) y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d
            (chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l) y *
            (partialDeriv (E := E) a
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) y +
             partialDeriv (E := E) b
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) y -
             partialDeriv (E := E) l
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) y) +
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l y *
            (partialDeriv (E := E) d
                (partialDeriv (E := E) a
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b)) y +
             partialDeriv (E := E) d
                (partialDeriv (E := E) b
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a)) y -
             partialDeriv (E := E) d
                (partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)) y)) := by
  classical
  set S : Fin (Module.finrank ℝ E) → E → ℝ := fun l y' =>
    partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) y' +
      partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) y' -
      partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) y'
    with hS
  set G : Fin (Module.finrank ℝ E) → E → ℝ := fun l =>
    chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l with hG
  have hS_diff : ∀ l : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (S l) y := by
    intro l
    exact ((partialDeriv_realizedGramDeriv_differentiableAt_local (I := I) g₀ T T'
            hδ_lt hδ hδ'_lt hδ' x a l b hy).add
        (partialDeriv_realizedGramDeriv_differentiableAt_local (I := I) g₀ T T'
            hδ_lt hδ hδ'_lt hδ' x b l a hy)).sub
      (partialDeriv_realizedGramDeriv_differentiableAt_local (I := I) g₀ T T'
            hδ_lt hδ hδ'_lt hδ' x l a b hy)
  have hG_diff : ∀ l : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (G l) y :=
    fun l => chartInvGramOnE_differentiableAt_interior (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l hy
  have hsummand_diff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y' => G l y' * S l y') y :=
    fun l => (hG_diff l).mul (hS_diff l)
  have hrewrite : (fun y' => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x a b j y' s₀) =
      fun y' => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E), G l y' * S l y' := by
    funext y'
    rw [realizedLinearizedChristoffelPrincipal]
  rw [hrewrite]
  rw [partialDeriv_const_mul (1 / 2 : ℝ)
        (fun y' => ∑ l : Fin (Module.finrank ℝ E), G l y' * S l y')
        (DifferentiableAt.fun_sum (fun l _ => hsummand_diff l))]
  congr 1
  rw [partialDeriv_sum Finset.univ (fun l y' => G l y' * S l y')
        (fun l _ => hsummand_diff l)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_mul (G l) (S l) (hG_diff l) (hS_diff l)]
  have hSderiv : partialDeriv (E := E) d (S l) y =
      partialDeriv (E := E) d
          (partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T'
            hδ_lt hδ hδ'_lt hδ' x l b)) y +
        partialDeriv (E := E) d
          (partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T'
            hδ_lt hδ hδ'_lt hδ' x l a)) y -
        partialDeriv (E := E) d
          (partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T'
            hδ_lt hδ hδ'_lt hδ' x a b)) y := by
    have h1 := partialDeriv_realizedGramDeriv_differentiableAt_local (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x a l b hy
    have h2 := partialDeriv_realizedGramDeriv_differentiableAt_local (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x b l a hy
    have h3 := partialDeriv_realizedGramDeriv_differentiableAt_local (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x l a b hy
    rw [hS]
    rw [partialDeriv_sub (E := E)
          (fun y' => partialDeriv (E := E) a
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b) y' +
            partialDeriv (E := E) b
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a) y')
          (partialDeriv (E := E) l
              (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)) (h1.add h2) h3]
    rw [partialDeriv_add (E := E)
          (partialDeriv (E := E) a (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l b))
          (partialDeriv (E := E) b (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l a))
          h1 h2]
  rw [hSderiv, hS, hG]

set_option linter.unusedSectionVars false in
private lemma realizedGramDeriv_differentiableAt_local
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I x).target) :
    DifferentiableAt ℝ (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) y₀ := by
  have hrw : realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b =
      fun y => chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x a b y -
        chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x a b y := by
    funext y; rw [realizedGramDeriv]
  rw [hrw]
  exact (chartGramOnE_differentiableAt_local (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x a b hy).sub
    (chartGramOnE_differentiableAt_local (I := I)
      (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x a b hy)

set_option linter.unusedSectionVars false in
private lemma gramBracket_realizedFam_differentiableAt_local
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j l : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I x).target) (s₀ : ℝ) :
    DifferentiableAt ℝ
      (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.gramBracket
        (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j l) y₀ := by
  have hrw :
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.gramBracket
        (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j l =
      fun y => partialDeriv (E := E) i
          (chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x l j) y +
        partialDeriv (E := E) j
          (chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x l i) y -
        partialDeriv (E := E) l
          (chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j) y := by
    funext y
    rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.gramBracket]
  rw [hrw]
  exact ((partialDeriv_chartGramOnE_differentiableAt_local (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i l j hy).add
      (partialDeriv_chartGramOnE_differentiableAt_local (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l i hy)).sub
    (partialDeriv_chartGramOnE_differentiableAt_local (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x l i j hy)

set_option linter.unusedSectionVars false in
private lemma realizedChristoffelNonPrincipalInner_differentiableAt_local
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (k l : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I x).target) (s₀ : ℝ) :
    DifferentiableAt ℝ
      (fun y => -(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k p y *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y *
            chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x q l y)) y₀ := by
  refine DifferentiableAt.fun_neg ?_
  refine DifferentiableAt.fun_sum (fun q _ => ?_)
  refine DifferentiableAt.fun_sum (fun p _ => ?_)
  exact ((chartInvGramOnE_differentiableAt_interior (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k p hy).mul
      (realizedGramDeriv_differentiableAt_local (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x p q hy)).mul
    (chartInvGramOnE_differentiableAt_interior (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x q l hy)

set_option linter.unusedSectionVars false in
private lemma partialDeriv_realizedChristoffelNonPrincipal
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k d : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) (s₀ : ℝ) :
    partialDeriv (E := E) d
        (fun y' => realizedChristoffelNonPrincipal (I := I) g₀ T T'
          hδ_lt hδ hδ'_lt hδ' x i j k y' s₀) y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) d
            (fun y' => -(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k p y' *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y' *
                chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x q l y')) y *
            DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.gramBracket
              (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j l y +
          (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k p y *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y *
                chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x q l y)) *
            DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.gramBracketDeriv
              (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x d i j l y) := by
  classical
  set F : Fin (Module.finrank ℝ E) → E → ℝ := fun l y' =>
    -(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k p y' *
        realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y' *
        chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x q l y') with hF
  set B : Fin (Module.finrank ℝ E) → E → ℝ := fun l =>
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.gramBracket
      (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j l with hB
  have hF_diff : ∀ l : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (F l) y := fun l =>
    realizedChristoffelNonPrincipalInner_differentiableAt_local (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x k l hy s₀
  have hB_diff : ∀ l : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (B l) y := fun l =>
    gramBracket_realizedFam_differentiableAt_local (I := I) g₀ T T' hδ hδ' x i j l hy s₀
  have hsummand_diff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y' => F l y' * B l y') y :=
    fun l => (hF_diff l).mul (hB_diff l)
  have hrewrite : (fun y' => realizedChristoffelNonPrincipal (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x i j k y' s₀) =
      fun y' => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E), F l y' * B l y' := by
    funext y'
    rw [realizedChristoffelNonPrincipal]
  rw [hrewrite]
  rw [partialDeriv_const_mul (1 / 2 : ℝ)
        (fun y' => ∑ l : Fin (Module.finrank ℝ E), F l y' * B l y')
        (DifferentiableAt.fun_sum (fun l _ => hsummand_diff l))]
  congr 1
  rw [partialDeriv_sum Finset.univ (fun l y' => F l y' * B l y')
        (fun l _ => hsummand_diff l)]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [partialDeriv_mul (F l) (B l) (hF_diff l) (hB_diff l)]
  rw [hF, hB]
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.partialDeriv_gramBracket_eq
    (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x d i j l hy]

theorem chartSlopeSecondOrderContribution_eq_principal_add_remainder
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) (s₀ : ℝ) :
    chartSlopeSecondOrderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k y s₀ =
      chartSlopePrincipalSymbolContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k y s₀ +
        chartSlopeFirstOrderRemainderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k y s₀ := by
  classical
  rw [chartSlopeSecondOrderContribution]
  have hexpand : ∀ j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) j
          (fun y' => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
            hδ_lt hδ hδ'_lt hδ' x i k j y' s₀) y -
        partialDeriv (E := E) k
          (fun y' => realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
            hδ_lt hδ hδ'_lt hδ' x i j j y' s₀) y =
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j
            (chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l) y *
            (partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l k) y +
             partialDeriv (E := E) k (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l i) y -
             partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x i k) y) +
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k)) y))) -
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k
            (chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l) y *
            (partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l j) y +
             partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l i) y -
             partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x i j) y) +
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j)) y))) := by
    intro j
    rw [partialDeriv_realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x i k j j hy,
      partialDeriv_realizedLinearizedChristoffelPrincipal (I := I) g₀ T T'
        hδ_lt hδ hδ'_lt hδ' x i j j k hy]
  rw [Finset.sum_congr rfl (fun j _ => hexpand j)]
  have hsplit : ∀ j : Fin (Module.finrank ℝ E),
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) j
            (chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l) y *
            (partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l k) y +
             partialDeriv (E := E) k (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l i) y -
             partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x i k) y) +
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k)) y))) -
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) k
            (chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l) y *
            (partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l j) y +
             partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l i) y -
             partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x i j) y) +
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j)) y))) =
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l y *
            (partialDeriv (E := E) j (partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l k)) y +
             partialDeriv (E := E) j (partialDeriv (E := E) k
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i)) y -
             partialDeriv (E := E) j (partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k)) y) -
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l y *
            (partialDeriv (E := E) k (partialDeriv (E := E) i
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) j
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) l
                  (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j)) y)) +
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) j
            (chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l) y *
            (partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l k) y +
             partialDeriv (E := E) k (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l i) y -
             partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x i k) y) -
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          partialDeriv (E := E) k
            (chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x j l) y *
            (partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l j) y +
             partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x l i) y -
             partialDeriv (E := E) l (realizedGramDeriv (I := I) g₀ T T'
                hδ_lt hδ hδ'_lt hδ' x i j) y)) := by
    intro j
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, mul_add, mul_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hsplit j)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [chartSlopePrincipalSymbolContribution]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  · rw [chartSlopeFirstOrderRemainderContribution]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

set_option linter.unusedSectionVars false in
private lemma order0Rhs_split_appCc (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i k : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)) (T - T')) x
          ![(chartModelBasis E) k, (chartModelBasis E) i]
        - unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s)) (T - T')) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] := by
  rw [linearizedRicciArm0BaseCoeff]
  rw [show iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') = T - T' from rfl]
  have hsplit :
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)) =
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
          + (-1 : ℝ) • ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [hsplit]
  rw [appCc_add_left, appCc_smul_left_local, unitModel_add2_apply, unitModel_smul_local]
  rw [ContinuousMultilinearMap.smul_apply, neg_one_smul, ← sub_eq_add_neg]

set_option linter.unusedSectionVars false in
private lemma ricEndoRaisedFib_eq_chartBasis_sum
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (p : Fin (Module.finrank ℝ E)) :
    ricEndoRaisedFib (I := I) g₁ x (chartModelBasis E p) =
      ∑ a : Fin (Module.finrank ℝ E),
        (∑ b : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x a b *
              chartRicciTensor (I := I) g₁ x p b (extChartAt I x x)) •
          (chartModelBasis E a) := by
  classical
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) x, extChartAt_source (I := I)]
    exact mem_chart_source H x
  have hself : ∀ t : Fin (Module.finrank ℝ E),
      chartBasisVecFiber (I := I) x t x = chartModelBasis E t := fun t =>
    chartBasisVecFiber_self (I := I) x t
  have hsharp := metricSharpChartLocal_eq_metricSharp (I := I) g₁ x
    (fun b : M => (ricciTensor (I := I) g₁ b (chartModelBasis E p)).toLinearMap) hxbase
  rw [ricEndoRaisedFib_apply, ← hsharp, metricSharpChartLocal]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hself a, metricSharpChartCoeff_def]
  refine congrArg (fun c : ℝ => c • (chartModelBasis E a)) ?_
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x a b * t) ?_
  have hricapply :
      (ricciTensor (I := I) g₁ x (chartModelBasis E p)).toLinearMap
          (chartBasisVecFiber (I := I) x b x) =
        ricciTensor (I := I) g₁ x (chartBasisVecFiber (I := I) x p x)
          (chartBasisVecFiber (I := I) x b x) := by
    rw [show (chartModelBasis E p : TangentSpace I x) =
      chartBasisVecFiber (I := I) x p x from (hself p).symm]
    rfl
  rw [hricapply]
  rw [ricciTensor_chartBasisVec_alpha_eq (I := I) g₁ x p b hxgood]

set_option linter.unusedSectionVars false in
private lemma ccTensorBilin_chartBasis_eq_tensorChartComponent
    (g₀ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2) (x : M)
    (a b : Fin (Module.finrank ℝ E)) :
    ccTensorBilin (I := I) g₀ W x (chartModelBasis E a) (chartModelBasis E b) =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 W x ![] ![a, b] x := by
  rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ W x
    (chartModelBasis E a) (chartModelBasis E b)]
  exact unitModel_basisChart_eq_tensorChartComponent (I := I) (M := M) g₀ W x a b

set_option linter.unusedSectionVars false in
private lemma order0RicciArm_basis_eq
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (g₁ : SmoothRiemannianMetric I M) (x : M) (k i : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) (T - T')) x
        ![(chartModelBasis E) k, (chartModelBasis E) i] =
      (∑ a : Fin (Module.finrank ℝ E),
          (∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x a b *
                chartRicciTensor (I := I) g₁ x k b (extChartAt I x x)) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, i] x) +
        (∑ a : Fin (Module.finrank ℝ E),
          (∑ b : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ x x a b *
                chartRicciTensor (I := I) g₁ x i b (extChartAt I x x)) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![k, a] x) := by
  classical
  rw [ricciArmOrder0CurvCoeff_appCc_eq_curvatureAction (I := I) (M := M) g₀ g₁ (T - T') x
    (![(chartModelBasis E) k, (chartModelBasis E) i])]
  have hv0 : (![(chartModelBasis E) k, (chartModelBasis E) i] : Fin 2 → TangentSpace I x) 0 =
      chartModelBasis E k := rfl
  have hv1 : (![(chartModelBasis E) k, (chartModelBasis E) i] : Fin 2 → TangentSpace I x) 1 =
      chartModelBasis E i := rfl
  rw [hv0, hv1]
  have hupd0 : (Function.update
        (![(chartModelBasis E) k, (chartModelBasis E) i] : Fin 2 → TangentSpace I x) 0
        (ricEndoRaisedFib (I := I) g₁ x (chartModelBasis E k))) =
      ![ricEndoRaisedFib (I := I) g₁ x (chartModelBasis E k), chartModelBasis E i] := by
    funext j; fin_cases j <;> simp [Function.update]
  have hupd1 : (Function.update
        (![(chartModelBasis E) k, (chartModelBasis E) i] : Fin 2 → TangentSpace I x) 1
        (ricEndoRaisedFib (I := I) g₁ x (chartModelBasis E i))) =
      ![chartModelBasis E k, ricEndoRaisedFib (I := I) g₁ x (chartModelBasis E i)] := by
    funext j; fin_cases j <;> simp [Function.update]
  rw [hupd0, hupd1]
  rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ (T - T') x
      (ricEndoRaisedFib (I := I) g₁ x (chartModelBasis E k)) (chartModelBasis E i),
    unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ (T - T') x
      (chartModelBasis E k) (ricEndoRaisedFib (I := I) g₁ x (chartModelBasis E i))]
  rw [ricEndoRaisedFib_eq_chartBasis_sum (I := I) g₁ x k,
    ricEndoRaisedFib_eq_chartBasis_sum (I := I) g₁ x i]
  congr 1
  · rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ccTensorBilin_chartBasis_eq_tensorChartComponent (I := I) (M := M) g₀ (T - T') x a i]
  · rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_smul, smul_eq_mul,
      ccTensorBilin_chartBasis_eq_tensorChartComponent (I := I) (M := M) g₀ (T - T') x k a]

set_option linter.unusedSectionVars false in
private lemma order0RiemannArm_eq_riemannBiContrFib_toModel
    (g₀ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 2)
    (g₁ : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁) W) x v =
      Tensor0SSpace.toModel
        (riemannBiContrFib (I := I) g₁ x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun j => (v j : E)) := by
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
  rfl

set_option linter.unusedSectionVars false in
private lemma riemannBiContrFib_toModel_basis_center
    (g₁ : SmoothRiemannianMetric I M) (x : M) (D : Tensor0SSpace 2 I x)
    (k i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel (riemannBiContrFib (I := I) g₁ x D)
        ![((chartModelBasis E) k : E), ((chartModelBasis E) i : E)] =
      2 * ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x m n *
          (∑ p : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ x x p l *
              ((∑ q : Fin (Module.finrank ℝ E),
                  chartRiemannTensor (I := I) g₁ x p k m q (extChartAt I x x) *
                    chartGramMatrix (I := I) g₁ x x q i) *
                Tensor0SSpace.toModel D
                  ![((chartModelBasis E) n : E), ((chartModelBasis E) l : E)])) := by
  classical
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) x, extChartAt_source (I := I)]
    exact mem_chart_source H x
  have hself : ∀ t : Fin (Module.finrank ℝ E),
      chartBasisVecFiber (I := I) x t x = chartModelBasis E t := fun t =>
    chartBasisVecFiber_self (I := I) x t
  rw [riemannBiContrFib_toModel_chartα (I := I) g₁ x hxbase D
    (![((chartModelBasis E) k : E), ((chartModelBasis E) i : E)])]
  have hv0 : (![((chartModelBasis E) k : E), ((chartModelBasis E) i : E)] : Fin 2 → E) 0 =
      (chartModelBasis E) k := rfl
  have hv1 : (![((chartModelBasis E) k : E), ((chartModelBasis E) i : E)] : Fin 2 → E) 1 =
      (chartModelBasis E) i := rfl
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  refine congrArg (fun t => chartInvGramMatrix (I := I) g₁ x x m n * t) ?_
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun l _ => ?_))
  refine congrArg (fun t => chartInvGramMatrix (I := I) g₁ x x p l * t) ?_
  congr 1
  · rw [hv0, hv1]
    rw [show (chartModelBasis E k : TangentSpace I x) = chartBasisVecFiber (I := I) x k x from
        (hself k).symm,
      show (chartModelBasis E i : TangentSpace I x) = chartBasisVecFiber (I := I) x i x from
        (hself i).symm]
    rw [riemannOp_chartBasisVec_alpha_eq (I := I) g₁ x p k m hxgood]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [g_inner_eq_chartGramMatrix_basis (I := I) g₁ x x q i]
  · rw [hself n, hself l]

set_option linter.unusedSectionVars false in
private lemma order0RHS_chart_eq
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i k : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] =
      (2 * ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x m n *
          (∑ p : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x p l *
              ((∑ q : Fin (Module.finrank ℝ E),
                  chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
                      x p k m q (extChartAt I x x) *
                    chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![n, l] x))) -
        ((∑ a : Fin (Module.finrank ℝ E),
            (∑ b : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b *
                  chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
                    x k b (extChartAt I x x)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, i] x) +
          (∑ a : Fin (Module.finrank ℝ E),
            (∑ b : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x a b *
                  chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
                    x i b (extChartAt I x x)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![k, a] x)) := by
  classical
  rw [linearizedRicciArm0BaseCoeff,
    show iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') = T - T' from rfl]
  have hsplit :
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)) =
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
          + (-1 : ℝ) • ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [hsplit]
  rw [appCc_add_left, appCc_smul_left_local, unitModel_add2_apply, unitModel_smul_local,
    ContinuousMultilinearMap.smul_apply, neg_one_smul, ← sub_eq_add_neg]
  congr 1
  · rw [order0RiemannArm_eq_riemannBiContrFib_toModel (I := I) (M := M) g₀ (T - T')
        (realizedFam (I := I) g₀ T T' hδ hδ' s) x
        (![(chartModelBasis E) k, (chartModelBasis E) i])]
    rw [show (fun j => ((![(chartModelBasis E) k, (chartModelBasis E) i] :
            Fin 2 → TangentSpace I x) j : E)) =
        ![((chartModelBasis E) k : E), ((chartModelBasis E) i : E)] from by
      funext j; fin_cases j <;> rfl]
    rw [riemannBiContrFib_toModel_basis_center (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from (T - T').toSection x)
        (unitTensor (I := I) (M := M) x)) k i]
    refine congrArg (fun t => (2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
    refine congrArg (fun t => chartInvGramMatrix (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) x x m n * t) ?_
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun l _ => ?_))
    refine congrArg (fun t => chartInvGramMatrix (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' s) x x p l * t) ?_
    refine congrArg (fun t => (∑ q : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s)
            x p k m q (extChartAt I x x) *
          chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x q i) * t) ?_
    rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from (T - T').toSection x)
            (unitTensor (I := I) (M := M) x))
          ![((chartModelBasis E) n : E), ((chartModelBasis E) l : E)] =
        unitModel (I := I) (M := M) g₀ 2 (T - T') x
          ![(chartModelBasis E) n, (chartModelBasis E) l] from rfl]
    rw [unitModel_basisChart_eq_tensorChartComponent (I := I) (M := M) g₀ (T - T') x n l]
  · exact order0RicciArm_basis_eq (I := I) (M := M) g₀ T T'
      (realizedFam (I := I) g₀ T T' hδ hδ' s) x k i

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_Csob_sub_pointwise_jet3_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Csub : ℝ, 0 ≤ Csub ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2) {R : ℝ} (_hR : 0 ≤ R),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ x : M,
          (∑ j ∈ Finset.range 3,
              (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
                Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
              ‖(iteratedCovGrad (I := I) g₀ 0 2 j (T - T')).toSection x‖)) ≤ Csub * R := by
  classical
  set k : ℕ := Module.finrank ℝ E / 2 + 3 with hk_def
  have hk_super : 2 * k > Module.finrank ℝ E + 4 := by rw [hk_def]; omega
  have h4k_le : 4 * k ≤ a + 2 := by rw [hk_def]; omega
  obtain ⟨Cc, hCc_pos, hCc⟩ :=
    iteratedCovGrad_toSobolev_embedding_C2_unconditional (I := I) (M := M) g₀ k hk_super
  obtain ⟨Ch, hCh_nn, hCh⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 (2 * k)
  refine ⟨Cc * Ch * ((4 * k + 1 : ℕ) : ℝ) * 2, by positivity, ?_⟩
  intro T T' R _hR hbudgetT hbudgetT' x
  set W : SmoothCcTensor g₀ 0 2 := T - T' with hW_def
  have hWbudget : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ≤ 2 * R := by
    intro j hj
    rw [hW_def, iteratedCovGrad_sub]
    refine le_trans (norm_sub_le _ _) ?_
    have := hbudgetT j hj
    have := hbudgetT' j hj
    linarith
  have hCol := hCc W x
  set Mn : ℝ := ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) W‖
    with hMn_def
  have hMn_nn : 0 ≤ Mn := norm_nonneg _
  have hHebey : Mn ≤ Ch * ∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ := by
    refine le_trans (hCh W) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCh_nn
    refine le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))
    exact (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j W)).symm
  have hSumBudget : ∑ j ∈ Finset.range (2 * (2 * k) + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ≤ ((4 * k + 1 : ℕ) : ℝ) * (2 * R) := by
    have hterm : ∀ j ∈ Finset.range (2 * (2 * k) + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖ ≤ 2 * R := by
      intro j hj
      have hjle : j ≤ a + 2 := by
        have := Finset.mem_range.mp hj; omega
      exact hWbudget j hjle
    calc ∑ j ∈ Finset.range (2 * (2 * k) + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j W‖
        ≤ ∑ _j ∈ Finset.range (2 * (2 * k) + 1), (2 * R) := Finset.sum_le_sum hterm
      _ = ((2 * (2 * k) + 1 : ℕ) : ℝ) * (2 * R) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((4 * k + 1 : ℕ) : ℝ) * (2 * R) := by
          congr 2
          omega
  have hMn_le : Mn ≤ Ch * (((4 * k + 1 : ℕ) : ℝ) * (2 * R)) := by
    refine le_trans hHebey ?_
    exact mul_le_mul_of_nonneg_left hSumBudget hCh_nn
  calc (∑ j ∈ Finset.range 3,
          (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
            Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
          ‖(iteratedCovGrad (I := I) g₀ 0 2 j W).toSection x‖))
      ≤ Cc * Mn := hCol
    _ ≤ Cc * (Ch * (((4 * k + 1 : ℕ) : ℝ) * (2 * R))) :=
        mul_le_mul_of_nonneg_left hMn_le hCc_pos.le
    _ = (Cc * Ch * ((4 * k + 1 : ℕ) : ℝ) * 2) * R := by ring

set_option linter.unusedSectionVars false in
theorem traceHessianCoeff_appCc_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (traceHessianCoeff (I := I) (M := M) g₀ g₁) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
            (Tensor0SBundle.Tensor0SSpace.toModel
              ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
                W.toSection x) (unitTensor (I := I) (M := M) x)))
            (Fin.cons (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k) v)) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 4 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (traceHessianCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [traceHessianCoeff_toSection, traceHessianFib_toModel,
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]

set_option linter.unusedSectionVars false in
theorem ricciArmOrder1KoszulCoeff_appCc_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 3)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2 (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) W) x v =
      ∑ k : Fin (Module.finrank ℝ E),
        Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x))
            (Fin.cons (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![(Module.finBasis ℝ E) k,
                raisedKoszulVec (I := I) g₀ g₁ x (v 0) (v 1)]) := by
  rw [unitModel, appCc_toSection]
  rw [show ((show Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          W.toSection x)) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SBundle.Tensor0SSpace 3 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I x from
        (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁).toSection x)
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)) from rfl]
  rw [ricciArmOrder1KoszulCoeff_toSection]
  change Tensor0SBundle.Tensor0SSpace.toModel
      (linearizedRicciArm1Fib (I := I) g₀ g₁ x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) v = _
  rw [linearizedRicciArm1Fib_apply, raisedKoszulFib_apply]
  rw [show Tensor0SBundle.Tensor0SSpace.toModel
        (raisedKoszulPairing (I := I) g₀ g₁ x
          (cometricDoubleTraceFib (I := I) g₁ 1 x
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x)))) v =
      (raisedKoszulPairing (I := I) g₀ g₁ x
          (cometricDoubleTraceFib (I := I) g₁ 1 x
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
              W.toSection x) (unitTensor (I := I) (M := M) x)))) v from rfl]
  rw [raisedKoszulPairing_apply]
  change Tensor0SBundle.Tensor0SSpace.toModel
      (cometricDoubleTraceFib (I := I) g₁ 1 x
        ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x)))
      (fun _ : Fin 1 => raisedKoszulVec (I := I) g₀ g₁ x (v 0) (v 1)) = _
  rw [cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g₁ x)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  funext j
  fin_cases j <;> rfl

set_option linter.unusedSectionVars false in
theorem cDualBasis_trace_basis_indep
    (B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (F : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k : Fin (Module.finrank ℝ E), F (B.cDualBasis k) (B k)) =
      ∑ k : Fin (Module.finrank ℝ E),
        F ((Module.finBasis ℝ E).cDualBasis k) ((Module.finBasis ℝ E) k) := by
  have hcoordB : ∀ k : Fin (Module.finrank ℝ E),
      B.cDualBasis k = LinearMap.toContinuousLinearMap (B.coord k) := by
    intro k
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    exact congrArg (fun L : E →ₗ[ℝ] ℝ => LinearMap.toContinuousLinearMap L)
      (congrFun (Module.Basis.coe_dualBasis B) k)
  have hcoordFin : ∀ k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).cDualBasis k =
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) := by
    intro k
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    exact congrArg (fun L : E →ₗ[ℝ] ℝ => LinearMap.toContinuousLinearMap L)
      (congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k)
  rw [show (∑ k : Fin (Module.finrank ℝ E), F (B.cDualBasis k) (B k)) =
        ∑ k : Fin (Module.finrank ℝ E),
          F (LinearMap.toContinuousLinearMap (B.coord k)) (B k) from
      Finset.sum_congr rfl (fun k _ => by rw [hcoordB k])]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            F ((Module.finBasis ℝ E).cDualBasis k) ((Module.finBasis ℝ E) k)) =
        ∑ k : Fin (Module.finrank ℝ E),
          F (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k))
            ((Module.finBasis ℝ E) k) from
      Finset.sum_congr rfl (fun k _ => by rw [hcoordFin k])]
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E with hb_def
  have h_cov : ∀ j : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
          LinearMap.toContinuousLinearMap (B.coord i)) =
        LinearMap.toContinuousLinearMap (b.coord j) := by
    intro j
    ext z
    calc
      (∑ i : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
          LinearMap.toContinuousLinearMap (B.coord i)) z
          = ∑ i : Fin (Module.finrank ℝ E), b.coord j (B i) * B.coord i z := by
              simp [smul_eq_mul]
      _ = b.coord j (∑ i : Fin (Module.finrank ℝ E), B.coord i z • B i) := by
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
              simp [smul_eq_mul, mul_comm]
      _ = b.coord j z := by
              rw [show (∑ i : Fin (Module.finrank ℝ E), B.coord i z • B i) = z from
                B.sum_repr z]
      _ = (LinearMap.toContinuousLinearMap (b.coord j)) z := rfl
  calc
    (∑ i : Fin (Module.finrank ℝ E),
        F (LinearMap.toContinuousLinearMap (B.coord i)) (B i))
        = ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (b.coord j (B i)) •
              F (LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            F (LinearMap.toContinuousLinearMap (B.coord i)) (B i)
                = F (LinearMap.toContinuousLinearMap (B.coord i))
                    (∑ j : Fin (Module.finrank ℝ E), b.coord j (B i) • b j) := by
                  rw [show (∑ j : Fin (Module.finrank ℝ E), b.coord j (B i) • b j) = B i from
                    b.sum_repr (B i)]
            _ = ∑ j : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
                    F (LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
                  rw [map_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [map_smul]
    _ = ∑ j : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
            (b.coord j (B i)) •
              F (LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin (Module.finrank ℝ E), F
            (∑ i : Fin (Module.finrank ℝ E), (b.coord j (B i)) •
              LinearMap.toContinuousLinearMap (B.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum]
          simp [map_smul]
    _ = ∑ j : Fin (Module.finrank ℝ E),
            F (LinearMap.toContinuousLinearMap (b.coord j)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_cov j]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
def corrFieldDataSpec (g₀ : SmoothRiemannianMetric I M) (CΓ : ℝ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (C0 : ℝ → SmoothCcTensor g₀ 2 2) (C1 : ℝ → SmoothCcTensor g₀ 3 2) : Prop :=
  linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s + C0 s)
      (δ := δ) (δ' := δ') ∧
  linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (fun s => linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s + C1 s)
      (δ := δ) (δ' := δ') ∧
  (∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0 s).toSection x)) ≤
        CΓ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) *
          (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j (T - T')).toSection x‖)) ∧
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x ((C1 s).toSection x)) ≤
        CΓ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) *
          (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j (T - T')).toSection x‖))) ∧
  ((∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v) →
    (∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v) →
    ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (x : M) (i k : Fin (Module.finrank ℝ E))
        (hδ_lt : δ < 1) (hδ'_lt : δ' < 1),
        chartSlopeSecondOrderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
              (extChartAt I x x) s +
            chartSlopeOrder0Contribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
              (extChartAt I x x) s =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2
                (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s + C0 s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2
                (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s + C1 s)
                (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2
                (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
              ![(chartModelBasis E) k, (chartModelBasis E) i])

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma arm2_appCc_eq_combinedTrace_unitModel4
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i k : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] =
      (1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k₁)))
                ![(chartModelBasis E) k, (chartModelBasis E) i, (Module.finBasis ℝ E) k₁])
            + unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
                (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k₁)))
                  ![(chartModelBasis E) i, (chartModelBasis E) k, (Module.finBasis ℝ E) k₁])
            - unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
                (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k₁)))
                  (Fin.cons ((Module.finBasis ℝ E) k₁)
                    ![(chartModelBasis E) k, (chartModelBasis E) i]))) +
        -(1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
            ![(chartModelBasis E) k, (chartModelBasis E) i,
              cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k₁)),
              (Module.finBasis ℝ E) k₁] := by
  rw [linearizedRicciArm2FieldLichnerowicz]
  have hsplit :
      (ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
        - (1 / 2 : ℝ) • traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)) =
      ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
        + (-(1 / 2) : ℝ) • traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) := by
    rw [neg_smul, ← sub_eq_add_neg]
  rw [hsplit, appCc_add_left, appCc_smul_left_local, unitModel_add2_apply, unitModel_smul_local,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [covDerivConnDiff_tracedPrincipal_eq_appCc (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T') x
        (![(chartModelBasis E) k, (chartModelBasis E) i])]
  rw [traceHessianCoeff_appCc_eq (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
        (![(chartModelBasis E) k, (chartModelBasis E) i])]
  have htrace_to_unitModel : ∀ k₁ : Fin (Module.finrank ℝ E),
      ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
          (Tensor0SBundle.Tensor0SSpace.toModel
            ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ]
                Tensor0SBundle.Tensor0SSpace 4 I x from
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')).toSection x)
              (unitTensor (I := I) (M := M) x)))
          (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k₁)))
            (Fin.cons ((Module.finBasis ℝ E) k₁)
              ![(chartModelBasis E) k, (chartModelBasis E) i])) =
        unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
          ![(chartModelBasis E) k, (chartModelBasis E) i,
            cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k₁)),
            (Module.finBasis ℝ E) k₁] := by
    intro k₁
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    set base : Fin 4 → TangentSpace I x :=
      Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k₁)))
        (Fin.cons ((Module.finBasis ℝ E) k₁)
          ![(chartModelBasis E) k, (chartModelBasis E) i]) with hbase
    have hbeq : (fun i_1 : Fin 4 => base (traceHessianSlotPerm i_1)) =
        ![(chartModelBasis E) k, (chartModelBasis E) i,
            cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k₁)),
            (Module.finBasis ℝ E) k₁] := by
      funext i_1
      fin_cases i_1 <;> rfl
    rw [hbeq]
    rfl
  rw [Finset.sum_congr rfl (fun k₁ _ => htrace_to_unitModel k₁)]
  have hprin : ∀ k₁ : Fin (Module.finrank ℝ E),
      (unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
            (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k₁)))
              ![(![(chartModelBasis E) k, (chartModelBasis E) i] : Fin 2 → TangentSpace I x) 0,
                (![(chartModelBasis E) k, (chartModelBasis E) i] : Fin 2 → TangentSpace I x) 1,
                (Module.finBasis ℝ E) k₁])
          + unitModel (I := I) (M := M) g₀ 4
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k₁)))
                ![(![(chartModelBasis E) k, (chartModelBasis E) i] : Fin 2 → TangentSpace I x) 1,
                  (![(chartModelBasis E) k, (chartModelBasis E) i] : Fin 2 → TangentSpace I x) 0,
                  (Module.finBasis ℝ E) k₁])
          - unitModel (I := I) (M := M) g₀ 4
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k₁)))
                (Fin.cons ((Module.finBasis ℝ E) k₁)
                  ![(chartModelBasis E) k, (chartModelBasis E) i]))) =
        (unitModel (I := I) (M := M) g₀ 4
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
            (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k₁)))
              ![(chartModelBasis E) k, (chartModelBasis E) i, (Module.finBasis ℝ E) k₁])
          + unitModel (I := I) (M := M) g₀ 4
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k₁)))
                ![(chartModelBasis E) i, (chartModelBasis E) k, (Module.finBasis ℝ E) k₁])
          - unitModel (I := I) (M := M) g₀ 4
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k₁)))
                (Fin.cons ((Module.finBasis ℝ E) k₁)
                  ![(chartModelBasis E) k, (chartModelBasis E) i]))) := by
    intro k₁
    congr 2
  rw [Finset.sum_congr rfl (fun k₁ _ => hprin k₁)]

set_option linter.unusedSectionVars false in
private lemma cometricFinBasisTrace_eq_chartInvGram_bilin
    (g₁ : SmoothRiemannianMetric I M) (x : M)
    (F : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ k₁ : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k₁)))
          ((Module.finBasis ℝ E) k₁)) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ l •
          F (chartModelBasis E l) (chartModelBasis E k₁) := by
  classical
  set L₁ : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (cometricLmodel (I := I) g₁ x).comp
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)) with hL₁
  set F' : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := F.comp L₁ with hF'
  have hFapp : ∀ (φ : E →L[ℝ] ℝ) (v : E),
      F' φ v = F (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) v := by
    intro φ v
    rfl
  have htrace := (cDualBasis_trace_basis_indep (E := E) (chartModelBasis E) F').symm
  rw [show (∑ k₁ : Fin (Module.finrank ℝ E),
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k₁)))
          ((Module.finBasis ℝ E) k₁)) =
      ∑ k₁ : Fin (Module.finrank ℝ E),
        F' ((Module.finBasis ℝ E).cDualBasis k₁) ((Module.finBasis ℝ E) k₁) from
    Finset.sum_congr rfl (fun k₁ _ => (hFapp _ _).symm)]
  rw [htrace]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [hFapp ((chartModelBasis E).cDualBasis k₁) (chartModelBasis E k₁)]
  rw [cometricLmodel_covectorOfCLM_cDualBasis_eq_chartBasis_sum (I := I) g₁ x k₁]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply]

set_option linter.unusedSectionVars false in
private def unitModel4SlotBilin
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (i j : Fin 4) (hij : i ≠ j) (base : Fin 4 → E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => f (Function.update (Function.update base i c) j v)
          map_add' := fun v1 v2 => by
            rw [f.map_update_add (Function.update base i c) j v1 v2]
          map_smul' := fun r v => by
            rw [f.map_update_smul (Function.update base i c) j r v]; rfl }
      map_add' := fun c1 c2 => by
        ext v
        show f (Function.update (Function.update base i (c1 + c2)) j v) =
          f (Function.update (Function.update base i c1) j v) +
          f (Function.update (Function.update base i c2) j v)
        rw [Function.update_comm hij c1 v base, Function.update_comm hij c2 v base,
          Function.update_comm hij (c1 + c2) v base]
        rw [f.map_update_add (Function.update base j v) i c1 c2]
      map_smul' := fun r c => by
        ext v
        show f (Function.update (Function.update base i (r • c)) j v) =
          r • f (Function.update (Function.update base i c) j v)
        rw [Function.update_comm hij c v base, Function.update_comm hij (r • c) v base]
        rw [f.map_update_smul (Function.update base j v) i r c] }

set_option linter.unusedSectionVars false in
private lemma unitModel4SlotBilin_apply
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (i j : Fin 4) (hij : i ≠ j) (base : Fin 4 → E) (c v : E) :
    unitModel4SlotBilin (E := E) f i j hij base c v =
      f (Function.update (Function.update base i c) j v) := rfl

set_option linter.unusedSectionVars false in
private lemma euclidPartial_add_local
    (l : Fin (Module.finrank ℝ E))
    {f h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    euclidPartial (E := E) l (fun z => f z + h z) y =
      euclidPartial (E := E) l f y + euclidPartial (E := E) l h y := by
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def, fderiv_fun_add hf hh,
    ContinuousLinearMap.add_apply]

set_option linter.unusedSectionVars false in
private lemma partialDeriv_scalarOnE_eq_euclidPartial_local
    (f : M → ℝ) (α : M) (m : Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    partialDeriv (E := E) m (scalarOnE (I := I) α f)
        (extChartAt I α ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      euclidPartial (E := E) m
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f) y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
      (I := I) hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]; exact (extChartAt I α).right_inv hy_pre
  rw [euclidPartial_def]
  have hpushed_eq :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f =ᶠ[𝓝 y]
        ((scalarOnE (I := I) α f) ∘ (toEuclidean (E := E)).symm) := by
    have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen
        (I := I) (M := M) α
    filter_upwards [hopen.mem_nhds hy] with z hz
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α f hz]
    rfl
  rw [Filter.EventuallyEq.fderiv_eq hpushed_eq]
  rw [(toEuclidean (E := E)).symm.comp_right_fderiv
    (f := scalarOnE (I := I) α f) (x := y)]
  rw [ContinuousLinearMap.comp_apply]
  rw [show (toEuclidean (E := E)).symm.toContinuousLinearMap
      (EuclideanSpace.single m (1 : ℝ)) = (chartModelBasis E) m from by
    rw [chartModelBasis_apply]; rfl]
  rw [partialDeriv]
  rw [show (toEuclidean (E := E)).symm y = extChartAt I α b from hphi_b.symm]

set_option linter.unusedSectionVars false in
noncomputable def arm2ReadoutCovDerivPair (g₀ : SmoothRiemannianMetric I M)
    (h : SmoothCcTensor g₀ 0 2) (x : M)
    (Jdx : Fin (2 + 2) → Fin (Module.finrank ℝ E)) : ℝ :=
  euclidPartial (E := E) (Jdx 0)
      (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x
        ((Matrix.vecTail Jdx) 0) ![]
        (Matrix.vecTail (Matrix.vecTail Jdx)) y')
      (toEuclidean (E := E) (extChartAt I x x))
    + covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 h) x (Jdx 0) ![]
        (Matrix.vecTail Jdx) (toEuclidean (E := E) (extChartAt I x x))

set_option linter.unusedSectionVars false in
private lemma covDerivLowerOrderTerm_differentiableAt_center
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g₀ r s) (x : M)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ r s S x m Idx Jdx)
      (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hcd : ContDiffOn ℝ ∞
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ r s S x m Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) x) :=
    covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g₀ r s S x m Idx Jdx
      (fun Idx' Jdx' => chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g₀ r s S x Idx' Jdx')
  exact (hcd.contDiffAt
    ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) x).mem_nhds hmem)).differentiableAt (by simp)

set_option linter.unusedSectionVars false in
private lemma euclidPartial_chartPushedRaw_differentiableAt_center
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g₀ r s) (x : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (euclidPartial (E := E) k
        (chartPushedRaw I x
          (tensorChartComponentRaw (I := I) (M := M) g₀ r s S x Idx Jdx)))
      (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hcd : ContDiffOn ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I x
          (tensorChartComponentRaw (I := I) (M := M) g₀ r s S x Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) x) :=
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g₀ r s S x k Idx Jdx
  exact (hcd.contDiffAt
    ((DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) x).mem_nhds hmem)).differentiableAt (by simp)

set_option linter.unusedSectionVars false in
private lemma unitModel4_basisChart_readout_split
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 h) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c, chartModelBasis E d] =
      euclidPartial (E := E) a
          (fun y' => euclidPartial (E := E) b
            (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
              h x ![] ![c, d])) y')
          (toEuclidean (E := E) (extChartAt I x x))
        + arm2ReadoutCovDerivPair (I := I) (M := M) g₀ h x ![a, b, c, d] := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hroundtrip : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [show (![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c,
        chartModelBasis E d] : Fin 4 → TangentSpace I x) =
      (fun j => chartModelBasis E ((![a, b, c, d] : Fin 4 → Fin (Module.finrank ℝ E)) j)) from by
    funext j; fin_cases j <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ (2 + 2)
    (iteratedCovGrad (I := I) g₀ 0 2 2 h) x (![a, b, c, d])]
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] (![a, b, c, d]) x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
        (iteratedCovGrad (I := I) g₀ 0 2 2 h) x ![] (![a, b, c, d])
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hroundtrip] ]
  rw [iteratedCovGrad2_chartComponent_readout (I := I) g₀ h x (![a, b, c, d])]
  have hJ0 : (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJ1 : (Matrix.vecTail (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) 0 = b := rfl
  have hJtail2 : Matrix.vecTail (Matrix.vecTail
      (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) = ![c, d] := by
    funext j; fin_cases j <;> rfl
  simp only [arm2ReadoutCovDerivPair, hJ0, hJ1, hJtail2, hroundtrip]
  have hPdiff : DifferentiableAt ℝ
      (euclidPartial (E := E) b
        (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d])))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    euclidPartial_chartPushedRaw_differentiableAt_center (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d]
  have hQdiff : DifferentiableAt ℝ
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d])
      (toEuclidean (E := E) (extChartAt I x x)) :=
    covDerivLowerOrderTerm_differentiableAt_center (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d]
  rw [euclidPartial_add_local a hPdiff hQdiff]
  ring

set_option linter.unusedSectionVars false in
private lemma euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (m₁ m₂ : Fin (Module.finrank ℝ E)) (a b : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) m₂
        (fun y' => euclidPartial (E := E) m₁
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b]))
          y')
        (toEuclidean (E := E) (extChartAt I x x)) =
      partialDeriv (E := E) m₂
        (partialDeriv (E := E) m₁
          (scalarOnE (I := I) x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b])))
        (extChartAt I x x) := by
  classical
  set f : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] with hf_def
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) x
  have hYmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  set gm : M → ℝ := fun p =>
    partialDeriv (E := E) m₁ (scalarOnE (I := I) x f) (extChartAt I x p) with hgm_def
  have hinner_eqOn : Set.EqOn
      (fun y' => euclidPartial (E := E) m₁ (chartPushedRaw I x f) y')
      (chartPushedRaw I x gm)
      (chartTargetEuclid (I := I) (M := M) x) := by
    intro y' hy'
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) x gm hy']
    show euclidPartial (E := E) m₁ (chartPushedRaw I x f) y' =
      partialDeriv (E := E) m₁ (scalarOnE (I := I) x f)
        (extChartAt I x ((extChartAt I x).symm ((toEuclidean (E := E)).symm y')))
    rw [partialDeriv_scalarOnE_eq_euclidPartial_local f x m₁ hy']
  have hinner_ev :
      (fun y' => euclidPartial (E := E) m₁ (chartPushedRaw I x f) y') =ᶠ[𝓝
        ((toEuclidean (E := E)) (extChartAt I x x))]
      (chartPushedRaw I x gm) :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hYmem) hinner_eqOn
  rw [show euclidPartial (E := E) m₂
        (fun y' => euclidPartial (E := E) m₁ (chartPushedRaw I x f) y')
        ((toEuclidean (E := E)) (extChartAt I x x)) =
      euclidPartial (E := E) m₂ (chartPushedRaw I x gm)
        ((toEuclidean (E := E)) (extChartAt I x x)) from by
    rw [euclidPartial_def, euclidPartial_def, hinner_ev.fderiv_eq] ]
  rw [← partialDeriv_scalarOnE_eq_euclidPartial_local gm x m₂ hYmem]
  have hscalarOnE_gm : scalarOnE (I := I) x gm =ᶠ[𝓝 (extChartAt I x x)]
      partialDeriv (E := E) m₁ (scalarOnE (I := I) x f) := by
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
      extChartAt_target_subset_interior_of_boundaryless (I := I) x htarget
    filter_upwards [isOpen_interior.mem_nhds hint] with z hz
    have hzt : z ∈ (extChartAt I x).target := interior_subset hz
    show partialDeriv (E := E) m₁ (scalarOnE (I := I) x f)
        (extChartAt I x ((extChartAt I x).symm z)) =
      partialDeriv (E := E) m₁ (scalarOnE (I := I) x f) z
    rw [(extChartAt I x).right_inv hzt]
  have hround : extChartAt I x ((extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) =
      extChartAt I x x := by
    rw [(toEuclidean (E := E)).symm_apply_apply]
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    rw [(extChartAt I x).right_inv htarget]
  rw [hround]
  rw [partialDeriv, partialDeriv]
  rw [Filter.EventuallyEq.fderiv_eq hscalarOnE_gm]

set_option linter.unusedSectionVars false in
private lemma realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (a b : Fin (Module.finrank ℝ E)) :
    realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b =ᶠ[𝓝 (extChartAt I x x)]
      (fun y => (1 / 2 : ℝ) *
        (scalarOnE (I := I) x
            (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b]) y +
          scalarOnE (I := I) x
            (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a]) y)) := by
  classical
  have hx_src : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source (I := I)]; exact mem_chart_source H x
  have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hx_src
  have htarget_open : IsOpen ((extChartAt I x).target : Set E) :=
    isOpen_extChartAt_target (I := I) x
  filter_upwards [htarget_open.mem_nhds htarget] with y hy_tgt
  have hp : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x).map_target hy_tgt
  rw [realizedGramDeriv]
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.chartGramOnE_realize_sub_eq_symm_rawComponent_two_witness
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b y hp]
  rw [scalarOnE_def, scalarOnE_def]

set_option linter.unusedSectionVars false in
private lemma scalarOnE_contDiffOn_tensorChartComponentRaw
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (scalarOnE (I := I) x
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] Jdx))
      (extChartAt I x).target := by
  classical
  set f : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] Jdx with hf_def
  have hpush : ContDiffOn ℝ ∞ (chartPushedRaw I x f)
      (chartTargetEuclid (I := I) (M := M) x) :=
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g₀ 0 2 S x ![] Jdx
  have hcomp : ContDiffOn ℝ ∞ ((chartPushedRaw I x f) ∘ (toEuclidean (E := E)))
      (extChartAt I x).target := by
    refine hpush.comp (toEuclidean (E := E)).contDiff.contDiffOn ?_
    intro z hz
    refine ⟨z, hz, rfl⟩
  refine hcomp.congr (fun z hz => ?_)
  have hzeucl : (toEuclidean (E := E)) z ∈ chartTargetEuclid (I := I) (M := M) x := ⟨z, hz, rfl⟩
  rw [Function.comp_apply,
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) x f hzeucl]
  rw [(toEuclidean (E := E)).symm_apply_apply]
  rw [scalarOnE_def]

set_option linter.unusedSectionVars false in
private lemma partialDeriv_scalarOnE_tensorChartComponentRaw_differentiableAt
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (m : Fin (Module.finrank ℝ E)) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) m
        (scalarOnE (I := I) x
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] Jdx)))
      (extChartAt I x x) := by
  classical
  set u : E → ℝ := scalarOnE (I := I) x
    (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] Jdx) with hu_def
  have hcd : ContDiffOn ℝ ∞ u (extChartAt I x).target :=
    scalarOnE_contDiffOn_tensorChartComponentRaw (I := I) (M := M) g₀ S x Jdx
  have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x
      ((extChartAt I x).map_source (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x))
  have hcd_int : ContDiffOn ℝ ∞ u (interior (extChartAt I x).target) := hcd.mono interior_subset
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) (interior (extChartAt I x).target) :=
    hcd_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hpd : ContDiffOn ℝ ∞ (partialDeriv (E := E) m u) (interior (extChartAt I x).target) := by
    unfold partialDeriv
    exact hfderiv.clm_apply contDiffOn_const
  exact (hpd.contDiffAt (isOpen_interior.mem_nhds hint)).differentiableAt (by simp)

set_option linter.unusedSectionVars false in
private lemma partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m₁ m₂ a b : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m₂
        (partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) =
      (1 / 2 : ℝ) * euclidPartial (E := E) m₂
          (fun y' => euclidPartial (E := E) m₁
            (chartPushedRaw I x
              (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b])) y')
          (toEuclidean (E := E) (extChartAt I x x)) +
        (1 / 2 : ℝ) * euclidPartial (E := E) m₂
          (fun y' => euclidPartial (E := E) m₁
            (chartPushedRaw I x
              (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a])) y')
          (toEuclidean (E := E) (extChartAt I x x)) := by
  classical
  rw [euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE (I := I) g₀ (T - T') x m₁ m₂ a b]
  rw [euclidPartial2_chartPushedRaw_eq_partialDeriv2_scalarOnE (I := I) g₀ (T - T') x m₁ m₂ b a]
  set fab : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b]
    with hfab_def
  set fba : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a]
    with hfba_def
  set Pab : E → ℝ := partialDeriv (E := E) m₁ (scalarOnE (I := I) x fab) with hPab_def
  set Pba : E → ℝ := partialDeriv (E := E) m₁ (scalarOnE (I := I) x fba) with hPba_def
  have hev := realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x a b
  have hev1 : partialDeriv (E := E) m₁
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) =ᶠ[𝓝 (extChartAt I x x)]
      (fun y => (1 / 2 : ℝ) * (Pab y + Pba y)) := by
    have hdab : ∀ᶠ y in 𝓝 (extChartAt I x x),
        DifferentiableAt ℝ (scalarOnE (I := I) x fab) y := by
      have hcd : ContDiffOn ℝ ∞ (scalarOnE (I := I) x fab) (extChartAt I x).target :=
        scalarOnE_contDiffOn_tensorChartComponentRaw (I := I) (M := M) g₀ (T - T') x ![a, b]
      have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
        extChartAt_target_subset_interior_of_boundaryless (I := I) x
          ((extChartAt I x).map_source (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x))
      filter_upwards [isOpen_interior.mem_nhds hint] with z hz
      exact ((hcd.mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)
    have hdba : ∀ᶠ y in 𝓝 (extChartAt I x x),
        DifferentiableAt ℝ (scalarOnE (I := I) x fba) y := by
      have hcd : ContDiffOn ℝ ∞ (scalarOnE (I := I) x fba) (extChartAt I x).target :=
        scalarOnE_contDiffOn_tensorChartComponentRaw (I := I) (M := M) g₀ (T - T') x ![b, a]
      have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
        extChartAt_target_subset_interior_of_boundaryless (I := I) x
          ((extChartAt I x).map_source (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x))
      filter_upwards [isOpen_interior.mem_nhds hint] with z hz
      exact ((hcd.mono interior_subset).contDiffAt
        (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)
    have hpd_ev : partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b) =ᶠ[𝓝 (extChartAt I x x)]
        partialDeriv (E := E) m₁
          (fun y => (1 / 2 : ℝ) * (scalarOnE (I := I) x fab y + scalarOnE (I := I) x fba y)) := by
      filter_upwards [hev.eventuallyEq_nhds] with z hz
      unfold partialDeriv
      rw [hz.fderiv_eq]
    filter_upwards [hpd_ev, hdab, hdba] with z hz hdz_ab hdz_ba
    rw [hz]
    rw [partialDeriv_const_mul (1 / 2 : ℝ)
        (fun y => scalarOnE (I := I) x fab y + scalarOnE (I := I) x fba y)
        (hdz_ab.add hdz_ba)]
    rw [partialDeriv_add (scalarOnE (I := I) x fab) (scalarOnE (I := I) x fba) hdz_ab hdz_ba]
  have hfinal : partialDeriv (E := E) m₂
        (partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) =
      partialDeriv (E := E) m₂ (fun y => (1 / 2 : ℝ) * (Pab y + Pba y)) (extChartAt I x x) := by
    show fderiv ℝ
        (partialDeriv (E := E) m₁
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
        (extChartAt I x x) ((chartModelBasis E) m₂) =
      fderiv ℝ (fun y => (1 / 2 : ℝ) * (Pab y + Pba y)) (extChartAt I x x) ((chartModelBasis E) m₂)
    rw [hev1.fderiv_eq]
  rw [hfinal]
  have hPab_diff : DifferentiableAt ℝ Pab (extChartAt I x x) :=
    partialDeriv_scalarOnE_tensorChartComponentRaw_differentiableAt (I := I) (M := M) g₀
      (T - T') x m₁ ![a, b]
  have hPba_diff : DifferentiableAt ℝ Pba (extChartAt I x x) :=
    partialDeriv_scalarOnE_tensorChartComponentRaw_differentiableAt (I := I) (M := M) g₀
      (T - T') x m₁ ![b, a]
  rw [partialDeriv_const_mul (1 / 2 : ℝ) (fun y => Pab y + Pba y)
      (hPab_diff.add hPba_diff)]
  rw [partialDeriv_add Pab Pba hPab_diff hPba_diff]
  ring

set_option linter.unusedSectionVars false in
noncomputable def arm2ChartReadoutResidual (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i k : Fin (Module.finrank ℝ E)) (s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
        (arm2ReadoutCovDerivPair (I := I) (M := M) g₀ (T - T') x ![l, k, i, k₁]
          + arm2ReadoutCovDerivPair (I := I) (M := M) g₀ (T - T') x ![l, i, k, k₁]
          - arm2ReadoutCovDerivPair (I := I) (M := M) g₀ (T - T') x ![l, k₁, k, i]) -
    (1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
        arm2ReadoutCovDerivPair (I := I) (M := M) g₀ (T - T') x ![k, i, l, k₁]

set_option linter.unusedSectionVars false in
private lemma eP2_swap
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) a
        (fun y' => euclidPartial (E := E) b
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![c, d]))
          y')
        (toEuclidean (E := E) (extChartAt I x x)) =
      euclidPartial (E := E) b
        (fun y' => euclidPartial (E := E) a
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![c, d]))
          y')
        (toEuclidean (E := E) (extChartAt I x x)) := by
  classical
  set u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![c, d])
    with hu_def
  set Y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (E := E) (extChartAt I x x) with hY_def
  have hmem : Y ∈ chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) x
  have hcd : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) x) :=
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g₀ 0 2 S x ![] ![c, d]
  have hcdAt : ContDiffAt ℝ ∞ u Y :=
    hcd.contDiffAt (hopen.mem_nhds hmem)
  have hsymm2 : IsSymmSndFDerivAt ℝ u Y := by
    refine ContDiffAt.isSymmSndFDerivAt hcdAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    decide
  have hg_diff : DifferentiableAt ℝ (fderiv ℝ u) Y := by
    have hcd_int : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) x) := hcd
    have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) (chartTargetEuclid (I := I) (M := M) x) :=
      hcd_int.fderiv_of_isOpen hopen (by rw [ENat.coe_top_add_one])
    exact (hfderiv.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
  have hkey : ∀ r t : Fin (Module.finrank ℝ E),
      euclidPartial (E := E) r
          (fun y' => euclidPartial (E := E) t u y') Y =
        (fderiv ℝ (fderiv ℝ u) Y (EuclideanSpace.single r 1))
          (EuclideanSpace.single t 1) := by
    intro r t
    rw [euclidPartial_def]
    set L : (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single t 1) with hL
    have hcomp_eq : (fun z => euclidPartial (E := E) t u z) =
        L ∘ (fderiv ℝ u) := by
      funext z; rw [euclidPartial_def]; rfl
    rw [hcomp_eq, fderiv_comp Y L.differentiableAt hg_diff, L.fderiv]
    rfl
  rw [hkey a b, hkey b a]
  exact (hsymm2 _ _).symm

set_option linter.unusedSectionVars false in
private lemma rawComponentTwo_swap_of_symm
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hSsymm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ S p v w = ccTensorBilin (I := I) g₀ S p w v)
    (x : M) (c d : Fin (Module.finrank ℝ E)) :
    chartPushedRaw I x
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![c, d]) =
      chartPushedRaw I x
        (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![d, c]) := by
  classical
  have hpt : ∀ p : M, p ∈ (chartAt H x).source →
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![c, d] p =
        tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![d, c] p := by
    intro p hp
    have hrawCD := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g₀ 0 2
      S x hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
      (![c, d] : Fin 2 → Fin (Module.finrank ℝ E))
    have hrawDC := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g₀ 0 2
      S x hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
      (![d, c] : Fin 2 → Fin (Module.finrank ℝ E))
    have hframe : chartFrameBasisModel (I := I) (M := M) x p 0
        (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) := by
      apply ContinuousMultilinearMap.ext
      intro v
      have h := chartFrameBasisModel_apply (I := I) (M := M) x p 0
        (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
      rw [Fin.prod_univ_zero] at h
      rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      exact h
    rw [hframe] at hrawCD hrawDC
    have hbilin : ∀ (a b : Fin (Module.finrank ℝ E)),
        (S.toSection p
            (ContinuousMultilinearMap.constOfIsEmpty ℝ
              (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) :
          ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I p) ℝ)
            (fun j : Fin 2 =>
              chartBasisVecFiber (I := I) x ((![a, b] : Fin 2 → _) j) p) =
          ccTensorBilin (I := I) g₀ S p
              (chartBasisVecFiber (I := I) x a p) (chartBasisVecFiber (I := I) x b p) := by
      intro a b
      have hvec : (fun j : Fin 2 =>
          chartBasisVecFiber (I := I) x ((![a, b] : Fin 2 → _) j) p) =
          ![chartBasisVecFiber (I := I) x a p, chartBasisVecFiber (I := I) x b p] := by
        funext j; fin_cases j <;> rfl
      rw [hvec, ccTensorBilin_apply]
      rfl
    rw [hrawCD, hrawDC, hbilin c d, hbilin d c]
    exact hSsymm p (chartBasisVecFiber (I := I) x c p) (chartBasisVecFiber (I := I) x d p)
  funext y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) x
  · rw [chartPushedRaw_apply_of_mem _ _ hy, chartPushedRaw_apply_of_mem _ _ hy]
    exact hpt _ (symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) x hy)
  · rw [chartPushedRaw_apply_of_notMem _ _ hy, chartPushedRaw_apply_of_notMem _ _ hy]

set_option linter.unusedSectionVars false in
private lemma eP2_componentSwap_of_symm
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (hSsymm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ S p v w = ccTensorBilin (I := I) g₀ S p w v)
    (x : M) (a b c d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) a
        (fun y' => euclidPartial (E := E) b
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![c, d]))
          y')
        (toEuclidean (E := E) (extChartAt I x x)) =
      euclidPartial (E := E) a
        (fun y' => euclidPartial (E := E) b
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![d, c]))
          y')
        (toEuclidean (E := E) (extChartAt I x x)) := by
  rw [rawComponentTwo_swap_of_symm (I := I) (M := M) g₀ S hSsymm x c d]

set_option linter.unusedSectionVars false in
private lemma ccTensorBilin_sub_symm_of_symm
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T p v w = ccTensorBilin (I := I) g₀ T p w v)
    (hT'symm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T' p v w = ccTensorBilin (I := I) g₀ T' p w v)
    (p : M) (v w : TangentSpace I p) :
    ccTensorBilin (I := I) g₀ (T - T') p v w =
      ccTensorBilin (I := I) g₀ (T - T') p w v := by
  have hsub : ∀ (u₁ u₂ : TangentSpace I p),
      ccTensorBilin (I := I) g₀ (T - T') p u₁ u₂ =
        ccTensorBilin (I := I) g₀ T p u₁ u₂ - ccTensorBilin (I := I) g₀ T' p u₁ u₂ := by
    intro u₁ u₂
    have hTT' : (T - T' : SmoothCcTensor g₀ 0 2) = T + (-1 : ℝ) • T' := by
      rw [neg_one_smul, ← sub_eq_add_neg]
    rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply, hTT',
      ccTensorModel_add, ccTensorModel_smul, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.smul_apply]
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [hsub v w, hsub w v, hTsymm p v w, hT'symm p v w]

private lemma arm2_eP2_abstract_sum_identity {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hAsymm : ∀ j l, A j l = A l j)
    (e : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hswap1 : ∀ a b c d, e a b c d = e b a c d)
    (hcomp : ∀ a b c d, e a b c d = e a b d c)
    (i k : Fin n) :
    (1 / 2 : ℝ) * (∑ j : Fin n, ∑ l : Fin n,
          A j l * (e j i l k + e j k l i - e j l i k)) -
      (1 / 2 : ℝ) * (∑ j : Fin n, ∑ l : Fin n,
          A j l * (e k i l j + e k j l i - e k l i j)) =
      (1 / 2 : ℝ) * (∑ k₁ : Fin n, ∑ l : Fin n,
          A k₁ l * (e l k i k₁ + e l i k k₁ - e l k₁ k i)) -
        (1 / 2 : ℝ) * (∑ k₁ : Fin n, ∑ l : Fin n,
          A k₁ l * e k i l k₁) := by
  classical
  have hL1 : (∑ j : Fin n, ∑ l : Fin n, A j l * e j i l k) =
      ∑ j : Fin n, ∑ l : Fin n, A j l * e l i k j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [hAsymm l j, hcomp l i j k]
  have hLexp : (∑ j : Fin n, ∑ l : Fin n,
        A j l * (e j i l k + e j k l i - e j l i k)) -
      (∑ j : Fin n, ∑ l : Fin n,
        A j l * (e k i l j + e k j l i - e k l i j)) =
      ((∑ j : Fin n, ∑ l : Fin n, A j l * e j i l k)
        + (∑ j : Fin n, ∑ l : Fin n, A j l * e j k l i)
        - (∑ j : Fin n, ∑ l : Fin n, A j l * e j l i k))
      - ((∑ j : Fin n, ∑ l : Fin n, A j l * e k i l j)
        + (∑ j : Fin n, ∑ l : Fin n, A j l * e k j l i)
        - (∑ j : Fin n, ∑ l : Fin n, A j l * e k l i j)) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hRexp : (∑ k₁ : Fin n, ∑ l : Fin n,
        A k₁ l * (e l k i k₁ + e l i k k₁ - e l k₁ k i)) -
      (∑ k₁ : Fin n, ∑ l : Fin n, A k₁ l * e k i l k₁) =
      ((∑ j : Fin n, ∑ l : Fin n, A j l * e l k i j)
        + (∑ j : Fin n, ∑ l : Fin n, A j l * e l i k j)
        - (∑ j : Fin n, ∑ l : Fin n, A j l * e l j k i))
      - (∑ j : Fin n, ∑ l : Fin n, A j l * e k i l j) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hT2 : (∑ j : Fin n, ∑ l : Fin n, A j l * e j k l i) =
      ∑ j : Fin n, ∑ l : Fin n, A j l * e k j l i :=
    Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by rw [hswap1 j k l i]))
  have hT3 : (∑ j : Fin n, ∑ l : Fin n, A j l * e j l i k) =
      ∑ j : Fin n, ∑ l : Fin n, A j l * e l j k i :=
    Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by
      rw [hswap1 j l i k, hcomp l j i k]))
  have hT6 : (∑ j : Fin n, ∑ l : Fin n, A j l * e k l i j) =
      ∑ j : Fin n, ∑ l : Fin n, A j l * e l k i j :=
    Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by rw [hswap1 k l i j]))
  rw [← mul_sub, ← mul_sub, hLexp, hRexp, hL1, hT2, hT3, hT6]
  ring

set_option linter.unusedSectionVars false in
theorem arm2_principalSymbol_chartSlope_eP2_identity
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T p v w = ccTensorBilin (I := I) g₀ T p w v)
    (hT'symm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T' p v w = ccTensorBilin (I := I) g₀ T' p w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i k : Fin (Module.finrank ℝ E)) :
    chartSlopePrincipalSymbolContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
        (extChartAt I x x) s =
      (1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
            ((fun a b c d => euclidPartial (E := E) a
                (fun y' => euclidPartial (E := E) b
                  (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
                    (T - T') x ![] ![c, d])) y')
                (toEuclidean (E := E) (extChartAt I x x))) l k i k₁ +
              (fun a b c d => euclidPartial (E := E) a
                (fun y' => euclidPartial (E := E) b
                  (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
                    (T - T') x ![] ![c, d])) y')
                (toEuclidean (E := E) (extChartAt I x x))) l i k k₁ -
              (fun a b c d => euclidPartial (E := E) a
                (fun y' => euclidPartial (E := E) b
                  (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
                    (T - T') x ![] ![c, d])) y')
                (toEuclidean (E := E) (extChartAt I x x))) l k₁ k i) -
        (1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x k₁ l *
            (fun a b c d => euclidPartial (E := E) a
                (fun y' => euclidPartial (E := E) b
                  (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
                    (T - T') x ![] ![c, d])) y')
                (toEuclidean (E := E) (extChartAt I x x))) k i l k₁ := by
  classical
  set eP2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b c d => euclidPartial (E := E) a
        (fun y' => euclidPartial (E := E) b
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (T - T') x ![] ![c, d])) y')
        (toEuclidean (E := E) (extChartAt I x x)) with heP2
  set A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun j l => chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x j l
    with hA_def
  have hTT'symm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ (T - T') p v w =
        ccTensorBilin (I := I) g₀ (T - T') p w v :=
    ccTensorBilin_sub_symm_of_symm (I := I) g₀ T T' hTsymm hT'symm
  have hcomp : ∀ a b c d, eP2 a b c d = eP2 a b d c := by
    intro a b c d
    rw [heP2]
    exact eP2_componentSwap_of_symm (I := I) g₀ (T - T') hTT'symm x a b c d
  have hAsymm : ∀ j l, A j l = A l j := by
    intro j l
    rw [hA_def]
    have hHerm : (chartInvGramMatrix (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) x x).IsHermitian := by
      unfold chartInvGramMatrix
      exact (chartGramMatrix_isHermitian (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) x x).inv
    have hentry := hHerm.apply l j
    rwa [star_trivial] at hentry
  have hP : ∀ (m₂ m₁ a b : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) m₂
          (partialDeriv (E := E) m₁
            (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b))
          (extChartAt I x x) = eP2 m₂ m₁ a b := by
    intro m₂ m₁ a b
    rw [partialDeriv2_realizedGramDeriv_eq_half_sum_euclidPartial2 (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x m₁ m₂ a b]
    rw [heP2]
    rw [show euclidPartial (E := E) m₂
            (fun y' => euclidPartial (E := E) m₁
              (chartPushedRaw I x
                (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a])) y')
            (toEuclidean (E := E) (extChartAt I x x)) =
          euclidPartial (E := E) m₂
            (fun y' => euclidPartial (E := E) m₁
              (chartPushedRaw I x
                (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b])) y')
            (toEuclidean (E := E) (extChartAt I x x)) from
      (eP2_componentSwap_of_symm (I := I) g₀ (T - T') hTT'symm x m₂ m₁ a b).symm]
    ring
  have hAval : ∀ (j l : Fin (Module.finrank ℝ E)),
      chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x j l
          (extChartAt I x x) = A j l := by
    intro j l
    rw [hA_def, chartInvGramOnE_def, (extChartAt I x).left_inv (mem_extChartAt_source x)]
  have hAmat : ∀ (j l : Fin (Module.finrank ℝ E)),
      chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x x j l = A j l :=
    fun j l => rfl
  have hswap1 : ∀ a b c d, eP2 a b c d = eP2 b a c d := by
    intro a b c d
    rw [heP2]
    exact eP2_swap (I := I) g₀ (T - T') x a b c d
  rw [chartSlopePrincipalSymbolContribution]
  simp only [hAval, hP, hAmat]
  exact arm2_eP2_abstract_sum_identity A hAsymm eP2 hswap1 hcomp i k

set_option linter.unusedSectionVars false in
theorem arm2_combinedTrace_eq_chartSlopePrincipal_add_residual
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T p v w = ccTensorBilin (I := I) g₀ T p w v)
    (hT'symm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T' p v w = ccTensorBilin (I := I) g₀ T' p w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i k : Fin (Module.finrank ℝ E)) :
    (1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E),
          (unitModel (I := I) (M := M) g₀ 4
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
              (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k₁)))
                ![(chartModelBasis E) k, (chartModelBasis E) i, (Module.finBasis ℝ E) k₁])
            + unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
                (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k₁)))
                  ![(chartModelBasis E) i, (chartModelBasis E) k, (Module.finBasis ℝ E) k₁])
            - unitModel (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
                (Fin.cons (cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k₁)))
                  (Fin.cons ((Module.finBasis ℝ E) k₁)
                    ![(chartModelBasis E) k, (chartModelBasis E) i]))) +
        -(1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E),
          unitModel (I := I) (M := M) g₀ 4 (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) x
            ![(chartModelBasis E) k, (chartModelBasis E) i,
              cometricLmodel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k₁)),
              (Module.finBasis ℝ E) k₁] =
      chartSlopePrincipalSymbolContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s +
        arm2ChartReadoutResidual (I := I) g₀ T T' hδ hδ' x i k s := by
  classical
  set W : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW_def
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
  set fW : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ :=
    Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) with hfW_def
  have hfW_eq : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 W x v = fW v := fun v => rfl
  set bch : Fin (Module.finrank ℝ E) → TangentSpace I x := fun t => chartModelBasis E t with hbch
  have hbk : (chartModelBasis E k : TangentSpace I x) = bch k := rfl
  have hbi : (chartModelBasis E i : TangentSpace I x) = bch i := rfl
  set covec : Fin (Module.finrank ℝ E) → TangentSpace I x := fun k₁ =>
    cometricLmodel (I := I) g₁ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k₁)) with hcovec
  have hreadout : ∀ a b c d : Fin (Module.finrank ℝ E),
      fW ![bch a, bch b, bch c, bch d] =
        euclidPartial (E := E) a
            (fun y' => euclidPartial (E := E) b
              (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
                (T - T') x ![] ![c, d])) y')
            (toEuclidean (E := E) (extChartAt I x x))
          + arm2ReadoutCovDerivPair (I := I) (M := M) g₀ (T - T') x ![a, b, c, d] := by
    intro a b c d
    rw [← hfW_eq]
    exact unitModel4_basisChart_readout_split (I := I) (M := M) g₀ (T - T') x a b c d
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  set F1 : E →L[ℝ] E →L[ℝ] ℝ :=
    unitModel4SlotBilin (E := E) fW 0 3 h03 ![0, bch k, bch i, 0] with hF1
  set F2 : E →L[ℝ] E →L[ℝ] ℝ :=
    unitModel4SlotBilin (E := E) fW 0 3 h03 ![0, bch i, bch k, 0] with hF2
  set F3 : E →L[ℝ] E →L[ℝ] ℝ :=
    unitModel4SlotBilin (E := E) fW 0 1 h01 ![0, 0, bch k, bch i] with hF3
  set F4 : E →L[ℝ] E →L[ℝ] ℝ :=
    unitModel4SlotBilin (E := E) fW 2 3 h23 ![bch k, bch i, 0, 0] with hF4
  have hF1app : ∀ c v : TangentSpace I x, F1 c v = fW ![c, bch k, bch i, v] := by
    intro c v
    rw [hF1, unitModel4SlotBilin_apply]
    congr 1; funext j; fin_cases j <;> simp [Function.update]
  have hF2app : ∀ c v : TangentSpace I x, F2 c v = fW ![c, bch i, bch k, v] := by
    intro c v
    rw [hF2, unitModel4SlotBilin_apply]
    congr 1; funext j; fin_cases j <;> simp [Function.update]
  have hF3app : ∀ c v : TangentSpace I x, F3 c v = fW ![c, v, bch k, bch i] := by
    intro c v
    rw [hF3, unitModel4SlotBilin_apply]
    congr 1; funext j; fin_cases j <;> simp [Function.update]
  have hF4app : ∀ c v : TangentSpace I x, F4 c v = fW ![bch k, bch i, c, v] := by
    intro c v
    rw [hF4, unitModel4SlotBilin_apply]
    congr 1; funext j; fin_cases j <;> simp [Function.update]
  have htraceFirst := cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x (F1 + F2 - F3)
  have htraceT4 := cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x F4
  have hLHS_first : ∑ k₁ : Fin (Module.finrank ℝ E),
        (unitModel (I := I) (M := M) g₀ 4 W x
            (Fin.cons (covec k₁)
              ![bch k, bch i, (Module.finBasis ℝ E) k₁])
          + unitModel (I := I) (M := M) g₀ 4 W x
              (Fin.cons (covec k₁)
                ![bch i, bch k, (Module.finBasis ℝ E) k₁])
          - unitModel (I := I) (M := M) g₀ 4 W x
              (Fin.cons (covec k₁)
                (Fin.cons ((Module.finBasis ℝ E) k₁) ![bch k, bch i]))) =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ l •
          (fW ![bch l, bch k, bch i, bch k₁] + fW ![bch l, bch i, bch k, bch k₁]
            - fW ![bch l, bch k₁, bch k, bch i]) := by
    have hper : ∀ k₁ : Fin (Module.finrank ℝ E),
        (unitModel (I := I) (M := M) g₀ 4 W x
              (Fin.cons (covec k₁) ![bch k, bch i, (Module.finBasis ℝ E) k₁])
            + unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (covec k₁) ![bch i, bch k, (Module.finBasis ℝ E) k₁])
            - unitModel (I := I) (M := M) g₀ 4 W x
                (Fin.cons (covec k₁)
                  (Fin.cons ((Module.finBasis ℝ E) k₁) ![bch k, bch i]))) =
          (F1 + F2 - F3) (covec k₁) ((Module.finBasis ℝ E) k₁) := by
      intro k₁
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
      rw [hF1app, hF2app, hF3app, hfW_eq, hfW_eq, hfW_eq]
      congr 1
    rw [Finset.sum_congr rfl (fun k₁ _ => hper k₁)]
    simp only [hcovec]
    rw [htraceFirst]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
    rw [hF1app, hF2app, hF3app]
  have hLHS_T4 : ∑ k₁ : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
          ![bch k, bch i, covec k₁, (Module.finBasis ℝ E) k₁] =
      ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ l • fW ![bch k, bch i, bch l, bch k₁] := by
    have hper : ∀ k₁ : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W x
            ![bch k, bch i, covec k₁, (Module.finBasis ℝ E) k₁] =
          F4 (covec k₁) ((Module.finBasis ℝ E) k₁) := by
      intro k₁
      rw [hF4app, hfW_eq]
    rw [Finset.sum_congr rfl (fun k₁ _ => hper k₁)]
    simp only [hcovec]
    rw [htraceT4]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [hF4app]
  rw [hLHS_first, hLHS_T4]
  simp only [hreadout]
  set eP2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b c d => euclidPartial (E := E) a
        (fun y' => euclidPartial (E := E) b
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            (T - T') x ![] ![c, d])) y')
        (toEuclidean (E := E) (extChartAt I x x)) with heP2
  set Rd : (Fin (2 + 2) → Fin (Module.finrank ℝ E)) → ℝ :=
    fun Jdx => arm2ReadoutCovDerivPair (I := I) (M := M) g₀ (T - T') x Jdx with hRd
  set C : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun a b => chartInvGramMatrix (I := I) g₁ x x a b with hC
  have hresid : arm2ChartReadoutResidual (I := I) g₀ T T' hδ hδ' x i k s =
        (1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          C k₁ l * (Rd ![l, k, i, k₁] + Rd ![l, i, k, k₁] - Rd ![l, k₁, k, i]) -
        (1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          C k₁ l * Rd ![k, i, l, k₁] := rfl
  have hprin : chartSlopePrincipalSymbolContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
        (extChartAt I x x) s =
      (1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          C k₁ l * (eP2 l k i k₁ + eP2 l i k k₁ - eP2 l k₁ k i) -
        (1 / 2 : ℝ) * ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          C k₁ l * eP2 k i l k₁ :=
    arm2_principalSymbol_chartSlope_eP2_identity (I := I) g₀ T T' hTsymm hT'symm
      hδ_lt hδ hδ'_lt hδ' s x i k
  rw [hresid, hprin]
  simp only [hC, smul_eq_mul]
  have key : ∀ (cf : ℝ) (G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      cf * ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), G k₁ l =
        ∑ k₁ : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), cf * G k₁ l := by
    intro cf G
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k₁ _ => Finset.mul_sum _ _ _)
  simp only [neg_mul, key]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

set_option linter.unusedSectionVars false in
theorem iteratedCovGrad1_chartComponent_readout (g₀ : SmoothRiemannianMetric I M)
    (h : SmoothCcTensor g₀ 0 2) (x : M)
    (Jdx : Fin (2 + 1) → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] Jdx
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm (toEuclidean (E := E) (extChartAt I x x)))) =
      euclidPartial (E := E) (Jdx 0)
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            h x ![] (Matrix.vecTail Jdx)))
          (toEuclidean (E := E) (extChartAt I x x))
        + covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x
            (Jdx 0) ![] (Matrix.vecTail Jdx)
            (toEuclidean (E := E) (extChartAt I x x)) := by
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hy : toEuclidean (E := E) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x hmemsrc
  have hcg : iteratedCovGrad (I := I) g₀ 0 2 1 h = covGrad (I := I) (M := M) g₀ 0 2 h := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [hcg]
  exact tensorChartComponentRaw_covGrad (I := I) (M := M) g₀ 0 2 h x ![] Jdx hy

set_option linter.unusedSectionVars false in
noncomputable def arm1ReadoutCovDeriv (g₀ : SmoothRiemannianMetric I M)
    (h : SmoothCcTensor g₀ 0 2) (x : M)
    (Jdx : Fin (2 + 1) → Fin (Module.finrank ℝ E)) : ℝ :=
  covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x
    (Jdx 0) ![] (Matrix.vecTail Jdx) (toEuclidean (E := E) (extChartAt I x x))

set_option linter.unusedSectionVars false in
private lemma unitModel3_basisChart_readout_split
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 3 (iteratedCovGrad (I := I) g₀ 0 2 1 h) x
        ![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] =
      euclidPartial (E := E) a
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2
            h x ![] ![b, c]))
          (toEuclidean (E := E) (extChartAt I x x))
        + arm1ReadoutCovDeriv (I := I) (M := M) g₀ h x ![a, b, c] := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hroundtrip : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [show (![chartModelBasis E a, chartModelBasis E b, chartModelBasis E c] :
        Fin 3 → TangentSpace I x) =
      (fun j => chartModelBasis E ((![a, b, c] : Fin 3 → Fin (Module.finrank ℝ E)) j)) from by
    funext j; fin_cases j <;> rfl]
  rw [unitModel_basisChart_eq_tensorChartComponentRaw (I := I) (M := M) g₀ (2 + 1)
    (iteratedCovGrad (I := I) g₀ 0 2 1 h) x (![a, b, c])]
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] (![a, b, c]) x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 1)
        (iteratedCovGrad (I := I) g₀ 0 2 1 h) x ![] (![a, b, c])
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hroundtrip] ]
  rw [iteratedCovGrad1_chartComponent_readout (I := I) g₀ h x (![a, b, c])]
  have hJ0 : (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = a := rfl
  have hJtail : Matrix.vecTail (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) = ![b, c] := by
    funext j; fin_cases j <;> rfl
  simp only [arm1ReadoutCovDeriv, hJ0, hJtail]

set_option linter.unusedSectionVars false in
private def unitModel3SlotBilin
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (i j : Fin 3) (hij : i ≠ j) (base : Fin 3 → E) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => LinearMap.toContinuousLinearMap
        { toFun := fun v => f (Function.update (Function.update base i c) j v)
          map_add' := fun v1 v2 => by
            rw [f.map_update_add (Function.update base i c) j v1 v2]
          map_smul' := fun r v => by
            rw [f.map_update_smul (Function.update base i c) j r v]; rfl }
      map_add' := fun c1 c2 => by
        ext v
        change f (Function.update (Function.update base i (c1 + c2)) j v) =
          f (Function.update (Function.update base i c1) j v) +
          f (Function.update (Function.update base i c2) j v)
        rw [Function.update_comm hij c1 v base, Function.update_comm hij c2 v base,
          Function.update_comm hij (c1 + c2) v base]
        rw [f.map_update_add (Function.update base j v) i c1 c2]
      map_smul' := fun r c => by
        ext v
        change f (Function.update (Function.update base i (r • c)) j v) =
          r • f (Function.update (Function.update base i c) j v)
        rw [Function.update_comm hij c v base, Function.update_comm hij (r • c) v base]
        rw [f.map_update_smul (Function.update base j v) i r c] }

set_option linter.unusedSectionVars false in
private lemma unitModel3SlotBilin_apply
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (i j : Fin 3) (hij : i ≠ j) (base : Fin 3 → E) (c v : E) :
    unitModel3SlotBilin (E := E) f i j hij base c v =
      f (Function.update (Function.update base i c) j v) := rfl

set_option linter.unusedSectionVars false in
theorem ricciArmOrder1KoszulCoeff_appCc_chartBasis_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 3)
    (x : M) (k' i' : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2 (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) W) x
        ![(chartModelBasis E) k', (chartModelBasis E) i'] =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k l *
            unitModel (I := I) (M := M) g₀ 3 W x
              ![(chartModelBasis E) l, (chartModelBasis E) k,
                raisedKoszulVec (I := I) g₀ g₁ x (chartModelBasis E k') (chartModelBasis E i')] := by
  classical
  rw [ricciArmOrder1KoszulCoeff_appCc_eq (I := I) (M := M) g₀ g₁ W x
    (![(chartModelBasis E) k', (chartModelBasis E) i'] : Fin 2 → TangentSpace I x)]
  set Wm : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ :=
    Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) with hWm
  have hWm_eq : ∀ w : Fin 3 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 3 W x w = Wm w := fun w => rfl
  set kvec : TangentSpace I x :=
    raisedKoszulVec (I := I) g₀ g₁ x (chartModelBasis E k') (chartModelBasis E i') with hkvec
  have hv0 : (![(chartModelBasis E) k', (chartModelBasis E) i'] : Fin 2 → TangentSpace I x) 0 =
      chartModelBasis E k' := rfl
  have hv1 : (![(chartModelBasis E) k', (chartModelBasis E) i'] : Fin 2 → TangentSpace I x) 1 =
      chartModelBasis E i' := rfl
  rw [hv0, hv1]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  set F : E →L[ℝ] E →L[ℝ] ℝ :=
    unitModel3SlotBilin (E := E) Wm 0 1 h01 ![0, 0, kvec] with hF
  have hFapp : ∀ c v : TangentSpace I x, F c v = Wm ![c, v, kvec] := by
    intro c v
    rw [hF, unitModel3SlotBilin_apply]
    congr 1
    funext j; fin_cases j <;> simp [Function.update]
  have hkey : ∀ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
            W.toSection x) (unitTensor (I := I) (M := M) x))
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            ![(Module.finBasis ℝ E) k, kvec]) =
        F (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          ((Module.finBasis ℝ E) k) := by
    intro k
    rw [hFapp]
    rfl
  rw [Finset.sum_congr rfl (fun k _ => hkey k)]
  rw [cometricFinBasisTrace_eq_chartInvGram_bilin (I := I) g₁ x F]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [smul_eq_mul, hFapp, hWm_eq]

set_option linter.unusedSectionVars false in
private lemma unitModel3_slot2_chartBasis_sum
    (g₀ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 3) (x : M)
    (l k : Fin (Module.finrank ℝ E)) (w : Fin (Module.finrank ℝ E) → ℝ) :
    unitModel (I := I) (M := M) g₀ 3 W x
        ![(chartModelBasis E) l, (chartModelBasis E) k,
          ∑ p : Fin (Module.finrank ℝ E), w p • (chartModelBasis E p : TangentSpace I x)] =
      ∑ p : Fin (Module.finrank ℝ E),
        w p * unitModel (I := I) (M := M) g₀ 3 W x
          ![(chartModelBasis E) l, (chartModelBasis E) k, (chartModelBasis E) p] := by
  classical
  set Wm : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace I x) ℝ :=
    Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) with hWm
  have hWm_eq : ∀ v : Fin 3 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 3 W x v = Wm v := fun v => rfl
  rw [hWm_eq]
  rw [show Wm ![(chartModelBasis E l : TangentSpace I x), (chartModelBasis E k : TangentSpace I x),
          ∑ p : Fin (Module.finrank ℝ E), w p • (chartModelBasis E p : TangentSpace I x)] =
        (Wm.toContinuousLinearMap
          ![(chartModelBasis E l : TangentSpace I x), (chartModelBasis E k : TangentSpace I x),
            (0 : TangentSpace I x)] 2)
          (∑ p : Fin (Module.finrank ℝ E), w p • (chartModelBasis E p : TangentSpace I x)) from by
    rw [ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext j; fin_cases j <;> simp [Function.update] ]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_smul, smul_eq_mul, hWm_eq]
  refine congrArg (fun t : ℝ => w p * t) ?_
  rw [ContinuousMultilinearMap.toContinuousLinearMap_apply]
  congr 1
  funext j; fin_cases j <;> simp [Function.update]

set_option linter.unusedSectionVars false in
theorem ricciArmOrder1KoszulCoeff_appCc_chartBasis_koszulExpanded
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 3)
    (x : M) (k' i' : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2 (ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀ g₁) W) x
        ![(chartModelBasis E) k', (chartModelBasis E) i'] =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ x x k l *
            ((∑ l₁ : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g₀ x x p l₁ *
                  (∑ q : Fin (Module.finrank ℝ E),
                    (chartChristoffel (I := I) g₁ x i' k' q (extChartAt I x x) -
                      chartChristoffel (I := I) g₀ x i' k' q (extChartAt I x x)) *
                      chartGramMatrix (I := I) g₁ x x q l₁)) *
              unitModel (I := I) (M := M) g₀ 3 W x
                ![(chartModelBasis E) l, (chartModelBasis E) k, (chartModelBasis E) p]) := by
  classical
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) x, extChartAt_source (I := I)]
    exact mem_chart_source H x
  have hself : ∀ t : Fin (Module.finrank ℝ E),
      chartBasisVecFiber (I := I) x t x = chartModelBasis E t := fun t =>
    chartBasisVecFiber_self (I := I) x t
  rw [ricciArmOrder1KoszulCoeff_appCc_chartBasis_eq (I := I) (M := M) g₀ g₁ W x k' i']
  have hkos : raisedKoszulVec (I := I) g₀ g₁ x (chartModelBasis E k') (chartModelBasis E i') =
      ∑ p : Fin (Module.finrank ℝ E),
        (fun p => ∑ l₁ : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₀ x x p l₁ *
            (∑ q : Fin (Module.finrank ℝ E),
              (chartChristoffel (I := I) g₁ x i' k' q (extChartAt I x x) -
                chartChristoffel (I := I) g₀ x i' k' q (extChartAt I x x)) *
                chartGramMatrix (I := I) g₁ x x q l₁)) p •
          (chartModelBasis E p : TangentSpace I x) := by
    rw [show (chartModelBasis E k' : TangentSpace I x) = chartBasisVecFiber (I := I) x k' x from
        (hself k').symm,
      show (chartModelBasis E i' : TangentSpace I x) = chartBasisVecFiber (I := I) x i' x from
        (hself i').symm]
    rw [raisedKoszulVec_realizedFam_chartα (I := I) g₀ g₁ x hxgood k' i']
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hself p]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  rw [← Finset.mul_sum]
  refine congrArg (fun t : ℝ => chartInvGramMatrix (I := I) g₁ x x k l * t) ?_
  rw [hkos]
  rw [unitModel3_slot2_chartBasis_sum (I := I) (M := M) g₀ W x l k
    (fun p => ∑ l₁ : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g₀ x x p l₁ *
        (∑ q : Fin (Module.finrank ℝ E),
          (chartChristoffel (I := I) g₁ x i' k' q (extChartAt I x x) -
            chartChristoffel (I := I) g₀ x i' k' q (extChartAt I x x)) *
            chartGramMatrix (I := I) g₁ x x q l₁))]

set_option linter.unusedSectionVars false in
theorem arm2_principalSymbol_chart_match
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T p v w = ccTensorBilin (I := I) g₀ T p w v)
    (hT'symm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T' p v w = ccTensorBilin (I := I) g₀ T' p w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (x : M) (i k : Fin (Module.finrank ℝ E)) :
    unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] =
      chartSlopePrincipalSymbolContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s +
        arm2ChartReadoutResidual (I := I) g₀ T T' hδ hδ' x i k s := by
  rw [arm2_appCc_eq_combinedTrace_unitModel4 (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' s x i k]
  rw [arm2_combinedTrace_eq_chartSlopePrincipal_add_residual (I := I) g₀ T T'
        hTsymm hT'symm hδ_lt hδ hδ'_lt hδ' s x i k]

set_option linter.unusedSectionVars false in
private lemma partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m a b : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) m
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)
        (extChartAt I x x) =
      (1 / 2 : ℝ) * euclidPartial (E := E) m
          (chartPushedRaw I x
            (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b]))
          (toEuclidean (E := E) (extChartAt I x x)) +
        (1 / 2 : ℝ) * euclidPartial (E := E) m
          (chartPushedRaw I x
            (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a]))
          (toEuclidean (E := E) (extChartAt I x x)) := by
  classical
  set fab : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![a, b]
    with hfab_def
  set fba : M → ℝ := tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 (T - T') x ![] ![b, a]
    with hfba_def
  have hev := realizedGramDeriv_eventuallyEq_symm_scalarOnE_raw (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x a b
  have hdab : DifferentiableAt ℝ (scalarOnE (I := I) x fab) (extChartAt I x x) := by
    have hcd : ContDiffOn ℝ ∞ (scalarOnE (I := I) x fab) (extChartAt I x).target :=
      scalarOnE_contDiffOn_tensorChartComponentRaw (I := I) (M := M) g₀ (T - T') x ![a, b]
    have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
      extChartAt_target_subset_interior_of_boundaryless (I := I) x
        ((extChartAt I x).map_source (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x))
    exact ((hcd.mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hint)).differentiableAt (by simp)
  have hdba : DifferentiableAt ℝ (scalarOnE (I := I) x fba) (extChartAt I x x) := by
    have hcd : ContDiffOn ℝ ∞ (scalarOnE (I := I) x fba) (extChartAt I x).target :=
      scalarOnE_contDiffOn_tensorChartComponentRaw (I := I) (M := M) g₀ (T - T') x ![b, a]
    have hint : extChartAt I x x ∈ interior (extChartAt I x).target :=
      extChartAt_target_subset_interior_of_boundaryless (I := I) x
        ((extChartAt I x).map_source (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x))
    exact ((hcd.mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hint)).differentiableAt (by simp)
  have hpd_eq : partialDeriv (E := E) m
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x a b)
        (extChartAt I x x) =
      partialDeriv (E := E) m
        (fun y => (1 / 2 : ℝ) * (scalarOnE (I := I) x fab y + scalarOnE (I := I) x fba y))
        (extChartAt I x x) := by
    unfold partialDeriv
    rw [hev.fderiv_eq]
  rw [hpd_eq]
  rw [partialDeriv_const_mul (1 / 2 : ℝ)
      (fun y => scalarOnE (I := I) x fab y + scalarOnE (I := I) x fba y)
      (hdab.add hdba)]
  rw [partialDeriv_add (scalarOnE (I := I) x fab) (scalarOnE (I := I) x fba) hdab hdba]
  have hround : extChartAt I x ((extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) =
      extChartAt I x x := by
    rw [(toEuclidean (E := E)).symm_apply_apply]
    have htarget : extChartAt I x x ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source
        (by rw [extChartAt_source (I := I)]; exact mem_chart_source H x)
    rw [(extChartAt I x).right_inv htarget]
  have hYmem : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hPab : partialDeriv (E := E) m (scalarOnE (I := I) x fab) (extChartAt I x x) =
      euclidPartial (E := E) m (chartPushedRaw I x fab)
        (toEuclidean (E := E) (extChartAt I x x)) := by
    have h := partialDeriv_scalarOnE_eq_euclidPartial_local fab x m hYmem
    rw [hround] at h
    exact h
  have hPba : partialDeriv (E := E) m (scalarOnE (I := I) x fba) (extChartAt I x x) =
      euclidPartial (E := E) m (chartPushedRaw I x fba)
        (toEuclidean (E := E) (extChartAt I x x)) := by
    have h := partialDeriv_scalarOnE_eq_euclidPartial_local fba x m hYmem
    rw [hround] at h
    exact h
  rw [hPab, hPba]
  ring

private lemma sum_pi_fin_succ' {n : ℕ} {β : Type*} [AddCommMonoid β]
    {N : ℕ} (g : (Fin (N + 1) → Fin n) → β) :
    (∑ p : Fin (N + 1) → Fin n, g p)
      = ∑ a : Fin n, ∑ q : Fin N → Fin n, g (Fin.cons a q) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Fin n)).sum_comp g]
  rw [Fintype.sum_prod_type]
  rfl

set_option linter.unusedSectionVars false in
private lemma covDerivLowerOrderTerm02_center_eq
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (m p q : Fin (Module.finrank ℝ E)) :
    covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S x m ![] ![p, q]
        (toEuclidean (E := E) (extChartAt I x x)) =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m p r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![r, q] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m q r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![p, r] x) := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x hmemsrc
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hmemsrc
  rw [covDerivLowerOrderTerm_def]
  rw [hround]
  haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
    ⟨⟨![]⟩, fun f => by funext j; exact absurd j.2 (by simp)⟩
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (![] : Fin 0 → Fin (Module.finrank ℝ E))]
  · -- inner sum over J' : Fin 2 → _, with coeff(![], J')
    simp only [covDerivLowerOrderCoeff_def]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, if_true, mul_one, zero_sub]
    have hout : ∀ J' : Fin 2 → Fin (Module.finrank ℝ E),
        (∑ l : Fin 2, outputSlotCoeff (I := I) (M := M) g₀ 2 x m l ![p, q] J'
            (toEuclidean (E := E) (extChartAt I x x))) =
          chartChristoffel (I := I) g₀ x p m (J' 0) (extChartAt I x x) *
              (if q = J' 1 then (1 : ℝ) else 0) +
            chartChristoffel (I := I) g₀ x q m (J' 1) (extChartAt I x x) *
              (if p = J' 0 then (1 : ℝ) else 0) := by
      intro J'
      rw [Fin.sum_univ_two]
      rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 2 x m 0 ![p, q] J' hcenter,
        outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 2 x m 1 ![p, q] J' hcenter]
      rw [hround]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 0) p,
        chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 1) q]
      have herase0 : (Finset.univ.erase (0 : Fin 2)) = {(1 : Fin 2)} := by decide
      have herase1 : (Finset.univ.erase (1 : Fin 2)) = {(0 : Fin 2)} := by decide
      rw [herase0, herase1]
      simp only [Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_congr rfl (fun J' _ => by rw [hout J'] :
      ∀ J' ∈ Finset.univ,
        (-∑ x_2, outputSlotCoeff (I := I) (M := M) g₀ 2 x m x_2 ![p, q] J'
            (toEuclidean (E := E) (extChartAt I x x))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] J' x =
        (-(chartChristoffel (I := I) g₀ x p m (J' 0) (extChartAt I x x) *
              (if q = J' 1 then (1 : ℝ) else 0) +
            chartChristoffel (I := I) g₀ x q m (J' 1) (extChartAt I x x) *
              (if p = J' 0 then (1 : ℝ) else 0))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] J' x)]
    rw [← (finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm.sum_comp
      (fun J' : Fin 2 → Fin (Module.finrank ℝ E) =>
        (-(chartChristoffel (I := I) g₀ x p m (J' 0) (extChartAt I x x) *
              (if q = J' 1 then (1 : ℝ) else 0) +
            chartChristoffel (I := I) g₀ x q m (J' 1) (extChartAt I x x) *
              (if p = J' 0 then (1 : ℝ) else 0))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] J' x)]
    rw [Fintype.sum_prod_type]
    simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hsplit : ∀ a : Fin (Module.finrank ℝ E),
        (∑ b : Fin (Module.finrank ℝ E),
          -((chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
                  (if q = b then (1 : ℝ) else 0)) +
              chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                (if p = a then (1 : ℝ) else 0)) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) =
          (-(chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, q] x)) +
          (if p = a then (1 : ℝ) else 0) *
            (-∑ b : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) := by
      intro a
      rw [show (∑ b : Fin (Module.finrank ℝ E),
            -((chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
                    (if q = b then (1 : ℝ) else 0)) +
                chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                  (if p = a then (1 : ℝ) else 0)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) =
          (∑ b : Fin (Module.finrank ℝ E),
            -(chartChristoffel (I := I) g₀ x p m a (extChartAt I x x) *
                (if q = b then (1 : ℝ) else 0)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x) +
          (∑ b : Fin (Module.finrank ℝ E),
            (if p = a then (1 : ℝ) else 0) *
              -(chartChristoffel (I := I) g₀ x q m b (extChartAt I x x) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S x ![] ![a, b] x)) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_); ring]
      congr 1
      · rw [Finset.sum_eq_single q]
        · rw [if_pos rfl]; ring
        · intro b _ hbq; rw [if_neg (fun h => hbq h.symm)]; ring
        · intro h; exact absurd (Finset.mem_univ q) h
      · rw [← Finset.mul_sum, Finset.sum_neg_distrib]
    rw [Finset.sum_congr rfl (fun a _ => hsplit a)]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [chartChristoffel_symm (I := I) g₀ x p m a (extChartAt I x x)]
    · rw [Finset.sum_eq_single p]
      · rw [if_pos rfl, one_mul]
        congr 1
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [chartChristoffel_symm (I := I) g₀ x q m b (extChartAt I x x)]
      · intro a _ hap; rw [if_neg (fun h => hap h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ p) h
  · intro b _ hb
    exact absurd (Subsingleton.elim b ![]) hb
  · intro h; exact absurd (Finset.mem_univ _) h

set_option linter.unusedSectionVars false in
private lemma covDerivLowerOrderTerm03_center_hout
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m b c d : Fin (Module.finrank ℝ E))
    (J' : Fin 3 → Fin (Module.finrank ℝ E)) :
    (∑ l : Fin 3, outputSlotCoeff (I := I) (M := M) g₀ 3 x m l ![b, c, d] J'
        (toEuclidean (E := E) (extChartAt I x x))) =
      chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
          ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
      chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
          ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
      chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
          ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)) := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x hmemsrc
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hmemsrc
  rw [Fin.sum_univ_three]
  rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 3 x m 0 ![b, c, d] J' hcenter,
    outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 3 x m 1 ![b, c, d] J' hcenter,
    outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 3 x m 2 ![b, c, d] J' hcenter]
  rw [hround]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 0) b,
    chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 1) c,
    chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hbase m (J' 2) d]
  have herase0 : (Finset.univ.erase (0 : Fin 3)) = {(1 : Fin 3), (2 : Fin 3)} := by decide
  have herase1 : (Finset.univ.erase (1 : Fin 3)) = {(0 : Fin 3), (2 : Fin 3)} := by decide
  have herase2 : (Finset.univ.erase (2 : Fin 3)) = {(0 : Fin 3), (1 : Fin 3)} := by decide
  rw [herase0, herase1, herase2]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide)]
  simp only [Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [chartChristoffel_symm (I := I) g₀ x b m (J' 0) (extChartAt I x x),
    chartChristoffel_symm (I := I) g₀ x c m (J' 1) (extChartAt I x x),
    chartChristoffel_symm (I := I) g₀ x d m (J' 2) (extChartAt I x x)]

set_option linter.unusedSectionVars false in
private lemma sum_fin3_collapse_gen
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ) :
    (∑ J' : Fin 3 → Fin (Module.finrank ℝ E), F (J' 0) (J' 1) (J' 2)) =
      ∑ a0 : Fin (Module.finrank ℝ E), ∑ a1 : Fin (Module.finrank ℝ E),
        ∑ a2 : Fin (Module.finrank ℝ E), F a0 a1 a2 := by
  classical
  rw [sum_pi_fin_succ']
  refine Finset.sum_congr rfl (fun a0 _ => ?_)
  rw [sum_pi_fin_succ']
  refine Finset.sum_congr rfl (fun a1 _ => ?_)
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (Module.finrank ℝ E))) _ _ (fun q => ?_)
  simp only [Equiv.funUnique_apply, Fin.cons_zero,
    show ((1 : Fin 3) = (Fin.succ 0)) from rfl,
    show ((2 : Fin 3) = (Fin.succ 1)) from rfl,
    show ((1 : Fin 2) = (Fin.succ 0)) from rfl, Fin.cons_succ]
  rw [show (default : Fin 1) = (0 : Fin 1) from rfl]

set_option linter.unusedSectionVars false in
private lemma covDerivLowerOrderTerm03_center_eq
    (g₀ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 3) (x : M)
    (m b c d : Fin (Module.finrank ℝ E)) :
    covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3 W x m ![] ![b, c, d]
        (toEuclidean (E := E) (extChartAt I x x)) =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m b r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![r, c, d] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m c r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![b, r, d] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x m d r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![b, c, r] x) := by
  classical
  have hmemsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x hmemsrc
  rw [covDerivLowerOrderTerm_def]
  rw [hround]
  haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
    ⟨⟨![]⟩, fun f => by funext j; exact absurd j.2 (by simp)⟩
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (![] : Fin 0 → Fin (Module.finrank ℝ E))]
  · simp only [covDerivLowerOrderCoeff_def]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, if_true, mul_one, zero_sub]
    rw [Finset.sum_congr rfl (fun J' _ => by
        rw [covDerivLowerOrderTerm03_center_hout (I := I) (M := M) g₀ x m b c d J'] :
      ∀ J' ∈ Finset.univ,
        (-∑ x_2, outputSlotCoeff (I := I) (M := M) g₀ 3 x m x_2 ![b, c, d] J'
            (toEuclidean (E := E) (extChartAt I x x))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] J' x =
        (-(chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
              ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] J' x)]
    rw [Finset.sum_congr rfl (fun J' _ =>
      show (-(chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
              ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0)) +
            chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
              ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)))) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] J' x =
        (-(chartChristoffel (I := I) g₀ x m b (J' 0) (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![J' 0, J' 1, J' 2] x) *
            ((if c = J' 1 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0))) +
        (-(chartChristoffel (I := I) g₀ x m c (J' 1) (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![J' 0, J' 1, J' 2] x) *
            ((if b = J' 0 then (1 : ℝ) else 0) * (if d = J' 2 then (1 : ℝ) else 0))) +
        (-(chartChristoffel (I := I) g₀ x m d (J' 2) (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![J' 0, J' 1, J' 2] x) *
            ((if b = J' 0 then (1 : ℝ) else 0) * (if c = J' 1 then (1 : ℝ) else 0)))
        from by
          rw [show (![J' 0, J' 1, J' 2] : Fin 3 → Fin (Module.finrank ℝ E)) = J' from by
            funext j; fin_cases j <;> rfl]
          ring)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [sum_fin3_collapse_gen
        (fun a0 a1 a2 => -(chartChristoffel (I := I) g₀ x m b a0 (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![a0, a1, a2] x) *
          ((if c = a1 then (1 : ℝ) else 0) * (if d = a2 then (1 : ℝ) else 0))),
      sum_fin3_collapse_gen
        (fun a0 a1 a2 => -(chartChristoffel (I := I) g₀ x m c a1 (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![a0, a1, a2] x) *
          ((if b = a0 then (1 : ℝ) else 0) * (if d = a2 then (1 : ℝ) else 0))),
      sum_fin3_collapse_gen
        (fun a0 a1 a2 => -(chartChristoffel (I := I) g₀ x m d a2 (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3 W x ![] ![a0, a1, a2] x) *
          ((if b = a0 then (1 : ℝ) else 0) * (if c = a1 then (1 : ℝ) else 0)))]
    congr 1
    congr 1
    · -- slot b: collapse a1=c, a2=d
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun a0 _ => ?_)
      rw [Finset.sum_eq_single c]
      · rw [Finset.sum_eq_single d]
        · rw [if_pos rfl, if_pos rfl]; ring
        · intro a2 _ ha2; rw [if_neg (show ¬ d = a2 from fun h => ha2 h.symm), mul_zero]; ring
        · intro h; exact absurd (Finset.mem_univ d) h
      · intro a1 _ ha1
        refine Finset.sum_eq_zero (fun a2 _ => ?_)
        rw [if_neg (show ¬ c = a1 from fun h => ha1 h.symm), zero_mul]; ring
      · intro h; exact absurd (Finset.mem_univ c) h
    · -- slot c: collapse a0=b, a2=d
      rw [← Finset.sum_neg_distrib]
      rw [Finset.sum_eq_single b]
      · refine Finset.sum_congr rfl (fun a1 _ => ?_)
        rw [Finset.sum_eq_single d]
        · rw [if_pos rfl, if_pos rfl]; ring
        · intro a2 _ ha2; rw [if_neg (show ¬ d = a2 from fun h => ha2 h.symm), mul_zero]; ring
        · intro h; exact absurd (Finset.mem_univ d) h
      · intro a0 _ ha0
        refine Finset.sum_eq_zero (fun a1 _ => ?_)
        refine Finset.sum_eq_zero (fun a2 _ => ?_)
        rw [if_neg (show ¬ b = a0 from fun h => ha0 h.symm), zero_mul]; ring
      · intro h; exact absurd (Finset.mem_univ b) h
    · -- slot d: collapse a0=b, a1=c
      rw [← Finset.sum_neg_distrib]
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single c]
        · refine Finset.sum_congr rfl (fun a2 _ => ?_)
          rw [if_pos rfl, if_pos rfl]; ring
        · intro a1 _ ha1
          refine Finset.sum_eq_zero (fun a2 _ => ?_)
          rw [if_neg (show ¬ c = a1 from fun h => ha1 h.symm), mul_zero]; ring
        · intro h; exact absurd (Finset.mem_univ c) h
      · intro a0 _ ha0
        refine Finset.sum_eq_zero (fun a1 _ => ?_)
        refine Finset.sum_eq_zero (fun a2 _ => ?_)
        rw [if_neg (show ¬ b = a0 from fun h => ha0 h.symm), zero_mul]; ring
      · intro h; exact absurd (Finset.mem_univ b) h
  · intro b' _ hb'
    exact absurd (Subsingleton.elim b' ![]) hb'
  · intro h; exact absurd (Finset.mem_univ _) h

set_option linter.unusedSectionVars false in
private lemma lowerOrderCoeff02_eqOn_chartChristoffelEuclid
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin 2 → Fin (Module.finrank ℝ E)) :
    Set.EqOn
      (covDerivLowerOrderCoeff (I := I) (M := M) g₀ 0 2 x m ![] ![] Jdx Jdx')
      (fun y =>
        - (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y *
              (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
            + chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y *
              (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0)))
      (chartTargetEuclid (I := I) (M := M) x) := by
  classical
  intro y hy
  change covDerivLowerOrderCoeff (I := I) (M := M) g₀ 0 2 x m ![] ![] Jdx Jdx' y =
      - (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y *
            (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
          + chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y *
            (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0))
  rw [covDerivLowerOrderCoeff_def]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, if_true, mul_one, zero_sub]
  rw [Fin.sum_univ_two]
  rw [outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 2 x m 0 Jdx Jdx' hy,
    outputSlotCoeff_eq_entry_mul_const (I := I) (M := M) g₀ 2 x m 1 Jdx Jdx' hy]
  have hb_base : (extChartAt I x).symm ((toEuclidean (E := E)).symm y) ∈
      (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) x hy
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I x).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hphi_b : extChartAt I x
      ((extChartAt I x).symm ((toEuclidean (E := E)).symm y)) =
      (toEuclidean (E := E)).symm y :=
    (extChartAt I x).right_inv hy_pre
  rw [chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hb_base m (Jdx' 0) (Jdx 0),
    chartLeviCivitaParallelCLM_coordEntry_eq_chartChristoffel (I := I) g₀ x hb_base m (Jdx' 1) (Jdx 1)]
  rw [hphi_b]
  rw [show chartChristoffel (I := I) g₀ x (Jdx 0) m (Jdx' 0) ((toEuclidean (E := E)).symm y) =
      chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y from rfl,
    show chartChristoffel (I := I) g₀ x (Jdx 1) m (Jdx' 1) ((toEuclidean (E := E)).symm y) =
      chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y from rfl]
  have herase0 : (Finset.univ.erase (0 : Fin 2)) = {(1 : Fin 2)} := by decide
  have herase1 : (Finset.univ.erase (1 : Fin 2)) = {(0 : Fin 2)} := by decide
  rw [herase0, herase1]
  simp only [Finset.prod_singleton]

set_option linter.unusedSectionVars false in
private lemma gradCoeff02_center_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin 2 → Fin (Module.finrank ℝ E)) :
    secondCovDerivLO_gradCoeff (I := I) (M := M) g₀ 0 2 x m ![] ![] Jdx Jdx'
        (toEuclidean (E := E) (extChartAt I x x)) =
      - (chartChristoffel (I := I) g₀ x (Jdx 0) m (Jdx' 0) (extChartAt I x x) *
            (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
          + chartChristoffel (I := I) g₀ x (Jdx 1) m (Jdx' 1) (extChartAt I x x) *
            (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0)) := by
  classical
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x (mem_chart_source H x)
  have hsymm : ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) =
      extChartAt I x x := (toEuclidean (E := E)).symm_apply_apply _
  unfold secondCovDerivLO_gradCoeff
  rw [lowerOrderCoeff02_eqOn_chartChristoffelEuclid (I := I) (M := M) g₀ x m Jdx Jdx' hcenter]
  simp only [chartChristoffelEuclid_def, hsymm]

set_option linter.unusedSectionVars false in
private lemma valueCoeff02_center_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m a : Fin (Module.finrank ℝ E))
    (Jdx Jdx' : Fin 2 → Fin (Module.finrank ℝ E)) :
    secondCovDerivLO_valueCoeff (I := I) (M := M) g₀ 0 2 x m a ![] ![] Jdx Jdx'
        (toEuclidean (E := E) (extChartAt I x x)) =
      - (euclidPartial (E := E) a
              (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0))
              (toEuclidean (E := E) (extChartAt I x x)) *
            (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
          + euclidPartial (E := E) a
              (chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1))
              (toEuclidean (E := E) (extChartAt I x x)) *
            (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0)) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    chartTargetEuclid_isOpen (I := I) (M := M) x
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  unfold secondCovDerivLO_valueCoeff
  have heq : Set.EqOn
      (covDerivLowerOrderCoeff (I := I) (M := M) g₀ 0 2 x m ![] ![] Jdx Jdx')
      (fun y =>
        - (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y *
              (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
            + chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y *
              (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0)))
      (chartTargetEuclid (I := I) (M := M) x) :=
    lowerOrderCoeff02_eqOn_chartChristoffelEuclid (I := I) (M := M) g₀ x m Jdx Jdx'
  rw [euclidPartial_def,
    Filter.EventuallyEq.fderiv_eq (heq.eventuallyEq_of_mem (hopen.mem_nhds hcenter))]
  rw [← euclidPartial_def]
  have hd0 : DifferentiableAt ℝ
      (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    ((chartChristoffelEuclid_contDiffOn (I := I) g₀ x (Jdx 0) m (Jdx' 0)).differentiableOn
      (by norm_cast)).differentiableAt (hopen.mem_nhds hcenter)
  have hd1 : DifferentiableAt ℝ
      (chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1))
      (toEuclidean (E := E) (extChartAt I x x)) :=
    ((chartChristoffelEuclid_contDiffOn (I := I) g₀ x (Jdx 1) m (Jdx' 1)).differentiableOn
      (by norm_cast)).differentiableAt (hopen.mem_nhds hcenter)
  rw [show (fun y =>
        - (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y *
              (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)
            + chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y *
              (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0))) =
      (fun y =>
        (chartChristoffelEuclid (I := I) g₀ x (Jdx 0) m (Jdx' 0) y *
            (- (if Jdx 1 = Jdx' 1 then (1 : ℝ) else 0)))
          + (chartChristoffelEuclid (I := I) g₀ x (Jdx 1) m (Jdx' 1) y *
            (- (if Jdx 0 = Jdx' 0 then (1 : ℝ) else 0)))) from by
    funext y; ring]
  rw [euclidPartial_add_local a
    (hd0.mul_const _) (hd1.mul_const _)]
  rw [euclidPartial_def, euclidPartial_def, fderiv_mul_const hd0 _, fderiv_mul_const hd1 _,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
    ← euclidPartial_def, ← euclidPartial_def]
  ring

set_option linter.unusedSectionVars false in
private lemma arm1ReadoutCovDeriv_center_eq
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    arm1ReadoutCovDeriv (I := I) (M := M) g₀ h x ![a, b, c] =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, c] x)
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![b, r] x) := by
  classical
  rw [arm1ReadoutCovDeriv]
  rw [show (Matrix.vecTail (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E))) = ![b, c] from by
    funext j; fin_cases j <;> rfl]
  rw [show (![a, b, c] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = a from rfl]
  exact covDerivLowerOrderTerm02_center_eq (I := I) (M := M) g₀ h x a b c

set_option linter.unusedSectionVars false in
private lemma euclidPartial_covDerivLowerOrderTerm02_center_eq_sum
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) a
        (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d] y')
        (toEuclidean (E := E) (extChartAt I x x)) =
      ∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) × (Fin 2 → Fin (Module.finrank ℝ E)),
        (secondCovDerivLO_valueCoeff (I := I) (M := M) g₀ 0 2 x b a ![] p.1 ![c, d] p.2
              (toEuclidean (E := E) (extChartAt I x x)) *
            rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h p.1 p.2
              (toEuclidean (E := E) (extChartAt I x x)) +
          secondCovDerivLO_gradCoeff (I := I) (M := M) g₀ 0 2 x b ![] p.1 ![c, d] p.2
              (toEuclidean (E := E) (extChartAt I x x)) *
            euclidPartial (E := E) a
              (rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h p.1 p.2)
              (toEuclidean (E := E) (extChartAt I x x))) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    chartTargetEuclid_isOpen (I := I) (M := M) x
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have heq : Set.EqOn
      (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d] y')
      (fun y' => ∑ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
            (Fin 2 → Fin (Module.finrank ℝ E)),
          lowerOrderSummand (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] p y')
      (chartTargetEuclid (I := I) (M := M) x) := by
    intro y _
    exact covDerivLowerOrderTerm_eq_sum_lowerOrderSummand
      (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] y
  rw [euclidPartial_def,
    Filter.EventuallyEq.fderiv_eq (heq.eventuallyEq_of_mem (hopen.mem_nhds hcenter)),
    ← euclidPartial_def]
  have hsummand_diff : ∀ p : (Fin 0 → Fin (Module.finrank ℝ E)) ×
        (Fin 2 → Fin (Module.finrank ℝ E)),
      DifferentiableAt ℝ (lowerOrderSummand (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] p)
        (toEuclidean (E := E) (extChartAt I x x)) := by
    intro p
    exact ((lowerOrderSummand_contDiffOn (I := I) (M := M) g₀ 0 2 x h b ![] ![c, d] p).differentiableOn
      (by norm_cast)).differentiableAt (hopen.mem_nhds hcenter)
  rw [euclidPartial_finsetSum a Finset.univ (fun p _ => hsummand_diff p)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact euclidPartial_lowerOrderSummand_apply (I := I) (M := M) g₀ 0 2 x h b a ![] ![c, d] p hcenter

set_option linter.unusedSectionVars false in
private lemma sum_two_slot_indicator_collapse
    (Cc Cd : Fin (Module.finrank ℝ E) → ℝ)
    (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (c d : Fin (Module.finrank ℝ E)) :
    (∑ J' : Fin 2 → Fin (Module.finrank ℝ E),
        (Cc (J' 0) * (if d = J' 1 then (1 : ℝ) else 0) +
          Cd (J' 1) * (if c = J' 0 then (1 : ℝ) else 0)) *
          F (J' 0) (J' 1)) =
      (∑ a0 : Fin (Module.finrank ℝ E), Cc a0 * F a0 d) +
        (∑ a1 : Fin (Module.finrank ℝ E), Cd a1 * F c a1) := by
  classical
  rw [← (finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm.sum_comp
    (fun J' : Fin 2 → Fin (Module.finrank ℝ E) =>
      (Cc (J' 0) * (if d = J' 1 then (1 : ℝ) else 0) +
        Cd (J' 1) * (if c = J' 0 then (1 : ℝ) else 0)) *
        F (J' 0) (J' 1))]
  rw [Fintype.sum_prod_type]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hinner : ∀ a0 : Fin (Module.finrank ℝ E),
      (∑ a1 : Fin (Module.finrank ℝ E),
        (Cc a0 * (if d = a1 then (1 : ℝ) else 0) +
          Cd a1 * (if c = a0 then (1 : ℝ) else 0)) * F a0 a1) =
        Cc a0 * F a0 d +
          (if c = a0 then (1 : ℝ) else 0) * (∑ a1 : Fin (Module.finrank ℝ E), Cd a1 * F a0 a1) := by
    intro a0
    rw [show (∑ a1 : Fin (Module.finrank ℝ E),
          (Cc a0 * (if d = a1 then (1 : ℝ) else 0) +
            Cd a1 * (if c = a0 then (1 : ℝ) else 0)) * F a0 a1) =
        (∑ a1 : Fin (Module.finrank ℝ E),
          Cc a0 * (if d = a1 then (1 : ℝ) else 0) * F a0 a1) +
        (∑ a1 : Fin (Module.finrank ℝ E),
          (if c = a0 then (1 : ℝ) else 0) * (Cd a1 * F a0 a1)) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a1 _ => ?_); ring]
    congr 1
    · rw [Finset.sum_eq_single d]
      · rw [if_pos rfl]; ring
      · intro a1 _ ha1; rw [if_neg (fun h => ha1 h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ d) h
    · rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a0 _ => hinner a0)]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single c]
  · rw [if_pos rfl, one_mul]
  · intro a0 _ ha0; rw [if_neg (fun h => ha0 h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ c) h

set_option linter.unusedSectionVars false in
private lemma arm2ReadoutPairTerm1_center_eq
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    euclidPartial (E := E) a
        (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 h x b ![] ![c, d] y')
        (toEuclidean (E := E) (extChartAt I x x)) =
      ((- ∑ r : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) a
                (chartChristoffelEuclid (I := I) g₀ x c b r)
                (toEuclidean (E := E) (extChartAt I x x)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d] x)
        + (- ∑ r : Fin (Module.finrank ℝ E),
            euclidPartial (E := E) a
                (chartChristoffelEuclid (I := I) g₀ x d b r)
                (toEuclidean (E := E) (extChartAt I x x)) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r] x))
      + ((- ∑ r : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₀ x c b r (extChartAt I x x) *
              euclidPartial (E := E) a
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d]))
                (toEuclidean (E := E) (extChartAt I x x)))
        + (- ∑ r : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₀ x d b r (extChartAt I x x) *
              euclidPartial (E := E) a
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r]))
                (toEuclidean (E := E) (extChartAt I x x)))) := by
  classical
  set Y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (E := E) (extChartAt I x x) with hY
  have hcenter : Y ∈ chartTargetEuclid (I := I) (M := M) x := by
    rw [hY]; exact toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) x) :=
    chartTargetEuclid_isOpen (I := I) (M := M) x
  rw [euclidPartial_covDerivLowerOrderTerm02_center_eq_sum (I := I) (M := M) g₀ h x a b c d]
  haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
    ⟨⟨![]⟩, fun f => by funext j; exact absurd j.2 (by simp)⟩
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (![] : Fin 0 → Fin (Module.finrank ℝ E))]
  · have hraweq : ∀ J' : Fin 2 → Fin (Module.finrank ℝ E),
        rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h ![] J' Y =
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] J' x := by
      intro J'
      rw [hY, rawComponentEuclid_def,
        symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x (mem_chart_source H x)]
    have hdReq : ∀ J' : Fin 2 → Fin (Module.finrank ℝ E),
        euclidPartial (E := E) a (rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h ![] J') Y =
          euclidPartial (E := E) a
            (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] J')) Y := by
      intro J'
      have heqraw : Set.EqOn (rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h ![] J')
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] J'))
          (chartTargetEuclid (I := I) (M := M) x) :=
        rawComponentEuclid_eqOn_chartPushed (I := I) (M := M) g₀ 0 2 x h ![] J'
      rw [euclidPartial_def, euclidPartial_def,
        Filter.EventuallyEq.fderiv_eq (heqraw.eventuallyEq_of_mem (hopen.mem_nhds hcenter))]
    have hsummand : ∀ J' : Fin 2 → Fin (Module.finrank ℝ E),
        secondCovDerivLO_valueCoeff (I := I) (M := M) g₀ 0 2 x b a ![] ![] ![c, d] J' Y *
            rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h ![] J' Y +
          secondCovDerivLO_gradCoeff (I := I) (M := M) g₀ 0 2 x b ![] ![] ![c, d] J' Y *
            euclidPartial (E := E) a (rawComponentEuclid (I := I) (M := M) g₀ 0 2 x h ![] J') Y =
          (((fun r => - euclidPartial (E := E) a (chartChristoffelEuclid (I := I) g₀ x c b r) Y) (J' 0) *
                (if d = J' 1 then (1 : ℝ) else 0) +
              (fun r => - euclidPartial (E := E) a (chartChristoffelEuclid (I := I) g₀ x d b r) Y) (J' 1) *
                (if c = J' 0 then (1 : ℝ) else 0)) *
            (fun p q => tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![p, q] x) (J' 0) (J' 1)) +
          (((fun r => - chartChristoffel (I := I) g₀ x c b r (extChartAt I x x)) (J' 0) *
                (if d = J' 1 then (1 : ℝ) else 0) +
              (fun r => - chartChristoffel (I := I) g₀ x d b r (extChartAt I x x)) (J' 1) *
                (if c = J' 0 then (1 : ℝ) else 0)) *
            (fun p q => euclidPartial (E := E) a
              (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![p, q])) Y)
              (J' 0) (J' 1)) := by
      intro J'
      have hv := valueCoeff02_center_eq (I := I) (M := M) g₀ x b a ![c, d] J'
      have hg := gradCoeff02_center_eq (I := I) (M := M) g₀ x b ![c, d] J'
      have hJeq : (![J' 0, J' 1] : Fin 2 → Fin (Module.finrank ℝ E)) = J' := by
        funext j; fin_cases j <;> rfl
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← hY] at hv hg
      rw [hv, hg, hraweq J', hdReq J']
      simp only [hJeq]
      ring
    rw [Finset.sum_congr rfl (fun J' _ => hsummand J')]
    rw [Finset.sum_add_distrib]
    rw [sum_two_slot_indicator_collapse
        (fun r => - euclidPartial (E := E) a (chartChristoffelEuclid (I := I) g₀ x c b r) Y)
        (fun r => - euclidPartial (E := E) a (chartChristoffelEuclid (I := I) g₀ x d b r) Y)
        (fun p q => tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![p, q] x) c d,
      sum_two_slot_indicator_collapse
        (fun r => - chartChristoffel (I := I) g₀ x c b r (extChartAt I x x))
        (fun r => - chartChristoffel (I := I) g₀ x d b r (extChartAt I x x))
        (fun p q => euclidPartial (E := E) a
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![p, q])) Y) c d]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) (congrArg₂ (· + ·) ?_ ?_) <;>
      refine Finset.sum_congr rfl (fun r _ => ?_) <;> ring
  · intro b' _ hb'
    exact absurd (Subsingleton.elim b' ![]) hb'
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

set_option linter.unusedSectionVars false in
private lemma rawCompCovGrad03_center_eq
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (p q r : Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![p, q, r] x =
      euclidPartial (E := E) p
          (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![q, r]))
          (toEuclidean (E := E) (extChartAt I x x))
        + ((- ∑ t : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x p q t (extChartAt I x x) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, r] x)
          + (- ∑ t : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x p r t (extChartAt I x x) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![q, t] x)) := by
  classical
  have hcenter : (toEuclidean (E := E)) (extChartAt I x x) ∈
      chartTargetEuclid (I := I) (M := M) x :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) x (mem_chart_source H x)
  have hround : (extChartAt I x).symm
      ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x))) = x :=
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) x (mem_chart_source H x)
  rw [show tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![p, q, r] x =
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![p, q, r]
        ((extChartAt I x).symm
          ((toEuclidean (E := E)).symm ((toEuclidean (E := E)) (extChartAt I x x)))) from by
    rw [hround] ]
  rw [tensorChartComponentRaw_covGrad (I := I) (M := M) g₀ 0 2 h x ![] ![p, q, r] hcenter]
  rw [show (Matrix.vecTail (![p, q, r] : Fin (2 + 1) → Fin (Module.finrank ℝ E))) = ![q, r] from by
    funext j; fin_cases j <;> rfl]
  rw [show (![p, q, r] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = p from rfl]
  rw [covDerivLowerOrderTerm02_center_eq (I := I) (M := M) g₀ h x p q r]

set_option linter.unusedSectionVars false in
private lemma arm2ReadoutPairTerm2_center_eq
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 h) x a ![] ![b, c, d]
        (toEuclidean (E := E) (extChartAt I x x)) =
      (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
            (euclidPartial (E := E) r
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d]))
                (toEuclidean (E := E) (extChartAt I x x))
              + ((- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x r c t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
                + (- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x r d t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x))))
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
            (euclidPartial (E := E) b
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d]))
                (toEuclidean (E := E) (extChartAt I x x))
              + ((- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
                + (- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x b d t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, t] x))))
      + (- ∑ r : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) *
            (euclidPartial (E := E) b
                (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r]))
                (toEuclidean (E := E) (extChartAt I x x))
              + ((- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x b c t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, r] x)
                + (- ∑ t : Fin (Module.finrank ℝ E),
                    chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                      tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x)))) := by
  classical
  rw [covDerivLowerOrderTerm03_center_eq (I := I) (M := M) g₀
    (covGrad (I := I) (M := M) g₀ 0 2 h) x a b c d]
  rw [show (∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![r, c, d] x) =
      ∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
          (euclidPartial (E := E) r
              (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d]))
              (toEuclidean (E := E) (extChartAt I x x))
            + ((- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x r c t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
              + (- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x r d t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x))) from by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [rawCompCovGrad03_center_eq (I := I) (M := M) g₀ h x r c d] ]
  rw [show (∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![b, r, d] x) =
      ∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
          (euclidPartial (E := E) b
              (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d]))
              (toEuclidean (E := E) (extChartAt I x x))
            + ((- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
              + (- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x b d t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, t] x))) from by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [rawCompCovGrad03_center_eq (I := I) (M := M) g₀ h x b r d] ]
  rw [show (∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) *
          tensorChartComponentRaw (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2 h) x ![] ![b, c, r] x) =
      ∑ r : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) *
          (euclidPartial (E := E) b
              (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r]))
              (toEuclidean (E := E) (extChartAt I x x))
            + ((- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x b c t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, r] x)
              + (- ∑ t : Fin (Module.finrank ℝ E),
                  chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x))) from by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [rawCompCovGrad03_center_eq (I := I) (M := M) g₀ h x b c r] ]

set_option linter.unusedSectionVars false in
private lemma arm2ReadoutCovDerivPair_center_eq
    (g₀ : SmoothRiemannianMetric I M) (h : SmoothCcTensor g₀ 0 2) (x : M)
    (a b c d : Fin (Module.finrank ℝ E)) :
    arm2ReadoutCovDerivPair (I := I) (M := M) g₀ h x ![a, b, c, d] =
      (((- ∑ r : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) a
                  (chartChristoffelEuclid (I := I) g₀ x c b r)
                  (toEuclidean (E := E) (extChartAt I x x)) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d] x)
          + (- ∑ r : Fin (Module.finrank ℝ E),
              euclidPartial (E := E) a
                  (chartChristoffelEuclid (I := I) g₀ x d b r)
                  (toEuclidean (E := E) (extChartAt I x x)) *
                tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r] x))
        + ((- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x c b r (extChartAt I x x) *
                euclidPartial (E := E) a
                  (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d]))
                  (toEuclidean (E := E) (extChartAt I x x)))
          + (- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x d b r (extChartAt I x x) *
                euclidPartial (E := E) a
                  (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r]))
                  (toEuclidean (E := E) (extChartAt I x x)))))
      + ((- ∑ r : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g₀ x a b r (extChartAt I x x) *
              (euclidPartial (E := E) r
                  (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, d]))
                  (toEuclidean (E := E) (extChartAt I x x))
                + ((- ∑ t : Fin (Module.finrank ℝ E),
                      chartChristoffel (I := I) g₀ x r c t (extChartAt I x x) *
                        tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
                  + (- ∑ t : Fin (Module.finrank ℝ E),
                      chartChristoffel (I := I) g₀ x r d t (extChartAt I x x) *
                        tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x))))
        + ((- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x a c r (extChartAt I x x) *
                (euclidPartial (E := E) b
                    (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, d]))
                    (toEuclidean (E := E) (extChartAt I x x))
                  + ((- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, d] x)
                    + (- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b d t (extChartAt I x x) *
                          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![r, t] x))))
          + (- ∑ r : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g₀ x a d r (extChartAt I x x) *
                (euclidPartial (E := E) b
                    (chartPushedRaw I x (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, r]))
                    (toEuclidean (E := E) (extChartAt I x x))
                  + ((- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b c t (extChartAt I x x) *
                          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![t, r] x)
                    + (- ∑ t : Fin (Module.finrank ℝ E),
                        chartChristoffel (I := I) g₀ x b r t (extChartAt I x x) *
                          tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 h x ![] ![c, t] x)))))) := by
  classical
  rw [arm2ReadoutCovDerivPair]
  rw [show (Matrix.vecTail (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E))) = ![b, c, d] from by
    funext j; fin_cases j <;> rfl]
  rw [show (Matrix.vecTail (![b, c, d] : Fin (2 + 1) → Fin (Module.finrank ℝ E))) = ![c, d] from by
    funext j; fin_cases j <;> rfl]
  rw [show (![a, b, c, d] : Fin (2 + 2) → Fin (Module.finrank ℝ E)) 0 = a from rfl]
  rw [show (![b, c, d] : Fin (2 + 1) → Fin (Module.finrank ℝ E)) 0 = b from rfl]
  rw [arm2ReadoutPairTerm1_center_eq (I := I) (M := M) g₀ h x a b c d]
  rw [arm2ReadoutPairTerm2_center_eq (I := I) (M := M) g₀ h x a b c d]
  ring

set_option linter.unusedSectionVars false in
private lemma firstOrderRemainder_add_order0_eq_baseArms_add_arm2residual
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T p v w = ccTensorBilin (I := I) g₀ T p w v)
    (hT'symm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T' p v w = ccTensorBilin (I := I) g₀ T' p w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : M) (i k : Fin (Module.finrank ℝ E)) :
    chartSlopeFirstOrderRemainderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s +
        chartSlopeOrder0Contribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s =
      (unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] +
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 3 2
            (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i]) +
      arm2ChartReadoutResidual (I := I) g₀ T T' hδ hδ' x i k s := by
  classical
  rw [order0RHS_chart_eq (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' s x i k]
  rw [show linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s =
      ricciArmOrder1KoszulCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl]
  rw [ricciArmOrder1KoszulCoeff_appCc_chartBasis_koszulExpanded (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) x k i]
  simp only [unitModel3_basisChart_readout_split (I := I) (M := M) g₀ (T - T') x]
  rw [chartSlopeFirstOrderRemainderContribution, chartSlopeOrder0Contribution,
    arm2ChartReadoutResidual]
  simp only [partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x]
  have hyint : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  simp only [partialDeriv_chartInvGramOnE_eq (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x
    (extChartAt I x x) _ _ _ hyint]
  simp only [chartRicciTensor_def, chartRiemannTensor_def]
  simp only [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.partialDeriv_chartChristoffel_eq
    (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x _ _ _ _ hyint]
  have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩
  simp only [linearizedChristoffel_eq_principal_add_nonPrincipal (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x _ _ _ hyint hmem]
  simp only [partialDeriv_realizedChristoffelNonPrincipal (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x _ _ _ _ hyint s]
  simp only [realizedLinearizedChristoffelPrincipal, realizedChristoffelNonPrincipal,
    arm2ReadoutCovDerivPair_center_eq (I := I) (M := M) g₀ (T - T') x,
    arm1ReadoutCovDeriv_center_eq (I := I) (M := M) g₀ (T - T') x,
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.chartChristoffel_eq_sum_invGramOnE_bracket
      (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x,
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.chartChristoffel_eq_sum_invGramOnE_bracket
      (I := I) g₀ x]
  simp only [partialDeriv_realizedGramDeriv_eq_half_sum_euclidPartial (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x]
  sorry

theorem chartRicciSlope_eq_threeArmBase_component
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T p v w = ccTensorBilin (I := I) g₀ T p w v)
    (hT'symm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T' p v w = ccTensorBilin (I := I) g₀ T' p w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : M) (i k : Fin (Module.finrank ℝ E)) :
    chartRicciTraceChristoffelSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
        (extChartAt I x x) s =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] +
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 3 2
            (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] +
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] := by
  classical
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩
  have hslope := chartRicciTraceChristoffelSlope_eq_secondOrder_add_order0 (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x i k hy hmem
  have hFOR := chartSlopeSecondOrderContribution_eq_principal_add_remainder (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x i k hy s
  have harm2 := arm2_principalSymbol_chart_match (I := I) g₀ T T' hTsymm hT'symm
    hδ_lt hδ hδ'_lt hδ' s x i k
  have hcore := firstOrderRemainder_add_order0_eq_baseArms_add_arm2residual (I := I) g₀ T T'
    hTsymm hT'symm hδ_lt hδ hδ'_lt hδ' s hs x i k
  rw [harm2]
  linarith [hslope, hFOR, harm2, hcore]

theorem chartSlopeRemainderOrder0_eq_baseArms_add_residual
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T p v w = ccTensorBilin (I := I) g₀ T p w v)
    (hT'symm : ∀ (p : M) (v w : TangentSpace I p),
      ccTensorBilin (I := I) g₀ T' p v w = ccTensorBilin (I := I) g₀ T' p w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : M) (i k : Fin (Module.finrank ℝ E)) :
    chartSlopeFirstOrderRemainderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s +
        chartSlopeOrder0Contribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s =
      (unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] +
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 3 2
            (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i]) +
      arm2ChartReadoutResidual (I := I) g₀ T T' hδ hδ' x i k s := by
  classical
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩
  have hFOR := chartSlopeSecondOrderContribution_eq_principal_add_remainder (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x i k hy s
  have hslope := chartRicciTraceChristoffelSlope_eq_secondOrder_add_order0 (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x i k hy hmem
  have harm2 := arm2_principalSymbol_chart_match (I := I) g₀ T T' hTsymm hT'symm
    hδ_lt hδ hδ'_lt hδ' s x i k
  have hthree := chartRicciSlope_eq_threeArmBase_component (I := I) g₀ T T' hTsymm hT'symm
    hδ_lt hδ hδ'_lt hδ' s hs x i k
  linarith [hFOR, hslope, harm2, hthree]

theorem exists_corrFieldChristoffelConst (g₀ : SmoothRiemannianMetric I M) :
    ∃ CΓ : ℝ, 0 ≤ CΓ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        ∃ (C0 : ℝ → SmoothCcTensor g₀ 2 2) (C1 : ℝ → SmoothCcTensor g₀ 3 2),
          corrFieldDataSpec (I := I) (M := M) g₀ CΓ T T' hδ hδ' C0 C1 := by
  classical
  refine ⟨0, le_refl 0, ?_⟩
  intro T T' δ hδ δ' hδ'
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · have hfun : (fun s => linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s + (0 : SmoothCcTensor g₀ 2 2)) =
        linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' := by
      funext s; exact add_zero _
    rw [hfun]
    exact linearizedRicci_arm0BaseCoeff_jointSmooth (I := I) g₀ T T' hδ hδ'
  · have hfun : (fun s => linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s + (0 : SmoothCcTensor g₀ 3 2)) =
        linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' := by
      funext s; exact add_zero _
    rw [hfun]
    exact linearizedRicci_arm1BaseCoeff_jointSmooth (I := I) g₀ T T' hδ hδ'
  · intro s _hs x
    refine ⟨?_, ?_⟩
    · rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
        riemannianFiberNormSq_zero, Real.sqrt_zero, zero_mul, zero_mul]
    · rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
        riemannianFiberNormSq_zero, Real.sqrt_zero, zero_mul, zero_mul]
  · intro hTsymm hT'symm s hs x i k hδ_lt hδ'_lt
    have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
      abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩
    have hyint : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
      extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
    have hsplit2 := chartSlopeSecondOrderContribution_eq_principal_add_remainder (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x i k hyint s
    have hkeystone := arm2_principalSymbol_chart_match (I := I) g₀ T T' hTsymm hT'symm
      hδ_lt hδ hδ'_lt hδ' s x i k
    have hreconcile := chartSlopeRemainderOrder0_eq_baseArms_add_residual (I := I) g₀ T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ' s hs x i k
    have harm0 : (fun s => linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s +
        (0 : SmoothCcTensor g₀ 2 2)) s =
        linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s := add_zero _
    have harm1 : (fun s => linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s +
        (0 : SmoothCcTensor g₀ 3 2)) s =
        linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s := add_zero _
    simp only [harm0, harm1]
    rw [unitModel_add2_apply, unitModel_add2_apply]
    rw [hsplit2, hkeystone]
    rw [show chartSlopePrincipalSymbolContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s +
        chartSlopeFirstOrderRemainderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s +
        chartSlopeOrder0Contribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s =
        chartSlopePrincipalSymbolContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s +
        (chartSlopeFirstOrderRemainderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s +
        chartSlopeOrder0Contribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s) by ring]
    rw [hreconcile]
    ring

noncomputable def corrFieldChristoffelConst (g₀ : SmoothRiemannianMetric I M) : ℝ :=
  (exists_corrFieldChristoffelConst (I := I) (M := M) g₀).choose

theorem corrFieldChristoffelConst_nonneg (g₀ : SmoothRiemannianMetric I M) :
    0 ≤ corrFieldChristoffelConst (I := I) (M := M) g₀ :=
  (exists_corrFieldChristoffelConst (I := I) (M := M) g₀).choose_spec.1

theorem exists_arm0_arm1_corrField_data (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (C0 : ℝ → SmoothCcTensor g₀ 2 2) (C1 : ℝ → SmoothCcTensor g₀ 3 2),
      corrFieldDataSpec (I := I) (M := M) g₀
        (corrFieldChristoffelConst (I := I) (M := M) g₀) T T' hδ hδ' C0 C1 :=
  (exists_corrFieldChristoffelConst (I := I) (M := M) g₀).choose_spec.2 T T' hδ hδ'

noncomputable def linearizedRicciArm0CorrField (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ℝ → SmoothCcTensor g₀ 2 2 :=
  (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose

noncomputable def linearizedRicciArm1CorrField (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ℝ → SmoothCcTensor g₀ 3 2 :=
  (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose

def linearizedRicciArm0Field (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
    + linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s

def linearizedRicciArm1Field (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 3 2 :=
  linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s
    + linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s

theorem linearizedRicci_arm0Field_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') :=
  (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec.1

theorem linearizedRicci_arm1Field_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') :=
  (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec.2.1

theorem exists_corrField_identity_of_symm
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (x : M) (i k : Fin (Module.finrank ℝ E))
        (hδ_lt : δ < 1) (hδ'_lt : δ' < 1),
        chartSlopeSecondOrderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
              (extChartAt I x x) s +
            chartSlopeOrder0Contribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
              (extChartAt I x x) s =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2
                (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2
                (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2
                (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
              ![(chartModelBasis E) k, (chartModelBasis E) i] := by
  intro s hs x i k hδ_lt hδ'_lt
  obtain ⟨_hj0, _hj1, _hbound, hident⟩ :=
    exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ'
      |>.choose_spec.choose_spec
  have hkey := hident hTsymm hT'symm s hs x i k hδ_lt hδ'_lt
  rw [show linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s =
      linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
        + linearizedRicciArm0CorrField (I := I) g₀ T T' hδ hδ' s from rfl,
    show linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s =
      linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s
        + linearizedRicciArm1CorrField (I := I) g₀ T T' hδ hδ' s from rfl]
  exact hkey

theorem chartSlopeContributions_eq_threeArm_component
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : M) (i k : Fin (Module.finrank ℝ E)) :
    chartSlopeSecondOrderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s +
        chartSlopeOrder0Contribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + appCc (I := I) (M := M) g₀ 3 2
            (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
          + appCc (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] :=
  exists_corrField_identity_of_symm (I := I) g₀ T T' hTsymm hT'symm hδ hδ'
    s hs x i k hδ_lt hδ'_lt

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 3200000 in

theorem ricciArmBaseFields_lichnerowicz_uniform_rfns_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC : ℝ, 0 ≤ ΛC ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC := by
  classical
  obtain ⟨Λcurv, hΛcurv_nn, hcurv⟩ :=
    exists_riemannArm0_curvCoeff_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Λcom, hΛcom_nn, hcom⟩ :=
    exists_lichnerowicz_cometric_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  set K : ℝ := max Λcurv Λcom with hK_def
  have hK_nn : 0 ≤ K := le_trans hΛcurv_nn (le_max_left _ _)
  refine ⟨Real.sqrt (4 * K), Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hRm, hCurvFib⟩ := hcurv T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hPrin, hTH⟩ := hcom T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  have hRm' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ K :=
    le_trans hRm (le_max_left _ _)
  have hCurvFib' : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ K :=
    le_trans hCurvFib (le_max_left _ _)
  have hPrin' : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ K :=
    le_trans hPrin (le_max_right _ _)
  have hTH' : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((traceHessianCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ K :=
    le_trans hTH (le_max_right _ _)
  constructor
  · have hsec : (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x =
        ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
          - ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) := by
      rw [linearizedRicciArm0BaseCoeff, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
        Pi.sub_apply]
    rw [hsec]
    have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
      ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
    have hbound : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
          - ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)) ≤ 4 * K := by
      nlinarith [hsub, hRm', hCurvFib', hK_nn]
    refine Real.sqrt_le_sqrt hbound
  · have hsec : (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x =
        ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
          - (1 / 2 : ℝ) • ((traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) := by
      rw [linearizedRicciArm2FieldLichnerowicz, SmoothCcTensor.toSection_sub,
        ContMDiffSection.coe_sub, Pi.sub_apply, SmoothCcTensor.toSection_smul,
        ContMDiffSection.coe_smul, Pi.smul_apply]
    rw [hsec]
    have hsub := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 4 2 x
      ((ricciArmPrincipalCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
      ((1 / 2 : ℝ) • ((traceHessianCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x))
    have hsmul : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((1 / 2 : ℝ) • ((traceHessianCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)) =
        (1 / 2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) :=
      riemannianFiberNormSq_smul_value_appCc (I := I) (M := M) g₀ 4 2 x (1 / 2 : ℝ) _
    have hbound : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (((ricciArmPrincipalCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
          - (1 / 2 : ℝ) • ((traceHessianCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)) ≤ 4 * K := by
      rw [hsmul] at hsub
      nlinarith [hsub, hPrin', hTH', hK_nn]
    refine Real.sqrt_le_sqrt hbound

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
theorem exists_arm1Base_realizedFam_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λarm1 : ℝ, 0 ≤ Λarm1 ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x) ≤ Λarm1 := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_Csob_convexPerturbation_pointwise_C2_le
      (I := I) (M := M) g₀ a ha_super
  obtain ⟨Λarm1, hΛarm1_nn, hΛarm1⟩ :=
    exists_arm1Koszul_realizedFam_pointwise_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀
      (Csob * R) (by positivity)
  refine ⟨Λarm1, hΛarm1_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  rw [linearizedRicciArm1BaseCoeff]
  refine hΛarm1 T T' hδ_le hδ hδ'_le hδ' s hs x ?_
  exact hCsob T T' hR hTball hT'ball s hs x

set_option linter.unusedVariables false in
set_option maxHeartbeats 3200000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_arm0_arm1_corrField_rfns_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λcorr : ℝ, 0 ≤ Λcorr ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ Λcorr ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ Λcorr := by
  classical
  obtain ⟨ΛCbase, hΛCbase_nn, hbase⟩ :=
    ricciArmBaseFields_lichnerowicz_uniform_rfns_ballUniform
      (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Λarm1, hΛarm1_nn, harm1⟩ :=
    exists_arm1Base_realizedFam_rfns_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨Csub, hCsub_nn, hCsub⟩ :=
    exists_Csob_sub_pointwise_jet3_le (I := I) (M := M) g₀ a ha_super
  have hCΓ_nn : 0 ≤ corrFieldChristoffelConst (I := I) (M := M) g₀ :=
    corrFieldChristoffelConst_nonneg (I := I) (M := M) g₀
  refine ⟨(ΛCbase + Real.sqrt Λarm1) +
    corrFieldChristoffelConst (I := I) (M := M) g₀ * ΛCbase * (Csub * R), ?_, ?_⟩
  · have hpos : 0 ≤ corrFieldChristoffelConst (I := I) (M := M) g₀ * ΛCbase * (Csub * R) :=
      mul_nonneg (mul_nonneg hCΓ_nn hΛCbase_nn) (mul_nonneg hCsub_nn hR)
    have h2 : 0 ≤ Real.sqrt Λarm1 := Real.sqrt_nonneg _
    linarith
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hbase0, hbase2⟩ := hbase T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  have harm1' := harm1 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  have hdata := hCsub T T' hR hTball hT'ball x
  obtain ⟨_hj0, _hj1, hbound, _hident⟩ :=
    (exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose_spec
  obtain ⟨hb0, hb1⟩ := hbound s hs x
  have hdata_nn : 0 ≤ (∑ j ∈ Finset.range 3,
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 j (T - T')).toSection x‖)) := by
    refine Finset.sum_nonneg (fun j _ => ?_)
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
    exact norm_nonneg _
  have harm1sqrt_nn : 0 ≤ Real.sqrt Λarm1 := Real.sqrt_nonneg _
  have hprod : corrFieldChristoffelConst (I := I) (M := M) g₀ *
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) *
          (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j (T - T')).toSection x‖)) ≤
        corrFieldChristoffelConst (I := I) (M := M) g₀ * ΛCbase * (Csub * R) := by
    have hstep : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) *
            (∑ j ∈ Finset.range 3,
              (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
                Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
              ‖(iteratedCovGrad (I := I) g₀ 0 2 j (T - T')).toSection x‖)) ≤
          ΛCbase * (Csub * R) :=
      mul_le_mul hbase2 hdata hdata_nn hΛCbase_nn
    calc corrFieldChristoffelConst (I := I) (M := M) g₀ *
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) *
            (∑ j ∈ Finset.range 3,
              (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
                Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
              ‖(iteratedCovGrad (I := I) g₀ 0 2 j (T - T')).toSection x‖))
          = corrFieldChristoffelConst (I := I) (M := M) g₀ *
              (Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
              ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) *
              (∑ j ∈ Finset.range 3,
                (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
                  Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
                ‖(iteratedCovGrad (I := I) g₀ 0 2 j (T - T')).toSection x‖))) := by ring
        _ ≤ corrFieldChristoffelConst (I := I) (M := M) g₀ * (ΛCbase * (Csub * R)) :=
            mul_le_mul_of_nonneg_left hstep hCΓ_nn
        _ = corrFieldChristoffelConst (I := I) (M := M) g₀ * ΛCbase * (Csub * R) := by ring
  constructor
  · have htri : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) +
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            (((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose s).toSection x)) := by
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
      rw [← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x _,
        ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x _,
        ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x _]
      have hfield_eq : (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s).toSection x =
          (linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x +
            ((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose s).toSection x := by
        rw [linearizedRicciArm0Field, linearizedRicciArm0CorrField,
          SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      rw [hfield_eq]
      exact norm_add_le _ _
    refine le_trans htri ?_
    have hcorr0 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose s).toSection x)) ≤
        corrFieldChristoffelConst (I := I) (M := M) g₀ * ΛCbase * (Csub * R) :=
      le_trans hb0 hprod
    linarith [hbase0, hcorr0, harm1sqrt_nn]
  · have htri : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) +
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            (((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose s).toSection
              x)) := by
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 3 2 I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 3 2
      rw [← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x _,
        ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x _,
        ← norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x _]
      have hfield_eq : (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s).toSection x =
          (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x +
            ((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose
              s).toSection x := by
        rw [linearizedRicciArm1Field, linearizedRicciArm1CorrField,
          SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      rw [hfield_eq]
      exact norm_add_le _ _
    refine le_trans htri ?_
    have hbase1' : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
        Real.sqrt Λarm1 := Real.sqrt_le_sqrt harm1'
    have hcorr1 : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        (((exists_arm0_arm1_corrField_data (I := I) g₀ T T' hδ hδ').choose_spec.choose s).toSection
          x)) ≤
        corrFieldChristoffelConst (I := I) (M := M) g₀ * ΛCbase * (Csub * R) :=
      le_trans hb1 hprod
    linarith [hbase1', hcorr1, hΛCbase_nn]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 3200000 in

theorem ricciArmFields_concrete_lichnerowicz_uniform_rfns_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ ΛC : ℝ, 0 ≤ ΛC ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            ((linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤ ΛC := by
  classical
  obtain ⟨ΛCbase, hΛCbase_nn, hbase⟩ :=
    ricciArmBaseFields_lichnerowicz_uniform_rfns_ballUniform (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λcorr, hΛcorr_nn, hcorr⟩ :=
    exists_arm0_arm1_corrField_rfns_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨max ΛCbase Λcorr, le_trans hΛCbase_nn (le_max_left _ _), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨_hbase0, hbase2⟩ := hbase T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hcorr0, hcorr1⟩ := hcorr T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  exact ⟨le_trans hcorr0 (le_max_right _ _), le_trans hcorr1 (le_max_right _ _),
    le_trans hbase2 (le_max_left _ _)⟩


theorem chartRicciSlope_eq_threeArm_lichnerowicz_curvature_component
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : M) (i k : Fin (Module.finrank ℝ E)) :
    chartRicciTraceChristoffelSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
        (extChartAt I x x) s =
      ccTensorBilin (I := I) g₀
        (appCc (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + appCc (I := I) (M := M) g₀ 3 2
            (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
          + appCc (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
          ((chartModelBasis E) k) ((chartModelBasis E) i) := by
  classical
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs.1.le, hs.2.le⟩
  rw [chartRicciTraceChristoffelSlope_eq_secondOrder_add_order0 (I := I) g₀ T T'
    hδ_lt hδ hδ'_lt hδ' x i k hy hmem]
  rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
    (appCc (I := I) (M := M) g₀ 2 2
        (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      + appCc (I := I) (M := M) g₀ 3 2
        (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      + appCc (I := I) (M := M) g₀ 4 2
        (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
    ((chartModelBasis E) k) ((chartModelBasis E) i)]
  exact chartSlopeContributions_eq_threeArm_component (I := I) g₀ T T'
    hTsymm hT'symm hδ_lt hδ hδ'_lt hδ' s hs x i k

theorem exists_chartSlope_component_threeArm_ccTensorBilin
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ Φ₁ : ℝ → SmoothCcTensor g₀ 3 2,
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (i k : Fin (Module.finrank ℝ E)),
          chartRicciTraceChristoffelSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
              (extChartAt I x x) s =
            ccTensorBilin (I := I) g₀
              (appCc (I := I) (M := M) g₀ 2 2
                  (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2
                  (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
                ((chartModelBasis E) k) ((chartModelBasis E) i) := by
  classical
  refine ⟨linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ',
    linearizedRicci_arm1Field_jointSmooth (I := I) g₀ T T' hδ hδ', fun s hs x i k => ?_⟩
  exact chartRicciSlope_eq_threeArm_lichnerowicz_curvature_component
    (I := I) g₀ T T' hTsymm hT'symm hδ_lt hδ hδ'_lt hδ' s hs x i k

theorem chartRicciTraceChristoffelSlope_threeArm_covariant_transfer
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ Φ₁ : ℝ → SmoothCcTensor g₀ 3 2,
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (i k : Fin (Module.finrank ℝ E)),
          chartRicciTraceChristoffelSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
              (extChartAt I x x) s =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2
                  (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2
                  (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
                ![(chartModelBasis E) k, (chartModelBasis E) i] := by
  obtain ⟨Φ₁, hΦ₁joint, hcomp⟩ :=
    exists_chartSlope_component_threeArm_ccTensorBilin (I := I) g₀ T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  refine ⟨Φ₁, hΦ₁joint, fun s hs x i k => ?_⟩
  rw [hcomp s hs x i k,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ _ x
      ((chartModelBasis E) k) ((chartModelBasis E) i)]

theorem exists_chartRicciTraceDeriv_threeArm_covariant_component
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ Φ₁ : ℝ → SmoothCcTensor g₀ 3 2,
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (i k : Fin (Module.finrank ℝ E)),
          (∑ j : Fin (Module.finrank ℝ E),
              deriv (fun s' : ℝ =>
                chartRiemannTensor (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s') x i j k j (extChartAt I x x)) s) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2
                  (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2
                  (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
                ![(chartModelBasis E) k, (chartModelBasis E) i] := by
  obtain ⟨Φ₁, hΦ₁joint, hΦ₁transfer⟩ :=
    chartRicciTraceChristoffelSlope_threeArm_covariant_transfer
      (I := I) g₀ T T' hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  refine ⟨Φ₁, hΦ₁joint, fun s hs x i k => ?_⟩
  rw [deriv_chartRicciTrace_realizedFam_eq_chartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k hs]
  exact hΦ₁transfer s hs x i k

theorem chartRiemannTraceDeriv_threeArm_appCc_transfer_orderOne
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ Φ₁ : ℝ → SmoothCcTensor g₀ 3 2,
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
                (∑ j : Fin (Module.finrank ℝ E),
                  deriv (fun s' : ℝ =>
                    chartRiemannTensor (I := I)
                      (realizedFam (I := I) g₀ T T' hδ hδ' s') x i j k j (extChartAt I x x)) s)) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2
                  (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2
                  (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  obtain ⟨Φ₁, hΦ₁joint, hcomp⟩ :=
    exists_chartRicciTraceDeriv_threeArm_covariant_component (I := I) g₀ T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  refine ⟨Φ₁, hΦ₁joint, fun s hs x v => ?_⟩
  set Wsum : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 2 2
        (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
        (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
        (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      + appCc (I := I) (M := M) g₀ 4 2
        (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hWsum
  have hcomp' : ∀ i k : Fin (Module.finrank ℝ E),
      (∑ j : Fin (Module.finrank ℝ E),
          deriv (fun s' : ℝ =>
            chartRiemannTensor (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s') x i j k j (extChartAt I x x)) s) =
        unitModel (I := I) (M := M) g₀ 2 Wsum x
          ![(chartModelBasis E) k, (chartModelBasis E) i] := fun i k => hcomp s hs x i k
  calc
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
          (∑ j : Fin (Module.finrank ℝ E),
            deriv (fun s' : ℝ =>
              chartRiemannTensor (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' s') x i j k j (extChartAt I x x)) s))
        = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
              unitModel (I := I) (M := M) g₀ 2 Wsum x
                ![(chartModelBasis E) k, (chartModelBasis E) i] := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
          rw [hcomp' i k]
      _ = unitModel (I := I) (M := M) g₀ 2 Wsum x v := by
          rw [unitModel_basis_expand_two (I := I) (M := M) g₀ Wsum x v]

theorem chartRiemannTraceDeriv_threeArm_appCc_transfer (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
                (∑ j : Fin (Module.finrank ℝ E),
                  deriv (fun s' : ℝ =>
                    chartRiemannTensor (I := I)
                      (realizedFam (I := I) g₀ T T' hδ hδ' s') x i j k j (extChartAt I x x)) s)) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2
                  (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  obtain ⟨Φ₁, hΦ₁joint, hident⟩ :=
    chartRiemannTraceDeriv_threeArm_appCc_transfer_orderOne (I := I) g₀ T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  refine ⟨linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ', Φ₁,
    linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ',
    hΦ₁joint, ?_, ?_, hident⟩
  · intro x
    exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2
      (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ')
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm0Field_jointSmooth (I := I) g₀ T T' hδ hδ') x
  · intro x
    exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 3 2 Φ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hΦ₁joint x

theorem realizedRicci_threeArm_lowerOrder_residual (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          deriv (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x (v 0) (v 1)) s =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2
                  (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  obtain ⟨Φ₀, Φ₁, hΦ₀joint, hΦ₁joint, hΦ₀cont, hΦ₁cont, hident⟩ :=
    chartRiemannTraceDeriv_threeArm_appCc_transfer (I := I) g₀ T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  refine ⟨Φ₀, Φ₁, hΦ₀joint, hΦ₁joint, hΦ₀cont, hΦ₁cont, fun s hs x v => ?_⟩
  rw [(DifferentialGeometry.PDE.DeTurck.RicciLinearization.hasDerivAt_realizedRicciChartSum_general
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) hs).deriv]
  exact hident s hs x v

theorem exists_linearizedRicciOrder1DivCoeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
      (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  obtain ⟨Φ₀, Φ₁, hΦ₀joint, hΦ₁joint, hΦ₀cont, hΦ₁cont, hident⟩ :=
    realizedRicci_threeArm_lowerOrder_residual (I := I) g₀ T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  refine ⟨Φ₀, Φ₁,
    linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ',
    hΦ₀joint, hΦ₁joint,
    linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ',
    hΦ₀cont, hΦ₁cont, ?_, ?_⟩
  · intro x
    exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ')
      (realizedSmallSet (δ := δ) (δ' := δ'))
      (linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ') x
  · intro s hs x v
    rw [linearizedRicciAt_eq_deriv_chartSum_on_Ioo (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
      x (v 0) (v 1) hs]
    exact hident s hs x v

theorem linearizedRicci_lichnerowicz_arm1_identity (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
      (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v :=
  exists_linearizedRicciOrder1DivCoeff (I := I) g₀ T T' hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'

set_option linter.unusedVariables false in
theorem exists_linearizedRicci_threeArm_coeffFields
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Φ₀ : ℝ → SmoothCcTensor g₀ 2 2) (Φ₁ : ℝ → SmoothCcTensor g₀ 3 2)
      (Φ₂ : ℝ → SmoothCcTensor g₀ 4 2),
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 2 Φ₀ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 3 Φ₁ (δ := δ) (δ' := δ') ∧
      linearizedRicciThreeArmHcont (I := I) (M := M) g₀ 4 Φ₂ (δ := δ) (δ' := δ') ∧
      ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  exact linearizedRicci_lichnerowicz_arm1_identity (I := I) g₀ T T'
    hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'

set_option linter.unusedSectionVars false in

theorem exists_ricciArmOrder1Coeff
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1) -
            ricciTensor (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨Φ₀, Φ₁, Φ₂, hj0, hj1, hj2, hc0, hc1, hc2, hid⟩ :=
    exists_linearizedRicci_threeArm_coeffFields (I := I) (M := M) g₀ g_bg T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le (zero_le_one)]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  set R₀ : SmoothCcTensor g₀ 2 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 2 2 Φ₀
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 with hR₀
  set R₁ : SmoothCcTensor g₀ 3 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 3 2 Φ₁
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 with hR₁
  set R₂ : SmoothCcTensor g₀ 4 2 :=
    pathIntegralCoeffField (I := I) (M := M) g₀ 4 2 Φ₂
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 with hR₂
  refine ⟨R₀, R₁, R₂, fun x v => ?_⟩
  set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
  set W₁ : SmoothCcTensor g₀ 0 3 := iteratedCovGrad (I := I) g₀ 0 2 1 (T - T') with hW₁
  set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂
  have hRic :=
    ricciTensor_realized_sub_eq_integral_linearizedRicci (I := I) g₀ T T'
      hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1)
  rw [hRic]
  have hintegrand : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) 1 →
      linearizedRicciAt (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) s =
        unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s) W₀) x v
          + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s) W₁) x v
          + unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s) W₂) x v := by
    rw [MeasureTheory.ae_iff]
    have hnull : MeasureTheory.volume ({1} : Set ℝ) = 0 := by simp
    refine MeasureTheory.measure_mono_null (fun s hs => ?_) hnull
    rw [Set.mem_setOf_eq, Classical.not_imp] at hs
    obtain ⟨hsmem, hsneq⟩ := hs
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hsmem
    rw [Set.mem_singleton_iff]
    by_contra hne
    have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hne⟩
    exact hsneq (by rw [hid s hsIoo x v, unitModel_add2_apply, unitModel_add2_apply])

  rw [intervalIntegral.integral_congr_ae hintegrand]
  have hI0 : IntervalIntegrable
      (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 (Φ₀ s) W₀) x v)
      MeasureTheory.volume 0 1 :=
    threeArm_unitModel_appCc_intervalIntegrable (I := I) g₀ 2 Φ₀ W₀ hSI hc0 x v
  have hI1 : IntervalIntegrable
      (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 (Φ₁ s) W₁) x v)
      MeasureTheory.volume 0 1 :=
    threeArm_unitModel_appCc_intervalIntegrable (I := I) g₀ 3 Φ₁ W₁ hSI hc1 x v
  have hI2 : IntervalIntegrable
      (fun s : ℝ => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (Φ₂ s) W₂) x v)
      MeasureTheory.volume 0 1 :=
    threeArm_unitModel_appCc_intervalIntegrable (I := I) g₀ 4 Φ₂ W₂ hSI hc2 x v
  rw [intervalIntegral.integral_add (hI0.add hI1) hI2,
    intervalIntegral.integral_add hI0 hI1]
  have he0 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 2 2 Φ₀ W₀
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj0 hc0 x v
  have he1 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 3 2 Φ₁ W₁
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj1 hc1 x v
  have he2 := pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ 4 2 Φ₂ W₂
    (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hj2 hc2 x v
  rw [← hR₀] at he0
  rw [← hR₁] at he1
  rw [← hR₂] at he2
  rw [← he0, ← he1, ← he2, unitModel_add2_apply, unitModel_add2_apply]

set_option linter.unusedSectionVars false in

theorem ricciTensor_realize_sub_eq_threeArm_appCc
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        ((-2 : ℝ) * ricciTensor (I := I)
              (smoothRiemannianMetricToInfty (I := I)
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)) x (v 0) (v 1)
            - (-2 : ℝ) * ricciTensor (I := I)
                (smoothRiemannianMetricToInfty (I := I)
                  (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ')) x (v 0) (v 1)) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨R₀, R₁, R₂, hR⟩ :=
    exists_ricciArmOrder1Coeff (I := I) (M := M) g₀ g_bg T T'
      hTsymm hT'symm hδ_lt hδ hδ'_lt hδ'
  refine ⟨(-2 : ℝ) • R₀, (-2 : ℝ) • R₁, (-2 : ℝ) • R₂, fun x v => ?_⟩
  set A₀ : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 2 2 R₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 3 2 R₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ : SmoothCcTensor g₀ 0 2 :=
    appCc (I := I) (M := M) g₀ 4 2 R₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  rw [appCc_smul_left_local, appCc_smul_left_local, appCc_smul_left_local, ← hA₀, ← hA₁, ← hA₂]
  have hsmulsum : (-2 : ℝ) • A₀ + (-2 : ℝ) • A₁ + (-2 : ℝ) • A₂ =
      (-2 : ℝ) • (A₀ + A₁ + A₂) := by
    rw [smul_add, smul_add]
  rw [hsmulsum]
  rw [unitModel_smul_local, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have htoinfty : ∀ (g : SmoothRiemannianMetric I M),
      ricciTensor (I := I) (smoothRiemannianMetricToInfty (I := I) g) x (v 0) (v 1) =
        ricciTensor (I := I) g x (v 0) (v 1) := fun g => rfl
  rw [htoinfty, htoinfty, hA₀, hA₁, hA₂, ← hR x v]
  ring

set_option linter.unusedSectionVars false in
private lemma unitModel4_consMetricSlot0_eq_chartInvGram_sum
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4) (x : M)
    (k₁ : Fin (Module.finrank ℝ E)) (w : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 W x
        (Fin.cons (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((chartModelBasis E).cDualBasis k₁))) w) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ l *
          unitModel (I := I) (M := M) g₀ 4 W x
            (Fin.cons ((chartModelBasis E l : TangentSpace I x)) w) := by
  classical
  set D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ :=
    Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) with hD_def
  have hUM : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 W x v = D v := fun v => rfl
  rw [hUM]
  rw [show D (Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((chartModelBasis E).cDualBasis k₁))) w) =
        D.curryLeft (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((chartModelBasis E).cDualBasis k₁))) w from rfl]
  rw [cometricLmodel_covectorOfCLM_cDualBasis_eq_chartBasis_sum (I := I) g₁ x k₁]
  rw [map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [hUM]
  rfl

set_option linter.unusedSectionVars false in
private lemma euclidPartial_sub_local
    (l : Fin (Module.finrank ℝ E))
    {f h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hf : DifferentiableAt ℝ f y) (hh : DifferentiableAt ℝ h y) :
    euclidPartial (E := E) l (fun z => f z - h z) y =
      euclidPartial (E := E) l f y - euclidPartial (E := E) l h y := by
  rw [euclidPartial_def, euclidPartial_def, euclidPartial_def, fderiv_fun_sub hf hh,
    ContinuousLinearMap.sub_apply]

set_option linter.unusedSectionVars false in
private lemma unitModel4_consMetricSlot2_eq_chartInvGram_sum
    (g₀ g₁ : SmoothRiemannianMetric I M) (W : SmoothCcTensor g₀ 0 4) (x : M)
    (k₁ : Fin (Module.finrank ℝ E)) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 W x
        ![a, b, cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((chartModelBasis E).cDualBasis k₁)), c] =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x k₁ l *
          unitModel (I := I) (M := M) g₀ 4 W x
            ![a, b, (chartModelBasis E l : TangentSpace I x), c] := by
  classical
  set D : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ :=
    Tensor0SBundle.Tensor0SSpace.toModel
      ((show Tensor0SBundle.Tensor0SSpace 0 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) with hD_def
  have hUM : ∀ v : Fin 4 → TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 4 W x v = D v := fun v => rfl
  rw [hUM]
  rw [show D ![a, b, cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((chartModelBasis E).cDualBasis k₁)), c] =
        (D.toContinuousLinearMap ![a, b, (0 : TangentSpace I x), c] 2)
          (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((chartModelBasis E).cDualBasis k₁))) from ?_]
  · rw [cometricLmodel_covectorOfCLM_cDualBasis_eq_chartBasis_sum (I := I) g₁ x k₁]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_smul, smul_eq_mul]
    rw [hUM]
    congr 1
    rw [ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext j; fin_cases j <;> simp [Function.update]
  · rw [ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext j; fin_cases j <;> simp [Function.update]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
