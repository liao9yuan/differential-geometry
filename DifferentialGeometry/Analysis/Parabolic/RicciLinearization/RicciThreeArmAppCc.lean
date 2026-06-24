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

def linearizedRicciArm0Field (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
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

def linearizedRicciArm1Field (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
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

theorem linearizedRicci_arm0Field_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') := by
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
  rw [linearizedRicciArm0Field, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
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

theorem linearizedRicci_arm1Field_jointSmooth (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 3
      (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ') (δ := δ) (δ' := δ') := by
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
  rw [linearizedRicciArm1Field, ricciArmOrder1KoszulCoeff_toSection]

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
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) x) ≤ Λ :=
  sorry

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
  · have hsec : (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s).toSection x =
        ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x)
          - ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) := by
      rw [linearizedRicciArm0Field, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
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

theorem chartSlopeOrder0Contribution_eq_curvatureArm_component
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : M) (i k : Fin (Module.finrank ℝ E)) :
    chartSlopeOrder0Contribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (linearizedRicciArm0Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] :=
  sorry

theorem chartSlopeSecondOrderContribution_eq_principalKoszul_arm_component
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : M) (i k : Fin (Module.finrank ℝ E)) :
    chartSlopeSecondOrderContribution (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k
          (extChartAt I x x) s =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 3 2
            (linearizedRicciArm1Field (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] +
        unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2
            (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x
          ![(chartModelBasis E) k, (chartModelBasis E) i] :=
  sorry

theorem chartSlopeContributions_eq_threeArm_component
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
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
          ![(chartModelBasis E) k, (chartModelBasis E) i] := by
  classical
  rw [chartSlopeSecondOrderContribution_eq_principalKoszul_arm_component
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' s hs x i k,
    chartSlopeOrder0Contribution_eq_curvatureArm_component
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' s hs x i k,
    unitModel_add2_apply, unitModel_add2_apply]
  ring

theorem chartRicciSlope_eq_threeArm_lichnerowicz_curvature_component
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
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
    hδ_lt hδ hδ'_lt hδ' s hs x i k

theorem exists_chartSlope_component_threeArm_ccTensorBilin
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
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
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' s hs x i k

theorem chartRicciTraceChristoffelSlope_threeArm_covariant_transfer
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
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
      hδ_lt hδ hδ'_lt hδ'
  refine ⟨Φ₁, hΦ₁joint, fun s hs x i k => ?_⟩
  rw [hcomp s hs x i k,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ _ x
      ((chartModelBasis E) k) ((chartModelBasis E) i)]

theorem exists_chartRicciTraceDeriv_threeArm_covariant_component
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
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
      (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨Φ₁, hΦ₁joint, fun s hs x i k => ?_⟩
  rw [deriv_chartRicciTrace_realizedFam_eq_chartSlope (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k hs]
  exact hΦ₁transfer s hs x i k

theorem chartRiemannTraceDeriv_threeArm_appCc_transfer_orderOne
    (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
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
      hδ_lt hδ hδ'_lt hδ'
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
      hδ_lt hδ hδ'_lt hδ'
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
    chartRiemannTraceDeriv_threeArm_appCc_transfer (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨Φ₀, Φ₁, hΦ₀joint, hΦ₁joint, hΦ₀cont, hΦ₁cont, fun s hs x v => ?_⟩
  rw [(DifferentialGeometry.PDE.DeTurck.RicciLinearization.hasDerivAt_realizedRicciChartSum_general
    (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x (v 0) (v 1) hs).deriv]
  exact hident s hs x v

theorem exists_linearizedRicciOrder1DivCoeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
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
    realizedRicci_threeArm_lowerOrder_residual (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'
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
  exists_linearizedRicciOrder1DivCoeff (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'

set_option linter.unusedVariables false in
theorem exists_linearizedRicci_threeArm_coeffFields
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
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
  exact linearizedRicci_lichnerowicz_arm1_identity (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ'

set_option linter.unusedSectionVars false in

theorem exists_ricciArmOrder1Coeff
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
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
      hδ_lt hδ hδ'_lt hδ'
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
    exists_ricciArmOrder1Coeff (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
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

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
