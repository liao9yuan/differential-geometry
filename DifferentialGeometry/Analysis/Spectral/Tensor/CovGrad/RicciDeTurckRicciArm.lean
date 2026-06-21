import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSStrictParabolic
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartGramRealizeDiffJet
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.SecondCovGradChartHessian

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
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in

theorem ricciTensor_sub_eq_palatini_telescope
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₁' x v w =
      (∑ i : Fin (Module.finrank ℝ E),
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
                  (smoothExtensionTangent (I := I) x v x))) i)
        - (∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          ((covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w) x
              - covDerivConnDiff (I := I) g₀ g₁'
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                (smoothExtensionTangent (I := I) x w) x)
            + (connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x v)
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
                - connDiff (I := I) g₁' g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁')
                    (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x v x))) i) := by
  have h₁ := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁ x v w
  have h₁' := ricciTensor_sub_eq_connDiff_palatini (I := I) g₀ g₁' x v w
  rw [show ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₁' x v w =
      (ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w)
        - (ricciTensor (I := I) g₁' x v w - ricciTensor (I := I) g₀ x v w) from by ring]
  rw [h₁, h₁']

private lemma unitModel_add_left (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W₁ W₂ : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (W₁ + W₂) x =
      unitModel (I := I) (M := M) g s W₁ x + unitModel (I := I) (M := M) g s W₂ x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (W₁ + W₂).toSection x = W₁.toSection x + W₂.toSection x := by
    rw [SmoothCcTensor.toSection_add]; rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from (W₁ + W₂).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W₁.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W₂.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [hsec]; rfl]
  rw [Tensor0SSpace.toModel_add]

noncomputable def ricciArmOrder2Coeff (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  symmAbsorbedPrincipalCoeffPure (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')

def IsRealizedChartVelocity (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (s : ℝ) (h : ChartMetricPerturbation E) : Prop :=
  ∀ (i j : Fin (Module.finrank ℝ E)),
    ∀ᶠ y in nhds (extChartAt I α α),
      HasDerivAt
        (fun σ : ℝ => chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' σ) α i j y)
        (h i j y) s

private lemma chartChristoffel_congr_of_chartGramOnE_eventuallyEq
    {g g' : SmoothRiemannianMetric I M} {α : M} {y : E}
    (hG : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b =ᶠ[nhds y] chartGramOnE (I := I) g' α a b)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := I) g α i j k y = chartChristoffel (I := I) g' α i j k y := by
  classical
  
  have hGpt : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b y = chartGramOnE (I := I) g' α a b y :=
    fun a b => (hG a b).eq_of_nhds
  
  have hInv : ∀ a b : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k a =
        chartInvGramMatrix (I := I) g' α ((extChartAt I α).symm y) k a := by
    intro a _b
    have hmat : chartGramMatrix (I := I) g α ((extChartAt I α).symm y) =
        chartGramMatrix (I := I) g' α ((extChartAt I α).symm y) := by
      ext p q
      have := hGpt p q
      simpa only [chartGramOnE_def] using this
    simp only [chartInvGramMatrix, hmat]
  
  have hpart : ∀ (p a b : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) p (chartGramOnE (I := I) g α a b) y =
        partialDeriv (E := E) p (chartGramOnE (I := I) g' α a b) y := by
    intro p a b
    simp only [partialDeriv]
    rw [(hG a b).fderiv_eq]
  rw [chartChristoffel_def, chartChristoffel_def]
  refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hInv l k, hpart i l j, hpart j l i, hpart l i j]

private lemma partialDeriv_chartChristoffel_congr_of_chartGramOnE_eventuallyEq
    {g g' : SmoothRiemannianMetric I M} {α : M} {y : E}
    (hGnhd : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b =ᶠ[nhds y] chartGramOnE (I := I) g' α a b)
    (i j k p : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p (chartChristoffel (I := I) g α i j k) y =
      partialDeriv (E := E) p (chartChristoffel (I := I) g' α i j k) y := by
  classical
  
  have hchr : (fun z => chartChristoffel (I := I) g α i j k z) =ᶠ[nhds y]
      (fun z => chartChristoffel (I := I) g' α i j k z) := by
    
    have hself : ∀ a b : Fin (Module.finrank ℝ E),
        ∀ᶠ z in nhds y, chartGramOnE (I := I) g α a b =ᶠ[nhds z] chartGramOnE (I := I) g' α a b :=
      fun a b => (hGnhd a b).eventually_nhds
    have hall : ∀ᶠ z in nhds y, ∀ a b : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α a b =ᶠ[nhds z] chartGramOnE (I := I) g' α a b := by
      rw [eventually_all]
      intro a
      rw [eventually_all]
      intro b
      exact hself a b
    filter_upwards [hall] with z hz
    exact chartChristoffel_congr_of_chartGramOnE_eventuallyEq (g := g) (g' := g') (α := α) (y := z)
      hz i j k
  simp only [partialDeriv]
  rw [hchr.fderiv_eq]

private lemma chartRiemannTensor_congr_of_chartGramOnE_eventuallyEq
    {g g' : SmoothRiemannianMetric I M} {α : M} {y : E}
    (hGnhd : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b =ᶠ[nhds y] chartGramOnE (I := I) g' α a b)
    (i j k l : Fin (Module.finrank ℝ E)) :
    chartRiemannTensor (I := I) g α i j k l y = chartRiemannTensor (I := I) g' α i j k l y := by
  classical
  have hchr : ∀ a b c : Fin (Module.finrank ℝ E),
      chartChristoffel (I := I) g α a b c y = chartChristoffel (I := I) g' α a b c y :=
    fun a b c => chartChristoffel_congr_of_chartGramOnE_eventuallyEq (g := g) (g' := g') (α := α)
      (y := y) hGnhd a b c
  have hdchr : ∀ a b c p : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) p (chartChristoffel (I := I) g α a b c) y =
        partialDeriv (E := E) p (chartChristoffel (I := I) g' α a b c) y :=
    fun a b c p => partialDeriv_chartChristoffel_congr_of_chartGramOnE_eventuallyEq
      (g := g) (g' := g') (α := α) (y := y) hGnhd a b c p
  rw [chartRiemannTensor_def, chartRiemannTensor_def]
  rw [hdchr i k l j, hdchr i j l k]
  refine congrArg _ ?_
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [hchr j m l, hchr i k m, hchr k m l, hchr i j m]

private lemma chartRicciTensor_congr_of_chartGramOnE_eventuallyEq
    {g g' : SmoothRiemannianMetric I M} {α : M} {y : E}
    (hGnhd : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b =ᶠ[nhds y] chartGramOnE (I := I) g' α a b)
    (i k : Fin (Module.finrank ℝ E)) :
    chartRicciTensor (I := I) g α i k y = chartRicciTensor (I := I) g' α i k y := by
  classical
  rw [chartRicciTensor_def, chartRicciTensor_def]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact chartRiemannTensor_congr_of_chartGramOnE_eventuallyEq (g := g) (g' := g') (α := α) (y := y)
    hGnhd i j k j

private lemma chartDeTurckVFComp_congr_of_chartGramOnE_eventuallyEq
    {g g' g_bg : SmoothRiemannianMetric I M} {α : M} {y : E}
    (hGnhd : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b =ᶠ[nhds y] chartGramOnE (I := I) g' α a b)
    (k : Fin (Module.finrank ℝ E)) :
    chartDeTurckVFComp (I := I) g g_bg α k y = chartDeTurckVFComp (I := I) g' g_bg α k y := by
  classical
  rw [chartDeTurckVFComp_def, chartDeTurckVFComp_def]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hInvOnE : chartInvGramOnE (I := I) g α a b y = chartInvGramOnE (I := I) g' α a b y := by
    have hmat : chartGramMatrix (I := I) g α ((extChartAt I α).symm y) =
        chartGramMatrix (I := I) g' α ((extChartAt I α).symm y) := by
      ext p q
      have := (hGnhd p q).eq_of_nhds
      simpa only [chartGramOnE_def] using this
    simp only [chartInvGramOnE_def, chartInvGramMatrix, hmat]
  have hchr : chartChristoffel (I := I) g α a b k y = chartChristoffel (I := I) g' α a b k y :=
    chartChristoffel_congr_of_chartGramOnE_eventuallyEq (g := g) (g' := g') (α := α) (y := y) hGnhd
      a b k
  rw [hInvOnE, hchr]

private lemma partialDeriv_chartDeTurckVFComp_congr_of_chartGramOnE_eventuallyEq
    {g g' g_bg : SmoothRiemannianMetric I M} {α : M} {y : E}
    (hGnhd : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b =ᶠ[nhds y] chartGramOnE (I := I) g' α a b)
    (k p : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) p (chartDeTurckVFComp (I := I) g g_bg α k) y =
      partialDeriv (E := E) p (chartDeTurckVFComp (I := I) g' g_bg α k) y := by
  classical
  have hcomp : (fun z => chartDeTurckVFComp (I := I) g g_bg α k z) =ᶠ[nhds y]
      (fun z => chartDeTurckVFComp (I := I) g' g_bg α k z) := by
    have hself : ∀ a b : Fin (Module.finrank ℝ E),
        ∀ᶠ z in nhds y, chartGramOnE (I := I) g α a b =ᶠ[nhds z] chartGramOnE (I := I) g' α a b :=
      fun a b => (hGnhd a b).eventually_nhds
    have hall : ∀ᶠ z in nhds y, ∀ a b : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α a b =ᶠ[nhds z] chartGramOnE (I := I) g' α a b := by
      rw [eventually_all]; intro a; rw [eventually_all]; intro b; exact hself a b
    filter_upwards [hall] with z hz
    exact chartDeTurckVFComp_congr_of_chartGramOnE_eventuallyEq (g := g) (g' := g') (g_bg := g_bg)
      (α := α) (y := z) hz k
  simp only [partialDeriv]
  rw [hcomp.fderiv_eq]

private lemma chartLieDeTurckComp_congr_of_chartGramOnE_eventuallyEq
    {g g' g_bg : SmoothRiemannianMetric I M} {α : M} {y : E}
    (hGnhd : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b =ᶠ[nhds y] chartGramOnE (I := I) g' α a b)
    (i j : Fin (Module.finrank ℝ E)) :
    chartLieDeTurckComp (I := I) g g_bg α i j y = chartLieDeTurckComp (I := I) g' g_bg α i j y := by
  classical
  have hGpt : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b y = chartGramOnE (I := I) g' α a b y :=
    fun a b => (hGnhd a b).eq_of_nhds
  have hVF : ∀ c : Fin (Module.finrank ℝ E),
      chartDeTurckVFComp (I := I) g g_bg α c y = chartDeTurckVFComp (I := I) g' g_bg α c y :=
    fun c => chartDeTurckVFComp_congr_of_chartGramOnE_eventuallyEq (g := g) (g' := g') (g_bg := g_bg)
      (α := α) (y := y) hGnhd c
  have hdVF : ∀ (c p : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) p (chartDeTurckVFComp (I := I) g g_bg α c) y =
        partialDeriv (E := E) p (chartDeTurckVFComp (I := I) g' g_bg α c) y :=
    fun c p => partialDeriv_chartDeTurckVFComp_congr_of_chartGramOnE_eventuallyEq (g := g) (g' := g')
      (g_bg := g_bg) (α := α) (y := y) hGnhd c p
  have hdG : ∀ (p a b : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) p (chartGramOnE (I := I) g α a b) y =
        partialDeriv (E := E) p (chartGramOnE (I := I) g' α a b) y := by
    intro p a b
    simp only [partialDeriv]
    rw [(hGnhd a b).fderiv_eq]
  rw [chartLieDeTurckComp_def, chartLieDeTurckComp_def]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hVF c, hdG c i j]
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hGpt c j, hdVF c i]
  · refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hGpt i c, hdVF c j]

private lemma chartDeTurckRicciRHS_congr_of_chartGramOnE_eventuallyEq
    {g g' g_bg : SmoothRiemannianMetric I M} {α : M} {y : E}
    (hGnhd : ∀ a b : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g α a b =ᶠ[nhds y] chartGramOnE (I := I) g' α a b)
    (i k : Fin (Module.finrank ℝ E)) :
    chartDeTurckRicciRHS (I := I) g g_bg α i k y = chartDeTurckRicciRHS (I := I) g' g_bg α i k y := by
  rw [chartDeTurckRicciRHS_def, chartDeTurckRicciRHS_def,
    chartRicciTensor_congr_of_chartGramOnE_eventuallyEq (g := g) (g' := g') (α := α) (y := y)
      hGnhd i k,
    chartLieDeTurckComp_congr_of_chartGramOnE_eventuallyEq (g := g) (g' := g') (g_bg := g_bg)
      (α := α) (y := y) hGnhd i k]

theorem exists_rebased_cutoffMetricPerturbationFamily
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) :
    ∃ (h : ChartMetricPerturbation E) (gfam : ℝ → SmoothRiemannianMetric I M),
      IsMetricPerturbationFamily (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x h gfam ∧
        IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h ∧
        (∀ (i k : Fin (Module.finrank ℝ E)),
          (fun σ : ℝ => chartRicciTensor (I := I) (gfam σ) x i k (extChartAt I x x))
            =ᶠ[nhds (0 : ℝ)]
              (fun σ : ℝ => chartRicciTensor (I := I)
                (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x i k (extChartAt I x x))) ∧
        (∀ (i k : Fin (Module.finrank ℝ E)),
          (fun σ : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
              (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg) (gfam σ) x i k
              (extChartAt I x x))
            =ᶠ[nhds (0 : ℝ)]
              (fun σ : ℝ => DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
                (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
                (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x i k (extChartAt I x x))) := by
  classical
  
  set n := Module.finrank ℝ E
  set y₀ : E := extChartAt I x x with hy₀
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs.1
  have hs1 : s ≤ 1 := le_of_lt hs.2
  
  set Psec : ∀ b : M, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ :=
    fun b => ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) b with hPsec
  set Bsec : ∀ b : M, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ :=
    fun b => ccTensorBilinSymm (I := I) g₀ (T - T') b with hBsec
  
  have hPbound : gFibreOpBound (I := I) (M := M) g₀ Psec ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) g₀ T T' hδ hδ' hs0 hs1
  set cP : ℝ := (1 - s) * δ' + s * δ with hcP
  have hcP_lt : cP < 1 := convex_smallConstant_lt_one hδ_lt hδ'_lt hs0 hs1
  have hBsec_sub : ∀ (b : M) (v w : TangentSpace I b),
      Bsec b v w = ccTensorBilinSymm (I := I) g₀ T b v w -
        ccTensorBilinSymm (I := I) g₀ T' b v w := by
    intro b v w
    have h0 : T - T' = T + (-1 : ℝ) • T' := by rw [neg_one_smul, ← sub_eq_add_neg]
    change ccTensorBilinSymm (I := I) g₀ (T - T') b v w = _
    rw [h0, DifferentialGeometry.PDE.DeTurck.RicciLinearization.ccTensorBilinSymm_add,
      ccTensorBilinSymm_smul]; ring
  set cB : ℝ := |δ| + |δ'| with hcB
  have hcB_nonneg : (0 : ℝ) ≤ cB := by positivity
  have hBbound : gFibreOpBound (I := I) (M := M) g₀ Bsec cB := by
    intro b v w
    have hsv : (0 : ℝ) ≤ Real.sqrt (g₀.inner b v v) := Real.sqrt_nonneg _
    have hsw : (0 : ℝ) ≤ Real.sqrt (g₀.inner b w w) := Real.sqrt_nonneg _
    have hbT := hδ b v w
    have hbT' := hδ' b v w
    rw [hBsec_sub b v w]
    calc |ccTensorBilinSymm (I := I) g₀ T b v w - ccTensorBilinSymm (I := I) g₀ T' b v w|
          ≤ |ccTensorBilinSymm (I := I) g₀ T b v w| +
              |ccTensorBilinSymm (I := I) g₀ T' b v w| := abs_sub _ _
      _ ≤ |δ| * Real.sqrt (g₀.inner b v v) * Real.sqrt (g₀.inner b w w) +
            |δ'| * Real.sqrt (g₀.inner b v v) * Real.sqrt (g₀.inner b w w) := by
          gcongr
          · exact le_trans hbT (by gcongr; exact le_abs_self δ)
          · exact le_trans hbT' (by gcongr; exact le_abs_self δ')
      _ = cB * Real.sqrt (g₀.inner b v v) * Real.sqrt (g₀.inner b w w) := by rw [hcB]; ring
  
  set gs : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hgs
  have hsmem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt (Set.mem_Icc_of_Ioo hs)
  
  obtain ⟨bumpFn⟩ : Nonempty (SmoothBumpFunction I x) := inferInstance
  set χE : E → ℝ := (bumpFn.toContDiffBump : E → ℝ) with hχE
  have hχE_closedBall : Metric.closedBall y₀ bumpFn.rOut ⊆ (extChartAt I x).target := by
    have hsub := bumpFn.closedBall_subset
    rw [I.range_eq_univ] at hsub
    simpa [hy₀] using hsub
  have hχE_one_near : χE =ᶠ[nhds y₀] (fun _ => (1 : ℝ)) := bumpFn.toContDiffBump.eventuallyEq_one
  have hχE_le_one : ∀ z : E, |χE z| ≤ 1 := by
    intro z
    rw [abs_of_nonneg bumpFn.toContDiffBump.nonneg]
    exact bumpFn.toContDiffBump.le_one
  have hχE_smooth : ContDiff ℝ ∞ χE := bumpFn.toContDiffBump.contDiff
  
  set χM : M → ℝ := (bumpFn : M → ℝ) with hχM
  have hχM_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ χM := bumpFn.contMDiff
  have hχM_le_one : ∀ b : M, |χM b| ≤ 1 := by
    intro b
    rw [abs_of_nonneg bumpFn.nonneg]
    exact bumpFn.le_one
  
  have hχM_eq_χE : ∀ {y : E}, y ∈ (extChartAt I x).target →
      χM ((extChartAt I x).symm y) = χE y := by
    intro y hy
    have hsrc : (extChartAt I x).symm y ∈ (chartAt H x).source := by
      rw [← extChartAt_source (I := I)]; exact (extChartAt I x).map_target hy
    rw [hχM, bumpFn.eqOn_source hsrc]
    simp only [Function.comp_apply, hχE]
    rw [(extChartAt I x).right_inv hy]
  
  set Bframe : Fin n → Fin n → E → ℝ :=
    fun i j y => Bsec ((extChartAt I x).symm y)
      (chartBasisVecFiber (I := I) x i ((extChartAt I x).symm y))
      (chartBasisVecFiber (I := I) x j ((extChartAt I x).symm y)) with hBframe
  
  
  have hBframe_eq : ∀ (i j : Fin n) (y : E),
      Bframe i j y =
        chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x i j y -
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x i j y := by
    intro i j y
    simp only [hBframe]
    rw [hBsec_sub, chartGramOnE_def, chartGramMatrix_apply, tensorSectionRealizeMetric_inner,
      chartGramOnE_def, chartGramMatrix_apply, tensorSectionRealizeMetric_inner]
    ring
  have hBframe_contDiffOn : ∀ i j : Fin n, ContDiffOn ℝ ∞ (Bframe i j) (extChartAt I x).target := by
    intro i j
    have hcd : ContDiffOn ℝ ∞
        (fun y => chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x i j y -
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x i j y)
        (extChartAt I x).target :=
      (chartGramOnE_contDiffOn (I := I) _ x i j).sub (chartGramOnE_contDiffOn (I := I) _ x i j)
    exact hcd.congr (fun y _ => hBframe_eq i j y)
  set hcomp : Fin n → Fin n → E → ℝ := fun i j y => χE y * Bframe i j y with hhcomp
  
  have hcomp_smooth : ∀ i j : Fin n, ContDiff ℝ ∞ (hcomp i j) := by
    intro i j
    rw [contDiff_iff_contDiffAt]
    intro c
    by_cases hc : c ∈ Metric.closedBall y₀ bumpFn.rOut
    · have hc_t : c ∈ (extChartAt I x).target := hχE_closedBall hc
      have hb_at : ContDiffAt ℝ ∞ χE c := hχE_smooth.contDiffAt
      have hB_at : ContDiffAt ℝ ∞ (Bframe i j) c :=
        (hBframe_contDiffOn i j).contDiffAt ((isOpen_extChartAt_target (I := I) x).mem_nhds hc_t)
      exact hb_at.mul hB_at
    · rw [Metric.mem_closedBall] at hc
      have hdist : bumpFn.rOut < dist c y₀ := not_le.mp hc
      have hopen : IsOpen {z : E | bumpFn.rOut < dist z y₀} :=
        (continuous_dist.comp₂ continuous_id continuous_const).isOpen_preimage _ isOpen_Ioi
      refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : E => (0 : ℝ)) contDiffAt_const ?_
      refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hdist) ?_
      intro z hz
      have hz0 : χE z = 0 := bumpFn.toContDiffBump.zero_of_le_dist (le_of_lt hz)
      change χE z * Bframe i j z = 0
      rw [hz0, zero_mul]
  have hcomp_symm : ∀ (i j : Fin n) (y : E), hcomp i j y = hcomp j i y := by
    intro i j y
    simp only [hhcomp, hBframe]
    rw [ccTensorBilinSymm_symm]
  
  set h : ChartMetricPerturbation E :=
    { toFun := hcomp
      symm' := hcomp_symm
      smooth' := hcomp_smooth } with hh
  
  set Pfield : ℝ → ∀ b : M, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ :=
    fun σ b => Psec b + ((σ * χM b) • Bsec b) with hPfield
  have hPfield_symm : ∀ (σ : ℝ) (b : M) (v w : TangentSpace I b),
      Pfield σ b v w = Pfield σ b w v := by
    intro σ b v w
    simp only [hPfield, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hPsec, hBsec, ccTensorBilinSymm_symm (I := I) g₀ _ b v w,
      ccTensorBilinSymm_symm (I := I) g₀ _ b v w]
  have hPfield_smooth : ∀ σ : ℝ, ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        b (Pfield σ b)) := by
    intro σ
    have hP : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) b (Psec b)) :=
      ccTensorBilinSymm_contMDiff (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)
    have hBsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) b (Bsec b)) :=
      ccTensorBilinSymm_contMDiff (I := I) g₀ (T - T')
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => σ * χM b) := contMDiff_const.mul hχM_smooth
    have hdiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
          b ((fun b' => (σ * χM b') • Bsec b') b)) := ContMDiff.smul_section hscalar hBsmooth
    exact ContMDiff.add_section hP hdiff
  have hPfield_bound : ∀ σ : ℝ,
      gFibreOpBound (I := I) (M := M) g₀ (Pfield σ) (cP + |σ| * cB) := by
    intro σ
    have hscaled : gFibreOpBound (I := I) (M := M) g₀
        (fun b => (σ * χM b) • Bsec b) (|σ| * cB) := by
      intro b v w
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul]
      have hσ : (0 : ℝ) ≤ |σ| := abs_nonneg _
      have hχb : |χM b| ≤ 1 := hχM_le_one b
      have hBb : |Bsec b v w| ≤ cB * Real.sqrt (g₀.inner b v v) * Real.sqrt (g₀.inner b w w) :=
        hBbound b v w
      have hsv : (0 : ℝ) ≤ Real.sqrt (g₀.inner b v v) := Real.sqrt_nonneg _
      have hsw : (0 : ℝ) ≤ Real.sqrt (g₀.inner b w w) := Real.sqrt_nonneg _
      calc |σ| * |χM b| * |Bsec b v w|
            ≤ |σ| * 1 * (cB * Real.sqrt (g₀.inner b v v) * Real.sqrt (g₀.inner b w w)) := by
              gcongr
        _ = |σ| * cB * Real.sqrt (g₀.inner b v v) * Real.sqrt (g₀.inner b w w) := by ring
    intro b v w
    simp only [hPfield, ContinuousLinearMap.add_apply]
    have hsv : (0 : ℝ) ≤ Real.sqrt (g₀.inner b v v) := Real.sqrt_nonneg _
    have hsw : (0 : ℝ) ≤ Real.sqrt (g₀.inner b w w) := Real.sqrt_nonneg _
    have hb1 := hPbound b v w
    have hb2 := hscaled b v w
    calc |Psec b v w + ((σ * χM b) • Bsec b) v w|
          ≤ |Psec b v w| + |((σ * χM b) • Bsec b) v w| := abs_add_le _ _
      _ ≤ cP * Real.sqrt (g₀.inner b v v) * Real.sqrt (g₀.inner b w w) +
            |σ| * cB * Real.sqrt (g₀.inner b v v) * Real.sqrt (g₀.inner b w w) := by
          refine add_le_add ?_ ?_
          · simpa [hcP] using hb1
          · simpa using hb2
      _ = (cP + |σ| * cB) * Real.sqrt (g₀.inner b v v) * Real.sqrt (g₀.inner b w w) := by ring
  
  set ε : ℝ := (1 - cP) / (1 + cB) with hε
  have hε_pos : 0 < ε := by
    rw [hε]; apply div_pos (by linarith) (by linarith)
  have hwindow : ∀ σ : ℝ, |σ| < ε → cP + |σ| * cB < 1 := by
    intro σ hσ
    have hden : (0 : ℝ) < 1 + cB := by linarith
    have h1 : |σ| * cB ≤ ε * cB := mul_le_mul_of_nonneg_right (le_of_lt hσ) hcB_nonneg
    have h2 : ε * cB < 1 - cP := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [hcP_lt, hcB_nonneg]
    linarith
  
  set gfam : ℝ → SmoothRiemannianMetric I M := fun σ =>
    if hσ : |σ| < ε then
      perturbedMetric (I := I) (M := M) g₀ (Pfield σ) (hPfield_symm σ) (hPfield_smooth σ)
        (hwindow σ hσ) (hPfield_bound σ)
    else gs with hgfam
  
  have hgfam_chartGram : ∀ (σ : ℝ), |σ| < ε → ∀ (i j : Fin n) (y : E),
      chartGramOnE (I := I) (gfam σ) x i j y =
        chartGramOnE (I := I) g₀ x i j y +
          Pfield σ ((extChartAt I x).symm y)
            (chartBasisVecFiber (I := I) x i ((extChartAt I x).symm y))
            (chartBasisVecFiber (I := I) x j ((extChartAt I x).symm y)) := by
    intro σ hσ i j y
    simp only [hgfam, dif_pos hσ]
    rw [chartGramOnE_def, chartGramMatrix_apply, perturbedMetric_inner, perturbedInner_apply,
      chartGramOnE_def, chartGramMatrix_apply]
  
  
  have hmetric_ext : ∀ {g g' : SmoothRiemannianMetric I M},
      (∀ (b : M) (v w : TangentSpace I b), g.inner b v w = g'.inner b v w) → g = g' := by
    intro g g' hi
    have hinner : g.inner = g'.inner := by funext b; ext v w; exact hi b v w
    cases g with
    | mk gi gsymm gpos gvon gcont =>
      cases g' with
      | mk gi' gsymm' gpos' gvon' gcont' => cases hinner; rfl
  have hgfam_zero : gfam 0 = gs := by
    have h0 : |(0 : ℝ)| < ε := by rwa [abs_zero]
    simp only [hgfam, dif_pos h0]
    apply hmetric_ext
    intro b v w
    rw [perturbedMetric_inner, perturbedInner_apply, hgs,
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hsmem]
    simp only [hPfield, hPsec, zero_mul, add_zero, zero_smul]
  
  
  have haffine : ∀ (σ : ℝ), |σ| < ε → ∀ (i j : Fin n) {y : E},
      y ∈ (extChartAt I x).target →
      chartGramOnE (I := I) (gfam σ) x i j y =
        chartGramOnE (I := I) (gfam 0) x i j y + σ * hcomp i j y := by
    intro σ hσ i j y hy
    have h0 : |(0 : ℝ)| < ε := by rwa [abs_zero]
    rw [hgfam_chartGram σ hσ i j y, hgfam_chartGram 0 h0 i j y]
    simp only [hPfield, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      zero_mul, zero_smul, add_zero]
    rw [hhcomp, hBframe]
    have hχ := hχM_eq_χE hy
    rw [hχ]
    ring
  
  have hA_diff : ∀ (i j : Fin n) {y : E}, y ∈ interior (extChartAt I x).target →
      DifferentiableAt ℝ (fun z => chartGramOnE (I := I) (gfam 0) x i j z) y := by
    intro i j y hy
    rw [hgfam_zero]
    have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) gs x i j) (extChartAt I x).target :=
      chartGramOnE_contDiffOn (I := I) gs x i j
    exact ((hcd.mono interior_subset).contDiffAt
      (isOpen_interior.mem_nhds hy)).differentiableAt (by norm_num)
  have hB_diff : ∀ (i j : Fin n) (y : E),
      DifferentiableAt ℝ (fun z => hcomp i j z) y :=
    fun i j y => ((hcomp_smooth i j).differentiable (by norm_num)).differentiableAt
  
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  set Wσ : Set ℝ := {σ : ℝ | |σ| < ε} ∩ {σ : ℝ | s + σ ∈ realizedSmallSet (δ := δ) (δ' := δ')}
    with hWσ
  have hWσ_open : IsOpen Wσ := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt continuous_abs continuous_const
    · exact hSopen.preimage (by fun_prop)
  have hWσ_mem : (0 : ℝ) ∈ Wσ := by
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_setOf_eq, abs_zero]; exact hε_pos
    · simp only [Set.mem_setOf_eq, add_zero]; exact hsmem
  have hWσ_nhds : Wσ ∈ nhds (0 : ℝ) := hWσ_open.mem_nhds hWσ_mem
  
  have hloc_gram : ∀ σ : ℝ, σ ∈ Wσ → ∀ a b : Fin n,
      chartGramOnE (I := I) (gfam σ) x a b =ᶠ[nhds y₀]
        chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x a b := by
    intro σ hσW a b
    obtain ⟨hσε, hσs⟩ := hσW
    simp only [Set.mem_setOf_eq] at hσε hσs
    
    have hbase_t : y₀ ∈ (extChartAt I x).target := by
      rw [hy₀]; exact mem_extChartAt_target x
    filter_upwards [hχE_one_near,
      (isOpen_extChartAt_target (I := I) x).mem_nhds hbase_t] with y hy1 hyt
    have hsσ_mem : s + σ ∈ realizedSmallSet (δ := δ) (δ' := δ') := hσs
    set yp : M := (extChartAt I x).symm y with hyp
    set fa : TangentSpace I yp := chartBasisVecFiber (I := I) x a yp with hfa
    set fb : TangentSpace I yp := chartBasisVecFiber (I := I) x b yp with hfb
    have hχ1 : χM yp = 1 := by rw [hyp, hχM_eq_χE hyt]; exact hy1
    
    have hRHS : chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x a b y =
        chartGramOnE (I := I) g₀ x a b y +
          (Psec yp fa fb + σ * Bsec yp fa fb) := by
      rw [chartGramOnE_def, chartGramMatrix_apply,
        realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hsσ_mem, chartGramOnE_def,
        chartGramMatrix_apply]
      congr 1
      have hcsplit : convexPerturbation (I := I) g₀ T T' (s + σ) =
          convexPerturbation (I := I) g₀ T T' s + σ • (T - T') := by
        simp only [convexPerturbation]
        module
      rw [hcsplit, DifferentialGeometry.PDE.DeTurck.RicciLinearization.ccTensorBilinSymm_add,
        ccTensorBilinSymm_smul]
    
    rw [hgfam_chartGram σ hσε a b y, hRHS]
    simp only [hPfield, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ← hyp, hχ1, mul_one]
    ring
  refine ⟨h, gfam, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hgfam_zero]
    · intro i j y hy
      have hyt : y ∈ (extChartAt I x).target := interior_subset hy
      have heq : (fun σ : ℝ => chartGramOnE (I := I) (gfam σ) x i j y) =ᶠ[nhds 0]
          (fun σ : ℝ => chartGramOnE (I := I) (gfam 0) x i j y + σ * h i j y) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε_pos] with σ hσ
        exact haffine σ (by simpa [Real.dist_eq] using hσ) i j hyt
      apply HasDerivAt.congr_of_eventuallyEq _ heq
      have h1 : HasDerivAt
          (fun σ : ℝ => chartGramOnE (I := I) (gfam 0) x i j y + σ * h i j y)
          (0 + 1 * h i j y) 0 := (hasDerivAt_const _ _).add ((hasDerivAt_id _).mul_const _)
      simpa using h1
    · intro i j y hy
      have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) gs x i j) (extChartAt I x).target :=
        chartGramOnE_contDiffOn (I := I) gs x i j
      have hyt : y ∈ (extChartAt I x).target := interior_subset hy
      
      have heq : (fun p : ℝ × E => chartGramOnE (I := I) (gfam p.1) x i j p.2)
          =ᶠ[nhds (0, y)]
          (fun p : ℝ × E => chartGramOnE (I := I) gs x i j p.2 + p.1 * hcomp i j p.2) := by
        have hmem : Wσ ×ˢ (extChartAt I x).target ∈ nhds ((0 : ℝ), y) :=
          (hWσ_open.prod (isOpen_extChartAt_target (I := I) x)).mem_nhds ⟨hWσ_mem, hyt⟩
        filter_upwards [hmem] with p hp
        have hp1 : |p.1| < ε := hp.1.1
        rw [haffine p.1 hp1 i j hp.2, hgfam_zero]
      apply ContDiffAt.congr_of_eventuallyEq _ heq
      have hAc : ContDiffAt ℝ ∞ (fun p : ℝ × E => chartGramOnE (I := I) gs x i j p.2) (0, y) :=
        ((hcd.contDiffAt ((isOpen_extChartAt_target (I := I) x).mem_nhds hyt)).comp (0, y)
          contDiffAt_snd)
      have hBc : ContDiffAt ℝ ∞ (fun p : ℝ × E => hcomp i j p.2) (0, y) :=
        ((hcomp_smooth i j).contDiffAt).comp (0, y) contDiffAt_snd
      exact hAc.add (contDiffAt_fst.mul hBc)
    · intro i j p y hy
      have hyt : y ∈ (extChartAt I x).target := interior_subset hy
      have hpart : ∀ σ : ℝ, |σ| < ε →
          partialDeriv (E := E) p (chartGramOnE (I := I) (gfam σ) x i j) y =
            partialDeriv (E := E) p (chartGramOnE (I := I) (gfam 0) x i j) y +
              σ * partialDeriv (E := E) p (h i j) y := by
        intro σ hσ
        have hgerm : chartGramOnE (I := I) (gfam σ) x i j =ᶠ[nhds y]
            (fun z => chartGramOnE (I := I) (gfam 0) x i j z + σ * h i j z) := by
          filter_upwards [(isOpen_extChartAt_target (I := I) x).mem_nhds hyt] with z hz
          exact haffine σ hσ i j hz
        simp only [partialDeriv]
        rw [hgerm.fderiv_eq]
        have hBσ : HasFDerivAt (fun z => σ * h i j z)
            (σ • fderiv ℝ (fun z => h i j z) y) y := (hB_diff i j y).hasFDerivAt.const_mul σ
        have hsum : HasFDerivAt (fun z => chartGramOnE (I := I) (gfam 0) x i j z + σ * h i j z)
            (fderiv ℝ (fun z => chartGramOnE (I := I) (gfam 0) x i j z) y +
              σ • fderiv ℝ (fun z => h i j z) y) y := (hA_diff i j hy).hasFDerivAt.add hBσ
        rw [hsum.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have heq : (fun σ : ℝ => partialDeriv (E := E) p (chartGramOnE (I := I) (gfam σ) x i j) y)
          =ᶠ[nhds 0]
          (fun σ : ℝ => partialDeriv (E := E) p (chartGramOnE (I := I) (gfam 0) x i j) y +
            σ * partialDeriv (E := E) p (h i j) y) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε_pos] with σ hσ
        exact hpart σ (by simpa [Real.dist_eq] using hσ)
      apply HasDerivAt.congr_of_eventuallyEq _ heq
      have h1 : HasDerivAt
          (fun σ : ℝ => partialDeriv (E := E) p (chartGramOnE (I := I) (gfam 0) x i j) y +
            σ * partialDeriv (E := E) p (h i j) y)
          (0 + 1 * partialDeriv (E := E) p (h i j) y) 0 :=
        (hasDerivAt_const _ _).add ((hasDerivAt_id _).mul_const _)
      simpa using h1
    · intro i j p q y hy
      have hyt : y ∈ (extChartAt I x).target := interior_subset hy
      
      have hinner : ∀ σ : ℝ, |σ| < ε →
          (fun z => partialDeriv (E := E) q (chartGramOnE (I := I) (gfam σ) x i j) z) =ᶠ[nhds y]
            (fun z => partialDeriv (E := E) q (chartGramOnE (I := I) (gfam 0) x i j) z +
              σ * partialDeriv (E := E) q (h i j) z) := by
        intro σ hσ
        filter_upwards [(isOpen_extChartAt_target (I := I) x).mem_nhds hyt] with z hz
        have hgerm : chartGramOnE (I := I) (gfam σ) x i j =ᶠ[nhds z]
            (fun z' => chartGramOnE (I := I) (gfam 0) x i j z' + σ * h i j z') := by
          filter_upwards [(isOpen_extChartAt_target (I := I) x).mem_nhds hz] with z' hz'
          exact haffine σ hσ i j hz'
        have hzint : z ∈ interior (extChartAt I x).target :=
          extChartAt_target_subset_interior_of_boundaryless (I := I) x hz
        simp only [partialDeriv]
        rw [hgerm.fderiv_eq]
        have hBσ : HasFDerivAt (fun z' => σ * h i j z')
            (σ • fderiv ℝ (fun z' => h i j z') z) z := (hB_diff i j z).hasFDerivAt.const_mul σ
        have hsum : HasFDerivAt (fun z' => chartGramOnE (I := I) (gfam 0) x i j z' + σ * h i j z')
            (fderiv ℝ (fun z' => chartGramOnE (I := I) (gfam 0) x i j z') z +
              σ • fderiv ℝ (fun z' => h i j z') z) z := (hA_diff i j hzint).hasFDerivAt.add hBσ
        rw [hsum.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      
      have hAq_diff : DifferentiableAt ℝ
          (fun z => partialDeriv (E := E) q (chartGramOnE (I := I) (gfam 0) x i j) z) y := by
        rw [hgfam_zero]
        have hcd : ContDiffOn ℝ ∞ (chartGramOnE (I := I) gs x i j) (extChartAt I x).target :=
          chartGramOnE_contDiffOn (I := I) gs x i j
        have hopen : IsOpen ((extChartAt I x).target : Set E) := isOpen_extChartAt_target (I := I) x
        have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartGramOnE (I := I) gs x i j))
            (extChartAt I x).target :=
          hcd.fderiv_of_isOpen hopen (by rw [ENat.coe_top_add_one])
        have hcd2 : ContDiffOn ℝ ∞
            (fun z => partialDeriv (E := E) q (chartGramOnE (I := I) gs x i j) z)
            (extChartAt I x).target := by
          simp only [partialDeriv]
          exact hfderiv.clm_apply contDiffOn_const
        exact (hcd2.contDiffAt (hopen.mem_nhds (interior_subset hy))).differentiableAt (by norm_num)
      have hBq_diff : DifferentiableAt ℝ
          (fun z => partialDeriv (E := E) q (h i j) z) y :=
        ((DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_contDiff_of_contDiff
          (hcomp_smooth i j) q).differentiable (by norm_num)).differentiableAt
      have hpt : ∀ σ : ℝ, |σ| < ε →
          partialDeriv (E := E) p (partialDeriv (E := E) q (chartGramOnE (I := I) (gfam σ) x i j)) y =
            partialDeriv (E := E) p
              (fun z => partialDeriv (E := E) q (chartGramOnE (I := I) (gfam 0) x i j) z) y +
            σ * partialDeriv (E := E) p
              (fun z => partialDeriv (E := E) q (h i j) z) y := by
        intro σ hσ
        have hgerm := hinner σ hσ
        set U : E → ℝ := fun z => partialDeriv (E := E) q (chartGramOnE (I := I) (gfam 0) x i j) z
          with hU
        set V : E → ℝ := fun z => partialDeriv (E := E) q (h i j) z with hV
        have hpartcongr : partialDeriv (E := E) p
            (partialDeriv (E := E) q (chartGramOnE (I := I) (gfam σ) x i j)) y =
            partialDeriv (E := E) p (fun z => U z + σ * V z) y := by
          simp only [partialDeriv]; rw [hgerm.fderiv_eq]
        rw [hpartcongr]
        simp only [partialDeriv]
        have hBσ : HasFDerivAt (fun z => σ * V z) (σ • fderiv ℝ V y) y :=
          hBq_diff.hasFDerivAt.const_mul σ
        have hsum : HasFDerivAt (fun z => U z + σ * V z)
            (fderiv ℝ U y + σ • fderiv ℝ V y) y := hAq_diff.hasFDerivAt.add hBσ
        rw [hsum.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have heq : (fun σ : ℝ =>
          partialDeriv (E := E) p (partialDeriv (E := E) q (chartGramOnE (I := I) (gfam σ) x i j)) y)
          =ᶠ[nhds 0] (fun σ : ℝ =>
            partialDeriv (E := E) p
              (fun z => partialDeriv (E := E) q (chartGramOnE (I := I) (gfam 0) x i j) z) y +
            σ * partialDeriv (E := E) p (fun z => partialDeriv (E := E) q (h i j) z) y) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε_pos] with σ hσ
        exact hpt σ (by simpa [Real.dist_eq] using hσ)
      apply HasDerivAt.congr_of_eventuallyEq _ heq
      have h1 : HasDerivAt (fun σ : ℝ =>
          partialDeriv (E := E) p
            (fun z => partialDeriv (E := E) q (chartGramOnE (I := I) (gfam 0) x i j) z) y +
          σ * partialDeriv (E := E) p (fun z => partialDeriv (E := E) q (h i j) z) y)
          (0 + 1 * partialDeriv (E := E) p
            (fun z => partialDeriv (E := E) q (h i j) z) y) 0 :=
        (hasDerivAt_const _ _).add ((hasDerivAt_id _).mul_const _)
      simpa using h1
  · intro i j
    have hbase_t : y₀ ∈ (extChartAt I x).target := by rw [hy₀]; exact mem_extChartAt_target x
    have hgs_eq : gs = realizedFam (I := I) g₀ T T' hδ hδ' s := hgs
    filter_upwards [hχE_one_near,
      (isOpen_extChartAt_target (I := I) x).mem_nhds hbase_t,
      (isOpen_extChartAt_target (I := I) x).mem_nhds hbase_t] with y hy1 hyt _
    
    have hdaff : HasDerivAt
        (fun σ : ℝ => chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' σ) x i j y)
        (chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x i j y -
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x i j y) s := by
      have heq2 : (fun σ : ℝ => chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' σ) x i j y)
          =ᶠ[nhds s] (fun σ : ℝ =>
            (1 - σ) * chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x i j y +
            σ * chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x i j y) := by
        filter_upwards [hSopen.mem_nhds hsmem] with σ hσ
        exact realizedFam_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hσ x i j y
      apply HasDerivAt.congr_of_eventuallyEq _ heq2
      have h1 : HasDerivAt (fun σ : ℝ =>
          (1 - σ) * chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x i j y +
          σ * chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x i j y)
          ((0 - 1) * chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x i j y +
            1 * chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x i j y) s := by
        apply HasDerivAt.add
        · exact (((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).mul_const _)
        · exact (hasDerivAt_id s).mul_const _
      convert h1 using 1
      ring
    
    have hhval : h i j y =
        chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x i j y -
          chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x i j y := by
      change hcomp i j y = _
      simp only [hhcomp]
      have hχ1 : χE y = 1 := hy1
      rw [hχ1, one_mul, hBframe_eq i j y]
    rw [hhval]
    exact hdaff
  · intro i k
    filter_upwards [hWσ_nhds] with σ hσW
    refine chartRicciTensor_congr_of_chartGramOnE_eventuallyEq (g := gfam σ)
      (g' := realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) (α := x) (y := y₀) ?_ i k
    intro a b
    exact hloc_gram σ hσW a b
  · intro i k
    have hbase_int : y₀ ∈ interior (extChartAt I x).target :=
      extChartAt_target_subset_interior_of_boundaryless (I := I) x (by rw [hy₀]; exact mem_extChartAt_target x)
    filter_upwards [hWσ_nhds] with σ hσW
    
    rw [DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartFComponentOnE_deTurckRicciRHS_eq
        (I := I) g_bg (gfam σ) x i k hbase_int,
      DifferentialGeometry.PDE.DeTurck.DeTurckLinearization.chartFComponentOnE_deTurckRicciRHS_eq
        (I := I) g_bg (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x i k hbase_int]
    refine chartDeTurckRicciRHS_congr_of_chartGramOnE_eventuallyEq (g := gfam σ)
      (g' := realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) (g_bg := g_bg) (α := x) (y := y₀) ?_ i k
    intro a b
    exact hloc_gram σ hσW a b

def realizedDeTurckRicciChartSum (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) : ℝ :=
  ∑ i, ∑ k,
    ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
      DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k (extChartAt I x x)

private theorem appCc_unitModel_read_continuousOn_of_toModel_continuousOn
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r 2) (W : SmoothCcTensor g₀ 0 r) {S : Set ℝ}
    {x : M} (hΨ : ContinuousOn (fun s : ℝ => TensorRSSpace.toModel ((Ψ s).toSection x)) S)
    (v : Fin 2 → TangentSpace I x) :
    ContinuousOn (fun s : ℝ =>
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Ψ s) W) x v) S := by
  
  set u : Tensor0SSpace r I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hu
  
  have key : ∀ s : ℝ,
      unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Ψ s) W) x v =
        ((TensorRSSpace.toModel ((Ψ s).toSection x)) (Tensor0SSpace.toModel u)) v := by
    intro s
    rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
      toModel_tensorRS_apply (I := I) r 2 x ((Ψ s).toSection x) u]
  
  have hchain : Continuous (fun T : Tensor0SBundle.TensorRSModel r 2 ℝ E =>
      (T (Tensor0SBundle.Tensor0SSpace.toModel u)) v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ v).continuous.comp
      (ContinuousLinearMap.apply ℝ (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (Tensor0SBundle.Tensor0SSpace.toModel u)).continuous
  exact (hchain.comp_continuousOn hΨ).congr (fun s _ => (key s).symm)

set_option backward.isDefEq.respectTransparency false in

theorem ricciArmPrincipalCoeffPure_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((ricciArmPrincipalCoeffPure (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  
  
  
  have hsection :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 2 p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
      (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace 4 I x)
      (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
      (φ := fun p : M × ℝ =>
        DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.cometricDoubleTraceFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) 2 p.1)
      (S := realizedSmallSet (δ := δ) (δ' := δ'))
    intro Y
    
    have hYjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 4 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) p.1 (Y p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
      Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
    
    exact cometricDoubleTraceFib_realizedFam_jointContMDiffOn (I := I) (p := 2) g₀ T T' hδ hδ'
      (fun p : M × ℝ => Y p.1) hYjoint
  refine hsection.congr (fun p _ => ?_)
  rw [ricciArmPrincipalCoeffPure_toSection]

theorem ricciArmPrincipalCoeffPure_realizedFam_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((ricciArmPrincipalCoeffPure (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t)).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := ricciArmPrincipalCoeffPure_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
    (fun t => ricciArmPrincipalCoeffPure (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' t)) (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x

set_option linter.unusedSectionVars false in

private theorem jointRSadd {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
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
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    rw [Pi.add_apply]
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · rw [Pi.add_apply]
    exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option linter.unusedSectionVars false in

private theorem jointS0add {s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.Tensor0SModel s ℝ E)
    (fun z : M => Tensor0SBundle.Tensor0SSpace s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    rw [Pi.add_apply]
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · rw [Pi.add_apply]
    exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option linter.unusedSectionVars false in

private theorem jointRSsmul {r s : ℕ} {S : Set ℝ} (a : ℝ)
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

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in

private theorem reindexCoeffGen_jointContMDiffOn {r : ℕ} {S : Set ℝ}
    (g₀ : SmoothRiemannianMetric I M) (R : ℝ → SmoothCcTensor g₀ r 2) (σ' : Equiv.Perm (Fin r))
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1
        ((R p.2).toSection p.1)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1
        ((reindexCoeffGen (I := I) (M := M) g₀ r 2 (R p.2) σ').toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SBundle.Tensor0SSpace r I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => reindexCoeffFibGen (I := I) r 2 σ' p.1
      (show Tensor0SBundle.Tensor0SSpace r I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        (R p.2).toSection p.1))
    (S := S)
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
  
  have hYσjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel r ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace r I z) p.1
        (Tensor0SBundle.Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)))))
      ((Set.univ : Set M) ×ˢ S) :=
    hYσ.comp_contMDiffOn contMDiffOn_fst
  have happ := ContMDiffOn.clm_bundle_apply (n := ∞) (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))
    (F₁ := Tensor0SBundle.Tensor0SModel r ℝ E) (E₁ := fun x : M => Tensor0SBundle.Tensor0SSpace r I x)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (E₂ := fun x : M => Tensor0SBundle.Tensor0SSpace 2 I x)
    (b := Prod.fst) (s := (Set.univ : Set M) ×ˢ S)
    (ϕ := fun p : M × ℝ =>
      (show Tensor0SBundle.Tensor0SSpace r I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        (R p.2).toSection p.1))
    (v := fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SBundle.Tensor0SSpace.toModel (Y p.1))))
    hR hYσjoint
  refine happ.congr (fun p _ => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 t)
    (reindexCoeffFibGen_apply (I := I) r 2 σ' p.1
      (show Tensor0SBundle.Tensor0SSpace r I p.1 →L[ℝ] Tensor0SBundle.Tensor0SSpace 2 I p.1 from
        (R p.2).toSection p.1) (Y p.1)).symm

open DifferentialGeometry.Integral.DivergenceTheorem in

theorem realizedFam_chartRiemannTensor_jointContMDiffOn [BoundarylessManifold I M]
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

open DifferentialGeometry.Integral.DivergenceTheorem in

theorem realizedFam_chartGramMatrix_jointContMDiffOn_free [BoundarylessManifold I M]
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

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0CurvCoeff_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  set σ' : Equiv.Perm (Fin (2 + 0)) :=
    Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 0) with hσ'
  set R : ℝ → SmoothCcTensor g₀ (2 + 0) 2 := fun s =>
    ricciArmOrder0CurvCoeff (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hR
  have hbare := ricciArmOrder0CurvCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  have hReind := reindexCoeffGen_jointContMDiffOn (I := I) (M := M) (r := 2 + 0)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g₀ R σ' hbare
  have hsum := jointRSadd (I := I) (r := 2 + 0) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (A := fun p : M × ℝ => (1 / 2 : ℝ) • (R p.2).toSection p.1)
    (B := fun p : M × ℝ =>
      (1 / 2 : ℝ) • (reindexCoeffGen (I := I) (M := M) g₀ (2 + 0) 2 (R p.2) σ').toSection p.1)
    (jointRSsmul (I := I) (r := 2 + 0) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
      (fun p : M × ℝ => (R p.2).toSection p.1) hbare)
    (jointRSsmul (I := I) (r := 2 + 0) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
      (fun p : M × ℝ => (reindexCoeffGen (I := I) (M := M) g₀ (2 + 0) 2 (R p.2) σ').toSection p.1)
      hReind)
  refine hsum.congr (fun p _ => ?_)
  rfl

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0CurvCoeff_realizedFam_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t) (T - T')).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := symmAbsorbedOrder0CurvCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2
    (fun t => symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' t) (T - T')) (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x

set_option linter.unusedSectionVars false in

theorem symmAbsorbedPrincipalCoeffPure_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((symmAbsorbedPrincipalCoeffPure (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  set σ' : Equiv.Perm (Fin (2 + 2)) :=
    Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 2) with hσ'
  set R : ℝ → SmoothCcTensor g₀ (2 + 2) 2 := fun s =>
    ricciArmPrincipalCoeffPure (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hR
  have hbare := ricciArmPrincipalCoeffPure_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  have hReind := reindexCoeffGen_jointContMDiffOn (I := I) (M := M) (r := 2 + 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g₀ R σ' hbare
  have hsum := jointRSadd (I := I) (r := 2 + 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (A := fun p : M × ℝ => (1 / 2 : ℝ) • (R p.2).toSection p.1)
    (B := fun p : M × ℝ =>
      (1 / 2 : ℝ) • (reindexCoeffGen (I := I) (M := M) g₀ (2 + 2) 2 (R p.2) σ').toSection p.1)
    (jointRSsmul (I := I) (r := 2 + 2) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
      (fun p : M × ℝ => (R p.2).toSection p.1) hbare)
    (jointRSsmul (I := I) (r := 2 + 2) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
      (fun p : M × ℝ => (reindexCoeffGen (I := I) (M := M) g₀ (2 + 2) 2 (R p.2) σ').toSection p.1)
      hReind)
  refine hsum.congr (fun p _ => ?_)
  rfl

set_option linter.unusedSectionVars false in

theorem symmAbsorbedPrincipalCoeffPure_realizedFam_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((symmAbsorbedPrincipalCoeffPure (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t) (T - T')).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := symmAbsorbedPrincipalCoeffPure_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 4 2
    (fun t => symmAbsorbedPrincipalCoeffPure (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' t) (T - T')) (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x

open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem riemannKernelChartα_eq [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (α : M) (a c pp qq : Fin (Module.finrank ℝ E))
    {w : M} (hx : w ∈ (chartAt H α).source) :
    g.inner w
        (riemannOp (cov := LeviCivita (I := I) g) w
          (chartBasisVecFiber (I := I) α a w) (chartBasisVecFiber (I := I) α pp w)
          (chartBasisVecFiber (I := I) α qq w))
        (chartBasisVecFiber (I := I) α c w) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) g α qq a pp l (extChartAt I α w) *
          chartGramMatrix (I := I) g α w l c := by
  have hxgood : w ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hx
  rw [riemannOp_chartBasisVec_alpha_eq (I := I) g α qq a pp hxgood]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, chartGramMatrix_apply g α w l c]

open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem riemannKernelChartα_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (a c pp qq : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun w : M × ℝ =>
        (realizedFam (I := I) g₀ T T' hδ hδ' w.2).inner w.1
          (riemannOp (cov := LeviCivita (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2)) w.1
            (chartBasisVecFiber (I := I) α a w.1) (chartBasisVecFiber (I := I) α pp w.1)
            (chartBasisVecFiber (I := I) α qq w.1))
          (chartBasisVecFiber (I := I) α c w.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hsum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun w : M × ℝ => ∑ l : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α qq a pp l
            (extChartAt I α w.1) *
          chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α w.1 l c)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    contMDiffOn_finset_sum (fun l _ =>
      (realizedFam_chartRiemannTensor_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α qq a pp l).mul
        (realizedFam_chartGramMatrix_jointContMDiffOn_free (I := I) g₀ T T' hδ hδ' α l c))
  refine hsum.congr (fun w hw => ?_)
  exact riemannKernelChartα_eq (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α a c pp qq hw.1

private def offFamCoord (α : M) {y : M} (F : Fin (Module.finrank ℝ E) → TangentSpace I y) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i m =>
    ((chartModelBasis E).repr
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ y (F i))) m

set_option linter.unusedSectionVars false in

private theorem off_sum_famCoord_eq_chartInvGram (g : SmoothRiemannianMetric I M) (α : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hysrc : y ∈ (extChartAt I α).source)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hF : ∀ i j, g.inner y (F i) (F j) = if i = j then (1 : ℝ) else 0)
    (m n : Fin (Module.finrank ℝ E)) :
    (∑ i : Fin (Module.finrank ℝ E),
        offFamCoord (I := I) α F i m * offFamCoord (I := I) α F i n) =
      chartInvGramMatrix (I := I) g α y m n := by
  classical
  have hCGCt : offFamCoord (I := I) α F *
      chartGramMatrix (I := I) g α y * (offFamCoord (I := I) α F)ᵀ = 1 := by
    ext i j
    rw [Matrix.one_apply]
    have hexp := g_inner_eq_chart_sum (I := I) g α hy hysrc (F i) (F j)
    rw [hF i j] at hexp
    have hchart : ∀ a b : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α a b (extChartAt I α y) =
          chartGramMatrix (I := I) g α y a b := by
      intro a b; unfold chartGramOnE; rw [(extChartAt I α).left_inv hysrc]
    rw [Matrix.mul_apply]
    rw [show (∑ a, (offFamCoord (I := I) α F *
          chartGramMatrix (I := I) g α y) i a *
          (offFamCoord (I := I) α F)ᵀ a j) =
        ∑ a, ∑ b, offFamCoord (I := I) α F i a * offFamCoord (I := I) α F j b *
          chartGramMatrix (I := I) g α y a b from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Matrix.transpose_apply]; ring]
    rw [hexp]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hchart a b]; rfl
  have hC : offFamCoord (I := I) α F *
        (chartGramMatrix (I := I) g α y * (offFamCoord (I := I) α F)ᵀ) = 1 := by
    rw [← Matrix.mul_assoc]; exact hCGCt
  have h2 : (chartGramMatrix (I := I) g α y * (offFamCoord (I := I) α F)ᵀ) *
        offFamCoord (I := I) α F = 1 :=
    mul_eq_one_comm.mp hC
  rw [Matrix.mul_assoc] at h2
  have hinv : (offFamCoord (I := I) α F)ᵀ * offFamCoord (I := I) α F =
      (chartGramMatrix (I := I) g α y)⁻¹ :=
    (Matrix.inv_eq_right_inv h2).symm
  have hmn := congrFun (congrFun hinv m) n
  rw [Matrix.mul_apply] at hmn
  rw [chartInvGramMatrix, ← hmn]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.transpose_apply]

set_option linter.unusedSectionVars false in

private lemma off_recompose (α : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I y) (i : Fin (Module.finrank ℝ E)) :
    (F i : TangentSpace I y) =
      ∑ m : Fin (Module.finrank ℝ E),
        offFamCoord (I := I) α F i m • chartBasisVecFiber (I := I) α m y := by
  classical
  exact chartBasisVecFiber_recompose (I := I) α hy (F i)

set_option linter.unusedSectionVars false in

private theorem off_scalarBilin_ortho_diag_eq_chartInvGram_trace
    (g : SmoothRiemannianMetric I M) (α : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hysrc : y ∈ (extChartAt I α).source)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hF : ∀ i j, g.inner y (F i) (F j) = if i = j then (1 : ℝ) else 0)
    (A : TangentSpace I y → TangentSpace I y → ℝ)
    (hAl : ∀ (c : ℝ) (a b w : TangentSpace I y), A (c • a + b) w = c * A a w + A b w)
    (hAr : ∀ (c : ℝ) (a w w' : TangentSpace I y), A a (c • w + w') = c * A a w + A a w') :
    (∑ i : Fin (Module.finrank ℝ E), A (F i) (F i)) =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α y m n *
          A (chartBasisVecFiber (I := I) α m y) (chartBasisVecFiber (I := I) α n y) := by
  classical
  have hAl0 : ∀ w, A (0 : TangentSpace I y) w = 0 := by
    intro w; have h := hAl 1 0 0 w; rw [smul_zero, add_zero, one_mul] at h; linarith
  have hAr0 : ∀ a, A a (0 : TangentSpace I y) = 0 := by
    intro a; have h := hAr 1 a 0 0; rw [smul_zero, add_zero, one_mul] at h; linarith
  have hAl_sum : ∀ (cs : Fin (Module.finrank ℝ E) → ℝ) (w : TangentSpace I y),
      A (∑ m, cs m • chartBasisVecFiber (I := I) α m y) w =
        ∑ m, cs m * A (chartBasisVecFiber (I := I) α m y) w := by
    intro cs w
    induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, hAl0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hAl, ih]
  have hAr_sum : ∀ (a : TangentSpace I y) (cs : Fin (Module.finrank ℝ E) → ℝ),
      A a (∑ n, cs n • chartBasisVecFiber (I := I) α n y) =
        ∑ n, cs n * A a (chartBasisVecFiber (I := I) α n y) := by
    intro a cs
    induction (Finset.univ : Finset (Fin (Module.finrank ℝ E))) using Finset.induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, hAr0]
    | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, hAr, ih]
  have hsummand : ∀ i, A (F i) (F i) =
      ∑ m, ∑ n, (offFamCoord (I := I) α F i m * offFamCoord (I := I) α F i n) *
        A (chartBasisVecFiber (I := I) α m y) (chartBasisVecFiber (I := I) α n y) := by
    intro i
    conv_lhs => rw [off_recompose (I := I) α hy F i]
    rw [hAl_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hAr_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mul_assoc]
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← Finset.sum_mul]
  congr 1
  rw [← off_sum_famCoord_eq_chartInvGram (I := I) g α hy hysrc F hF m n]

set_option linter.unusedSectionVars false in

private theorem off_double_frame_bilin_trace_eq_chartAlpha
    (g : SmoothRiemannianMetric I M) (α : M) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hysrc : y ∈ (extChartAt I α).source)
    (K Dd : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hF : ∀ i j, g.inner y (F i) (F j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (F a) (F b) * Dd (F a) (F b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g α y m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α y k l *
          (K (chartBasisVecFiber (I := I) α m y) (chartBasisVecFiber (I := I) α k y) *
            Dd (chartBasisVecFiber (I := I) α n y) (chartBasisVecFiber (I := I) α l y))) := by
  classical
  have hinner : ∀ a, ∑ b, K (F a) (F b) * Dd (F a) (F b) =
      ∑ k, ∑ l, chartInvGramMatrix (I := I) g α y k l *
        (K (F a) (chartBasisVecFiber (I := I) α k y) *
          Dd (F a) (chartBasisVecFiber (I := I) α l y)) := by
    intro a
    exact off_scalarBilin_ortho_diag_eq_chartInvGram_trace (I := I) g α hy hysrc F hF
      (fun p q => K (F a) p * Dd (F a) q)
      (by intro c p q w; simp only [map_add, map_smul, smul_eq_mul]; ring)
      (by intro c p q w; simp only [map_add, map_smul, smul_eq_mul]; ring)
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  set Φ : TangentSpace I y → TangentSpace I y → ℝ :=
    fun X X' => ∑ k, ∑ l, chartInvGramMatrix (I := I) g α y k l *
        (K X (chartBasisVecFiber (I := I) α k y) *
          Dd X' (chartBasisVecFiber (I := I) α l y)) with hΦ
  have hΦl : ∀ (c : ℝ) (p w w' : TangentSpace I y), Φ (c • p + w) w' = c * Φ p w' + Φ w w' := by
    intro c p w w'
    rw [hΦ]
    simp only
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro l _
    rw [map_add, map_smul]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hΦr : ∀ (c : ℝ) (p w w' : TangentSpace I y), Φ p (c • w + w') = c * Φ p w + Φ p w' := by
    intro c p w w'
    rw [hΦ]
    simp only
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro l _
    rw [map_add, map_smul]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  exact off_scalarBilin_ortho_diag_eq_chartInvGram_trace (I := I) g α hy hysrc F hF Φ hΦl hΦr

set_option linter.unusedSectionVars false in

private theorem contMDiffOn_bilinSection_of_jointChartScalar {S : Set ℝ}
    (Hb : (p : M × ℝ) → TangentSpace I p.1 →L[ℝ] TangentSpace I p.1 →L[ℝ] ℝ)
    (hscalar : ∀ (α : M) (σ : Fin 2 → Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ => Hb p (chartBasisVecFiber (I := I) α (σ 0) p.1)
          (chartBasisVecFiber (I := I) α (σ 1) p.1))
        ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := p.1)
          (bilinFormToModel (TangentSpace I p.1) (Hb p)))) ((Set.univ : Set M) ×ˢ S) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  intro p₀ hp₀
  have hs₀ : p₀.2 ∈ S := hp₀.2
  set x₀ := p₀.1 with hx₀
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb_def
  set Bb := continuousMultilinearMap_basis b 2 with hBb
  set f := fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := p.1)
      (bilinFormToModel (TangentSpace I p.1) (Hb p)) with hf
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set g := fun p : M × ℝ => (trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x₀ ⟨p.1, f p⟩).2 with hg
  change ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E) ∞ g
    ((Set.univ : Set M) ×ˢ S) p₀
  rw [show g = fun p => Bb.equivFun.symm (Bb.equivFun (g p)) from
      funext fun p => (Bb.equivFun.symm_apply_apply (g p)).symm]
  refine (Bb.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.contMDiffAt).comp_contMDiffWithinAt
    p₀ ?_
  rw [contMDiffWithinAt_pi_space]
  intro σ
  have hbase : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hsc := hscalar x₀ σ
  have hsc_at : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => Hb p (chartBasisVecFiber (I := I) x₀ (σ 0) p.1)
        (chartBasisVecFiber (I := I) x₀ (σ 1) p.1))
      ((trivializationAt E (TangentSpace I) x₀).baseSet ×ˢ S) p₀ :=
    hsc p₀ ⟨by rw [← hx₀]; exact hbase, hs₀⟩
  have hmem : (trivializationAt E (TangentSpace I) x₀).baseSet ×ˢ S ∈
      nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S) := by
    have h1 : (trivializationAt E (TangentSpace I) x₀).baseSet ×ˢ S =
        ((Set.univ : Set M) ×ˢ S) ∩
          ((trivializationAt E (TangentSpace I) x₀).baseSet ×ˢ (Set.univ : Set ℝ)) := by
      ext q
      simp only [Set.mem_prod, Set.mem_univ, true_and, and_true, Set.mem_inter_iff]
      tauto
    rw [h1]
    exact inter_mem_nhdsWithin ((Set.univ : Set M) ×ˢ S)
      (((trivializationAt E (TangentSpace I) x₀).open_baseSet.prod isOpen_univ).mem_nhds
        ⟨by rw [← hx₀]; exact hbase, trivial⟩)
  have hsc_univ := hsc_at.mono_of_mem_nhdsWithin hmem
  
  have hcoord : ∀ {p : M × ℝ}, p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet →
      Bb.equivFun (g p) σ =
        Hb p (chartBasisVecFiber (I := I) x₀ (σ 0) p.1)
          (chartBasisVecFiber (I := I) x₀ (σ 1) p.1) := by
    intro p hp
    have hrepr : Bb.equivFun (g p) σ = (g p) (fun j => b (σ j)) := by
      rw [hBb]; exact continuousMultilinearMap_basis_repr b 2 (g p) σ
    rw [hrepr, hg]
    change Tensor0SBundle.Tensor0SSpace.toModel (f p)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.1 (b (σ j))) = _
    rw [hf, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]
    exact bilinFormToModel_apply (TangentSpace I p.1) (Hb p)
      (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ p.1 (b (σ j)))
  refine hsc_univ.congr_of_eventuallyEq ?_ (hcoord (by rw [← hx₀]; exact hbase))
  have h_base_nhd : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S),
      p.1 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
      ((trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds (by rw [← hx₀]; exact hbase))
  filter_upwards [h_base_nhd] with p hp
  exact hcoord hp

open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem riemannBiContrFib_toModel_chartα_eq [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (α : M) (σ : Fin 2 → Fin (Module.finrank ℝ E))
    {w : M} (hx : w ∈ (chartAt H α).source)
    (Dw : Tensor0SBundle.Tensor0SSpace 2 I w) :
    Tensor0SBundle.Tensor0SSpace.toModel (riemannBiContrFib (I := I) g w Dw)
        (fun i => chartBasisVecFiber (I := I) α (σ i) w) =
      2 * ∑ m, ∑ n, chartInvGramMatrix (I := I) g α w m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α w k l *
          (g.inner w
              (riemannOp (cov := LeviCivita (I := I) g) w
                (chartBasisVecFiber (I := I) α (σ 0) w) (chartBasisVecFiber (I := I) α m w)
                (chartBasisVecFiber (I := I) α k w))
              (chartBasisVecFiber (I := I) α (σ 1) w) *
            Tensor0SBundle.Tensor0SSpace.toModel Dw
              ![chartBasisVecFiber (I := I) α n w, chartBasisVecFiber (I := I) α l w])) := by
  classical
  have hxbase : w ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
      TangentBundle.trivializationAt_baseSet (I := I) α]
    exact hx
  have hxsrc : w ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  rw [riemannBiContrFib, riemannBiContrFibFixedFrame_toModel]
  set v0 := chartBasisVecFiber (I := I) α (σ 0) w with hv0
  set v1 := chartBasisVecFiber (I := I) α (σ 1) w with hv1
  have hrewrite : (∑ a, ∑ b,
        g.inner w (riemannOp (LeviCivita (I := I) g) w v0
          (smoothOrthoFrame (I := I) g w a w) (smoothOrthoFrame (I := I) g w b w)) v1 *
          Tensor0SBundle.Tensor0SSpace.toModel Dw
            ![(smoothOrthoFrame (I := I) g w a w : E), (smoothOrthoFrame (I := I) g w b w : E)]) =
      ∑ a, ∑ b,
        frameRiemannKernel (I := I) g w v0 v1
            (smoothOrthoFrame (I := I) g w a w) (smoothOrthoFrame (I := I) g w b w) *
          (bilinFormToModel (TangentSpace I w)).symm (Tensor0SBundle.Tensor0SSpace.toModel Dw)
            (smoothOrthoFrame (I := I) g w a w) (smoothOrthoFrame (I := I) g w b w) := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [frameRiemannKernel_apply]
    congr 1
    rw [bilinFormToModel_symm_apply (TangentSpace I w) (Tensor0SBundle.Tensor0SSpace.toModel Dw)
      (smoothOrthoFrame (I := I) g w a w) (smoothOrthoFrame (I := I) g w b w)]
    rfl
  rw [hrewrite]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  rw [off_double_frame_bilin_trace_eq_chartAlpha (I := I) g α hxbase hxsrc
      (frameRiemannKernel (I := I) g w v0 v1)
      ((bilinFormToModel (TangentSpace I w)).symm (Tensor0SBundle.Tensor0SSpace.toModel Dw))
      (fun a => smoothOrthoFrame (I := I) g w a w)
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g w i j)]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  congr 1
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  congr 1
  rw [frameRiemannKernel_apply]
  congr 1
  rw [bilinFormToModel_symm_apply (TangentSpace I w) (Tensor0SBundle.Tensor0SSpace.toModel Dw)
    (chartBasisVecFiber (I := I) α n w) (chartBasisVecFiber (I := I) α l w)]
  rfl

set_option linter.unusedSectionVars false in

private theorem realizedFam_YchartComponent_jointContMDiffOn {S : Set ℝ} (α : M)
    (Y : Cₛ^∞⟮I; Tensor0SBundle.Tensor0SModel 2 ℝ E, fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z⟯)
    (n l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
        ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1])
      ((trivializationAt E (TangentSpace I) α).baseSet ×ˢ S) := by
  classical
  have hbase : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Tensor0SBundle.Tensor0SSpace.toModel (Y x)
        ![chartBasisVecFiber (I := I) α n x, chartBasisVecFiber (I := I) α l x])
      (trivializationAt E (TangentSpace I) α).baseSet := by
    intro x hx
    have hY : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun b : M => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) b (Y b)) x :=
      Y.contMDiff x
    have hv0 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (chartBasisVecFiber (I := I) α n b)) x :=
      ((chartBasisVec_contMDiffOn (I := I) α n) x hx).contMDiffAt
        ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)
    have hv1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (chartBasisVecFiber (I := I) α l b)) x :=
      ((chartBasisVec_contMDiffOn (I := I) α l) x hx).contMDiffAt
        ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)
    have happ := TensorMultilinear.contMDiffAt_section_apply (n := 2) (x₀ := x) (fun b => Y b) hY
      (![fun b => chartBasisVecFiber (I := I) α n b, fun b => chartBasisVecFiber (I := I) α l b])
      (by
        intro i
        fin_cases i
        · exact hv0
        · exact hv1)
    refine (happ.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards with b
    congr 1
    funext i
    fin_cases i <;> rfl
  exact hbase.comp contMDiffOn_fst (fun p hp => hp.1)

set_option linter.unusedSectionVars false in

theorem ricciArmOrder0RiemannCoeff_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((ricciArmOrder0RiemannCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  
  have hsection :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
          (Tensor0SBundle.TensorRSSpace.ofCLM
            (riemannBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
      (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
      (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
      (φ := fun p : M × ℝ => riemannBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1)
      (S := realizedSmallSet (δ := δ) (δ' := δ'))
    intro Y
    
    have hbridge := contMDiffOn_bilinSection_of_jointChartScalar (I := I) (M := M)
      (S := realizedSmallSet (δ := δ) (δ' := δ'))
      (Hb := fun p : M × ℝ => (bilinFormToModel (TangentSpace I p.1)).symm
        (Tensor0SBundle.Tensor0SSpace.toModel
          (riemannBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1))))
      (by
        intro α σ
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        
        have hsum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun p : M × ℝ => 2 * ∑ m, ∑ n,
                chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m n *
                (∑ k, ∑ l,
                  chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
                  ((realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
                      (riemannOp (cov := LeviCivita (I := I)
                          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)) p.1
                        (chartBasisVecFiber (I := I) α (σ 0) p.1) (chartBasisVecFiber (I := I) α m p.1)
                        (chartBasisVecFiber (I := I) α k p.1))
                      (chartBasisVecFiber (I := I) α (σ 1) p.1) *
                    Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
                      ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1])))
            ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
          have hYcomp : ∀ n l : Fin (Module.finrank ℝ E),
              ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
              (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
                ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1])
              ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
            intro n l
            have h := realizedFam_YchartComponent_jointContMDiffOn (I := I)
              (S := realizedSmallSet (δ := δ) (δ' := δ')) α Y n l
            rwa [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
              TangentBundle.trivializationAt_baseSet (I := I) α] at h
          have hInvGram : ∀ i j : Fin (Module.finrank ℝ E),
              ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
              (fun p : M × ℝ =>
                chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
              ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := fun i j =>
            realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T T' hδ hδ' α i j
          have hinner : ∀ m n k l : Fin (Module.finrank ℝ E),
              ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
              (fun p : M × ℝ =>
                chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
                  ((realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
                      (riemannOp (cov := LeviCivita (I := I)
                          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)) p.1
                        (chartBasisVecFiber (I := I) α (σ 0) p.1) (chartBasisVecFiber (I := I) α m p.1)
                        (chartBasisVecFiber (I := I) α k p.1))
                      (chartBasisVecFiber (I := I) α (σ 1) p.1) *
                    Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
                      ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1]))
              ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
            intro m n k l
            exact (hInvGram k l).mul ((riemannKernelChartα_realizedFam_jointContMDiffOn (I := I)
              g₀ T T' hδ hδ' α (σ 0) (σ 1) m k).mul (hYcomp n l))
          have hmiddle : ∀ m n : Fin (Module.finrank ℝ E),
              ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
              (fun p : M × ℝ =>
                chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m n *
                (∑ k, ∑ l,
                  chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
                  ((realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
                      (riemannOp (cov := LeviCivita (I := I)
                          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)) p.1
                        (chartBasisVecFiber (I := I) α (σ 0) p.1) (chartBasisVecFiber (I := I) α m p.1)
                        (chartBasisVecFiber (I := I) α k p.1))
                      (chartBasisVecFiber (I := I) α (σ 1) p.1) *
                    Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
                      ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1])))
              ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
            intro m n
            exact (hInvGram m n).mul (contMDiffOn_finset_sum (fun k _ =>
              contMDiffOn_finset_sum (fun l _ => hinner m n k l)))
          have hbody : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
              (fun p : M × ℝ => ∑ m, ∑ n,
                chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m n *
                (∑ k, ∑ l,
                  chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
                  ((realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
                      (riemannOp (cov := LeviCivita (I := I)
                          (realizedFam (I := I) g₀ T T' hδ hδ' p.2)) p.1
                        (chartBasisVecFiber (I := I) α (σ 0) p.1) (chartBasisVecFiber (I := I) α m p.1)
                        (chartBasisVecFiber (I := I) α k p.1))
                      (chartBasisVecFiber (I := I) α (σ 1) p.1) *
                    Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
                      ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1])))
              ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
            contMDiffOn_finset_sum (fun m _ => contMDiffOn_finset_sum (fun n _ => hmiddle m n))
          exact (contMDiffOn_const.mul hbody)
        refine hsum.congr (fun p hp => ?_)
        rw [bilinFormToModel_symm_apply (TangentSpace I p.1)
          (Tensor0SBundle.Tensor0SSpace.toModel
            (riemannBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) p.1 (Y p.1)))]
        have hpsrc : p.1 ∈ (chartAt H α).source := by
          rw [← TangentBundle.trivializationAt_baseSet (I := I) α]; exact hp.1
        rw [show (![chartBasisVecFiber (I := I) α (σ 0) p.1, chartBasisVecFiber (I := I) α (σ 1) p.1] :
              Fin 2 → TangentSpace I p.1) =
            (fun i => chartBasisVecFiber (I := I) α (σ i) p.1) from by
          funext i; fin_cases i <;> rfl]
        exact riemannBiContrFib_toModel_chartα_eq (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α σ hpsrc (Y p.1))
    refine hbridge.congr (fun p _ => ?_)
    congr 1
    rw [LinearEquiv.apply_symm_apply, Tensor0SBundle.Tensor0SSpace.ofModel_toModel]
  refine hsection.congr (fun p _ => ?_)
  rw [ricciArmOrder0RiemannCoeff_toSection]

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0RiemannCoeff_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  set σ' : Equiv.Perm (Fin (2 + 0)) :=
    Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 0) with hσ'
  set R : ℝ → SmoothCcTensor g₀ (2 + 0) 2 := fun s =>
    ricciArmOrder0RiemannCoeff (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hR
  have hbare := ricciArmOrder0RiemannCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  have hReind := reindexCoeffGen_jointContMDiffOn (I := I) (M := M) (r := 2 + 0)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g₀ R σ' hbare
  have hsum := jointRSadd (I := I) (r := 2 + 0) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (A := fun p : M × ℝ => (1 / 2 : ℝ) • (R p.2).toSection p.1)
    (B := fun p : M × ℝ =>
      (1 / 2 : ℝ) • (reindexCoeffGen (I := I) (M := M) g₀ (2 + 0) 2 (R p.2) σ').toSection p.1)
    (jointRSsmul (I := I) (r := 2 + 0) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
      (fun p : M × ℝ => (R p.2).toSection p.1) hbare)
    (jointRSsmul (I := I) (r := 2 + 0) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
      (fun p : M × ℝ => (reindexCoeffGen (I := I) (M := M) g₀ (2 + 0) 2 (R p.2) σ').toSection p.1)
      hReind)
  refine hsum.congr (fun p _ => ?_)
  rfl

open DifferentialGeometry.Integral.DivergenceTheorem in

theorem realizedFam_chartChristoffel_jointContMDiffOn [BoundarylessManifold I M]
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

open DifferentialGeometry.Integral.DivergenceTheorem in

theorem realizedFam_partial_chartChristoffel_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (m i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => partialDeriv (E := E) m
        (fun y => chartChristoffel (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α i j k y) (extChartAt I α p.1))
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
  have hentry := gen_joint_partial_christoffel (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ') α hG m i j k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => partialDeriv (E := E) m
        (fun y => chartChristoffel (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' r.1) α i j k y) r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun p : M × ℝ => (p.2, extChartAt I α p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr
    (fun q _ => rfl) rfl

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.DivergenceTheorem in

theorem chartChristoffel_fixed_jointContMDiffOn [BoundarylessManifold I M] {S : Set ℝ}
    (g_bg : SmoothRiemannianMetric I M) (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => chartChristoffel (I := I) g_bg α i j k (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hbase : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g_bg α i j k) (extChartAt I α p.1) :=
    (chartChristoffel_contDiffOn_interior (I := I) g_bg α i j k).contDiffAt
      (isOpen_interior.mem_nhds hy)
  have hbaseM : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E => chartChristoffel (I := I) g_bg α i j k y) (extChartAt I α p.1) :=
    hbase.contMDiffAt
  have hmove : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : M × ℝ => extChartAt I α q.1)
      ((chartAt H α).source ×ˢ S) p :=
    ((contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun q hq => hq.1)) p ⟨hx, hs⟩
  exact (hbaseM.comp_contMDiffWithinAt p hmove).congr (fun q _ => rfl) rfl

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.DivergenceTheorem in

theorem partial_chartChristoffel_fixed_jointContMDiffOn [BoundarylessManifold I M] {S : Set ℝ}
    (g_bg : SmoothRiemannianMetric I M) (α : M) (m i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => partialDeriv (E := E) m
        (fun y => chartChristoffel (I := I) g_bg α i j k y) (extChartAt I α p.1))
      ((chartAt H α).source ×ˢ S) := by
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  
  have hbase : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g_bg α i j k) (extChartAt I α p.1) :=
    (chartChristoffel_contDiffOn_interior (I := I) g_bg α i j k).contDiffAt
      (isOpen_interior.mem_nhds hy)
  have hconst : ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        (fun _ : ℝ => fun y : E => chartChristoffel (I := I) g_bg α i j k y) r.1 r.2)
      (p.2, extChartAt I α p.1) := by
    rw [show (fun r : ℝ × E =>
        (fun _ : ℝ => fun y : E => chartChristoffel (I := I) g_bg α i j k y) r.1 r.2) =
        (chartChristoffel (I := I) g_bg α i j k) ∘ (fun r : ℝ × E => r.2) from rfl]
    exact ContDiffAt.comp (p.2, extChartAt I α p.1) hbase contDiffAt_snd
  have hentry := gen_joint_partialDeriv
    (fun _ : ℝ => fun y : E => chartChristoffel (I := I) g_bg α i j k y) m hconst
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => partialDeriv (E := E) m
        (fun y => chartChristoffel (I := I) g_bg α i j k y) r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ => (q.2, extChartAt I α q.1))
      ((chartAt H α).source ×ˢ S) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun q hq => hq.1)
  have hmove : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun q : M × ℝ => (q.2, extChartAt I α q.1))
      ((chartAt H α).source ×ˢ S) p := by
    have hm := hmoveOn p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmove).congr (fun q _ => rfl) rfl

open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private lemma covDeriv_chartCoordField_alpha [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M) (a : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (c : Fin (Module.finrank ℝ E) → M → ℝ)
    (hc : ∀ p : Fin (Module.finrank ℝ E), MDifferentiableAt I 𝓘(ℝ, ℝ) (c p) x)
    {S : Π b : M, TangentSpace I b} {U : Set M}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (S b)))
    (hU_open : IsOpen U) (hxU : x ∈ U)
    (hS_eq : ∀ y ∈ U, S y = ∑ p : Fin (Module.finrank ℝ E),
      c p y • chartBasisVecFiber (I := I) α p y) :
    (LeviCivita (I := I) g).toFun S x (chartBasisVecFiber (I := I) α a x) =
      ∑ l : Fin (Module.finrank ℝ E),
        (extDerivFun (I := I) (c l) x (chartBasisVecFiber (I := I) α a x) +
          ∑ m : Fin (Module.finrank ℝ E),
            c m x * chartChristoffel (I := I) g α a m l (extChartAt I α x)) •
          chartBasisVecFiber (I := I) α l x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  set term : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun p y => c p y • chartBasisVecFiber (I := I) α p y with hterm_def
  have hframe_diff : ∀ m : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (chartBasisVecFiber (I := I) α m b)) x :=
    fun m => chartBasisVec_alpha_mdifferentiableAt (I := I) α m hx
  have hterm_diff : ∀ p : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (term p b)) x :=
    fun p => MDifferentiableAt.smul_section (hc p) (hframe_diff p)
  have hsum_diff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (∑ p : Fin (Module.finrank ℝ E), term p b)) x :=
    MDifferentiableAt.sum_section (s := Finset.univ) (t := term) hterm_diff
  have hS_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (S b)) x :=
    (hS x).mdifferentiableAt (by simp)
  have hS_ev_sum :
      (fun y : M => S y) =ᶠ[𝓝 x]
        (fun y : M => ∑ p : Fin (Module.finrank ℝ E), term p y) := by
    filter_upwards [hU_open.mem_nhds hxU] with y hy using hS_eq y hy
  have hcov_S_eq :
      cov.toFun S x =
        cov.toFun (fun y : M => ∑ p : Fin (Module.finrank ℝ E), term p y) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hS_diff hsum_diff
      Filter.univ_mem hS_ev_sum
  rw [hcov_S_eq]
  have hsum_apply :
      (cov.toFun (fun y : M => ∑ p : Fin (Module.finrank ℝ E), term p y) x)
          (chartBasisVecFiber (I := I) α a x) =
        ∑ p : Fin (Module.finrank ℝ E),
          (cov.toFun (term p) x) (chartBasisVecFiber (I := I) α a x) := by
    have hfun :
        (fun y : M => ∑ p : Fin (Module.finrank ℝ E), term p y) =
          (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum term := by
      funext y; simp
    rw [hfun]
    exact leviCivita_finset_sum_apply (I := I) g
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) term
      (chartBasisVecFiber (I := I) α a x) hterm_diff
  rw [hsum_apply]
  have hleib : ∀ p : Fin (Module.finrank ℝ E),
      (cov.toFun (term p) x) (chartBasisVecFiber (I := I) α a x) =
        extDerivFun (I := I) (c p) x (chartBasisVecFiber (I := I) α a x) •
            chartBasisVecFiber (I := I) α p x +
          c p x •
            (cov.toFun (fun y : M => chartBasisVecFiber (I := I) α p y) x)
              (chartBasisVecFiber (I := I) α a x) := by
    intro p
    have hleibniz := cov.isCovariantDerivativeOnUniv.leibniz
      (σ := fun y : M => chartBasisVecFiber (I := I) α p y) (g := c p) (x := x)
      (hframe_diff p) (hc p)
    have hterm_eq : term p = (c p) • (fun y : M => chartBasisVecFiber (I := I) α p y) := by
      funext y; rfl
    rw [hterm_eq]
    have happ := congr($(hleibniz) (chartBasisVecFiber (I := I) α a x))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply] at happ
    rw [happ, add_comm]
  rw [Finset.sum_congr rfl (fun p _ => hleib p)]
  have hinner : ∀ p : Fin (Module.finrank ℝ E),
      (cov.toFun (fun y : M => chartBasisVecFiber (I := I) α p y) x)
          (chartBasisVecFiber (I := I) α a x) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α a p l (extChartAt I α x) •
            chartBasisVecFiber (I := I) α l x := by
    intro p
    rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g α a p hx]
  rw [Finset.sum_congr rfl (fun p _ => by rw [hinner p])]
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun l => chartBasisVecFiber (I := I) α l x with he_def
  set D : Fin (Module.finrank ℝ E) → ℝ :=
    fun l => extDerivFun (I := I) (c l) x (chartBasisVecFiber (I := I) α a x) with hD_def
  set Γq : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun p l => chartChristoffel (I := I) g α a p l (extChartAt I α x) with hΓq_def
  set cc : Fin (Module.finrank ℝ E) → ℝ := fun p => c p x with hcc_def
  calc
    (∑ p : Fin (Module.finrank ℝ E),
        (D p • e p + cc p • ∑ l : Fin (Module.finrank ℝ E), Γq p l • e l))
        = (∑ p : Fin (Module.finrank ℝ E), D p • e p) +
            (∑ p : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E), (cc p * Γq p l) • e l) := by
          rw [Finset.sum_add_distrib]
          refine congrArg (fun t => (∑ p : Fin (Module.finrank ℝ E), D p • e p) + t) ?_
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [smul_smul]
      _ = (∑ l : Fin (Module.finrank ℝ E), D l • e l) +
            (∑ l : Fin (Module.finrank ℝ E),
              ∑ p : Fin (Module.finrank ℝ E), (cc p * Γq p l) • e l) := by
          rw [Finset.sum_comm]
      _ = ∑ l : Fin (Module.finrank ℝ E),
            (D l + ∑ p : Fin (Module.finrank ℝ E), cc p * Γq p l) • e l := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [← Finset.sum_smul, ← add_smul]

private def connDiffChartCoeff (g g_bg : SmoothRiemannianMetric I M) (α : M)
    (j k p : Fin (Module.finrank ℝ E)) (y : M) : ℝ :=
  chartChristoffel (I := I) g α k j p (extChartAt I α y) -
    chartChristoffel (I := I) g_bg α k j p (extChartAt I α y)

open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private lemma connDiffChartCoeff_mdiff [I.Boundaryless]
    (g g_bg : SmoothRiemannianMetric I M) (α : M) (j k p : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (connDiffChartCoeff (I := I) g g_bg α j k p) x := by
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hgE_cda : ContDiffAt ℝ ∞
      (fun y : E => chartChristoffel (I := I) g α k j p y -
        chartChristoffel (I := I) g_bg α k j p y) (extChartAt I α x) :=
    (chartChristoffel_contDiffAt_alpha (I := I) g α k j p hx).sub
      (chartChristoffel_contDiffAt_alpha (I := I) g_bg α k j p hx)
  have hgE_d : DifferentiableAt ℝ
      (fun y : E => chartChristoffel (I := I) g α k j p y -
        chartChristoffel (I := I) g_bg α k j p y) (extChartAt I α x) :=
    hgE_cda.differentiableAt (by simp)
  have hgE_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (fun y : E => chartChristoffel (I := I) g α k j p y -
        chartChristoffel (I := I) g_bg α k j p y) (extChartAt I α x) := by
    rw [mdifferentiableAt_iff_differentiableAt]; exact hgE_d
  have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
  exact hgE_mdiff.comp x hphi_mdiff

open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private lemma connDiffChartCoeff_extDerivFun [I.Boundaryless]
    (g g_bg : SmoothRiemannianMetric I M) (α : M) (a j k p : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    extDerivFun (I := I) (connDiffChartCoeff (I := I) g g_bg α j k p) x
        (chartBasisVecFiber (I := I) α a x) =
      partialDeriv (E := E) a
          (fun y => chartChristoffel (I := I) g α k j p y -
            chartChristoffel (I := I) g_bg α k j p y) (extChartAt I α x) := by
  have hgE_cda : ContDiffAt ℝ ∞
      (fun y : E => chartChristoffel (I := I) g α k j p y -
        chartChristoffel (I := I) g_bg α k j p y) (extChartAt I α x) :=
    (chartChristoffel_contDiffAt_alpha (I := I) g α k j p hx).sub
      (chartChristoffel_contDiffAt_alpha (I := I) g_bg α k j p hx)
  exact extDerivFun_comp_extChartAt_apply_basis_alpha (I := I) α hx hgE_cda a

open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem dLaCovDerivA_chartBasis_inner_eq [I.Boundaryless]
    (g₁ g_bg : SmoothRiemannianMetric I M) (α : M) (a c pp qq : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    g₁.inner x
        (deTurckLieCovDerivA (I := I) g₁ g_bg
          (fun b : M => chartBasisVecFiber (I := I) α a b)
          (fun b : M => chartBasisVecFiber (I := I) α pp b)
          (fun b : M => chartBasisVecFiber (I := I) α qq b) x)
        (chartBasisVecFiber (I := I) α c x) =
      (∑ l : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) a
              (fun y => chartChristoffel (I := I) g₁ α qq pp l y -
                chartChristoffel (I := I) g_bg α qq pp l y) (extChartAt I α x) +
            ∑ m : Fin (Module.finrank ℝ E),
              connDiffChartCoeff (I := I) g₁ g_bg α pp qq m x *
                chartChristoffel (I := I) g₁ α a m l (extChartAt I α x)) *
          chartGramMatrix (I := I) g₁ α x l c)
      - (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ α a pp m (extChartAt I α x) *
            ∑ l : Fin (Module.finrank ℝ E),
              connDiffChartCoeff (I := I) g₁ g_bg α m qq l x *
                chartGramMatrix (I := I) g₁ α x l c)
      - (∑ n : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ α a qq n (extChartAt I α x) *
            ∑ l : Fin (Module.finrank ℝ E),
              connDiffChartCoeff (I := I) g₁ g_bg α pp n l x *
                chartGramMatrix (I := I) g₁ α x l c) := by
  classical
  obtain ⟨Spp, Upp, hSpp_smooth, hUpp_open, hxUpp, hUpp_good, hSpp_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext_alpha (I := I) α pp hx
  obtain ⟨Sqq, Uqq, hSqq_smooth, hUqq_open, hxUqq, hUqq_good, hSqq_eq⟩ :=
    exists_globalSmooth_chartBasisVec_ext_alpha (I := I) α qq hx
  set U := Upp ∩ Uqq with hU_def
  have hU_open : IsOpen U := hUpp_open.inter hUqq_open
  have hxU : x ∈ U := ⟨hxUpp, hxUqq⟩
  have hU_good : U ⊆ chartLeviCivitaGoodSet (I := I) α := fun y hy => hUpp_good hy.1
  
  set cd : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun p y => connDiffChartCoeff (I := I) g₁ g_bg α pp qq p y with hcd_def
  set Sfield : Π b : M, TangentSpace I b :=
    fun b => connDiff (I := I) g₁ g_bg b (Spp b) (Sqq b) with hSfield_def
  have hSfield_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (Sfield b)) :=
    connDiff_contMDiff (I := I) g₁ g_bg hSpp_smooth hSqq_smooth
  have hSfield_eq : ∀ y ∈ U, Sfield y =
      ∑ p : Fin (Module.finrank ℝ E), cd p y • chartBasisVecFiber (I := I) α p y := by
    intro y hy
    have hygood : y ∈ chartLeviCivitaGoodSet (I := I) α := hU_good hy
    change connDiff (I := I) g₁ g_bg y (Spp y) (Sqq y) =
      ∑ p : Fin (Module.finrank ℝ E), cd p y • chartBasisVecFiber (I := I) α p y
    rw [hSpp_eq y hy.1, hSqq_eq y hy.2]
    rw [connDiff_chartBasis_pair_eq_sum (I := I) g₁ g_bg α hygood pp qq]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hcd_def]; rfl
  have hcd_diff : ∀ p : Fin (Module.finrank ℝ E),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (cd p) x :=
    fun p => connDiffChartCoeff_mdiff (I := I) g₁ g_bg α pp qq p hx
  
  have hterm1 :
      (LeviCivita (I := I) g₁).toFun Sfield x (chartBasisVecFiber (I := I) α a x) =
        ∑ l : Fin (Module.finrank ℝ E),
          (extDerivFun (I := I) (cd l) x (chartBasisVecFiber (I := I) α a x) +
            ∑ m : Fin (Module.finrank ℝ E),
              cd m x * chartChristoffel (I := I) g₁ α a m l (extChartAt I α x)) •
            chartBasisVecFiber (I := I) α l x :=
    covDeriv_chartCoordField_alpha (I := I) g₁ α a hx cd hcd_diff hSfield_smooth
      hU_open hxU hSfield_eq
  
  have hcovPP : (LeviCivita (I := I) g₁).toFun
        (fun b : M => chartBasisVecFiber (I := I) α pp b) x (chartBasisVecFiber (I := I) α a x) =
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₁ α a pp m (extChartAt I α x) •
          chartBasisVecFiber (I := I) α m x :=
    LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g₁ α a pp hx
  have hcovQQ : (LeviCivita (I := I) g₁).toFun
        (fun b : M => chartBasisVecFiber (I := I) α qq b) x (chartBasisVecFiber (I := I) α a x) =
      ∑ n : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₁ α a qq n (extChartAt I α x) •
          chartBasisVecFiber (I := I) α n x :=
    LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g₁ α a qq hx
  
  have hconnDiffChart : ∀ j k : Fin (Module.finrank ℝ E),
      connDiff (I := I) g₁ g_bg x
          (chartBasisVecFiber (I := I) α j x) (chartBasisVecFiber (I := I) α k x) =
        ∑ l : Fin (Module.finrank ℝ E),
          connDiffChartCoeff (I := I) g₁ g_bg α j k l x • chartBasisVecFiber (I := I) α l x := by
    intro j k
    rw [connDiff_chartBasis_pair_eq_sum (I := I) g₁ g_bg α hx j k]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [connDiffChartCoeff]
  
  
  have hfield_ev :
      (fun b : M => connDiff (I := I) g₁ g_bg b
        (chartBasisVecFiber (I := I) α pp b) (chartBasisVecFiber (I := I) α qq b)) =ᶠ[𝓝 x]
        (fun b : M => Sfield b) := by
    filter_upwards [hU_open.mem_nhds hxU] with b hb
    change connDiff (I := I) g₁ g_bg b
        (chartBasisVecFiber (I := I) α pp b) (chartBasisVecFiber (I := I) α qq b) = Sfield b
    rw [hSfield_def]
    change connDiff (I := I) g₁ g_bg b
        (chartBasisVecFiber (I := I) α pp b) (chartBasisVecFiber (I := I) α qq b) =
      connDiff (I := I) g₁ g_bg b (Spp b) (Sqq b)
    rw [hSpp_eq b hb.1, hSqq_eq b hb.2]
  have hfield_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (connDiff (I := I) g₁ g_bg b
          (chartBasisVecFiber (I := I) α pp b) (chartBasisVecFiber (I := I) α qq b))) x :=
    connDiff_pairing_mdiffAt (I := I) g₁ g_bg
      (chartBasisVec_alpha_mdifferentiableAt (I := I) α pp hx)
      (chartBasisVec_alpha_mdifferentiableAt (I := I) α qq hx)
  have hSfield_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (Sfield b)) x :=
    (hSfield_smooth x).mdifferentiableAt (by simp)
  
  rw [deTurckLieCovDerivA]
  
  rw [hcovPP, hcovQQ]
  rw [(LeviCivita (I := I) g₁).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hfield_diff hSfield_diff Filter.univ_mem hfield_ev]
  rw [hterm1]
  
  rw [show connDiff (I := I) g₁ g_bg x
        (∑ m : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ α a pp m (extChartAt I α x) •
            chartBasisVecFiber (I := I) α m x)
        (chartBasisVecFiber (I := I) α qq x) =
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₁ α a pp m (extChartAt I α x) •
          connDiff (I := I) g₁ g_bg x (chartBasisVecFiber (I := I) α m x)
            (chartBasisVecFiber (I := I) α qq x) from by
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.smul_apply]]
  rw [show connDiff (I := I) g₁ g_bg x (chartBasisVecFiber (I := I) α pp x)
        (∑ n : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g₁ α a qq n (extChartAt I α x) •
            chartBasisVecFiber (I := I) α n x) =
      ∑ n : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g₁ α a qq n (extChartAt I α x) •
          connDiff (I := I) g₁ g_bg x (chartBasisVecFiber (I := I) α pp x)
            (chartBasisVecFiber (I := I) α n x) from by
    rw [map_sum]; simp only [map_smul]]
  
  rw [map_sub, map_sub]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  congr 1
  · congr 1
    · rw [map_sum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [chartGramMatrix_apply g₁ α x l c]
      congr 2
      rw [show cd l = connDiffChartCoeff (I := I) g₁ g_bg α pp qq l from rfl]
      rw [connDiffChartCoeff_extDerivFun (I := I) g₁ g_bg α a pp qq l hx]
    · rw [map_sum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hconnDiffChart m qq]
      rw [map_sum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul,
        ContinuousLinearMap.smul_apply, smul_eq_mul, chartGramMatrix_apply]
  · rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hconnDiffChart pp n]
    rw [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, chartGramMatrix_apply]

open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem dLaBiContrFib_toModel_chartα_eq [BoundarylessManifold I M]
    (g₁ g_bg : SmoothRiemannianMetric I M) (α : M) (σ : Fin 2 → Fin (Module.finrank ℝ E))
    {w : M} (hx : w ∈ (chartAt H α).source)
    (Dw : Tensor0SBundle.Tensor0SSpace 2 I w) :
    Tensor0SBundle.Tensor0SSpace.toModel (dLaBiContrFib (I := I) g₁ g_bg w Dw)
        (fun i => chartBasisVecFiber (I := I) α (σ i) w) =
      (-1 : ℝ) * ∑ m, ∑ n, chartInvGramMatrix (I := I) g₁ α w m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g₁ α w k l *
          ((g₁.inner w
              (dLaCovKernel (I := I) g₁ g_bg w
                (chartBasisVecFiber (I := I) α (σ 0) w) (chartBasisVecFiber (I := I) α m w)
                (chartBasisVecFiber (I := I) α k w))
              (chartBasisVecFiber (I := I) α (σ 1) w) +
            g₁.inner w
              (dLaCovKernel (I := I) g₁ g_bg w
                (chartBasisVecFiber (I := I) α (σ 1) w) (chartBasisVecFiber (I := I) α m w)
                (chartBasisVecFiber (I := I) α k w))
              (chartBasisVecFiber (I := I) α (σ 0) w)) *
            Tensor0SBundle.Tensor0SSpace.toModel Dw
              ![chartBasisVecFiber (I := I) α n w, chartBasisVecFiber (I := I) α l w])) := by
  classical
  have hxbase : w ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
      TangentBundle.trivializationAt_baseSet (I := I) α]
    exact hx
  have hxsrc : w ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  rw [dLaBiContrFib, dLaBiContrFibFixedFrame_toModel]
  set v0 := chartBasisVecFiber (I := I) α (σ 0) w with hv0
  set v1 := chartBasisVecFiber (I := I) α (σ 1) w with hv1
  
  have hrewrite : (∑ a, ∑ b,
        (g₁.inner w (dLaCovKernel (I := I) g₁ g_bg w v0
            (smoothOrthoFrame (I := I) g₁ w a w) (smoothOrthoFrame (I := I) g₁ w b w)) v1 +
          g₁.inner w (dLaCovKernel (I := I) g₁ g_bg w v1
            (smoothOrthoFrame (I := I) g₁ w a w) (smoothOrthoFrame (I := I) g₁ w b w)) v0) *
          Tensor0SBundle.Tensor0SSpace.toModel Dw
            ![(smoothOrthoFrame (I := I) g₁ w a w : E), (smoothOrthoFrame (I := I) g₁ w b w : E)]) =
      ∑ a, ∑ b,
        frameDLaKernel (I := I) g₁ g_bg w v0 v1
            (smoothOrthoFrame (I := I) g₁ w a w) (smoothOrthoFrame (I := I) g₁ w b w) *
          (bilinFormToModel (TangentSpace I w)).symm (Tensor0SBundle.Tensor0SSpace.toModel Dw)
            (smoothOrthoFrame (I := I) g₁ w a w) (smoothOrthoFrame (I := I) g₁ w b w) := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [frameDLaKernel_apply]
    congr 1
    rw [bilinFormToModel_symm_apply (TangentSpace I w) (Tensor0SBundle.Tensor0SSpace.toModel Dw)
      (smoothOrthoFrame (I := I) g₁ w a w) (smoothOrthoFrame (I := I) g₁ w b w)]
    rfl
  rw [hrewrite]
  refine congrArg (fun t => (-1 : ℝ) * t) ?_
  rw [off_double_frame_bilin_trace_eq_chartAlpha (I := I) g₁ α hxbase hxsrc
      (frameDLaKernel (I := I) g₁ g_bg w v0 v1)
      ((bilinFormToModel (TangentSpace I w)).symm (Tensor0SBundle.Tensor0SSpace.toModel Dw))
      (fun a => smoothOrthoFrame (I := I) g₁ w a w)
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ w i j)]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  congr 1
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  congr 1
  rw [frameDLaKernel_apply]
  congr 1
  rw [bilinFormToModel_symm_apply (TangentSpace I w) (Tensor0SBundle.Tensor0SSpace.toModel Dw)
    (chartBasisVecFiber (I := I) α n w) (chartBasisVecFiber (I := I) α l w)]
  rfl

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem connDiffChartCoeff_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (j k p : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun w : M × ℝ => connDiffChartCoeff (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α j k p w.1)
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have h := (realizedFam_chartChristoffel_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α k j p).sub
    (chartChristoffel_fixed_jointContMDiffOn (I := I)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) g_bg α k j p)
  refine h.congr (fun w _ => ?_)
  rw [connDiffChartCoeff]

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem dLaKernelChartα_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (a c pp qq : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun w : M × ℝ =>
        (realizedFam (I := I) g₀ T T' hδ hδ' w.2).inner w.1
          (deTurckLieCovDerivA (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg
            (fun b : M => chartBasisVecFiber (I := I) α a b)
            (fun b : M => chartBasisVecFiber (I := I) α pp b)
            (fun b : M => chartBasisVecFiber (I := I) α qq b) w.1)
          (chartBasisVecFiber (I := I) α c w.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  set Sset := realizedSmallSet (δ := δ) (δ' := δ') with hSset
  
  have hΓ : ∀ i j l : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun w : M × ℝ => chartChristoffel (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α i j l (extChartAt I α w.1))
        ((chartAt H α).source ×ˢ Sset) :=
    fun i j l => realizedFam_chartChristoffel_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α i j l
  have hGram : ∀ l : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun w : M × ℝ => chartGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α w.1 l c)
        ((chartAt H α).source ×ˢ Sset) :=
    fun l => realizedFam_chartGramMatrix_jointContMDiffOn_free (I := I) g₀ T T' hδ hδ' α l c
  have hcd : ∀ j k pidx : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun w : M × ℝ => connDiffChartCoeff (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α j k pidx w.1)
        ((chartAt H α).source ×ˢ Sset) :=
    fun j k pidx => connDiffChartCoeff_realizedFam_jointContMDiffOn (I := I) g₀ g_bg T T' hδ hδ'
      α j k pidx
  have hpΓdiff : ∀ l : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun w : M × ℝ => partialDeriv (E := E) a
          (fun y => chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α qq pp l y -
            chartChristoffel (I := I) g_bg α qq pp l y) (extChartAt I α w.1))
        ((chartAt H α).source ×ˢ Sset) := by
    intro l
    have hsub := (realizedFam_partial_chartChristoffel_jointContMDiffOn (I := I)
        g₀ T T' hδ hδ' α a qq pp l).sub
      (partial_chartChristoffel_fixed_jointContMDiffOn (I := I)
        (S := Sset) g_bg α a qq pp l)
    refine hsub.congr (fun w hw => ?_)
    have hwgood : w.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
      exact hw.1
    have hu : DifferentiableAt ℝ
        (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α qq pp l)
        (extChartAt I α w.1) :=
      (chartChristoffel_contDiffAt_alpha (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α qq pp l hwgood).differentiableAt (by simp)
    have hv : DifferentiableAt ℝ (chartChristoffel (I := I) g_bg α qq pp l) (extChartAt I α w.1) :=
      (chartChristoffel_contDiffAt_alpha (I := I) g_bg α qq pp l hwgood).differentiableAt (by simp)
    exact partialDeriv_sub (E := E) (i := a)
      (chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α qq pp l)
      (chartChristoffel (I := I) g_bg α qq pp l) hu hv
  
  have hbody : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun w : M × ℝ =>
        (∑ l : Fin (Module.finrank ℝ E),
            (partialDeriv (E := E) a
                (fun y => chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α qq pp l y -
                  chartChristoffel (I := I) g_bg α qq pp l y) (extChartAt I α w.1) +
              ∑ m : Fin (Module.finrank ℝ E),
                connDiffChartCoeff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α pp qq m w.1 *
                  chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α a m l
                    (extChartAt I α w.1)) *
            chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α w.1 l c)
        - (∑ m : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α a pp m
                (extChartAt I α w.1) *
              ∑ l : Fin (Module.finrank ℝ E),
                connDiffChartCoeff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α m qq l w.1 *
                  chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α w.1 l c)
        - (∑ n : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α a qq n
                (extChartAt I α w.1) *
              ∑ l : Fin (Module.finrank ℝ E),
                connDiffChartCoeff (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α pp n l w.1 *
                  chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α w.1 l c))
      ((chartAt H α).source ×ˢ Sset) := by
    refine ((contMDiffOn_finset_sum (fun l _ => ?_)).sub
      (contMDiffOn_finset_sum (fun m _ => ?_))).sub (contMDiffOn_finset_sum (fun n _ => ?_))
    · exact ((hpΓdiff l).add (contMDiffOn_finset_sum
        (fun m _ => (hcd pp qq m).mul (hΓ a m l)))).mul (hGram l)
    · exact (hΓ a pp m).mul (contMDiffOn_finset_sum (fun l _ => (hcd m qq l).mul (hGram l)))
    · exact (hΓ a qq n).mul (contMDiffOn_finset_sum (fun l _ => (hcd pp n l).mul (hGram l)))
  refine hbody.congr (fun w hw => ?_)
  have hwgood : w.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hw.1
  exact dLaCovDerivA_chartBasis_inner_eq (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α a c pp qq hwgood

open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private lemma chartDeTurckVFComp_contDiffAt_alpha [I.Boundaryless]
    (g g_bg : SmoothRiemannianMetric I M) (α : M) (p : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞ (chartDeTurckVFComp (I := I) g g_bg α p) (extChartAt I α x) := by
  have hy : extChartAt I α x ∈ interior (extChartAt I α).target := by
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source]
      exact chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  exact (chartDeTurckVFComp_contDiffOn_interior (I := I) g g_bg α p).contDiffAt
    (isOpen_interior.mem_nhds hy)

open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem deTurckLieWEndo_chartBasis_inner_eq [I.Boundaryless]
    (g₁ g_bg : SmoothRiemannianMetric I M) (α : M) (a c : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    g₁.inner x
        (deTurckLieWEndo (I := I) g₁ g_bg x (chartBasisVecFiber (I := I) α a x))
        (chartBasisVecFiber (I := I) α c x) =
      ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) a (fun y => chartDeTurckVFComp (I := I) g₁ g_bg α l y)
            (extChartAt I α x) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartDeTurckVFComp (I := I) g₁ g_bg α m (extChartAt I α x) *
              chartChristoffel (I := I) g₁ α a m l (extChartAt I α x)) *
          chartGramMatrix (I := I) g₁ α x l c := by
  classical
  set cd : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun p y => chartDeTurckVFComp (I := I) g₁ g_bg α p (extChartAt I α y) with hcd_def
  set Sfield : Π b : M, TangentSpace I b :=
    fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg : Π b : M, TangentSpace I b) b with hSfield_def
  have hSfield_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (Sfield b)) :=
    (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff
  have hSfield_eq : ∀ y ∈ chartLeviCivitaGoodSet (I := I) α, Sfield y =
      ∑ p : Fin (Module.finrank ℝ E), cd p y • chartBasisVecFiber (I := I) α p y := by
    intro y hy
    rw [hSfield_def]
    exact deTurckVF_apply_eq_chartDeTurckVFComp_sum (I := I) g₁ g_bg α hy
  have hcd_diff : ∀ p : Fin (Module.finrank ℝ E),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (cd p) x := by
    intro p
    have hxchart : x ∈ (chartAt H α).source :=
      chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
    have hgE_d : DifferentiableAt ℝ (chartDeTurckVFComp (I := I) g₁ g_bg α p) (extChartAt I α x) :=
      (chartDeTurckVFComp_contDiffAt_alpha (I := I) g₁ g_bg α p hx).differentiableAt (by simp)
    have hgE_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
        (chartDeTurckVFComp (I := I) g₁ g_bg α p) (extChartAt I α x) := by
      rw [mdifferentiableAt_iff_differentiableAt]; exact hgE_d
    have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
      mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
    exact hgE_mdiff.comp x hphi_mdiff
  
  have hexpand :
      (LeviCivita (I := I) g₁).toFun Sfield x (chartBasisVecFiber (I := I) α a x) =
        ∑ l : Fin (Module.finrank ℝ E),
          (extDerivFun (I := I) (cd l) x (chartBasisVecFiber (I := I) α a x) +
            ∑ m : Fin (Module.finrank ℝ E),
              cd m x * chartChristoffel (I := I) g₁ α a m l (extChartAt I α x)) •
            chartBasisVecFiber (I := I) α l x :=
    covDeriv_chartCoordField_alpha (I := I) g₁ α a hx cd hcd_diff hSfield_smooth
      (chartLeviCivitaGoodSet_isOpen (I := I) α) hx (fun y hy => hSfield_eq y hy)
  
  have hendo : deTurckLieWEndo (I := I) g₁ g_bg x (chartBasisVecFiber (I := I) α a x) =
      (LeviCivita (I := I) g₁).toFun Sfield x (chartBasisVecFiber (I := I) α a x) := by
    rw [deTurckLieWEndo, hSfield_def]
  rw [hendo, hexpand]
  
  rw [map_sum]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [chartGramMatrix_apply g₁ α x l c]
  congr 2
  · rw [hcd_def]
    have hgE_cda : ContDiffAt ℝ ∞ (chartDeTurckVFComp (I := I) g₁ g_bg α l) (extChartAt I α x) :=
      chartDeTurckVFComp_contDiffAt_alpha (I := I) g₁ g_bg α l hx
    exact extDerivFun_comp_extChartAt_apply_basis_alpha (I := I) α hx hgE_cda a

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.DivergenceTheorem in

theorem realizedFam_chartDeTurckVFComp_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun w : M × ℝ => chartDeTurckVFComp (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α k (extChartAt I α w.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun w : M × ℝ => (w.2, extChartAt I α w.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun w hw => hw.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_chartDeTurckVFComp
    (gfam := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s) α hG g_bg k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => chartDeTurckVFComp (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg α k r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun w : M × ℝ => (w.2, extChartAt I α w.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr (fun q _ => rfl) rfl

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.DivergenceTheorem in

theorem realizedFam_partial_chartDeTurckVFComp_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (m k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun w : M × ℝ => partialDeriv (E := E) m
        (fun y => chartDeTurckVFComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α k y) (extChartAt I α w.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hG := realizedFam_genJointGram_free (I := I) g₀ T T' hδ hδ' α
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun w : M × ℝ => (w.2, extChartAt I α w.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine ContMDiffOn.prodMk contMDiffOn_snd ?_
    exact (contMDiffOn_extChartAt (I := I) (x := α)).comp contMDiffOn_fst (fun w hw => hw.1)
  intro p hp
  obtain ⟨hx, hs⟩ := hp
  have hxsrc : p.1 ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
  have hy : extChartAt I α p.1 ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hentry := gen_joint_partial_chartDeTurckVFComp
    (gfam := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s) α hG g_bg m k hs hy
  have hentryM : ContMDiffAt (𝓘(ℝ, ℝ × E)) 𝓘(ℝ) ∞
      (fun r : ℝ × E => partialDeriv (E := E) m
        (fun y => chartDeTurckVFComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' r.1) g_bg α k y) r.2) (p.2, extChartAt I α p.1) :=
    hentry.contMDiffAt
  have hmoveAt : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × E)) ∞
      (fun w : M × ℝ => (w.2, extChartAt I α w.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) p := by
    have hm := hmove p ⟨hx, hs⟩
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm
  exact (hentryM.comp_contMDiffWithinAt p hmoveAt).congr (fun q _ => rfl) rfl

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem deTurckLieWEndoChartα_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (a c : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun w : M × ℝ =>
        (realizedFam (I := I) g₀ T T' hδ hδ' w.2).inner w.1
          (deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg w.1
            (chartBasisVecFiber (I := I) α a w.1))
          (chartBasisVecFiber (I := I) α c w.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  set Sset := realizedSmallSet (δ := δ) (δ' := δ') with hSset
  have hΓ : ∀ i j l : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun w : M × ℝ => chartChristoffel (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α i j l (extChartAt I α w.1))
        ((chartAt H α).source ×ˢ Sset) :=
    fun i j l => realizedFam_chartChristoffel_jointContMDiffOn (I := I) g₀ T T' hδ hδ' α i j l
  have hGram : ∀ l : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun w : M × ℝ => chartGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α w.1 l c)
        ((chartAt H α).source ×ˢ Sset) :=
    fun l => realizedFam_chartGramMatrix_jointContMDiffOn_free (I := I) g₀ T T' hδ hδ' α l c
  have hW : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun w : M × ℝ => chartDeTurckVFComp (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α k (extChartAt I α w.1))
        ((chartAt H α).source ×ˢ Sset) :=
    fun k => realizedFam_chartDeTurckVFComp_jointContMDiffOn (I := I) g₀ g_bg T T' hδ hδ' α k
  have hpW : ∀ l : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun w : M × ℝ => partialDeriv (E := E) a
          (fun y => chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α l y) (extChartAt I α w.1))
        ((chartAt H α).source ×ˢ Sset) :=
    fun l => realizedFam_partial_chartDeTurckVFComp_jointContMDiffOn (I := I) g₀ g_bg T T' hδ hδ' α a l
  have hbody : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun w : M × ℝ => ∑ l : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) a (fun y => chartDeTurckVFComp (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α l y) (extChartAt I α w.1) +
          ∑ m : Fin (Module.finrank ℝ E),
            chartDeTurckVFComp (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α m
                (extChartAt I α w.1) *
              chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α a m l
                (extChartAt I α w.1)) *
          chartGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' w.2) α w.1 l c)
      ((chartAt H α).source ×ˢ Sset) :=
    contMDiffOn_finset_sum (fun l _ =>
      ((hpW l).add (contMDiffOn_finset_sum (fun m _ => (hW m).mul (hΓ a m l)))).mul (hGram l))
  refine hbody.congr (fun w hw => ?_)
  have hwgood : w.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
    exact hw.1
  exact deTurckLieWEndo_chartBasis_inner_eq (I := I)
    (realizedFam (I := I) g₀ T T' hδ hδ' w.2) g_bg α a c hwgood

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem deTurckLieWEndoSection_chartComponent_realizedFam_jointContMDiffOn
    [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (Y : Cₛ^∞⟮I; E, (fun x : M => TangentSpace I x)⟯)
    (α : M) (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
        (deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1 (Y p.1))
        (chartBasisVecFiber (I := I) α j p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) α
  have hsum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ q : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) α Y q p.1 *
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
            (deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
              (chartBasisVecFiber (I := I) α q p.1))
            (chartBasisVecFiber (I := I) α j p.1))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    refine contMDiffOn_finset_sum (fun q _ => ?_)
    have hcoeff : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartCoeff (I := I) α Y q p.1)
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
      have hc := chartCoeff_contMDiffOn (I := I) α Y q
      rw [hbase_eq] at hc
      exact hc.comp contMDiffOn_fst (fun p hp => hp.1)
    exact hcoeff.mul
      (deTurckLieWEndoChartα_realizedFam_jointContMDiffOn (I := I) g₀ g_bg T T' hδ hδ' α q j)
  refine hsum.congr (fun p hp => ?_)
  obtain ⟨hx, _hs⟩ := hp
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [hbase_eq]; exact hx
  set gs := realizedFam (I := I) g₀ T T' hδ hδ' p.2 with hgs
  rw [chartCoeff_recompose (I := I) α Y hxbase]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Integral.Connection in
open DifferentialGeometry.Integral.DivergenceTheorem in

private theorem deTurckLieWEndo_realizedFam_jointContMDiffOn [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) p.1
        (deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun p : M × ℝ => deTurckLieWEndo (I := I)
      (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  
  set cv : ℝ → Π b : M, TangentSpace I b →ₗ[ℝ] ℝ :=
    fun s b => ((realizedFam (I := I) g₀ T T' hδ hδ' s).inner b
      (deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg b (Y b))).toLinearMap
    with hcvdef
  have hinv : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    fun α i j => realizedFam_chartInvGramMatrix_jointContMDiffOn_free
      (I := I) g₀ T T' hδ hδ' α i j
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => cv p.2 p.1 (chartBasisVecFiber (I := I) α j p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
    intro α j
    have hbase := deTurckLieWEndoSection_chartComponent_realizedFam_jointContMDiffOn
      (I := I) g₀ g_bg T T' hδ hδ' Y α j
    refine hbase.congr (fun p _ => ?_)
    rw [hcvdef]
    rfl
  have hjoint := metricSharp_jointContMDiffOn (I := I)
    (gfam := fun s => realizedFam (I := I) g₀ T T' hδ hδ' s) (cv := cv)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) realizedSmallSet_isOpen hinv hcv
  refine hjoint.congr (fun p _ => ?_)
  
  refine congrArg (TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1) ?_
  set gs := realizedFam (I := I) g₀ T T' hδ hδ' p.2 with hgs
  set v := deTurckLieWEndo (I := I) gs g_bg p.1 (Y p.1) with hv
  change v = metricSharp (I := I) gs p.1 (cv p.2 p.1)
  rw [hcvdef]
  have hflat : metricSharp (I := I) gs p.1 ((gs.inner p.1 v).toLinearMap) = v := by
    have heq : (gs.inner p.1 v).toLinearMap = metricFlatMap (I := I) gs p.1 v := by
      apply LinearMap.ext; intro w; rw [metricFlatMap_apply]; rfl
    rw [heq, metricSharp]
    exact (metricFlatMap (I := I) gs p.1).symm_apply_apply v
  exact hflat.symm

set_option linter.unusedSectionVars false in

private theorem dLaBiContrFib_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (dLaBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun p : M × ℝ => dLaBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  have hbridge := contMDiffOn_bilinSection_of_jointChartScalar (I := I) (M := M)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (Hb := fun p : M × ℝ => (bilinFormToModel (TangentSpace I p.1)).symm
      (Tensor0SBundle.Tensor0SSpace.toModel
        (dLaBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1 (Y p.1))))
    (by
      intro α σ
      rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
        TangentBundle.trivializationAt_baseSet (I := I) α]
      set kern : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → M × ℝ → ℝ :=
        fun m k p =>
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
              (deTurckLieCovDerivA (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg
                (fun b : M => chartBasisVecFiber (I := I) α (σ 0) b)
                (fun b : M => chartBasisVecFiber (I := I) α m b)
                (fun b : M => chartBasisVecFiber (I := I) α k b) p.1)
              (chartBasisVecFiber (I := I) α (σ 1) p.1) +
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2).inner p.1
              (deTurckLieCovDerivA (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg
                (fun b : M => chartBasisVecFiber (I := I) α (σ 1) b)
                (fun b : M => chartBasisVecFiber (I := I) α m b)
                (fun b : M => chartBasisVecFiber (I := I) α k b) p.1)
              (chartBasisVecFiber (I := I) α (σ 0) p.1) with hkern
      have hsum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
          (fun p : M × ℝ => (-1 : ℝ) * ∑ m, ∑ n,
              chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m n *
              (∑ k, ∑ l,
                chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
                (kern m k p *
                  Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
                    ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1])))
          ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
        have hYcomp : ∀ n l : Fin (Module.finrank ℝ E),
            ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
              ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1])
            ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
          intro n l
          have h := realizedFam_YchartComponent_jointContMDiffOn (I := I)
            (S := realizedSmallSet (δ := δ) (δ' := δ')) α Y n l
          rwa [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
            TangentBundle.trivializationAt_baseSet (I := I) α] at h
        have hInvGram : ∀ i j : Fin (Module.finrank ℝ E),
            ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun p : M × ℝ =>
              chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 i j)
            ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := fun i j =>
          realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T T' hδ hδ' α i j
        have hkernel : ∀ m k : Fin (Module.finrank ℝ E),
            ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => kern m k p)
            ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := fun m k =>
          (dLaKernelChartα_realizedFam_jointContMDiffOn (I := I) g₀ g_bg T T' hδ hδ'
              α (σ 0) (σ 1) m k).add
            (dLaKernelChartα_realizedFam_jointContMDiffOn (I := I) g₀ g_bg T T' hδ hδ'
              α (σ 1) (σ 0) m k)
        have hinner : ∀ m n k l : Fin (Module.finrank ℝ E),
            ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun p : M × ℝ =>
              chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
                (kern m k p *
                  Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
                    ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1]))
            ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := fun m n k l =>
          (hInvGram k l).mul ((hkernel m k).mul (hYcomp n l))
        have hmiddle : ∀ m n : Fin (Module.finrank ℝ E),
            ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun p : M × ℝ =>
              chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m n *
              (∑ k, ∑ l,
                chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
                (kern m k p *
                  Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
                    ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1])))
            ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := fun m n =>
          (hInvGram m n).mul (contMDiffOn_finset_sum (fun k _ =>
            contMDiffOn_finset_sum (fun l _ => hinner m n k l)))
        have hbody : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (fun p : M × ℝ => ∑ m, ∑ n,
              chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 m n *
              (∑ k, ∑ l,
                chartInvGramMatrix (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) α p.1 k l *
                (kern m k p *
                  Tensor0SBundle.Tensor0SSpace.toModel (Y p.1)
                    ![chartBasisVecFiber (I := I) α n p.1, chartBasisVecFiber (I := I) α l p.1])))
            ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
          contMDiffOn_finset_sum (fun m _ => contMDiffOn_finset_sum (fun n _ => hmiddle m n))
        exact contMDiffOn_const.mul hbody
      refine hsum.congr (fun p hp => ?_)
      rw [bilinFormToModel_symm_apply (TangentSpace I p.1)
        (Tensor0SBundle.Tensor0SSpace.toModel
          (dLaBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1 (Y p.1)))]
      have hpsrc : p.1 ∈ (chartAt H α).source := by
        rw [← TangentBundle.trivializationAt_baseSet (I := I) α]; exact hp.1
      have hgoodp : p.1 ∈ chartLeviCivitaGoodSet (I := I) α := by
        rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α, extChartAt_source (I := I)]
        exact hpsrc
      have hfld : ∀ (a m k : Fin (Module.finrank ℝ E)),
          dLaCovKernel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
              (chartBasisVecFiber (I := I) α a p.1) (chartBasisVecFiber (I := I) α m p.1)
              (chartBasisVecFiber (I := I) α k p.1) =
            deTurckLieCovDerivA (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg
              (fun b : M => chartBasisVecFiber (I := I) α a b)
              (fun b : M => chartBasisVecFiber (I := I) α m b)
              (fun b : M => chartBasisVecFiber (I := I) α k b) p.1 := by
        intro a m k
        exact dLaCovKernel_apply_field3 (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1
          (fun b : M => chartBasisVecFiber (I := I) α a b)
          (fun b : M => chartBasisVecFiber (I := I) α m b)
          (fun b : M => chartBasisVecFiber (I := I) α k b)
          (chartBasisVec_alpha_mdifferentiableAt (I := I) α a hgoodp)
          (chartBasisVec_alpha_mdifferentiableAt (I := I) α m hgoodp)
          (chartBasisVec_alpha_mdifferentiableAt (I := I) α k hgoodp)
      rw [show (![chartBasisVecFiber (I := I) α (σ 0) p.1,
            chartBasisVecFiber (I := I) α (σ 1) p.1] : Fin 2 → TangentSpace I p.1) =
          (fun i => chartBasisVecFiber (I := I) α (σ i) p.1) from by
        funext i; fin_cases i <;> rfl]
      have hread := dLaBiContrFib_toModel_chartα_eq (I := I)
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg α σ hpsrc (Y p.1)
      refine hread.trans ?_
      rw [hkern]
      simp only
      refine congrArg (fun t => (-1 : ℝ) * t) ?_
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
      congr 1
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      congr 1
      congr 1
      rw [hfld (σ 0) m k, hfld (σ 1) m k])
  refine hbridge.congr (fun p _ => ?_)
  congr 1
  rw [LinearEquiv.apply_symm_apply, Tensor0SBundle.Tensor0SSpace.ofModel_toModel]

set_option linter.unusedSectionVars false in

private theorem deTurckLieDLbFib_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        (Tensor0SBundle.TensorRSSpace.ofCLM
          (deTurckLieDLbFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun p : M × ℝ => deTurckLieDLbFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
  intro Y
  set Λ : ∀ p : M × ℝ, TangentSpace I p.1 →L[ℝ] TangentSpace I p.1 :=
    fun p => deTurckLieWEndo (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1 with hΛ
  have hΛjoint := deTurckLieWEndo_realizedFam_jointContMDiffOn (I := I) g₀ g_bg T T' hδ hδ'
  have hAjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have h0 := slotInsertEndo0Field_apply_jointContMDiffOn (I := I) (M := M) (d := 1)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) Λ hΛjoint (fun p => Y p.1) hAjoint
  have h1 := slotInsertEndo1Field_apply_jointContMDiffOn (I := I) (M := M) (d := 0)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (realizedFam (I := I) g₀ T T' hδ hδ' 0) Λ hΛjoint (fun p => Y p.1) hAjoint
  have hsum := jointS0add (I := I) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (A := fun p : M × ℝ => slotInsertEndoFib (I := I) (M := M) 2 0 p.1 (Λ p) (Y p.1))
    (B := fun p : M × ℝ => slotInsertEndoFib (I := I) (M := M) 2 1 p.1 (Λ p) (Y p.1)) h0 h1
  refine hsum.congr (fun p _ => ?_)
  rfl

set_option linter.unusedSectionVars false in

theorem ricciArmOrder0DeTurckLieCoeff_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((ricciArmOrder0DeTurckLieCoeff (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  have hsum := jointRSadd (I := I) (r := 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (A := fun p : M × ℝ => Tensor0SBundle.TensorRSSpace.ofCLM
      (dLaBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
    (B := fun p : M × ℝ => Tensor0SBundle.TensorRSSpace.ofCLM
      (deTurckLieDLbFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1))
    (dLaBiContrFib_realizedFam_jointContMDiff (I := I) g₀ g_bg T T' hδ hδ')
    (deTurckLieDLbFib_realizedFam_jointContMDiff (I := I) g₀ g_bg T T' hδ hδ')
  refine hsum.congr (fun p _ => ?_)
  rw [ricciArmOrder0DeTurckLieCoeff_toSection]
  refine congrArg (TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1) ?_
  change Tensor0SBundle.TensorRSSpace.ofCLM
      (deTurckLieFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1) =
    Tensor0SBundle.TensorRSSpace.ofCLM
        (dLaBiContrFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1) +
      Tensor0SBundle.TensorRSSpace.ofCLM
        (deTurckLieDLbFib (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg p.1)
  rw [deTurckLieFib]
  rfl

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0DeTurckLieCoeff_realizedFam_jointContMDiff [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
        ((symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg (T - T')).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) := by
  classical
  set σ' : Equiv.Perm (Fin (2 + 0)) :=
    Classical.choose (exists_iteratedCovGrad_unitModel_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) (T - T') 0) with hσ'
  set R : ℝ → SmoothCcTensor g₀ (2 + 0) 2 := fun s =>
    ricciArmOrder0DeTurckLieCoeff (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg with hR
  have hbare := ricciArmOrder0DeTurckLieCoeff_realizedFam_jointContMDiff (I := I) g₀ g_bg T T' hδ hδ'
  have hReind := reindexCoeffGen_jointContMDiffOn (I := I) (M := M) (r := 2 + 0)
    (S := realizedSmallSet (δ := δ) (δ' := δ')) g₀ R σ' hbare
  have hsum := jointRSadd (I := I) (r := 2 + 0) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (A := fun p : M × ℝ => (1 / 2 : ℝ) • (R p.2).toSection p.1)
    (B := fun p : M × ℝ =>
      (1 / 2 : ℝ) • (reindexCoeffGen (I := I) (M := M) g₀ (2 + 0) 2 (R p.2) σ').toSection p.1)
    (jointRSsmul (I := I) (r := 2 + 0) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
      (fun p : M × ℝ => (R p.2).toSection p.1) hbare)
    (jointRSsmul (I := I) (r := 2 + 0) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) (1 / 2 : ℝ)
      (fun p : M × ℝ => (reindexCoeffGen (I := I) (M := M) g₀ (2 + 0) 2 (R p.2) σ').toSection p.1)
      hReind)
  refine hsum.congr (fun p _ => ?_)
  rfl

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0RiemannCoeff_realizedFam_toModel_continuous [BoundarylessManifold I M]
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t) (T - T')).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := symmAbsorbedOrder0RiemannCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2
    (fun t => symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' t) (T - T')) (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x

set_option linter.unusedSectionVars false in

theorem symmAbsorbedOrder0DeTurckLieCoeff_realizedFam_toModel_continuous [BoundarylessManifold I M]
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg (T - T')).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) := by
  have hjoint := symmAbsorbedOrder0DeTurckLieCoeff_realizedFam_jointContMDiff (I := I) g₀ g_bg T T' hδ hδ'
  exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2
    (fun t => symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' t) g_bg (T - T')) (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x

theorem exists_pathIntegralCoeffField
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) (W : SmoothCcTensor g₀ 0 r)
    (S : Set ℝ) (hS : IsOpen S) (hSI : Set.uIcc (0:ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 ((Φ p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S))
    (hcont : ∀ x : M, ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x)) S) :
    ∃ IΦ : SmoothCcTensor g₀ r 2,
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 IΦ W) x v =
          ∫ s in (0 : ℝ)..1,
            unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ r 2 (Φ s) W) x v := by
  
  refine ⟨pathIntegralCoeffField (I := I) (M := M) g₀ r 2 Φ S hS hSI hjoint, fun x v => ?_⟩
  
  exact pathIntegralCoeffField_appCc_eq (I := I) (M := M) g₀ r 2 Φ W S hS hSI hjoint hcont x v

private theorem deriv_realizedDeTurckRicciChartSum_eq_rebased_chartSymbol
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) (x : M) (v w : TangentSpace I x) :
    ∃ h : ChartMetricPerturbation E,
      IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h ∧
        deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s =
          ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
              (((-2 : ℝ) * chartRicciSecondOrderPart (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                  chartDeTurckCorrSecondOrderPart (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x)) +
                metricFamilyDeTurckRicciFirstOrderRemainder (I := I)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x)) := by
  classical
  obtain ⟨h, gfam, hfam, hvel, _hlocRic, hloc⟩ :=
    exists_rebased_cutoffMetricPerturbationFamily (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' hs x
  refine ⟨h, hvel, ?_⟩
  set gs : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g₀ T T' hδ hδ' s with hgs
  set y₀ : E := extChartAt I x x with hy₀
  have hy : y₀ ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  set Pval : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => ((-2 : ℝ) * chartRicciSecondOrderPart (I := I) gs x h i k y₀ +
        chartDeTurckCorrSecondOrderPart (I := I) gs g_bg x h i k y₀) +
      metricFamilyDeTurckRicciFirstOrderRemainder (I := I) gs g_bg x h i k y₀ with hPval
  have hper : ∀ i k : Fin (Module.finrank ℝ E),
      HasDerivAt (fun t : ℝ => chartFComponentOnE (I := I)
          (deTurckRicciRHS (I := I) g_bg)
          (realizedFam (I := I) g₀ T T' hδ hδ' t) x i k y₀)
        (Pval i k) s := by
    intro i k
    have hsplit : HasDerivAt
        (fun σ : ℝ => chartFComponentOnE (I := I) (deTurckRicciRHS (I := I) g_bg) (gfam σ) x i k y₀)
        (Pval i k) 0 := by
      rw [hPval, hgs]
      exact hasDerivAt_chartFComponentOnE_deTurckRicciRHS (I := I) hfam g_bg i k hy
    have htrans : HasDerivAt
        (fun σ : ℝ => chartFComponentOnE (I := I) (deTurckRicciRHS (I := I) g_bg)
          (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x i k y₀)
        (Pval i k) 0 :=
      hsplit.congr_of_eventuallyEq (hloc i k).symm
    have htrans' : HasDerivAt
        (fun σ : ℝ => chartFComponentOnE (I := I) (deTurckRicciRHS (I := I) g_bg)
          (realizedFam (I := I) g₀ T T' hδ hδ' (s + σ)) x i k y₀)
        (Pval i k) (s - s) := by
      rwa [sub_self]
    have hsub := htrans'.comp_sub_const s s
    have hcongr : (fun t : ℝ => chartFComponentOnE (I := I) (deTurckRicciRHS (I := I) g_bg)
          (realizedFam (I := I) g₀ T T' hδ hδ' (s + (t - s))) x i k y₀) =
        (fun t : ℝ => chartFComponentOnE (I := I) (deTurckRicciRHS (I := I) g_bg)
          (realizedFam (I := I) g₀ T T' hδ hδ' t) x i k y₀) := by
      funext t; rw [add_sub_cancel]
    rwa [hcongr] at hsub
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          chartFComponentOnE (I := I) (deTurckRicciRHS (I := I) g_bg)
            (realizedFam (I := I) g₀ T T' hδ hδ' t) x i k y₀)
      (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i * (Pval i k)) s := by
    refine HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun k _ => ?_))
    exact (hper i k).const_mul _
  have hfun : realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w =
      (fun t : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          chartFComponentOnE (I := I) (deTurckRicciRHS (I := I) g_bg)
            (realizedFam (I := I) g₀ T T' hδ hδ' t) x i k y₀) := by
    funext t
    rw [realizedDeTurckRicciChartSum, hy₀]
  rw [hfun, hsum.deriv]

private theorem exists_chartRicciDeTurckOrder1CoeffField
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ R₁fib : ℝ → SmoothCcTensor g₀ 3 2,
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
            ((R₁fib p.2).toSection p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
        (∀ x : M, ContinuousOn (fun t : ℝ =>
            Tensor0SBundle.TensorRSSpace.toModel ((R₁fib t).toSection x))
            (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
        ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 →
          ∀ (x : M) (v : Fin 2 → TangentSpace I x)
            (h : ChartMetricPerturbation E),
            IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h →
            (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
                (((-2 : ℝ) * chartRicciSecondOrderPart (I := I)
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                    chartDeTurckCorrSecondOrderPart (I := I)
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x)) +
                  metricFamilyDeTurckRicciFirstOrderRemainder (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x))) =
              unitModel (I := I) (M := M) g₀ 2
                (appCc (I := I) (M := M) g₀ 2 2
                    (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
                        (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')
                      + (-1 : ℝ) • symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
                        (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')
                      + symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀
                        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg (T - T'))
                    (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                  + appCc (I := I) (M := M) g₀ 3 2 (R₁fib s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                  + appCc (I := I) (M := M) g₀ 4 2
                      (ricciArmPrincipalCoeffPure (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v :=
  sorry

private noncomputable def chartRicciDeTurckOrder1CoeffField
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ℝ → SmoothCcTensor g₀ 3 2 :=
  Classical.choose (exists_chartRicciDeTurckOrder1CoeffField (I := I) g₀ g_bg T T' hδ hδ')

private theorem chartRicciDeTurckOrder1CoeffField_jointContMDiff
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
        ((chartRicciDeTurckOrder1CoeffField (I := I) g₀ g_bg T T' hδ hδ' p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) :=
  (Classical.choose_spec (exists_chartRicciDeTurckOrder1CoeffField (I := I) g₀ g_bg T T' hδ hδ')).1

private theorem chartRicciDeTurckOrder1CoeffField_toModel_continuous
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) :
    ContinuousOn (fun t : ℝ =>
      Tensor0SBundle.TensorRSSpace.toModel
        ((chartRicciDeTurckOrder1CoeffField (I := I) g₀ g_bg T T' hδ hδ' t).toSection x))
      (realizedSmallSet (δ := δ) (δ' := δ')) :=
  (Classical.choose_spec (exists_chartRicciDeTurckOrder1CoeffField (I := I) g₀ g_bg T T' hδ hδ')).2.1 x

private theorem chartRicciDeTurckOrder1CoeffField_readout
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : M) (v : Fin 2 → TangentSpace I x)
    (h : ChartMetricPerturbation E)
    (hvel : IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
        (((-2 : ℝ) * chartRicciSecondOrderPart (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
            chartDeTurckCorrSecondOrderPart (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x)) +
          metricFamilyDeTurckRicciFirstOrderRemainder (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x))) =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')
              + (-1 : ℝ) • symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')
              + symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg (T - T'))
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + appCc (I := I) (M := M) g₀ 3 2
              (chartRicciDeTurckOrder1CoeffField (I := I) g₀ g_bg T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
          + appCc (I := I) (M := M) g₀ 4 2
              (ricciArmPrincipalCoeffPure (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v :=
  (Classical.choose_spec (exists_chartRicciDeTurckOrder1CoeffField (I := I) g₀ g_bg T T' hδ hδ')).2.2
    s hs x v h hvel

private theorem deTurckRicci_chartSymbolSum_eq_appCc_intrinsic
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : M) (v : Fin 2 → TangentSpace I x)
    (h : ChartMetricPerturbation E)
    (hvel : IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
        (((-2 : ℝ) * chartRicciSecondOrderPart (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
            chartDeTurckCorrSecondOrderPart (I := I)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x)) +
          metricFamilyDeTurckRicciFirstOrderRemainder (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x))) =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2
            (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')
              + (-1 : ℝ) • symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')
              + symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg (T - T'))
            (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
          + appCc (I := I) (M := M) g₀ 3 2
              (chartRicciDeTurckOrder1CoeffField (I := I) g₀ g_bg T T' hδ hδ' s)
              (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
          + appCc (I := I) (M := M) g₀ 4 2
              (ricciArmPrincipalCoeffPure (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s))
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v :=
  chartRicciDeTurckOrder1CoeffField_readout (I := I) g₀ g_bg T T' hδ hδ' s hs x v h hvel

private theorem deTurckRicci_threeSlot_appCc_covariantTransfer
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ}
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀fib : ℝ → SmoothCcTensor g₀ 2 2) (R₁fib : ℝ → SmoothCcTensor g₀ 3 2)
      (R₂fib : ℝ → SmoothCcTensor g₀ 4 2),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
            ((R₀fib p.2).toSection p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
            ((R₁fib p.2).toSection p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
            ((R₂fib p.2).toSection p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
        (∀ x : M, ContinuousOn (fun t : ℝ =>
            Tensor0SBundle.TensorRSSpace.toModel ((R₀fib t).toSection x))
            (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
        (∀ x : M, ContinuousOn (fun t : ℝ =>
            Tensor0SBundle.TensorRSSpace.toModel ((R₁fib t).toSection x))
            (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
        (∀ x : M, ContinuousOn (fun t : ℝ =>
            Tensor0SBundle.TensorRSSpace.toModel ((R₂fib t).toSection x))
            (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
        ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 →
          ∀ (x : M) (v : Fin 2 → TangentSpace I x)
            (h : ChartMetricPerturbation E),
            IsRealizedChartVelocity (I := I) g₀ T T' hδ hδ' x s h →
            (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) k * ((chartModelBasis E).repr (v 1)) i *
                (((-2 : ℝ) * chartRicciSecondOrderPart (I := I)
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) x h i k (extChartAt I x x) +
                    chartDeTurckCorrSecondOrderPart (I := I)
                      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x)) +
                  metricFamilyDeTurckRicciFirstOrderRemainder (I := I)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg x h i k (extChartAt I x x))) =
              unitModel (I := I) (M := M) g₀ 2
                (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                  + appCc (I := I) (M := M) g₀ 3 2 (R₁fib s)
                      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                  + appCc (I := I) (M := M) g₀ 4 2 (R₂fib s)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  refine ⟨fun s =>
      symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')
        + (-1 : ℝ) • symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')
        + symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg (T - T'),
    fun s => chartRicciDeTurckOrder1CoeffField (I := I) g₀ g_bg T T' hδ hδ' s,
    fun s => ricciArmPrincipalCoeffPure (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hR := symmAbsorbedOrder0RiemannCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
    have hC := jointRSsmul (I := I) (r := 2) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) (-1 : ℝ)
      (fun p : M × ℝ => (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1)
      (symmAbsorbedOrder0CurvCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ')
    have hL := symmAbsorbedOrder0DeTurckLieCoeff_realizedFam_jointContMDiff (I := I) g₀ g_bg T T' hδ hδ'
    have hRC := jointRSadd (I := I) (r := 2) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ'))
      (A := fun p : M × ℝ =>
        (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1)
      (B := fun p : M × ℝ =>
        (-1 : ℝ) • (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1) hR hC
    have hRCL := jointRSadd (I := I) (r := 2) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ'))
      (A := fun p : M × ℝ =>
        (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1
          + (-1 : ℝ) • (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1)
      (B := fun p : M × ℝ =>
        (symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg (T - T')).toSection p.1) hRC hL
    refine hRCL.congr (fun p _ => ?_)
    congr 1
  · exact chartRicciDeTurckOrder1CoeffField_jointContMDiff (I := I) g₀ g_bg T T' hδ hδ'
  · exact ricciArmPrincipalCoeffPure_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
  · intro x
    have hR := symmAbsorbedOrder0RiemannCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ'
    have hC := jointRSsmul (I := I) (r := 2) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ')) (-1 : ℝ)
      (fun p : M × ℝ => (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1)
      (symmAbsorbedOrder0CurvCoeff_realizedFam_jointContMDiff (I := I) g₀ T T' hδ hδ')
    have hL := symmAbsorbedOrder0DeTurckLieCoeff_realizedFam_jointContMDiff (I := I) g₀ g_bg T T' hδ hδ'
    have hRC := jointRSadd (I := I) (r := 2) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ'))
      (A := fun p : M × ℝ =>
        (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1)
      (B := fun p : M × ℝ =>
        (-1 : ℝ) • (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1) hR hC
    have hRCL := jointRSadd (I := I) (r := 2) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ'))
      (A := fun p : M × ℝ =>
        (symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1
          + (-1 : ℝ) • (symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' p.2) (T - T')).toSection p.1)
      (B := fun p : M × ℝ =>
        (symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg (T - T')).toSection p.1) hRC hL
    have hjoint := hRCL.congr (fun p _ => by congr 1)
    exact jointContMDiff_toModel_continuous_slice (I := I) g₀ 2 2
      (fun s => symmAbsorbedOrder0RiemannCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')
          + (-1 : ℝ) • symmAbsorbedOrder0CurvCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) (T - T')
          + symmAbsorbedOrder0DeTurckLieCoeff (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hjoint x
  · exact chartRicciDeTurckOrder1CoeffField_toModel_continuous (I := I) g₀ g_bg T T' hδ hδ'
  · exact ricciArmPrincipalCoeffPure_realizedFam_toModel_continuous (I := I) g₀ T T' hδ hδ'
  · intro s hs x v h hvel
    exact deTurckRicci_chartSymbolSum_eq_appCc_intrinsic (I := I) g₀ g_bg T T' hδ hδ' s hs x v h hvel

theorem deriv_realizedDeTurckRicciChartSum_eq_riemann_appCc_pointwise
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀fib : ℝ → SmoothCcTensor g₀ 2 2) (R₁fib : ℝ → SmoothCcTensor g₀ 3 2)
      (R₂fib : ℝ → SmoothCcTensor g₀ 4 2),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 2 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1
            ((R₀fib p.2).toSection p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 2 I z) p.1
            ((R₁fib p.2).toSection p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
            ((R₂fib p.2).toSection p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ')) ∧
        (∀ x : M, ContinuousOn (fun t : ℝ =>
            Tensor0SBundle.TensorRSSpace.toModel ((R₀fib t).toSection x))
            (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
        (∀ x : M, ContinuousOn (fun t : ℝ =>
            Tensor0SBundle.TensorRSSpace.toModel ((R₁fib t).toSection x))
            (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
        (∀ x : M, ContinuousOn (fun t : ℝ =>
            Tensor0SBundle.TensorRSSpace.toModel ((R₂fib t).toSection x))
            (realizedSmallSet (δ := δ) (δ' := δ'))) ∧
        ∀ s : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 → ∀ (x : M) (v : Fin 2 → TangentSpace I x),
          deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x (v 0) (v 1)) s =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 (R₁fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 (R₂fib s)
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨R₀fib, R₁fib, R₂fib, hjoint₀, hjoint₁, hjoint₂, hcont₀, hcont₁, hcont₂, hpt⟩ :=
    deTurckRicci_threeSlot_appCc_covariantTransfer (I := I) g₀ g_bg T T' hδ hδ'
  refine ⟨R₀fib, R₁fib, R₂fib, hjoint₀, hjoint₁, hjoint₂, hcont₀, hcont₁, hcont₂, fun s hs x v => ?_⟩
  obtain ⟨h, hvel, hderiv⟩ :=
    deriv_realizedDeTurckRicciChartSum_eq_rebased_chartSymbol (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ' hs x (v 0) (v 1)
  rw [hderiv]
  exact hpt s hs x v h hvel

theorem integratedLinearizedRicci_appCc_eq
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        (∫ s in (0 : ℝ)..1,
              deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x (v 0) (v 1)) s) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 R₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 R₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  obtain ⟨R₀fib, R₁fib, R₂fib, hjoint₀, hjoint₁, hjoint₂, hcont₀, hcont₁, hcont₂, hpt⟩ :=
    deriv_realizedDeTurckRicciChartSum_eq_riemann_appCc_pointwise (I := I) g₀ g_bg T T'
      hδ_lt hδ hδ'_lt hδ'

  have hcontRead₀ : ∀ (x : M) (v : Fin 2 → TangentSpace I x), ContinuousOn
      (fun s => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v)
      (Set.Icc (0 : ℝ) 1) := by
    intro x v
    have hIcc : Set.Icc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') :=
      Icc_subset_realizedSmallSet hδ_lt hδ'_lt
    exact (appCc_unitModel_read_continuousOn_of_toModel_continuousOn (I := I) g₀ 2
      R₀fib (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) (hcont₀ x) v).mono hIcc
  have hcontRead₁ : ∀ (x : M) (v : Fin 2 → TangentSpace I x), ContinuousOn
      (fun s => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2 (R₁fib s)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v)
      (Set.Icc (0 : ℝ) 1) := by
    intro x v
    have hIcc : Set.Icc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') :=
      Icc_subset_realizedSmallSet hδ_lt hδ'_lt
    exact (appCc_unitModel_read_continuousOn_of_toModel_continuousOn (I := I) g₀ 3
      R₁fib (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) (hcont₁ x) v).mono hIcc
  have hcontRead₂ : ∀ (x : M) (v : Fin 2 → TangentSpace I x), ContinuousOn
      (fun s => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (R₂fib s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v)
      (Set.Icc (0 : ℝ) 1) := by
    intro x v
    have hIcc : Set.Icc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') :=
      Icc_subset_realizedSmallSet hδ_lt hδ'_lt
    exact (appCc_unitModel_read_continuousOn_of_toModel_continuousOn (I := I) g₀ 4
      R₂fib (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) (hcont₂ x) v).mono hIcc
  have hint₀ : ∀ (x : M) (v : Fin 2 → TangentSpace I x), IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s)
          (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))) x v)
      MeasureTheory.volume 0 1 :=
    fun x v => ((hcontRead₀ x v)).intervalIntegrable_of_Icc zero_le_one
  have hint₁ : ∀ (x : M) (v : Fin 2 → TangentSpace I x), IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 3 2 (R₁fib s)
          (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))) x v)
      MeasureTheory.volume 0 1 :=
    fun x v => ((hcontRead₁ x v)).intervalIntegrable_of_Icc zero_le_one
  have hint₂ : ∀ (x : M) (v : Fin 2 → TangentSpace I x), IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (R₂fib s)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v)
      MeasureTheory.volume 0 1 :=
    fun x v => ((hcontRead₂ x v)).intervalIntegrable_of_Icc zero_le_one
  
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  have hSI : Set.uIcc (0:ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') := by
    rw [Set.uIcc_of_le (zero_le_one)]
    exact Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  obtain ⟨IΦ₀, heval₀⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 2 R₀fib
      (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjoint₀ hcont₀
  obtain ⟨IΦ₁, heval₁⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 3 R₁fib
      (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjoint₁ hcont₁
  obtain ⟨IΦ₂, heval₂⟩ :=
    exists_pathIntegralCoeffField (I := I) (M := M) g₀ 4 R₂fib
      (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjoint₂ hcont₂


  refine ⟨IΦ₀, IΦ₁, IΦ₂, fun x v => ?_⟩
  set W₀ : SmoothCcTensor g₀ 0 2 := iteratedCovGrad (I := I) g₀ 0 2 0 (T - T') with hW₀
  set W₁ : SmoothCcTensor g₀ 0 3 := iteratedCovGrad (I := I) g₀ 0 2 1 (T - T') with hW₁
  set W₂ : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 (T - T') with hW₂


  have hrhs :
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2 IΦ₀ W₀
            + appCc (I := I) (M := M) g₀ 3 2 IΦ₁ W₁
            + appCc (I := I) (M := M) g₀ 4 2 IΦ₂ W₂) x v =
        (unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 IΦ₀ W₀) x v +
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 IΦ₁ W₁) x v) +
          unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 IΦ₂ W₂) x v := by
    rw [unitModel_add_left, ContinuousMultilinearMap.add_apply, unitModel_add_left,
      ContinuousMultilinearMap.add_apply]
  rw [hrhs]

  rw [heval₀ x v, heval₁ x v, heval₂ x v]


  have hii₀ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 2 2 (R₀fib s) W₀) x v)
      MeasureTheory.volume 0 1 := hint₀ x v
  have hii₁ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 3 2 (R₁fib s) W₁) x v)
      MeasureTheory.volume 0 1 := hint₁ x v
  have hii₂ : IntervalIntegrable
      (fun s => unitModel (I := I) (M := M) g₀ 2 (appCc (I := I) (M := M) g₀ 4 2 (R₂fib s) W₂) x v)
      MeasureTheory.volume 0 1 := hint₂ x v
  rw [← intervalIntegral.integral_add hii₀ hii₁, ← intervalIntegral.integral_add (hii₀.add hii₁) hii₂]



  refine intervalIntegral.integral_congr_ae ?_

  refine MeasureTheory.measure_mono_null (t := {(1 : ℝ)}) (fun s hs => ?_)
    (MeasureTheory.measure_singleton 1)

  rw [Set.mem_singleton_iff]
  by_contra hne1
  apply hs
  intro hsmem
  rw [Set.mem_uIoc] at hsmem
  rcases hsmem with ⟨hs0, hs1⟩ | ⟨hs1, hs0⟩
  · rw [hpt s ⟨hs0, lt_of_le_of_ne hs1 hne1⟩ x v, unitModel_add_left,
      ContinuousMultilinearMap.add_apply, unitModel_add_left,
      ContinuousMultilinearMap.add_apply]
  · exact absurd (lt_of_lt_of_le hs1 hs0) (by norm_num)

private theorem realizedFam_one_eq_realize (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    realizedFam (I := I) g₀ T T' hδ hδ' 1 = tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ := by
  have hmem : (1 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt ⟨zero_le_one, le_refl 1⟩
  refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
  rw [realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem, tensorSectionRealizeMetric_inner,
    convexPerturbation_one]

private theorem realizedFam_zero_eq_realize (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    realizedFam (I := I) g₀ T T' hδ hδ' 0 = tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ' := by
  have hmem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt ⟨le_refl 0, zero_le_one⟩
  refine riemannianMetric_eq_of_inner _ _ (fun b u z => ?_)
  rw [realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hmem, tensorSectionRealizeMetric_inner,
    convexPerturbation_zero]

private theorem realizedDeTurckRicciChartSum_endpoint_eq
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) (s : ℝ) :
    realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w s =
      DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s) x v w := by
  classical
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb
  set g : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg
  set F : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg g x with hF
  
  have hcomp : ∀ i k : Fin (Module.finrank ℝ E),
      DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg) g x i k
          (extChartAt I x x) = F (b i) (b k) := by
    intro i k
    rw [DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE]
    have hleft : (extChartAt I x).symm (extChartAt I x x) = x :=
      (extChartAt I x).left_inv (mem_extChartAt_source x)
    rw [hleft]
    rw [show DifferentialGeometry.PDE.RicciFlow.chartPushforwardFrameVec (I := I) x i x = b i from
        chartBasisVecFiber_self (I := I) x i,
      show DifferentialGeometry.PDE.RicciFlow.chartPushforwardFrameVec (I := I) x k x = b k from
        chartBasisVecFiber_self (I := I) x k]
  
  
  have hExpand : F w v =
      ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        (b.repr w) i * (b.repr v) k * F (b i) (b k) := by
    conv_lhs => rw [show w = ∑ i, (b.repr w) i • b i from (b.sum_repr w).symm,
      show v = ∑ k, (b.repr v) k • b k from (b.sum_repr v).symm]
    rw [map_sum F, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, ContinuousLinearMap.smul_apply, map_sum (F (b i))]
    rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul]
    ring
  rw [realizedDeTurckRicciChartSum, show
      DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s) x v w = F v w from rfl,
    show F v w = F w v from deTurckRicciRHS_isPointwiseSymm (I := I) g_bg g x v w,
    hExpand]
  
  
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hcomp i k]
  ring

theorem deTurckRicciRHS_realized_sub_eq_integral_chartDeriv
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) :
    DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x v w -
        DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x v w =
      ∫ s in (0 : ℝ)..1,
        deriv (realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w) s := by
  classical
  set f : ℝ → ℝ := realizedDeTurckRicciChartSum (I := I) g₀ g_bg T T' hδ hδ' x v w with hf
  
  have hfeq : f = (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          DifferentialGeometry.PDE.RicciFlow.chartFComponentOnE (I := I)
            (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k (extChartAt I x x)) := by
    funext s; rw [hf, realizedDeTurckRicciChartSum]
  
  have hcd : ∀ s ∈ realizedSmallSet (δ := δ) (δ' := δ'), ContDiffAt ℝ ∞ f s := by
    intro s hs
    rw [hfeq]
    exact realizedDeTurckRicciChartSum_contDiffAt (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ' x v w hs
  
  have hsub : Set.Icc (0:ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ') :=
    Icc_subset_realizedSmallSet hδ_lt hδ'_lt
  have hcont : ContinuousOn f (Set.Icc (0:ℝ) 1) := fun s hs =>
    (hcd s (hsub hs)).continuousAt.continuousWithinAt
  
  have hderiv : ∀ s ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (deriv f s) s := by
    intro s hs
    exact (hcd s (hsub (Set.mem_Icc_of_Ioo hs))).differentiableAt (by simp) |>.hasDerivAt
  
  have hderiv_cont : ContinuousOn (deriv f) (Set.Icc (0:ℝ) 1) := by
    have hcdOn : ContDiffOn ℝ ∞ f (realizedSmallSet (δ := δ) (δ' := δ')) := fun s hs =>
      (hcd s hs).contDiffWithinAt
    exact (hcdOn.continuousOn_deriv_of_isOpen realizedSmallSet_isOpen
      (by exact_mod_cast le_top)).mono hsub
  have hint : IntervalIntegrable (deriv f) MeasureTheory.volume 0 1 :=
    hderiv_cont.intervalIntegrable_of_Icc zero_le_one
  
  have hFTC : ∫ s in (0:ℝ)..1, deriv f s = f 1 - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  rw [hFTC]
  
  rw [hf, realizedDeTurckRicciChartSum_endpoint_eq (I := I) g₀ g_bg T T' hδ hδ' x v w 1,
    realizedDeTurckRicciChartSum_endpoint_eq (I := I) g₀ g_bg T T' hδ hδ' x v w 0,
    realizedFam_one_eq_realize (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ',
    realizedFam_zero_eq_realize (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ']

theorem deTurckRicciArm_appCc_eval
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
      ∀ (x : M) (v : Fin 2 → TangentSpace I x),
        (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
              (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
            - DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)) =
          unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 R₀
                (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
              + appCc (I := I) (M := M) g₀ 3 2 R₁
                  (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
              + appCc (I := I) (M := M) g₀ 4 2 R₂
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v := by
  classical
  
  
  obtain ⟨R₀, R₁, R₂, heval⟩ :=
    integratedLinearizedRicci_appCc_eq (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  refine ⟨R₀, R₁, R₂, fun x v => ?_⟩

  rw [deTurckRicciRHS_realized_sub_eq_integral_chartDeriv (I := I) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
    x (v 0) (v 1)]


  exact heval x v

theorem deTurckRicciArm_appCc_graded
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    ∃ (Λ : ℝ), 0 ≤ Λ ∧
      ∃ (R₀ : SmoothCcTensor g₀ 2 2) (R₁ : SmoothCcTensor g₀ 3 2) (R₂ : SmoothCcTensor g₀ 4 2),
        (∀ (x : M) (v : Fin 2 → TangentSpace I x),
          (DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 0) (v 1)
              - DifferentialGeometry.PDE.RicciFlow.deTurckRicciRHS (I := I) g_bg
                  (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') x (v 0) (v 1)) =
            unitModel (I := I) (M := M) g₀ 2
              (appCc (I := I) (M := M) g₀ 2 2 R₀
                  (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T'))
                + appCc (I := I) (M := M) g₀ 3 2 R₁
                    (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T'))
                + appCc (I := I) (M := M) g₀ 4 2 R₂
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) x v) ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (R₀.toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (R₁.toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R₂.toSection x) ≤ Λ ^ 2) ∧
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 2 2 a R₀).toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 3 2 a R₁).toSection x) ≤ Λ ^ 2 ∧
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 4 2 a R₂).toSection x) ≤ Λ ^ 2) := by
  
  obtain ⟨R₀, R₁, R₂, heval⟩ :=
    deTurckRicciArm_appCc_eval (I := I) (M := M) g₀ g_bg T T' hδ_lt hδ hδ'_lt hδ'
  
  
  obtain ⟨K₀, hK₀_nn, hK₀⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2 R₀
  obtain ⟨K₁, hK₁_nn, hK₁⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 2 R₁
  obtain ⟨K₂, hK₂_nn, hK₂⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 2 R₂
  
  
  obtain ⟨J₀, hJ₀_nn, hJ₀⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + a)
      (iteratedCovGrad (I := I) g₀ 2 2 a R₀)
  obtain ⟨J₁, hJ₁_nn, hJ₁⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 3 (2 + a)
      (iteratedCovGrad (I := I) g₀ 3 2 a R₁)
  obtain ⟨J₂, hJ₂_nn, hJ₂⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + a)
      (iteratedCovGrad (I := I) g₀ 4 2 a R₂)
  
  set Kmax : ℝ := max (max (max K₀ K₁) K₂) (max (max J₀ J₁) J₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax :=
    le_trans hK₀_nn (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  refine ⟨Real.sqrt Kmax, Real.sqrt_nonneg _, R₀, R₁, R₂, heval, fun x => ?_, fun x => ?_⟩
  · have hsq : Real.sqrt Kmax ^ 2 = Kmax := Real.sq_sqrt hKmax_nn
    rw [hsq]
    refine ⟨le_trans (hK₀ x) ?_, le_trans (hK₁ x) ?_, le_trans (hK₂ x) ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
    · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · have hsq : Real.sqrt Kmax ^ 2 = Kmax := Real.sq_sqrt hKmax_nn
    rw [hsq]
    refine ⟨le_trans (hJ₀ x) ?_, le_trans (hJ₁ x) ?_, le_trans (hJ₂ x) ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
    · exact le_trans (le_max_right _ _) (le_max_right _ _)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
