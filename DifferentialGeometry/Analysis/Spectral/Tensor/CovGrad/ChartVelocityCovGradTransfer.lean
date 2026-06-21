import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.SecondCovGradChartHessian
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.DeTurckCorrectionPrincipalSymbolRemainder

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def chartRoughLaplacianSymbol (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g α j l y *
      partialDeriv (E := E) j (partialDeriv (E := E) l (h.toFun i k)) y

@[simp] lemma chartRoughLaplacianSymbol_def (g : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRoughLaplacianSymbol (I := I) g α h i k y =
      ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α j l y *
          partialDeriv (E := E) j (partialDeriv (E := E) l (h.toFun i k)) y :=
  rfl

private lemma sum_chartGram_mul_chartInvGram_general
    (g : SmoothRiemannianMetric I M) (α : M) (j l : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    ∑ k : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α k j y * chartInvGramOnE (I := I) g α k l y =
      (if j = l then (1 : ℝ) else 0) := by
  classical
  have hp : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α,
      ← extChartAt_source_eq_chartAt_source (I := I) α]
    exact (extChartAt I α).map_target (interior_subset hy)
  have hmul := chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hp
  have hentry : (chartGramMatrix (I := I) g α ((extChartAt I α).symm y) *
      chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y)) j l =
      (1 : Matrix _ _ ℝ) j l := by rw [hmul]
  rw [Matrix.one_apply] at hentry
  rw [Matrix.mul_apply] at hentry
  rw [← hentry]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartGramOnE_def, chartInvGramOnE_def]
  rw [show chartGramMatrix (I := I) g α ((extChartAt I α).symm y) j k =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y) k j from by
    rw [chartGramMatrix_apply, chartGramMatrix_apply]; exact g.symm _ _ _]

private lemma chartDeTurckCorrBlock_contracted
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (d c : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    (∑ m : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α m c y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h d a b m y) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          ((1 / 2 : ℝ) *
            (partialDeriv (E := E) d (partialDeriv (E := E) a (h.toFun c b)) y +
             partialDeriv (E := E) d (partialDeriv (E := E) b (h.toFun c a)) y -
             partialDeriv (E := E) d (partialDeriv (E := E) c (h.toFun a b)) y)) := by
  classical
  simp only [chartDeTurckCorrHessBlock_def]
  set Z := fun (a b l : Fin (Module.finrank ℝ E)) =>
    partialDeriv (E := E) d (partialDeriv (E := E) a (h.toFun l b)) y +
      partialDeriv (E := E) d (partialDeriv (E := E) b (h.toFun l a)) y -
      partialDeriv (E := E) d (partialDeriv (E := E) l (h.toFun a b)) y with hZ
  set X := fun (a b : Fin (Module.finrank ℝ E)) => chartInvGramOnE (I := I) g α a b y with hX
  set Y := fun (m l : Fin (Module.finrank ℝ E)) => chartInvGramOnE (I := I) g α m l y with hY
  set Gc := fun (m : Fin (Module.finrank ℝ E)) => chartGramOnE (I := I) g α m c y with hGc
  have hgoal : (∑ m : Fin (Module.finrank ℝ E),
        Gc m * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            X a b * ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E), Y m l * Z a b l)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        X a b * ((1 / 2 : ℝ) * Z a b c) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_comm]
    rw [show (∑ l : Fin (Module.finrank ℝ E), ∑ m : Fin (Module.finrank ℝ E),
          Gc m * (X a b * ((1 / 2 : ℝ) * (Y m l * Z a b l)))) =
        ∑ l : Fin (Module.finrank ℝ E),
          (∑ m : Fin (Module.finrank ℝ E), Gc m * Y m l) *
            (X a b * ((1 / 2 : ℝ) * Z a b l)) from by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring]
    rw [show (∑ l : Fin (Module.finrank ℝ E),
          (∑ m : Fin (Module.finrank ℝ E), Gc m * Y m l) *
            (X a b * ((1 / 2 : ℝ) * Z a b l))) =
        ∑ l : Fin (Module.finrank ℝ E),
          (if c = l then (1 : ℝ) else 0) * (X a b * ((1 / 2 : ℝ) * Z a b l)) from by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hGc, hY, sum_chartGram_mul_chartInvGram_general (I := I) g α c l hy]]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ c
      (fun l => X a b * ((1 / 2 : ℝ) * Z a b l))]
    simp only [Finset.mem_univ, if_true]
  exact hgoal

theorem chartRicciDeTurck_gaugeCancellation_principalSymbol
    (g g' : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    (-2 : ℝ) * chartRicciSecondOrderPrincipalSymbol (I := I) g α h i k y +
        chartDeTurckCorrPrincipalSymbolExpr (I := I) g g' α h i k y =
      chartRoughLaplacianSymbol (I := I) g α h i k y := by
  classical
  rw [chartRicciSecondOrderPrincipalSymbol_def, chartDeTurckCorrPrincipalSymbolExpr_def,
    chartRoughLaplacianSymbol_def]
  rw [chartDeTurckCorrBlock_contracted (I := I) g g' α h i k hy,
    show (∑ m : Fin (Module.finrank ℝ E),
        chartGramOnE (I := I) g α i m y *
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α a b y *
              chartDeTurckCorrHessBlock (I := I) g g' α h k a b m y) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α a b y *
          ((1 / 2 : ℝ) *
            (partialDeriv (E := E) k (partialDeriv (E := E) a (h.toFun i b)) y +
             partialDeriv (E := E) k (partialDeriv (E := E) b (h.toFun i a)) y -
             partialDeriv (E := E) k (partialDeriv (E := E) i (h.toFun a b)) y)) from by
      rw [show (∑ m : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) g α i m y *
              ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α a b y *
                  chartDeTurckCorrHessBlock (I := I) g g' α h k a b m y) =
          ∑ m : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) g α m i y *
              ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g α a b y *
                  chartDeTurckCorrHessBlock (I := I) g g' α h k a b m y from by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [chartGramOnE_symm (I := I) g α i m y]]
      exact chartDeTurckCorrBlock_contracted (I := I) g g' α h k i hy]
  set G := fun a b => chartInvGramOnE (I := I) g α a b y with hG
  set D := fun p q a b => partialDeriv (E := E) p (partialDeriv (E := E) q (h.toFun a b)) y with hD
  have hclr : ∀ p q a b : Fin (Module.finrank ℝ E), D p q a b = D q p a b :=
    fun p q a b =>
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.partialDeriv_partialDeriv_perturbation_swap
        (E := E) h a b p q y
  have hcomp : ∀ p q a b : Fin (Module.finrank ℝ E), D p q a b = D p q b a :=
    fun p q a b => by
      have : h.toFun a b = h.toFun b a := h.symm_fun a b
      simp only [hD, this]
  have hgsymm : ∀ a b : Fin (Module.finrank ℝ E), G a b = G b a :=
    fun a b => DifferentialGeometry.Integral.DivergenceTheorem.chartInvGramOnE_symm
      (I := I) g α a b y
  have hsymeq : ∀ (X Y : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      (∀ a b, X a b + X b a = Y a b + Y b a) →
        (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), G a b * X a b) =
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), G a b * Y a b := by
    intro X Y hXY
    have hdbl : ∀ (Z : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
        (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * Z a b) =
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * (Z a b + Z b a) := by
      intro Z
      have hswap : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * Z a b) =
          ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * Z b a := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [hgsymm a b]
      have hsplit : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * (Z a b + Z b a)) =
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * Z a b) +
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * Z b a) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
      rw [hsplit, ← hswap]
      ring
    have h2X := hdbl X
    have h2Y := hdbl Y
    have hpt : (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          G a b * (X a b + X b a)) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          G a b * (Y a b + Y b a) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [hXY a b]
    have : (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          G a b * X a b) =
        (2 : ℝ) * (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          G a b * Y a b) := by rw [h2X, h2Y, hpt]
    linarith [this]
  have hLhs : (-2 : ℝ) * ((1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          G j l * (D j i l k + D k l i j - D j l i k - D k i l j)) +
        ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * ((1 / 2 : ℝ) * (D i a k b + D i b k a - D i k a b))) +
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * ((1 / 2 : ℝ) * (D k a i b + D k b i a - D k i a b)))) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        G a b * (-(D a i b k + D k b i a - D a b i k - D k i b a) +
          ((1 / 2 : ℝ) * (D i a k b + D i b k a - D i k a b) +
           (1 / 2 : ℝ) * (D k a i b + D k b i a - D k i a b))) := by
    have hRic : (-2 : ℝ) * ((1 / 2 : ℝ) * ∑ j : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            G j l * (D j i l k + D k l i j - D j l i k - D k i l j)) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          G a b * (-(D a i b k + D k b i a - D a b i k - D k i b a)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring
    rw [hRic]
    rw [show ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * ((1 / 2 : ℝ) * (D i a k b + D i b k a - D i k a b))) +
          (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            G a b * ((1 / 2 : ℝ) * (D k a i b + D k b i a - D k i a b)))) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          G a b * ((1 / 2 : ℝ) * (D i a k b + D i b k a - D i k a b) +
           (1 / 2 : ℝ) * (D k a i b + D k b i a - D k i a b)) from by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hLhs]
  rw [show (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        G j l * D j l i k) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        G a b * D a b i k from rfl]
  refine hsymeq _ _ (fun a b => ?_)
  have eP1 : D i a k b = D a i b k := by rw [hclr i a k b, hcomp a i k b]
  have eT1 : D b i a k = D i b k a := by rw [hclr b i a k, hcomp i b a k]
  have eR1 : D b a i k = D a b i k := by rw [hclr b a i k]
  have eU1 : D k i b a = D i k a b := by rw [hclr k i b a, hcomp i k b a]
  have eU2 : D k i a b = D i k a b := by rw [hclr k i a b]
  have eU3 : D i k b a = D i k a b := by rw [hcomp i k b a]
  linarith [eP1, eT1, eR1, eU1, eU2, eU3]

def chartRoughLaplacianLowerCorr (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    (α : M) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramOnE (I := I) g₁ α j l y *
      (covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
          (covGrad (I := I) (M := M) g₀ 0 2 S) α j ![] ![l, i, k]
          (toEuclidean (E := E) y)
        + euclidPartial (E := E) j
            (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k] y')
            (toEuclidean (E := E) y))

private lemma partialDeriv_eq_euclidPartial_comp_symm
    (u : E → ℝ) (l : Fin (Module.finrank ℝ E))
    (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    partialDeriv (E := E) l u ((toEuclidean (E := E)).symm z) =
      euclidPartial (E := E) l (u ∘ (toEuclidean (E := E)).symm) z := by
  rw [euclidPartial_def,
    (toEuclidean (E := E)).symm.comp_right_fderiv (f := u) (x := z),
    ContinuousLinearMap.comp_apply]
  rw [show (toEuclidean (E := E)).symm.toContinuousLinearMap
      (EuclideanSpace.single l (1 : ℝ)) = (chartModelBasis E) l from by
    rw [chartModelBasis_apply]; rfl]
  rw [partialDeriv]

private lemma partialDeriv_partialDeriv_eq_euclidPartial
    (u : E → ℝ) (j l : Fin (Module.finrank ℝ E))
    (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    partialDeriv (E := E) j (partialDeriv (E := E) l u) ((toEuclidean (E := E)).symm z) =
      euclidPartial (E := E) j
        (euclidPartial (E := E) l (u ∘ (toEuclidean (E := E)).symm)) z := by
  rw [partialDeriv_eq_euclidPartial_comp_symm
    (E := E) (partialDeriv (E := E) l u) j z]
  congr 1
  funext z'
  exact partialDeriv_eq_euclidPartial_comp_symm (E := E) u l z'

private lemma euclidPartial_eq_of_eventuallyEq
    {u v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ} (j : Fin (Module.finrank ℝ E))
    {z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))} (huv : u =ᶠ[nhds z] v) :
    euclidPartial (E := E) j u z = euclidPartial (E := E) j v z := by
  rw [euclidPartial_def, euclidPartial_def, huv.fderiv_eq]

theorem chartRoughLaplacianSymbol_eq_chartInvGram_iteratedCovGrad
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (α : M)
    (h : ChartMetricPerturbation E) (i k : Fin (Module.finrank ℝ E))
    (hlink : ∀ a b : Fin (Module.finrank ℝ E),
      (fun y => h.toFun a b y) =ᶠ[nhds (extChartAt I α α)]
        (fun y => tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S α ![] ![a, b]
          ((extChartAt I α).symm y))) :
    chartRoughLaplacianSymbol (I := I) g₁ α h i k (extChartAt I α α) =
      (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α)
        - chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α) := by
  classical
  set y₀ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) (extChartAt I α α) with hy₀
  have hy₀mem : y₀ ∈ chartTargetEuclid (I := I) (M := M) α :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) α (mem_chart_source H α)
  have hround : (extChartAt I α).symm ((toEuclidean (E := E)).symm y₀) = α := by
    rw [hy₀]
    exact symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) α (mem_chart_source H α)
  have hcenter : (toEuclidean (E := E)).symm y₀ = extChartAt I α α := by
    rw [hy₀, (toEuclidean (E := E)).symm_apply_apply]
  set chP := chartPushedRaw I α
    (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S α ![] ![i, k]) with hchP
  set hessTerm := fun (j l : Fin (Module.finrank ℝ E)) =>
    euclidPartial (E := E) j (euclidPartial (E := E) l chP) y₀ with hhessTerm
  have hLHS : chartRoughLaplacianSymbol (I := I) g₁ α h i k (extChartAt I α α) =
      ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) * hessTerm j l := by
    rw [chartRoughLaplacianSymbol_def]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    congr 1
    have hpd : partialDeriv (E := E) j (partialDeriv (E := E) l (h.toFun i k))
          (extChartAt I α α) =
        euclidPartial (E := E) j
          (euclidPartial (E := E) l ((h.toFun i k) ∘ (toEuclidean (E := E)).symm)) y₀ := by
      rw [← hcenter]
      exact partialDeriv_partialDeriv_eq_euclidPartial (E := E) (h.toFun i k) j l y₀
    rw [hpd, hhessTerm]
    have hev : ((h.toFun i k) ∘ (toEuclidean (E := E)).symm) =ᶠ[nhds y₀] chP := by
      have hcomp : ((h.toFun i k) ∘ (toEuclidean (E := E)).symm) =ᶠ[nhds y₀]
          ((fun y => tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S α ![] ![i, k]
              ((extChartAt I α).symm y)) ∘ (toEuclidean (E := E)).symm) := by
        have htend : Filter.Tendsto (toEuclidean (E := E)).symm (nhds y₀)
            (nhds (extChartAt I α α)) := by
          rw [← hcenter]
          exact ((toEuclidean (E := E)).symm.continuous.continuousAt)
        exact (hlink i k).comp_tendsto htend
      have hchPeq : chP =ᶠ[nhds y₀]
          ((fun y => tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S α ![] ![i, k]
              ((extChartAt I α).symm y)) ∘ (toEuclidean (E := E)).symm) := by
        have hopen := chartTargetEuclid_isOpen (I := I) (M := M) α
        filter_upwards [hopen.mem_nhds hy₀mem] with z hz
        rw [hchP, chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hz]
        rfl
      exact hcomp.trans hchPeq.symm
    have hev2 : euclidPartial (E := E) l
          ((h.toFun i k) ∘ (toEuclidean (E := E)).symm) =ᶠ[nhds y₀]
        euclidPartial (E := E) l chP := by
      filter_upwards [hev.eventuallyEq_nhds] with z hz
      rw [euclidPartial_def, euclidPartial_def, hz.fderiv_eq]
    exact euclidPartial_eq_of_eventuallyEq (E := E) j hev2
  rw [hLHS]
  have hrawCD : ∀ (Idx' : Fin 0 → Fin (Module.finrank ℝ E))
      (Jdx' : Fin 2 → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (↑(⊤ : ℕ∞))
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S α Idx' Jdx'))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro Idx' Jdx'
    exact chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
      g₀ 0 2 S α Idx' Jdx'
  have hnhds : chartTargetEuclid (I := I) (M := M) α ∈ nhds y₀ :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hy₀mem
  have hAdiff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (euclidPartial (E := E) l
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S α ![] ![i, k]))) y₀ := by
    intro l
    exact ((euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k]
      ).differentiableOn (by simp)).differentiableAt hnhds
  have hBdiff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k] y') y₀ := by
    intro l
    exact ((covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k]
      hrawCD).differentiableOn (by simp)).differentiableAt hnhds
  have hbridge : ∀ j l : Fin (Module.finrank ℝ E),
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α =
        hessTerm j l +
          (euclidPartial (E := E) j
              (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k] y') y₀ +
            covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
              (covGrad (I := I) (M := M) g₀ 0 2 S) α j ![] ![l, i, k] y₀) := by
    intro j l
    have hb := chartCovariantSecondGrad_chartHessian_sub_correction
      (I := I) (M := M) g₀ S α ![] ![j, l, i, k] hy₀mem
    rw [show ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₀)) = α from hround] at hb
    have hT1 : Matrix.vecTail (![j, l, i, k] : Fin 4 → Fin (Module.finrank ℝ E)) =
        ![l, i, k] := by
      funext z; fin_cases z <;> rfl
    rw [hb]
    simp only [Matrix.cons_val_zero, hT1]
    change euclidPartial (E := E) j
          (fun y' => euclidPartial (E := E) l chP y' +
            covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k] y') y₀ +
          covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
            (covGrad (I := I) (M := M) g₀ 0 2 S) α j ![] ![l, i, k] y₀ =
        hessTerm j l +
          (euclidPartial (E := E) j
              (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k] y') y₀ +
            covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 3
              (covGrad (I := I) (M := M) g₀ 0 2 S) α j ![] ![l, i, k] y₀)
    rw [hhessTerm]
    have hadd : euclidPartial (E := E) j
          (fun y' => euclidPartial (E := E) l chP y' +
            covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k] y') y₀ =
        euclidPartial (E := E) j (euclidPartial (E := E) l chP) y₀ +
          euclidPartial (E := E) j
            (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k] y') y₀ := by
      rw [euclidPartial_def, euclidPartial_def, euclidPartial_def]
      rw [show (fun y' => euclidPartial (E := E) l chP y' +
            covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k] y') =
          (fun y' => euclidPartial (E := E) l chP y') +
            (fun y' => covDerivLowerOrderTerm (I := I) (M := M) g₀ 0 2 S α l ![] ![i, k] y')
          from rfl]
      rw [fderiv_add (hAdiff l) (hBdiff l), ContinuousLinearMap.add_apply]
    rw [hadd]
    ring
  have hRHS : (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
            tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α)
        - chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α) =
      ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) * hessTerm j l := by
    rw [chartRoughLaplacianLowerCorr]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hbridge j l]
    have hy₀eq : (toEuclidean (E := E)) (extChartAt I α α) = y₀ := hy₀.symm
    rw [hy₀eq]
    ring
  rw [hRHS]

private lemma cmm4_slot_sum_smul
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (s : Fin 4) (c : Fin (Module.finrank ℝ E) → ℝ)
    (u : Fin (Module.finrank ℝ E) → E) (base : Fin 4 → E) :
    f (Function.update base s
        (∑ i : Fin (Module.finrank ℝ E), c i • u i)) =
      ∑ i : Fin (Module.finrank ℝ E), c i * f (Function.update base s (u i)) := by
  classical
  have hsum : f (Function.update base s
        (∑ i : Fin (Module.finrank ℝ E), c i • u i)) =
      ∑ i : Fin (Module.finrank ℝ E),
        f (Function.update base s (c i • u i)) := by
    rw [show (∑ i : Fin (Module.finrank ℝ E), c i • u i) =
        ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), c i • u i from rfl]
    exact f.toMultilinearMap.map_update_sum Finset.univ s (fun i => c i • u i) base
  rw [hsum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [f.map_update_smul, smul_eq_mul]

private lemma tensorChartComponentRaw_zero_eq_unitModel_chartBasis
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) (α : M)
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentRaw (I := I) (M := M) g 0 s W α ![] Jdx α =
      unitModel (I := I) (M := M) g s W α
        (fun j : Fin s => (chartModelBasis E) (Jdx j)) := by
  classical
  rw [tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 s W α
    (mem_chart_source H α) ![] Jdx]
  have hframe : chartFrameBasisModel (I := I) (M := M) α α 0 ![] =
      unitTensor (I := I) (M := M) α := by
    refine Tensor0SBundle.tensor0SSpace_ext 0 α (fun w => ?_)
    rw [chartFrameBasisModel_apply (I := I) (M := M) α α 0 ![] w]
    rw [Finset.prod_of_isEmpty]
    have hunit : unitTensor (I := I) (M := M) α w = (1 : ℝ) := rfl
    rw [hunit]
  rw [hframe]
  rw [unitModel]
  refine congrArg _ ?_
  funext j
  exact chartBasisVecFiber_self (I := I) (M := M) α (Jdx j)

theorem chartInvGram_iteratedCovGrad_trace_eq_unitModel_appCc
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (α : M)
    (v : Fin 2 → TangentSpace I α) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
                (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α)) =
      unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 S)) α v := by
  classical
  set W : SmoothCcTensor g₀ 0 4 := iteratedCovGrad (I := I) g₀ 0 2 2 S with hW
  set Wm : Tensor0SBundle.Tensor0SModel 4 ℝ E := unitModel (I := I) (M := M) g₀ 4 W α with hWm
  have hcomp : ∀ a b c d : Fin (Module.finrank ℝ E),
      tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2) W α ![] ![a, b, c, d] α =
        Wm ![(chartModelBasis E) a, (chartModelBasis E) b,
          (chartModelBasis E) c, (chartModelBasis E) d] := by
    intro a b c d
    rw [tensorChartComponentRaw_zero_eq_unitModel_chartBasis (I := I) (M := M) g₀ (2 + 2) W α
      ![a, b, c, d]]
    rw [hWm]
    congr 1
    funext m
    fin_cases m <;> rfl
  -- raised cometric covector expansion in the chart basis
  have hα_base : α ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]; exact mem_chart_source H α
  have hraise : ∀ k' : Fin (Module.finrank ℝ E),
      cometricLmodel (I := I) g₁ α
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k')) =
        ∑ j : Fin (Module.finrank ℝ E),
          (∑ n : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ α α j n *
              ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n)) •
            (chartModelBasis E) j := by
    intro k'
    have hcomet : cometricLmodel (I := I) g₁ α
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k')) =
        inverseMetricSharpFib (I := I) g₁ α
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k')) := rfl
    rw [hcomet, inverseMetricSharpFib_apply,
      ← metricSharpChartLocal_eq_metricSharp (I := I) g₁ α
        (fun b => Tensor0SBundle.cotangentToDualLinear
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k'))) hα_base]
    rw [metricSharpChartLocal]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [metricSharpChartCoeff_def]
    rw [chartBasisVecFiber_self (I := I) (M := M) α j]
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [chartBasisVecFiber_self (I := I) (M := M) α n]
    rfl
  -- update-conversion facts for the Fin 4 tuples
  have hupd3 : ∀ a b c d : E,
      Function.update (![a, b, c, d] : Fin 4 → E) 3 d = ![a, b, c, d] := by
    intro a b c d; funext z; fin_cases z <;> rfl
  have hupd2 : ∀ a b c d : E,
      Function.update (![a, b, c, d] : Fin 4 → E) 2 c = ![a, b, c, d] := by
    intro a b c d; funext z; fin_cases z <;> rfl
  have hupd0 : ∀ a b c d : E,
      Function.update (![a, b, c, d] : Fin 4 → E) 0 a = ![a, b, c, d] := by
    intro a b c d; funext z; fin_cases z <;> rfl
  have hupd1 : ∀ a b c d : E,
      Function.update (![a, b, c, d] : Fin 4 → E) 1 b = ![a, b, c, d] := by
    intro a b c d; funext z; fin_cases z <;> rfl
  have hv0 : ∑ i : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i • (chartModelBasis E) i = v 0 :=
    (chartModelBasis E).sum_repr (v 0)
  have hv1 : ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 1)) k • (chartModelBasis E) k = v 1 :=
    (chartModelBasis E).sum_repr (v 1)
  -- the common middle form
  set mid : ℝ := ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g₁ α α j l *
      Wm ![(chartModelBasis E) j, (chartModelBasis E) l, v 0, v 1] with hmid
  -- Wm-tuple multilinear reconstruction of v0,v1 in slots 2,3
  have hmid_expand : mid =
      ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ α α j l *
              Wm ![(chartModelBasis E) j, (chartModelBasis E) l,
                (chartModelBasis E) i, (chartModelBasis E) k]) := by
    rw [hmid]
    have hexp : ∀ j l : Fin (Module.finrank ℝ E),
        Wm ![(chartModelBasis E) j, (chartModelBasis E) l, v 0, v 1] =
          ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
              Wm ![(chartModelBasis E) j, (chartModelBasis E) l,
                (chartModelBasis E) i, (chartModelBasis E) k] := by
      intro j l
      have ht2 : (![(chartModelBasis E) j, (chartModelBasis E) l, v 0, v 1] : Fin 4 → E) =
          Function.update (![(chartModelBasis E) j, (chartModelBasis E) l,
              (0 : E), v 1] : Fin 4 → E) 2
            (∑ i : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) i • (chartModelBasis E) i) := by
        funext z; fin_cases z
        · rfl
        · rfl
        · exact hv0.symm
        · rfl
      rw [ht2, cmm4_slot_sum_smul Wm 2 (fun i => ((chartModelBasis E).repr (v 0)) i)
        (fun i => (chartModelBasis E) i)
        (![(chartModelBasis E) j, (chartModelBasis E) l, (0 : E), v 1])]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have ht2i : Function.update (![(chartModelBasis E) j, (chartModelBasis E) l, (0 : E), v 1]
              : Fin 4 → E) 2 ((chartModelBasis E) i) =
            ![(chartModelBasis E) j, (chartModelBasis E) l, (chartModelBasis E) i, v 1] := by
        funext z; fin_cases z <;> rfl
      rw [ht2i]
      have ht3 : (![(chartModelBasis E) j, (chartModelBasis E) l, (chartModelBasis E) i, v 1]
            : Fin 4 → E) =
          Function.update (![(chartModelBasis E) j, (chartModelBasis E) l,
              (chartModelBasis E) i, (0 : E)] : Fin 4 → E) 3
            (∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 1)) k • (chartModelBasis E) k) := by
        funext z; fin_cases z
        · rfl
        · rfl
        · rfl
        · exact hv1.symm
      rw [ht3, cmm4_slot_sum_smul Wm 3 (fun k => ((chartModelBasis E).repr (v 1)) k)
        (fun k => (chartModelBasis E) k)
        (![(chartModelBasis E) j, (chartModelBasis E) l, (chartModelBasis E) i, (0 : E)])]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have ht3k : Function.update (![(chartModelBasis E) j, (chartModelBasis E) l,
              (chartModelBasis E) i, (0 : E)] : Fin 4 → E) 3 ((chartModelBasis E) k) =
            ![(chartModelBasis E) j, (chartModelBasis E) l, (chartModelBasis E) i,
              (chartModelBasis E) k] := by
        funext z; fin_cases z <;> rfl
      rw [ht3k]
      ring
    rw [show (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ α α j l *
            Wm ![(chartModelBasis E) j, (chartModelBasis E) l, v 0, v 1]) =
        ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ α α j l *
            ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
                Wm ![(chartModelBasis E) j, (chartModelBasis E) l,
                  (chartModelBasis E) i, (chartModelBasis E) k] from by
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [hexp j l]]
    -- reorder ∑_jl ∑_ik → ∑_ik ∑_jl via product-index Fubini
    have hflip : ∀ (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
        (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E), F j l i k) =
          ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), F j l i k := by
      intro F
      have hL : (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E), F j l i k) =
          ∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), F p.1 p.2 q.1 q.2 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
        rw [Fintype.sum_prod_type]
      have hR : (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E), F j l i k) =
          ∑ q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), F p.1 p.2 q.1 q.2 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
        rw [Fintype.sum_prod_type]
      rw [hL, hR, Finset.sum_comm]
    rw [show (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ α α j l *
            ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
                Wm ![(chartModelBasis E) j, (chartModelBasis E) l,
                  (chartModelBasis E) i, (chartModelBasis E) k]) =
        ∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
              (chartInvGramMatrix (I := I) g₁ α α j l *
                Wm ![(chartModelBasis E) j, (chartModelBasis E) l,
                  (chartModelBasis E) i, (chartModelBasis E) k]) from by
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
    rw [hflip (fun j l i k => ((chartModelBasis E).repr (v 0)) i *
      ((chartModelBasis E).repr (v 1)) k *
      (chartInvGramMatrix (I := I) g₁ α α j l *
        Wm ![(chartModelBasis E) j, (chartModelBasis E) l,
          (chartModelBasis E) i, (chartModelBasis E) k]))]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
  -- theorem LHS = mid
  have hLHSmid : (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2) W α ![] ![j, l, i, k] α)) =
      mid := by
    rw [hmid_expand]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    congr 1
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [hcomp j l i k, chartInvGramOnE_extChartAt_self (I := I) g₁ α j l]
  -- RHS = mid via the appCc brick + hraise reconstruction
  have hRHSmid : unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) g₀ g₁) W) α v =
      mid := by
    rw [ricciArmPrincipalCoeffPure_appCc_eq_roughLaplacian (I := I) (M := M) g₀ g₁ W α v]
    rw [hmid]
    -- each k'-summand: expand raisedCovec in chart basis (slot 0), collapse finB k' (slot 1)
    have hsumk : ∀ k' : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4 W α
            (Fin.cons (cometricLmodel (I := I) g₁ α
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k')))
              (Fin.cons ((Module.finBasis ℝ E) k') v)) =
          ∑ j : Fin (Module.finrank ℝ E),
            (∑ n : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ α α j n *
                ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n)) *
              Wm ![(chartModelBasis E) j, (Module.finBasis ℝ E) k', v 0, v 1] := by
      intro k'
      rw [show (Fin.cons (cometricLmodel (I := I) g₁ α
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k')))
              (Fin.cons ((Module.finBasis ℝ E) k') v) : Fin 4 → E) =
          Function.update (![(0 : E), (Module.finBasis ℝ E) k', v 0, v 1] : Fin 4 → E) 0
            (∑ j : Fin (Module.finrank ℝ E),
              (∑ n : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g₁ α α j n *
                  ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n)) •
                (chartModelBasis E) j) from by
        rw [← hraise k']
        funext z; fin_cases z <;> rfl]
      rw [show Wm = unitModel (I := I) (M := M) g₀ 4 W α from rfl] at *
      rw [cmm4_slot_sum_smul (unitModel (I := I) (M := M) g₀ 4 W α) 0
        (fun j => ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ α α j n *
            ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n))
        (fun j => (chartModelBasis E) j)
        (![(0 : E), (Module.finBasis ℝ E) k', v 0, v 1])]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show Function.update (![(0 : E), (Module.finBasis ℝ E) k', v 0, v 1] : Fin 4 → E) 0
            ((chartModelBasis E) j) =
          ![(chartModelBasis E) j, (Module.finBasis ℝ E) k', v 0, v 1] from by
        funext z; fin_cases z <;> rfl]
    rw [Finset.sum_congr rfl (fun k' _ => hsumk k')]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- collapse ∑_k' against finB k' (slot 1) via Basis.sum_repr
    have hcollapse : (∑ k' : Fin (Module.finrank ℝ E),
          (∑ n : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ α α j n *
              ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n)) *
            Wm ![(chartModelBasis E) j, (Module.finBasis ℝ E) k', v 0, v 1]) =
        ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ α α j n *
            Wm ![(chartModelBasis E) j, (chartModelBasis E) n, v 0, v 1] := by
      have hexpand : ∀ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g₁ α α j n *
              Wm ![(chartModelBasis E) j, (chartModelBasis E) n, v 0, v 1] =
            ∑ k' : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ α α j n *
                ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n) *
                  Wm ![(chartModelBasis E) j, (Module.finBasis ℝ E) k', v 0, v 1] := by
        intro n
        have hrec : (∑ k' : Fin (Module.finrank ℝ E),
              ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n) •
                (Module.finBasis ℝ E) k') = (chartModelBasis E) n := by
          have : ∀ k' : Fin (Module.finrank ℝ E),
              ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n) =
                ((Module.finBasis ℝ E).repr ((chartModelBasis E) n)) k' := by
            intro k'
            change (Module.finBasis ℝ E).dualBasis k' ((chartModelBasis E) n) = _
            rw [Module.Basis.dualBasis_apply]
          simp only [this]
          exact (Module.finBasis ℝ E).sum_repr ((chartModelBasis E) n)
        have hslot1 : Wm ![(chartModelBasis E) j, (chartModelBasis E) n, v 0, v 1] =
            ∑ k' : Fin (Module.finrank ℝ E),
              ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n) *
                Wm ![(chartModelBasis E) j, (Module.finBasis ℝ E) k', v 0, v 1] := by
          have ht1 : (![(chartModelBasis E) j, (chartModelBasis E) n, v 0, v 1] : Fin 4 → E) =
              Function.update (![(chartModelBasis E) j, (0 : E), v 0, v 1] : Fin 4 → E) 1
                (∑ k' : Fin (Module.finrank ℝ E),
                  ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n) •
                    (Module.finBasis ℝ E) k') := by
            funext z; fin_cases z
            · rfl
            · exact hrec.symm
            · rfl
            · rfl
          rw [ht1, cmm4_slot_sum_smul Wm 1
            (fun k' => ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n))
            (fun k' => (Module.finBasis ℝ E) k')
            (![(chartModelBasis E) j, (0 : E), v 0, v 1])]
          refine Finset.sum_congr rfl (fun k' _ => ?_)
          rw [show Function.update (![(chartModelBasis E) j, (0 : E), v 0, v 1] : Fin 4 → E) 1
                ((Module.finBasis ℝ E) k') =
              ![(chartModelBasis E) j, (Module.finBasis ℝ E) k', v 0, v 1] from by
            funext z; fin_cases z <;> rfl]
        rw [hslot1, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        ring
      rw [show (∑ n : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g₁ α α j n *
              Wm ![(chartModelBasis E) j, (chartModelBasis E) n, v 0, v 1]) =
          ∑ n : Fin (Module.finrank ℝ E),
            ∑ k' : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g₁ α α j n *
                ((Module.finBasis ℝ E).cDualBasis k') ((chartModelBasis E) n) *
                  Wm ![(chartModelBasis E) j, (Module.finBasis ℝ E) k', v 0, v 1] from by
        refine Finset.sum_congr rfl (fun n _ => hexpand n)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k' _ => ?_)
      rw [Finset.sum_mul]
    rw [hcollapse]
  rw [hLHSmid, hRHSmid]

theorem chartRicciSecondOrderPrincipalSymbol_eq_appCc_iteratedCovGrad
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (α : M)
    (h : ChartMetricPerturbation E)
    (hlink : ∀ a b : Fin (Module.finrank ℝ E),
      (fun y => h.toFun a b y) =ᶠ[nhds (extChartAt I α α)]
        (fun y => tensorChartComponentRaw (I := I) (M := M) g₀ 0 2 S α ![] ![a, b]
          ((extChartAt I α).symm y)))
    (v : Fin 2 → TangentSpace I α) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          ((-2 : ℝ) * chartRicciSecondOrderPrincipalSymbol (I := I) g₁ α h i k (extChartAt I α α) +
            chartDeTurckCorrPrincipalSymbolExpr (I := I) g₁ g₁ α h i k (extChartAt I α α))) =
      unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S)) α v
        - (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
              chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α)) := by
  classical
  have hyint : (extChartAt I α α) ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α (mem_extChartAt_target α)
  have hgauge : ∀ i k : Fin (Module.finrank ℝ E),
      (-2 : ℝ) * chartRicciSecondOrderPrincipalSymbol (I := I) g₁ α h i k (extChartAt I α α) +
          chartDeTurckCorrPrincipalSymbolExpr (I := I) g₁ g₁ α h i k (extChartAt I α α) =
        chartRoughLaplacianSymbol (I := I) g₁ α h i k (extChartAt I α α) :=
    fun i k => chartRicciDeTurck_gaugeCancellation_principalSymbol (I := I) g₁ g₁ α h i k hyint
  have hhessian : ∀ i k : Fin (Module.finrank ℝ E),
      chartRoughLaplacianSymbol (I := I) g₁ α h i k (extChartAt I α α) =
        (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
              tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
                (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α)
          - chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α) := by
    intro i k
    have := chartRoughLaplacianSymbol_eq_chartInvGram_iteratedCovGrad
      (I := I) g₀ g₁ S α h i k hlink
    simpa using this
  calc
    (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
          ((-2 : ℝ) * chartRicciSecondOrderPrincipalSymbol (I := I) g₁ α h i k (extChartAt I α α) +
            chartDeTurckCorrPrincipalSymbolExpr (I := I) g₁ g₁ α h i k (extChartAt I α α)))
        = ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
              ((∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α)
                - chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α)) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
          rw [hgauge i k, hhessian i k]
      _ = (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
                (∑ j : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g₁ α j l (extChartAt I α α) *
                    tensorChartComponentRaw (I := I) (M := M) g₀ 0 (2 + 2)
                      (iteratedCovGrad (I := I) g₀ 0 2 2 S) α ![] ![j, l, i, k] α))
            - (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
                ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
                  chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          ring
      _ = unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 4 2 (ricciArmPrincipalCoeffPure (I := I) g₀ g₁)
              (iteratedCovGrad (I := I) g₀ 0 2 2 S)) α v
          - (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
              ((chartModelBasis E).repr (v 0)) i * ((chartModelBasis E).repr (v 1)) k *
                chartRoughLaplacianLowerCorr (I := I) g₀ g₁ S α i k (extChartAt I α α)) := by
          rw [chartInvGram_iteratedCovGrad_trace_eq_unitModel_appCc (I := I) g₀ g₁ S α v]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
