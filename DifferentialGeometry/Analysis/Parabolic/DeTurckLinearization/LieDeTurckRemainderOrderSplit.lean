import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization

noncomputable section
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
open Set Function
open scoped Topology ContDiff Matrix Manifold BigOperators
namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace DeTurckLinearization
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

private lemma partial_chartGramOnE_differentiableAt'
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

private lemma chartChristoffel_differentiableAt'
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (fun y => chartChristoffel (I := I) g α i j k y) y₀ := by
  classical
  have heq : (fun y => chartChristoffel (I := I) g α i j k y) =
      (fun y => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α k l y * gramBracket (I := I) g α i j l y) := by
    funext y; rw [chartChristoffel_eq_sum_invGramOnE_bracket]
  rw [heq]
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.fun_sum (fun l _ => ?_)
  refine DifferentiableAt.mul (chartInvGramOnE_differentiableAt_interior (I := I) g α k l hy) ?_
  unfold gramBracket
  exact ((partial_chartGramOnE_differentiableAt' (I := I) g α i l j hy).add
    (partial_chartGramOnE_differentiableAt' (I := I) g α j l i hy)).sub
    (partial_chartGramOnE_differentiableAt' (I := I) g α l i j hy)

private lemma christoffelFirstOrderCorr_differentiableAt'
    {g₀ : SmoothRiemannianMetric I M} {α : M} {h : ChartMetricPerturbation E}
    {i j k : Fin (Module.finrank ℝ E)} {y₀ : E}
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ
      (fun y => christoffelFirstOrderCorr (I := I) g₀ α h i j k y) y₀ := by
  classical
  unfold christoffelFirstOrderCorr
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.fun_sum (fun l _ => ?_)
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.neg ?_
    refine DifferentiableAt.fun_sum (fun q _ => ?_)
    refine DifferentiableAt.fun_sum (fun p _ => ?_)
    refine DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_
    · exact chartInvGramOnE_differentiableAt_interior (I := I) g₀ α k p hy
    · exact (h.differentiableAt p q y₀)
    · exact chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q l hy
  · unfold gramBracket
    refine DifferentiableAt.sub (DifferentiableAt.add ?_ ?_) ?_
    · exact partial_chartGramOnE_differentiableAt' (I := I) g₀ α i l j hy
    · exact partial_chartGramOnE_differentiableAt' (I := I) g₀ α j l i hy
    · exact partial_chartGramOnE_differentiableAt' (I := I) g₀ α l i j hy

private lemma partialDeriv_invGramCoeff_split
    (g₀ : SmoothRiemannianMetric I M) (α : M) (h : ChartMetricPerturbation E)
    (m a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m
      (fun y' => -(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
          chartInvGramOnE (I := I) g₀ α q b y')) y
    = -(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α a p) y * h p q y *
            chartInvGramOnE (I := I) g₀ α q b y +
          chartInvGramOnE (I := I) g₀ α a p y * h p q y *
            partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q b) y))
      + -(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α a p y * partialDeriv (E := E) m (h p q) y *
          chartInvGramOnE (I := I) g₀ α q b y) := by
  classical
  have hdiff : ∀ q r : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y' => chartInvGramOnE (I := I) g₀ α a r y' * h r q y' *
        chartInvGramOnE (I := I) g₀ α q b y') y :=
    fun q r => ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a r hy).mul
      (h.differentiableAt r q y)).mul
      (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q b hy)
  rw [show (fun y' => -(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
          chartInvGramOnE (I := I) g₀ α q b y')) =
      (fun y' => (-1 : ℝ) * ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
          chartInvGramOnE (I := I) g₀ α q b y') from by funext y'; ring]
  rw [partialDeriv_const_mul (E := E) (-1 : ℝ) _
        (DifferentiableAt.fun_sum (fun q _ => DifferentiableAt.fun_sum (fun p _ => hdiff q p)))]
  rw [partialDeriv_sum Finset.univ _ (fun q _ => DifferentiableAt.fun_sum (fun p _ => hdiff q p))]
  have hinner : ∀ q : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) m (fun y' => ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
          chartInvGramOnE (I := I) g₀ α q b y') y
      = ∑ p : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α a p) y * h p q y *
            chartInvGramOnE (I := I) g₀ α q b y +
          chartInvGramOnE (I := I) g₀ α a p y * partialDeriv (E := E) m (h p q) y *
            chartInvGramOnE (I := I) g₀ α q b y +
          chartInvGramOnE (I := I) g₀ α a p y * h p q y *
            partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q b) y) := by
    intro q
    rw [partialDeriv_sum Finset.univ _ (fun p _ => hdiff q p)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [partialDeriv_mul (E := E) (fun y' => chartInvGramOnE (I := I) g₀ α a p y' * h p q y')
          (chartInvGramOnE (I := I) g₀ α q b)
          ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a p hy).mul
            (h.differentiableAt p q y))
          (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q b hy)]
    rw [partialDeriv_mul (E := E) (chartInvGramOnE (I := I) g₀ α a p) (h p q)
          (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a p hy)
          (h.differentiableAt p q y)]
    ring
  have hstep : ∑ q : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) m (fun y' => ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
          chartInvGramOnE (I := I) g₀ α q b y') y
      = ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α a p) y * h p q y *
            chartInvGramOnE (I := I) g₀ α q b y +
          chartInvGramOnE (I := I) g₀ α a p y * partialDeriv (E := E) m (h p q) y *
            chartInvGramOnE (I := I) g₀ α q b y +
          chartInvGramOnE (I := I) g₀ α a p y * h p q y *
            partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q b) y) :=
    Finset.sum_congr rfl (fun q _ => hinner q)
  rw [hstep]
  have hsplit : ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
        (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α a p) y * h p q y *
            chartInvGramOnE (I := I) g₀ α q b y +
          chartInvGramOnE (I := I) g₀ α a p y * partialDeriv (E := E) m (h p q) y *
            chartInvGramOnE (I := I) g₀ α q b y +
          chartInvGramOnE (I := I) g₀ α a p y * h p q y *
            partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q b) y)
      = (∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α a p) y * h p q y *
              chartInvGramOnE (I := I) g₀ α q b y +
            chartInvGramOnE (I := I) g₀ α a p y * h p q y *
              partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q b) y))
        + (∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₀ α a p y * partialDeriv (E := E) m (h p q) y *
            chartInvGramOnE (I := I) g₀ α q b y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  rw [hsplit]; ring

def deTurckVFFirstOrderCorrDeriv1 (g₀ g_bg : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (m k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₀ α a p y * partialDeriv (E := E) m (h p q) y *
            chartInvGramOnE (I := I) g₀ α q b y)) *
        (chartChristoffel (I := I) g₀ α a b k y - chartChristoffel (I := I) g_bg α a b k y) +
      chartInvGramOnE (I := I) g₀ α a b y *
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α k p y * partialDeriv (E := E) m (h p q) y *
                chartInvGramOnE (I := I) g₀ α q l y)) *
            gramBracket (I := I) g₀ α a b l y))

def deTurckVFFirstOrderCorrDeriv0 (g₀ g_bg : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (m k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α a p) y * h p q y *
              chartInvGramOnE (I := I) g₀ α q b y +
            chartInvGramOnE (I := I) g₀ α a p y * h p q y *
              partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q b) y))) *
        (chartChristoffel (I := I) g₀ α a b k y - chartChristoffel (I := I) g_bg α a b k y) +
      (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₀ α a p y * h p q y *
            chartInvGramOnE (I := I) g₀ α q b y)) *
        partialDeriv (E := E) m (fun y' => chartChristoffel (I := I) g₀ α a b k y' -
          chartChristoffel (I := I) g_bg α a b k y') y +
      partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α a b) y *
        christoffelFirstOrderCorr (I := I) g₀ α h a b k y +
      chartInvGramOnE (I := I) g₀ α a b y *
        ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α k p) y * h p q y *
                    chartInvGramOnE (I := I) g₀ α q l y +
                  chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                    partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q l) y))) *
              gramBracket (I := I) g₀ α a b l y +
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                  chartInvGramOnE (I := I) g₀ α q l y)) *
              partialDeriv (E := E) m (gramBracket (I := I) g₀ α a b l) y)))

private lemma partialDeriv_christoffelFirstOrderCorr_split
    (g₀ : SmoothRiemannianMetric I M) (α : M) (h : ChartMetricPerturbation E)
    (m a b k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h a b k y') y
    = ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α k p) y * h p q y *
                  chartInvGramOnE (I := I) g₀ α q l y +
                chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                  partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q l) y))) *
            gramBracket (I := I) g₀ α a b l y +
          (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                chartInvGramOnE (I := I) g₀ α q l y)) *
            partialDeriv (E := E) m (gramBracket (I := I) g₀ α a b l) y))
      + ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α k p y * partialDeriv (E := E) m (h p q) y *
                chartInvGramOnE (I := I) g₀ α q l y)) *
            gramBracket (I := I) g₀ α a b l y) := by
  classical
  have hCdiff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y' => -(∑ q : Fin (Module.finrank ℝ E),
        ∑ p : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g₀ α k p y' * h p q y' *
          chartInvGramOnE (I := I) g₀ α q l y')) y := by
    intro l
    refine DifferentiableAt.neg ?_
    refine DifferentiableAt.fun_sum (fun q _ => DifferentiableAt.fun_sum (fun p _ => ?_))
    exact ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α k p hy).mul
      (h.differentiableAt p q y)).mul
      (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q l hy)
  have hgBdiff : ∀ l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (gramBracket (I := I) g₀ α a b l) y := by
    intro l
    unfold gramBracket
    exact ((partial_chartGramOnE_differentiableAt' (I := I) g₀ α a l b hy).add
      (partial_chartGramOnE_differentiableAt' (I := I) g₀ α b l a hy)).sub
      (partial_chartGramOnE_differentiableAt' (I := I) g₀ α l a b hy)
  rw [show (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h a b k y') =
      (fun y' => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α k p y' * h p q y' *
              chartInvGramOnE (I := I) g₀ α q l y')) *
          gramBracket (I := I) g₀ α a b l y') from by funext y'; rw [christoffelFirstOrderCorr]]
  rw [partialDeriv_const_mul (E := E) (1 / 2 : ℝ)
        (fun y' => ∑ l : Fin (Module.finrank ℝ E),
          (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α k p y' * h p q y' *
                chartInvGramOnE (I := I) g₀ α q l y')) *
            gramBracket (I := I) g₀ α a b l y')
        (DifferentiableAt.fun_sum (fun l _ => (hCdiff l).mul (hgBdiff l)))]
  rw [partialDeriv_sum Finset.univ
        (fun l y' => (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α k p y' * h p q y' *
              chartInvGramOnE (I := I) g₀ α q l y')) *
          gramBracket (I := I) g₀ α a b l y')
        (fun l _ => (hCdiff l).mul (hgBdiff l))]
  have hl : ∀ l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) m (fun y' =>
        (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α k p y' * h p q y' *
              chartInvGramOnE (I := I) g₀ α q l y')) *
          gramBracket (I := I) g₀ α a b l y') y
      = ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α k p) y * h p q y *
                  chartInvGramOnE (I := I) g₀ α q l y +
                chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                  partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q l) y))) *
            gramBracket (I := I) g₀ α a b l y +
          (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                chartInvGramOnE (I := I) g₀ α q l y)) *
            partialDeriv (E := E) m (gramBracket (I := I) g₀ α a b l) y)
        + (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α k p y * partialDeriv (E := E) m (h p q) y *
              chartInvGramOnE (I := I) g₀ α q l y)) *
          gramBracket (I := I) g₀ α a b l y := by
    intro l
    rw [partialDeriv_mul (E := E)
          (fun y' => -(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α k p y' * h p q y' *
              chartInvGramOnE (I := I) g₀ α q l y'))
          (gramBracket (I := I) g₀ α a b l) (hCdiff l) (hgBdiff l)]
    rw [partialDeriv_invGramCoeff_split (I := I) g₀ α h m k l hy]
    ring
  have hstep : ∑ l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) m (fun y' =>
        (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α k p y' * h p q y' *
              chartInvGramOnE (I := I) g₀ α q l y')) *
          gramBracket (I := I) g₀ α a b l y') y
      = ∑ l : Fin (Module.finrank ℝ E),
        (((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α k p) y * h p q y *
                    chartInvGramOnE (I := I) g₀ α q l y +
                  chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                    partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q l) y))) *
              gramBracket (I := I) g₀ α a b l y +
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                  chartInvGramOnE (I := I) g₀ α q l y)) *
              partialDeriv (E := E) m (gramBracket (I := I) g₀ α a b l) y)
          + (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α k p y * partialDeriv (E := E) m (h p q) y *
                chartInvGramOnE (I := I) g₀ α q l y)) *
            gramBracket (I := I) g₀ α a b l y) :=
    Finset.sum_congr rfl (fun l _ => hl l)
  rw [hstep, Finset.sum_add_distrib, mul_add]

private lemma partialDeriv_deTurckVFFirstOrderCorr_cell
    (g₀ g_bg : SmoothRiemannianMetric I M) (α : M) (h : ChartMetricPerturbation E)
    (m k a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (fun y' =>
      (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
              chartInvGramOnE (I := I) g₀ α q b y')) *
          (chartChristoffel (I := I) g₀ α a b k y' -
            chartChristoffel (I := I) g_bg α a b k y') +
        chartInvGramOnE (I := I) g₀ α a b y' *
          christoffelFirstOrderCorr (I := I) g₀ α h a b k y') y
    = ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α a p) y * h p q y *
                chartInvGramOnE (I := I) g₀ α q b y +
              chartInvGramOnE (I := I) g₀ α a p y * h p q y *
                partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q b) y))) *
          (chartChristoffel (I := I) g₀ α a b k y - chartChristoffel (I := I) g_bg α a b k y) +
        (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α a p y * h p q y *
              chartInvGramOnE (I := I) g₀ α q b y)) *
          partialDeriv (E := E) m (fun y' => chartChristoffel (I := I) g₀ α a b k y' -
            chartChristoffel (I := I) g_bg α a b k y') y +
        partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α a b) y *
          christoffelFirstOrderCorr (I := I) g₀ α h a b k y +
        chartInvGramOnE (I := I) g₀ α a b y *
          ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α k p) y * h p q y *
                      chartInvGramOnE (I := I) g₀ α q l y +
                    chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                      partialDeriv (E := E) m (chartInvGramOnE (I := I) g₀ α q l) y))) *
                gramBracket (I := I) g₀ α a b l y +
              (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g₀ α k p y * h p q y *
                    chartInvGramOnE (I := I) g₀ α q l y)) *
                partialDeriv (E := E) m (gramBracket (I := I) g₀ α a b l) y)))
      + ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α a p y * partialDeriv (E := E) m (h p q) y *
              chartInvGramOnE (I := I) g₀ α q b y)) *
          (chartChristoffel (I := I) g₀ α a b k y - chartChristoffel (I := I) g_bg α a b k y) +
        chartInvGramOnE (I := I) g₀ α a b y *
          ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
            (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
                chartInvGramOnE (I := I) g₀ α k p y * partialDeriv (E := E) m (h p q) y *
                  chartInvGramOnE (I := I) g₀ α q l y)) *
              gramBracket (I := I) g₀ α a b l y)) := by
  classical
  have hCdiff : DifferentiableAt ℝ (fun y' => -(∑ q : Fin (Module.finrank ℝ E),
      ∑ p : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
        chartInvGramOnE (I := I) g₀ α q b y')) y := by
    refine DifferentiableAt.neg ?_
    refine DifferentiableAt.fun_sum (fun q _ => DifferentiableAt.fun_sum (fun p _ => ?_))
    exact ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a p hy).mul
      (h.differentiableAt p q y)).mul
      (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q b hy)
  have hΓdiff : DifferentiableAt ℝ (fun y' => chartChristoffel (I := I) g₀ α a b k y' -
      chartChristoffel (I := I) g_bg α a b k y') y :=
    (chartChristoffel_differentiableAt' (I := I) g₀ α a b k hy).sub
      (chartChristoffel_differentiableAt' (I := I) g_bg α a b k hy)
  have hiGdiff : DifferentiableAt ℝ (chartInvGramOnE (I := I) g₀ α a b) y :=
    chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a b hy
  have hcfocdiff : DifferentiableAt ℝ
      (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h a b k y') y :=
    christoffelFirstOrderCorr_differentiableAt' (I := I) (g₀ := g₀) hy
  rw [partialDeriv_add (E := E)
        (fun y' => (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
              chartInvGramOnE (I := I) g₀ α q b y')) *
          (chartChristoffel (I := I) g₀ α a b k y' -
            chartChristoffel (I := I) g_bg α a b k y'))
        (fun y' => chartInvGramOnE (I := I) g₀ α a b y' *
          christoffelFirstOrderCorr (I := I) g₀ α h a b k y')
        (hCdiff.mul hΓdiff) (hiGdiff.mul hcfocdiff)]
  rw [partialDeriv_mul (E := E)
        (fun y' => -(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
            chartInvGramOnE (I := I) g₀ α q b y'))
        (fun y' => chartChristoffel (I := I) g₀ α a b k y' -
          chartChristoffel (I := I) g_bg α a b k y') hCdiff hΓdiff]
  rw [partialDeriv_mul (E := E) (chartInvGramOnE (I := I) g₀ α a b)
        (fun y' => christoffelFirstOrderCorr (I := I) g₀ α h a b k y') hiGdiff hcfocdiff]
  rw [partialDeriv_invGramCoeff_split (I := I) g₀ α h m a b hy]
  rw [partialDeriv_christoffelFirstOrderCorr_split (I := I) g₀ α h m a b k hy]
  ring

theorem partialDeriv_deTurckVFFirstOrderCorr
    (g₀ g_bg : SmoothRiemannianMetric I M) (α : M) (h : ChartMetricPerturbation E)
    (m k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    partialDeriv (E := E) m (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') y
    = deTurckVFFirstOrderCorrDeriv0 (I := I) g₀ g_bg α h m k y +
      deTurckVFFirstOrderCorrDeriv1 (I := I) g₀ g_bg α h m k y := by
  classical
  have hsummand_diff : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y' =>
        (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
              chartInvGramOnE (I := I) g₀ α q b y')) *
            (chartChristoffel (I := I) g₀ α a b k y' -
              chartChristoffel (I := I) g_bg α a b k y') +
          chartInvGramOnE (I := I) g₀ α a b y' *
            christoffelFirstOrderCorr (I := I) g₀ α h a b k y') y := by
    intro a b
    refine DifferentiableAt.add (DifferentiableAt.mul ?_ ?_) ?_
    · refine DifferentiableAt.neg ?_
      refine DifferentiableAt.fun_sum (fun q _ => DifferentiableAt.fun_sum (fun p _ => ?_))
      exact ((chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a p hy).mul
        (h.differentiableAt p q y)).mul
        (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α q b hy)
    · exact (chartChristoffel_differentiableAt' (I := I) g₀ α a b k hy).sub
        (chartChristoffel_differentiableAt' (I := I) g_bg α a b k hy)
    · exact (chartInvGramOnE_differentiableAt_interior (I := I) g₀ α a b hy).mul
        (christoffelFirstOrderCorr_differentiableAt' (I := I) (g₀ := g₀) hy)
  rw [show (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') =
      (fun y' => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g₀ α a p y' * h p q y' *
                chartInvGramOnE (I := I) g₀ α q b y')) *
            (chartChristoffel (I := I) g₀ α a b k y' -
              chartChristoffel (I := I) g_bg α a b k y') +
          chartInvGramOnE (I := I) g₀ α a b y' *
            christoffelFirstOrderCorr (I := I) g₀ α h a b k y')) from by
        funext y'; rw [deTurckVFFirstOrderCorr]]
  rw [partialDeriv_sum Finset.univ _
        (fun a _ => DifferentiableAt.fun_sum (fun b _ => hsummand_diff a b))]
  rw [deTurckVFFirstOrderCorrDeriv0, deTurckVFFirstOrderCorrDeriv1]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [partialDeriv_sum Finset.univ _ (fun b _ => hsummand_diff a b)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  exact partialDeriv_deTurckVFFirstOrderCorr_cell (I := I) g₀ g_bg α h m k a b hy

def order0Part (g₀ g_bg : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y *
        partialDeriv (E := E) k (chartGramOnE (I := I) g₀ α i j) y) +
  (∑ k : Fin (Module.finrank ℝ E),
      h k j y * partialDeriv (E := E) i (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y) +
  (∑ k : Fin (Module.finrank ℝ E),
      h i k y * partialDeriv (E := E) j (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g₀ α k j y *
        deTurckVFFirstOrderCorrDeriv0 (I := I) g₀ g_bg α h i k y) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g₀ α i k y *
        deTurckVFFirstOrderCorrDeriv0 (I := I) g₀ g_bg α h j k y)

def order1Part (g₀ g_bg : SmoothRiemannianMetric I M) (α : M)
    (h : ChartMetricPerturbation E) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ k : Fin (Module.finrank ℝ E),
      chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y *
        partialDeriv (E := E) k (chartGramOnE (I := I) g₀ α i j) y) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartDeTurckVFComp (I := I) g₀ g_bg α k y * partialDeriv (E := E) k (h i j) y) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g₀ α k j y *
        deTurckVFFirstOrderCorrDeriv1 (I := I) g₀ g_bg α h i k y) +
  (∑ k : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g₀ α i k y *
        deTurckVFFirstOrderCorrDeriv1 (I := I) g₀ g_bg α h j k y)

theorem lieDerivFirstOrderRemainder_eq_order0_add_order1
    (g₀ g_bg : SmoothRiemannianMetric I M) (α : M) (h : ChartMetricPerturbation E)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    lieDerivFirstOrderRemainder (I := I) g₀ g_bg α h i j y
    = order0Part (I := I) g₀ g_bg α h i j y + order1Part (I := I) g₀ g_bg α h i j y := by
  classical
  rw [lieDerivFirstOrderRemainder]
  have hA : (∑ k : Fin (Module.finrank ℝ E),
        ((chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y +
              deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y) *
            partialDeriv (E := E) k (chartGramOnE (I := I) g₀ α i j) y +
          chartDeTurckVFComp (I := I) g₀ g_bg α k y * partialDeriv (E := E) k (h i j) y))
      = (∑ k : Fin (Module.finrank ℝ E),
          chartLinearizedDeTurckVFPrincipal (I := I) g₀ g_bg α h k y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g₀ α i j) y)
        + (∑ k : Fin (Module.finrank ℝ E),
          deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g₀ α i j) y)
        + (∑ k : Fin (Module.finrank ℝ E),
          chartDeTurckVFComp (I := I) g₀ g_bg α k y * partialDeriv (E := E) k (h i j) y) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hB : (∑ k : Fin (Module.finrank ℝ E),
        (h k j y *
            partialDeriv (E := E) i (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y +
          chartGramOnE (I := I) g₀ α k j y *
            partialDeriv (E := E) i
              (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') y))
      = (∑ k : Fin (Module.finrank ℝ E),
          h k j y * partialDeriv (E := E) i (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y)
        + (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g₀ α k j y *
            deTurckVFFirstOrderCorrDeriv0 (I := I) g₀ g_bg α h i k y)
        + (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g₀ α k j y *
            deTurckVFFirstOrderCorrDeriv1 (I := I) g₀ g_bg α h i k y) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [partialDeriv_deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h i k hy]
    ring
  have hC : (∑ k : Fin (Module.finrank ℝ E),
        (h i k y *
            partialDeriv (E := E) j (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y +
          chartGramOnE (I := I) g₀ α i k y *
            partialDeriv (E := E) j
              (fun y' => deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h k y') y))
      = (∑ k : Fin (Module.finrank ℝ E),
          h i k y * partialDeriv (E := E) j (fun y' => chartDeTurckVFComp (I := I) g₀ g_bg α k y') y)
        + (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g₀ α i k y *
            deTurckVFFirstOrderCorrDeriv0 (I := I) g₀ g_bg α h j k y)
        + (∑ k : Fin (Module.finrank ℝ E),
          chartGramOnE (I := I) g₀ α i k y *
            deTurckVFFirstOrderCorrDeriv1 (I := I) g₀ g_bg α h j k y) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [partialDeriv_deTurckVFFirstOrderCorr (I := I) g₀ g_bg α h j k hy]
    ring
  rw [hA, hB, hC, order0Part, order1Part]
  ring

end DeTurckLinearization
end DeTurck
end PDE
end DifferentialGeometry
end
