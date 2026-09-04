import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Homogeneous
import DifferentialGeometry.Geometry.Comparison.BusemannLineSolution
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Metric Set Topology
open scoped ENNReal Manifold NNReal

namespace DifferentialGeometry

open Analysis.Laplacian.MetricExtension
open Analysis.Sobolev
open Geometry.Riemannian
open Geometry.Riemannian.BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The forward Busemann function of a minimizing line has local `W^{2,2}`
regularity in every manifold chart. -/
theorem busemann_chart_h2
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (α : M) :
    letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
    ∃ ρ : ℝ, 0 < ρ ∧
      Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (Chart.chartPushedRaw (I := I) (M := M) α
          (busemann (I := I) γ))
        (Metric.ball
          (toEuclidean (E := E) (extChartAt I α α)) ρ) := by
  classical
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let c : EuclN := toEuclidean (E := E) (extChartAt I α α)
  let u : EuclN → ℝ :=
    Chart.chartPushedRaw (I := I) (M := M) α (busemann (I := I) γ)
  obtain ⟨r, hr, A, s, hs, hA, hsol⟩ :=
    busemann_chart_data (I := I) g hEnorm hγ hd hRic α
  have hc_target :
      c ∈ Chart.chartTargetEuclid (I := I) (M := M) α := by
    refine ⟨extChartAt I α α,
      (extChartAt I α).map_source (mem_extChartAt_source (I := I) α), ?_⟩
    rfl
  let O : Set EuclN := Metric.ball c r ∩
    Chart.chartTargetEuclid (I := I) (M := M) α
  have hO_open : IsOpen O :=
    Metric.isOpen_ball.inter
      (Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)
  have hcO : c ∈ O := ⟨Metric.mem_ball_self hr, hc_target⟩
  have hsingleton_O : ({c} : Set EuclN) ⊆ O := by
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ hcO
  obtain ⟨δ, hδ, hδ_sub⟩ :=
    (isCompact_singleton : IsCompact ({c} : Set EuclN)).exists_cthickening_subset_open
      hO_open hsingleton_O
  let K : Set EuclN := Metric.cthickening δ ({c} : Set EuclN)
  have hK_compact : IsCompact K := by
    change IsCompact (Metric.cthickening δ ({c} : Set EuclN))
    rw [Metric.cthickening_singleton c hδ.le]
    exact isCompact_closedBall c δ
  have hK_ball : K ⊆ Metric.ball c r := fun x hx ↦ (hδ_sub hx).1
  have hK_target :
      K ⊆ Chart.chartTargetEuclid (I := I) (M := M) α :=
    fun x hx ↦ (hδ_sub hx).2
  obtain ⟨_, _, _, _, _, B, hB, hBc⟩ :=
    exists_smooth_metric_extension (I := I) g α hK_compact hK_target
  have hδ_fourth : 0 < δ / 4 := by positivity
  have hδ_half : 0 < δ / 2 := by positivity
  have hcore_supp :
      Metric.closedBall c (δ / 4) ⊆ Metric.ball c (δ / 2) := by
    exact Metric.closedBall_subset_ball (by linarith)
  obtain ⟨η, hη_smooth, hη_compact, hη_range, hη_one, hη_supp⟩ :=
    DeGiorgi.exists_smooth_cutoff (d := Module.finrank ℝ E)
      (isCompact_closedBall c (δ / 4)) Metric.isOpen_ball hcore_supp
  have hη_deriv_compact : HasCompactSupport (fderiv ℝ η) :=
    hη_compact.fderiv (𝕜 := ℝ)
  obtain ⟨C, hC⟩ := hη_deriv_compact.isCompact.exists_bound_of_continuousOn
    ((hη_smooth.continuous_fderiv (by simp)).continuousOn)
  let N : ℝ := max C 0
  have hη_deriv : ∀ x : EuclN, ‖fderiv ℝ η x‖ ≤ N := by
    intro x
    by_cases hx : x ∈ tsupport (fderiv ℝ η)
    · exact (hC x hx).trans (le_max_left _ _)
    · have hzero : fderiv ℝ η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [N, hzero]
  have hthick_K :
      Metric.cthickening (δ / 4) (tsupport η) ⊆ K := by
    calc
      Metric.cthickening (δ / 4) (tsupport η) ⊆
          Metric.cthickening (δ / 4) (Metric.ball c (δ / 2)) :=
        Metric.cthickening_subset_of_subset _ hη_supp
      _ = Metric.closedBall c (δ / 4 + δ / 2) :=
        cthickening_ball hδ_fourth.le hδ_half c
      _ ⊆ Metric.closedBall c δ :=
        Metric.closedBall_subset_closedBall (by linarith)
      _ = K := by
        change Metric.closedBall c δ = Metric.cthickening δ ({c} : Set EuclN)
        exact (Metric.cthickening_singleton c hδ.le).symm
  have hthick_ball :
      Metric.cthickening (δ / 4) (tsupport η) ⊆ Metric.ball c r :=
    hthick_K.trans hK_ball
  have hcoeff : ∀ x ∈ Metric.cthickening (δ / 4) (tsupport η),
      ∀ i j : Fin (Module.finrank ℝ E),
        A.1.a x i j = s * B.a x i j := by
    intro x hx i j
    rw [hA x (hthick_ball hx) i j, hB x (hthick_K hx) i j]
  have hB_zero : ∀ x : EuclN, B.c x = 0 := by
    intro x
    exact congrFun hBc x
  have hinner_compact : IsCompact (closure (Metric.ball c (δ / 4))) :=
    (isCompact_closedBall c (δ / 4)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hη_inner : ∀ x ∈ closure (Metric.ball c (δ / 4)), η x = 1 := by
    intro x hx
    exact hη_one x (Metric.closure_ball_subset_closedBall hx)
  let hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball c r) :=
    DeGiorgi.MemW1p.someWitness hsol.1.1
  refine ⟨δ / 4, hδ_fourth, ?_⟩
  simpa only [u, c] using
    (Analysis.Sobolev.NirenbergHomogeneous.homSol_memW2
      (d := Module.finrank ℝ E) (Omega := Metric.ball c r)
      Metric.isOpen_ball hu hsol B hs hη_smooth hη_compact hη_range
      hδ_fourth hthick_ball hcoeff hB_zero Metric.isOpen_ball hinner_compact
      hη_inner (N := N) hη_deriv)

end DifferentialGeometry
