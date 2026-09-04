import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.HomogeneousAllOrder
import DifferentialGeometry.Geometry.Comparison.BusemannLineSolution
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Metric Set Topology
open scoped ENNReal Manifold NNReal

namespace DifferentialGeometry

open Analysis.Laplacian.MetricExtension
open Analysis.Sobolev
open Analysis.Sobolev.IntrinsicLp
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

omit [I.Boundaryless]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private theorem contMDiffAt_of_raw
    (α : M) {f : M → ℝ}
    (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Chart.chartPushedRaw (I := I) (M := M) α f)
      ((toEuclidean (E := E)) (extChartAt I α α))) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f α := by
  let coord : M → EuclN := fun y =>
    (toEuclidean (E := E)) (extChartAt I α y)
  have hext : ContMDiffAt I 𝓘(ℝ, E) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (extChartAt I α) α :=
    contMDiffAt_extChartAt (I := I)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (x := α)
  have hto : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, EuclN)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (toEuclidean (E := E))
      (extChartAt I α α) :=
    contMDiffAt_iff_contDiffAt.mpr
      (toEuclidean (E := E)).contDiff.contDiffAt
  have hcoord : ContMDiffAt I 𝓘(ℝ, EuclN)
      ((⊤ : ℕ∞) : WithTop ℕ∞) coord α := by
    simpa only [coord, Function.comp_apply] using
      (hto.comp α hext)
  have hf' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Chart.chartPushedRaw (I := I) (M := M) α f) (coord α) := by
    simpa only [coord] using hf
  have hraw : ContMDiffAt 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Chart.chartPushedRaw (I := I) (M := M) α f) (coord α) :=
    contMDiffAt_iff_contDiffAt.mpr hf'
  have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((Chart.chartPushedRaw (I := I) (M := M) α f) ∘ coord) α :=
    hraw.comp α hcoord
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H α).open_source.mem_nhds
    (mem_chart_source (H := H) (M := M) α)] with y hy
  have hy_ext : y ∈ (extChartAt I α).source := by
    rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
  have hy_target : extChartAt I α y ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hy_ext
  have hy_eucl : coord y ∈
      Chart.chartTargetEuclid (I := I) (M := M) α := by
    exact ⟨extChartAt I α y, hy_target, rfl⟩
  rw [Function.comp_apply,
    Chart.chartPushedRaw_apply_of_mem (I := I) (M := M) α f hy_eucl]
  simp only [coord, ContinuousLinearEquiv.symm_apply_apply,
    (extChartAt I α).left_inv hy_ext]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The chart expression of the forward Busemann function of a minimizing line
has arbitrary-order local `W^{k,2}` regularity on one fixed chart ball. -/
theorem busemann_chart_wkp
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (α : M) :
    letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : ℕ,
      Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k 2
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
  have hK_eq : K = Metric.closedBall c δ := by
    dsimp only [K]
    exact Metric.cthickening_singleton c hδ.le
  have hK_compact : IsCompact K := by
    rw [hK_eq]
    exact isCompact_closedBall c δ
  have hK_ball : K ⊆ Metric.ball c r := fun x hx ↦ (hδ_sub hx).1
  have hK_target :
      K ⊆ Chart.chartTargetEuclid (I := I) (M := M) α :=
    fun x hx ↦ (hδ_sub hx).2
  obtain ⟨_, _, _, _, _, B, hB, hBc⟩ :=
    exists_smooth_metric_extension (I := I) g α hK_compact hK_target
  have hδ_half : 0 < δ / 2 := half_pos hδ
  have hδ_fourth : 0 < δ / 4 := by positivity
  have houter_K : Metric.closedBall c (δ / 2) ⊆ K := by
    intro x hx
    rw [hK_eq]
    exact Metric.closedBall_subset_closedBall (by linarith) hx
  have houter_original :
      Metric.closedBall c (δ / 2) ⊆ Metric.ball c r :=
    houter_K.trans hK_ball
  have hinner_compact : IsCompact (closure (Metric.ball c (δ / 4))) :=
    (isCompact_closedBall c (δ / 4)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hinner_outer :
      closure (Metric.ball c (δ / 4)) ⊆ Metric.ball c (δ / 2) :=
    Metric.closure_ball_subset_closedBall.trans
      (Metric.closedBall_subset_ball (by linarith))
  let Ahalf : DeGiorgi.EllipticCoeff (Module.finrank ℝ E)
      (Metric.ball c (δ / 2)) :=
    A.1.restrict (Metric.ball_subset_closedBall.trans houter_original)
  have hsol_half : DeGiorgi.IsSolution Ahalf u := by
    dsimp only [Ahalf]
    exact hsol.restrict_ball (d := Module.finrank ℝ E)
      Metric.isOpen_ball hδ_half houter_original
  have hcoeff : ∀ x ∈ Metric.ball c (δ / 2),
      ∀ i j : Fin (Module.finrank ℝ E),
        Ahalf.a x i j = s * B.a x i j := by
    intro x hx i j
    have hxK : x ∈ K :=
      houter_K (Metric.ball_subset_closedBall hx)
    change A.1.a x i j = s * B.a x i j
    rw [hA x (hK_ball hxK) i j, hB x hxK i j]
  have hB_zero : ∀ x : EuclN, B.c x = 0 := fun x ↦ congrFun hBc x
  have hall : ∀ k : ℕ,
      Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k 2 u (Metric.ball c (δ / 4)) := by
    intro k
    have hk :=
      Analysis.Sobolev.NirenbergHomogeneous.homSol_memWkp_on
        (d := Module.finrank ℝ E) k
        (Omega := Metric.ball c (δ / 2)) (V := Metric.ball c (δ / 4))
        Metric.isOpen_ball Metric.isOpen_ball hinner_compact hinner_outer
        hsol_half B hs hcoeff hB_zero
    exact Analysis.Sobolev.Euclidean.MemWkp.le_of_le (by omega) hk
  refine ⟨δ / 4, hδ_fourth, ?_⟩
  simpa only [u, c] using hall

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The actual chart expression of the forward Busemann function of a
minimizing line is smooth on a sufficiently small chart ball. -/
theorem busemann_chart_cdiff
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (α : M) :
    letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
    ∃ ρ : ℝ, 0 < ρ ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Chart.chartPushedRaw (I := I) (M := M) α
          (busemann (I := I) γ))
        (Metric.ball
          (toEuclidean (E := E) (extChartAt I α α)) ρ) := by
  classical
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let c : EuclN := toEuclidean (E := E) (extChartAt I α α)
  let u : EuclN → ℝ :=
    Chart.chartPushedRaw (I := I) (M := M) α (busemann (I := I) γ)
  obtain ⟨r, hr, hu⟩ :=
    busemann_chart_wkp (I := I) g hEnorm hγ hd hRic α
  have hu_r : ∀ k : ℕ,
      Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k 2 u (Metric.ball c r) := by
    simpa only [u, c] using hu
  have hc_target :
      c ∈ Chart.chartTargetEuclid (I := I) (M := M) α := by
    refine ⟨extChartAt I α α,
      (extChartAt I α).map_source (mem_extChartAt_source (I := I) α), ?_⟩
    rfl
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.mp
    ((Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hc_target)
  let ρ : ℝ := min r ε / 2
  have hmin : 0 < min r ε := lt_min hr hε
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact half_pos hmin
  have hρ_le_r : ρ ≤ r := by
    dsimp only [ρ]
    calc
      min r ε / 2 ≤ min r ε := by linarith
      _ ≤ r := min_le_left _ _
  have hρ_le_ε : ρ ≤ ε := by
    dsimp only [ρ]
    calc
      min r ε / 2 ≤ min r ε := by linarith
      _ ≤ ε := min_le_right _ _
  have hball_r : Metric.ball c ρ ⊆ Metric.ball c r :=
    Metric.ball_subset_ball hρ_le_r
  have hball_target :
      Metric.ball c ρ ⊆ Chart.chartTargetEuclid (I := I) (M := M) α :=
    (Metric.ball_subset_ball hρ_le_ε).trans hε_sub
  have hu_small : ∀ k : ℕ,
      Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k 2 u (Metric.ball c ρ) := by
    intro k
    exact Analysis.Sobolev.Euclidean.MemWkp.mono_set
      (by norm_num) Metric.isOpen_ball Metric.isOpen_ball hball_r (hu_r k)
  obtain ⟨u_smooth, hu_smooth, hu_ae⟩ :=
    Analysis.Sobolev.EuclideanIteratedEmbedding.contDiffOn_of_forall_memWkp_two
      (d := Module.finrank ℝ E) Metric.isOpen_ball hu_small
  have hpos_lip : ∀ x y,
      edist (busemann (I := I) γ x) (busemann (I := I) γ y) ≤
        (1 : ENNReal) * riemannianEDistOf (I := I) g x y := by
    intro x y
    rw [one_mul, riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnorm, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_toReal
      (Exponential.riemannianEDist_ne_top (I := I) x y)]
    exact ENNReal.ofReal_le_ofReal (busemann_dist (I := I) hγ.pos_ray x y)
  have hpos_cont : Continuous (busemann (I := I) γ) :=
    intrinsic_lip_cont (I := I) g hpos_lip
  have hcomp_cont : ContinuousOn
      (fun y : EuclN ↦ busemann (I := I) γ
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
      (Chart.chartTargetEuclid (I := I) (M := M) α) :=
    hpos_cont.comp_continuousOn'
      (Chart.continuousOn_symm_toEuclideanSymm (I := I) (M := M) α)
  have hu_cont : ContinuousOn u (Metric.ball c ρ) := by
    refine (hcomp_cont.mono hball_target).congr ?_
    intro y hy
    exact Chart.chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (busemann (I := I) γ) (hball_target hy)
  have hu_eq : Set.EqOn u u_smooth (Metric.ball c ρ) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hu_ae Metric.isOpen_ball
      hu_cont hu_smooth.continuousOn
  refine ⟨ρ, hρ, ?_⟩
  simpa only [u, c] using hu_smooth.congr (fun y hy ↦ hu_eq hy)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The forward Busemann function of a minimizing line is smooth. -/
theorem busemann_smooth
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (busemann (I := I) γ) := by
  intro α
  obtain ⟨ρ, hρ, hraw⟩ :=
    busemann_chart_cdiff (I := I) g hEnorm hγ hd hRic α
  exact contMDiffAt_of_raw (I := I) α
    (hraw.contDiffAt (Metric.ball_mem_nhds
      (toEuclidean (E := E) (extChartAt I α α)) hρ))

end DifferentialGeometry
