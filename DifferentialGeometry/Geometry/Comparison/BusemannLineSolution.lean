import DifferentialGeometry.External.DeGiorgi.Localization
import DifferentialGeometry.Geometry.Comparison.BusemannLineMinimum

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Metric Set Topology
open scoped ENNReal Manifold NNReal

namespace DifferentialGeometry

open Analysis.Laplacian.DistribSupersolution
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a sufficiently small chart ball, the forward Busemann function of a
minimizing line is a De Giorgi weak solution for a normalized coefficient,
together with the coefficient's positive-scalar metric provenance. -/
theorem busemann_chart_data
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (α : M) :
    letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
    ∃ r : ℝ, 0 < r ∧
      ∃ A : DeGiorgi.NormalizedEllipticCoeff
          (Module.finrank ℝ E)
          (Metric.ball
            (toEuclidean (E := E) (extChartAt I α α)) r),
        ∃ s : ℝ, 0 < s ∧
          (∀ y ∈ Metric.ball
              (toEuclidean (E := E) (extChartAt I α α)) r, ∀ i j,
            A.1.a y i j =
              s * weightedInvGramOnEuclid (I := I) g α i j y) ∧
          DeGiorgi.IsSolution A.1
            (Chart.chartPushedRaw (I := I) (M := M) α
              (busemann (I := I) γ)) := by
  classical
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let bp : M → ℝ := busemann (I := I) γ
  let bn : M → ℝ := busemann (I := I) (fun t : ℝ ↦ γ (-t))
  let c : EuclN := toEuclidean (E := E) (extChartAt I α α)
  let bpE : EuclN → ℝ :=
    Chart.chartPushedRaw (I := I) (M := M) α bp
  let bnE : EuclN → ℝ :=
    Chart.chartPushedRaw (I := I) (M := M) α bn
  have hpos_lip : ∀ x y, edist (bp x) (bp y) ≤
      (1 : ENNReal) * riemannianEDistOf (I := I) g x y := by
    intro x y
    dsimp only [bp]
    rw [one_mul, riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnorm, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_toReal
      (Exponential.riemannianEDist_ne_top (I := I) x y)]
    exact ENNReal.ofReal_le_ofReal (busemann_dist (I := I) hγ.pos_ray x y)
  have hpos_cont : Continuous bp :=
    intrinsic_lip_cont (I := I) g hpos_lip
  have hpair (x : M) : bp x + bn x = 0 := by
    simpa only [bp, bn] using buse_pair_eq_zero (I := I) g hEnorm hγ hd hRic x
  have hneg_cont : Continuous bn := by
    have hneg_eq : bn = fun x ↦ -bp x := by
      funext x
      linarith [hpair x]
    rw [hneg_eq]
    exact hpos_cont.neg
  obtain ⟨rW, hrW, hposW⟩ :=
    Chart.raw_memW1p_of_lip (I := I) g α hpos_lip
  have hc_target :
      c ∈ Chart.chartTargetEuclid (I := I) (M := M) α := by
    refine ⟨extChartAt I α α,
      (extChartAt I α).map_source (mem_extChartAt_source (I := I) α), ?_⟩
    rfl
  obtain ⟨delta, hdelta, hdelta_sub⟩ := Metric.mem_nhds_iff.mp
    ((Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).mem_nhds hc_target)
  let R : ℝ := min rW (delta / 2)
  have hR : 0 < R := by
    dsimp only [R]
    exact lt_min hrW (half_pos hdelta)
  have hR_le_rW : R ≤ rW := by
    dsimp only [R]
    exact min_le_left _ _
  have hR_lt_delta : R < delta := by
    calc
      R ≤ delta / 2 := by
        dsimp only [R]
        exact min_le_right _ _
      _ < delta := half_lt_self hdelta
  have hclosure : closure (Metric.ball c R) ⊆
      Chart.chartTargetEuclid (I := I) (M := M) α :=
    Metric.closure_ball_subset_closedBall.trans
      ((Metric.closedBall_subset_ball hR_lt_delta).trans hdelta_sub)
  have hposW' : DeGiorgi.MemW1p 2 bpE (Metric.ball c rW) := by
    simpa only [bpE, c] using hposW
  have hposW_R : DeGiorgi.MemW1p 2 bpE (Metric.ball c R) :=
    ((DeGiorgi.MemW1p.someWitness hposW').restrict Metric.isOpen_ball
      (Metric.ball_subset_ball hR_le_rW)).memW1p
  have hraw_neg : bnE = fun z ↦ -bpE z := by
    funext z
    by_cases hz : z ∈ Chart.chartTargetEuclid (I := I) (M := M) α
    · dsimp only [bnE, bpE]
      rw [
        Chart.chartPushedRaw_apply_of_mem (I := I) (M := M) α bn hz,
        Chart.chartPushedRaw_apply_of_mem (I := I) (M := M) α bp hz]
      linarith [hpair ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm z))]
    · dsimp only [bnE, bpE]
      rw [
        Chart.chartPushedRaw_apply_of_notMem (I := I) (M := M) α bn hz,
        Chart.chartPushedRaw_apply_of_notMem (I := I) (M := M) α bp hz,
        neg_zero]
  have hnegW_R : DeGiorgi.MemW1p 2 bnE (Metric.ball c R) := by
    rw [hraw_neg]
    have hneg_wit : DeGiorgi.MemW1pWitness 2
        (fun z ↦ -bpE z) (Metric.ball c R) := by
      simpa only [neg_one_mul] using
        (DeGiorgi.MemW1p.someWitness hposW_R).smul (-1)
    exact hneg_wit.memW1p
  have hd_lap : 0 < Module.finrank ℝ E - 1 := by omega
  have hpos_lap : IsLapLEDistribOn (I := I) g bp
      (fun _ : M ↦ 0) univ := by
    simpa only [bp] using
      busemann_lap (I := I) g hEnorm hγ.pos_ray hd_lap hRic
  have hneg_lap : IsLapLEDistribOn (I := I) g bn
      (fun _ : M ↦ 0) univ := by
    simpa only [bn] using
      busemann_lap (I := I) g hEnorm hγ.neg_ray hd_lap hRic
  obtain ⟨A, s, hs, hA⟩ :=
    exists_metric_coeff (I := I) g α hR hclosure
  have hpos_super : DeGiorgi.IsSupersolution A.1 bpE := by
    exact chart_super_of_lap (I := I) (M := M) g α hclosure
      hpos_lap hpos_cont hposW_R A hs hA
  have hneg_super : DeGiorgi.IsSupersolution A.1 bnE := by
    exact chart_super_of_lap (I := I) (M := M) g α hclosure
      hneg_lap hneg_cont hnegW_R A hs hA
  have hraw_ae : bnE =ᵐ[volume.restrict (Metric.ball c R)] fun z ↦ -bpE z :=
    Filter.Eventually.of_forall fun z ↦ congrFun hraw_neg z
  have hminus_super : DeGiorgi.IsSupersolution A.1 (fun z ↦ -bpE z) :=
    DeGiorgi.IsSupersolution.congr_ae hraw_ae hneg_super
  have hpos_sub : DeGiorgi.IsSubsolution A.1 bpE := by
    simpa only [neg_neg] using
      DeGiorgi.IsSupersolution.neg_ball
        (d := Module.finrank ℝ E) hR hminus_super
  refine ⟨R, hR, A, s, hs, hA, ?_⟩
  exact ⟨hpos_sub, hpos_super⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On a sufficiently small chart ball, the forward Busemann function of a
minimizing line is a De Giorgi weak solution for the normalized metric
coefficient. -/
theorem busemann_chart_sol
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (α : M) :
    letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
    ∃ r : ℝ, 0 < r ∧
      ∃ A : DeGiorgi.NormalizedEllipticCoeff
          (Module.finrank ℝ E)
          (Metric.ball
            (toEuclidean (E := E) (extChartAt I α α)) r),
        DeGiorgi.IsSolution A.1
          (Chart.chartPushedRaw (I := I) (M := M) α
            (busemann (I := I) γ)) := by
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨r, hr, A, _s, _hs, _hA, hsol⟩ :=
    busemann_chart_data (I := I) g hEnorm hγ hd hRic α
  exact ⟨r, hr, A, hsol⟩

end DifferentialGeometry
