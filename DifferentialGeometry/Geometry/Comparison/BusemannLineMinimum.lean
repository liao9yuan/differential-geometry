import DifferentialGeometry.Analysis.Elliptic.DistribSupersolution
import DifferentialGeometry.External.DeGiorgi.StrongMinimum
import DifferentialGeometry.Geometry.Comparison.BusemannLineEnergy
import DifferentialGeometry.Geometry.Comparison.BusemannLineLaplacian

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ENNReal Manifold NNReal Topology

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
/-- On a connected manifold of dimension greater than two, the two Busemann
functions determined by a minimizing line sum to zero everywhere under
nonnegative Ricci curvature. -/
theorem buse_pair_eq_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (x : M) :
    busemann (I := I) γ x +
      busemann (I := I) (fun t : ℝ ↦ γ (-t)) x = 0 := by
  classical
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let u : M → ℝ := fun y ↦
    busemann (I := I) γ y +
      busemann (I := I) (fun t : ℝ ↦ γ (-t)) y
  have hpos_lip : ∀ y z, edist (busemann (I := I) γ y)
      (busemann (I := I) γ z) ≤
      (1 : ENNReal) * riemannianEDistOf (I := I) g y z := by
    intro y z
    rw [one_mul, riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnorm, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_toReal
      (Exponential.riemannianEDist_ne_top (I := I) y z)]
    exact ENNReal.ofReal_le_ofReal (busemann_dist (I := I) hγ.pos_ray y z)
  have hneg_lip : ∀ y z,
      edist (busemann (I := I) (fun t : ℝ ↦ γ (-t)) y)
        (busemann (I := I) (fun t : ℝ ↦ γ (-t)) z) ≤
      (1 : ENNReal) * riemannianEDistOf (I := I) g y z := by
    intro y z
    rw [one_mul, riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnorm, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_toReal
      (Exponential.riemannianEDist_ne_top (I := I) y z)]
    exact ENNReal.ofReal_le_ofReal (busemann_dist (I := I) hγ.neg_ray y z)
  have hpos_cont : Continuous (busemann (I := I) γ) :=
    intrinsic_lip_cont (I := I) g hpos_lip
  have hneg_cont : Continuous (busemann (I := I) (fun t : ℝ ↦ γ (-t))) :=
    intrinsic_lip_cont (I := I) g hneg_lip
  have hu_cont : Continuous u := by
    dsimp only [u]
    exact hpos_cont.add hneg_cont
  have hu_nonneg (y : M) : 0 ≤ u y := by
    simpa only [u] using buse_pair_nonneg (I := I) hγ y
  have hd_lap : 0 < Module.finrank ℝ E - 1 := by omega
  have hu_lap : IsLapLEDistribOn (I := I) g u (fun _ : M ↦ 0) univ := by
    simpa only [u] using buse_pair_lap (I := I) g hEnorm hγ hd_lap hRic
  have hu_zero : u (γ 0) = 0 := by
    simpa only [u] using buse_pair_zero (I := I) hγ
  let Z : Set M := {y | u y = 0}
  have hZ_closed : IsClosed Z := by
    dsimp only [Z]
    exact isClosed_eq hu_cont continuous_const
  have hZ_nonempty : Z.Nonempty := by
    refine ⟨γ 0, ?_⟩
    simpa only [Z, Set.mem_setOf_eq] using hu_zero
  have hZ_open : IsOpen Z := by
    rw [isOpen_iff_mem_nhds]
    intro alpha halpha
    have hualpha : u alpha = 0 := by
      simpa only [Z, Set.mem_setOf_eq] using halpha
    obtain ⟨rW, hrW, huW⟩ :=
      buse_pair_memW1p (I := I) g hEnorm hγ alpha
    let c : EuclN :=
      toEuclidean (E := E) (extChartAt I alpha alpha)
    let uE : EuclN → ℝ :=
      Chart.chartPushedRaw (I := I) (M := M) alpha u
    have hc_target :
        c ∈ Chart.chartTargetEuclid (I := I) (M := M) alpha := by
      refine ⟨extChartAt I alpha alpha,
        (extChartAt I alpha).map_source
          (mem_extChartAt_source (I := I) alpha), ?_⟩
      rfl
    obtain ⟨delta, hdelta, hdelta_sub⟩ := Metric.mem_nhds_iff.mp
      ((Chart.chartTargetEuclid_isOpen (I := I) (M := M) alpha).mem_nhds hc_target)
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
        Chart.chartTargetEuclid (I := I) (M := M) alpha :=
      Metric.closure_ball_subset_closedBall.trans
        ((Metric.closedBall_subset_ball hR_lt_delta).trans hdelta_sub)
    have hball_target : Metric.ball c R ⊆
        Chart.chartTargetEuclid (I := I) (M := M) alpha :=
      subset_closure.trans hclosure
    have huW' : DeGiorgi.MemW1p 2 uE (Metric.ball c rW) := by
      simpa only [uE, u, c] using huW
    have huW_R : DeGiorgi.MemW1p 2 uE (Metric.ball c R) :=
      ((DeGiorgi.MemW1p.someWitness huW').restrict Metric.isOpen_ball
        (Metric.ball_subset_ball hR_le_rW)).memW1p
    obtain ⟨A, s, hs, hA⟩ :=
      exists_metric_coeff (I := I) g alpha hR hclosure
    have hsuper : DeGiorgi.IsSupersolution A.1 uE := by
      exact chart_super_of_lap (I := I) (M := M) g alpha hclosure
        hu_lap hu_cont huW_R A hs hA
    have huE_cont : ContinuousOn uE (Metric.ball c R) := by
      have hcomp : ContinuousOn
          (fun y : EuclN ↦
            u ((extChartAt I alpha).symm
              ((toEuclidean (E := E)).symm y)))
          (Metric.ball c R) :=
        hu_cont.comp_continuousOn'
          ((Chart.continuousOn_symm_toEuclideanSymm
            (I := I) (M := M) alpha).mono hball_target)
      refine ContinuousOn.congr hcomp ?_
      intro y hy
      change Chart.chartPushedRaw (I := I) (M := M) alpha u y = _
      exact Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) alpha u (hball_target hy)
    have huE_nonneg : ∀ y ∈ Metric.ball c R, 0 ≤ uE y := by
      intro y hy
      dsimp only [uE]
      rw [Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) alpha u (hball_target hy)]
      exact hu_nonneg _
    have hc_zero : uE c = 0 := by
      dsimp only [uE]
      rw [Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) alpha u hc_target]
      simpa only [c, (toEuclidean (E := E)).symm_apply_apply,
        (extChartAt I alpha).left_inv
          (mem_extChartAt_source (I := I) alpha)] using hualpha
    have hd_real : 2 < (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast hd
    have hR_fourth : 0 < R / 4 := div_pos hR (by norm_num)
    have huE_zero : Set.EqOn uE (fun _ ↦ 0) (Metric.ball c (R / 4)) :=
      DeGiorgi.super_zero_on_ball (d := Module.finrank ℝ E) hd_real hR A
        huE_cont huE_nonneg hsuper (x₀ := c)
        (Metric.mem_ball_self hR_fourth) hc_zero
    have hball_model :
        (toEuclidean (E := E)) ⁻¹' Metric.ball c (R / 4) ∈
          nhds (extChartAt I alpha alpha) := by
      apply (toEuclidean (E := E)).continuous.continuousAt.preimage_mem_nhds
      simpa only [c] using Metric.ball_mem_nhds c hR_fourth
    have hcoord_nhds :
        (extChartAt I alpha) ⁻¹'
            ((toEuclidean (E := E)) ⁻¹' Metric.ball c (R / 4)) ∈
          nhds alpha :=
      (continuousAt_extChartAt (I := I) alpha).preimage_mem_nhds hball_model
    have hnear :
        (extChartAt I alpha).source ∩
            (extChartAt I alpha) ⁻¹'
              ((toEuclidean (E := E)) ⁻¹' Metric.ball c (R / 4)) ∈
          nhds alpha :=
      inter_mem (extChartAt_source_mem_nhds (I := I) alpha) hcoord_nhds
    refine mem_of_superset hnear ?_
    intro y hy
    have hy_source : y ∈ (extChartAt I alpha).source := hy.1
    let z : EuclN := toEuclidean (E := E) (extChartAt I alpha y)
    have hz_ball : z ∈ Metric.ball c (R / 4) := hy.2
    have hz_target :
        z ∈ Chart.chartTargetEuclid (I := I) (M := M) alpha := by
      refine ⟨extChartAt I alpha y,
        (extChartAt I alpha).map_source hy_source, ?_⟩
      rfl
    have hinv :
        (extChartAt I alpha).symm
            ((toEuclidean (E := E)).symm z) = y := by
      dsimp only [z]
      rw [(toEuclidean (E := E)).symm_apply_apply,
        (extChartAt I alpha).left_inv hy_source]
    have hz_eval :
        uE z = u ((extChartAt I alpha).symm
          ((toEuclidean (E := E)).symm z)) := by
      exact Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) alpha u hz_target
    have hz_zero : uE z = 0 := by
      simpa only using huE_zero hz_ball
    change u y = 0
    calc
      u y = u ((extChartAt I alpha).symm
          ((toEuclidean (E := E)).symm z)) := congrArg u hinv.symm
      _ = uE z := hz_eval.symm
      _ = 0 := hz_zero
  have hZ_univ : Z = univ :=
    IsClopen.eq_univ ⟨hZ_closed, hZ_open⟩ hZ_nonempty
  have hxZ : x ∈ Z := by
    rw [hZ_univ]
    exact Set.mem_univ x
  change u x = 0
  simpa only [Z, Set.mem_setOf_eq] using hxZ

end DifferentialGeometry
