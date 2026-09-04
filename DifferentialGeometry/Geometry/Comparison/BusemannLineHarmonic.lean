import DifferentialGeometry.Analysis.Elliptic.WeakLaplacian
import DifferentialGeometry.Geometry.Comparison.BusemannLineSmooth

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set Topology
open scoped ENNReal Manifold NNReal

namespace DifferentialGeometry

open Analysis.Sobolev.IntrinsicLp
open Geometry.Operator
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The forward Busemann function of a minimizing line is pointwise harmonic. -/
theorem busemann_lap_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (x : M) :
    Δ_g (I := I) g
      ⟨busemann (I := I) γ,
        busemann_smooth (I := I) g hEnorm hγ hd hRic⟩ x = 0 := by
  classical
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let bp : M → ℝ := busemann (I := I) γ
  let bn : M → ℝ := busemann (I := I) (fun t : ℝ ↦ γ (-t))
  have hbp_smooth : ContMDiff I 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) bp := by
    simpa only [bp] using busemann_smooth (I := I) g hEnorm hγ hd hRic
  have hpair (y : M) : bp y + bn y = 0 := by
    simpa only [bp, bn] using
      buse_pair_eq_zero (I := I) g hEnorm hγ hd hRic y
  have hbn_eq : bn = fun y ↦ -bp y := by
    funext y
    linarith [hpair y]
  have hbn_smooth : ContMDiff I 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) bn := by
    rw [hbn_eq]
    exact hbp_smooth.neg
  have hd_lap : 0 < Module.finrank ℝ E - 1 := by omega
  have hbp_distrib : IsLapLEDistribOn (I := I) g bp
      (fun _ : M ↦ 0) univ := by
    simpa only [bp] using
      busemann_lap (I := I) g hEnorm hγ.pos_ray hd_lap hRic
  have hbn_distrib : IsLapLEDistribOn (I := I) g bn
      (fun _ : M ↦ 0) univ := by
    simpa only [bn] using
      busemann_lap (I := I) g hEnorm hγ.neg_ray hd_lap hRic
  have hbp_le : Δ_g (I := I) g ⟨bp, hbp_smooth⟩ x ≤ 0 := by
    exact lap_le_of_distrib (I := I) g hbp_smooth continuousOn_const
      hbp_distrib x (Set.mem_univ x)
  have hbn_le : Δ_g (I := I) g ⟨bn, hbn_smooth⟩ x ≤ 0 := by
    exact lap_le_of_distrib (I := I) g hbn_smooth continuousOn_const
      hbn_distrib x (Set.mem_univ x)
  have hbn_as_neg :
      Δ_g (I := I) g ⟨bn, hbn_smooth⟩ x =
        Δ_g (I := I) g ⟨fun y ↦ -bp y, hbp_smooth.neg⟩ x := by
    exact Δ_g_congr_of_eventuallyEq (I := I) g hbn_smooth hbp_smooth.neg
      (Filter.Eventually.of_forall fun y ↦ congrFun hbn_eq y)
  have hbn_lap :
      Δ_g (I := I) g ⟨bn, hbn_smooth⟩ x =
        -Δ_g (I := I) g ⟨bp, hbp_smooth⟩ x := by
    calc
      Δ_g (I := I) g ⟨bn, hbn_smooth⟩ x =
          Δ_g (I := I) g ⟨fun y ↦ -bp y, hbp_smooth.neg⟩ x := hbn_as_neg
      _ = -Δ_g (I := I) g ⟨bp, hbp_smooth⟩ x :=
        Δ_g_neg (I := I) g hbp_smooth
  have hbp_nonneg : 0 ≤ Δ_g (I := I) g ⟨bp, hbp_smooth⟩ x := by
    linarith [hbn_le, hbn_lap]
  have hzero : Δ_g (I := I) g ⟨bp, hbp_smooth⟩ x = 0 :=
    le_antisymm hbp_le hbp_nonneg
  simpa only [bp] using hzero

end DifferentialGeometry
