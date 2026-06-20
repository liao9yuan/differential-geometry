import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ZeroSectionConstancy
import DifferentialGeometry.Geometry.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Exponential.ChartFlow.PreconnectedPropagation
import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.ODE.Flow.C1Regularity.ContDiffOnOne
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

theorem maximalGeodesic_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ContinuousAt (maximalGeodesic (I := I) g p v) 0 := by
  classical
  obtain ⟨g_v, hg0, hg_int⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) (g := g)
      (p := p) (v := v)
  have hlift_cont : ContinuousAt g_v 0 := hg_int.continuousAt
  have hπ_cont : Continuous
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hproj_cont : ContinuousAt (fun t => (g_v t).proj) 0 :=
    hπ_cont.continuousAt.comp hlift_cont
  obtain ⟨ε, hε, h_eq⟩ :=
    picardLift_proj_eq_maximalGeodesic_on_ball (I := I) (g := g) (p := p)
      (v := v) hg0 hg_int
  have h_eventually :
      maximalGeodesic (I := I) g p v =ᶠ[𝓝 (0 : ℝ)] fun t => (g_v t).proj := by
    have h_ball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)
    filter_upwards [h_ball] with t ht using h_eq t ht
  exact hproj_cont.congr h_eventually.symm

theorem expMap_geodesicSegment_compactImage
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    IsCompact (maximalGeodesic (I := I) g p v₀ '' Set.Icc (0 : ℝ) 1) := by
  have h_cont :
      ContinuousOn (maximalGeodesic (I := I) g p v₀) (Set.Icc (0 : ℝ) 1) := by
    sorry
  exact isCompact_Icc.image_of_continuousOn h_cont

theorem expMap_chainedFlow_joint_continuity
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : TangentSpace I p) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContinuousOn
        (fun vt : TangentSpace I p × ℝ =>
          maximalGeodesic (I := I) g p vt.1 vt.2)
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  sorry

theorem expMap_chainedFlow_joint_contMDiff
    (g : SmoothRiemannianMetric I M) (p : M) (v₀ : E)
    (hv₀ : (show TangentSpace I p from v₀) ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1
        (fun vt : E × ℝ =>
          (maximalGeodesic (I := I) g p (show TangentSpace I p from vt.1) vt.2 : M))
        ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
  sorry

theorem expMap_continuous
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (expMap (I := I) g p) := by
  rw [continuous_iff_continuousAt]
  intro v₀
  obtain ⟨ρ, hρ, hjoint⟩ :=
    expMap_chainedFlow_joint_continuity (I := I) g p v₀
  set F : TangentSpace I p × ℝ → M :=
    fun vt => maximalGeodesic (I := I) g p vt.1 vt.2 with hF_def
  set s : TangentSpace I p → TangentSpace I p × ℝ := fun v => (v, 1) with hs_def
  have hcomp_eq : expMap (I := I) g p = F ∘ s := by
    funext v
    simp only [Function.comp_apply, hF_def, hs_def, expMap]
  rw [hcomp_eq]
  have hs_cont : Continuous s := by
    rw [hs_def]; exact continuous_id.prodMk continuous_const
  have hs_maps : Set.MapsTo s (Metric.ball v₀ ρ)
      ((Metric.ball v₀ ρ) ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro v hv
    refine ⟨hv, ?_⟩
    exact ⟨zero_le_one, le_refl 1⟩
  have hball_nhds : Metric.ball v₀ ρ ∈ 𝓝 v₀ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
  have hcw : ContinuousWithinAt (F ∘ s) (Metric.ball v₀ ρ) v₀ := by
    apply ContinuousOn.continuousWithinAt _ (Metric.mem_ball_self hρ)
    exact hjoint.comp hs_cont.continuousOn hs_maps
  exact hcw.continuousAt hball_nhds

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
