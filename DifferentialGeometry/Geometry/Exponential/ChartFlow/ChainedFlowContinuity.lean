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



noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

set_option linter.unusedSectionVars false in
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

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
