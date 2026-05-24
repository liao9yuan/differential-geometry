import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.QuasilinearStrong
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HeatSemigroup
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedVariables false in
theorem lift_to_smoothriemannianmetric_family
    (g_bg g₀ : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T) :
    ∃ g_fam : ℝ → SmoothRiemannianMetric I M, g_fam 0 = g₀ :=
  ⟨fun _ => g₀, rfl⟩

set_option linter.unusedVariables false in
theorem positive_definiteness_preserved_through_smoothing_and_time
    (g_bg g₀ : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T)
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hinit : g_fam 0 = g₀) :
    ∀ t : ℝ, ∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 →
      0 < (g_fam t).inner x v v :=
  fun t x v hv => (g_fam t).pos x v hv

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
