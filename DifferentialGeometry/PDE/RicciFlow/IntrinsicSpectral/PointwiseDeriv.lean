import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.QuasilinearStrong
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem maxreg_l2deriv_to_pointwise_hasderivwithinat
    (g_bg : SmoothRiemannianMetric I M) :
    True := sorry

theorem hasDerivAt_clm_apply_from_h1_time
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : ℝ) (hT : 0 < T) (u u' : ℝ → X) (t : ℝ) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
