import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChartFrameNorm
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.GramTwist
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.ChristoffelCkBound
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.NablaTensorFormula
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.IteratedNabla
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.UniformChartBounds
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.PouNormChartComp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem assemble_pou_h1_iso_intrinsic_h1
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock
