import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.PDE.RicciFlow.HebeyBlock.SpectralPouH2Identify
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Basic

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem tensorPouSobolevHilbert_embedding_Ck
    {g : SmoothRiemannianMetric I M} {r s k m : ℕ}
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow
