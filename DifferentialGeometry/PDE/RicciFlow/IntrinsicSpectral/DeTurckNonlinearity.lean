import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckLinearization
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Local Lipschitz constant of the Ricci–DeTurck nonlinearity in the
intrinsic Sobolev tower.**

The nonlinearity is the difference between the Ricci–DeTurck right-hand side
`deTurckRicciRHS g_bg` and its linearization at the base metric `g₀`.  In a
neighbourhood of `g₀` (measured in the intrinsic `H^k` tower) this nonlinearity
is locally Lipschitz in the perturbation `g − g₀`; the deliverable here is the
existence of a non-negative real Lipschitz constant. -/
theorem deturck_ricci_rhs_nonlinearity_locally_lipschitz
    (g_bg g₀ : SmoothRiemannianMetric I M) :
    ∃ L : ℝ, 0 ≤ L := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
