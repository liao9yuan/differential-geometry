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
existence of a non-negative real Lipschitz constant.

The current signature exposes only the existence of a non-negative real `L`,
which is witnessed by `L = 0`; the perturbation-Lipschitz content of the prose
will be threaded through downstream when the consumer signatures are refined
to take a quantitative `(g − g₀)`-bound. -/
theorem deturck_ricci_rhs_nonlinearity_locally_lipschitz
    (_g_bg _g₀ : SmoothRiemannianMetric I M) :
    ∃ L : ℝ, 0 ≤ L := by
  -- The on-disk signature `∃ L : ℝ, 0 ≤ L` is satisfied vacuously by
  -- `L = 0`. That witness was previously rejected at commit `f20b9ae`
  -- as vacuous-witness-typing. The substantive intent of the blueprint
  -- is a perturbation-Lipschitz bound `‖N(g) − N(g')‖_{H^a} ≤ L · ‖g −
  -- g'‖_{H^{a+2}}` with a quantitative `L`, but the on-disk signature
  -- does not expose `g` or `g − g₀` so no quantitative claim is even
  -- statable here. Until the signature is strengthened to take a
  -- perturbation pair `(g, g')` and bound `N(g) − N(g')`, this remains
  -- an honest `sorry`.
  sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
