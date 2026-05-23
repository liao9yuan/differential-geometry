import DifferentialGeometry.PDE.RicciFlow.DeTurck.Nonlinearity

/-!
# Lipschitz estimate for the DeTurck nonlinearity

The contraction-mapping construction of short-time existence for the
DeTurck flow rests on a **local Lipschitz estimate** for the nonlinear
remainder `deTurckNonlinearity g₀ ·` viewed as a self-map of the
maximal-regularity space `MaxReg([0,T]; 0, 2, g₀)`:

> There exist a Lipschitz constant `L < 1`, a radius `R > 0`, and a
> time horizon `T > 0` such that on the closed `R`-ball of
> `MaxReg([0,T]; 0, 2, g₀)` around the origin, the remainder satisfies
> `‖Q(h₁) − Q(h₂)‖_{MaxReg} ≤ L · ‖h₁ − h₂‖_{MaxReg}` for every pair
> `h₁, h₂` in the ball.

The proof exploits the quasilinear structure of `Q` (each term is a
product of `h` and `∇h` with smooth tensorial coefficients depending on
`g₀` and its inverse), combined with continuous embeddings of the
maximal-regularity space into Hölder spaces. In particular the Lipschitz
constant `L` becomes arbitrarily small as `T → 0`, which is what allows
us to satisfy `L < 1`.

This file fixes the public-API surface for the Lipschitz statement; the
precise formulation (the exact ball, the exact norm) is fixed
downstream once the underlying type of `maxRegSpace` and its norm are
committed to. In the skeleton the proposition is the placeholder
`True`.

## Main result

* `deTurckNonlinearity_lipschitz` — local Lipschitz continuity of the
  nonlinear remainder on a ball of the maximal-regularity space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace DeTurck

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian
open DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension
open DifferentialGeometry.PDE.RicciFlow.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## The Lipschitz estimate -/

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- **Local Lipschitz estimate for the DeTurck nonlinearity.** For every
background metric `g₀`, every time horizon `T > 0`, and every radius
`R > 0`, the nonlinear remainder `deTurckNonlinearity g₀ ·` satisfies a
local Lipschitz estimate on the closed `R`-ball of the
maximal-regularity space `MaxReg([0,T]; 0, 2, g₀)` around the origin,
with constant `< 1` for `T` sufficiently small:

> there exist `L ∈ [0, 1)` such that
> `‖deTurckNonlinearity g_0 h_1 − deTurckNonlinearity g_0 h_2‖_{MaxReg}
>   ≤ L · ‖h_1 − h_2‖_{MaxReg}`
> for every `h_1, h_2` in the closed `R`-ball of `MaxReg`.

This is the analytic input for the contraction-mapping construction of
short-time existence in `ShortTime.lean`. The smallness of `L` is what
forces the contraction property; the time-Lipschitz constant becomes
arbitrarily small as `T → 0`, by the continuous embedding of the
maximal-regularity space into Hölder spaces.

In the skeleton the proposition is the placeholder `True`; the precise
formulation is fixed downstream once the underlying type of
`maxRegSpace` and its norm are committed to. -/
theorem deTurckNonlinearity_lipschitz
    (g_0 : SmoothRiemannianMetric I M) (T : ℝ) (hT : 0 < T)
    {R : ℝ} (hR : 0 < R) :
    -- Placeholder: precise statement requires the genuine
    -- maximal-regularity norm and ball, which the skeleton does not
    -- expose. Downstream files refine the body to the precise
    -- Lipschitz estimate.
    True := by
  trivial

end DeTurck
end RicciFlow
end PDE
end DifferentialGeometry

end
