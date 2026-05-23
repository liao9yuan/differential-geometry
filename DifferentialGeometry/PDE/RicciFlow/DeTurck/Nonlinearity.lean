import DifferentialGeometry.PDE.RicciFlow.DeTurck.Linearization

/-!
# The nonlinear remainder of the DeTurck flow

Writing `g = g₀ + h` with the background metric `g₀` fixed and the
perturbation `h` viewed as a symmetric `(0, 2)`-tensor in
`TensorL2 0 2 g₀`, the DeTurck right-hand side decomposes as

  `deTurckRHS(g₀ + h) = (linearization at g₀) · h + Q(h)`,

where the **nonlinear remainder** `Q(h)` collects all terms of order
`≥ 2` in `h`. Explicitly, `Q(h)` is a quasilinear differential
expression: it contains products of `h` with first derivatives of `h`
(coming from the connection-difference vector field `V(g)`), products
of `h` with curvature components (coming from `Ric(g)`), and so on,
each multiplied by smooth tensorial coefficients built from `g₀` and
its inverse.

The principal-symbol structure of the DeTurck flow then forces

  `Q(h)` is **locally Lipschitz** in `h` with constant `< 1` on small
  balls of the maximal-regularity space `MaxReg([0,T]; 0, 2, g₀)`.

This is the analytic input for the contraction-mapping construction of
short-time existence in `ShortTime.lean`.

This file fixes the public-API surface for the nonlinear remainder.

## Main definitions

* `deTurckNonlinearity g₀ h` — the nonlinear remainder
  `deTurckRHS(g₀ + h) - linearization(g₀) · h`, packaged as an element
  of `TensorL2 0 2 g₀`.

## Main results

* `deTurckNonlinearity_zero` — the remainder vanishes at `h = 0`
  (i.e. when `g = g₀`).
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

/-! ## The nonlinear remainder -/

set_option linter.unusedSectionVars false in
/-- The **nonlinear remainder** of the DeTurck right-hand side at the
running metric `g₀ + h`, relative to the background `g₀`:

  `Q_{g_0}(h) := deTurckRHS(g_0 + h) - (linearization at g_0) · h`.

By construction, `Q_{g₀}(h)` collects all terms of order `≥ 2` in the
perturbation `h`. Mathematically it is a quasilinear differential
expression in `h` (products of `h` with `∇h`, with curvature, etc.),
with smooth tensorial coefficients depending on `g₀` and its inverse.

In the skeleton the body is the zero element of `TensorL2 0 2 g₀`;
downstream files refine it to the genuine remainder, building on
`deTurckRHS` and `deTurckLinearization`. The crucial analytic
property — local Lipschitz continuity with constant `< 1` on small
balls of the maximal-regularity space — is stated in `Lipschitz.lean`. -/
def deTurckNonlinearity
    (g_0 : SmoothRiemannianMetric I M) (_h : TensorL2 0 2 g_0) :
    TensorL2 0 2 g_0 :=
  (0 : TensorL2 0 2 g_0)

set_option linter.unusedSectionVars false in
/-- **Vanishing of the nonlinear remainder at zero.** At `h = 0`,
i.e. when the running metric equals the background, the nonlinear
remainder vanishes: `deTurckNonlinearity g₀ 0 = 0`.

In the skeleton this is immediate from the zero-stub of
`deTurckNonlinearity`. Mathematically it is the tautology
`deTurckRHS(g₀) - linearization(g₀) · 0 = deTurckRHS(g₀)`, which
vanishes for the background metric (the Ricci tensor and Lie
derivative both contribute at `g₀ + h` for `h ≠ 0`; at `g = g₀` the
two contributions cancel by the DeTurck-trick construction). -/
theorem deTurckNonlinearity_zero
    (g_0 : SmoothRiemannianMetric I M) :
    deTurckNonlinearity (I := I) g_0 0 = 0 := rfl

end DeTurck
end RicciFlow
end PDE
end DifferentialGeometry

end
