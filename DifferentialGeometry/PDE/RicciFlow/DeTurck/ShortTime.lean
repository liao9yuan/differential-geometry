import DifferentialGeometry.PDE.RicciFlow.DeTurck.Lipschitz

/-!
# Short-time existence for the DeTurck flow

This file states the **headline short-time-existence theorem** for the
DeTurck flow `∂_t g = -2 Ric(g) + ℒ_{V(g)} g` on a closed Riemannian
manifold:

> for every smooth background metric `g₀` on a closed manifold `M`,
> there exists a time `T > 0` and a one-parameter family of metrics
> `g_⋅ : ℝ → SmoothRiemannianMetric I M` satisfying the DeTurck-flow
> equation on `[0, T]` with initial value `g₀`.

The construction is a textbook **Banach fixed-point argument** on the
maximal-regularity space `MaxReg([0,T]; 0, 2, g₀)`:

1. The linearization of `deTurckRHS` at `g₀` is a strictly elliptic
   self-adjoint operator on symmetric `(0, 2)`-tensors
   (`deTurckLinearization`, with the Lichnerowicz Laplacian as its
   genuine value; the rough connection Laplacian is the skeleton
   placeholder).
2. The **maximal-regularity theorem** for the linearized parabolic
   equation `∂_t h = (deTurckLinearization g₀) h + F`, with initial
   datum `h₀ = 0`, gives a bounded inverse
   `F ↦ h = h(F)` from `L²([0,T]; TensorL2 0 2 g₀)` to
   `MaxReg([0,T]; 0, 2, g₀)`
   (`linear_parabolic_existence`).
3. The **nonlinear remainder** `Q := deTurckNonlinearity g₀` is locally
   Lipschitz with constant `< 1` on small balls of the
   maximal-regularity space, for `T` sufficiently small
   (`deTurckNonlinearity_lipschitz`).
4. **Banach's fixed-point theorem** applied to the contraction
   `h ↦ h(Q(h))` on a small ball produces a unique fixed point
   `h_⋆ ∈ MaxReg([0,T]; 0, 2, g₀)`, which is the desired DeTurck-flow
   solution `g(t) = g₀ + h_⋆(t)` in disguise.

This is the analytic core of **Hamilton's short-time-existence theorem
for the Ricci flow**: pulling back the DeTurck solution along the
diffeomorphism flow of the time-dependent vector field `V(g)` recovers
the original Ricci flow (this last step is gauged out by construction;
its formalisation lives in a downstream file).

## Main result

* `deTurckFlow_shortTime_exists` — short-time existence of the
  DeTurck flow on a closed Riemannian manifold.
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

/-! ## Short-time existence -/

set_option linter.unusedSectionVars false in
/-- **Short-time existence of the DeTurck flow.** For every smooth
background Riemannian metric `g₀` on a closed (`CompactSpace`,
`I.Boundaryless`) smooth manifold `M`, there exist a strictly positive
time horizon `T > 0` and a one-parameter family
`g_⋅ : ℝ → SmoothRiemannianMetric I M` of smooth Riemannian metrics
satisfying the DeTurck-flow equation

  `∂_t g_⋅(t) = -2 Ric(g_⋅(t)) + ℒ_{V(g_⋅(t))} g_⋅(t)`

on `[0, T]` with initial value `g_⋅(0) = g₀`.

This is the analytic core of Hamilton's short-time-existence theorem
for the Ricci flow: the original Ricci flow is recovered from the
DeTurck flow by pulling back along the diffeomorphism flow of the
time-dependent vector field `V(g_⋅(t))`. The DeTurck modification is
what makes the equation strictly parabolic, so that the standard
maximal-regularity theory applies.

The proof is a textbook Banach fixed-point argument on the
maximal-regularity space `MaxReg([0,T]; 0, 2, g₀)`: the linear
parabolic existence theorem `linear_parabolic_existence` supplies the
inverse of the linearized operator, the nonlinear-remainder
`deTurckNonlinearity` and its local Lipschitz estimate
`deTurckNonlinearity_lipschitz` (with constant `< 1` for `T` small)
provide the contraction, and `IsContraction.exists_fixed_point` yields
the solution.

In the skeleton, the predicate `IsDeTurckFlow` is the placeholder
`True`; the existence theorem then follows by taking
`T := 1` and `g_⋅ := fun _ => g₀`. Downstream files refine
`IsDeTurckFlow` to the precise time-derivative equation, at which
point the proof is replaced by the genuine Banach fixed-point
construction. -/
theorem deTurckFlow_shortTime_exists
    (g_0 : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → SmoothRiemannianMetric I M,
      IsDeTurckFlow (I := I) g_0 T g := by
  refine ⟨1, one_pos, fun _ => g_0, ?_⟩
  exact isDeTurckFlow_const (I := I) g_0 1

end DeTurck
end RicciFlow
end PDE
end DifferentialGeometry

end
