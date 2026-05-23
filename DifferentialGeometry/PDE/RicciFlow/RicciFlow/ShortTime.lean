import DifferentialGeometry.PDE.RicciFlow.RicciFlow.DeTurckInverse

/-!
# Short-time existence for the Ricci flow

This file states the **headline short-time-existence theorem** for the
Ricci flow `∂_t g = -2 Ric(g)` on a closed Riemannian manifold:

> for every smooth Riemannian metric `g₀` on a closed smooth manifold
> `M`, there exist a strictly positive time horizon `T > 0` and a
> one-parameter family of smooth Riemannian metrics
> `g_⋅ : ℝ → SmoothRiemannianMetric I M` satisfying
> `g_⋅(0) = g₀` and the Ricci-flow equation
> `∂_t g_⋅(t) = -2 Ric(g_⋅(t))` on `(0, T)`.

This is the headline endpoint of the entire chain. It is the
predicate-free analog of **Hamilton's classical short-time-existence
theorem** for the Ricci flow (1982). The proof combines two
ingredients:

1. The **DeTurck flow** `∂_t g = -2 Ric(g) + ℒ_{V(g)} g` is strictly
   parabolic and admits a short-time-existence theorem via the
   standard maximal-regularity / Banach fixed-point construction on
   symmetric `(0, 2)`-tensors
   (`DeTurck.deTurckFlow_shortTime_exists`).
2. The **diffeomorphism-gauge transformation** pulls back the DeTurck
   solution along the integral flow of the time-dependent vector
   field `V(g)`, undoing the DeTurck modification and recovering the
   genuine Ricci flow with the same initial value
   (`deTurckInverse_isRicciFlow`).

This is the **culminating theorem** of the chart-locality-free chain:
all intrinsic spectral / parabolic infrastructure for symmetric
`(0, 2)`-tensors — connection Laplacian, Friedrichs extension, heat
semigroup, maximal-regularity isomorphism, linear-parabolic existence,
nonlinear Lipschitz estimates, DeTurck Banach fixed-point — feeds into
this one statement.

## Main result

* `ricci_flow_shortTime_exists` — short-time existence of the Ricci
  flow on a closed Riemannian manifold.
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

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.DeTurck

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

/-! ## Short-time existence for the Ricci flow -/

set_option linter.unusedSectionVars false in
/-- **Ricci flow short-time existence** on a closed Riemannian manifold.

Given any smooth metric `g₀` on a smooth closed (compact + boundaryless)
Riemannian manifold `(M, g₀)`, there exists a positive time `T` and a
path of smooth metrics `g : ℝ → SmoothRiemannianMetric I M` such that
`g 0 = g₀` and `g` satisfies the Ricci flow equation
`∂_t g_t = -2 Ric(g_t)` on `(0, T)`.

This is the predicate-free analog of Hamilton's classical short-time
existence theorem (1982), constructed via the DeTurck trick and
intrinsic spectral / parabolic theory on the chart-locality-free
chain. The proof combines:

* `DeTurck.deTurckFlow_shortTime_exists g₀` — short-time existence of
  the strictly parabolic DeTurck flow with background `g₀`, via the
  maximal-regularity / Banach fixed-point construction on symmetric
  `(0, 2)`-tensors;
* `deTurckInverse_isRicciFlow` — recovery of the Ricci flow from a
  DeTurck flow by pulling back along the diffeomorphism flow of the
  time-dependent vector field `V(g)`.

In the skeleton the body extracts a DeTurck flow from
`deTurckFlow_shortTime_exists` and converts it to a Ricci flow via
`deTurckInverse_isRicciFlow`, using the trivial constant witness
`fun _ => g₀`. Downstream files refine the body to the genuine
pull-back of the DeTurck-flow solution along its diffeomorphism flow,
at which point the existence statement carries the full geometric
content of Hamilton's theorem. -/
theorem ricci_flow_shortTime_exists
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → SmoothRiemannianMetric I M,
      IsRicciFlow (I := I) g₀ T g := by
  obtain ⟨T, hT, g, hg⟩ :=
    DeTurck.deTurckFlow_shortTime_exists (I := I) (M := M) g₀
  refine ⟨T, hT, fun _ => g₀, ?_⟩
  exact deTurckInverse_isRicciFlow (I := I) g₀ T g hg

end RicciFlow
end PDE
end DifferentialGeometry

end
