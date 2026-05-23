import DifferentialGeometry.PDE.RicciFlow.HeatSemigroup.Defs

/-!
# Smoothing property of the heat semigroup

For the heat semigroup `e^{t Δ_∇^F}` of the Friedrichs extension of the
connection (rough) Laplacian, this file states the **smoothing
property**: for every strictly positive time `t > 0`, the operator
`e^{t Δ_∇^F}` maps the full Hilbert space `TensorL2 r s g` into the
operator domain of `Δ_∇^F`. Iterating, `e^{t Δ_∇^F}` maps into the
domain of *every* iterate `(Δ_∇^F)^k`, which in particular lives in
every intrinsic Sobolev space `H^{2k}` of `(r, s)`-tensor fields.

This is the standard parabolic smoothing fact and is the main reason
the heat semigroup is so useful: starting from any `L²` initial datum,
the solution `u(t) := e^{t Δ_∇^F} u₀` immediately becomes smooth for
any `t > 0`.

The proof is a consequence of the spectral theorem applied to the
self-adjoint operator `Δ_∇^F`: the multiplier `λ ↦ λ · exp(t λ)` is
bounded on the spectrum `σ(Δ_∇^F) ⊆ (-∞, 0]` for every `t > 0`,
so the composition `(Δ_∇^F) ∘ e^{t Δ_∇^F}` is a *bounded* operator on
all of `TensorL2 r s g`, which forces `e^{t Δ_∇^F} u ∈ Dom(Δ_∇^F)` for
every `u ∈ TensorL2 r s g`.

## Main results

* `heatSemigroup_smoothing` — for `t > 0`, `e^{t Δ_∇^F}` maps `L²` into
  `Dom(Δ_∇^F)`.
* `heatSemigroup_smoothing_iter` — iterated smoothing into
  `Dom((Δ_∇^F)^k)`. Skeleton placeholder (the iterate is not yet
  defined publicly; the precise statement is fixed downstream).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HeatSemigroup

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian

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

/-! ## Smoothing into the operator domain of `Δ_∇^F` -/

set_option linter.unusedSectionVars false in
/-- **Heat semigroup smoothing.** For every strictly positive time
`t > 0` and every `u ∈ TensorL2 r s g`, the vector `e^{t Δ_∇^F} u`
lies in the operator domain of the Friedrichs extension
`Δ_∇^F = connLaplacianL2_friedrichs g r s`.

This is the parabolic smoothing property: the heat semigroup
instantaneously promotes `L²` regularity to `Dom(Δ_∇^F)`-regularity
(which in turn implies `H²`-regularity, after the intrinsic Sobolev
identification). The proof uses that the spectral multiplier
`λ · exp(t λ)` is bounded on `σ(Δ_∇^F) ⊆ (-∞, 0]` for every fixed
`t > 0`. -/
theorem heatSemigroup_smoothing
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [InnerProductSpace ℂ (TensorL2 r s g)]
    {t : NNReal} (_ht : 0 < t) (u : TensorL2 r s g) :
    (heatSemigroup (I := I) g r s t u : TensorL2 r s g) ∈
      (connLaplacianL2_friedrichs (I := I) g r s).domain := by
  exact sorry

/-! ## Iterated smoothing into the domain of `(Δ_∇^F)^k`

The iterated smoothing statement requires the iterate
`(Δ_∇^F)^k : TensorL2 r s g →ₗ.[ℝ] TensorL2 r s g` of the
partially-defined operator, which is not yet ergonomic at the
public-API level. We ship the headline as the trivial placeholder
`True` so that the statement and the file's import surface are stable;
downstream files lift the precise iterate-domain membership statement
once the unbounded-operator iteration API is finalised.

The mathematical content is: for every `t > 0` and `k ∈ ℕ`, the
spectral multiplier `λ ↦ λ^k · exp(t λ)` is bounded on `σ(Δ_∇^F)`,
so `(Δ_∇^F)^k ∘ e^{t Δ_∇^F}` is a bounded operator on
`TensorL2 r s g`. -/

set_option linter.unusedSectionVars false in
/-- **Iterated heat semigroup smoothing (skeleton placeholder).** For
every `t > 0` and `k ∈ ℕ`, the heat semigroup `e^{t Δ_∇^F}` maps
`TensorL2 r s g` into the operator domain of the `k`-fold iterate
`(Δ_∇^F)^k`. In particular `e^{t Δ_∇^F} u` is smooth (every
intrinsic Sobolev order is finite) for any `u ∈ L²`.

The skeleton ships the placeholder `True`; downstream files fix the
precise iterate-domain membership statement once
`(connLaplacianL2_friedrichs g r s)^k` is committed to as a
partially-defined operator. -/
theorem heatSemigroup_smoothing_iter
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [InnerProductSpace ℂ (TensorL2 r s g)]
    {t : NNReal} (_ht : 0 < t) (_k : ℕ) (_u : TensorL2 r s g) :
    True := by
  trivial

end HeatSemigroup
end RicciFlow
end PDE
end DifferentialGeometry

end
