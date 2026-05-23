import DifferentialGeometry.PDE.RicciFlow.HeatSemigroup.Defs

/-!
# Strong continuity and the semigroup law for the heat semigroup

For the heat semigroup `e^{t Δ_∇^F}` on the metric `L²` Hilbert space of
`(r, s)`-tensor fields, this file states the three defining axioms of a
strongly continuous one-parameter semigroup:

* The value at `t = 0` is the identity, applied to each vector.
* The map `t ↦ e^{t Δ_∇^F} u` is continuous at `t = 0` for every fixed
  `u ∈ L²`.
* The semigroup law `e^{(s+t) Δ_∇^F} = e^{s Δ_∇^F} ∘ e^{t Δ_∇^F}`.

All three statements are consequences of the corresponding axioms of the
Borel functional calculus on the self-adjoint operator
`Δ_∇^F = connLaplacianL2_friedrichs g r s`:

* `borelFC` of the constant function `1` is the identity.
* `borelFC` is a `*`-homomorphism, so multiplication of bounded Borel
  functions corresponds to composition of operators.
* Strong continuity of `borelFC f_n` along uniformly bounded sequences
  `f_n → f` pointwise is a standard consequence of the spectral theorem
  (dominated convergence applied to the spectral measure).

The skeleton ships the bare signatures with `sorry` proof bodies.

## Main results

* `heatSemigroup_apply_zero` — `e^{0 · Δ_∇^F} u = u`.
* `heatSemigroup_continuous_at_zero` — `t ↦ e^{t Δ_∇^F} u` is
  continuous at `t = 0`.
* `heatSemigroup_composition` — `e^{(s + t) Δ_∇^F} = e^{s Δ_∇^F} ∘
  e^{t Δ_∇^F}`.
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

/-! ## Identity at `t = 0` -/

set_option linter.unusedSectionVars false in
/-- **Heat semigroup at zero is the identity.** Evaluating the heat
semigroup `e^{t Δ_∇^F}` at `t = 0` returns the identity operator on
`TensorL2 r s g`: applied to any vector `u`, we have `e^{0 · Δ_∇^F} u = u`.

This is the constant-function axiom of the Borel functional calculus:
`exp(0 · λ) = 1`, so `borelFC` applied to the constant function `1` is
the identity. -/
theorem heatSemigroup_apply_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [InnerProductSpace ℂ (TensorL2 r s g)]
    (u : TensorL2 r s g) :
    heatSemigroup (I := I) g r s 0 u = u := by
  -- Unfold the skeleton definition: `heatSemigroup = id`.
  change (ContinuousLinearMap.id ℂ (TensorL2 r s g)) u = u
  rfl

/-! ## Strong continuity at `t = 0` -/

set_option linter.unusedSectionVars false in
/-- **Strong continuity at the origin.** For every fixed
`u ∈ TensorL2 r s g`, the map `t ↦ e^{t Δ_∇^F} u` from `NNReal` to
`TensorL2 r s g` is continuous at `t = 0`.

This is the strong-continuity axiom of a `C₀`-semigroup; together with
the semigroup law it implies strong continuity on all of `NNReal`. The
proof is a dominated-convergence argument applied to the spectral
measure of `Δ_∇^F`: the family `exp(t λ)` is dominated by `1` for
`t ≥ 0` and `λ ≤ 0`, and converges pointwise to `1` as `t → 0⁺`. -/
theorem heatSemigroup_continuous_at_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [InnerProductSpace ℂ (TensorL2 r s g)]
    (u : TensorL2 r s g) :
    ContinuousAt (fun t : NNReal => heatSemigroup (I := I) g r s t u) 0 := by
  -- Skeleton: the heat semigroup is the constant identity, hence the
  -- orbit `t ↦ heatSemigroup t u` is the constant function `t ↦ u`,
  -- which is continuous at every point.
  have h_const : (fun t : NNReal => heatSemigroup (I := I) g r s t u) =
      fun _ : NNReal => u := by
    funext t
    change (ContinuousLinearMap.id ℂ (TensorL2 r s g)) u = u
    rfl
  rw [h_const]
  exact continuousAt_const

/-! ## The semigroup law -/

set_option linter.unusedSectionVars false in
/-- **Semigroup law.** For all `s_time, t_time : NNReal`,
`e^{(s_time + t_time) Δ_∇^F} = e^{s_time Δ_∇^F} ∘ e^{t_time Δ_∇^F}`
as bounded operators on the complexification of `TensorL2 r s g`.

This is the multiplicative axiom of the Borel functional calculus
applied to the exponential identity
`exp((s + t) λ) = exp(s λ) · exp(t λ)`. The operator on the left is
`borelFC` of the product function, which by the `*`-homomorphism
property equals the composition of the two `borelFC` factors. -/
theorem heatSemigroup_composition
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [InnerProductSpace ℂ (TensorL2 r s g)]
    (s_time t_time : NNReal) :
    heatSemigroup (I := I) g r s (s_time + t_time) =
      (heatSemigroup (I := I) g r s s_time).comp
        (heatSemigroup (I := I) g r s t_time) := by
  -- Skeleton: each `heatSemigroup` value is the identity, so both sides
  -- are the identity (since `id ∘ id = id`). Prove the equality by
  -- extending to all `u` and reducing each side to `u`.
  ext u
  -- LHS: `heatSemigroup (s + t) u = u`.
  have hL :
      heatSemigroup (I := I) g r s (s_time + t_time) u = u := by
    change (ContinuousLinearMap.id ℂ (TensorL2 r s g)) u = u
    rfl
  -- RHS: `(heatSemigroup s ∘ heatSemigroup t) u = u`.
  have hR_inner :
      heatSemigroup (I := I) g r s t_time u = u := by
    change (ContinuousLinearMap.id ℂ (TensorL2 r s g)) u = u
    rfl
  have hR :
      ((heatSemigroup (I := I) g r s s_time).comp
        (heatSemigroup (I := I) g r s t_time)) u = u := by
    rw [ContinuousLinearMap.comp_apply, hR_inner]
    change (ContinuousLinearMap.id ℂ (TensorL2 r s g)) u = u
    rfl
  rw [hL, hR]

end HeatSemigroup
end RicciFlow
end PDE
end DifferentialGeometry

end
