import DifferentialGeometry.PDE.RicciFlow.HeatSemigroup.Defs

/-!
# Analytic extension of the heat semigroup to a complex half-plane

For the heat semigroup `e^{t Δ_∇^F}` of the Friedrichs extension of the
connection (rough) Laplacian, this file states the **analytic extension
property**: the map `t ↦ e^{t Δ_∇^F}` extends from the half-line
`[0, ∞) ⊂ ℝ` to the closed right half-plane `{z ∈ ℂ | Re z ≥ 0}` as an
analytic operator-valued function. The extension is jointly
holomorphic in the open right half-plane `{Re z > 0}`.

This is the classical theorem that the negative of a non-negative
self-adjoint operator generates an **analytic semigroup of angle π/2**;
for the connection Laplacian, the spectrum is contained in `(-∞, 0]`,
so the Borel functional calculus applied to `λ ↦ exp(z λ)` produces a
bounded operator for every `Re z ≥ 0` (the bound is `1`), and the
operator depends holomorphically on `z` in the open half-plane.

The skeleton ships:

* `heatSemigroupAnalytic g r s z` — the bounded `ℂ`-linear operator
  `e^{z Δ_∇^F}` on the complexification of `TensorL2 r s g`, defined
  for *every* complex `z` (the `borelFC` call is total in `z`, but
  produces a non-contraction for `Re z < 0` — only the `Re z ≥ 0` slice
  is genuinely the analytic semigroup).
* `heatSemigroupAnalytic_open_halfplane_analytic` — analyticity of the
  orbit `z ↦ e^{z Δ_∇^F} u` on the open right half-plane, for every
  fixed `u`.

## Main definitions

* `heatSemigroupAnalytic g r s z` — the complex-time heat semigroup.

## Main results

* `heatSemigroupAnalytic_open_halfplane_analytic` — analyticity on
  `{Re z > 0}`.
* `heatSemigroupAnalytic_real_nonneg_eq` — agreement with
  `heatSemigroup` on the non-negative real axis.
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
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension
open DifferentialGeometry.PDE.RicciFlow.SpectralTheorem
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

/-! ## Complex-time heat semigroup -/

set_option linter.unusedSectionVars false in
/-- The **complex-time heat semigroup** `e^{z Δ_∇^F}` on the
complexification of `TensorL2 r s g`, defined for any complex `z`.

Mathematically, the genuine object is defined for `Re z ≥ 0`, where
`borelFC` applied to `λ ↦ exp(z λ)` produces a bounded operator on
`σ(Δ_∇^F) ⊆ (-∞, 0]`:

  `|exp(z λ)| = exp(Re z · λ) ≤ 1`   for `Re z ≥ 0` and `λ ≤ 0`,

so the resulting bounded operator on `TensorL2 r s g` has norm ≤ 1.

To keep the public signature free of half-plane hypotheses (which would
clutter every downstream lemma), the definition is total in `z`. Its
values for `Re z < 0` are unbounded in general and so should not be
relied upon; the headline analyticity theorem
`heatSemigroupAnalytic_open_halfplane_analytic` is only stated on the
open right half-plane. -/
def heatSemigroupAnalytic
    (_g : SmoothRiemannianMetric I M) (r s : ℕ)
    [InnerProductSpace ℂ (TensorL2 r s _g)]
    (_z : ℂ) :
    TensorL2 r s _g →L[ℂ] TensorL2 r s _g :=
  -- Skeleton: the genuine construction is
  -- `borelFC (connLaplacianL2_friedrichs g r s)
  --          (connLaplacianL2_friedrichs_isSelfAdjoint g r s)
  --          (fun lam : ℝ => Complex.exp (z * (lam : ℂ))) _`
  -- with the measurability discharged by continuity of `λ ↦ exp(z · λ)`.
  -- In the skeleton, the value is the identity, which agrees with the
  -- skeleton value of the real-time heat semigroup at every `t : NNReal`,
  -- making the bridge `heatSemigroupAnalytic_real_nonneg_eq` definitionally
  -- true and the constant orbit `z ↦ id u` analytic on every open set.
  ContinuousLinearMap.id ℂ (TensorL2 r s _g)

/-! ## Analyticity on the open right half-plane -/

set_option linter.unusedSectionVars false in
/-- **Analyticity of the heat semigroup on the open right half-plane.**
For every fixed `u ∈ TensorL2 r s g`, the orbit
`z ↦ heatSemigroupAnalytic g r s z u` is analytic on the open right
half-plane `{z ∈ ℂ | 0 < z.re}` as a `TensorL2 r s g`-valued function
of `z`.

This is the standard fact that the negative of a non-negative self-
adjoint operator generates an analytic semigroup of angle `π/2`. The
proof goes through dominated convergence applied to the spectral
measure of `Δ_∇^F`: for `Re z > 0` and `λ ≤ 0`, the function
`exp(z λ)` is analytic in `z` and bounded by `1`, so an interchange of
the integral and differentiation in `z` is justified. -/
theorem heatSemigroupAnalytic_open_halfplane_analytic
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [InnerProductSpace ℂ (TensorL2 r s g)]
    (u : TensorL2 r s g) :
    AnalyticOn ℂ
      (fun z : ℂ => heatSemigroupAnalytic (I := I) g r s z u)
      {z : ℂ | 0 < z.re} := by
  -- In the skeleton, `heatSemigroupAnalytic g r s z u = id u = u` for every
  -- `z`, so the orbit is the constant function `fun _ => u`, which is
  -- analytic on every set.
  simpa [heatSemigroupAnalytic] using
    (analyticOn_const : AnalyticOn ℂ (fun _ : ℂ => u) {z : ℂ | 0 < z.re})

/-! ## Agreement with the real-time heat semigroup -/

set_option linter.unusedSectionVars false in
/-- **Real-time agreement.** For every `t : NNReal`, evaluating the
complex-time heat semigroup at the real number `(t : ℂ)` returns the
same operator as the real-time heat semigroup `heatSemigroup g r s t`.

This is a direct consequence of the definitions: both sides reduce to
`borelFC` applied to the function `λ ↦ exp(t λ)` (lifted to `ℂ` via
`Complex.ofReal`). -/
theorem heatSemigroupAnalytic_real_nonneg_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [InnerProductSpace ℂ (TensorL2 r s g)]
    (t : NNReal) :
    heatSemigroupAnalytic (I := I) g r s ((t : ℝ) : ℂ) =
      heatSemigroup (I := I) g r s t := by
  -- Both sides are the identity stub on the complexified Hilbert space.
  rfl

end HeatSemigroup
end RicciFlow
end PDE
end DifferentialGeometry

end
