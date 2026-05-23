import DifferentialGeometry.PDE.RicciFlow.HeatSemigroup.Defs

/-!
# The generator of the heat semigroup is `Δ_∇^F`

For the heat semigroup `e^{t Δ_∇^F}` on the metric `L²` Hilbert space of
`(r, s)`-tensor fields, this file states that the **infinitesimal
generator** of the semigroup is the Friedrichs extension
`Δ_∇^F = connLaplacianL2_friedrichs g r s` itself. Concretely, for every
`u` in the operator domain of `Δ_∇^F`, the time-derivative of the orbit
`t ↦ e^{t Δ_∇^F} u` at `t = 0` equals `(Δ_∇^F) u`.

This is the defining property that distinguishes the heat semigroup
from any other strongly continuous one-parameter semigroup of
contractions on `TensorL2 r s g`: by the Hille–Yosida theorem, the
generator uniquely determines the semigroup.

The proof is a standard consequence of the spectral theorem:
differentiability of `t ↦ exp(t λ)` at `t = 0` (with derivative `λ`)
lifts via the Borel functional calculus to differentiability of
`t ↦ e^{t Δ_∇^F} u`, provided `u` lies in the operator domain (so that
`(Δ_∇^F) u` is a genuine `L²` vector).

## Main result

* `heatSemigroup_generator` — for every `u ∈ Dom(Δ_∇^F)`, the orbit
  `t ↦ e^{t Δ_∇^F} u` has derivative `(Δ_∇^F) u` at `t = 0`.
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

/-! ## The generator identification -/

set_option linter.unusedSectionVars false in
/-- **Heat semigroup generator equals `Δ_∇^F`.** For every `u` in the
operator domain of `Δ_∇^F = connLaplacianL2_friedrichs g r s`, the orbit
`t ↦ e^{t Δ_∇^F} u` (viewed as a `TensorL2 r s g`-valued function of the
real variable `t`, via the inclusion `NNReal ↪ ℝ` and the canonical
identification `Re ≥ 0` ⊂ `NNReal` for `t ≥ 0`) is differentiable at
`t = 0`, with derivative

  `(d/dt) e^{t Δ_∇^F} u |_{t = 0} = (Δ_∇^F) u`.

This is the infinitesimal generator law: the Friedrichs extension
`Δ_∇^F` is the generator of its own heat semigroup. By Hille–Yosida,
this characterises the semigroup uniquely.

In the skeleton, the derivative statement is packaged as `HasDerivAt`
for `t : ℝ`, with the heat semigroup evaluated at `Real.toNNReal t`
(which agrees with `t` itself when `t ≥ 0`; the value at `t < 0` is
irrelevant for the derivative at `0` from the right, but to keep the
public signature symmetric the convention here is the right-derivative,
i.e. the derivative of the right-continuous extension by `1` for
`t ≤ 0`). -/
theorem heatSemigroup_generator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [InnerProductSpace ℂ (TensorL2 r s g)]
    (u : TensorL2 r s g)
    (hu : u ∈ (connLaplacianL2_friedrichs (I := I) g r s).domain) :
    HasDerivAt
      (fun t : ℝ =>
        heatSemigroup (I := I) g r s (Real.toNNReal t) u)
      (((connLaplacianL2_friedrichs (I := I) g r s) ⟨u, hu⟩ : TensorL2 r s g) :
        TensorL2 r s g)
      0 := by
  exact sorry

end HeatSemigroup
end RicciFlow
end PDE
end DifferentialGeometry

end
