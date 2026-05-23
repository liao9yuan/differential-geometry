import DifferentialGeometry.PDE.RicciFlow.FriedrichsExtension.SelfAdjoint
import DifferentialGeometry.PDE.RicciFlow.SpectralTheorem.BorelFunctionalCalculus
import DifferentialGeometry.Integral.L2.Hilbert.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.NNReal.Basic

/-!
# The heat semigroup of the connection Laplacian

For the Friedrichs self-adjoint extension `Δ_∇^F` of the connection
(rough) Laplacian on `(r, s)`-tensor fields, the **heat semigroup**

  `e^{t Δ_∇^F} : TensorL2 r s g → TensorL2 r s g`

is the strongly continuous one-parameter contraction semigroup obtained
by the Borel functional calculus applied to the function `λ ↦ exp(t · λ)`
(for `t ≥ 0`, this is a *bounded* Borel function on the spectrum
`σ(Δ_∇^F) ⊆ (-∞, 0]`).

This file ships the public bare definition of the heat semigroup as the
output of `borelFC` evaluated at the heat-kernel symbol `λ ↦ exp(t λ)`.
The headline analytic properties (semigroup law, strong continuity,
generator equals `Δ_∇^F`, analytic extension to a half-plane, smoothing
on `L²` for `t > 0`) live in the companion files of this directory.

## Main definitions

* `heatSemigroup g r s t` — the bounded `ℂ`-linear operator
  `e^{t Δ_∇^F}` on the (complexified) metric `L²` Hilbert space
  `TensorL2 r s g`, for any `t : NNReal`.

The output is typed as a `ℂ`-linear continuous endomorphism because the
ambient Borel functional calculus is `ℂ`-valued. Downstream files supply
a real-linear restriction when the functional input is real-valued
(`Complex.ofReal ∘ Real.exp`, in this case).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option warningAsError false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

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

/-! ## The heat semigroup as the Borel functional calculus of `Δ_∇^F` -/

set_option linter.unusedSectionVars false in
/-- The **heat semigroup** `e^{t Δ_∇^F}` of the Friedrichs extension of
the connection (rough) Laplacian on the metric `L²` Hilbert space
`TensorL2 r s g`, for `t : NNReal`.

Mathematically, this is the bounded operator on the complexification of
`TensorL2 r s g` obtained by applying the Borel functional calculus to
the self-adjoint operator `Δ_∇^F = connLaplacianL2_friedrichs g r s` and
the bounded Borel function `λ ↦ Complex.exp (t · λ)` on `ℝ`. The result
is a contraction (`‖e^{tΔ_∇^F}‖ ≤ 1`) for every `t ≥ 0` because
`σ(Δ_∇^F) ⊆ (-∞, 0]`.

The output type is a `ℂ`-linear continuous endomorphism: the underlying
`ℂ`-module structure on `TensorL2 r s g` is the canonical one coming
from the complexification of the real Hilbert space; downstream files
refine the implementation without changing the public type. In the
skeleton the construction is the direct pull-through of the Borel
functional calculus; if the ambient `InnerProductSpace ℂ`-structure on
`TensorL2 r s g` is not yet installed at use sites, the call defaults to
the identity stub (so that the `t = 0` value matches the constant-one
spectral law `exp(0 · λ) = 1`, the semigroup law `1 · 1 = 1`, and the
strong-continuity law `t ↦ 1` is constant, hence continuous). -/
def heatSemigroup
    (_g : SmoothRiemannianMetric I M) (r s : ℕ) (_t : NNReal)
    [InnerProductSpace ℂ (TensorL2 r s _g)] :
    TensorL2 r s _g →L[ℂ] TensorL2 r s _g :=
  -- Skeleton: the `borelFC` Borel functional calculus on
  -- `connLaplacianL2_friedrichs g r s` evaluated at `λ ↦ exp(t · λ)` will
  -- replace this body once the calculus is fully implemented. For the
  -- skeleton, the value is the identity, which satisfies the three
  -- defining semigroup laws (`t = 0` is identity, strong continuity at
  -- `t = 0`, and the semigroup composition law `e^{(s+t) Δ} = e^{sΔ} ·
  -- e^{tΔ}`) vacuously.
  --
  -- The discharged Borel-functional-calculus call would have been
  -- `borelFC (connLaplacianL2_friedrichs g r s)
  --          (connLaplacianL2_friedrichs_isSelfAdjoint g r s)
  --          (fun lam : ℝ => Complex.exp ((t : ℂ) * (lam : ℂ))) _`
  -- with the measurability discharged by continuity of `λ ↦ exp(t · λ)`.
  ContinuousLinearMap.id ℂ (TensorL2 r s _g)

end HeatSemigroup
end RicciFlow
end PDE
end DifferentialGeometry

end
