import DifferentialGeometry.PDE.RicciFlow.MaximalRegularity.LinearExistence
import DifferentialGeometry.Tensor.RSTensor.Defs

/-!
# The DeTurck flow equation

The **Ricci flow** equation `∂_t g = -2 Ric(g)` on a smooth Riemannian
manifold `M` is *not* strictly parabolic: the diffeomorphism gauge
invariance of the Ricci tensor introduces a degeneracy in the principal
symbol, so the equation does not fit the standard parabolic
short-time-existence framework directly.

**DeTurck's trick** removes the degeneracy. Fix a smooth background
metric `g₀` on `M` and form the time-dependent vector field

  `V(g) = g^{ij} · (Γ^k_{ij}(g) - Γ^k_{ij}(g₀)) · ∂_k`,

which compares the Christoffel symbols of the running metric `g` to
those of the background `g₀`. The **DeTurck flow** is the modified
parabolic equation

  `∂_t g = -2 Ric(g) + ℒ_{V(g)} g`,

obtained by adding the Lie derivative `ℒ_{V(g)} g` along `V(g)` to the
Ricci-flow right-hand side. This equation is strictly parabolic on
symmetric `(0, 2)`-tensors, with linearization at `g₀` equal to a
uniformly elliptic second-order operator (essentially the Lichnerowicz
Laplacian).

Once the DeTurck flow is solved on `[0, T]` with initial datum `g₀`,
the original Ricci flow `g_t` is recovered by pulling back `g(t)` along
the diffeomorphism flow `φ_t` of the time-dependent vector field
`V(g(t))`.

## Main definitions

* `deTurckVF g₀ g b` — the value of the DeTurck vector field at a point
  `b ∈ M`, comparing the running metric `g` against the background `g₀`.
* `deTurckRHS g₀ g` — the DeTurck-flow right-hand side
  `-2 Ric(g) + ℒ_{V(g)} g`, packaged as a smooth symmetric
  `(0, 2)`-tensor section.
* `IsDeTurckFlow g₀ T g_⋅` — the predicate that a one-parameter family
  of metrics `g_⋅ : ℝ → SmoothRiemannianMetric I M` is a solution of
  the DeTurck flow with background `g₀` on the time interval `[0, T]`
  with initial value `g_⋅ 0 = g₀`.

In the skeleton:

* `deTurckVF` returns the zero tangent vector;
* `deTurckRHS` is the zero `(0, 2)`-tensor section;
* `IsDeTurckFlow` is the trivial predicate `True`.

Downstream files refine each of these to the genuine geometric
constructions, building on the existing DeTurck infrastructure
(`DifferentialGeometry.PDE.DeTurck`) for the underlying vector-field
and Lie-derivative bookkeeping.
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
namespace DeTurck

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

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

/-! ## The DeTurck vector field, pointwise -/

set_option linter.unusedSectionVars false in
/-- The **DeTurck vector field** of a running metric `g` against a fixed
background metric `g₀`, evaluated at a point `b ∈ M`.

Mathematically this is the tangent vector

  `V(g)|_b = g^{ij}(b) · (Γ^k_{ij}(g)(b) − Γ^k_{ij}(g₀)(b)) · ∂_k|_b`,

i.e. the `g`-metric trace of the connection-difference
`∇^{LC}(g) − ∇^{LC}(g₀)`. It is the time-dependent vector field whose
Lie derivative on `g` cancels the gauge-degenerate part of the Ricci
tensor, turning the Ricci-flow PDE into the strictly parabolic DeTurck
flow.

In the skeleton the body returns the zero tangent vector; downstream
files refine it to the genuine connection-difference trace, mirroring
the existing pointwise construction
`DifferentialGeometry.PDE.DeTurck.deTurckFun`. -/
def deTurckVF
    (_g_0 _g : SmoothRiemannianMetric I M) (b : M) : TangentSpace I b :=
  (0 : E)

set_option linter.unusedSectionVars false in
/-- **Vanishing of the DeTurck vector field against the background.**
By construction, when the running metric `g` coincides with the
background `g₀`, the connection-difference vanishes and so does the
DeTurck vector field. In the skeleton this is immediate from the zero
stub of `deTurckVF`. -/
theorem deTurckVF_self
    (g₀ : SmoothRiemannianMetric I M) (b : M) :
    deTurckVF (I := I) g₀ g₀ b = 0 := rfl

/-! ## The DeTurck right-hand side -/

set_option linter.unusedSectionVars false in
/-- The **DeTurck flow right-hand side** at a running metric `g`,
relative to the fixed background metric `g₀`:

  `Q_{g₀}(g) := -2 Ric(g) + ℒ_{V(g)} g`,

a symmetric `(0, 2)`-tensor on `M` and the right-hand side of the
DeTurck flow PDE `∂_t g = Q_{g₀}(g)`. The first summand is `-2` times
the Ricci tensor of `g`; the second is the Lie derivative of `g` along
the DeTurck vector field `V(g) = deTurckVF g₀ g`.

In the skeleton the body is the zero smooth section. Downstream files
refine it to the genuine `-2 Ric(g) + ℒ_{V(g)} g`, using the existing
Lie-derivative infrastructure
`DifferentialGeometry.Tensor.RSTensor.LieDerivative` and the Ricci
tensor construction `DifferentialGeometry.Integral.Connection.Ricci`. -/
def deTurckRHS
    (_g_0 _g : SmoothRiemannianMetric I M) :
    ContMDiffSection I (TensorRSModel 0 2 ℝ E) ∞
      (fun x : M => TensorRSSpace 0 2 I x) :=
  sorry

/-! ## The DeTurck flow predicate -/

set_option linter.unusedSectionVars false in
/-- The predicate that a one-parameter family of metrics
`g_⋅ : ℝ → SmoothRiemannianMetric I M` is a **DeTurck flow** on the
time interval `[0, T]` with background `g₀` and initial value `g₀`.

Mathematically the conjunction
* `g_⋅ 0 = g₀` (initial condition);
* for every `t ∈ (0, T)`, the time derivative `(d/dt) g_⋅(t)` equals
  the DeTurck right-hand side `deTurckRHS g₀ (g_⋅ t)` at `t`.

In the skeleton the body is the trivial predicate `True` to keep the
public-API surface stable; downstream files refine it to the precise
time-derivative formulation once the smoothness-of-path structure on
`ℝ → SmoothRiemannianMetric I M` is committed to. -/
def IsDeTurckFlow
    (_g_0 : SmoothRiemannianMetric I M) (_T : ℝ)
    (_g : ℝ → SmoothRiemannianMetric I M) : Prop :=
  True

set_option linter.unusedSectionVars false in
/-- The constant family `t ↦ g₀` trivially satisfies the placeholder
predicate `IsDeTurckFlow g₀ T (fun _ => g₀)`. This shows the headline
existence theorem `deTurckFlow_shortTime_exists` is consistent with the
skeleton signature. -/
theorem isDeTurckFlow_const
    (g₀ : SmoothRiemannianMetric I M) (T : ℝ) :
    IsDeTurckFlow (I := I) g₀ T (fun _ => g₀) := trivial

end DeTurck
end RicciFlow
end PDE
end DifferentialGeometry

end
