import DifferentialGeometry.Geometry.Riemannian.Geodesic.Rescaling.BundleDerivative
import DifferentialGeometry.Geometry.Riemannian.Exponential.ChartPushVFEq

set_option linter.unusedSectionVars false

/-!
# Manifold-level geodesic time rescaling: chart-fibre bridges

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a finite-dimensional inner-product space `E`, the classical
geodesic flow has the scaling invariance
$$\gamma_{p, a v}(t) = \gamma_{p, v}(a t).$$

This file packages the **chart-fibre level** bridge between the abstract
`geodesicVectorFieldChart` (section value in `T_p(TM)`) and the explicit
`gvfFiber` form (value in `E × E` via the trivialisation of `T(TM)` at
`⟨α, 0⟩`), used by the manifold-level chain-rule argument for the
geodesic time-rescaling theorems.

## Strategy

For `p : TangentBundle I M` with `p.proj ∈ (chartAt H α).source`, we have

* `geodesicVectorFieldChart g α p ∈ T_p(TM)` (the **abstract** chart-fixed
  geodesic vector field section value), and
* `geodesicVectorFieldChartFiber g α p ∈ E × E` (the **chart-fibre** form,
  related to the abstract form by the trivialisation of `T(TM)` at
  `⟨α, 0⟩`).

The trivialisation `e := trivializationAt (E × E) (TangentSpace I.tangent) ⟨α, 0⟩`
provides the bridge:
`e.continuousLinearMapAt ℝ p (geodesicVectorFieldChart g α p) = gvfFiber g α p`.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.Exponential

/-! ## Chart-fibre extraction lemma

The trivialisation `e := trivAt _ ⟨α, 0⟩` sends
`geodesicVectorFieldChart g α p` to `geodesicVectorFieldChartFiber g α p`,
for `p` in the chart at `α`.
-/

section ChartLevelExtraction

variable [I.Boundaryless]

/-- The trivialisation of `T(TM)` at `⟨α, 0⟩` sends
`geodesicVectorFieldChart g α p` to `geodesicVectorFieldChartFiber g α p`,
for `p` with projection in the chart at `α` source. This is the inverse
of the defining identity `V_α(p) = e.symm p (gvfFiber g α p)`. -/
lemma continuousLinearMapAt_trivializationAt_geodesicVectorFieldChart
    (g : SmoothRiemannianMetric I M) (α : M)
    {p : TangentBundle I M} (hp : p.proj ∈ (chartAt H α).source) :
    (trivializationAt (E × E) (TangentSpace I.tangent)
        (⟨α, (0 : E)⟩ : TangentBundle I M)).continuousLinearMapAt ℝ p
      (geodesicVectorFieldChart (I := I) g α p) =
        geodesicVectorFieldChartFiber (I := I) g α p := by
  classical
  set e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨α, (0 : E)⟩ : TangentBundle I M) with he_def
  have hp_base : p ∈ e.baseSet := by
    rw [he_def, TangentBundle.trivializationAt_baseSet]
    exact (mem_chartAt_modelProd_zero_source_iff (I := I) α p).mpr hp
  -- `geodesicVectorFieldChart g α p = e.symm p (gvfFiber g α p) =
  --   e.symmL ℝ p (gvfFiber g α p)`, then apply
  -- `continuousLinearMapAt_symmL`.
  change e.continuousLinearMapAt ℝ p
      (e.symm p (geodesicVectorFieldChartFiber (I := I) g α p)) =
    geodesicVectorFieldChartFiber (I := I) g α p
  -- `e.symm p (v) = e.symmL ℝ p (v)` definitionally as functions.
  have hsymm : e.symm p (geodesicVectorFieldChartFiber (I := I) g α p) =
      e.symmL ℝ p (geodesicVectorFieldChartFiber (I := I) g α p) := rfl
  rw [hsymm]
  exact e.continuousLinearMapAt_symmL hp_base
    (geodesicVectorFieldChartFiber (I := I) g α p)

end ChartLevelExtraction

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
