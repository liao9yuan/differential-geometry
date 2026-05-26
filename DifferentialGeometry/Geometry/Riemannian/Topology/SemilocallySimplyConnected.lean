import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Semi-locally simply connected spaces

A topological space `X` is *semi-locally simply connected* if every point
has a neighbourhood `U` such that every loop in `U` (based at the point)
is null-homotopic in `X`. This is the point-set hypothesis required for
the standard construction of the universal cover (Hatcher, Prop. 1.36):
the universal cover exists for spaces that are connected, locally path
connected, and semi-locally simply connected.

`Mathlib` does not yet provide this typeclass, so we introduce it here
in the same style as `LocPathConnectedSpace` and `SimplyConnectedSpace`
(a `class` with a single proof-valued field `out`).

We then establish, as the manifold instance, that every smooth manifold
modelled on an inner-product space is semi-locally simply connected: each
chart pulls a neighbourhood of `x` back to an open ball in the model
space, which is contractible, so every loop in the chart neighbourhood
is null-homotopic.
-/

open Set Function Filter Metric Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology

/-- A topological space is *semi-locally simply connected* if every point
has a neighbourhood `U` such that every loop in `U` (based at the point)
is null-homotopic in the ambient space.

This is the point-set hypothesis (alongside connectedness and local path
connectedness) under which the universal cover exists. -/
class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] :
    Prop where
  /-- For every point, there is a neighbourhood in which every loop is
  null-homotopic in `X`. -/
  out : ∀ x : X, ∃ U ∈ nhds x, ∀ γ : _root_.Path x x,
          Set.range γ.toContinuousMap ⊆ U →
            (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧

/-- If `U ⊆ X` is open and `ContractibleSpace U`, then every loop
`γ : Path x x` with `range γ ⊆ U` is null-homotopic in `X`, i.e.
`⟦γ⟧ = ⟦Path.refl x⟧` in `Path.Homotopic.Quotient x x`. -/
theorem contractible_loops_nullhomotopic_in_subset
    {X : Type*} [TopologicalSpace X]
    {U : Set X} (hUopen : IsOpen U) [ContractibleSpace U]
    {x : X} (hxU : x ∈ U)
    (γ : _root_.Path x x)
    (hγU : Set.range γ.toContinuousMap ⊆ U) :
    (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧ :=
  sorry

section ChartContractible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Every point of a smooth manifold modelled on an inner-product space
has an open neighbourhood that is contractible. The neighbourhood is the
preimage, under the extended chart at `x`, of a small open ball around
`extChartAt I x x` lying inside the chart's target. -/
theorem chart_contractible_nhd_at_point (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ContractibleSpace U := by
  sorry

/-- Every smooth manifold modelled on an inner-product space is
semi-locally simply connected. For each `x : M`, a chart neighbourhood
is contractible, hence every loop in it is null-homotopic in `M`. -/
instance manifold_semilocallySimplyConnectedSpace :
    SemilocallySimplyConnectedSpace M := ⟨sorry⟩

end ChartContractible

end Topology
end Riemannian
end Geometry
end DifferentialGeometry
