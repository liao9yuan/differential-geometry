import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Locally constant chart selection

This file introduces the predicate `HasLocallyConstantChartAt H M`, expressing
that the canonical chart-selection function `chartAt H : M → OpenPartialHomeomorph M H`
of a `ChartedSpace H M` is locally constant at every point: for each
`b₀ : M`, there is a neighbourhood of `b₀` on which `chartAt H _` agrees with
`chartAt H b₀`.

The abstract `ChartedSpace` axioms do not imply this property — they only
require that each point lies in the source of its chart and that the chosen
chart belongs to the atlas. Nevertheless, every standard manifold
construction (open subsets of the model space, spheres, Lie groups, smooth
products and quotients, normal-coordinate charts, …) selects its chart in a
locally constant way. We therefore add `HasLocallyConstantChartAt` as an
explicit hypothesis to be threaded through downstream theorems that depend
on uniform control of the bundle trivialisation across a base set.

## Main definitions

* `HasLocallyConstantChartAt H M` — the predicate.

## Main results

* `HasLocallyConstantChartAt.exists_isOpen_nhds` — locality gives an open
  neighbourhood on which `chartAt H` is constant.
* `hasLocallyConstantChartAt_self` — the prototypical example: the model
  space `H`, viewed as a charted space over itself via `chartedSpaceSelf`,
  has locally constant chart selection (in fact, the chart is constant
  *globally*).
-/

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry
namespace Geometry

/-- A `ChartedSpace H M` has locally constant chart selection if the
canonical chart-selection function `chartAt H : M → OpenPartialHomeomorph M H`
is locally constant at every point: for each `b₀ : M`, there is a
neighbourhood of `b₀` on which `chartAt H` agrees with `chartAt H b₀`.

This is automatic for all standard manifold constructions (open submanifolds
of the model space, spheres, Lie groups, smooth products and quotients,
normal-coord charts) but is not implied by the abstract `ChartedSpace`
axioms. Theorems that require uniform control of the bundle trivialisation
across a compact base set carry this predicate explicitly. -/
def HasLocallyConstantChartAt
    (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop :=
  ∀ b₀ : M, ∀ᶠ b in 𝓝 b₀, chartAt H b = chartAt H b₀

namespace HasLocallyConstantChartAt

variable {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Unfold the locality hypothesis to an open neighbourhood on which the
chart is constant. -/
theorem exists_isOpen_nhds
    (h : HasLocallyConstantChartAt H M) (b₀ : M) :
    ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧
      ∀ b ∈ U, chartAt H b = chartAt H b₀ := by
  obtain ⟨U, hU_subset, hU_open, hU_mem⟩ := eventually_nhds_iff.mp (h b₀)
  exact ⟨U, hU_open, hU_mem, hU_subset⟩

end HasLocallyConstantChartAt

/-- The model space `H`, viewed as a charted space over itself via
`chartedSpaceSelf`, has locally constant chart selection. In fact, the chart
selection is globally constant: `chartAt H b = OpenPartialHomeomorph.refl H`
for every `b : H`. -/
theorem hasLocallyConstantChartAt_self
    (H : Type*) [TopologicalSpace H] :
    HasLocallyConstantChartAt H H := by
  intro b₀
  filter_upwards with b
  rfl

end Geometry
end DifferentialGeometry
