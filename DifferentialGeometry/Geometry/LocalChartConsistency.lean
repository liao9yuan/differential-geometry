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
* `HasChartSourceConsistentChartAt H M` — the stronger predicate: the
  chart-selection function `chartAt H` is constant on each chart source.

## Main results

* `HasLocallyConstantChartAt.exists_isOpen_nhds` — locality gives an open
  neighbourhood on which `chartAt H` is constant.
* `hasLocallyConstantChartAt_self` — the prototypical example: the model
  space `H`, viewed as a charted space over itself via `chartedSpaceSelf`,
  has locally constant chart selection (in fact, the chart is constant
  *globally*).
* `hasChartSourceConsistentChartAt_self` — the model space `H`, viewed as a
  charted space over itself via `chartedSpaceSelf`, has chart-source-
  consistent chart selection.
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

/-- A `ChartedSpace H M` has chart-source-consistent chart selection if the
canonical chart-selection function `chartAt H : M → OpenPartialHomeomorph M H`
is constant on each chart source: for every `α : M` and every `b` in the
source of `chartAt H α`, the chart at `b` coincides with the chart at `α`.

This is strictly stronger than `HasLocallyConstantChartAt` (which only
requires the chart to be locally constant near each point), and is typical of
manifolds whose chart sources are connected (e.g. spheres, Lie groups,
products of charted spaces, open submanifolds of the model space). -/
def HasChartSourceConsistentChartAt
    (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop :=
  ∀ α : M, ∀ b ∈ (chartAt H α).source, chartAt H b = chartAt H α

namespace HasChartSourceConsistentChartAt

variable {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The chart-source-consistency predicate implies the locally-constant
predicate at every point of the manifold: on any chart source, the chart is
constant, and every point lies in its own chart source. -/
theorem toHasLocallyConstantChartAt
    (h : HasChartSourceConsistentChartAt H M) :
    HasLocallyConstantChartAt H M := by
  intro b₀
  have hb₀_src : b₀ ∈ (chartAt H b₀).source := mem_chart_source H b₀
  have hopen : IsOpen (chartAt H b₀).source := (chartAt H b₀).open_source
  refine Filter.eventually_of_mem (hopen.mem_nhds hb₀_src) ?_
  intro b hb
  exact h b₀ b hb

end HasChartSourceConsistentChartAt

/-- The model space `H`, viewed as a charted space over itself via
`chartedSpaceSelf`, has chart-source-consistent chart selection. In fact,
the chart selection is globally constant: `chartAt H b = OpenPartialHomeomorph.refl H`
for every `b : H`. -/
theorem hasChartSourceConsistentChartAt_self
    (H : Type*) [TopologicalSpace H] :
    HasChartSourceConsistentChartAt H H := by
  intro _ _ _
  rfl

end Geometry
end DifferentialGeometry
