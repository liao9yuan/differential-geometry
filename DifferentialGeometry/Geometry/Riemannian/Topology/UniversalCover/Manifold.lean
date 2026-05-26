import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.CoveringMap

/-!
# Manifold structure on the universal cover

Equips the universal cover `UniversalCover M` of a smooth manifold `M`
with its own smooth-manifold structure, transported through the local
homeomorphism `proj : UniversalCover M → M` (which is a covering map by
`UniversalCover.isCoveringMap`).

The instances assembled here are:

* `ChartedSpace H (UniversalCover M)` — charts pulled back along the
  sheet homeomorphisms of the covering trivialisations.
* `IsManifold I ∞ (UniversalCover M)` — pulled-back chart transitions
  factor through the upstairs transitions in `contDiffGroupoid ∞ I`.
* `T2Space (UniversalCover M)` — separation lifts from `M` for distinct
  projections, and uses sheet-disjointness for distinct points over the
  same projection.
* `SigmaCompactSpace (UniversalCover M)` — assembled from σ-compactness
  of the base plus countability of the fibre (which equals the
  fundamental group, itself countable for second-countable manifolds).
* `LocallyCompactSpace (UniversalCover M)` — local compactness pulls
  back along the local homeomorphism `proj`.
-/

open Set Function Filter
open scoped Topology ContDiff

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

/-- **Charted-space structure on the universal cover.**

For each `x̃ : UniversalCover M`, choose an evenly-covered open
neighbourhood `U ∋ proj x̃` lying inside `(chartAt H (proj x̃)).source`;
take the unique sheet `S_{x̃}` containing `x̃` together with the
homeomorphism `e_{x̃} : S_{x̃} ≃ U` provided by the covering
trivialisation, and define `chartAt x̃ := e_{x̃} ≫ chartAt H (proj x̃)`. -/
noncomputable instance instChartedSpace :
    ChartedSpace H
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  sorry

/-- **The universal cover is a smooth manifold.**

The pulled-back charts of `instChartedSpace` have transitions that
agree, in a neighbourhood of every point, with the upstairs transitions
of `M`. The latter lie in `contDiffGroupoid ∞ I`, so the same holds
upstairs. -/
instance instIsManifold :
    IsManifold I ∞
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  sorry

/-- **The universal cover is Hausdorff.**

Two distinct cover-points either project to distinct points (separate
their projections in `M` and pull back the disjoint opens through
`proj`) or to the same point (use sheet-disjointness from the covering
trivialisation around that projection). -/
instance instT2Space :
    T2Space
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  ⟨sorry⟩

/-- **Countability of the fundamental group for second-countable
connected locally-simply-connected spaces.**

A polygonal-path approximation through a countable base topology: every
loop is homotopic to a path along edges of a countable simplicial
structure, of which there are only countably many up to homotopy. -/
theorem pi1_countable_from_secondCountable
    (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X]
    [ConnectedSpace X] [LocPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    (x : X) :
    Countable (FundamentalGroup X x) :=
  sorry

/-- **Countability of fibres of the universal cover.**

The fibre `proj ⁻¹' {x}` is in bijection with the fundamental group
`FundamentalGroup M x` (via `pi1-fibre-pi1-bijection`); the latter is
countable by `pi1_countable_from_secondCountable`. -/
theorem fibre_countable
    [SecondCountableTopology M]
    (x : M) :
    Countable
      ((proj :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M → M)
        ⁻¹' {x}) :=
  sorry

/-- **σ-compactness from σ-compact base and countable fibre.**

For a covering map `proj : E → X` with `[SigmaCompactSpace X]` and
countable fibres, a σ-compact exhaustion `K_n` of `X` is covered by
finitely many evenly-covered open sets; each preimage is a countable
disjoint union of compact sheets; the total preimage is then a
countable union of σ-compact pieces. -/
theorem sigmaCompact_from_countable_fibre
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [SigmaCompactSpace X] [T2Space X]
    {p : E → X} (hp : IsCoveringMap p)
    (hfib : ∀ x, Countable (p ⁻¹' {x})) :
    SigmaCompactSpace E :=
  sorry

variable [SecondCountableTopology M] [Nonempty M]

/-- **The universal cover is σ-compact.**

Combine `UniversalCover.isCoveringMap`, `fibre_countable`, and
`sigmaCompact_from_countable_fibre`. -/
instance instSigmaCompactSpace :
    SigmaCompactSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  sorry

/-- **The universal cover is locally compact.**

Local compactness pulls back along the local homeomorphism `proj`
provided by `UniversalCover.isCoveringMap`. -/
instance instLocallyCompactSpace :
    LocallyCompactSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  sorry

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
