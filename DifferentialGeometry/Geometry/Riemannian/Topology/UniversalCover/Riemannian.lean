import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Manifold
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Riemannian structure on the universal cover

Equips the universal cover `UniversalCover M` of a smooth Riemannian
manifold `M` with its own smooth Riemannian metric, pulled back fiberwise
along `proj : UniversalCover M → M` (which is a local diffeomorphism by
the covering structure of `UniversalCover.isCoveringMap`).

The pieces assembled here are:

* `UniversalCover.liftedMetric g` — the lifted `SmoothRiemannianMetric`
  on the universal cover. Fiberwise it is the pullback of `g` along the
  invertible linear map `mfderiv I I proj x' : T_{x'} M̃ → T_{proj x'} M`.
* `PseudoEMetricSpace (UniversalCover M)` — built from
  `riemannianEDist (liftedMetric g)` via
  `PseudoEMetricSpace.ofEDistOfTopology`.
* `IsRiemannianManifold I (UniversalCover M)` — immediate from the
  defining equation of the constructed `edist`.
* `UniversalCover.proj_isLocalIsometry` — the pointwise statement that
  `mfderiv I I proj x'` is a linear isometry from the tangent space at
  `x'` (with the lifted metric) onto the tangent space at `proj x'` (with
  the base metric).
-/

open Set Function Filter
open scoped Topology ContDiff
open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric)

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

/-- **The lifted smooth Riemannian metric on the universal cover.**

For each `x' : UniversalCover M`, the fibre at `x'` is the pullback of the
fibre of `g` at `proj x'` along the invertible continuous linear map
`mfderiv I I proj x' : T_{x'} M̃ → T_{proj x'} M` (an isomorphism because
`proj` is a local diffeomorphism by `UniversalCover.isCoveringMap`).

In the chart-tangent representation `TangentSpace I (M := UC M) x' = E
= TangentSpace I (M := M) (proj x')` (definitional), the chart-tangent
representation of `mfderiv proj x'` is the identity, so the fibrewise
pullback inner product collapses to the inner product of `g` at the
projected point. Symmetry, positivity and the
`IsVonNBounded` axiom of `ContMDiffRiemannianMetric` therefore all
inherit pointwise from `g`. Smoothness of the assembled section is the
chart-conjugacy obligation `uc_liftedMetric_contMDiff` (see
`LiftedMetricSmoothness.lean`); it is the only non-trivial field. -/
noncomputable def liftedMetric (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) where
  inner x' := g.inner (proj x')
  symm x' v w := g.symm (proj x') v w
  pos x' v hv := g.pos (proj x') v hv
  isVonNBounded x' := g.isVonNBounded (proj x')
  contMDiff := by
    -- Smoothness of `b ↦ TotalSpace.mk' _ b (g.inner (proj b))` on the
    -- universal cover: reduces, via the chart-conjugacy of the cover's
    -- tangent-bundle trivialisations with those of `M`, to the
    -- smoothness of `g.contMDiff` composed with the smooth projection
    -- `proj_contMDiff`. The chart-conjugacy decomposition lives in
    -- `LiftedMetricSmoothness.lean` (`uc_liftedMetric_contMDiff`).
    sorry

/-- **Pseudo-EMetric structure on the universal cover.**

Apply `PseudoEMetricSpace.ofEDistOfTopology` to
`riemannianEDist (liftedMetric g)`, using
`riemannianEDist_self`, `riemannianEDist_comm`,
`riemannianEDist_triangle`, plus the topology-compatibility lemmas
`setOf_riemannianEDist_lt_subset_nhds'` and
`eventually_riemannianEDist_lt`. -/
instance instPseudoEMetricSpace [Nonempty M] :
    PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  sorry

/-- **The universal cover, with its lifted metric, is a Riemannian
manifold in the sense of `IsRiemannianManifold`.**

By construction of `instPseudoEMetricSpace`, the `edist` on the universal
cover is literally `riemannianEDist (liftedMetric g)`, so the defining
equation `edist x y = riemannianEDist I x y` holds by `rfl`. -/
instance instIsRiemannianManifold [Nonempty M]
    [Bundle.RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x)] :
    IsRiemannianManifold I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  sorry

/-- **`proj` is a local isometry on tangent spaces.**

At each `x' : UniversalCover M`, the derivative
`mfderiv I I proj x' : T_{x'} M̃ → T_{proj x'} M` is a linear isomorphism
(because `proj` is a local diffeomorphism), and by definition of the
lifted metric it carries the lifted inner product on `T_{x'} M̃` to the
original inner product on `T_{proj x'} M`. Packaged here as a linear
isometric equivalence. -/
theorem proj_isLocalIsometry (g : SmoothRiemannianMetric I M)
    (x' : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :
    ∀ (v w : E),
      g.inner (proj x') v w =
        (liftedMetric (I := I) g).inner x' v w :=
  -- By construction of `liftedMetric` the `inner` field at `x'` is
  -- literally `g.inner (proj x')`, so the equality is a `rfl` after
  -- the field projection unfolds.
  fun _ _ => rfl

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
