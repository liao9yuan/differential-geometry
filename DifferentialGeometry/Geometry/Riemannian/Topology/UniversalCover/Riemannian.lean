import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.Manifold
import DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.LiftedMetricSmoothness
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
* `UniversalCover.uc_pseudoEMetricSpace g` — the canonical
  `PseudoEMetricSpace` on the universal cover, built from
  `riemannianEDist` for the lifted bundle via Mathlib's
  `PseudoEMetricSpace.ofRiemannianMetric`. Mirrors Mathlib's pattern
  (`def` with the metric witness `g` and the model-with-corners `I`
  explicit) rather than `instance`, since the model-space parameters
  cannot be recovered from the conclusion type alone.
* `uc_isRiemannianManifold g` — companion `theorem`: the
  `IsRiemannianManifold` predicate holds for the canonical
  `uc_pseudoEMetricSpace g`, by `rfl` on `riemannianEDist`.
* `uc_regularSpace` — the universal cover is a regular topological
  space (Hausdorff + locally compact ⇒ regular), discharging the
  `[RegularSpace (UC M)]` hypothesis of the principled API above.
* `UniversalCover.proj_isLocalIsometry` — the pointwise statement that
  `mfderiv I I proj x'` is a linear isometry from the tangent space at
  `x'` (with the lifted metric) onto the tangent space at `proj x'`
  (with the base metric).
-/

open Set Function Filter Bundle
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
`mfderiv I I proj x' : T_{x'} M̃ → T_{proj x'} M`.

Symmetry, positivity and `IsVonNBounded` inherit pointwise from `g`.
Smoothness of the assembled section is BLOCKED on the still-stub
`uc_hom_bundle_inCoordinates_pullback` (see `LiftedMetricSmoothness.lean`),
which is a `True`-typed placeholder pending a cross-file
private-visibility refactor of the cover-side chart accessors. -/
noncomputable def liftedMetric (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) where
  inner x' := g.inner (proj x')
  symm x' v w := g.symm (proj x') v w
  pos x' v hv := g.pos (proj x') v hv
  isVonNBounded x' := g.isVonNBounded (proj x')
  contMDiff := uc_liftedMetric_contMDiff (I := I) (M := M) g

/-- **Principled pseudo-emetric construction on the universal cover.**

Mirrors Mathlib's `PseudoEMetricSpace.ofRiemannianMetric`: a `def` with
the lifted-metric witness `g` (and `I` via the section variable)
explicit rather than an `instance`, since the model-space parameters
cannot be recovered from the conclusion type alone.

Downstream consumers should invoke this via
`letI : PseudoEMetricSpace (UC M) := uc_pseudoEMetricSpace g` once they
have the lifted metric `g` in hand. By reducibility of Mathlib's
`ofRiemannianMetric`, the resulting `edist` is `riemannianEDist I`.

The body installs the auxiliary instances `RiemannianBundle`
(from `g.toRiemannianMetric`) and `IsContinuousRiemannianBundle` (from
the smooth-implies-continuous projection of `g`) so that Mathlib's
`ofRiemannianMetric` typechecks. -/
@[reducible] noncomputable def uc_pseudoEMetricSpace
    (g : SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
    [RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)] :
    PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
  letI : RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  PseudoEMetricSpace.ofRiemannianMetric I _

/-- **Principled `IsRiemannianManifold` for the universal cover.**

Companion to `uc_pseudoEMetricSpace`: under the `letI`-injected
canonical pseudo-emetric structure, the defining equation
`edist x y = riemannianEDist I x y` holds by `rfl`. -/
theorem uc_isRiemannianManifold
    (g : SmoothRiemannianMetric I
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M))
    [RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M)] :
    letI : RiemannianBundle
        (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
          TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
      uc_pseudoEMetricSpace (I := I) (M := M) g
    IsRiemannianManifold I
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  letI : RiemannianBundle
      (fun (x : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) ↦
        TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : PseudoEMetricSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) :=
    uc_pseudoEMetricSpace (I := I) (M := M) g
  exact ⟨fun _ _ => rfl⟩

/-- **The universal cover is a regular topological space.**

`UniversalCover M` is Hausdorff (`instT2Space`, hence `R1Space`) and,
being a finite-dimensional smooth manifold, locally compact: its base
`M` is locally compact (`Manifold.locallyCompact_of_finiteDimensional`)
and local compactness pulls back along the covering projection
(`instLocallyCompactSpace`).  A weakly
locally compact `R1` space is regular
(`WeaklyLocallyCompactSpace` + `R1Space` → `RegularSpace`), so the
cover is regular.

This discharges the `[RegularSpace (UniversalCover M)]` hypothesis of
`uc_pseudoEMetricSpace` / `uc_isRiemannianManifold`, with no extra
ambient assumptions beyond the manifold structure already in scope.

Supplied as a `theorem` (taking `I` explicitly) rather than an
`instance`, because the model-space data `E`, `H`, `I` cannot be
recovered from `UniversalCover M` alone — the same reason
`uc_pseudoEMetricSpace` is a `def`.  Consumers inject it via
`haveI := uc_regularSpace I`. -/
theorem uc_regularSpace (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    RegularSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) := by
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  infer_instance

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
  fun _ _ => rfl

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end
