import Mathlib.Init

/-!
# Divergence theorem and integration by parts on manifolds with boundary

This module is the umbrella file for the with-boundary variant of the divergence
theorem and the associated integration-by-parts machinery on smooth Riemannian
manifolds whose model has a non-trivial boundary (i.e., where `[I.Boundaryless]`
is **not** assumed).

## Architecture

The boundaryless API in `DifferentialGeometry/Analysis/Integration/DivergenceTheorem/`
(`LocalFormula.lean`, `ChartInvariance.lean`, `Closed.lean`, `Proper.lean`,
`IntegrationByParts.lean`, `Green.lean`, `Family.lean`) is preserved unchanged.
The with-boundary variant is built as a parallel, independent API under the
present `WithBoundary/` sub-tree.

The two APIs agree on common ground (boundaryless manifolds, or sections /
functions whose support lies in the manifold interior). They diverge for inputs
that interact with the boundary, where the with-boundary API produces a
boundary integral term consistent with Stokes' theorem.

## Layered build-up

The sub-files are organised in successive layers, each independent of the
boundaryless API. The layers are loaded in order; later layers depend on
earlier ones.

### Interior-supported integration by parts

For an ambient manifold whose model `I` may have a boundary, but for inputs
whose support lies in `I.interior M`:

* `WithBoundary/Divergence/PartialDerivWithin.lean` — Fréchet partial
  derivatives on the chart target, defined via `fderivWithin` (well-posed on a
  half-space target thanks to `uniqueDiffOn_extChartAt_target`).
* `WithBoundary/Divergence/LocalFormula.lean` — chart-local Voss–Weyl
  divergence via within-derivatives; chart-invariance in the interior.
* `WithBoundary/Divergence/Global.lean` — global divergence on the manifold,
  with Voss–Weyl identity on chart sources.
* `WithBoundary/Divergence/POUReduction.lean` — Leibniz and POU sum identities.
* `WithBoundary/Divergence/InteriorCompactSupport.lean` — divergence theorem and
  proper-support variant for sections supported strictly in `I.interior M`.
* `WithBoundary/Divergence/IntegrationByParts.lean` — integration by parts and
  Green's identities for inputs supported in `I.interior M`.

### Boundary as a manifold

The boundary-manifold infrastructure — equipping `boundary I M` with a smooth
`(n-1)`-dimensional manifold structure when the model `I` admits a smooth
boundary, defining the induced Riemannian metric, and constructing the surface
measure — is first-class geometry and lives under `Geometry/Boundary/`.

* `Geometry/Boundary/ModelBoundary.lean` — the abstract `HasSmoothBoundary I`
  typeclass.
* `Geometry/Boundary/BoundaryManifold.lean` — `boundary I M` as a `ChartedSpace`
  and `IsManifold`.
* `Geometry/Boundary/InducedMetric.lean` — pull-back of the ambient Riemannian
  metric to the boundary submanifold.
* `Geometry/Boundary/SurfaceMeasure.lean` — Riemannian volume of the induced
  metric on the boundary.
* `Geometry/Boundary/EuclideanHalfSpaceInstance.lean` — `EuclideanHalfSpace n`
  as a `HasSmoothBoundary` instance.
* `Geometry/Boundary/OutwardNormal.lean` — outward unit normal vector field on
  the boundary, defined intrinsically via Riesz duality applied to a chart-local
  half-space-direction.

### Stokes' theorem and Green's identities

* `WithBoundary/BoundaryContribution/Stokes.lean` — divergence theorem with
  boundary integral.
* `WithBoundary/BoundaryContribution/GreenWithBoundary.lean` — Green's first and
  second identities with boundary terms.

### Time-dependent versions

* `WithBoundary/Divergence/Family.lean` — pointwise-in-time wrappers and
  time-derivative identities for time-parameterised metric families.

## Out of scope

Manifolds with corners (e.g., `EuclideanQuadrant n`) are **not** handled by the
present API. The boundary of a corner-modelled manifold is a stratified space,
not a smooth submanifold, so the outward normal is not single-valued and
Stokes' theorem requires Whitney-style integration over strata. The
`HasSmoothBoundary` typeclass deliberately excludes corner models. A future
parallel tree (`WithBoundary/Corners/`) could host such an extension without
disturbing the present API.
-/
