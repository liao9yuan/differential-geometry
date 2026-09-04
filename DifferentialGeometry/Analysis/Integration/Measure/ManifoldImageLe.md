# ManifoldImageLe

## 2026-08-30: noninjective manifold image bound

### Mathematical route

- `mapJacDensity` is the coordinate-free Gram-Jacobian density of a map from
  the model vector space to a Riemannian manifold. It is the square root of the
  determinant of the metric Gram matrix of the images of the fixed model
  basis under `mfderiv`.
- `riemVol_image_le` assumes only that the map is `C¹` on an open neighborhood
  of a compact source set. Compactness makes both the source and its continuous
  image measurable. No injectivity or global smoothness is assumed.
- The proof localizes each partition-of-unity summand to a target chart,
  extends the chart-coordinate map measurably by zero, and applies the existing
  weighted noninjective Euclidean image inequality. A private determinant
  calculation identifies the coordinate determinant times chart density with
  `mapJacDensity`; summing the partition of unity gives the Riemannian-volume
  bound.
- All chart-basis and determinant support lemmas are private. The module stays
  in the integration/measure layer and does not import comparison geometry.

### Verification and progress

The source is complete, contains no placeholder, and passed a warning-free
focused check. The public `riemVol_image_le` theorem and its dedicated local
machinery are therefore 100% complete in this module.

## 2026-09-01: public Jacobian continuity

- `mapJac_contOn` is now public with its original weakest signature: an open
  source set and `C¹` manifold-map regularity imply continuity of
  `mapJacDensity` on that set. Its existing chart-local proof is unchanged.
- This is the lowest reusable bridge required by the raw-polar Fubini argument
  for the incomplete-ambient Bishop volume-ratio lane. It adds neither a
  completeness assumption nor comparison-geometry dependencies.
- The module is warning-free focused-check GREEN after this visibility change.

This module is a reusable measure-theoretic producer. The raw exponential
corollary and its Jacobi-density identification are separate downstream work;
the final compact-closure Bishop endpoint remains 0% until those consumers are
stated and verified.
