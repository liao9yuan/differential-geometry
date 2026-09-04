# MaximalUniqueness

## Mathematical route

`maximalGeo_eqOn` compares an arbitrary geodesic with prescribed initial tangent lift
to the choice-based `maximalGeodesic`.  At a supported time, both curves provide
maximal-interval witnesses.  Their lifted curves solve the same global geodesic vector
field on the intersection of two open preconnected intervals and agree at time zero, so
`gvf_eqOn` identifies the lifts and hence their projections.

## Reuse

- Reuses `maximalGeodesic_of_mem` and `maximalGeodesicChosenCurve_spec` without changing
  the established maximal-geodesic representation.
- Reuses the source-free global uniqueness theorem `gvf_eqOn`.
- The intersection is preconnected because preconnected subsets of `ℝ` are order
  connected and intersections of order-connected sets are order connected.

## Verification

Focused verification and the explicit downstream-required module refresh passed without warnings.
