# Raw exponential-domain smoothness

## Scope and endpoint

This module targets the raw, maximal-geodesic exponential map.  Its public
endpoints are `expMap_contMDiffAt`, `isOpen_expDomain`, and
`expMap_contMDiffOn`, together with the raw radial curve globalization
`exists_raw_ray_ext`, under only finite-dimensionality, boundarylessness, and
Hausdorffness of the tangent-bundle phase manifold.  It does not assume metric
completeness of `M` and does not use the intrinsic exponential map.

## Mathematical route

For a velocity in `expDomain`, choose its existing open preconnected
time-one witness and a compact subinterval strictly containing `[0, 1]`.  The
lifted integral curve has compact image on that subinterval.  A smooth compactly
supported cutoff on the tangent-bundle phase manifold is one on a neighborhood
of this image.  Multiplying the global geodesic vector field by this cutoff
gives a complete smooth vector field.

Uniqueness identifies its global integral curve with the original lift on the
smaller time interval.  Joint continuity of the complete cutoff flow and the
generalized tube lemma then give one phase-space neighborhood whose trajectories
remain in the cutoff-one set through time one.  Every fixed-base velocity in
that neighborhood therefore supplies a genuine raw maximal-geodesic witness.
`maximalGeo_eqOn` identifies its time-one projection with `expMap`.  Smoothness
of the complete cutoff flow gives a smooth local representative of `expMap`.

The same neighborhood data proves openness of `expDomain`; pointwise
smoothness then gives the on-domain statement without another construction.

For `exists_raw_ray_ext`, the inverse image of `expDomain` under the radial line
`t ↦ t • u` is open.  Compactness of `[0,L]` supplies a buffered time interval
inside that inverse image.  A global smooth time clamp takes values in the
buffer and is the identity on an open neighborhood of `[0,L]`.  Composing the
raw exponential map with this clamped radial line gives the required global
smooth curve, and the identity neighborhood gives germ equality at every time
in the original segment.

## Reused API

- `exists_bump_nhds` for the compact-image cutoff.
- `geodesicVF_smooth` and `ContMDiff.smul_section` for the cutoff field.
- `exists_globalIntegralCurve_of_compactSupport` and
  `contMDiff_globalFlow_joint_of_compactSupport` for the complete smooth flow.
- `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless` for equality with
  the original lifted witness.
- `generalized_tube_lemma` for uniform time-one control near the initial lift.
- `maximalGeo_eqOn` for identification with the choice-based raw exponential.
- `isCompact_Icc.exists_cthickening_subset_open` for the uniform radial time
  buffer.
- `exists_smooth_time_clamp` for the global smooth reparameterization.

The fixed-fiber inclusion into the tangent bundle is proved privately from the
tangent-bundle trivialization.  Its coordinate identity currently exists in a
higher `MaximalRescaling` module whose imports would be inappropriate here, so
only the small low-layer trivialization argument is kept locally.

## Alternatives not used

1. Chaining finitely many chart flows along the witness would reintroduce the
   chart-flow smoothness hierarchy and require explicit transition matching.
2. A maximal-flow-domain theorem would be shorter, but the current repository
   has no directly reusable manifold theorem identifying that domain with raw
   `expDomain` while providing smooth dependence.
3. Importing intrinsic exponential smoothness would add metric completeness and
   reverse the intended dependency direction.

## Verification and project status

Source writing is complete with no placeholder, `sorry`, or new assumption
wrapper.  The focused file verification passed without warnings, so all four
public theorems are now verified in their defining module.  The first
globalization check exposed only an incorrect model-notation glyph; correcting
that local source typo closed the proof without changing its route.  The
dedicated implementation is complete; no downstream module refresh or build
was run in this lane.

This is only raw smoothness/domain and interval-globalization machinery.  The
P1b E1/E2 theorem endpoints remain unstated at 0%; their dedicated machinery
remains about 94%, aggregate P1 remains 78.6%, and the whole Poincaré theorem
endpoint remains unstated at 0%.  This producer removes the curve-globalization
premise for the next interval-local parallel-frame adapter but does not prove
that frame or the curvature-to-raw-derivative injectivity gate.
