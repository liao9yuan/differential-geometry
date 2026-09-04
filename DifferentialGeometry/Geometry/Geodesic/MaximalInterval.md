# MaximalInterval

## Global-vector-field migration

`IsGeodesicOnWithInitial` now records an integral curve of the global
`geodesicVectorField g`.  Its name, parameters, projection equation, prescribed
initial lift, and existential shape are unchanged.  The definitions
`MaximalGeodesicWitness`, `maximalGeodesicInterval`, and `maximalGeodesic` also
retain their previous shapes.

The initial witness is produced directly from `geodesicVF_smooth` and the
generic boundaryless-manifold local ODE theorem.  It no longer starts with a
fixed-chart vector field.

At an interior time, `IsGeodesicOnWithInitial.geoAt` intersects the supplied
time neighborhood with the inverse image of the chart source centered at the
current foot point.  Continuity of the global integral curve supplies this
chart neighborhood, and `chart_vf_on_iff` converts the restricted global
integral curve to the existing chart-based `IsGeodesicAt` predicate.

## Public API

The weakest canonical endpoints are:

- `IsGeodesicOnWithInitial.geoAt`, with no fixed-initial-chart source premise;
- `exists_geoAt_of_mem` and `exists_geoAt_zero`, with no source-control
  function and no `CompleteSpace E` assumption;
- `maximalGeo_structure`, with no foot-in-source premise.

The previous source-hypothesis endpoints remain thin compatibility wrappers:
`IsGeodesicOnWithInitial.isGeodesicAt`,
`exists_isGeodesicAt_of_mem_maximalGeodesicInterval`,
`exists_isGeodesicAt_zero_of_mem_maximalGeodesicInterval`, and
`maximalGeodesic_structure_of_footInSource`.  Their source hypotheses are
retained only for call-site compatibility and are no longer consumed.

The global vector-field foundation handles the zero-dimensional model
separately, so the local-existence and source-free maximal-interval endpoints
retain the previous weakest signatures and do not require
`NeZero (Module.finrank ℝ E)`.

## Resolved failure and verification

The first migration attempt failed because `CrossVFReduction` depended back on
`MaximalInterval`, producing duplicate declarations when imported here.  That
attempt was fully removed.  The cycle was resolved upstream by extracting
`geodesicVectorFieldChart_eq_geodesicVectorField`, `chart_vf_on_iff`, and
`geodesicVF_smooth` into the lower `GlobalVectorField` module; this file imports
that module directly and never `CrossVFReduction`.

Focused verification of the migrated file passed without warnings.  No
downstream artifact refresh was performed in this lane.

- Requested public support migration: 100% complete and checked.
- Canonical source-free maximal-interval support API: 100% complete, with old
  public source-taking entries retained as wrappers.
- Whole P1a compact-closure comparison theorem: not stated or proved here
  (0% theorem completion in this file); this migration is estimated below 2%
  of that larger assembly.
