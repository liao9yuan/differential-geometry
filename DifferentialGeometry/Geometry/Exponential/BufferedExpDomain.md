# BufferedExpDomain

## Compact-radius raw domain producer

`mem_expDom_of_cpt` packages the checked compact geodesic continuation
`exists_geo_one_cpt` into the repository's canonical raw `expDomain`.
The theorem assumes only that the initial tangent vector is shorter than a
radius whose closed eball is compact; it does not assume ambient completeness,
connectedness, or containment in a fixed chart.

The earlier fixed-chart obstruction disappeared when
`IsGeodesicOnWithInitial` was migrated to the global
`geodesicVectorField`.  The proof now takes the intrinsic geodesic supplied
through time one, forms its `velocityLift`, uses
`geoLift_isIntegralOn` for global phase support, checks the prescribed
initial lift, and assembles the existing `MaximalGeodesicWitness`.
No secondary domain or wrapper predicate is introduced.

## Verification and scope

Focused verification passed without warnings.  The first explicit named
refresh exposed and was unblocked by the global-support migration in
`ChartFlow/PreconnectedPropagation`.  The retry then stopped earlier in the
dependency chain at two corresponding chart/global support mismatches in
`ChartFlow/RescaledLift`; that source migration is in progress.  The producer
itself remains focused-green, and its refresh must be retried after that
dependency is green.

The latest focused recheck is again warning-free GREEN.  Its object artifact is
currently absent, so downstream `RadialSurjectivity.lean` stops at import
preflight until an exclusive-window named refresh is allowed; that absence does
not change this file's verified source status.

- `mem_expDom_of_cpt`: 100% complete and checked.
- Compact-radius raw `expDomain` membership machinery: 100%.
- The next minimizing-endpoint theorem identifying the choice-based
  `expMap` value with a prescribed endpoint is not yet stated or proved
  (0%).
- The compact-closure Bishop endpoint itself remains unstated and unproved
  (0%); this producer is infrastructure for that theorem, not the theorem.
