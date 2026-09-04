# Raw radial geodesicity

## Mathematical route

`raw_radial_geo_at` identifies the raw radial exponential curve with the
maximal geodesic germ at every supported time.  Openness of `expDomain` keeps
nearby scaled vectors supported.  The nonzero rescaling theorem
`expMap_smul_max_ne` gives the identification away from the pole, while the
stationary identities supply the value at zero.  The chosen maximal-geodesic
witness then provides the geodesic equation, which is transported across the
two germ equalities.

The theorem needs no metric completeness, intrinsic exponential map, Ricci
bound, or norm hypothesis.  It lives above both the raw-domain smoothness and
maximal-rescaling modules so neither lower layer gains a reverse dependency.

## Reused native API

- `isOpen_expDomain`
- `expMap_smul_max_ne`
- `maximalGeo_eqOn`
- `IsGeodesicAt.hasGeodesicEquationAt`
- `HasGeodesicEquationAt.congr_of_eventuallyEq_at`

## Verification

Focused verification passed without warnings.  No refresh or build was run
during the parallel-task window.

This is infrastructure only.  The compact-closure Bishop--Gromov endpoint is
still unstated and remains 0% complete.
