# GaussLemmaPullback

## Route

`raw_gauss_pullback` assumes only that the closed radial segment lies in the raw
`expDomain`.  Openness of `expDomain` and compactness of `Icc 0 1` give a
uniform transverse tube by `generalized_tube_lemma`.  The existing Gauss
variation then runs inside that tube, using raw exponential smoothness,
`raw_radial_geo_at`, and the resulting constant-speed identity.  Its conclusion
is the full pairing
`g (D exp_v v) (D exp_v w) = g_p(v,w)` consumed by the raw framed-exp layer.

The historical small-radius `gauss_lemma_pullback` is retained as a compatibility
wrapper: the radius bound supplies radial `expDomain` coverage, and the raw
pairing specializes to its diagonal and orthogonal conclusions.  The private
tube is not exposed as a new assumption or public API.

## Earlier global-support migration

The top-file change to
`radial_maximalGeodesic_hasGeodesicEquationAt_of_small` predates the raw Gauss
work.  `IsGeodesicOnWithInitial` now requires an integral curve of the global
`geodesicVectorField`, whereas the uniform chart-flow construction provides an
integral curve of `geodesicVectorFieldChart`.  At the selected time the latter,
together with the existing chart-source fact, constructs `IsGeodesicAt`
directly.  The obsolete initial-data witness and unused global source-radius
detour were therefore removed.  The explicit `NeZero` binder preserves the
previous public signature while avoiding an unused section-variable warning.

## Verification

The raw-domain refactor and compatibility wrapper passed focused verification
without warnings.  No dependency refresh or broader build was run.

## Project status

This raw Gauss producer is locally complete (100%).  The P1b E1/E2 endpoints
remain unstated here and therefore remain 0%; their broader incomplete-ambient
machinery is still only infrastructure, approximately 94% complete before this
producer is integrated.
