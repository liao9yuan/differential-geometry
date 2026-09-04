# Raw core regularity producer

## Status

rawCore_min_regular is warning-free focused GREEN. It is a raw complete-
extension regularity producer, not a strict-Jensen theorem, and does not
identify branch energy with the actual pullback half-squared distance.

Its first focused check reached the complete-extension launch identification:
rawExtJoin retains its native zero-dimensional conditional, while this theorem
is already in the positive-finrank CGT section. The source now discharges that
conditional directly with the ambient NeZero fact before the next focused
check.

The next check reduced the conditional and exposed an instance mismatch:
the Producer had selected an EMetricSpace while rawExtJoin selects the native
PseudoEMetricSpace directly. The Producer now uses that same extension metric
instance. A subsequent focused retry still leaves exactly
`rawExtLaunch ... u = rawExtJoin ... pt q`: rawExtJoin hides the local canonical
metric-norm/minimizing-vector witness used to define its minJoin. No equality
assumption or wrapper was added. `CGTRawExtJoin.rawExtJoin_eq_min` now exports
that canonical witness bridge after warning-free focused verification and exact
refresh; this Producer consumes it directly, and its focused recheck is GREEN.

## Route

The theorem takes raw-core endpoints, the whole-ball raw exponential-domain
hypothesis, and the raw curvature bound. It obtains a scale L from the public
CGTScale.exists_short_scale theorem, bounds the complete-extension minimizing
vector by rawExt_edist_le and minimizingVec_len, identifies that launch with
rawExtJoin, obtains its fence from rawExtJoin_fenced, and invokes
rawExt_no_conj. Its conclusion uses the native IsConjVec exponential API, whose
existing CGT section already carries the positive-finrank instance; the theorem
does not add another hypothesis or construct a shadow instance.

## Frontier

The actual raw half-squared-distance strict-Jensen theorem is not yet stated
(0%). Its supporting branch-energy Hessian brick, rawExt_no_conj bridge, and
rawCore_min_regular are verified. The next consumer must prove a germ equality
with the actual distance before using any branch-energy Hessian fact.

The former launch-identification API gap is closed by `rawExtJoin_eq_min`.

## Current source route

`rawExt_minVec_mem` is the private raw complete-extension continuity bridge:
it confines every convergent-endpoint minimizing-vector sequence in a compact
metric-length ball, extracts a convergent subsequence, and applies the supplied
unique minimizer conclusion.  It uses completeness only for the extension on
the model space; it adds neither `CompleteSpace M` nor an ambient
`SigmaCompactSpace M` requirement.  Its focused recheck is warning-free GREEN.

`rawCore_dist_germ` is now source-written but intentionally unchecked until
the shared `rawCore_short_inj` export lands.  Its direct existential conclusion
states a germ on `rawPullBall`, with `branchEnergy` equal to the actual raw
pullback half-squared distance.  The proof obtains no conjugate endpoint from
`rawCore_min_regular`, turns short-bigon exclusion into the minimizer
uniqueness needed by `rawExt_minVec_mem`, and applies `branchEnergy_min_germ`.
It then restricts the extension germ along the subtype inclusion and uses
`rawCore_edist_eq` only on a strictly enlarged local norm core.  No branch
energy is substituted for the actual distance, and no extra completeness or
ambient-Sigma hypothesis is introduced.

## Jensen assembly audit

The shortest honest `rawCore_jensen` consumer has the same public conclusion
as `intrCore_jensen`, with `rawPullBall`, `rawCore`, and `rawPullMetric`: it
supplies one join and proves `CenterOfMass.StrictMidJensenOn join (rawCore R a)`
for every center in the core.  Its strict-convexity chain is already native:
`rawCore_dist_germ`, `rawBranch_hess_pos`, `deriv2_geo_on_at`,
`strictConvexOn_of_deriv2_pos`, and `CenterOfMass.jensen_of_strict`.

The remaining non-negotiable input is core-segment closure for the fenced
extension join.  The intrinsic implementation obtains it from
`intrExt_edge_core`; current raw sources expose `rawExt_short_fenced` and a
private scale estimate but initially had no public raw edge-core theorem.
`CGTRawBigon` has now source-written `rawExt_edge_core`, so
`rawCore_jensen` is source-written directly after `rawCore_dist_germ`.

The theorem chooses the existing fenced pullback geodesic only on core
endpoints, proves its entire segment remains in the raw core through
`rawExt_edge_core`, and applies the actual-distance germ along the segment.
At an interior parameter it converts the subtype germ to the extension
calculation only after `rawCore_edist_eq`; the branch energy is never used as
a replacement definition of the distance.  The final chain is
`rawBranch_hess_pos`, `deriv2_geo_on_at`,
`strictConvexOn_of_deriv2_pos`, and `CenterOfMass.jensen_of_strict`.
This source remains unchecked until the pending `rawCore_short_inj` producer
is exported and refreshed as coordinated.
