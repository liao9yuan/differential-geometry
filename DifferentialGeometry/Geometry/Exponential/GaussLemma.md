# GaussLemma notes

## 2026-07-01, normal-chart source projection

Added `memNChartSrcOfDist`, the direct source-membership projection of
`metricBall_subset_normalBall`: a point at finite Riemannian distance strictly
below `expRadiusGp g c` lies in `(normalChartAt g c).source`.

This keeps C4 code from unpacking the radial-vector existential when it only
needs the normal-chart source predicate. Verification passed for the edited
file and the targeted module build. The axiom probe reports only the usual
project axioms.

## 2026-07-09, public radial distance identity

Added `edist_exp_eq_radius`, a public wrapper around the existing private
radial-distance theorem.  A single intrinsic-radius hypothesis now supplies
the Euclidean normal-chart bound, exponential-domain membership, and
normal-chart-target membership internally.

This is the reusable bridge needed by C4 chart-bump support proofs: a bump
defined from the centre metric quadratic form can now be compared directly
with the Riemannian distance of its exponential image.  The edited file passed
focused verification.
