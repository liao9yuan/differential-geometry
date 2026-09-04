# MovingDistance

## Route

The final smooth moving-endpoint estimates are a thin mathematical assembly of
three proved ingredients: the short or long fixed-endpoint support, the local
first-order endpoint displacement bound for the backward-time metric, and the
abstract triangle/support slope transfer.  The short and long cases remain
separate so the long theorem does not acquire the unused assumption `0 ≤ K`.

The endpoint regularity is local `C¹` at the base time.  This is exactly what
the direct curve-segment proof of the varying-metric endpoint bound consumes;
no completeness, global curvature bound, ancient-flow assumption, or surgery
object is added for endpoint motion itself.

For compact-interval regularity, `dist_lip_Icc` combines the fixed-reference
endpoint bound `edist_curve_lip` with the two-time metric comparison
`edistEquiv_Icc`.  The public hypothesis is the honest global absolute Ricci
quadratic bound on the regular time slab.  Internally the proof replaces its
constant by `max K 0`, bounds both endpoint motions in a fixed reference
metric, and uses the triangle inequality plus the exponential metric factor.
`dist_ac_Icc` is the direct absolute-continuity projection of that Lipschitz
theorem.  Neither theorem assumes completeness, Harnack, ancientness, or any
surgery object.

`dist_ac_rm` is the complete bounded-curvature adapter needed by the reduced-
geometry consumer.  It reuses `twoTensorQuadBound_of_solutions` to contract the
global `Rm` norm-square bound to an absolute Ricci quadratic bound, reconciles
`metricRicciAt` with `ricciTensor`, and then applies `dist_ac_Icc`.  It adds no
ancient-flow, Harnack, nonnegative-curvature, or surgery assumption.

## Verification

The original smooth slope theorems, the compact-interval Lipschitz and absolute-
continuity theorems, and the curvature-bound adapter pass focused verification
warning-free.  The two
new upstream distance/metric producers were also focused-checked and exactly
refreshed before the consumer check.

## Progress

`dist_short_slope` and `dist_long_slope` are proved and warning-free focused
GREEN: each theorem endpoint is 100%.  Their dedicated smooth moving-endpoint
changing-distance machinery is 100%.  `dist_lip_Icc` and `dist_ac_Icc` are
also proved and warning-free focused GREEN: the compact-interval moving-
distance Lipschitz/AC endpoint is 100%.  The complete bounded-curvature adapter
`dist_ac_rm` is also a proved, warning-free focused-GREEN theorem endpoint.
The exact module refresh and the unified 61-declaration audit are GREEN; every
printed declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.
