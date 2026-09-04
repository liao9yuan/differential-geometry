# PointedActionLower

## Route

The pointed lower-semicontinuity endpoint is factored through explicit compact
confinement.  Its first local producer is the compact-range version of the
energy-bounded curve subsequence theorem: compact Arzelà--Ascoli uses the
supplied common compact range rather than a global `CompactSpace` instance.
The local fixed-endpoint adapter preserves both endpoint values after
subsequence extraction.

The pointed-action endpoint now combines the fixed-chart weak kinetic liminf
with scalar-curvature convergence on the explicitly confined compact set.
`lRegAction_pt_lsc` identifies the limit chart quadratic form with the limit
flow metric, identifies the source forms almost everywhere with the mapped
term-flow kinetic energies, proves scalar-potential convergence by dominated
convergence, and then applies a bounded liminf-plus-limit argument to the
actual regularized actions.

The desired HCG theorem is `ConvOut.chartGram_convOn`: for a fixed chart, a
compact coordinate set, compact-window times, uniformly convergent coordinate
paths `u k -> uLim`, and eventual membership in that coordinate set, the Gram
operators built from `gSeqExt ... (co.phi k)` converge uniformly to those built
from `co.gInf`.  Its small generic input should be
`chartGramOp_diff_le`: on one compact chart set, the operator norm of the
fixed-chart Gram difference is at most a compact constant times
`metricDerivNorm ... 0`.

Three routes were checked.  Reusing `ConvOut.kinetic_convOn` fails because its
velocity is fixed while the minimizer derivatives vary.  Comparing complete
actions first still needs the same operator estimate to control the varying
kinetic integrals.  Reusing compact-manifold `lAction_consts` fails honestly
without a global `CompactSpace`; explicit confinement supplies compactness of
the curves, not compactness of the entire manifold.  The direct chart route is
therefore the smallest native route.

Local elaboration failures in the final assembly were confined to interval
orientation, the `a + r` versus `r + a` shift, explicit compatible uniform
structures for the varying manifolds, and the exact unrestricted-measure shape
required by interval dominated convergence.  The proof uses the native
`uIoc`/`uIcc` conversions and a metrizable uniformity compatible with each
stored manifold topology; it does not add a public topology or compactness
assumption.

## Verification

The compact-confined energy subsequence producer and fixed-endpoint adapter
pass warning-free focused verification.
The public `lRegAction_pt_lsc` endpoint also passes warning-free focused
verification and exact named refresh.  The unified 70-declaration P2 audit
includes this endpoint and all eight new direct producers; each uses only
`propext`, `Classical.choice`, and `Quot.sound`.
