# CGTWhiteheadProducer

## State — 2026-07-28

This module exposes the two public endpoints of the localized Whitehead lane.

- `intrCore_minimizingVec_regular_unique` proves that the selected minimizing
  launch is nonconjugate and is unique among every launch with the same
  endpoint and length equal to the true `riemannianEDistOf`.
- `intrCore_dist_germ` chooses the inverse branch at that launch and proves
  that its `branchEnergy` agrees near the endpoint with the true half-squared
  distance.

The second theorem uses finite-dimensional compactness to keep nearby selected
minimizers in the branch source.  It does not infer distance equality merely
from branch openness.  The hard uniqueness input is the proved
`intrCore_short_inj`; no cut-locus, global injectivity, or connectedness
assumption is exported.

Focused verification and the exact targeted refresh passed.  Direct axiom
audits for both public endpoints report only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`.

Accounting:

- `intrCore_minimizingVec_regular_unique`: theorem 100%, dedicated machinery
  100%;
- `intrCore_dist_germ`: theorem 100%, dedicated machinery 100%;
- `intrCore_jensen`: theorem 100%, dedicated machinery 100%;
- paper CGT Lemma 4.6: theorem 0%; dedicated machinery is about 90%;
- pointwise CGT producer: theorem 0%; dedicated machinery is about 80%;
- whole HCG supporting machinery: about 63%.

The canonical Jensen consumer is now proved in `CGTWhiteheadJensen.lean`.
The next frontier is the paper Lemma 4.6 propeller assembly, beginning with
the canonical loop-transport action and invariance of the finite-center
energy.
