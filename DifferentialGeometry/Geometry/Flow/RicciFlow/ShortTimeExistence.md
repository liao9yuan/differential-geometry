# ShortTimeExistence audit

## 2026-06-05 exhaustive source audit

Scope: the headline `ShortTimeExistence.lean`, the short-time assembly/flow
directories, the direct DeTurck and Pullback files used by the headline, and the
Hamilton consumer adapter.

What was learned:

- `ricci_flow_short_time_existence` returns a global
  `Real -> SmoothRiemannianMetric I M` family.  The chart-Gram hypotheses are
  coordinate read-offs from that global family, not independent local chart data.
- The actual proof-body `sorry`s in the short-time dependency surface are the
  DeTurck-Ricci parabolic short-time theorem and the Weyl/on-diagonal spectral
  analytic input.
- The old comment in `ShortTimeFlow/ConjugatingFlowProperties.lean` about a
  labeled flow-continuity `sorry` is not an active proof placeholder in the
  current source.
- A direct source check of `Pullback/Defs.lean` initially failed at the
  bilinear-pullback smoothness proof because the `flip` smoothness route was
  using the continuous-linear-map seminormed instance instead of the normed
  instance expected by `ContDiff`.  That was repaired in `Pullback/Defs.lean`.

Verification passed for the checked source files in this audit and for the
Hamilton consumer.  No target `.olean` refresh was run because the project lock
script is absent in this checkout and an existing Lake server is active; the
claim here is source-level focused verification.
