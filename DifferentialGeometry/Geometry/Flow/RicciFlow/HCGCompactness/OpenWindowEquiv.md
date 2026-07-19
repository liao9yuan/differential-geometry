# OpenWindowEquiv

## Purpose

`OpenWindowEquiv.lean` owns only the order-zero time-direction estimate needed
by the P4 producer.  It converts the uniform Riemann-curvature bound on one
canonical compact window into:

- a Ricci quadratic coefficient chosen before the sequence member;
- a finite majorant for the exponential metric-equivalence factor; and
- uniform equivalence of every member's time-slice metrics to its time-zero
  metric on that window.

This is separate from complete-noncompact Shi estimates, varying-source
covariant induction, Step-D provenance, and bump localization.

## Current status

The theorem `CurvBoundInput.metricEquiv_open` is stated and awaiting focused
verification.  It uses the existing arbitrary-dimensional Ricci trace bound
and the checked Ricci-flow metric-equivalence theorem; it introduces no new
geometric hypothesis.  The latest focused check stopped before elaborating this
file because the interrupted shared refresh temporarily left
`Geometry/Exponential/GaussLemma.olean` absent.  The H6 framed-coordinate lane
currently owns restoration of that import chain, so no competing targeted
build was started here.

A source-only audit while that refresh is paused confirmed that the calls to
`CurvBoundInput.bound_on_window`, `twoTensorQuadBound_of_solutions`, and
`metricUniformEquivalentOnWindow_of_solutions'` have the intended constants-first
quantifier order.  This is not a verification result: elaboration still awaits
the shared `GaussLemma` repair chain.

The theorem itself is currently 0% until focused verification passes.  Its
dedicated assembly is approximately 80%; the unconditional `compactnessSol`
endpoint remains 0%, and whole-HCG support machinery remains approximately
60%.
