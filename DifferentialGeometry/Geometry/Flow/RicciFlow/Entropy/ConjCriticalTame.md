# ConjCriticalTame

## Role

`scalar_crit_tame` is the solution-specific finite-core closure needed by the
scalar non-autonomous Galerkin energy hierarchy.  It combines the genuine
moving-minus-frozen scalar Laplacian with the time-reversed conjugate-heat
potential `-R` on one common terminal-time interval.

The theorem chooses the interval and the full order-indexed lower-constant
family before the time, Sobolev order, finite spectral set, and finite-support
vector.  The A2 top coefficient is `5/3`; the A1 coefficient is `1/4`; hence
the combined coefficient is `23/12 < 2` and leaves coercivity `1/12`.

## Current state

The solution-specific source has been written without a new consumer
assumption or chart-local-constancy hypothesis.  Its one-interval generic A2
producer `cc_a2_unif` is now source-complete in the lower Garding layer; the A1
arm uses `cc_a1_unif` and `conjCoeff_rev`.  Focused verification of this full
dependency chain is still pending while shared upstream object-file writers
are active.

The next genuine analytic frontier after this theorem verifies is scalar
time-dependent finite-dimensional Galerkin ODE existence, followed by the
Galerkin limit and identification with the existing strong solution.  The
existing DeTurck ODE/limit files are specialized to `(0,2)` tensors and cannot
serve as the scalar producer directly.

## Honest progress

- `scalar_crit_tame`: source written, theorem completion remains 0% until Lean
  verification succeeds; dedicated source-level machinery is approximately
  96%.
- Scalar Galerkin ODE existence: not started (0%).
- `heatpot_of_maxreg`: not started as a theorem (0%); dedicated reusable
  machinery is approximately 35%.
- Classical moving conjugate heat: theorem-level 0%; dedicated machinery is
  approximately 77%.
- Perelman no-local-collapsing and `ham3_noncollapse`: theorem-level 0%;
  dedicated analytic machinery is approximately 42%.
- Whole HCG compactness machinery is approximately 54%; endpoint theorems
  remain 0%.
