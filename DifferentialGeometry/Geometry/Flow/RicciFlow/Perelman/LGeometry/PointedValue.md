# Pointed restricted L-values

This module assembles the pointed fixed-competitor upper bound with the
fixed-chart lower-semicontinuity theorem for varying regularized actions.
The target is convergence of restricted same-clock segment values when exact
source and limit minimizers satisfy explicit compact/chart confinement.

The confinement and weak time-H1 data are hypotheses of this smooth pointed
stability interface.  Producing them from ancient-flow coercivity is a separate
P3 input; no kappa-solution, surgery, or RFWS structure is introduced here.

## Verification

The first focused pass exposed only a missing `WithTop Real` topology import and
a deterministic local heartbeat limit while elaborating the full two-sided
assembly.  The canonical order topology import and an explicit scalar-curve
application removed both issues without changing the statement or assumptions.

`lSegValue_pt_lim` is warning-free focused green and exact-refresh green.  It
combines the checked fixed-competitor limsup with the checked varying-action
liminf, first proving convergence in `Real` and then applying the continuous
coercion to `WithTop Real`.  Exact source and limit attainers plus explicit
compact/chart confinement remain honest hypotheses; geometric production of
that confinement is not hidden here.
