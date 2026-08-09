# PrincipalPerturbH2

## Purpose

This module builds the fixed-background linear perturbation of the
Ricci--DeTurck principal coefficient as a continuous linear map from spectral
metric `H2` to bounded operators on rank-four spectral `H2`.

The coefficient is the background-cometric raise of the symmetrized metric
deviation inserted directly in the leading covariant slot of the rank-four
Hessian.  Thus the highest-order coefficient depends only on the `H2` metric
deviation; no higher norm of the metric enters.

## Current status

The implementation is sorry-free and focused verification passed.  It provides
the continuous linear map `perturbH2`, its smooth-core identity, and the
dimension-three estimate

`‖perturbH2 g T‖ ≤ C ‖T‖_{H2}`.

The original passenger-extension route was wrong: it acted in rank-four slot
three, whereas the Ricci--DeTurck principal coefficient acts in slot zero.
The corrected proof uses `slotInsertEndoCc g 3`, the background
cometric-raise jet bound, and the completed `H2` coefficient action.  The
continuous-linear-map codomain needs the direct Mathlib operator-norm import;
without it only the seminormed structure is visible to this module.

Focused verification and the named producer refresh passed after this
correction.

`ricci_flow_unif_existence` remains an unproved endpoint (0%).  This file is
dedicated A2 machinery and does not by itself prove uniform short-time
existence.
