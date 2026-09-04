# RawFramedLocalDiffeo

## Native plumbing

`framedExp_mdiffAt` transports raw exponential smoothness through the fixed
normal-frame continuous linear equivalence.  `mfderiv_framedMap` records the
corresponding derivative chain rule.  `framedExp_locdiff` packages the remaining
formal implication from pointwise raw-domain membership and injectivity of the
framed exponential derivative to a smooth local diffeomorphism on an open set.

The set-level adapter uses only finite-dimensional injective-implies-surjective
linear algebra, `Coordinates.written_fderiv_inv`, and the canonical coordinate
inverse-function theorem.  It deliberately carries no curvature,
no-conjugacy, completeness, or radius assumptions.

## Verification

Focused verification passes without warnings, including the derivative chain
rule, after the explicitly named
`Coordinates.LocalDiffeoIFT` artifact refresh.  The earlier failure was only a
stale-import error for `Coordinates.written_fderiv_inv`; there is no remaining
local proof error.  The first formulation also exposed a missing model-space
chart for a tangent-space-valued `normalFrame`; using its explicit
continuous-linear-map representative is the checked native repair.
