# ProjDerivative

## Layer split

The tangent-chart and fixed-chart vector-field projection lemmas were moved
unchanged to the acyclic `GlobalVectorField` foundation.  This file keeps the
original import path and the higher chart-flow theorem
`IsMIntegralCurveAt.mfderiv_proj_one`.

This is an ownership move, not a new API: declaration names and statements are
unchanged and downstream users may continue importing `ProjDerivative`.

## Verification

Focused verification passed without warnings after refreshing the lower
dependencies.  The explicit named refresh also passed.
