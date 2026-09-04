# ChartIdentification

## Lowered tangent-chart facts

The generic formulas `extChartAt_tangent_apply_snd` and
`extChartAt_tangent_apply_fst` now live in
`Geodesic.GlobalVectorField`, below the maximal-geodesic layer.  This module
imports that foundation and continues to expose the same declarations
transitively; all chart-flow identification statements and public signatures
remain unchanged.

## Verification

Focused verification passed without warnings.  The explicit named refresh
also passed.
