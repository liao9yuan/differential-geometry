# SegmentCost

## Role

This module compares the finite-action same-clock segment value with the
existing global `C1` regularized cost without conflating the two curve classes.

## Native route

`lSegValue_le_reg` uses `lRegLag_int_c1` to make every global `C1` competitor
integrable, `lSegCurve_sqrt` to place its square-root reparameterization in the
raw segment class, and `lSegValue_le_c1` to compare actions.  A scalar lower
bound on the exact squared time slab gives a common lower bound for the real
`C1` action set, so `WithTop.coe_sInf'` and `le_csInf` pass from pointwise
competitor bounds to the infimum.

The source theorem makes no compactness or minimizer-attainment assumption.  A
single global `C1` endpoint curve is supplied only to witness nonemptiness of
the regular competitor class.

## Downstream closure

The reverse inequality and equality endpoint are now proved in
`SegmentDensity.lean`. Its `lSegChartH1_fin` theorem supplies the finite-chart
`timeH1` realization without exposing chart/H1 data in the final statement,
and `lSegValue_eq_reg` proves the exact equality with the global `C1`
regularized infimum.

## Verification

`lSegValue_le_reg` is warning-free focused GREEN.  Its exact named refresh and
downstream axiom audit are intentionally deferred until a real consumer imports
the new declaration.
