# LowRegGaugeRemoval

## Role

This file is the gauge-removal consumer for the uniform low-regularity
Ricci--DeTurck route.  It starts only after the fixed-point solution has been
realized as a smooth metric family satisfying the project-native strong
DeTurck equation and `JointChartGramSmooth`.

## Result

`ricci_gauge_of_dt` constructs the full-horizon flow of the negative DeTurck
vector field, packages it as a diffeomorphism family, and pulls the realized
DeTurck metric back to a Ricci-flow family.  It returns the gauge equation,
the pullback identity, the initial metric, joint chart-Gram smoothness and
continuity on the half-open slab, and the Ricci-flow equation including the
left endpoint.

The background metric is allowed to differ from the initial metric.  This is
essential for the uniform bounded-geometry family, where the DeTurck
background is fixed while the initial metric varies.

## Project status

The endpoint `ricci_flow_unif_existence` remains unproved (0%).  This theorem
does not construct or smooth the low-regularity fixed point; it discharges the
downstream gauge-removal assembly once a realized strong DeTurck solution and
joint chart-Gram regularity are available.  Dedicated gauge-removal machinery
for that final stage is now 100% as stated; the separate smooth
realization/bootstrap producer remains 0% until stated and proved.  The
existing plan's estimate for all dedicated uniform-existence machinery remains
approximately 88--90%; this consumer alone does not justify raising it.

Focused Lean verification passed without local warnings.  The static
forbidden-token scan was clear.
