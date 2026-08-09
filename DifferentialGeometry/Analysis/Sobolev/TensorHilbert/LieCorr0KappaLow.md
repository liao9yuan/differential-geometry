# LieCorr0KappaLow

## Role

This small public leaf replaces the lowered connection-difference portion of
the unfinished `LieCorr0LowJet` module for the low-regularity Ricci--DeTurck
route.

## Current state

The canonical `lc0Kappa` wrapper reuses the checked
`metricConnDiffLoweredCc` object rather than defining a duplicate section.
The fibre evaluation theorem is stated here. The public `pbLow_sub` identity
records exact subtraction in the perturbation slot; it is the algebraic input
needed to turn a two-state fixed-background passenger into one passenger acting
on the state difference. Focused verification passes.

The remaining arbitrary-background C1 work is analytic rather than algebraic:
prove an H2 pair bound for the background correction of `lieArm1PsiB`, then
assemble the three surviving Lie-arm background pieces. No Ricci term remains
in that correction.
