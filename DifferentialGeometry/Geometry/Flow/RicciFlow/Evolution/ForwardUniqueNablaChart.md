# `ForwardUniqueNablaChart.lean`

## Role

This is the first derivative-layer brick for the final forward-uniqueness lane.  It
provides the off-centre chart-frame identity needed to feed the half-open
`partRicciWithinM` tower into a joint-regularity proof for `metricNabla0S g Ric`.

`nablaRicChartComp` itself is complete (100%).  It is the first of the four recorded
derivative-layer continuation steps, so that local continuation is about 25% complete.
The target theorem `ricci_flow_forward_unique` remains unproved (0%), while its dedicated
machinery remains about 90% complete.  The whole HCG compactness program remains about
10%.

## Route

The proof specializes `nabla0SFun_eval_coordFrame_moving_raw` directly to the
chart-`α` frame at an off-centre good-set point.  The leading slot is represented by
the existing global smooth chart-basis extension.  Smoothness of the moving-slot
pairing comes from `tensor0SField_eval_cmdAt_slots`; its chart-coordinate germ is
then identified through the off-centre Ricci component identity.  Finally,
`LeviCivita_chartBasisVec_alpha_basis_apply` supplies the two Christoffel corrections.
The conditional `ModelDerivEqCoordDeriv0SAt` route is deliberately not used.

The existing `nablaRicReal_frame` theorem in `Evolution/StarSum/TimeRecursion.lean`
and `coordNablaRealOn` in `Evolution/Ricci/CoordinateRegularity.lean` already supply
the later frame realizations used by `hNR`; this file does not duplicate those results.
The earlier forward-uniqueness audit missed those producers.

## Verification

Focused verification passed without warnings or `sorry`.  The hygiene scan found no
new axioms, instances, notation, opaque declarations, macros, elaborators, or syntax.
