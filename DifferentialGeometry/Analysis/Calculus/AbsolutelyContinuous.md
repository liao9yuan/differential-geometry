# AbsolutelyContinuous

## Role

This module supplies the generic adjacent-interval pasting theorem for
metric-valued absolutely continuous curves.  It is the lowest-layer producer
needed before the same-clock Perelman segment-value API can use a curve class
closed under exact concatenation.

## Route

`piecewise_Iic` uses the epsilon-delta characterization.  Each disjoint source
interval is clipped at the common endpoint into a left and a right interval.
Clipping preserves pairwise disjointness and does not increase total interval
length.  The two absolute-continuity estimates are then combined with the
triangle inequality and equality of the two curves at the common endpoint.

No matching theorem was found in the current `DifferentialGeometry` tree or
Mathlib; Mathlib's existing `AbsolutelyContinuousOnInterval.mono` supplies only
restriction to a smaller interval.

## Verification

Focused verification passed without warnings.

## Upper-Dini integration

`sub_le_integral_dini` is the whole-interval absolutely continuous form of
the finite upper-right-Dini inequality.  At almost every differentiability
point, the Dini slope bound controls `deriv`; Mathlib's absolutely continuous
FTC and interval-integral monotonicity then give the endpoint inequality.

`sub_le_int_loc_dini` is the book12 form used near a singular initial time:
the function is continuous on the closed interval and absolutely continuous on
every terminal subinterval away from the left endpoint.  It applies the first
theorem on each such subinterval and closes at the endpoint by continuity of
the function and of the primitive of the integrable majorant.

These are generic analysis producers.  They do not establish the separate
geometric fact that a moving Ricci-flow distance is locally absolutely
continuous.  Focused verification of both new declarations passed without
warnings.  A direct audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Lipschitz composition and square root

`comp_lipschitzOn` proves that postcomposition by a map Lipschitz on the
curve's image preserves interval absolute continuity.  The proof works
directly from the epsilon-delta definition and therefore applies to arbitrary
pseudo-metric codomains.  `congr_of_eqOn` supplies the accompanying interval
congruence rule.

`Real.sqrt_ac_sq` realizes square root as the integral of the integrable
power `t ^ (-1/2)` plus the left-endpoint constant.  It gives absolute
continuity on `[a^2,b^2]` under exactly `0 ≤ a ≤ b`, including the singular
case `a = 0`.  All three declarations are warning-free focused green.  They
complete the generic analysis part of `lSegCurve_sqrt`; the remaining piece is
the fixed-Riemannian-metric Lipschitz estimate for a global `C¹` manifold
curve.

## Monotone time precomposition

`comp_mono_lip` proves that precomposition by a real map which is monotone and
Lipschitz on the source interval preserves interval absolute continuity.  Its
epsilon-delta proof sends each finite disjoint interval through the monotone
map, proves the images remain pairwise disjoint using endpoint order, and uses
the Lipschitz constant to control their total length.

`comp_sq` specializes this bridge to `s ↦ s ^ 2` on a nonnegative compact
interval.  The square map is monotone there, and its compact-interval
Lipschitz bound comes from its smoothness.  This is the raw-time bridge needed
to pass an absolutely continuous L-segment curve on `[a²,b²]` to its
square-time reparametrization on `[a,b]`.

Focused verification of both declarations passed without warnings.
