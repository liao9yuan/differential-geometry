# ShiBallCalabi

## Status

`exists_ballCalabi` is source-written. It is the fixed-time bridge from an
Rm-controlled flow metric ball to a Calabi distance upper support on the inner
half-radius ball. The selected comparison tail is shortened so its whole
Jacobi interval remains in the controlled outer ball.

The coefficient is `q = finrank E / radius`. When the transverse dimension is
positive, this dominates the pointwise Ricci loss obtained from
`ricci_ge_of_rm`; the zero-transverse-dimension branch needs no Ricci input.

Focused verification is warning-free GREEN.

`exists_ballFlow` is also warning-free focused GREEN. It uses the same
shortened tail, `ricci_abs_of_rm` on the outer ball, and the generic
`DistanceBarrierCore.scaled_of_tail` theorem to produce an actual
time-dependent `ScaledDistSupport`. The transverse comparison coefficient is
chosen exactly so the spatial Calabi term agrees with the established
parabolic support constant. The one-dimensional branch still needs no Ricci
lower input.

## Next theorem

Compose `exists_ballFlow` with the native cutoff profile to produce
`ShiCutoffLowerSupportAt` with error of order `radius⁻²`, then apply the finite
compact-support maximum-principle estimate for the `m = 1` Bernstein quantity.
