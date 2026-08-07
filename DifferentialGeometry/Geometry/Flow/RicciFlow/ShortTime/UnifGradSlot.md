# UnifGradSlot

## Class-first producer

`gradSlot_grid_unif` fixes one nonnegative order-zero/order-one pointwise grid
before the class metric varies.  In dimension three its two entries are the
finite Parseval caps `3^6 * (2*C0)^2` and `3^7 * (2*C1)^2`.

Here `C0` comes from `unifCurvSup_of`, while `C1` comes from
`unifRmOpOne_of`.  Their fixed-background inputs are chosen before the class
metric, and the variable metric consumes only uniform equivalence and metric
jets through order three.

This is the fixed-curvature pointwise producer needed before assembling the
class-first `H1` curvature coefficient packet.  It does not itself prove the
final Ricci order-zero arm or `lowreg_bounds_unif`.

## Verification

Focused verification passed without warnings.  The axiom audit contains only
the standard `propext`, `Classical.choice`, and `Quot.sound`.
