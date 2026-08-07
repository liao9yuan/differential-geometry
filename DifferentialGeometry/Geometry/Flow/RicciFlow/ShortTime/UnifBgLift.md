# UnifBgLift

## Role

`BgLiftData` is the class-first scalar layer for the arbitrary-fixed-background
adjacent-scale lift.  It deliberately contains no metricwise coefficient maps
and no orbit witness.

The force margin uses
`lowregStateRad K.top K.slope K.outer K.realize / 4`, exactly the bound exported
by `IsLowSolveBg.force_bound`.  It does not use `K.realize / 4`.

The coefficient radius lies between the realized state radius and
`K.realize`, so the low-bound realization certificate applies throughout the
whole coefficient-validity ball.

The file also defines the positive common low/lift horizon, exports its two
projection inequalities to the low-solve and lift horizons, and connects an
`IsLowSolveBg` force estimate to the stored `forceCap`.

## Verification

Focused verification passed.

## Remaining frontier

The metricwise coefficient certificate and realized-orbit package remain
separate.  Their honest construction still needs the arbitrary-background high
A1 pair and a class-first A2 contraction packet.
