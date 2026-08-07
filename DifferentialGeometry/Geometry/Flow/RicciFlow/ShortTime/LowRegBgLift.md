# LowRegBgLift

## Role

This file is the metricwise certificate layer between class-first scalar data
and orbit realization.

- `BgLiftOps` contains only the completed high/low A1 maps.
- `IsBgLiftAt` proves continuity, common bounds, exact actual-core identities,
  and both Sobolev inclusion squares.
- A2 uses the canonical `lowA2HiBg` and `lowA2LoBg` maps.
- The realization witness at the coefficient radius is derived from
  `IsLowBoundsAt` and `BgLiftData.coeffRadius_le_realize`; it is not an extra
  assumption.

The certificate intentionally does not contain an orbit or temporary
measurability witnesses.

## Verification

Focused verification passed.

## Remaining frontier

An existence theorem for `BgLiftOps` and `IsBgLiftAt` is still required.  In
particular, the arbitrary-background high A1 pair and the class-first high A2
bound remain analytic producer obligations.
