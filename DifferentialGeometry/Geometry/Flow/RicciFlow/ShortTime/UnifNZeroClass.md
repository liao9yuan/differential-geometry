# UnifNZeroClass.lean

## Purpose

This module exposes the already-proved class-uniform static Ricci--DeTurck
one-jet bound as an explicit `zeroBd` data/proof package for the common-time
interface.  The cap is chosen before the class metric varies.

## Route

- `unifKsupLeOne` chooses one nonnegative static-field one-jet cap before every
  order-three class metric.
- `nZero_unif` converts that cap to the closed scalar `nZeroC` bound on the
  zero-state nonlinearity.
- `exists_lowZero` packages the resulting cap as `IsLowZeroUnif`.
- `lowZero_nfun` presents the bound in the exact `IsLowBoundsAt.hzero` shape.

The smooth-core continuity hypothesis remains explicit because it is produced
together with the future joint tame packet.  No new frontier assumption is
introduced here.

## Boundary

This closes only the zero-state scalar cap.  The top second-order remainder arm
and the two lower arms still lack a class-first joint tame producer.

## Verification

Focused verification passes without local warnings, and the exact targeted
refresh is current.  The narrow package census reports only `propext`,
`Classical.choice`, and `Quot.sound` for `lowZero_unif_of`, `exists_lowZero`,
and `lowZero_nfun`.
