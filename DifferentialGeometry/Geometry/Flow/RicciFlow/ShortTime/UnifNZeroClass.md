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
together with the future tame/A2/affine packet.  No new frontier assumption is
introduced here.

## Boundary

This closes only the zero-state scalar cap.  The top/A2 radius and the lower
affine coefficients still lack class-first supplied-constant producers.

## Verification

Pending focused verification after the current single-process dependency
refresh finishes.
