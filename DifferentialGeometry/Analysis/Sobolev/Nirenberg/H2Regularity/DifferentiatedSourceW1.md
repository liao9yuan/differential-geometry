# DifferentiatedSourceW1

## Target

Prove that the canonical scalar source `homDiffSource B u Omega l` belongs to
`W^{1,2}(Omega)` whenever `u` belongs to `W^{3,2}(Omega)`, the coefficient field
`B` is globally smooth, and `Omega` has compact closure.

## Route

- The all-order proof now lives in `DifferentiatedSourceK.lean` as
  `homDiff_memWkp`.
- This file keeps the established public name `homDiff_memW1` as the thin
  specialization `m = 1`; it introduces no duplicate proof route.

## Verification

The thin specialization passed focused verification and its explicit named
export refresh without reported warnings.

## Failed routes

No mathematical route failed. Importing the tensor-regularity bootstrap merely
to reuse its finite-sum helper was rejected as an unnecessarily high and heavy
dependency; the local finite-sum proof uses the canonical `MemWkp.add` API.

## Progress estimate

- `homDiff_memW1`: 100% as a checked compatibility specialization with a
  refreshed export.
- The fixed `W^3 -> W^1` mathematical route remains settled; the generalized
  producer subsumes it.
- The subsequent `W^4` smoke-test endpoint remains unstated/unproved, 0%; this
  file supplies only its source-regularity producer.
- The all-order P1c bootstrap and Cheeger--Gromoll splitting endpoint remain
  unstated/unproved, 0%.
