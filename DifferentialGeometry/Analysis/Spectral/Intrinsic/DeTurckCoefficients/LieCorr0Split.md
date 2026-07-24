# LieCorr0Split

## Proved design encoded in the source

The zeroth-order DeTurck correction is packaged as four public smooth fields:
the insertion, vector--bilinear, mixed connection-difference, and fixed
curvature pieces.  The intended public equalities are:

- `lc0_decomp`, the exact four-piece realization of `lieCorr0Field`;
- `nEndo_base`, identifying the base insertion endomorphism with the negative
  DeTurck `W` endomorphism;
- `insert_base`, cancelling the base-background endomorphism arm and leaving
  a difference of insertion fields;
- `tail_base_split`, the resulting cancellation-preserving normal form.

This is the mathematically essential split: estimating `lieCorr0` and the
base `DLb` arm separately would reintroduce a highest-derivative term that is
not small at `H3` regularity.

## Verification

The source is written but not yet focused-checked because the shared build is
under an exclusive sequential artifact refresh.  Thus these are not yet
counted as verified Lean theorems.

Endpoint theorem progress remains 0%; this file is producer machinery only.
