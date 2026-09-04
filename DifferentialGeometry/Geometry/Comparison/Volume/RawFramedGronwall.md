# RawFramedGronwall

## Purpose

This module keeps the inner-product normal-frame specialization separate from
the generic normed-space raw Jacobi/Gronwall producer.  The separation avoids
an incompatible normed-space instance diamond while preserving the weakest
signature of `rawExp_mfderiv_inj`.

## Route

- `framed_mfderiv_inj` composes `rawExp_mfderiv_inj` with the injective
  `normalFrame` continuous linear equivalence and the checked
  `mfderiv_framedMap` chain rule.
- `framed_locdiff_rm` supplies those pointwise injectivity results to the
  existing `framedExp_locdiff` inverse-function-theorem adapter on an open set.

No new curvature estimate, normal-map abstraction, or local-diffeomorphism
definition is introduced.

## Verification

Warning-free focused verification passed for both public theorems.  The first
inline placement inside the generic raw module failed only because combining
the generic `NormedSpace` and normal-frame `InnerProductSpace` sections
produced a finite-dimensional instance mismatch; splitting at the abstraction
boundary removed that instance diamond.  The first check of the split file
then stopped before elaboration on the expected missing upstream artifact;
after the exact downstream-required `RawRadialGronwall` refresh, the file
checked cleanly.

## Accounting

These are dedicated P1b machinery, not the exact incomplete-ambient E1/E2
consumer statements.  E1 and E2 remain 0%; aggregate P1 remains eleven of
fourteen endpoints (78.6%), and the whole Poincare theorem endpoint remains
0%.
