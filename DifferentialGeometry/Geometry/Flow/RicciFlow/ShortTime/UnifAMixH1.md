# UnifAMixH1

## Role

This module supplies the dimension-three class-first affine `H1` estimate for
the genuine mixed-connection order-zero correction `lc0AMix`.  It is one of the
five leaves consumed by the cancellation-preserving order-zero tail assembly.

## Mathematical route

- `kappaBg_h1_unif` bounds the fixed-background connection factor using only
  the perturbation's low `H2` radius and class metric jets through order three.
- `kappaSelf_h2` carries the unique third derivative of the perturbation.  The
  separate top norm is combined with the low radius as `R + A`.
- The four moving traces and the mixed applications reuse the existing
  dimension-three class-first product packages.
- The final exact `amix_refold_rf` identity preserves the established
  cancellation-compatible tensor form.

## Current verification state

`amix_h1_unif` passes a warning-free focused Lean check and has a fresh exact
module export.  Its axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`; the theorem is therefore verified.

Progress accounting: this theorem is proved and verified (100%); the five-leaf uniform tail producer remains
unstated (0%); `lowreg_bounds_unif` and `ricci_flow_unif_existence` remain
unproved (0% each).  The broader dedicated uniform-existence infrastructure is
about 99%, and the whole HCG project remains about 3%.

## Next check

Verify the fixed-curvature `Riem` passenger/refold, then assemble this leaf
with the other four class-first order-zero leaves.
