# LowRegLieOne

## Role

This module is the dimension-three, `C3`-compatible producer for the concrete
order-one DeTurck Lie coefficient.  Its class-first public endpoint is
`lie1_h2_unif`; the older metricwise endpoints `lie1_h2_tame` and `lie1_h2`
remain available as compatibility interfaces.  The uniform theorem fixes the
background, class parameter, and coefficient functions before the class metric
varies, and uses only class metric jets through order three.

## Mathematical route

- `sharpFlatEndoCc` is split into the inverse-metric difference insertion and
  a fixed parallel-background insertion.  The moving part is integrated with
  the low `H2` jet grid, so this factor uses no third derivative.
- `lieArm1LoweredBgKappa` is identified with `-lc0Kappa`.  The exact
  `kappa_bg` split is applied before estimating: the self-background term is
  controlled by `kappaSelf_h2`, the fixed term is harmless, and `pbLow_h2`
  uses only the lower radius.  Hence the endpoint `H3` size occurs affinely.
- `lieArm1PsiB` is estimated by the dimension-three `H2 x H2 -> H2`
  application estimate.
- The canonical fourteen-piece decomposition of `deTurckLieArm1Coeff` is
  assembled without changing its cancellations or introducing an order-four
  metric jet.
- `lieFix_h2_unif`, `pbLow_h2_unif`, `psi_h2_unif`, and `piece_h2_unif`
  replace every metric-local compactness coefficient in that decomposition by
  a class-first coefficient.  The orientation identity `fix_eq_neg` connects
  the fixed Lie tensor to the public fixed-background connection producer.
- `kappaBg_h1_unif` reuses the same class-first fixed-connection and low
  product bounds to control the full background connection-difference tensor
  in `H1`.  This is the dimension-three coefficient needed by the uniform
  `AMix` leaf.

## Current verification state

The 1893-line source remains below the hand-maintained-file limit and contains
no `sorry`, `admit`, or new axiom.  The previously established
`lie1_h2_unif` check and export remain green.  The newly added
`kappaBg_h1_unif` now also passes a warning-free focused check, has a fresh
exact module export, and audits to only `propext`, `Classical.choice`, and
`Quot.sound`.

For the Route-(c) Rung-3 correction redesign, the already proved helpers
`lieFix_h2_unif`, `pbLow_h2_unif`, and `piece_h2_unif` are now public with
docstrings.  Their proof bodies are unchanged, and the source passes focused
verification after the visibility change.

Progress accounting: `lie1_h2_unif` itself is proved and verified (100%); the
joint class-first RHS tame producer that consumes it is still unstated (0%);
`lowreg_bounds_unif` and `ricci_flow_unif_existence` remain unproved (0% each).
The dedicated uniform-existence supporting machinery is about 99%, while the
whole HCG project remains about 3%.

## Next check

Verify the `amix_h1_unif` consumer of `kappaBg_h1_unif`, then combine the five
closed order-zero leaves into the class-first tail producer.  Do not reopen the
fixed-connection orientation or the fourteen-piece Lie assembly unless a
downstream interface exposes a genuinely different target.
