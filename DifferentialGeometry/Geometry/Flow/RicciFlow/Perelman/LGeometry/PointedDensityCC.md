# PointedDensityCC

## Role

This module closes the finite preferred-chart assembly from the checked
weighted source theorem to compactly supported real tests on one fixed limit
space. It uses raw transported `Measure`s and does not assert global finiteness,
tightness, total-mass convergence, or no-mass-loss.

## Route

- `redDensitySrcMeas` is the inverse pointed-map transport of the source
  Riemannian volume with reduced density, restricted to the partial-map target.
- `redDensityTermMeas` names the corresponding terminal reduced-density
  measure before transport.  `redSrc_tail_le` applies the generic inverse-map
  tail theorem to turn target-set capture into a fixed-limit compact-complement
  bound without assuming global finiteness.
- `redDensityLimVol`, `redDensityLimDens`, and `redDensityLimMeas` keep the limit
  volume, density, and weighted measure instance-stable.
- `ccChartSet` extracts the finite preferred-chart set meeting the compact test
  support. `ccCarrier`, `ccChartImage`, `ccPosWeight`, and `ccNegWeight` are the
  canonical local data.
- The finite POU identity, compact-source exhaustion, bump-one property, and
  pointed-map/chart covariance derive both raw nonnegative measure splits.
- `redDensity_src_wgt` supplies convergence for each positive and negative
  chart term. Finite limit terms imply eventual source finiteness; the signed
  integral follows by subtracting the two finite lower-integral sums.

The generic lower-layer theorem `lint_map_fin_loc` supplies the inverse-map
formula, finite nonnegative sum, and support localization. The private
`redDensity_cc_aux` remains only the finite signed convergence engine; the
public theorem derives its split equalities rather than exposing them.

## Assumption boundary

The public `redDensity_cc_lim` has no conclusion-shaped split or convergence
hypothesis. It takes the existing local weighted-source inputs on the canonical
chart images, plus local AEMeasurability of the source and limit reduced
densities on the canonical compact carriers.

The local density-measurability hypotheses are currently necessary because the
available `redDensity_meas` producer carries a compact-manifold section
assumption, while the pointed approximating and limit manifolds here need not
be compact. No global `FiniteMeasure` or mass assumption was introduced.

## Verification

`PointedDensityCC.lean` is warning-free focused GREEN and exact-refresh GREEN.
A direct axiom audit of `redDensity_cc_lim` reports only `propext`,
`Classical.choice`, and `Quot.sound`.  The L-geometry umbrella and the expanded
89-item P2 audit are also focused GREEN.

`redDensityTermMeas` and `redSrc_tail_le` are warning-free focused and exact-
refresh GREEN.  The expanded 97-declaration P2 audit is focused GREEN, with
only `propext`, `Classical.choice`, and `Quot.sound`.  A
direct application through the internally stored infinite-grade pointed map
exposed a Borel-instance diamond between `L.M` and `(L.atTime 0).M`; merely
reordering those instances did not remove it.  Rebuilding the same
`PartialEquiv` as the standard local grade-one partial diffeomorphism in the
final Borel environment removed the diamond without changing its function,
source, target, or public assumptions.

## Progress

- `redDensity_cc_lim`: stated and proved, theorem endpoint 100%.
- Dedicated fixed-space compact-test machinery: 100% for this endpoint.
- Fixed-space reverse-tail transport: 100% stated, proved, and warning-free
  focused-check verified.
- Broader no-mass-loss theorem: not stated or proved, 0%; it remains a separate
  tightness/global-mass frontier.
- Whole P0--P9 program: unchanged at roughly 15--25%; this closes one P2b
  compact-test producer and does not complete the P3 asymptotic-shrinker chain.
