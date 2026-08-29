# SmoothNLC

## Role

This module is the final compact ordinary-smooth-flow L-geometry producer for
the canonical `Perelman.NoLocalCollapsing` predicate.  It is deliberately
separate from both the entropy/W producer and the later surgery-spacetime
noncollapsing theorem.

The elementary measurable-set lower bound now lives canonically in
`RedVolumeSetLow.lean`; moving it there breaks the former dependency cycle
through `SliceVolumeLow` and `LateVolumeLow`.

## Public endpoint

`smooth_nlc` strengthens the consumer shape of `no_local_open`: a compact,
connected, boundaryless smooth finite-dimensional solution on `[0, omega)`
and a positive scale `rho` produce `NoLocalCollapsing S rho`.  The former
three-dimensional equality is unnecessary because every producer in the
reduced-volume proof is dimension-generic.  No ambient `PseudoMetricSpace`
assumption is added to the public theorem.  A compatible metric is installed
locally from manifold metrizability for the internal L-geometry producers.

## Proof route

The proof is entirely native to the reduced-volume route:

1. `family_vol_low` supplies the initial-time ball-volume constant directly,
   without importing the W-route `EarlyTime` module.
2. If its time threshold is `tauE`, the late branch uses
   `a0 = tauE / 4` and `a = tauE / 2` in `redVolume_late_low`.
3. `redVolume_le_one` makes the resulting positive floor `v0` finite; the
   Gaussian tail is fixed as `eta = v0 / 2`.
4. `redVolume_ball_unif` supplies a threshold `eps0`; the proof fixes
   `eps = min eps0 (1/2)` before the terminal ball.
5. The exact identity

   ```text
   c(eps, r) * r^n =
     exp(n^2*eps - (n/2)*log eps - (n/2)*log(4*pi))
   ```

   removes the radius from the reduced-volume upper coefficient.  ENNReal
   subtraction and division then give a positive late-time kappa.
6. The minimum of the early and late constants proves
   `KappaNoncollapsedBelowScale`, hence `NoLocalCollapsing`.

The controlled-ball carrier condition supplies both `r^2 <= t` and the open
regularity window needed by `redVolume_ball_unif`; no extra consumer
regularity assumption is introduced.

## Verification and accounting

`smooth_nlc` is warning-free focused green, with no `sorry`, `admit`, wrapper
hypothesis, or new axiom.  The theorem itself is now **100%**, and its dedicated
compact ordinary-flow reduced-volume-to-noncollapse assembly is **100%**.
Reused L-geometry, small-ball volume, measure, and ENNReal infrastructure are
tracked separately.  Complete bounded-curvature L8 and surgery/eventwise
noncollapsing remain distinct later project phases; this theorem does not claim
their completion.
