# LowRegA1FixedPairBg

## Role

This module owns the complete order-one Galerkin correction produced by
replacing the self DeTurck background with one fixed background, and its direct
Rung-3 signed energy pairing.

## Current state

`galA1FixVecBg` and `galA1FixPairBg` are complete public definitions.  Both
carry the realization hypothesis explicitly, so the retracted state and zero
endpoint use the canonical `galRepFib` and `lowregFibZero` certificates.

`galA1FixPair3_le` is proved and focused-check green.  Its quantifiers have the
required class-first order `eta -> g -> G`, followed by the capped Galerkin
radius, fibre parameter, realization data, mode set, and coefficients.  The
proof applies `lowC1Corr_unif` at radius one, uses the H2-by-H3 first-order
action estimate, bounds the finite output mass by its spectral norm, and
applies the signed cross-scale Young theorem.  It introduces no fourth
varying-metric jet and is uniform in the Galerkin dimension.

The forcing-level algebra is also focused-check green.  `galA1RestVecBg`
retains the fixed-background `C2` and `C0` actions and substitutes only the
self-background `C1` coefficient.  `galArmVecBg_split` then isolates the exact
complete C1 correction, while `galA1RestPairBg` and `galArmPair3_split` lift
that identity to the signed Rung-3 weighted pairing.  In particular, the split
does not incorrectly identify the full fixed-background arm difference with
the C1 correction.

The theorem `galA1FixPair3_le` and the signed C1 split are complete (100%).
The rest-only Rung-3 theorem is not stated (0%), and the headline
`ricci_flow_unif_existence` theorem remains unproved (0%).  Dedicated
fixed-background direct-smoothing machinery is approximately 92%, the
verified conditional metricwise adapted-to-mass-to-packet chain remains 100%,
and the whole HCG project remains approximately 3%.

## Current stop: signed C2 Rung-3 pairing

The `C0`, self-background `C1`, and static-seed pieces of
`galA1RestPairBg` are routine with `c0JetTowerQBg`, `c1JetTowerQ`,
`appCc_h2_h2_h2`, `appCc_h2_h3_h2`, `galRepHs_le g 3`, Young's inequality,
and `lowRegSeedMass`.  The only unresolved analytic piece is the fixed-background
`C2` action.  The smallest missing consumer has the class-first order
`eta -> g -> G`, followed by the capped `H2` state radius, and must prove the
signed estimate

```text
2 * |sum i in F, weight i 3 * c i *
      (smoothCcToTensorHs g 1 (AB.a2 T)).coeff i|
  <= eta * E4 + G * (1 + E3)^2
```

(The sharper `G * E3` lower term may suffice for the isolated `C2` action.)
It may use only the `C3` metric class and the solver's capped `H2` state
radius; it must not depend on `galRepJet_le g 4`, `fixCdAtgw 3`, or an `H4/H5`
state radius.

Three genuinely different routes were checked and did not close:

1. `top_path_dev_unif` gives class-first `H2`-smallness of `C2`, but the
   available `appCc_h2_h4_h2`/`appD2Hs_norm` action route is metricwise and
   requires the forbidden high state jet.
2. `top_path_h1_unif` with `appCc_h23_unif` gives an `H3 -> H1` action bound,
   one derivative short of the raw weight-three pairing; the naive spectral
   duality repair requires `H5`.
3. `EdgeRefoldPairing.edgeTop_green` exists, but its same-name note records the
   missing structural bound for `covDivergence edgeTopPartner`; there is no
   usable energy consumer.

This is a missing structural spectral/Garding API, not a local elaboration
problem.  A future consumer may live in `LowRegA1RestPairBg.lean`, while the
structural pairing theorem belongs in the lower DeTurck layer.  No partial rest
theorem or new assumption was added at this stop.
