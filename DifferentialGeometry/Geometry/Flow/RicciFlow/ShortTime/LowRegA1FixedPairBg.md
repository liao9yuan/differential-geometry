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

## Current frontier: one-sided full-slope Rung-3 Gårding

The former isolated-`C2` absolute-value target is superseded.  It throws away
the sign and separates terms whose principal pieces must cancel.  The binding
route keeps the fixed-background `C0` and `C2` actions together through the
diagonal Rung-3 pairing and proves only the one-sided upper bound needed by the
energy inequality.  The first missing theorem is the homogeneous analytic
producer, tentatively `lowbase_full3_unif`:

```text
eta > 0
  -> exists delta2 R2,
     0 < delta2 < 1/3 and 0 < R2 <= 1,
     forall g in the C3 metric class, exists G >= 0,
     forall 0 <= delta <= delta2, 0 <= R <= R2, hreal, F, c,
       2 * fullSlopePair3 g gBase ...
         <= eta * H4^2 + G * H3^2.
```

The final raw/rest consumer then adds the static seed and routine lower pieces;
its `galA1RestPairBg` conclusion may use `G * (1 + E3)^2`.  The essential cap
order is
`eta -> exists delta2, R2 -> g -> exists G`: the fibre/state caps are chosen
uniformly over the metric class before `g`, while the lower-order Gårding
constant may be metricwise.  This does not alter `galA1FixPair3_le`: the
completed C1 correction correctly retains `eta -> g -> G`, followed by its
solver-supplied cap `R <= 1`.

Two lower pieces of the corrected route are already complete:

1. `finite_pair_split`, specialized to `a = 1`, `b = 2`, converts the finite
   weight-three Galerkin sum to the complementary `L2` pairing with two
   state-side and one arm-side iterates of `1 - Δ∇`.  `finite_symm_scale`
   transports the retraction scalar and slot symmetrization by exact linearity,
   with no division by `theta` and hence no
   separate `theta = 0` branch.
2. `edgePair_l2_bi`, `edgePair_inner_bi`, and `edgePair_green_bi` provide the
   polarized monomial formal-adjoint identity and exact one-derivative Green
   movement.

The exact caveat is that the complete low-base `C2` kernel in
`galA1RestVecBg` is **not definitionally `edgeTopPair`**.  `edgeTopPair` is a
closed-edge top family with the same state baked into its coefficient and
acted slots.  A genuine low-base full-slope adapter must preserve the actual
coefficient state, acted state, and test tensor and must recombine `C0+C2` at
the consumer layer.  Consequently neither a raw `oneMinus_appCc2_comm`
estimate nor the old diagonal closed-edge theorem is the binding result.

The live analytic brick is the diagonal full-slope low-base
commutator/Gårding estimate after that C0+C2 recombination.  The earlier three
failed routes remain evidence only against a standalone high-jet C2 action,
naive raw duality, and a false `lowBase C2 = edgeTopPair` identification; they
do not block the corrected route.  The canonical ShortTime home for
`lowbase_full3_unif` is the future `LowRegBgC2Pair.lean`; a later final rest
consumer may live in `LowRegA1RestPairBg.lean`.  No canonical reusable theorem
below ShortTime has yet been identified.  The rest-only theorem remains
unstated (0%); no partial theorem or stronger assumption has been added.
