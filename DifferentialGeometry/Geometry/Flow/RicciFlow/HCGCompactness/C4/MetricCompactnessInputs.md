# MetricCompactnessInputs notes

## 2026-07-08

Added `MetricCompactnessInputs.ofUniformVolume`, a small constructor that
keeps the public conditional endpoint bundle in the existing
`VolumeComparisonInput` consumer shape while accepting the more explicit
`UniformBallPack` producer data from `VolumeComparisonBridge.lean`.

This is infrastructure, not a theorem discharge. The conditional Theorem 3.9
endpoint `metricCompactness` is still 0% proved because its Steps A-D assembly
is still the `sorry`. The volume-comparison theorem from the original sequence
hypotheses is also 0% proved: no Bishop-Gromov or equivalent uniform-volume
producer from `SeqBoundedGeometry` has been formalized. Its dedicated
local-volume/packing machinery is now about 75%: the generic packing
cardinality gate is checked, the explicit uniform input is checked, and this
bundle constructor is checked.

Verification passed. The existing `metricCompactness` endpoint `sorry` remains
unchanged.

Next target: either formalize the real Bishop-Gromov producer that supplies
`UniformBallPack`, or keep `UniformBallPack` as the explicit book-external
volume-comparison input and continue with the Ch4 Steps B/C/D assembly.

## 2026-07-08 joint-cap correction

Updated the bundle compatibility field from the old `lambda[0] <= r0` shape to
`stepA_cap_le`: the maximum of the Step A ratios `4` and
`50 * exp(C * 20 * lambda[0])`, multiplied by `lambda[0]`, is bounded by the
producer cap.  This is exactly what the two Step A `ballMult` consumers need
after `VolumeComparisonInput` was corrected to the joint cap `m * r <= r0`.

`ofUniformVolume` now asks for this stronger cap compatibility.  Verification
passed through the targeted `MetricCompactnessInputs` module.  The endpoint
`metricCompactness` `sorry` remains unchanged.

Added checked projection lemmas `cap_four`, `cap_four_of_nonneg`, and
`cap_inter` from `stepA_cap_le`.  These are the concrete Step A caps consumed
by `net_multiplicity` at the base scale or a smaller nonnegative radius, and
by `NetLimitData.inter_count` at the item-5 ratio scale.  Verification passed
for the focused file check and the targeted `MetricCompactnessInputs` module;
the endpoint `metricCompactness` `sorry` remains unchanged.

Added checked bundle-level Step A adapters: `net_mult`, `inter_count`,
`exists_net_data`, `exists_stable_net`, and `exists_stepA_net`.  These route
the existing Step A net and multiplicity theorems through a single
`MetricCompactnessInputs` value, so the later D6 assembly can obtain the
stable `NetLimitData` plus the item-5 intersection count without rethreading
`decay`, `pack`, `volume`, `dist_eq`, and the cap projections by hand.
Verification passed for the focused file check and the targeted
`MetricCompactnessInputs` module; the endpoint `metricCompactness` `sorry`
remains unchanged.

Added checked D6-facing wrappers `subseq`, `properMetrics`, and `stepA_net`.
The bundle now reindexes all Step A and Step B honest inputs along a
subsequence, produces the per-member `ProperMetricOn` family from the
endpoint's `SeqMetricComplete` and connectedness hypotheses, and obtains the
Step A net package directly from endpoint hypotheses.  Verification passed
after refreshing the new Step B `.subseq` exports; the endpoint
`metricCompactness` `sorry` remains unchanged.

Refreshed the remaining endpoint hypothesis reindexing API:
`SeqMetricComplete.subseq` and `SeqBoundedGeometry.subseq` are now checked and
built in their native files.  D6 can use these wrappers after composing Step
A/D subsequences instead of manually reindexing completeness and curvature
derivative bounds.  The next concrete D6 input-threading target is a composed
subsequence adapter that combines the existing `MetricCompactnessInputs.subseq`
with these endpoint wrappers and the already checked `BaseInjBound.subseq`.

Added checked `stepA_net_subseq`, which applies the bundled Step A net package
after reindexing by a subsequence and reuses `SeqMetricComplete.subseq` for the
proper metric realization.  This completes the local D6 input-threading adapter
for Step A nets after diagonal subsequences.  A first product-shaped helper for
bundling `SeqMetricComplete`, `SeqBoundedGeometry`, and `BaseInjBound` failed
because ordinary `Prod` is the wrong wrapper for these `Prop` hypotheses; it
was removed in favor of the direct consumer theorem.

Verification passed.  The endpoint `metricCompactness` `sorry` remains
unchanged.

## 2026-07-10 uniform branch-radius audit

The bundled `normalBounds` field does not currently entail the uniform radius
used in older D6 plan prose.  Its constants are uniform, but
`NormalCoordMetricBoundInput.radius` has only pointwise positivity and may tend
to zero with the member index.  Consequently `Item3RadiusInput`,
`Item3GpScaleInput`, and a globally `k`-independent `SigmaScaleField` cannot be
discharged from the present bundle merely by choosing `D` large.

No endpoint assumption was added.  The honest next choice is either to produce
a sequence-uniform quantitative normal-coordinate inverse-exp radius from the
book's bounded-geometry hypotheses, or to redesign the B/C construction around
fixed-index local radii together with an explicit diagonal/eventual argument.
The conditional endpoint remains 0% proved.
