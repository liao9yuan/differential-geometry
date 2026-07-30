# StepCStageComparisonH6.lean

## 2026-07-29 provider-native root, jet, and base readout

`stage_root_tail`, `stage_jet_of_root`, `stage_jet_tail`, and
`stage_base_tail` keep the H6 family `d.chart` through the stage target,
finite-stage comparison map, root decode, derivative jet, and pointed
basepoint readout. `exists_supp_base` is the direct consumer of
`H6NormalData.exists_supp_data`: on one selected subsequence it returns both
the full H6 support/transition package and pointed preservation for the actual
stage maps.

`exists_supp_metric` now retains the exact all-stage center bound from the
metric extraction. `stage_data_of` combines that package with the H6
fixed-center branch diagonal, and `exists_stage_data` chooses a physical
`aMin`, performs the common finite extraction, and returns the complete
`HasStageJetDataOn ... d.chart` package.

Focused and exact verification are GREEN (`4148/4148`). Direct axiom audits of
`exists_diagPair_at`, `exists_stage_pair`, `stage_data_of`,
`exists_supp_metric`, and `exists_stage_data` report only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

Gate 5 provider substitution is complete (100%) at the support, target-decode,
root, jet, base-readout, and master stage-data levels. This is not an
unconditional MSM135 endpoint: that theorem remains unstated (0%), and the
provider-native input/Step-B1 assembly remains the next phase. The existing
legacy input hardcodes `NormalRadiusProfile`, `normalCoordMetric`, and the
default stage-map provider; converting the H6 package back to it would require
the independent unproved `NormalRadiusProfile.le_exp_radius`. The correct next
step is therefore a native consumer interface, not a legacy conversion.
Whole-HCG supporting machinery is about 70%.

## 2026-07-29 canonical scale and raw consumer

`stageScale` exposes the fixed positive coefficient already selected by the
H6 branch producer. `stage_data` and `stage_diag` use that exact value, so the
divisor can be chosen afterward without a circular existential witness.
Focused and exact verification pass (`4150/4150`).

The master package now feeds `H6NormalData.b1_raw_of_diag`; the H6 provider
path through the raw record and Step D is complete and axiom-clean. The
remaining unconditional seam is the legacy shape of
`MetricCompactnessInputs`, not stage geometry or a missing radius inequality.
