# H6StageMetrics

This module extracts one common subsequence for the H6 chart metrics at all
finite live source slots while retaining a separate phase-radius domain for
each slot.

The construction reuses the fixed-center `exists_h6_metric_lim` theorem and
the existing finite diagonal extractor. It does not use the legacy
`NormalRadiusProfile`, `normalCoordMetric`, or fixed-base chart provider.

Focused and exact verification are GREEN (`4145/4145`). The finite live-slot
metric extraction is complete (100%).

This extraction is now combined with the H6 support, root, and branch
producers by `H6NormalData.exists_stage_data`. The next frontier is the
provider-native input/Step-B1 consumer seam, not another metric diagonal.
