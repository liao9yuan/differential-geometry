# StepB1MetricReverse

## Role

This file is the coordinate-level reverse metric producer for Step B1.  It
uses the exact `Function.invFunOn` of the forward stage comparison map; the
opposite-direction comparison map remains only an approximate return map for
injectivity and is never identified with the exact inverse.

## Checked result

`HasStageJetData.inv_cov_comp_tail` is focused-green with no `sorry`.  It gives
the intended rectangular `k,l` tail, a basis-parametric finite
covariant-component tower, and evaluation on the actual moving target image of
the buffered source cover.  Its proof uses `inv_chart_conv`, normal-coordinate
metric convergence, `MapCInfConvOnCompacts.pullbackAlong`, and
`metric_tower_conv`.

The first API gap was that `inv_chart_conv` hid the eventual smoothness of its
exact inverse charts even though its moving-inverse construction already proves
it.  The upstream theorem now exposes that conclusion in its output, with no
new assumption or radius field.

The source/target roles are explicit: the exact inverse pulls back the
source-stage metric, while the target-stage metric supplies the background
Christoffel coefficients and subtracted metric.  The reverse finite-stage
comparison map is not used or identified with the exact inverse.

## Remaining frontier

This theorem is still coordinate-level.  A downstream intrinsic bridge must
turn its finite component bounds into the reverse
`tensor02CovDerivNormWith`/`metricDerivNorm` tail on the local pullback-field
carrier before `StepB1RawInput` can be assembled.

## Accounting

- `inv_cov_comp_tail` theorem: 100%.
- Dedicated reverse coordinate machinery: 100%.
- Reverse intrinsic norm/carrier bridge: not completed in this file.
- StepB1RawInput producer: still 0% until the forward and reverse intrinsic
  metric tails are both checked and the producer theorem is proved.
- Textbook Step B1: 0%.
