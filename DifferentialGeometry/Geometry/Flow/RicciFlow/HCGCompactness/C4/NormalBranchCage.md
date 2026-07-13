# NormalBranchCage

## Role

This module is intended to combine the center/point cage ledger with one
selected quantitative branch for the whole finite configuration.

## Verified state

- `seqCenterD_dist_le` combines eventual live-slot realization with
  `seqRadius_mem`, giving the explicit ordered-net basepoint-distance bound.
- `liveCenters_dist_le` and `liveCenters_cage` finite-intersect those bounds and
  place every live center in one fixed packing-cage sublevel on a common tail.
- `exists_live_dom` consumes `normalBrScale` at that sublevel and gives one
  relative selected branch domain for all live centers on the same tail.
- `exists_cm_branch` combines `centerPairs_lt_le` with
  `HasNormalBranchDom.exists_pair_readout`; the distance-orientation mismatch
  is discharged by `riemannianEDist_comm`.  The whole finite center/point family
  now lies in one selected `B.readDom`.

Focused verification and the targeted module build pass without a local
`sorry` or warning, including regression against the full-acceptance producer
and its `normalBrScale` compatibility projection.

## Frontier

The fixed-trivialization gate is closed.  `NormalCoordinates.expMapDiffeo`
retains the existing `exists_exp_pd_chart` target-in-base-chart property, and
the finite-family consumer reaches `B.readDom` without a second normal chart.

The physical finite-hat ledger still needs the book's
large-`D` inequality against the positive coefficient produced by
`normalBrScale`.  `normalBrHat` proves the scalar implication, but the exact
assembly witness must remain visible rather than being renamed as a new radius
assumption.

The more immediate center-root blocker is quantitative compatibility with the
realized exponential: `expDiffeoRadius` contains a pointwise qualitative
agreement radius not bounded by `NormalRadiusProfile`.  `readDom` membership
alone cannot produce this inequality.

`StepB1RawInput` and textbook B1 remain 0%; this finite-cage consumer is only
supporting machinery.  Dedicated Step-B/B1 machinery is about 77%, Chapter 4
machinery about 74%, and whole HCG compactness machinery about 51%.
