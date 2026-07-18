# StepCStageInjectivity

## Verified result

`HasStageJetData.inj_tail` is focused-green.  With the same explicit radius
room used by `return_tail`, it proves one rectangular all-pairs tail on which
the actual global `stageComparisonMap` is injective on the retained closed
source ball.

The proof uses the reverse-stage comparison map only as an approximate return
map.  Equality of forward images puts two source points inside one uniform
intrinsic buffer; the normal-coordinate segment then stays in a slightly
larger retained ball, and the order-one stage-map jet estimate plus the
Neumann injectivity lemma identifies the two points.  No exact inverse claim,
whole-cage containment, endpoint-radius assumption, or new compactness input
is introduced.

## Frontier and accounting

- This global-injectivity producer: 100%.
- Stage-map local diffeomorphism, basepoint preservation, return control, and
  global injectivity: 100% as individual producers.
- Concrete `StepB1RawInput` comparison fields: approximately 55--60%; the
  forward and exact-inverse `PreApproxIsoDataOn` fields remain open.
- `MetricCompactBase.exists_b1_raw` and textbook Step B1: 0% as theorems until
  their remaining proof is discharged without `sorry`.
- Dedicated B/C machinery: approximately 98%; Chapter 4 machinery about 90%;
  whole-HCG machinery about 60%.

The next analytic frontier is the chart-coefficient-to-intrinsic
`tensor02CovDerivNormWith` bridge, followed by its exact-local-inverse version.
