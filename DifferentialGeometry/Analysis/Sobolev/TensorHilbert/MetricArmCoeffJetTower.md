# MetricArmCoeffJetTower

## Current change

The generic smooth output-slot permutation producer
`rsDomDomCongrFib_contMDiff`, its section constructor, and its section
read-off were moved to
`OperatorFieldOutputSlotPermutation.lean`.  This file now imports that
lower canonical module and retains only the metric-arm coefficient estimates
that consume the API.

## Verification

The extracted lower module is focused-green.  This large downstream estimate
file was not rechecked because verification is currently blocked by missing
unrelated shared artifacts.  The source edit is an exact declaration move,
not a change to theorem statements.
