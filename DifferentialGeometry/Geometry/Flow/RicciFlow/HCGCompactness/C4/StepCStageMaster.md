# StepCStageMaster

## Status

`stageMapCast` and `HasRadiusTail.geom_tail` are focused-green and contain no
`sorry`.  This closes the purely index-theoretic transport from a fixed
integer-radius tail to the master sequence for the first three concrete Step-B1
fields.

## Implemented route

- `stageMapCast` transports only the source and target manifold indices of the
  actual finite-stage comparison map.
- `HasRadiusTail.geom_tail` keeps the radius-tail selector, its strictness, the
  exact tail/master index equality, and the corresponding `HasStageJetData`.
- One shifted threshold then gives, for every pair of sufficiently large
  master indices, local diffeomorphism and injectivity on the retained closed
  source ball together with exact basepoint preservation for the same
  transported map.
- No `LiveSlot` or `InterSlot` equivalence is introduced.  All branch-local
  types remain attached to the fixed-radius tail where they were constructed.

The equality transport is isolated in a private generic lemma.  This avoids
dependent elimination on expressions such as `psi k`, which was the only local
Lean obstruction encountered while assembling the theorem.

## Remaining frontier and accounting

The master-sequence transport in this file is complete (100%).  It does not
prove either forward or exact-inverse `PreApproxIsoDataOn`; those still require
the chart-coefficient-to-intrinsic covariant tensor bridge.  Consequently the
concrete `MetricCompactBase.exists_b1_raw` theorem remains unproved (0%), as
does textbook Step B1 (0%).  Dedicated C-side comparison-map infrastructure is
about 98%; the actual B-side raw-field closure is roughly 55--60%.
