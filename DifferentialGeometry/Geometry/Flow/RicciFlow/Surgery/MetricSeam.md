# MetricSeam

## Role

`MetricSeam.lean` adds the first proof predicate over `SurgerySeam`.  It says
that the open-neighborhood identification pulls the post-surgery metric back
to the pre-surgery metric at retained points.

The equality is deliberately restricted to `S.keep`: the discarded part of
the old event neighborhood may be deformed and replaced by a cap.  A stronger
whole-neighborhood equality implies the predicate through `metricSeam_of_eq`.

The implementation reuses the canonical cross-model metric pullback and open
metric restriction APIs.  No parallel pullback construction was added.

## Verification

Focused verification is pending.

## Next frontier

The next S0 producer is a surgery event joining two fixed-manifold
`SolutionOn` slabs at an event time.  The event should carry the seam data and
an `IsMetricSeam` proof, while the Ricci-flow equations remain in separate
`IsSolutionOn` proofs for the slabs.

## Honest progress

- Metric-seam predicate: source-written, verification pending.
- Global RFWS endpoint: unstated, therefore 0%.
- Dedicated S0 data-model machinery: approximately 15--20% if this module
  verifies.
- Whole surgery phase: approximately 2% infrastructure, theorem endpoints 0%.
- Whole post-HCG Poincare program: approximately 15--20%.
