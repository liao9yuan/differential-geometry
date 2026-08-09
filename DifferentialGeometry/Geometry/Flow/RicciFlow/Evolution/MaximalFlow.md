# MaximalFlow

## Status (2026-08-07)

`exists_max_flow` is implemented without `sorry`.  The constructor now takes a
three-dimensional compact boundaryless initial metric with pointwise positive
scalar curvature and returns a positive endpoint, a `SolutionOn [0, omega)`, its
`IsSolutionOn` proof, the initial-value equality, and actual
`IsMaximalAtEndpoint`.

The previous positive-Ricci interface was focused-green.  After weakening the
interface, the direct scalar producer is focused/exact-green.  Rechecking this
module is currently blocked only by the missing
`DeTurckRemainderLowBaseH2Pair.olean` imported through `MaximalTime`; the source
proof itself has not produced a Lean diagnostic.  Exact refresh and axiom audit
therefore remain pending.

## Construction

- `FlowTo` retains the one-sided `Ico` chart-Gram regularity and `Ici 0` metric
  PDE needed by forward uniqueness at time zero.
- `flow_to_seed` projects `short_time_joint` through `solutionOn_of_joint`.
- `flow_to_agree` applies `ricci_flow_forward_unique` on the common interval.
- `flow_to_extend` transports both retained invariants from the old candidate
  near zero and uses the extended solution on the positive-time interior.
- `exists_max_flow` takes the supremum of candidate endpoints.  A fixed initial
  scalar minimum and `flow_end_le` bound the endpoint set independently of the
  candidate.  Choice independence supplies local candidate representatives for
  the supremal metric family, and an extension past the supremum contradicts
  `le_csSup`.

## Progress accounting

- `exists_max_flow`: 100% source-implemented; current weaker interface
  verification and axiom audit pending on the missing imported artifact.
- Dedicated maximal-compatible-flow machinery: 100% implemented.
- `ham3_flow_exists_normalized`: source assembly written; trusted/axiom-clean
  completion remains 0% until downstream verification and audit.
- Hamilton positive-Ricci theorem program: this closes the maximal-flow
  existence producer, but later pinching, blow-up compactness, and spherical
  classification phases remain separate; whole HCG machinery remains
  conservatively approximately 87%.
