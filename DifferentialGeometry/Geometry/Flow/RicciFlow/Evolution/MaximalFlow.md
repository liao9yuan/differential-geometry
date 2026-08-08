# MaximalFlow

## Status (2026-08-07)

`exists_max_flow` is implemented without `sorry`.  The constructor takes a
three-dimensional compact boundaryless initial metric with positive Ricci
curvature and returns a positive endpoint, a `SolutionOn [0, omega)`, its
`IsSolutionOn` proof, the initial-value equality, and actual
`IsMaximalAtEndpoint`.

Focused verification passed.  The exact producer refresh was started after the
focused check; record its final result here once the downstream Hamilton
assembly is checked.

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

- `exists_max_flow`: 100% implemented and focused-verified.
- Dedicated maximal-compatible-flow machinery: 100% implemented.
- `ham3_flow_exists_normalized`: assembly patch written; verification pending.
- Hamilton positive-Ricci theorem program: this closes the maximal-flow
  existence producer, but later pinching, blow-up compactness, and spherical
  classification phases remain separate; whole program remains approximately
  80% complete pending the live project-map reconciliation.
