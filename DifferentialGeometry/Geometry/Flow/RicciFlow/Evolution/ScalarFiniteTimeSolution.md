# ScalarFiniteTimeSolution

## 2026-08-08 status

`flow_end_le` is source-proved and focused/exact verified.  Its public input is
now the weakest datum used by the proof: pointwise positive scalar curvature of
the fixed initial metric.  It applies the
existing scalar lower-barrier and `finiteTime3D` machinery directly to an
arbitrary `SolutionOn (closedOpen 0 T)` segment.

The scalar minimum is supplied for the static family
`fun _ x => metricScalarAt g0 x`; `initMin_of_start` transports that same
package through `S.family.metric 0 = g0`.  Thus every candidate starting at
`g0` uses one common `c0`.  The separate public producer
`scalar_pos_of_ricci` derives this scalar positivity from positive Ricci plus
the dimension-three hypothesis; Hamilton assembly calls it explicitly.  No part of the proof
mentions `Ham3FlowPackage`, `curvUnbounded`, or `ham3_finite_time`.

Status accounting:

- `flow_end_le`: 100% source-proved and verified;
- `scalar_pos_of_ricci`: 100% source-proved and verified;
- dedicated segment-level finite-lifetime machinery: 100%;
- `exists_max_flow`: not yet stated in this module (0% theorem completion);
- maximal-flow dedicated machinery after this brick: approximately 20%.
