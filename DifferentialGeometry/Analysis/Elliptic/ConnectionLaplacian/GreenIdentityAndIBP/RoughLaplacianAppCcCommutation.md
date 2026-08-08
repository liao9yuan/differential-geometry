# RoughLaplacianAppCcCommutation

## Mixed-rank trace transport

`cometricTrace_appCcRS` lifts the existing double-trace/slot-extension
commutation identity from covariant tensors to arbitrary contravariant valence.
It is the exact structural bridge needed to trace the top argument corner of a
mixed-rank `appCcRS` Leibniz expansion without changing tensor
representations.

## Verification and scope

The focused check passed with four Lean threads and the 6144 MB cap, without a
local warning.  It does not prove the Route-(c) `q/K` curvature cancellation;
that complete-edge theorem remains unstated and 0% complete.
