# Compact-double approximation

## Result

`CompactDouble.lean` introduces `ClosedApprox`, a data-only bundle for a compact
pointed metric, and proves `exists_closed_flow` by reusing the native closed
Ricci-flow short-time existence theorem through `FlowTo`.

No theorem yet constructs the Morgan--Tian doubled metrics from `capJoin`.
That construction requires a smooth capped-cylinder metric realization and
uniform lower time, curvature, and injectivity estimates. These remain visible
rather than being encoded as a polished existence assumption.

## Verification

Focused verification passed.

## Progress

P5 main theorem remains 0%. P5-C is approximately 10%: the compact metric to
closed-flow producer is implemented, while the actual double sequence and its
uniform estimates are missing.
