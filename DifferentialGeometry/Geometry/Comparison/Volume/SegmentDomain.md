# Segment-domain API

## Compact raw minimizing locus

The closed metric tangent ball API (`closedGBall`, `isClosed_closedGBall`, and
`isCompact_closedGBall`) now lives beside `gBall` and `SegDom`.  These
declarations were moved mechanically from `SegmentPolar.lean`; their namespace,
names, signatures, and proofs are unchanged.

`isCompact_rawSeg` is the first compact-closure producer after raw minimizing
surjectivity.  A strict radius buffer `R < R₀` and compactness of the base
`closedEBall p (ENNReal.ofReal R₀)` put the entire tangent `closedGBall` of
radius `R` inside `expDomain` via `mem_expDom_of_cpt`.  The verified smoothness
of `expMap` on `expDomain` then makes the ENNReal-valued minimizing equality
locus relatively closed in that compact tangent ball.

`ball_sub_rawSeg` covers the open metric ball of radius `R` by the raw
exponential image of the same truncated equality locus.  It uses
`RadialSurjectivity.minExp_of_cptBall`; coverage only needs `R ≤ R₀`, so its
radius hypothesis is intentionally weaker than the strict buffer required for
compactness.  No new segment-domain predicate or parallel exponential API is
introduced.

## Verification

The focused Lean check is warning-free green.  In `ball_sub_rawSeg`, substituting
the endpoint equality `expMap g p v = q` makes the minimizing-length conclusion
from `minExp_of_cptBall` exactly the raw-segment membership equality.  This avoids
transporting `riemannianEDist` across the two hidden tangent-norm instances.

The local compact-closure Bishop--Gromov endpoint remains unstated and 0%.
The two compact raw-segment producers in this file are verified (100% of this
local brick), but they remain only an early infrastructure step toward that
endpoint and the wider P1 comparison campaign.
