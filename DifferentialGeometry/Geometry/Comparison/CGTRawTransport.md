# Raw loop transport

## Role and accounting

This module is the bounded completeness-free transport producer for the raw
CGT route.  It stops at continuity, C1 regularity, and exact pullback
path-length preservation.  It does not state nonexpansion, construct minimizing
joins, invoke strict Jensen, or prove either final P1b endpoint.

The P1b E1/E2 theorem endpoints therefore remain 0% complete.  Dedicated P1b
machinery remains about 96% complete, and the whole Poincare endpoint remains
0% complete.

## Mathematical route

The loop-radial path concatenates a flat based loop with `rawFlatPath`.
`rawLoop_len` and `rawLoop_len_lt` reduce its length to the existing exact raw
radial length.  `exists_raw_lift` then gives a canonical `IsLiftOn` witness in
the raw framed-exponential ball.  `rawLoopLift` chooses that witness and
`rawTransport` records its endpoint.

Continuity uses the map-generic `IsLocalHomeomorph.continuous_lift` theorem.
Joint continuity of the radial family is proved from the caller's local
diffeomorphism on the ball and the fact that `rawFlatRay` stays in that ball;
no globally smooth intrinsic exponential is imported.  The curve theorem gets
C1 regularity from `IsLiftOn.contDiffOn` and exact source length preservation
from two applications of `rawPull_pathLen` plus equality of projections.

The generic lift-continuity theorem is declared in the narrow Mathlib module
`Topology.Homotopy.Lifting`, which was not in the transitive closure of the
three raw CGT imports.  The module therefore imports that declaration directly
instead of acquiring it indirectly through heavier intrinsic CGT machinery.

## Reuse and boundary

- Reused: `rawFlatPath_flat`, `rawFlatPath_len`, `exists_raw_lift`,
  `Path.trans_continuous_family`, `IsLocalHomeomorph.continuous_lift`,
  `IsLiftOn.contDiffOn`, `rawPull_pathLen`, and `pathELength_congr`.
- No collision-vector specialization is present; downstream code can supply
  any flat loop `c : Path p p`.
- No curvature, complete extension, minimizing join, or Jensen machinery is
  imported.

The next geometric frontier after this module is a raw distance-realizing core
join.  Only after that bridge is available can exact transport length be turned
into the nonexpansion statement used by the fixed-point argument.

## Verification

Focused verification passed without warnings.  The first pass exposed only
local instance-scope, open-subtype naming, and radial-membership elaboration
issues.  The only import-boundary issue was the absent canonical generic
lift-continuity theorem described above; no alternate transport hierarchy was
introduced.

Static review found no `sorry` or `admit`, no declaration over the twenty-letter
budget, and no `CompleteSpace`, connectedness, sigma-compactness of the ambient
manifold, curvature, minimizing-join, collision-vector, or Jensen assumption.
