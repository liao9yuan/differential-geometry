# CompactGeodesic

## Result

`exists_geo_one_cpt` is complete.  It produces a geodesic through times `0` and
`1` with prescribed initial point and velocity from compactness of a strictly
larger closed metric ball.  The statement does not assume `CompleteSpace M` and
does not expose `expDomain`, maximal-geodesic witnesses, or their public
semantics.

The endpoint-continuation layer genuinely requires `T2Space M` and
`SigmaCompactSpace M`, so these hypotheses remain explicit in the producer.

## Proof route

The proof reuses the prescribed-velocity seed from `LocalGeodesicSeed`, chooses
a finite horizon `B > 1` with `c * B < r`, and invokes the capped continuation
producer `geo_Ioo_extend_to`.  Candidate extensions agree with the seed near
zero, so constant geodesic energy gives the speed bound `c`.  The native
distance estimate then places a left-neighborhood of every candidate endpoint
inside the supplied compact closed ball, where `endpointCont_compact` supplies
continuation.  Agreement with the seed recovers the initial point and model-space
velocity at time zero.

No Zorn argument is duplicated in this file; it remains encapsulated in
`geo_Ioo_extend_to`.

## Verification and scope

Focused verification passed without warnings after the required targeted
refresh of the upstream `HopfRinow` module.

- `exists_geo_one_cpt`: 100% complete and checked.
- Dedicated compact finite-horizon producer machinery used here: 100% complete.
- Downstream local compact-closure Bishop comparison theorem: not stated or
  proved in this file (0% theorem completion here); this producer is estimated
  to be under 5% of that larger assembly.

