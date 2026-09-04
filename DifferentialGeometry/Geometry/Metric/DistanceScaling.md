# DistanceScaling

## Route

`riemannianEDistOf` installs the chosen smooth metric as the local
`RiemannianBundle`, so symmetry and the triangle inequality are direct
transports of Mathlib's intrinsic Riemannian extended-distance theorems.  This
keeps the facts at the metric layer and removes the need for downstream private
copies.

## Verification

`edistOf_triangle` and `edistOf_comm` passed warning-free focused verification.

## Frontier

The extended-valued triangle theorem needs no connectedness or completeness.
A real-valued version additionally needs a finiteness producer and therefore
belongs above the minimizing-geodesic layer, not in this file.
