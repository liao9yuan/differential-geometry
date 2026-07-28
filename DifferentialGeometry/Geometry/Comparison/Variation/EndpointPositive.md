# EndpointPositive

## Role

This module owns the geometry-to-ODE adapter for the sharp Jacobi endpoint
pairing used by the Cheeger--Gromov--Taylor producer.  The intended public
endpoint is `jacobi_pair_pos`.  It is deliberately independent of manifold
completeness and connectedness so the same theorem applies on the intrinsic
exponential pullback ball.

## Current status

`jacobi_pair_pos` is focused- and exact-green.  It is assembled from the
checked positive-speed perpendicular-frame coefficient API and
`IsJacobiSolOn.end_pair_pos`.  The endpoint readout only expands the Jacobi
field in the perpendicular frame, so it does not require a separate
orthogonality hypothesis for its covariant derivative.

## Connectedness policy

This layer never assumes `ConnectedSpace M`.  The current CGT application works
on the connected Euclidean pullback ball.  If a later legacy ambient capstone
requires connectedness, its inputs are restricted to the connected component
of the basepoint; no global connectedness hypothesis is added to HCG inputs.

## Honest accounting

- `jacobi_pair_pos`: theorem 100%; dedicated machinery 100%.
- the intrinsic curvature-bound corollary: theorem 0%; dedicated machinery
  about 80%.
- `intrLoop_ge_cgt`: theorem 0%.
- the unconditional metric-compactness endpoint: theorem 0%.
- whole HCG supporting machinery: about 61%.
