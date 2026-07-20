# HeatDuhamelCore

## Role

This file is the physical-space entry point for the causal smooth-core
`L²` Hessian estimate.  It transfers spatial derivatives from the heat kernel
to a compactly supported smooth source, avoiding a separate spacetime Fourier
realization theorem.

## Current state

- `slice_compact` packages compact support of each spatial slice.
- `heatD1_ibp` transfers one heat-kernel derivative to the source.
- `heatD2_ibp` transfers one of two heat-kernel derivatives to the source.
- `heatD2_ibp2` transfers both derivatives; slice-shaped versions are exported.
- `heatPot1_eq_pot0` identifies the causal divergence potential with the
  ordinary potential of the spatial derivative for a smooth compactly
  supported space-time source.
- `heatPot0_zero` and `heatPot1_zero` record exact initial values.

## Verification

Focused verification is GREEN and warning-free.  The file contains no
`sorry`, `admit`, axiom, or opaque declaration.

## Next frontier

The next producer is the jointly time-dependent ordinary Duhamel PDE/jet
realization: spatially differentiate `heatPot0`, identify the time derivative
with Laplacian plus source, and prove the zero trace continuously as time tends
to zero.  The derivative-transfer identities here remove the terminal-time
singularities needed for its domination arguments.

Endpoint accounting remains honest: `ricci_flow_unif_existence` is still 0%
until its exact theorem is proved.  The exact causal `heatD2_l2` theorem is
also 0% until stated and proved; its dedicated physical-space machinery is
about 15% complete (the derivative-transfer brick is done, while the general
PDE/jet realization, finite-slab energy identity, and exhaustion remain).
