# KochLammEarlyFlux

## Scope

This file connects the local `L²` arm of `KLSource1` to the gradient-Carleson
source class used by the global early first-derivative heat estimate.

`klL2Scale_inv` and `klL2_inv_sq` record the exact scale identities.
`gradMass_eq_l2sq` identifies the rough cylinder mass with the square of the
local `eLpNorm 2`.  `kl1_to_gradCarl` then converts
`KLSource1 T A₂ Aₚ f` into `GradCarl T A₂² f`.

No endpoint theorem is claimed here.  `ricci_flow_forward_unique` remains 0%.
