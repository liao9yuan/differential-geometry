# MSM110 Chapter 6.1

## 2026-05-12 scalar evolution wrapper

The Section 6.1 companion exposes `eq_scalar_curv_evolu`, a wrapper around
`RicciFlower.RicciFlow.msm110_ch6_1_scalar_curvature_evolution`.

The companion intentionally does not reprove the variation formulas or the
contracted Bianchi identity. Those remain RicciFlower-side inputs.

Verification passed.

## 2026-05-12 broader evolution aliases

The companion now also exposes checked book-label aliases for inverse metric,
Christoffel, Ricci, and volume evolution:

- `eq_inverse_metric_ricci_flow`
- `eq_christoffel_symbols_ricci_flow`
- `eq_ricci_tensor_ricci_flow_two`
- `eq_evolution_of_volume_element_integrated`
- `total_volume_evolution_ricci_flow`

The Riemann `(3,1)` display is recorded in the status map as partially covered
by the local coordinate-frame producer in `RicciFlower.RicciFlow.Evolution.Ricci`.

Verification passed.

## 2026-05-12 local Ricci chain and scalar bridge

The companion now exposes thin wrappers for the local coordinate-frame
Riemann/Ricci chain:

- `eq_riemann_curvature_three_one_ricci_flow_one_local`
- `eq_ricci_tensor_ricci_flow_one_local_from_christoffel`
- `eq_ricci_tensor_ricci_flow_two_local`

It also exposes `scalar_contracted_bianchi_reduction`, the scalar algebra bridge
from the second-derivative contracted-Bianchi trace to the reduction used by
`eq_scalar_curv_evolu`.

Verification passed.
