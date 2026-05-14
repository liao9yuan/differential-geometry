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

The companion now exposes a thin wrapper for the local fixed-frame Ricci
evolution step:

- `eq_ricci_tensor_ricci_flow_two_local`

It also exposes `scalar_contracted_bianchi_reduction`, the scalar algebra bridge
from the second-derivative contracted-Bianchi trace to the reduction used by
`eq_scalar_curv_evolu`.

Verification passed.

## 2026-05-13 stale Christoffel-to-Riemann wrappers removed

The wrappers
`eq_riemann_curvature_three_one_ricci_flow_one_local` and
`eq_ricci_tensor_ricci_flow_one_local_from_christoffel` were removed because
they delegated to the old local Christoffel-evolution-to-`Rm13` producer chain.
That chain is no longer present in `RicciFlower.RicciFlow.Evolution.Ricci`.

The remaining Section 6.1 Ricci wrapper consumes the honest
`RicciVariationFormulaInFrameOnLocal` input directly.

Verification passed.

## 2026-05-13 full Section 6.1 statement scaffold

Added book-facing component statements for the rest of Chapter 6.1 before
Uhlenbeck's trick.  The new declarations intentionally expose future theorem
frontiers with `sorry` instead of hiding them behind extra assumptions.

New scaffold covers:

- Lemma `lem:general_evolution_revisited`, split into Christoffel, Riemann,
  Ricci, scalar, and volume-trace component RHS definitions/statements.
- Equations `eq:riemann_curvature_three_one_ricci_flow_one` and
  `eq:ricci_tensor_ricci_flow_one`.
- Lemma `lem:scalar_positivity_is_preserved`.
- The 3D Riemann-from-Ricci display and
  `eq:ricci_tensor_ricci_flow_dimension_three`.
- Corollary `cor:ricci_positivity_is_preserved`, with separate nonnegative and
  positive frame-component statements.
- The Riemann heat equations in `(3,1)` and `(4,0)` form.
- The quadratic `B_ijkl` definition, its algebraic identities, and the
  Riemann evolution formula in terms of `B`.

Verification passed with the expected scaffold `sorry` warnings.
