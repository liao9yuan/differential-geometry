# LowRegCoeffJets

## Route

This file follows the three-dimensional low-regularity route required by the
uniform short-time construction.  It keeps the frozen spectral metric `g0`
separate from the fixed DeTurck gauge background `g_bg`.

The source currently contains:

- `convex_h3_jet`, transferring endpoint spectral `H3` bounds to the whole
  convex path without shrinking time;
- `ricci0_h1` and `dla_h1`, direct range-two jet bounds for the order-zero
  Ricci and `DLa` coefficients;
- `dlbDiff_h1`, a range-two jet bound for
  `DLb(g_bg) - DLb(g0)` obtained from the pointwise grid-window theorem and
  `h3_grid_int`;
- the rank-generic `grid_h1_le` and `h1_of_grid` integration bridge;
- `riem_h1`, the complete range-two jet bound for the fixed-curvature
  `lieCorr0` piece.  Its proof keeps the exact moving double trace applied to
  the fixed curvature passenger, places the trace in `H1`, the passenger in
  `H2`, and uses the mixed `appCcRS` product estimate;
- `tail0_decomp`, the exact cancellation-preserving decomposition of the
  remaining order-zero tail;
- `rhs0_h1_of_aux` and `rhs1_h2_of_aux`, consumer-shaped synthesis theorems
  whose remaining auxiliary inputs are explicit.

The order-zero source frontier after `dlbDiff_h1` and `riem_h1` is the `H1`
control of the insertion difference, vector--bilinear, and mixed fields in
`tail0_decomp`.  The order-one frontier is the `H2` control of the Ricci
`appCcRS` arm and `deTurckLieArm1Coeff`.

## Verification and accounting

The current source passes focused verification.  This establishes elaboration
of the local coefficient-jet producers; it does not discharge any unrelated
analytic `sorry` elsewhere in the short-time tree.

`ricci_flow_unif_existence` remains 0%.  This machinery is currently a
three-dimensional route and therefore does not by itself close the existing
dimension-generic public endpoint statement.

## 2026-08-06 supplied order-zero assembly

`rhs0_h1_parts` now exposes the reusable supplied-parts assembly hidden inside
the older metricwise `rhs0_h1_of_aux`.  It accepts `H1` bounds for the Ricci,
`DLa`, and cancellation-preserving tail pieces and returns the exact complete
order-zero RHS coefficient bound.  This is a projection/assembly lemma, not a
new analytic frontier and not a replacement hypothesis.

Focused verification and direct export passed.  Its axiom census contains only
`propext`, `Classical.choice`, and `Quot.sound`.  This helper is 100% complete;
the final class-uniform low-bound packet remains a separate unstated theorem.

## 2026-08-07 self-kappa H2 pair

`symm_grad3_sub` and `koszul_covec_sub` record the exact subtraction laws for
the fixed Koszul operator.  The public `kappa_pair_h2` then proves that the
two-state self-background lowered connection difference has an `H2` jet
bounded by ten times the `H3` jet of the perturbation difference.  The proof
uses exact Koszul cancellation, so it needs neither an inverse-metric estimate
nor a spectral small-ball hypothesis.

Focused verification passed.  This brick is complete and is the self-kappa
input for lifting the arbitrary-background `AMix` telescope from `H1` to `H2`;
the full `AMix` arm and the other two order-zero arms remain separate work.

The public `pbLow_h2_mul` also exposes the linear-in-radius form of the fixed
background pairing estimate.  Its focused verification and direct module
refresh passed.  This is the second connection-factor input consumed by
`amixBg_pair_h2`; it does not by itself estimate a complete order-zero arm.
