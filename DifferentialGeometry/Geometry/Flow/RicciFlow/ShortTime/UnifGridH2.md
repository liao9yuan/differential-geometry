# UnifGridH2

## Status (2026-08-06)

`h2_tame_unif` is the dimension-three class-first finite-summation adapter for
the exact post-witness conclusion of `h2_grid_tame`.  It fixes `B0 B1 : ℝ → ℝ`
from the background metric, class parameter, tensor valences, and pointwise
coefficient family before the class metric and tensor fields vary.

The proof reuses the metric-local summation kernel `grid_h2_le`.  Its lower
grid certificates come from `h2_grid_unif`, while its unique total-order-three
certificate comes from `h3_top_grid_unif`; hence the lower `H2` radius remains
separate from the top third-derivative bound.  No new analytic assumptions,
frontier wrappers, or `sorry`s are introduced.

Focused verification passed with four Lean threads under the 6 GB cap.  The
axiom audit reports only the project's standard `propext`, `Classical.choice`,
and `Quot.sound`; the theorem is therefore 100% complete locally.  The full
joint tame producer and `lowreg_bounds_unif` remain theorem-level 0%; dedicated
low-regularity supporting machinery toward `(N)` remains approximately 98%,
`ricci_flow_unif_existence` remains 0%, and whole HCG closure remains
approximately 3%.

## Class-first low-window adapter

`h2_low_unif` is the matching class-first summation theorem for pointwise
grids whose order-`i` window stops at total order `i`.  Its coefficient depends
only on the background, class parameter, valence, and fixed pointwise grid
constant; it consumes only class metric jets of orders one and two.  This is
the reusable integration layer for the moving rank-two trace.

Focused verification passed without warnings.  Its axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`.
