# Class-first mixed H2 application estimate

## Status (2026-08-06)

`appRS_h22_unif` is the generic-valence, dimension-three class-first sibling of
`appRS_h2_h2_h2`.  It uses the already uniform `grid_rs_unif` order-two
two-arm product grid and the existing pointwise covariant Leibniz grid for
`appCcRS`.  Its constant is chosen before the class metric varies, and its
public class inputs are uniform equivalence plus metric jets of orders one and
two.

The proof keeps the mathematical frontier unchanged: the smaller order-`i`
Leibniz triangle is bounded by the single order-two triangle returned by
`grid_rs_unif`, then the three output jet cells are summed.  No new analytic
assumption or metricwise existential constant is introduced.

Focused verification passed.  `appRS_h22_unif` depends only on the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.  The local package is
therefore 100% implemented and verified.
The class-first joint tame producer, `lowreg_bounds_unif`, and
`ricci_flow_unif_existence` remain theorem-level 0%; their dedicated
uniform-existence infrastructure remains approximately 97%, and the whole HCG
compactness project remains approximately 3% complete.

## Status (2026-08-08)

`appCc_h23_h2_unif` is now proved in the same canonical class-first application
layer.  It specializes the mixed order-two grid to a rank-`(3,2)` coefficient
acting on one derivative of a rank-two tensor, and uses the uniform rank-two /
rank-three curvature-action packet to convert the acted tensor's spectral `H3`
norm into its first four covariant jets.  The resulting `H3 → H2` constant is
chosen before the metric varies over the order-three class.

Focused verification passed.  This application cell is 100% complete.  Its
diagonal D1 pairing consumer is also complete in `UnifLow1PathPair.lean`, but
the combined D0/top directed-Green residual remains unstated (0%), as does
`lowbase_full3_unif` itself (0%).  The D1 cell is therefore 100% while the
rounded dedicated Route (c) machinery remains approximately 92%; theorem `(N)`
remains 0%, and the whole HCG compactness project remains approximately 3%.
