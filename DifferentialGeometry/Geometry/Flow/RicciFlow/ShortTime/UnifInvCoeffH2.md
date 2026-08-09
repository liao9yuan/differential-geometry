# Class-first inverse-metric coefficient bounds

## Status (2026-08-06)

`inv_coeff_h2_unif` is the dimension-three, class-first sibling of
`inv_coeff_h2`.  It chooses one positive realization radius and one
pointwise/two-jet coefficient before the class metric varies.

The order-zero cell uses the uniform Morrey/curvature-action operator radius
and class volume comparison.  The positive derivative cells use the explicit
`invDiff_grid_unif` coefficient together with `rank_two_grid_unif`; the lower
jet radius is frozen at the uniform `H²` covariant-sum constant, while the top
derivative retains the perturbation norm.  This keeps every output cell linear
in the `H²` norm without asking for metric jets above order three.

Focused verification passed.  `inv_coeff_h2_unif` depends only on the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.  The local theorem and
its dedicated implementation are therefore 100% complete.

The class-first joint tame producer, `lowreg_bounds_unif`, and
`ricci_flow_unif_existence` remain theorem-level 0%; this verified result is
supporting infrastructure for their top-path packet, not yet their assembly.
