# UnifPhiDevH2

## Status (2026-08-06)

`phi_dev_h2_unif` is the dimension-three class-first sibling of `phi_dev_h2`.
It selects the radius and deviation coefficient from `gBase` and `Λ` before
the class metric varies, using `inv_coeff_h2_unif` and the explicit
dimension-only principal-coefficient constants.

Focused verification passed with four Lean threads under the 6 GB cap, without
warnings.  Its axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`, so this class-first theorem is 100% complete locally.  It is only
the unintegrated top-deviation producer; the integrated top-path arm,
fixed-curvature arm, full joint tame producer, `lowreg_bounds_unif`, and
`ricci_flow_unif_existence` remain open.  Dedicated supporting infrastructure
is approximately 99%, while whole HCG closure remains approximately 3%.
