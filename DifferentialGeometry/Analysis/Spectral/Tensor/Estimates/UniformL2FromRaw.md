# UniformL2FromRaw

## 2026-07-15 uniform component-to-L2 producer

`l2_bdd_of_raw` upgrades one nonnegative bound for every raw chart-frame
component on every active partition-of-unity support to a uniform intrinsic
`L2` bound for an arbitrary tensor family.  The proof uses the POU weight
bounds, finite Riemannian volume, `eLpNorm_le_of_ae_bound`, and the existing
global component reconstruction theorem
`tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq`.

This is a genuine reusable analytic producer rather than a Ricci--DeTurck
wrapper.  It is the local-to-global step needed to turn the new zero- and
first-order RHS chart bounds into a tensor `H1` forcing budget.

Focused verification passed.  The theorem itself is complete (100%).
