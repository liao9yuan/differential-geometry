# H2H4Principal

## Result

The existing mixed-tensor theorem `appRS_h2_h2_h2` already contains the
three-dimensional Sobolev-algebra input needed at low base order.  This module
specializes it to `appCc` and combines it with `icg_comp_norm`,
`hsJet_le`, and `hs_le_jet`.

The public theorem `appCc_h2_h4_h2` proves that an operator coefficient whose
covariant `L2` jet through order two is bounded by `A` acts on a second
covariant derivative from spectral `H4` to spectral `H2`, with norm at most a
fixed constant times `A`.  No high-order condition on the Sobolev exponent is
introduced.

Focused verification passed without local warnings.  The module's targeted
refresh also passed.

## Frontier

This is the smooth-core estimate.  `AppD2Hs.lean` now extends it to a bounded
linear map from the completed `H4` tensor space to the completed `H2` tensor
space.  The remaining frontier is continuity of the resulting operator with
respect to the spectral `H2` coefficient, followed by time measurability and
the affine nonautonomous forcing decomposition.
