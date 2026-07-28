# AppD2Hs

## Result

`appD2Hs` is the completed spatial action
`U |-> appCc Phi (nabla^2 U)` from spectral `H4` to spectral `H2`.
In dimension three, `appD2Hs_norm` controls its operator norm by the intrinsic
coefficient jet through order two, and `appD2Hs_core` identifies the completed
map with the exact smooth geometric expression.

The construction uses the existing dense smooth inclusion and the low-base
`H2 x H2 -> H2` tensor product estimate.  It does not require pointwise
high-order coefficient bounds.  Focused verification and the targeted module
refresh both passed without local warnings.

## Frontier

The map is linear in its input section, but the public API does not yet expose
additive or difference identities in the coefficient `Phi`.  The next smallest
producer is an operator-norm difference estimate controlled by the spectral
`H2` coefficient difference.  That estimate is needed to extend metric-dependent
principal operators from smooth metrics to a genuine low-regularity `H2` state.
