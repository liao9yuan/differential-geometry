# Minimizing-ray prefix reduced-length estimate

## Status

`lMinPrefix_le` is complete and focused-verified.  It records the P2
minimizing-ray prefix estimate with scalar nonnegativity required only on the
intervening square-root-time segment
`[sqrt s, sqrt tau]`.

## Proof route

The proof obtains minimizing membership at `s` from `lMinDomain_down`, rewrites
both reduced lengths through the exact minimizing ray actions, and decomposes
the terminal action at `sqrt s`.  The tail action is nonnegative from the
pointwise nonnegative regularized speed square and the local scalar assumption.
`redLength_mul` then supplies the final normalization algebra.

## Verification

Focused verification passed without warnings.

This theorem itself is 100% complete.  It is a narrow P2 L-geometry bridge;
the broader P2b package theorem remains unstated at 0%, with dedicated
machinery roughly 64--68%.  Compact ordinary-flow P2a, including `smooth_nlc`,
remains closed at 100%; the ancient Harnack speed producer belongs to P3.
