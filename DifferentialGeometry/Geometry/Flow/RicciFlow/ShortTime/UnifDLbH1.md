# UnifDLbH1

## Target

`dlbDiff_h1_unif` is the dimension-three class-first `H1` estimate for
`deTurckLieDLbCoeffField(gBase) - deTurckLieDLbCoeffField(g₀)`.  Its coefficient
function is selected from `(gBase, Λ, δ₀)` before the class metric, moving
metric, perturbation, and radius vary.

## Proof route

The proof takes the fixed-background cancellation before estimating:

1. the trace and fixed lowered-connection packages give the `wOmega`
   background difference in `H2`;
2. slot permutation of its covariant derivative gives the `wAlphaA` difference
   in `H1`;
3. the connection-action product gives the `wAlphaB` difference in `H1`;
4. the two arms assemble the full `wAlpha` and inserted-endomorphism
   differences;
5. `dlbDiff_jet_le` transports that bound to `DLb`.

Only class metric jets through order three and the perturbation `H2` jet are
used.  No `∇³P` term and no new analytic assumption is introduced.

## Status

The theorem and its local proof pass a warning-free focused Lean check.  Its
exact module export is fresh and the axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  Thus `dlbDiff_h1_unif` is fully verified
as the third closed leaf in the five-piece uniform tail packet.
