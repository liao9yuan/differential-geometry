# UnifMorreyTwo

## Purpose

`UnifMorreyTwo.lean` packages the rank-two class Morrey constant needed by the
finite-`H²` realization route.  It is the first non-cyclic HCG layer above both
`UnifJetTowerMatch` and the narrow `UnifReverseJetTwo` producer.

## Implemented interface (2026-08-05)

- `morreyTwoC gBase Λ` fixes the order-two fibre-Morrey constant from the
  background metric, the class parameter, and the model dimension.  It does
  not depend on the individual class metric.
- `morreyTwoC_spec` proves nonnegativity and the uniform rank-two Morrey bound.
  Its variable-metric hypotheses are exactly `Λ`-equivalence plus separate
  forward order-one and order-two metric-jet bounds.
- The reverse order-one and order-two jets are supplied by `reverseJetPack`;
  the Morrey estimate itself is reused from `fibreMorrey_unif_class`.

## Verification

The first focused check failed because the new module omitted the ambient
finite-dimensional/compact-manifold instances and because the broad
`UnifDeTurckRHSOne` compiled artifact predated `reverseJetPack`.  The structural
instances and local nonnegativity reduction are repaired, and the consumer now
imports the extracted narrow producer.  After that producer passed focused
verification and its compiled-artifact refresh, this module's focused
one-thread check and direct targeted module refresh also passed under the
campaign memory guard.

## Project position

This producer is dedicated infrastructure for the finite-`H²` realization
package.  That downstream package and the final uniform-existence theorem are
not proved here and remain at 0%; this Morrey producer itself is now
implemented and focused-verification complete.
