# RicciDeTurckLinearization

## Subtraction linearity

The canonical covariant slot-permutation layer now exposes
`domDomCongr_sub`: applying `domDomCongrSection` to a section difference is the
difference of the two permuted sections.  The proof lifts the fibrewise
multilinear-map subtraction identity through the existing `unitModel`
extensionality bridge.

This removes the need for another consumer-local subtraction wrapper in the
class-first `DLb` estimate.  Focused and exported-module verification remain
green.  No mathematical frontier or additional axiom was introduced.
