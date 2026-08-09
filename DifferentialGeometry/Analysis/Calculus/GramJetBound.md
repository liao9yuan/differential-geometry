# GramJetBound

## Role

`gramBilinear` is the fixed analytic operation that turns two linear maps into
their pointwise Gram bilinear form. `gram_jet_le` transfers all-order
Fréchet-derivative bounds for a fixed-space linear-map field to its Gram field.

For H6 this closes the analytic last step after intrinsic Jacobi endpoint jets
have been transported to a fixed Hilbert space. It does not prove those Jacobi
jet bounds and introduces no geometric or compactness assumption.

## Status

Source implementation is focused-green with no diagnostics.

## Progress

- `gram_jet_le`: implemented and focused-verified.
- H6 all-order metric-jet theorem: 0%; dedicated machinery approximately 37%.
- Native H6 producer machinery overall: approximately 55%.
