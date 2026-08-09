# DeTurckRealizedSolutionFamily

## Layering note

The zero-section fibre-smallness lemmas now live in
`Analysis/Spectral/Intrinsic/DeTurck/LowRegBaseForce.lean`.  This file imports
that lower module, so its existing consumers retain the same public theorem
names without keeping low-level coefficient facts in the final realization
layer.

Focused verification passed after the import-only refactor.  The declaration
around the smooth-metric extensionality helper now explicitly omits unused
ambient instances, so the edited file has no new linter warning.
