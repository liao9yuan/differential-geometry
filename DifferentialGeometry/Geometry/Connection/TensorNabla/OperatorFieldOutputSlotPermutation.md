# OperatorFieldOutputSlotPermutation

## Mathematical conclusion

The generic mixed-tensor output-slot permutation API now lives at the
connection/operator-field layer rather than inside Sobolev estimate files.
It provides the fibre operation `rsDomDomCongr`, its model and evaluation
read-offs, smoothness of the permuted operator field, and the packaged
`rsDomDomCongrSection`.

The public declaration names and statements are the existing API.  Their
implementations were moved from `OperatorFieldFibreNormJet.lean` and
`MetricArmCoeffJetTower.lean`; no parallel hierarchy was introduced.

## Verification

Focused verification passed without warnings.  The explicitly named module
refresh also passed and compiled only this target; replayed dependency
warnings were pre-existing.

The module has no `sorry` or `whnf`.  Its imports are restricted to smooth
section definitions, the pointwise Hom-section smoothness bridge, and
multilinear basis coordinates.
