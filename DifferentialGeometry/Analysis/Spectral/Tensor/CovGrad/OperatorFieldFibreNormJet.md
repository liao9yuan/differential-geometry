# OperatorFieldFibreNormJet

## Current change

The exact fibre definitions `rsDomDomCongr`,
`toModel_rsDomDomCongr_apply`, and `rsDomDomCongr_apply_eval` were moved to
`OperatorFieldOutputSlotPermutation.lean`.  This file imports that canonical
module and retains the fibre-norm and covariant-jet estimates built on top of
the API.

## Verification

The extracted lower module is focused-green.  This estimate file was not
rechecked because its new import artifact was restored only after a shared
cache chain appeared; no broad or transitive refresh was attempted.
