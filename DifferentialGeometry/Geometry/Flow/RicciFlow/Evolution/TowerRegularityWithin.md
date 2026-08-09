# TowerRegularityWithin

## Closed-edge component-tower engine

`iterRmComp_joint` is the within-set counterpart of the existing
pointwise tower regularity theorem. It propagates joint smoothness on an
arbitrary time set times an open spatial frame domain through every level of
`iteratedRmComp`.

The proof reuses the generic spatial exterior-derivative-within lemma from
`Bundle/PartialMfderiv/Basic`; no curvature-specific coordinate expansion is
introduced here.

Status: the proof is written. Focused verification is currently blocked before
elaboration by concurrently missing upstream `.olean` artifacts in the existing
tensor-nabla import chain; no theorem-level diagnostic has been produced.
