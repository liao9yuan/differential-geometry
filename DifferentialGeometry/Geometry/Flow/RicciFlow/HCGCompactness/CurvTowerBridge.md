# CurvTowerBridge

## 2026-07-25 verified statement and performance frontier

`curvNormSq_eq` is now stated at the canonical normalization boundary and its
module is focused- and exact-verified.  The declaration deliberately retains
one explicit `sorry`; therefore the theorem itself is 0% proved even though the
interface and its downstream Adapter consumer both check.

The exact obstruction is the dependent rank normalization between the static
`curvCovDeriv` tower (`k + 4`) and the PDE `nablaKRm04Field` tower (`4 + k`).
Three genuinely different proof routes were tested:

1. recursive whole-field equality with a `Fin (4 + k) ≃ Fin (k + 4)`
   reindex;
2. the same equality under reduced transparency and scalar evaluation;
3. an `HEq` route avoiding an explicit transported equality.

The first two spent minutes and gigabytes in whole tensor/Hom normalization;
the third failed dependent elimination on the arity equation.  Raising
heartbeats does not address the bottleneck.  The smallest remaining design
choice is either a cheap evaluated norm theorem at the tensor layer or explicit
approval to canonicalize the public static tower to the already canonical PDE
tower.  No consumer assumptions or wrapper black boxes were added.

The constants-first compact Riemann estimate is separately 100% complete.
`curvNormSq_eq` remains theorem-level 0%; `ham3_cgh_limit` remains theorem-level
0%; whole-HCG supporting machinery remains about 60%.

## 2026-07-25 static/PDE tower normalization

The intended public consumer statement is `curvNormSq_eq`: the squared norm
used by `HasSpacetimeCurvDerivBound` equals
`nablaKRm04NormSqIntrinsic` for a Ricci-flow solution.

The step identity `curvCovDerivStep = covStep` is definitional.  The initial
field-equality route through a recursive `Fin (4 + k) ≃ Fin (k + 4)` reindex
was abandoned: two focused attempts spent more than two minutes normalizing
the whole tensor-field equality, reproducing the known Hom/bundle whnf
performance wall.  The live proof instead uses an `HEq` normal form so the
dependent arity normalization is not stated as a whole-section equality.

Verification of the `HEq` version is pending the active shared build that is
currently refreshing the newly edited `BoundedGeometry` dependency.  Until
that focused check passes, `curvNormSq_eq` is 0% complete.  The compact
constants-first Riemann estimate is separately 100% complete; the Hamilton
`FlowDerivativeInput` assembly remains blocked at this normalization bridge.
`ham3_cgh_limit` remains theorem-level 0%, and whole HCG supporting machinery
remains about 60%.
