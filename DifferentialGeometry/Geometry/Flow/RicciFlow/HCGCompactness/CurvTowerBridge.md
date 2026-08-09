# CurvTowerBridge

## 2026-07-26 scalar arity bridge complete

`curvNormSq_eq` is proved without assumptions beyond the existing solution and
manifold context.  Focused verification and the exact module build passed, and
`CurvTowerBridge.lean` now contains no `sorry`.

The obstruction was elaboration rather than mathematics.  Induction on the
whole dependent tensor-field equality between ranks `k + 4` and `4 + k`
reproduced the Hom/bundle normalization wall even after adding the cheap
`curvCovDeriv_succ` projection.  Explicit whole-field `rw` and `calc` variants
were therefore discarded.

The successful normal form is scalar:

1. `curvCovDeriv_succ` exposes the dependent recursion without unfolding it.
2. `curvEquiv` recursively extends the base-four slot equivalence.
3. `curv_apply_iterCov` proves equality only after evaluating at a point and a
   complete slot tuple.  Its local field equality is reconstructed from the
   scalar induction hypothesis by extensionality, so the induction motive
   never contains a whole dependent Hom equality.
4. `curvNormSq_eq` reconstructs only the single fiber equality needed by the
   consumer, then applies `normSq0S_domDomCongr` and the existing
   `nablaKRm_eq_iterCov`.

This closes the only explicit proof dependency of the Hamilton
`source_deriv`/`FlowDerivativeInput` assembly.  `curvNormSq_eq` is theorem-level
100%; the constants-first compact Riemann estimate remains 100%;
`ham3_cgh_limit` remains theorem-level 0%; whole-HCG supporting machinery
remains about 60%.
