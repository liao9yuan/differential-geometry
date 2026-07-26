# Tensor0SMetricCongr.lean — slot-reindexing invariance of `inner0S`

Status: **VERIFIED GREEN, 0 sorry, axiom-clean** (both declarations on exactly
`[propext, Classical.choice, Quot.sound]`).  Focused check and the targeted module build
both pass; no linter warnings.

## Why this file exists

`Tensor/RSTensor/NormSqProduct.lean:94` already had `normSq0S_domDomCongr` (the squared
Frobenius norm is invariant under a slot reindexing `Fin s ≃ Fin s'`).  There was **no**
bilinear companion: a tree-wide search for `inner0S` together with `domDomCongr` returned
zero hits.  Both `ForwardUniqueRateLe.md` (K4's owed-items list) and the K1C-b framing
named `inner0S_domDomCongr` as the missing canonical-layer producer.

## Contents

* `inner0S_identity_eq_sum` — in an orthonormal basis, `⟪A,B⟫ = Σ_slots A_slots · B_slots`.
  This is the bilinear form of `normSq0S_identity_eq_sum_sq`
  (`Tensor0SRiemannian/Comparison.lean:221`); proved from `inner0S_eq_coord` +
  `coordInner0S_identity_eq_sum` exactly as the norm version is.
* `inner0S_domDomCongr` — `⟪domDomCongr e A, domDomCongr e B⟫ = ⟪A,B⟫`, same hypothesis
  shape as `normSq0S_domDomCongr` (basis + `MetricInverseInBasis_gen … identityInvMetric`).

## Design decisions

* **Direct route, not polarisation.**  The mission allowed a polarisation corollary of
  `normSq0S_domDomCongr`.  The direct mirror is strictly better here: polarisation would
  have forced importing `NormSqProduct.lean`, whose section variable block carries
  `[IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I (∞+1) M] [T2Space M]` — all
  auto-included into the signature.  Going through `Tensor0SRiemannian/Comparison.lean`
  instead keeps the file on the minimal `[IsManifold I ∞ M]`, matching the project's
  weakest-assumptions rule.
* Stated for `SmoothMetric_gen` (not `SmoothRiemannianMetric`) so that no positivity /
  ON-frame-existence is needed; the caller supplies the orthonormal witness, exactly as
  `normSq0S_domDomCongr` does.  `MetricInverseInBasis` and `MetricInverseInBasis_gen` are
  the same `def` in two files, and `exact`/application-level defeq crosses them freely
  (`Comparison.lean` already relies on this when it feeds a `_gen` witness to
  `normSq0S_eq_coord`, which asks for the non-`_gen` one).

## Lean lesson (cost me one iteration)

`rw [Tensor0SSpace.domDomCongr_apply]` **failed** ("did not find an occurrence of the
pattern") on a goal that visibly contained the pattern, in a context where the identical
`rw` succeeds inside `normSq0S_domDomCongr`.  This is the known `Tensor0SSpace`
FunLike-coercion trap (`Tensor0SSpace` is a non-reducible `def`, so the coercion instance
in the lemma and in the goal are defeq but not syntactically equal).  Since
`domDomCongr_apply` is `rfl`, the fix is simply to finish with `rfl` instead of `rw`.
General rule confirmed again: **on `Tensor0SSpace` fiber algebra, prefer `rfl` / term-form
`have h := lemma …` / `calc` over `rw`.**

## Follow-up (not done here, deliberately)

`domDomCongr_sub` (slot reindexing commutes with `-`) was needed downstream and currently
lives in `Evolution/ForwardUniqueRatePro.lean`.  Its canonical home is
`Tensor/RSTensor/Defs.lean` next to `Tensor0SSpace.domDomCongr_apply`; it was not placed
there because that file was outside this brick's claim.
