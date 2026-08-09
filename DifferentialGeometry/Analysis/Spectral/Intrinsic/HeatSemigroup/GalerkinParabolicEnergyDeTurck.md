# `GalerkinParabolicEnergyDeTurck.lean` — notes

The supercritical (`4·finrank ℝ E + 10 ≤ a`) Galerkin energy layer for the
Ricci–DeTurck forcing: coordinate field, ODE existence, per-scale coercive split
and forcing closure.

## 2026-08-03, brick E3 — both private clones of the eigen-combination bridge deleted

Two byte-identical `private lemma`s stated
`finiteEigenComboHs g₀ S c σ = smoothCcToTensorHs g₀ σ (finiteEigenCombo g₀ S c)`:

* `finiteEigenComboHs_eq_smoothCcToTensorHs` — had **zero** uses in the file
  (dead code; the grep that appeared to find uses was matching the `gscr_`
  sibling as a substring);
* `gscr_finiteEigenComboHs_eq_smoothCcToTensorHs` — two uses, one inside
  `deTurckSobolevNHa2_diff_sobolevSplit_perScale'` and one inside the private
  `deTurckSobolevNHa2Symm_finiteEigenComboHs_eq`.

Both were deleted.  The two uses now call the public
`IntrinsicSpectral.finiteEigenComboHs_eq`, promoted to
`DeTurck/DeTurckRemainderDefs.lean` (see that file's note for why the plan's
target `Garding/EigenCombination.lean` was impossible).

The three `set_option`s (`backward.isDefEq.respectTransparency`,
`synthInstance.maxHeartbeats`, `maxHeartbeats`) that preceded the `gscr_` clone
were carried by that clone alone; deleting it left the identical block that
already preceded `deTurckSmoothRemainder_spectralCoercive_split'` untouched.  The
clone did not actually need them — the copy in the canonical home compiles with
no `set_option` at all.

No public statement in this file changed.

## Verification

**GREEN.**  Focused check passed after the deletions and the rewiring; the file
stays `sorry`-free.  One `unusedSectionVars` warning is reported for the private
`gscr_eigenIdxFinset_lambda_closed` (`[BoundarylessManifold I M]`).  It is
pre-existing, unrelated to this brick, and suppressed in real builds by
`lakefile.toml`'s `linter.unusedSectionVars = false`; left alone as out of scope.
