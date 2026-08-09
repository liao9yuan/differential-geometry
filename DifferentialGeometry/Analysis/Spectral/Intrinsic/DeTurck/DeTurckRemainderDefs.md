# `DeTurckRemainderDefs.lean` — notes

Shared-definition module: `deTurckSmoothRemainder` and `smoothCcToTensorHs`, kept
upstream of the tame-Lipschitz tower.

## 2026-08-03, brick E3 — `finiteEigenComboHs_eq` promoted here

`F6_ESTIMATE_RECON.md` §7.6 row E3 asked for the eigen-combination bridge
`finiteEigenComboHs g₀ F c σ = smoothCcToTensorHs g₀ σ (finiteEigenCombo g₀ F c)`
to be promoted out of two `private` clones in
`HeatSemigroup/GalerkinParabolicEnergyDeTurck.lean` and into
`Garding/EigenCombination.lean`.

**That target file is impossible.**  `smoothCcToTensorHs` is defined *here*, and
this module **imports** `Garding.EigenCombination` — the dependency runs the other
way, so the bridge cannot be stated in `EigenCombination.lean`.  The lowest module
where both sides of the equation are in scope is this one, which is also the
canonical home of the right-hand side, so the lemma landed here instead.

Public name is `finiteEigenComboHs_eq` (20 letters) rather than the plan's
`finiteEigenComboHs_eq_smoothCcToTensorHs` (36), to stay inside the project name
budget; the LHS head symbol still leads the name, matching the sibling
`finiteEigenComboHs_coeff_eq` in `EigenCombination.lean`.

Proof is the four-line one the clones already used (`tensorHs.ext`, `funext`, then
`finiteEigenComboHs_coeff_eq` / `smoothCcToTensorHs_coeff` / `←
SmoothCcTensor.toL2_apply`).  No `set_option` and no `open scoped Classical` was
needed here, although one clone carried each.

## Verification

**GREEN.**  Focused check passed; targeted module build passed (0 errors).  The
module stays `sorry`-free.  Note that this is a low module: refreshing its olean
makes every downstream olean stale for the next full build.
