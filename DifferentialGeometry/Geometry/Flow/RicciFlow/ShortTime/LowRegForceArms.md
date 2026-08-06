# `LowRegForceArms.lean` — Brick B of the rung-3 campaign

Companion note for `LowRegForceArms.lean` (created 2026-08-05, executor report
№160 in `UNIF_EXISTENCE_PLAN5.md`).

## What this file is

The forcing-realization layer between the order-one Galerkin ODE
(`LowRegGalerkinSol.lean`) and the per-index ladder estimates
(`LowRegA2PerIndex.lean` / `LowRegA1PerIndex.lean`).  The ODE reports its
forcing as `galTameForce`, i.e. the *dense* nonlinearity `lowregNfun` evaluated
at the retracted spectral state `galTameStateC`; the ladder estimates speak
about covariant jets of the low-base actions `A.a2 T`, `A.a1 T` of a genuine
smooth tensor `T`.  This module writes the first as the second.

## Declarations (all public, all `[propext, Classical.choice, Quot.sound]`)

| name | content |
|---|---|
| `galCoreRep` | `(min 1 (R/‖·‖)) • finiteEigenCombo g₀ S c` — the named smooth representative |
| `galCoreRep_eq` | its spectral embedding is `galTameStateC g₀ 1 R S c` |
| `galCoreRep_ball` | the representative stays in the lower `H²` ball of radius `R` |
| `galState_core` | the retracted Galerkin state is a point of `smoothCore g₀ R` |
| `galRepFib` | fibre certificate at `symmS g₀ (galCoreRep …)` (the `hδg` slot) |
| `lowregFibZero` | fibre certificate at the zero tensor (the `hδZ` slot) |
| `galN_eval` | `lowRegN` at the Galerkin state `= deTurckSmoothN g₀ g₀ 1 (symmS g₀ (galCoreRep …))` |
| `galArmId` | `𝒩(state) − 𝒩(0) = smoothCcToTensorHs g₀ 1 (A.a2 T + A.a1 T)`, `A = lowBaseData g₀ g₀ T` |
| `galArmCap` | `∃ Cδ ≥ 0`, mode-set- and level-free, capping `A.C2`'s fibre norm — the `hfib` binder of `a2PerIdxLin` |
| `galForceArm` | the ODE forcing coordinate as seed coefficient plus arm coefficient, at the `lowregNfun` / six-number level |

Statement discipline: every lemma takes `IsLowSolve`-grade inputs directly
(`δ < 1`, `0 ≤ δ`, `δ ≤ 1/3`, the realization bound `hreal`, continuity of
`coreN` at the *same* realization).  `lowreg_proj_tendsto` is deliberately NOT
used — its export discards those fields.  Constants and certificates precede the
trajectory data `(S, c)`, so a consumer destructures once and applies per time.
The background is pinned to `g₀` itself (self-background), matching `IsLowSolve`,
`lowData_split g₀ g₀` and `a2PerIdxLin`'s `lowBaseData g g`.

## Reused, not rebuilt

Everything below already existed; nothing was ported, copied or duplicated.

* `galTameStateC`, `galTameStateC_mem`, `galTameForce_apply`, `galLowView`
  (`HeatSemigroup/GalerkinTameSol.lean`) — the retracted state and the forcing
  coordinate.
* `finiteEigenCombo` (`Garding/EigenCombination.lean`) and
  `finiteEigenComboHs_eq` (`DeTurck/DeTurckRemainderDefs.lean`) — the smooth
  eigen-combination and the bridge to its spectral packaging.
* `smoothCcToTensorHs_smul` (`DeTurck/SobolevNonlinearityExistence.lean`) — the
  retraction scalar passes through the embedding.
* `symm_h2_of_state`, `lowRegN_on_smooth` (`ShortTime/LowRegSmoothBridge.lean`)
  — the evaluation layer; `lowRegSeedMass`, landed in Brick A, is the
  `state = 0` instance of exactly the same pattern and was used as the template.
* `smoothCcToTensorHs_zero`, `nZero_eq_static`, `deTurckSmoothN_zero`
  (`ShortTime/UnifNZeroBound.lean`) — **the seed handle**.  See the
  over-count note below.
* `deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub`
  (`DeTurck/SobolevNonlinearityExistence.lean`) and `lowData_split`
  (`DeTurck/DeTurckRemainderLowBaseAction.lean`, read-only other-lane file —
  consumed, not edited) — the arm split with its `C2` cap.
* `DeTurckRemainderTameLipschitz.ccTensorBilin_symmS_symm`
  (`DeTurck/DeTurckRemainderTameLipschitz/Base.lean`) — the unconditional
  symmetry binder `hT` of `lowData_split` / `a2PerIdxLin` / `a1PerIdxLin`.
* `n_diff_h1_rung` (`DeTurck/LowRegDissipRung.lean`) — used only as the
  *pattern* for consuming `lowData_split` at the self-background.

## Over-count avoided: `symmS 0` was never needed

The natural-looking obstruction was that `lowRegN … ⟨0, …⟩` evaluates (through
`coreN`) at `symmS g₀ (coreRep …)`, whereas `lowData_split`'s seed is the
*literal* zero tensor — apparently forcing a new `symmS_zero` lemma in the
upstream `CovGrad/RicciDeTurckSectionDifference.lean` (an expensive edit).  It
is unnecessary: `nZero_eq_static` (`UnifNZeroBound.lean:249`) already crosses
that gap and lands on `smoothCcToTensorHs g₀ 1 (deTurckRHSSection g₀ g₀)`, and
`deTurckSmoothN_zero` (:229) turns that back into `deTurckSmoothN g₀ g₀ 1 0`.
Likewise `smoothCcToTensorHs_zero` (:169) is public, so the `hzero_embed`
computation open-coded inside `lowRegSeedMass` did not need to be re-derived.
Grep `UnifNZeroBound.lean` before inventing anything about the zero state.

## Design decisions

* **New file, not an extension of `LowRegSmoothBridge.lean`.**  The bridge file
  is small (≈277 lines) and would have stayed well under the 3000-line limit,
  but the new content needs `GalerkinTameSol`, `UnifNZeroBound` and
  `DeTurckRemainderLowBaseAction` in its import closure.  Adding those to
  `LowRegSmoothBridge` would push them onto its three existing consumers
  (`LowRegBgAffine`, `LowRegLiftAffine`, `LowRegRHSSymm`) for no benefit.
* **General `lowRegN` level + one `lowregNfun` specialization.**  `galN_eval`,
  `galArmId`, `galArmCap` are stated at an arbitrary radius `R` with `hreal` at
  `R` (weakest hypotheses); `galForceArm` is the six-number specialization at
  `R := lowregStateRad Ctop B1 ρ P`, `hreal := lowregRealRad … hP.le hreal`,
  because that is the term `lowregGalSol`'s ODE conclusion mentions verbatim and
  `rw` needs a syntactic match there.  This mirrors the existing
  `nZero_unif` / `nZero_lowregNfun` pair.
* **`hδ : δ < 1` in the `lowBaseData` slot.**  The per-index estimates write
  `lt_of_le_of_lt hδ3 (by norm_num)` in the same slot.  The two terms are
  definitionally equal (proof irrelevance); this was checked with a throwaway
  `rfl` `example` against `lowBaseData … h … = lowBaseData … h' …`, which
  elaborated, and the probe was then removed.  A consumer therefore needs no
  transport lemma; the module docstring records this.
* **The `C2` cap is stated at `riemannianFiberNormSq g₀ (2 + 2) 2`**, matching
  `a2PerIdxLin`'s `hfib` binder rather than `lowData_split`'s `4`; the two agree
  by nat-literal reduction, and `exact` bridges them.
* **`open scoped Classical in`** is required before `galForceArm`: its statement
  contains `if i ∈ S then … else 0` with no `DecidableEq` on `TensorEigenIdx`.
  Same idiom as `galTameForce` itself.

## Verification

Focused check green on `LowRegForceArms.lean` and `ScratchIdentCensus.lean`;
targeted builds green for both modules.  Census: all ten new declarations report
`[propext, Classical.choice, Quot.sound]`, with zero occurrences of `sorryAx` in
the whole census output.  No `sorry` anywhere in the file.  No new
`maxHeartbeats`.  No read-only other-lane file was edited.

## What Brick C still has to do

Everything mathematical.  This file moves no estimate: it is pure translation.
Brick C owns the closure statement at `k = 3`, `q = 2`, the cross-scale pairing,
the `L¹_t` Grönwall with the two interface variants (`two_mul_sum_ladder_le`
with an additive `+γ`; the Grönwall bound with a `seed²/4 + c₀` slot), and the
adapter-H threading.  The entry points it should `obtain` once, outside `∀ N`
and `∀ t`, are `galArmCap` (the `hfib` constant) and `lowRegSeedMass` (the seed
mass); `galForceArm` is then applied per `(N, t)` at
`S := eigenIdxFinset g₀ N`, `c := U N t`.

## 2026-08-05 — constant-one spectral realization bridge

`galRepHs_le` now reads the Sobolev norm of `symmS (galCoreRep R F c)` directly
from its finite weighted coefficient mass with constant one, for every real
order.  This exact coefficient is load-bearing: the generic higher-rung top
coefficient remains the stored `κ`, rather than acquiring a rung-dependent
realization norm.

The higher-rung consumer has landed in `LowRegHigherRung.lean`.  Focused
verification and the direct module refresh passed.  The bridge is per metric;
it does not assert uniformity over the `(N)` metric class.
