# DeTurckRemainderLowBaseH2Pair — status, findings, blockers

Lane A of the `(N)` endgame (recon brick **A1a**): the `H²` analogue of the
private `H¹` five-class capstone `selfLow_pair_h1`
(`DeTurckRemainderLowBaseLip.lean:9896`), then its path integral.

Statements follow the **corrected `UNIF_N_PRO_RULING` second-order arms at the
`a = 2` rung** (coordinator ruling; supersedes the first draft's
`rhs1_pair_h2` orientation, which was strictly stricter and unreachable here).

## Admissible modulus actually used

```
(B0 R · (1+A) · (D4 + D3 + D2 + N) + B1 R · A4 · (D3 + N))²
```

`A` = `J3`-size of either state, `A4` = `J4`-size of either state (linear
only), `D2/D3/D4` = `J2/J3/J4` differences, `N` = spectral `Hs2` difference.
Every difference slot carries a coefficient of `A`-degree `≤ 1` **or**
`A4`-degree `≤ 1`; `A4²`, `D4·A4` and `A`-degree `≥ 2` against a difference are
excluded.  Hypotheses added over the first draft: `J3 U ≤ A²`, `J4 T ≤ A4²`,
`J4 U ≤ A4²`, `J4 (T−U) ≤ D4²`.

## Status (`lake build` GREEN, 1 `sorry`)

**Class 2 is done (class-2 pass).**  `lieCovH2Pair` is proved sorry-free in the
new sibling `DeTurckRemainderLowBaseH2Cov.lean` (import order
`…Lip → …H2VB → …H2Cov → …H2Pair`); the `sorry` stub here was deleted and the
master's call site is unchanged, since the proved theorem carries the same name
in the same namespace.  See `DeTurckRemainderLowBaseH2Cov.md` for the route.
Only **class 1** (`goodH2Pair`) is still open.

**File split (class-3 pass).**  The whole `H²` jet-algebra layer that used to be
`private` here — `jetNn / jetSmul / jetAdd / sqAdd2 / jetMono`, the spectral
interpolation chain `prodOfParam / wgtAmgm / specInterp3 / jetSumSq / jetSumLe /
jetInterp3`, and the slot/reindex/product layer `sqTwo / quadFour / amixScalar /
slotL2 / slotH2 / reindexJet / reindexSub / trSub / trJet / appH2` — was **moved
verbatim** into the new sibling module `DeTurckRemainderLowBaseH2VB.lean`, which
also carries class 3.  Nothing is duplicated: this file imports it, the
declarations live in the same namespace under the same names, so every call site
here is unchanged.  Reason: adding class 3 here would have pushed the file past
the 3000-line limit, and the split keeps the class-3 iteration loop off the
900-line class-4 proof (VB build ≈ 150–200 s vs. H2Pair ≈ 450 s).

| declaration | status |
|---|---|
| jet algebra / interpolation / slot-reindex-product layer | **moved** to `DeTurckRemainderLowBaseH2VB.lean`, all proved |
| `selfParts` | proved — re-proof of Lip's private `selfLow_parts` from public `LowBaseInternal.selfLow_good`, `deTurckLieCoeffField_eq_covDerivArm_add_endoArm`, `tail_base_split` |
| `selfSubParts` | proved — five-class telescope equation, level-agnostic |
| `goodH2Pair` (class 1, `ricciGoodLow`) | **`sorry`** |
| `lieCovH2Pair` (class 2, Lie cov-deriv edge) | **proved** — in `DeTurckRemainderLowBaseH2Cov.lean`; see that file's `.md` |
| `vbH2Pair` (class 3, `lc0VB`) | **proved** — in `DeTurckRemainderLowBaseH2VB.lean`; see that file's `.md` |
| `amixScalar` | **proved** — the class-4 scalar re-pairing step, isolated (now in the VB module) |
| `amixHalfH2Pair` (class 4, one half) | **proved** |
| `amixH2Pair` (class 4, `lc0AMix`) | **proved** |
| `riemH2Pair` (class 5, `lc0Riem`) | **proved** from public `riem_pair_h2` |
| `selfLow_pair_h2` | proved *from the five class lemmas* |
| `c0Diff_h2_tame` | proved from it via `path_jetL2_le g 2 2 2` |

## Class 4 is now proved — and it *did* need `jetInterp3`

The earlier recipe recorded here ("every ingredient is public and **no
interpolation is required**") was **wrong**.  `lc0AMixHalfRF` is the five-factor
product `Tr₂ · Tr₄ · Ext³mcd · Tr₃ · Ext²mcd`, i.e. it carries **two**
`metricConnDiffLoweredCc` factors.  Since `mcd_h2_bdd` only gives
`(Bm R (1+A))`, the bounded chain of any telescope term is `(1+A)²`, and against
a difference that is `A`-degree `2` — outside the arm class.  There is no
`A`-free single-state `mcd` bound, so the class cannot land directly.

Resolution actually used (`amixHalfH2Pair`):

* Instantiate **both** `mcd` producers at `a := √(Cip·R·A4)` instead of `A`,
  which is legitimate because `jetInterp3` gives `J3 P ≤ Cip·(R·A4)` from
  `J2 P ≤ R²` and `J4 P ≤ A4²` (both hold for `P = s•T`, `|s| ≤ 1`).
* Then `(1+a)⁴ ≤ 8(1 + (Cip R A4)²)`, so the whole excess is a *single*
  `A4`-linear arm with an `R`-dependent coefficient: `B0 R := √(8·Bh R)`,
  `B1 R := √(8·Bh R)·Cip·R`, and `B1² A4² = 8 Bh (Cip R A4)²`.
* Feed `mcd_pair_h2` with `D2 := D3`, legitimate since
  `J2 (T−U) ≤ J3 (T−U) ≤ D3²` (`jetMono`).  This is the step that saves the
  proof: the producer's `B1·A·D2` slot would otherwise become the **forbidden**
  `A4·D2`; as `A4·D3` it is exactly the second admissible arm.
* Difference budget is therefore `u := D3² + N²` (not `D2² + N²` as at `H¹`),
  and the envelope is `pl2 := (1+a)²` (replacing the `H¹` `(1+A+A²)²`).

Modulus achieved: exactly the file's arm class
`(B0 R (1+A)(D4+D3+D2+N) + B1 R · A4 · (D3+N))²`.  `D2` and `D4` are only
absorbed as slack; the proof uses neither `A` nor `D2`/`D4` quantitatively.

## GAP 1 RESOLVED — `jetInterp3` is built and sorry-free

The coordinator's spectral route works.  Landed in this file, all proved:

| lemma | content |
|---|---|
| `wgtAmgm` | `w³ ≤ (t·w² + w⁴/t)/2` mode by mode on the Sobolev weight `w = 1+λ` |
| `specInterp3` | parametric spectral interpolation `‖·‖²_{Hs3} ≤ (t‖·‖²_{Hs2} + ‖·‖²_{Hs4}/t)/2`, via `tensorHs.norm_sq_eq_tsum` + termwise AM--GM + `Summable.tsum_le_tsum` |
| `prodOfParam` | Young ⇒ product: `(∀ t>0, X ≤ (t a² + b²/t)/2) → X ≤ a·b`, by `t := (b+δ)/(a+δ)` and `le_of_forall_pos_le_add` (no case split, no limits) |
| `jetSumSq` / `jetSumLe` | jet-sum ↔ `lowJetSq` transport (`Finset.sum_sq_le_sq_sum_of_nonneg`, `Finset.sum_mul_sq_le_sq_mul_sq` with `f = 1`) |
| **`jetInterp3`** | `∃ C ≥ 0, ∀ S R A4, 0≤R → 0≤A4 → J2 S ≤ R² → J4 S ≤ A4² → J3 S ≤ C·(R·A4)` |

Route: `lowJetSq 3 ≤ (Σ‖∇ʲ‖)² ≤ (C₃‖·‖_{Hs3})²` by `hsJet_le`; interpolate in
the spectral scale; come back with `hs_le_jet` at orders 2 and 4 plus the
jet-index Cauchy--Schwarz.  **No Gagliardo--Nirenberg leaf, no covariant
integration by parts, no `sorryAx`.**

Correction to the earlier report: the jet-sum Cauchy--Schwarz *route* is
unsound (`a0 = ε, a1 = a2 = 0, a3 = 1, a4 = 0` gives `J3² > J2·J4`), but the
inequality is recovered exactly on the *spectral* scale, where the weights
`(1+λ)^σ` make it a termwise AM--GM.  Constant `C` is per-`g`; uniformity in
the Λ-class is Lane E's job.

Canonical home for the whole block once it has a second consumer:
`Analysis/Spectral/Tensor/SobolevScale/IteratedCovGradHsJetBound.lean`.

## GAP 2 — class 1 still needs `aaKer_bdd_h2` sharpened first

`aaKer_bdd_h2` (Lip:8451) gives `J2 (ricciAAKer) ≤ B R·(1+A+A²)⁴`, i.e.
`H²`-**norm** `≲ A⁴`, while `ricciAAKer ~ Γ*Γ` is truly `~A²` (compare the
sharp `wXi_self_tame`: `J2 (wXi) ≤ (B R·A)²`).  Re-pairing the lossy bound with
`jetInterp3` yields `A⁴ ≤ (C R A4)²` — the forbidden `A4²`.  The rebuild is
mechanical (six blocks, `appRS_h2_h2_h2` against the two sharp connection
factors) and is recorded as sub-step 1 of the class-1 `sorry`.

## Blocker 3 — the `H¹` chain is `private`, and the `H²` pair lemmas do not exist

Every helper the `H¹` capstone consumes is `private` to `…LowBaseLip.lean` /
`…Action.lean` (`good_pair_h1`, `lieCov_pair_h1`, `vb_pair_h1`,
`amix_pair_h1`, `amixHalf_pair_h1`, `ricciAA_pair_h1`, `ricciDA_pair_h1`,
`aaKer_*`, `fourtrace_*`, `dagLow_*`, `covX_*`, `lcvPair_*`, `refold_*`,
`inputSymm_*`, `app_h*_mul_lip`, and even
`selfLow_parts`/`selfLow_sub_parts`).  There is no `open private` in this
toolchain (absent from Mathlib and Batteries here).

**Publicization was authorised but deliberately not performed**, because it is
not the binding constraint: what the four class proofs need at `H²` does not
exist at any visibility.  Only `H¹` pair versions exist.  Each class needs one
genuinely new `H²` pair lemma:

| class | missing `H²` lemma | nearest existing | rough size |
|---|---|---|---|
| 1 | `aaKer_pair_h2` **+ sharpened `aaKer_bdd_h2`** + `dagLow_pair_h2` | `aaKer_pair_h1` (Lip:8654), `dagLow_pair_h1` (Lip:8045) | ~600 |
| 2 | ~~`covX_bdd_h2`, `covX_pair_h2`~~ | **done** — `covXBddH2` / `covXPairH2` + `lieCovH2Pair` in `…H2Cov.lean`, ~1780 lines | — |
| 3 | ~~`vb_pair_h2`~~ | **done** — `vbH2Pair` in `…H2VB.lean`, ~730 lines | — |
| 4 | ~~`amixHalf_pair_h2`~~ | **done** — `amixHalfH2Pair`, ~940 lines | — |

Class 4 confirmed the estimate (~940 lines including the re-derived `H²`
slot/reindex/product layer) and confirmed that **no publicization was needed**:
the private Lip helpers `slot_h2_lip`, `reindex_jet_lip`, `reindex_sub_lip`,
`trPair_sub_lip`, `trPair_jet_lip`, `jet_mono_lip`, `app_h2_mul_lip` were all
re-derived locally in ~180 lines from the public `rfns_iteratedCovGrad_*` layer
and `appRS_h2_h2_h2`.  The same local layer is available to classes 1–3.

Minimal publicization list, **once those exist and are wanted from this file**
(all in `…LowBaseLip.lean` unless noted): `jet_mono_lip`, `app_h2_mul_lip`,
`fourtrace_bdd_h2`, `fourtrace_pair_h2`, `aaKer_bdd_h2`, `dagLow_bdd_h2`,
`inputSymm_h1` / `inputSymm_h2` (Action:7017), `refold_h2_lip`,
`wXi_self_tame`, `lcvPair_h2_bdd`.  Note `lcvPair_pair_h2` and
`lcvPair_h2_bdd` already have public C2Lip twins
(`LowBaseInternal.pairTrace_pair_h2` / `pairTrace_bdd_h2`), and a public
single-state `wXi` `H²` bound is recoverable from the public `wXi_sub_tame` at
`U := 0, gU := g` (`wXi g g g = 0`) — so the list may shrink further.

Public `H²` material usable now: `riem_pair_h2`,
`lieOmega_pair_h2 / _bdd_h2`, `lieArm2_pair_h2 / _bdd_h2`,
`metricCorr_pair_h3`, `metricCorr_sub_h2`; C1Lip `wXi_sub_h2 / wXi_sub_tame`,
`connSec_sub_tame`, `connIns_sub_tame`, `ricciKer_sub_tame`,
`mcd_pair_h2 / mcd_pair_h1 / mcd_h2_bdd`, `revSlot_pair_h2 / _bdd_h2`,
`fullSlot_bdd_h2`, `connSec_self_h2`, `ricci1_pair_h2`, `lie1_pair_h2`,
`rhs1_pair_h2`; C2Lip (`LowBaseInternal`) `trace{1,2,3,4}_pair_h2 / _h2_bdd`,
`pairTrace_pair_h2 / _bdd_h2`, `connLow_pair_h2 / _h2_bdd`,
`invCoeff_h2_lip`; Action `dagLow_h2_rf`, `connLow_h3_rf`.  Product engines:
`appRS_h2_h2_h2`, `appCc_h2_h2_h2`.

## Lean lessons banked

* `set … with h` folds the hypotheses too — the five class bounds fold
  automatically into the `Yᵢ`/`Zᵢ` names, making the ladder pure
  `linarith`-over-scalars.
* Never hand the 5-variable degree-2 ladder goal to `nlinarith`: it times out
  in `Linarith.SimplexAlgorithm.Gauss` at 3.2M heartbeats.  Split it — chain
  `sqAdd2 : 0≤a → 0≤b → a²+b² ≤ (a+b)²` four times for `Σ Zᵢ² ≤ (ΣZᵢ)²`, bound
  the nested ladder by `16·ΣZᵢ²` with `linarith` + three `sq_nonneg`, then
  `16·(ΣZᵢ)² = (4ΣZᵢ)²` by `ring`.
* Master needs `maxHeartbeats 6400000`, `synthInstance.maxHeartbeats 1000000`.
* `path_jetL2_le g 2 2 2` is the order-2 sibling of `c0Diff_tame`'s `… 2 2 1`;
  the `simpa only [lowJetSq, lowC0Diff, Φ, S, Nat.reduceAdd]` bridge is
  unchanged.
* With 7 size variables the hypothesis block repeats 7× across class lemmas +
  master + path integral; generating the file from a template is worth it
  (`scratchpad/h2pair/gen.py`, `gen2.py`).
* **Never finish a big tensor-telescope declaration with scalar tactics.**  The
  class-4 pass first failed with a `maxHeartbeats 3200000` timeout and then, at
  `12800000`, with `deep recursion was detected at 'interpreter'` — a hard
  crash of the whole `lake env lean` process (no per-declaration diagnostics).
  Cause: the ~80-hypothesis context of the telescope contains `lowJetSq`
  applied to nested `appCcRS`/`slotExtendIter` trees, and the closing
  `linarith` / `ring` / `nlinarith` steps parse *every* order hypothesis in
  context.  Fix: hoist the entire scalar endgame into a standalone lemma over
  plain reals (`amixScalar`) and end the big declaration with a single
  `exact`.  This dropped the telescope back under `6400000` heartbeats and
  removed the crash.  Same reflex for one-off inequalities: `sqTwo`,
  `quadFour` exist only to keep `nlinarith` out of the big context.
* The `H¹` sibling's `pl2 · u` bookkeeping *was* translated after all, with
  `pl2 := (1+a)²` and `u := D3² + N²`; only the `(1+A+A²)` envelope is dropped.
* `simp only [X]` reliably zeta-delta-unfolds tactic-`let` names (`S5b`, `Bh`,
  `B0`, …) in this toolchain, and `set … with h` + `rw [h]` reliably re-exposes
  the definition at the point of use — both patterns are load-bearing here.

## Verification

Targeted `lake build` of this module passes: exactly **one** `sorry` warning
(class 1, `goodH2Pair`), no errors, no other warnings.  Classes 2, 3, 4 and 5
are sorry-free, as are `selfLow_pair_h2` and `c0Diff_h2_tame` *conditional on*
that single remaining class sorry.  The siblings `…H2VB.lean` and
`…H2Cov.lean` both build fully sorry-free.
