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

## Status (focused check GREEN, five classes complete)

**Class 1 is now closed.**  `goodH2Pair` is proved without placeholders by a
sharp six-block `ricciAAKer` estimate, an inverse-slot H² factorization, the
AA/DA pair estimates, third-jet interpolation, and the bounded input
symmetrizer.  Its real focused check is GREEN.  Together with the sibling
class-2 and class-3 proofs, the five-class H² capstone is now **5/5**.

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
| `goodH2Pair` (class 1, `ricciGoodLow`) | **proved** — sharp AA + DA re-pairing |
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

## Class 1 resolved — sharp AA and DA re-pairing

The lossy all-order `aaKer_bdd_h2` wrapper was not used.  The proof rebuilds
the six `ricciAAKer` blocks directly with `appRS_h2_h2_h2`, giving the sharp
quadratic connection envelope needed before interpolation.  The remaining
pieces are then assembled in this order:

* `fullPairH2` uses the exact inverse-slot factorization and has no state-`A`
  passenger;
* `ricciAAPairH2` controls the AA contribution with the sharp six-block bound;
* `ricciDAPairH2` interpolates the state `J3` size by
  `sqrt (C · R · A4)`, so the high arm is `A4 · D3`, never `A4²`;
* `inputSymmH2` transfers the combined unsymmetrized estimate to
  `ricciGoodLow`.

No private H¹ declaration was publicized.  The H² lemmas were rebuilt locally
from the public slot, reindex, trace, connection, and product APIs.  This closes
the only remaining five-class dependency of `selfLow_pair_h2` and hence makes
`c0Diff_h2_tame` unconditional.

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

The final real focused check of this module passes with no errors or warnings.
The source contains no `sorry`, `admit`, `axiom`, or `whnf`.  All five class
lemmas, `selfLow_pair_h2`, and `c0Diff_h2_tame` are now unconditional.  The
siblings `…H2VB.lean` and `…H2Cov.lean` remain fully checked as recorded in
their own ledgers.

Project accounting after this brick: `ricci_flow_unif_existence` itself remains
unstated here and still has its one endpoint placeholder elsewhere, so the
theorem is **0%**.  Its dedicated machinery is approximately **76%**.  The
whole HCG compactness project remains in the low single-digit percentage range.
The next low-regularity brick is the D₄-free `a1Lo` pair estimate, which should
simultaneously discharge the `hfLo` bridge, the `lowA1` restatement, and the
M-witness consumer.

## Local H3 coefficient pair (2026-07-31)

The fixed-order continuity lane is now separated from the historical
H4-affine compatibility estimate.  The new public theorem `c0_pair_h3` proves
the radial zero-coefficient pair bound

`J2(C0(T)-C0(U)) <= (B R (1+A^2) (D3+D2+N))^2`

on a common small spectral H2 ball.  It assumes only state H3 bounds and
H2/H3 difference bounds; there is no state H4 or difference D4 input.

The proof specializes each already-verified factorwise telescope at the actual
H3 radius before estimating.  The private chain is
`ricciAA_h3_pair` / `ricciDA_h3_pair` / `good_h3_pair`, then
`lieCov_h3_pair`, `vb_h3_pair`, `amixHalf_h3_pair` / `amix_h3_pair`, and
`riem_h3_pair`, followed by `selfLow_h3_pair` and `path_jetL2_le`.
This closes the missing C0 half of the local H3-to-H2 coefficient continuity
argument.  It does not by itself prove the separate affine-in-H3 time-growth
bound needed for the final Nemytskii/MemLp consumer.

Persistent LSP elaboration is green for the complete theorem chain.  A fresh,
standalone focused module verification also passes.  With the persistent LSP
server stopped, the cold check used roughly 6.3 GB of private committed memory;
the earlier 11--12 GB figure was therefore persistent-worker accumulation, not
the cold cost of this source alone.  The named module refresh also passes, so
the public `c0_pair_h3` export is current for downstream consumers.  The next
consumer brick is to combine `c0_pair_h3` with the existing D4-free C1 H2 pair
and extend the same smooth-core first-order action continuously from H3 to H2.
