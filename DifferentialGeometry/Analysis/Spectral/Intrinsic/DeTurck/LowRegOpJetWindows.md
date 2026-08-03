# `LowRegOpJetWindows.lean` — TK2 + TK3 of ruling No. 104

**Status: GREEN.**  All **four** summands of `topKernel_eq` have their all-order
jet windows, and the `IsPathPert` discharge along the radial path is proved.
Zero `sorry`, zero `axiom`, zero `maxHeartbeats` bump, no linter warnings.
1409 lines, 42 declarations.  Focused check clean; targeted module builds of
this module and of `…DeTurck.LowRegLadderRung` clean; axiom census clean
(`propext`, `Classical.choice`, `Quot.sound`) on every endpoint probed,
including the downstream `topKer_jet`, `c2_jet_tower` and `a2_ladder`.

## What this file is

`topKer_jet` (`LowRegC2JetTower.lean:196`) needs, for **every** order `i` and
uniformly in the path parameter `s ∈ [0,1]`, an affine covariant `L2` jet
window for each summand of `topKernel_eq`.  The tree stocked those only at
fixed order two, as `private` helpers inside the other-lane-claimed
`DeTurckRemainderLowBaseAction.lean`.  This file supplies the order-generic
members, ball-free, and (TK3) the moving-metric branch and the path discharge.

## The organizing device, and why it is the whole content

```lean
def IsMoserWin g T A S X : Prop :=
  0 ≤ S ∧ (∀ x, rfns g r c x (X.toSection x) ≤ S ^ 2) ∧
          (∀ n, lowJetSq g n X ≤ A n * (1 + lowJetSq g n T))
```

Carrying the pointwise (`L∞`) bound *alongside* the jet bound is what makes the
brick work.  The fixed-order-two route could not stay affine: `ricciTop_h2`
bounds a product by `C · jet Φ · jet W` and then has to assume
`lowJetSq g 2 P ≤ 1` — an `H2` ball — to linearize.  Ruling No. 104 forbids the
ball.  With the pointwise slot present, `appRS_hn_sup` (TK1) multiplies each
arm's `L∞` bound by the *other* arm's `L2` jet, so a product of two windows is
again a window, with **no order gate and no ball**.  Affinity is preserved by
construction, and every closure lemma below is three lines of bookkeeping.

`IsPathPert g g₁ P T δ₀` bundles the hypothesis side: `g₁ = g + P`, `P`
`δ₀`-fibre-small with its pointwise certificate, and `P` jet-dominated by `T`.
For the radial path `g₁ = realizedFam g T 0 hδ hδZ s`,
`P = convexPerturbation g T 0 s`, this holds for every `s ∈ [0,1]` with the
*same* `δ₀` — which is exactly where the `s`-uniformity comes from: no constant
produced in this file mentions `s`.

## The `T`-uniformity refactor (TK3, load-bearing)

TK2 stated every family window as `theorem … (g) (T) … : ∃ A S, …`, i.e. with
the state bound **before** the existential.  `topKer_jet` produces its `Kk`
**before** `T` (its consumer `c2_jet_tower` is written that way, and the whole
point of the ladder is a state-uniform constant), so `∀ T, ∃ A` is not enough.

The constants were already morally `T`-free — `moserWin_const` bounds a
background object, `moserWin_appRS`'s `C` comes from `appRS_hn_sup g p r c`,
`moserWin_self`'s envelope is `1`, `moserWin_sharp`'s comes from the
radius-free engine — so TK3 hoisted `T` inside the `∃` in twelve statements
(`moserWin_const`, `_appRS`, `_sharp`, `_fullSlot`, `_gInvDiff`, `_connLow`,
`_dagTop`, `_daWeight`, `_curvMono`, `_daTrans`, `_ricciTop`, `_phiDev`).  Each
proof needed only `intro T` moved past `refine ⟨…⟩` and the `T` argument
dropped from the corresponding calls; the whole refactor checked clean on the
first pass.  **Lesson: when a window predicate mentions the state, decide the
quantifier order from the *final* consumer, not from the local statement.**

The `hTsup` hypotheses (`_daWeight`, `_daTrans`, `_ricciTop`) moved inside the
`∀ T` as an antecedent, which is where they belong.

## Landed (all `w = 0`, i.e. order `n` on the left costs order `n` of `T`)

Closure lemmas: `moserWin_appRS` (`:328`, the Moser product step),
`moserWin_slot` (`:390`), `moserWin_dom` (`:419`), `moserWin_reindex` (`:461`),
`moserWin_rsperm` (`:481`), `moserWin_add` (`:200`), `moserWin_sub` (`:232`),
`moserWin_smul` (`:263`), `moserWin_const` (`:175`), `moserWin_endoIns`
(`:696`), `moserWin_self` (`:538`).

Family windows, dependency order:

| decl | line | replaces (fixed order 2) |
|---|---|---|
| `moserWin_sharp` | 660 | `sharp_h2_low` |
| `moserWin_fullSlot` | 736 | `full_slot_h2_low` |
| `moserWin_gInvSlot` | 811 | (new: the common core, arbitrary slot) |
| `moserWin_gInvDiff` | 850 | `inv_coeff_h2` (was ball-based) |
| `moserWin_connLow` | 874 | `connLow_h2_low` |
| **`moserWin_dagTop`** | 910 | inline `hDag` inside `ricciTop_h2` |
| `moserWin_daWeight` | 939 | inline `hWeight` inside `ricciTop_h2` |
| `moserWin_curvMono` | 966 | `curvMono_h2` |
| **`moserWin_daTrans`** | 1010 | inline `hTrans` inside `ricciTop_h2` |
| `moserWin_ricciTop` | 1039 | `ricciTop_h2` (ball-free now) |
| **`moserWin_phiDev`** | 1089 | `phi_dev_h2` (ball-free now) |

TK3's additions — the moving-metric branch and the path discharge:

| decl | line | content |
|---|---|---|
| `moserWin_symmS` | 589 | window for `symmS g T`, same constants as `T`'s |
| `moserWin_pureTr` | 1177 | window for `pureTrace g gm k`, via `pureTrace_split` |
| `moserWin_lieCovP` | 1201 | window for `lieCovPair g gm`, via `pairTrace_eq` |
| `moserWin_monoMov` | 1224 | moving-metric sibling of `moserWin_curvMono` |
| `pathPert_rad` | 1278 | `IsPathPert` along `s ↦ realizedFam g T 0 s` |
| **`moserWin_lieRef2`** | 1324 | the fourth summand of `topKernel_eq` |

### The `lieCovPair` route (TK3's one producer job)

`lieRefold2`'s monomials differ from `daTrans`'s only in that their pair
coefficient is taken at the *moving* metric.  The chain, all public, all
order-generic already:

```
lieCovPair g gm  =(pairTrace_eq)=  appCcRS g 6 4 2 (pureTrace g gm 2) (pureTrace g gm 4)
pureTrace g gm k =(pureTrace_split)= appCcRS g (k+2) (k+2) k (cometricDoubleTraceField g k)
                                       (slotInsertEndoCc g (k+1) (gInvDiffRaisedEndoField g gm))
                                     + cometricDoubleTraceField g k
```

so the only genuinely metric-dependent factor is `slotInsertEndoCc g (k+1)
(gInvDiffRaisedEndoField g gm)` — which is `moserWin_gInvDiff`'s own core at a
different slot.  TK3 therefore split `moserWin_gInvDiff` into
`moserWin_gInvSlot k` (the core) plus a three-line corollary at `k = 1`, and
`moserWin_lieCovP` is two `moserWin_appRS` steps and two `moserWin_const`s on
top of it.  **Fifteenth stocked wall**: nothing new was needed; the "moving
second metric" reduces to the same inverse-difference endomorphism that family
`dagTopOp` already goes through.

### The `lieRefold2` assembly

`deTurckLieCovDerivRefoldC2Family_eq_symmS_weight` gives

```
lieRefold2 g T hδ hδZ s = s • ∑ i : Fin 3, lieRefoldEps i • curvMono g gm (unit (symmS g T)) (lieRefoldQ i)
```

so: `moserWin_symmS` for the argument, `moserWin_monoMov` for each monomial,
`moserWin_smul` + `moserWin_mono` for the two scalars (`|εᵢ| ≤ 1`, `|s| ≤ 1`,
so both are absorbed and **no constant sees `s`**), `Fin.sum_univ_three` +
`moserWin_add` twice for the sum.

`moserWin_symmS` reuses `iteratedCovGrad_symmS_eq` and
`riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection` (both public,
both per-order): the symmetrization is a half-sum of `T` and a covariant slot
permutation of `T`, and the permutation is a fibre isometry, so `symmS g T`
inherits `T`'s window verbatim.  This does **not** need `T` symmetric.

### `pathPert_rad`, and where `s`-uniformity comes from

Along the radial path `P = convexPerturbation g T 0 s = s • T` (`cvxRad`), so
all four `IsPathPert` fields hold with the **same** `δ₀` for every `s ∈ [0,1]`:
the fibre bound is `convexPerturbation_gFibreOpBound_abs` with
`|1−s|δ + |s|δ = δ` (exactly `lieRefold2_cap`'s step), the tie is
`realizedFam_inner_of_mem ∘ Icc_subset_realizedSmallSet`, and both the
pointwise and the jet domination are `s² ≤ 1` after `riemannianFiberNormSq_smul`
/ `jetSmul`.  That is the whole content of "uniform in the path parameter".

## What was reused vs built

**Reused unchanged (public, already order-generic — this is most of the brick):**

* `sharpFlatEndoCc_lowOrder_jetL2_radiusFree` (`DeTurckVFJetRadiusFree.lean:428`).
  Its order cap `a` is a **free parameter** subject only to
  `2·finrank + 10 ≤ a`, and the conclusion is `∀ i ≤ a + 1`.  So instantiating
  `a := 2·finrank + 10 + n` gives order `n` for every `n` at no cost.  The two
  fixed-order privates `sharp_h2_low` / `sharp_h3_rf` are byte-identical
  invocations at `a := 2·finrank + 10`, differing only in the `2` vs `3`.  This
  is the fourteenth stocked wall.
* `appRS_hn_sup` (TK1, `AppCcRSJetMul.lean:83`) — the gate-free engine, used
  exactly as TK1's report instructed.
* `rfns_iteratedCovGrad_slotExtend_le`, `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo`,
  `rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr`,
  `rfns_iteratedCovGrad_reindexCoeffGen_eq`, `riemannianFiberNormSq_compRS_le_mul`,
  `normSq_le_integral_of_pointwise_fiberNormSq_le_rs` — all already per-order.
* `LowBaseInternal.curvMono_eq` (`…LowBaseAction.lean:8985`) — **public**.  The
  transparent two-trace product form.  The `private` `curvMono_pair` (`:6469`,
  ~190 lines of index work) has a public wrapper in the file's second
  `LowBaseInternal` block, together with the public `monoPerm`.  Finding this
  is what made family `daTrans` cheap instead of a 270-line copy.
* `traceHessianCoeff_sub_background_{perOrder_rfns,jetL2}_le_gInvDiffSlotCoeff_*`
  and the `ricciArmPrincipalCoeff` siblings
  (`RemainderCoeffL2JetMoser.lean:185,199,345,365`) — already order-generic.
* `phiMet_reindex` (`DeTurckTopCoeff.lean:78`),
  `gInvDiffSlotCoeff_eq_slotInsertEndoCc` (`MetricArmCoeffJetTower.lean:143`).

**Re-derived from public API** (each has 2–5 `private` copies elsewhere in the
tree; `DeTurckVFJetRadiusFree.lean:334` documents that "every sibling
re-derives them"):

* `sharpSlot0` (`:612`) — `sharpFlatEndoCc = slotInsertEndoCc 0 (fullRaisedEndoField)`.
* `raisedSelf` / `raisedDecomp` / `insAdd` (`:755`, `:764`, `:784`).
* `reindexSub` (`:1059`).
* `rfnsSymmS` (`:552`) — the per-order `symmS` contraction; a copy of the
  `private` `bdRfns_iCG_symmS_le` (`RiemannCoefficientPalatiniRefold.lean:4108`,
  and a byte-identical sibling in `DeTurckLieArm1CoeffL2JetBound.lean:1140`).
* `cvxRad` (`:1267`) — `convexPerturbation g T 0 s = s • T`.
* `jetNn`, `jetSub`, `jetMono`, `jetSmul`, `l2OfPt`, `jetOfPt` — the
  jet-algebra layer.  The originals (`jet_nonneg`, `jet_sub`, `jet_mono`,
  `slot_l2`) were **already order-generic in their bodies**; only `private`
  and, for the `_h2` wrappers, order-two in the statement.

**Genuinely new:** nothing about tensor calculus.  The new content is the
`IsMoserWin` packaging, the observation that it is closed under everything
`topKernel_eq` uses, and the quantifier order that makes the constants
state-uniform.

## Derivative offsets, and the budget

Every family window has `w = 0`.  `topKer_jet`'s budget is
`∑ j ∈ range (i + 2)` = `lowJetSq g (i+1) T`, i.e. `w = 1`.  **No family
overruns; every one has a full order of slack.**  This is a consequence of the
Moser route: the `L∞` factor is a constant, so no jet is ever spent on the
smallness input.  In the final assembly the slack is simply thrown away by one
`Finset.sum_le_sum_of_subset_of_nonneg`.

## The four summands of `topKernel_eq`, as consumed by `topKer_jet`

1. `lieRefold2 g T hδ hδZ s` — `moserWin_lieRef2`.
2. `deTurckPhiMetTotal g g_bg gm − deTurckPhiMetTotal g g_bg g` — `moserWin_phiDev`.
3. `(−2s) • ricciTop g gm T` — `moserWin_ricciTop` + `moserWin_smul`; the
   scalar costs `(−2s)² ≤ 4` and `|−2s| ≤ 2`, absorbed by `moserWin_mono`.
4. the path data itself — `pathPert_rad`.

Ruling No. 104's rejection of
`exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow` (the pre-existing
all-order `lieRefold2` producer, gated at `2·finrank+10 ≤ a`) stands: nothing
in the Moser route needs it, and reusing it would have re-gated the chain to
`a ≥ 16`.

## Lean lessons

* **`omit … in` must precede the docstring, not sit between it and the
  `theorem`.**  Putting it after a `/-- … -/` gives
  `unexpected token 'omit'; expected 'lemma'` at the *end column of the
  docstring line*, which reads like a docstring error and is not.
* **Opaque witnesses for `private` constants in a public definition's body.**
  `connLowOp`'s body mentions the `private` `koszulOp`, which cannot be named
  downstream.  `obtain ⟨Q, Kop, hcl⟩ : ∃ Q Kop, ∀ g₁, connLowOp g g₁ = … :=
  ⟨_, _, fun _ => rfl⟩` extracts both factors opaquely and unification fills
  them from the `rfl`.  This is the general escape hatch for the
  public-def-over-private-body pattern, which is common in this tree.
* `simp only [… , Finset.sum_range_one]` does **not** fire on
  `Finset.range (0 + 1)`: `simp only` does not run `Nat.reduceAdd`.  Add
  `Nat.zero_add` explicitly.
* `nlinarith` reliably fails on the four-way product
  `C·(U²·a + S²·b) ≤ C·(U²·A + S²·B)·(1+J)`.  Split it: `add_le_add` of two
  `mul_le_mul_of_nonneg_left`, then one `ring` step.  Two occurrences.
* Deriving `0 ≤ A n` from the window itself (`moserWin_nnA`) rather than
  carrying it as a field keeps every closure lemma's constant arithmetic
  free of side conditions.
* **Quantifier order is an API decision, not a formatting one.**  See the
  `T`-uniformity section above.  The tell that a hoist is *possible* is that
  every constant-producing call in the proof is already state-free; the tell
  that it is *needed* is the consumer's `∃ K, … ∀ T`.
* `nlinarith` will not expand `(-2 * s)^2` on its own.  `rw [show (-2*s:ℝ)^2 =
  4*s^2 from by ring]` first, then hand it the product hint
  `mul_nonneg (…: 0 ≤ 1 - s^2) (hA n)`.
* `Finset.range_subset.mpr (by omega)` inside an `exact` for
  `Finset.sum_le_sum_of_subset_of_nonneg` sends `omega` a goal it cannot see
  (the reported counterexample mentions the *sum's* bound variable).  Prove the
  `⊆` as a standalone `have`, or `intro x hx; rw [Finset.mem_range] at hx ⊢;
  omega`.

## Honest denominators (2026-08-03, after TK3)

TK2 + TK3 in this file: **100%**.  `topKer_jet`: **PROVED**, sorry-free and
axiom-clean, so `c2_jet_tower` and `a2_ladder` are **unconditional**.  F6 as a
whole: ≈ 72% (was ≈ 62%) — the estimate side's `a₂` arm is closed; what remains
of F6 is the rest of E0's assembly, not this chain.  Front 2 (fixed-horizon
bootstrap): ≈ 53%.  (N) `ricci_flow_unif_existence`: **0%** (stated, unproved).
Machinery ≈ 92%.  Whole HCG compactness project: low single digits.
