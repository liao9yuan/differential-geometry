# UNIF existence ledger, volume 3 (entries No. 104+)

Continuation of `UNIF_EXISTENCE_PLAN2.md` (entries No. 70–103 + executor
reports; frozen at ~2.7k lines against the 3000-line cap, same precedent as
`UNIF_EXISTENCE_PLAN.md` = frozen history No. 1–69).  Same conventions: one
planner entry per landed/ruled brick, executor reports appended by builders,
honest-denominator footers everywhere.  Planner numbering is canonical.

State snapshot at the volume break (2026-08-03, end of the No. 91–103 run):

- (N) `ricci_flow_unif_existence` — STATED (`Evolution/ExtendViaUniqueness.lean:80`,
  sorry at :98), proof 0%.
- Front 2 (fixed-horizon bootstrap): wiring COMPLETE through
  `lowreg_joint_two`; the chain's single sorry is `lowreg_spatialMass`
  (`ShortTime/LowRegAllOrderJet.lean`, cite by name).  F6 status: `a2_ladder`
  k-uniform at gate `3 ≤ a` (`DeTurck/LowRegLadderRung.lean:232`), its single
  sorry = `c2_jet_tower` (:144, the all-order jet tower of the path-integral
  coefficient `A.C2`); remaining = `c2_jet_tower` + a₁-arm ladder +
  `N(T)−N(0)` assembly + E1′ Galerkin plumbing (handover design in No. 103).
- Front 3 (class-uniform τ₀): plan = `FRONT3_ASSEMBLY_PLAN.md`; G1 landed
  (`refold_aff_bg`); G2 waits on front 2's leaf; G3 = constant-exposed sweep;
  open USER DECISION No. 99 (jet budget ∀a≤3 vs `staticForce` floor — default
  option (b)).
- Real sorries across the campaign lanes: `lowreg_spatialMass`,
  `c2_jet_tower`, plus the dormant off-path `hAcc_of_jets` and the off-path
  Weyl citation.  Machinery ≈90%; whole HCG compactness: low single digits.

  > SUPERSEDED for F6 by the executor report below: `c2_jet_tower` is proved;
  > the F6 leaf is now `topKer_jet` (`DeTurck/LowRegC2JetTower.lean`).

---

## Executor report — F6 main estimate brick (E0a‴): `c2_jet_tower` PROVED, frontier moved (2026-08-03)

**Verdict: GREEN-REDUCED.**  `c2_jet_tower` is a proved theorem;
`LowRegLadderRung.lean` has **zero `sorry`**.  Campaign frontier count unchanged
at exactly ONE — the leaf moved *inside* the path integral.

### Landed

New file `Analysis/Spectral/Intrinsic/DeTurck/LowRegC2JetTower.lean` (note:
`LowRegC2JetTower.md`), two declarations plus one private helper:

* `path_add_sub_jet` (`:78`) — **axiom-clean**.  Order-generic
  differentiation-under-the-integral for covariant jets:
  `∀ t ∈ [0,1], lowJetSq g n (Φ t + Ψ t − C) ≤ Λ` ⟹
  `lowJetSq g n (∫₀¹Φ + ∫₀¹Ψ − C) ≤ Λ`, same `Λ`, every order `n`, every rank.
  Improves on both siblings by deriving the combined integrand's joint
  smoothness internally instead of taking it as a third hypothesis.
* `topKer_jet` (`:212`) — **the single frontier `sorry`**.  Stated below.
* `armConst` (`:59`, private) — constant families are jointly smooth; the
  public `arm_const`/`joint_const` are `private` in files this lane cannot edit,
  so the two-line body was re-derived.

Edited: `LowRegLadderRung.lean` — import swapped to the new file, one `open`
added (`PDE.DeTurck.RicciLinearization`, for `realizedSmallSet`), `c2_jet_tower`
docstring rewritten, `sorry` replaced by a 30-line proof.  No other file touched;
`DeTurckRemainderLowBaseAction.lean` was read only.

### The moved leaf, exactly

```
topKer_jet (hDim : finrank ℝ E = 3) (g : SmoothRiemannianMetric I M) :
  ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
    ∀ (T : SmoothCcTensor g 0 2) (hT : T symmetric)
      {δ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1/3)
      (hδg : gFibreOpBound g (ccTensorBilinSymm g T) δ)
      (hδZ : gFibreOpBound g (ccTensorBilinSymm g 0) δ)
      (i : ℕ) (s : ℝ), s ∈ Set.Icc (0:ℝ) 1 →
      lowJetSq g i (rhsRefoldTop g g T hδg hδZ s
                     + LowBaseInternal.rhsSelfTop g T hδg hδZ s
                     − deTurckPhiMetTotal g g g)
        ≤ Kk i * (1 + ∑ j ∈ Finset.range (i+2), ‖iteratedCovGrad g 0 2 j T‖^2)
```

### Two corrections to the standing narrative

1. **The integral layer was NOT the new content** (autopsy §5 risk 1 partly
   refuted).  `path_jetL2_le` (`ParametricJetIntegral.lean:331`) and the real
   `∇ⁱ∫ = ∫∇ⁱ` commutation `icg_path_comm` (`:291`) already exist and are
   order-generic.  Only the additive rearrangement `∫Φ+∫Ψ−C = ∫(Φ+Ψ−C)` was
   missing in usable form (the two copies are a `private` in the claimed
   13.8k-line file and a fibre-pointwise, non-jet public lemma).  Another
   "framework wall" that was already stocked.
2. **`c2_jet_tower`'s `H^{a+2}` ball is vestigial.**  `a2_ladder` calls it
   without forwarding `ha : 3 ≤ a`, so `a` is arbitrary; at `a = 0` the ball
   buys nothing.  The real input is `δ ≤ 1/3`, which via `hδg` is the pointwise
   operator bound `‖T‖_{L^∞} ≤ 1/3` — the Moser/GN input.  Leaf stated
   ball-free.

### Producer inventory for the leaf, and a PLANNER DECISION

`topKernel_eq` splits the integrand into three summands:

| summand | all-order producer |
|---|---|
| `lieRefold2` | **EXISTS**, exact shape: `exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow` (`RiemannCoefficientPalatiniRefold.lean:18865`), 3rd clause |
| `Φmet(gm) − Φmet(g)` | none (only `phi_dev_h2`, `LowRegPathSplit.lean:461`) |
| `(−2s)•ricciTop g gm T` | none (only `ricciTop_h2`, `…LowBaseAction.lean:9656`) |

The existing `lieRefold2` producer gates on `2·finrank ℝ E + 10 ≤ a` (dim 3:
`a ≥ 16`) and consumes a *pointwise jet window* `∀ j ≤ a+2, ‖∇ʲT‖ ≤ R`, not an
`L^∞` bound.  **Reusing it re-gates the whole chain to `a ≥ 16` and undoes the
`a ≥ 3` bottom that brick E0a″ bought the same day** (`H⁵` → `H^{18}`).
Executor recommendation: keep `a ≥ 3`, pay the ball-free Moser route.

**Smallest next statement** (next brick's unit, `Tensor/Estimates/` layer): an
all-order `appCcRS` product jet estimate
`‖∇ⁱ(appCcRS g a b c A B)‖² ≲ C i · (∑_{p≤i}‖∇^pA‖²)(∑_{q≤i}‖∇^qB‖²)`, plus
all-order jet windows for `daTrans`, `dagTopOp`, `deTurckPhiMetTotal ∘
realizedFam` — the general-`i` replacements for the fixed-order-two privates
`app_h2_mul`, `full_slot_h2_low`, `curvMono_h2`, `connLow_h2_low`.  Own
multi-session estimate brick; **not** an API gap.

### Verification

Focused checks clean on both edited/created files; targeted module builds of
`…DeTurck.LowRegC2JetTower` and `…DeTurck.LowRegLadderRung` both succeeded.
Axiom census: `path_add_sub_jet` and `appCc_cap_hs_le` clean
(`propext, Classical.choice, Quot.sound`); `c2_jet_tower` and `a2_ladder` carry
`sorryAx` solely through `topKer_jet`.  Sorry census across
`{LowRegLadderRung, LowRegC2JetTower, LowRegDissipRung, AppCcSplitEnvelope,
ConnLapCommutatorCoefficientTame}`: exactly **1**.  No `maxHeartbeats` above
800 000.

### Honest denominators

`path_add_sub_jet` ≈ 35% of `topKer_jet`+integral-layer taken together, but 0%
of the *estimate* itself.  `topKer_jet`: **not started (0%)** — one of its three
summands has a ready producer that is not contract-compatible, so call the
stocked fraction ≈ 15% and the usable fraction ≈ 0%.  `c2_jet_tower`: **100%**
(proved).  `a2_ladder` unconditional: gated entirely on `topKer_jet`.  F6 as a
whole: ladder + engine + threshold done, estimate open ⇒ ≈ 55%.  Front 2
(fixed-horizon bootstrap): ≈ 45%.  (N) `ricci_flow_unif_existence`: still
**0%** (stated, unproved).  Whole HCG compactness project: low single digits.

## Planner update No. 104 (2026-08-03) - EXECUTOR RECOMMENDATION RATIFIED: KEEP a ≥ 3, MOSER ROUTE FOR topKer_jet

Ruling on the decision the `c2_jet_tower` executor surfaced: the
existing all-order `lieRefold2` producer
(`RiemannCoefficientPalatiniRefold.lean:18865`) is REJECTED for the
`topKer_jet` route — its `2·finrank+10 ≤ a` gate and pointwise
jet-window contract would re-gate the whole chain to `a ≥ 16` (ball
`H^{18}`) and undo the `a ≥ 3` bottom that the threshold brick bought,
which the No. 103 handover design depends on.  `topKer_jet` is to be
proved on the ball-free Moser route with `δ ≤ 1/3` (`‖T‖_{L^∞} ≤ 1/3`)
as the only smallness input.

Brick sequence for `topKer_jet` (per the executor's pinned inventory):
1. TK1 — the all-order `appCcRS` product jet estimate at
   `Tensor/Estimates/`:
   `‖∇ⁱ(appCcRS g a b c A B)‖² ≲ C i · (∑_{p≤i}‖∇ᵖA‖²)(∑_{q≤i}‖∇^qB‖²)`
   (the general-`i` replacement for the fixed-order-two private
   `app_h2_mul`); FIRST dispatchable unit.
2. TK2 — all-order jet windows for the three operator families
   (`daTrans`, `dagTopOp`, `deTurckPhiMetTotal ∘ realizedFam`;
   general-`i` replacements for `full_slot_h2_low`, `curvMono_h2`,
   `connLow_h2_low`).
3. TK3 — the three-summand assembly of `topKer_jet` (uses
   `topKernel_eq`'s split + TK1/TK2 + the `s`-uniformity from the
   bounded-below denominators).

Executor trap notes carried forward: the `LowBaseInternal` double
declarations (`Invalid argument name 'I'` failure shape, not "unknown
identifier"); opacity discipline; `linarith only`.

Honest accounting: (N) stated, proof 0%.  F6 ≈55% (ladder+engine+
threshold done; estimate = TK1-TK3 open).  Front 2 ≈45-70% by
sub-ledger (wiring 100%, estimate side open).  Machinery ≈90%.  Whole
HCG compactness: low single digits.

---

## Executor report — TK1 (`appCcRS` all-order product jet estimate): GREEN, and it was stocked (2026-08-03)

**Verdict: GREEN.**  TK1 of ruling No. 104 is landed, zero `sorry`, all
declarations axiom-clean.  The campaign frontier count is unchanged at exactly
ONE (`topKer_jet`); TK1 was a *producer* brick, not a frontier.

**The scoping was wrong, and in the now-familiar direction.**  The ruling
scoped TK1 as "its own multi-session estimate brick, **not** an API gap".  It
is neither: it is a ~200-line composition of machinery that was already in the
tree, order-generic *and* arity-generic.  This is stocked-wall instance
**thirteen**.  Nothing new about tensor calculus was proved.

### Landed

New file `Analysis/Spectral/Tensor/Estimates/AppCcRSJetMul.lean` (note:
`AppCcRSJetMul.md`), in the canonical home of the `appCc`/`appRS` estimate
family, importing only `Estimates/H1H2AppCcRS.lean`.  Three theorems, every one
universally quantified over the valences `(p, r, c)`
(`Φ : SmoothCcTensor g r c`, `W : SmoothCcTensor g p r`).  Write
`Sₙ X := ∑_{j ∈ range (n+1)} ‖iteratedCovGrad g _ _ j X‖²`, which is
`lowJetSq g n X` unfolded (`lowJetSq` is defined downstream in
`DeTurckRemainderLowBaseAction.lean` and is not importable at this layer, so the
sums are spelled out — exactly as `appRS_h2_h2_h2` does).

* `appRS_hn_sup` (`:83`) — **the engine.**  Gate-free, dimension-free, sharp in
  the jet order:
  `Sₙ(appCcRS g p r c Φ W) ≤ C n * (B²·SₙΦ + A²·SₙW)`, where `A`, `B` bound the
  pointwise fibre norms of `Φ`, `W`.  Each arm's `L∞` bound multiplies the
  *other* arm's full `L²` jet — literally the Moser/GN pairing the ruling
  ratified.  `C n = ∑_{j≤n} appCcGdiag j · G j`, exponential in `n`; no
  `n`-uniformity claimed or needed.
* `appCcRS_jet_mul` (`:196`) — **the product form the ruling asked for**:
  `Sₙ(appCcRS g p r c Φ W) ≤ C n * SₙΦ * SₙW`, gated at
  `finrank ℝ E / 2 + 1 ≤ n` (dim 3: `2 ≤ n`).  This is the general-`i`
  replacement for the private fixed-order `app_h2_mul`, which is its `n = 2`
  case.
* `appRS_hn_hn_hn` (`:266`) — the family's `(A, B)` envelope shape at `2 ≤ n`;
  at `n = 2` it *is* `appRS_h2_h2_h2`.

No file was edited.  `DeTurckRemainderLowBaseAction.lean` and
`ConnLapCommutatorCoefficientTame.lean` were read only.  A new file was used
rather than appending to `H1H2AppCcRS.lean` because the latter sits directly
under the other-lane-claimed 13.8k-line `…LowBaseAction.lean`.

### What was already there (measured)

| ingredient | where | generic in |
|---|---|---|
| covariant Leibniz for `appCcRS`, all orders | `iteratedCovGrad_appCcRS_eq`, `CovGrad/IteratedAppCcLeibniz.lean:90` | order + arity |
| pointwise diagonal product grid, arbitrary contravariant rank | `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le`, `MetricArmCoeffJetTower.lean:2361` | order + arity |
| integrated GN two-arm companion for that grid | `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`, `RemainderCoeffPerOrderJetEnvelopes.lean:862` | order + arity |
| sharp `C0` jet-sum Sobolev window | `exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`, `SobolevEmbeddingSharpC0JetSum.lean:717` | arity |

The decisive observation, and the sharpest version of the stocked-wall lesson so
far: **`appRS_h2_h2_h2`'s proof was already the general theorem.**  Its internal
`hterm` is proved for an *arbitrary* order `i`; the `hi : i < 3` hypothesis is
consumed only by `Finset.range_mono`, to shrink the running jet window into the
fixed one.  Only the `Finset.range 3` in the **statement** was order-two.
Lesson to carry: when a fixed-order member blocks a lane, read its *proof*, not
its statement — the generality is often already inside.

### One real gate, and a routing instruction for TK3

`appCcRS_jet_mul`'s gate is **mathematically necessary**, not routing debris: at
`n = 0` the claim is `‖ΦW‖²_{L²} ≤ C‖Φ‖²_{L²}‖W‖²_{L²}`, false (concentrating
bump); `H¹` in dim 3 is not an algebra either.  The gate is exactly Sobolev
supercriticality, i.e. `range (finrank/2 + 2) ⊆ range (n+1)`.

**TK3 should assemble `topKer_jet` through `appRS_hn_sup`, not through the
product form.**  The engine is gate-free and costs no jet orders, and its `L∞`
slot is precisely what the leaf already carries: `hδg` with `δ ≤ 1/3` unfolds to
the pointwise operator bound on `T`.  Routing through `appCcRS_jet_mul` instead
would need `S₂` at `i = 0`, overrunning `topKer_jet`'s `∑_{j < i+2}‖∇ʲT‖²`
budget by one order.  This is worth pinning in the TK3 brief.

### Arity coverage vs `topKernel_eq`

Total.  `ricciTop = appCcRS g 4 4 2 (daTrans g gm T) (dagTopOp g gm)`
(`…LowBaseAction.lean:3514`) is the `(p, r, c) = (4, 4, 2)` instance; the ~20
distinct `appCcRS` arities appearing across `…LowBaseAction.lean` (`0 2 2`,
`2 2 2`, `2 3 3`, `2 3 4`, `2 4 2`, `2 4 4`, `3 3 3`, `4 4 2`, `4 6 2`, `6 4 2`,
`6 6 4`, …) are all instances of the same three statements.  Probed at `4 4 2`
and `0 2 2`; the dim-3 gate discharges by `rw [hDim]` alone.

### Verification

Focused check clean (no warnings at all); targeted module build of
`…Tensor.Estimates.AppCcRSJetMul` succeeded.  Axiom census: `appRS_hn_sup`,
`appCcRS_jet_mul`, `appRS_hn_hn_hn` **all clean**
(`propext, Classical.choice, Quot.sound`).  Sorry census in the new file: **0**.
No `set_option maxHeartbeats` anywhere in the file — none was needed.  A scratch
probe (not committed) confirmed the `lowJetSq` drop-in closes by
`simpa only [lowJetSq]`, so TK2/TK3 pay nothing for the vocabulary change.

### Honest denominators

TK1: **100%** (done).  `topKer_jet`: still **not started (0%)** as a theorem —
TK1 is dedicated machinery for it, and with the product calculus now stocked the
usable fraction of its inputs is ≈ 40% (was ≈ 0%: `lieRefold2`'s producer is
contract-incompatible, the `appCcRS` product layer is now real, the operator
windows of TK2 are not).  TK2 is now the load-bearing unknown of the sequence —
TK1 removed the product calculus, not the operator-family windows, and it is
those windows that carry the `realizedFam` metric dependence.  `c2_jet_tower`:
100%.  `a2_ladder` unconditional: still gated entirely on `topKer_jet`.  F6 as a
whole: ≈ 58% (was ≈ 55%; ladder + engine + threshold done, estimate side now one
of three bricks in).  Front 2 (fixed-horizon bootstrap): ≈ 47%.  (N)
`ricci_flow_unif_existence`: **0%** (stated, unproved).  Machinery ≈ 90%.  Whole
HCG compactness project: low single digits.


---

## Executor report — TK2 (all-order operator-family jet windows): GREEN, all three families (2026-08-03)

**Verdict: GREEN.**  TK2 of ruling No. 104 is landed for **all three** families,
zero `sorry`, all declarations axiom-clean, no `maxHeartbeats` bump, no linter
warnings.  Campaign frontier count unchanged at exactly ONE (`topKer_jet`);
TK2, like TK1, was a *producer* brick.

### Landed

New file `Analysis/Spectral/Intrinsic/DeTurck/LowRegOpJetWindows.lean` (note:
`LowRegOpJetWindows.md`), 1050 lines, 34 declarations, importing only
`DeTurckRemainderLowBaseAction` (read-only, other-lane claimed) and TK1's
`AppCcRSJetMul`.  No existing file was edited.

Every family window has the shape the brief asked for, with **derivative offset
`w = 0`**:

```
lowJetSq g n F  ≤  A n * (1 + lowJetSq g n T)      -- uniformly in s ∈ [0,1]
```

| family | decl | line | `w` | `K i` realization |
|---|---|---|---|---|
| `daTrans g gm T` | `moserWin_daTrans` | 890 | 0 | `2(A' n + A' n)`, `A'` from `moserWin_curvMono ∘ moserWin_daWeight` |
| `dagTopOp g gm` | `moserWin_dagTop` | 792 | 0 | `C n ((√fr·S_conn)²·A_perm n + S_perm²·fr·A_conn n)` |
| `deTurckPhiMetTotal g g_bg gm − …g` | `moserWin_phiDev` | 967 | 0 | `2(2(A_TH+A_TH) + 2(A_R+A_R))`, `A_TH n = (∑_{i≤n}C_i)·A_gInv n` |

Plus the assembled `moserWin_ricciTop` (`:918`) — the **ball-free**
`ricciTop_h2` — and the supporting tower: `moserWin_sharp` (`:566`),
`moserWin_fullSlot` (`:640`), `moserWin_gInvDiff` (`:717`), `moserWin_connLow`
(`:757`), `moserWin_daWeight` (`:820`), `moserWin_curvMono` (`:846`).  These are
the general-`i` replacements for `sharp_h2_low`, `full_slot_h2_low`,
`inv_coeff_h2`, `connLow_h2_low`, `curvMono_h2` respectively.

### The one design decision, and why it is load-bearing

A single predicate carries both halves the Moser pairing consumes:

```lean
def IsMoserWin g T A S X : Prop :=
  0 ≤ S ∧ (∀ x, rfns g r c x (X.toSection x) ≤ S ^ 2)
        ∧ (∀ n, lowJetSq g n X ≤ A n * (1 + lowJetSq g n T))
```

Carrying the `L∞` bound *alongside* the jet bound is the whole content.
`appRS_hn_sup` multiplies each arm's `L∞` bound by the **other** arm's `L2`
jet, so a product of two windows is again a window — affinity preserved, no
ball, no order gate.  The fixed-order-two route cannot do this: `ricciTop_h2`
produces `C·jetΦ·jetW` and has to assume `lowJetSq g 2 P ≤ 1`, an `H2` ball, to
linearize.  **TK1's routing instruction was therefore not a budget optimization
— routing through the engine is what removes the ball**, which is the whole
point of the Moser ruling.  Ten closure lemmas (`moserWin_appRS`, `_slot`,
`_dom`, `_reindex`, `_rsperm`, `_add`, `_sub`, `_const`, `_endoIns`, `_self`)
are each three lines of bookkeeping once the predicate is right.

The hypothesis side is bundled as `IsPathPert g g₁ P T δ₀`: `g₁ = g + P`, `P`
`δ₀`-fibre-small with its pointwise certificate, `P` jet-dominated by `T`.  The
`s`-uniformity is structural — no constant produced in the file mentions `s`.

### Stocked-wall instance fourteen, twice over

1. **`sharpFlatEndoCc_lowOrder_jetL2_radiusFree` is already all-order.**  Its
   order cap `a` is a *free parameter* subject only to `2·finrank+10 ≤ a`, and
   the conclusion is `∀ i ≤ a+1`.  Instantiating `a := 2·finrank+10+n` gives
   order `n` at no cost.  The privates `sharp_h2_low` and `sharp_h3_rf` are
   byte-identical invocations differing only in `2` vs `3`.  Same lesson as
   TK1's `appRS_h2_h2_h2`, one layer down.
2. **The `private` `curvMono_pair` has a public wrapper.**  `curvMono_pair`
   (`…LowBaseAction.lean:6469`, ~190 lines of delicate index work) is what made
   family `daTrans` look like a 270-line copy job.  It is re-exported as
   `LowBaseInternal.curvMono_eq` (`:8985`) together with the public `monoPerm`
   (`:8980`) — in the file's **second** `LowBaseInternal` block (`:8976–9008`),
   disjoint from the first (`:3372–3835`).  Grepping only the first block is
   what produced §5.1e's "no all-order producer" reading.
   **Rule to carry: `…LowBaseAction.lean` has two disjoint public-export blocks;
   grep both before declaring a helper unreachable.**

Nothing new about tensor calculus was proved.  The re-derived helpers
(`sharpSlot0`, `raisedSelf`, `raisedDecomp`, `insAdd`, `reindexSub`, and the
jet-algebra layer) each already have 2–5 `private` copies in the tree;
`DeTurckVFJetRadiusFree.lean:334` documents in prose that "every sibling
re-derives them", so this is the established pattern, not duplication drift.

### Correction to the No. 104 inventory

The ruling listed the metric deviation as having "no all-order producer".  Its
per-order producers were in fact already order-generic
(`traceHessianCoeff_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2` and the
`ricciArmPrincipalCoeff` sibling, `RemainderCoeffL2JetMoser.lean:199,365`); the
only gap was a ball-free window for their common factor `gInvDiffSlotCoeff`,
which is one `moserWin_sub` away from the sharp engine.  Family C was the
*cheapest* of the three, not the hardest.

### TK3 handoff

**Budget: no family overruns.**  `topKer_jet`'s RHS `∑_{j ∈ range (i+2)}` is
`w = 1`; every TK2 window is `w = 0`, so each has a full order of slack.  Nothing
to absorb.

TK3 owes exactly two things:

1. **`lieRefold2`'s Moser window** — deliberately outside TK2's scope, since the
   ruling's inventory names three families and `lieRefold2` was listed as
   already having a producer (rejected for its gate).  `moserWin_curvMono` is
   stated over a *general* window argument `Y`, so it applies to `lieRefold2`'s
   monomials `curvatureRefoldMonomialCoeffField g gm (unit (symmS g T)) σ`
   verbatim.  The one structural difference: `lieRefold2`'s second metric
   argument is the *moving* `gm`, so `lieCovPair g gm` is not a constant and
   needs its own window — `LowBaseInternal.pairTrace_eq` (`:9000`) factors it
   into two `pureTrace`s.  Its ball-free order-0 cap `lieRefold2_cap`
   (`LowRegPathSplit.lean:101`) is public.
2. **The `IsPathPert` discharge along the radial path**, for each `s ∈ [0,1]`:
   `realizedFam_inner_of_mem` + `Icc_subset_realizedSmallSet` (tie),
   `convexPerturbation_gFibreOpBound_abs` (the `δ` bound) — both used verbatim
   in `lieRefold2_cap` — `rfns_symmS_zero_le_fibreSmall` (pointwise
   certificate), and `jet_smul` for
   `lowJetSq g n (convexPerturbation g T 0 s) ≤ lowJetSq g n T`.

After that, `topKer_jet` is `path_add_sub_jet`-style bookkeeping plus
`moserWin_add`/`moserWin_sub` on three windows, with `Kk i := A i`.

### Verification

Focused check clean (no errors, no warnings).  One targeted module build of
`…DeTurck.LowRegOpJetWindows` succeeded.  Axiom census on `moserWin_daTrans`,
`moserWin_dagTop`, `moserWin_phiDev`, `moserWin_ricciTop`, `moserWin_gInvDiff`,
`moserWin_sharp`, `moserWin_appRS`: **all clean**
(`propext, Classical.choice, Quot.sound`).  Sorry census in the new file: **0**.

### Honest denominators

TK2: **100%**.  `topKer_jet`: still **not started as a theorem (0%)** — no
statement of it has been proved; the usable fraction of its inputs is now ≈ 80%
(was ≈ 40% after TK1): the product calculus and two of the three summands are
stocked, `lieRefold2`'s Moser window and the `IsPathPert` discharge are not.
`c2_jet_tower`: 100%.  `a2_ladder` unconditional: still gated entirely on
`topKer_jet`.  F6 as a whole: ≈ 62% (was ≈ 58%).  Front 2 (fixed-horizon
bootstrap): ≈ 49%.  (N) `ricci_flow_unif_existence`: **0%** (stated, unproved).
Machinery ≈ 91%.  Whole HCG compactness project: low single digits.

## Planner update No. 105 (2026-08-03) - USER DECISION No. 99 RESOLVED: OPTION (b)

The user ruled: take option (b) — re-derive the floor horizon one order
lower so the class-uniform τ₀ needs only `‖staticForce g₀ g₀ 1‖`
(3 metric derivatives, inside (N)'s `∀ a ≤ 3` budget); the (N) black-box
statement stays untouched.  Options (a) (widen (N) to `a ≤ 4`) and (c)
(carry `Λ₄`) are retired unless (b) hits a wall, in which case (a) with
its consumer-side Shi-tail feasibility check is the fallback.

Implementation constraint noted at ruling time: any `H²`-valued bound on
`fHi` necessarily passes through `staticForce`-at-order-2 (the fixed
point's constant term at scale `aHi = 2`), so (b) means either LOWERING
THE SLOT ORDER (does the joint-smoothness engine's `hfloor` truly need
`√T‖u.deriv‖` in `L²ₜH²`, or does a lower-order/weaker floor suffice for
its actual role in the engine's proof?) or MOVING THE FLOOR to the Lo
side (the `f = fLo` fixed point at `H¹`, whose forcing constant is
`staticForce`-at-1 with `norm_liftForceLo_le` already in
`LowRegLiftNTerm`).  A read-only design recon settles which; the
implementation brick follows once the Lean slot frees.

## Planner update No. 106 (2026-08-03) - (b) DESIGN RULED: THE FLOOR IS DELETED, NOT LOWERED

The (b) design recon returned (full design =
`ShortTime/OPTIONB_FLOOR_PLAN.md`, 316 lines) and the planner
spot-verified its two central claims before accepting:

- `hfloor` has exactly ONE use in the joint-smoothness engine
  (`MaxRegSolutionJointlySmooth.lean:1347` declaration, `:1502` sole
  use).  The calc chain `‖u(t)‖ = ‖u(t) − u.init‖ ≤ √t‖u.deriv‖ ≤
  √T‖u.deriv‖ ≤ 1/(2C)` shows its true content is smallness of the
  STATE `sup_t ‖u(t)‖_{H^a} ≤ 1/(2C)` (feeding `gFibreOpBound … 1/2`,
  i.e. "g₀ + F t stays a metric"); `u.deriv` is only a proxy.
  VERIFIED by grep: no other use site.
- `IsRealizedTwo` ALREADY carries that state bound as a separate
  conjunct: `∀ᵐ t ∂timeMeasure T, ‖u.lo.toFun t‖ ≤ R`
  (`LowRegApplyTwo.lean:218`), on the very object the engine bounds,
  with `R = lowregStateRad ≤ P/4` and `P` chosen inside
  `lowreg_solve_two` under upper-bound-only constraints.  VERIFIED by
  read: the conjunct sits immediately before the `√T‖fHi‖ ≤ Kf`
  conjunct.

RULING (stocked-wall instance SIXTEEN): option (b) is implemented by
DELETION, not by re-derivation at a lower order.  Replace the engine's
`hfloor` slot by the state bound, cap `P ≤ Rcap ~ 1/(2C)`, delete the
`√T‖fHi‖ ≤ Kf` conjunct and `lowregFloorHorizon` — and
`‖staticForce g g 2‖` leaves the tree entirely.  Front-3 item (C)1 is
DISSOLVED, not relocated: the order-1 force number is already the `D`
inside `lowregHorizon` (`UnifClassBounds.lean:81`), class-bounded via
`staticN_h1_le → nZero_unif` with producer `unifKsupLeOne`
(`UnifDeTurckRHSOne.lean:1538`, hypotheses at orders 1–3 only — inside
(N)'s `∀ a ≤ 3` budget).  Cost: `τ₀` shrinks by a class-uniform
`(1/(2C))²` factor through `lowregHorizon` — not a failure signal.

Brick sequence (details in OPTIONB_FLOOR_PLAN.md):
- **B1 (first, dispatchable at next Lean-slot release)**: engine slot
  lowering in `MaxRegSolutionJointlySmooth.lean` — swap `hfloor` for
  `hstate : ∀ t ∈ Icc 0 T, ‖timeH1.toFun u t‖ ≤ 1/(2C)`, extract the
  old calc as producer `state_le_of_sqrt_floor` so the single call
  site (`LowRegAllOrderJet.lean:1550`) keeps passing the old floor
  through the shim — pure refactor, tree stays green.  File is NOT
  owned by the F6/TK3 lane.
- B2: a.e. → everywhere on `Icc 0 T` via the closed-bound-set
  density argument (`Measure.eqOn_Icc_of_ae_eq` pattern at
  `LowRegAllOrderJet.lean:334-348` + `timeH1.continuousOn_toFun`).
- B3/B4: conjunct swap + `P` cap in `LowRegApplyTwo.lean` (front-2
  shared file — claim after the front-2 leaf releases).
- B5: endpoint wiring.

Fallback to (a) ONLY on the conjunction: B2 fails at the closed
endpoint `t = T` AND fallback route B (`H¹` floor via
`maxRegDuhamelSolField_inclusion_Ha1_ae_pointwise_le`,
`FieldHa1TimeSupTrace.lean:183`, plus a Lo-side `norm_fix_le` mirror)
also fails.  Residual (pre-existing, unchanged): the engine's `C` comes
from an opaque `(hs2_opBound_at_two …).choose` — class-uniformity still
needs front 3's constant-exposure swap to `hs2OpC`.

Honest denominators: design only, no new Lean proved.  (N): 0%.
F6 ≈ 62% (TK3 in flight).  Front 2 ≈ 49%.  Front 3: one of ~8 items
dissolved in design.  Machinery ≈ 91%.  Whole HCG project: low single
digits.  Route-error counter: 0/3 (№99→(b)→deletion is a plan
refinement chain, not a route error — the floor brick itself was landed
green and stays usable through the B1 shim).

---

## Executor report — TK3 (`topKer_jet` assembly): GREEN, `a2_ladder` unconditional (2026-08-03)

**Verdict: GREEN.**  TK3 of ruling No. 104 is landed.  `topKer_jet`
(`Analysis/Spectral/Intrinsic/DeTurck/LowRegC2JetTower.lean:196`) is **proved**,
zero `sorry`, axiom-clean — and with it `c2_jet_tower` and **`a2_ladder`**
(`LowRegLadderRung.lean:144`, `:232`) are **unconditional**.  The campaign
frontier count goes from ONE to **ZERO** on the F6 estimate chain.

### Campaign sorry census after this brick

* F6 estimate chain (`a2_ladder ⇐ c2_jet_tower ⇐ topKer_jet` and everything
  below): **zero**.
* Remaining campaign `sorry`: exactly one, `lowreg_spatialMass`
  (`ShortTime/LowRegAllOrderJet.lean:1053`) — upstream, brick E1′'s target.
* Outside the campaign, unchanged: the Weyl citation-`sorry`
  (`ShortTime/WeylEigenvalueCountingBound.lean:115`, policy pending) and
  `Sobolev/TensorHilbert/Rellich.lean:63`.

### The `Kk` realization

```
Kk i = |2 * (2 * (A_lie i + A_phi i) + 4 * A_ric i)|
```

`A_lie`, `A_phi`, `A_ric` are the envelopes of `moserWin_lieRef2`,
`moserWin_phiDev`, `moserWin_ricciTop`.  The `2 * (· + ·)` nesting is
`moserWin_add`'s constant applied twice; the `4` is `moserWin_smul` at
`a = −2s` followed by `moserWin_mono` with `(−2s)² ≤ 4`.  The outer `|·|` is
the only piece with no mathematical content: `∀ i, 0 ≤ Kk i` must be discharged
*before* `T` is introduced, and window nonnegativity (`moserWin_nnA`) needs a
window instance and hence a state, so `le_abs_self` supplies it for free.
No constant mentions `s`.

### The `lieCovPair` window route (TK3's producer job)

```
lieCovPair g gm   =(LowBaseInternal.pairTrace_eq)=  appCcRS g 6 4 2 (pureTrace g gm 2) (pureTrace g gm 4)
pureTrace g gm k  =(pureTrace_split)=              appCcRS g (k+2) (k+2) k (cometricDoubleTraceField g k)
                                                     (slotInsertEndoCc g (k+1) (gInvDiffRaisedEndoField g gm))
                                                   + cometricDoubleTraceField g k
```

The only metric-dependent factor is `slotInsertEndoCc g (k+1)
(gInvDiffRaisedEndoField g gm)` — the **same** inverse-difference endomorphism
that `moserWin_gInvDiff` already windows, at a different slot.  TK3 therefore
split `moserWin_gInvDiff` into `moserWin_gInvSlot k` (the core, arbitrary slot)
plus a three-line corollary at `k = 1`, and the rest is two `moserWin_appRS`
steps per layer.  **Stocked-wall instance fifteen**: the "moving second metric"
that the handoff flagged as the one structural difference is not a new object
at all.

`moserWin_symmS` (the argument of `lieRefold2`'s monomials) is likewise free:
`iteratedCovGrad_symmS_eq` plus the public per-order permutation isometry
`riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection` give `symmS g T` the
*same* window as `T`, without assuming `T` symmetric.

### What the handoff did not name, and what it actually cost

**A quantifier-order mismatch, and it was the bulk of the brick.**
`topKer_jet` produces `Kk` **before** `T`; every TK2 family window bound `T`
before its `∃ A S`.  `∀ T, ∃ A` does not give `∃ A, ∀ T`.  The constants were
already morally state-free, so the fix was to hoist `T` inside the existential
in twelve statements (`moserWin_const`, `_appRS`, `_sharp`, `_fullSlot`,
`_gInvDiff`, `_connLow`, `_dagTop`, `_daWeight`, `_curvMono`, `_daTrans`,
`_ricciTop`, `_phiDev`), each proof needing only `intro T` moved past
`refine ⟨…⟩`.  It checked clean on the first pass, but it is a public-API
change to a file landed the same day.

**Rule to carry:** when a window/envelope predicate mentions the state, fix the
quantifier order from the *final consumer's* signature, not from the local
statement.  A producer brick that stops at `∀ state, ∃ constant` has not
delivered a constant.

### Declarations landed

`LowRegOpJetWindows.lean` (now 1409 lines, 42 declarations): `moserWin_smul`
(`:263`), `jetSmul` (`:253`), `moserWin_symmS` (`:589`), `moserWin_gInvSlot`
(`:811`), `moserWin_pureTr` (`:1177`), `moserWin_lieCovP` (`:1201`),
`moserWin_monoMov` (`:1224`), `pathPert_rad` (`:1278`), `moserWin_lieRef2`
(`:1324`); plus the private `rfnsSymmS` (`:552`) and `cvxRad` (`:1267`).

`LowRegC2JetTower.lean` (284 lines): `topKer_jet` (`:196`) — `sorry` replaced,
FRONTIER docstring rewritten to record the route; one import added
(`LowRegOpJetWindows`).

Notes updated: `LowRegOpJetWindows.md`, `LowRegC2JetTower.md`,
`LowRegLadderRung.md`, `F6_ESTIMATE_RECON.md` §5.1h.

### Verification

Focused checks clean on both edited files, zero warnings.  One targeted module
build each of `…DeTurck.LowRegOpJetWindows` and `…DeTurck.LowRegLadderRung`
(the latter covering `LowRegC2JetTower`) succeeded.  Axiom census clean
(`propext, Classical.choice, Quot.sound`) on `topKer_jet`, `c2_jet_tower`,
`a2_ladder`, `path_add_sub_jet`, `moserWin_lieRef2`, `moserWin_lieCovP`,
`moserWin_monoMov`, `moserWin_pureTr`, `moserWin_symmS`, `pathPert_rad`,
`moserWin_ricciTop`, `moserWin_phiDev`.  No `maxHeartbeats` added anywhere (the
only bump in either file is the pre-existing `800000` on `path_add_sub_jet`).

### Honest denominators

TK1/TK2/TK3: **100%** — ruling No. 104's brick sequence is complete.
`topKer_jet`: **100%** (proved).  `c2_jet_tower`: 100%, unconditional.
`a2_ladder`: 100%, **unconditional** — E0a′ is settled affirmatively with no
residual.  F6 as a whole: ≈ **72%** (was ≈ 62%); what remains of F6 is the rest
of E0's assembly (E0c, E1–E5) and the `a₁` arm's ladder, not this chain.
Front 2 (fixed-horizon bootstrap): ≈ **53%** (was ≈ 49%).  (N)
`ricci_flow_unif_existence`: **0%** — stated at
`Evolution/ExtendViaUniqueness.lean:80`, proof not started; nothing in this
brick touches its statement.  Machinery ≈ 92%.  Whole HCG compactness project:
**low single digits** — this brick closes one estimate chain inside one front of
one of the project's several phases.

## Planner update No. 107 (2026-08-03) - TK3 ACCEPTED; F6 ESTIMATE CHAIN CLOSED; B1 DISPATCHED

TK3 acceptance: the planner independently re-ran the sorry census by
grep — `LowRegC2JetTower.lean` real sorries = 0 (the single textual hit
is a docstring), `LowRegAllOrderJet.lean` real sorries = 1
(`lowreg_spatialMass` at :1053; all other hits are docstrings).  This
matches the executor's claim: the F6 estimate chain
(`a2_ladder` ← `c2_jet_tower` ← `topKer_jet` ← TK1/TK2/TK3) is
sorry-free and axiom-clean, `a2_ladder` UNCONDITIONAL at gate `3 ≤ a`.
The campaign's remaining Lean frontier is exactly ONE sorry:
`lowreg_spatialMass` (E1′'s target), plus (N) itself.

Two durable rules from TK3's report, promoted to standing guidance:
- **Quantifier order of window/family predicates is fixed by the FINAL
  consumer's signature** (constants-before-state vs state-before-
  constants).  TK3 had to hoist `T` inside the existential in twelve
  same-day TK2 statements because the handoff did not name the
  consumer's `∃ Kk, ∀ T` order.  Future window-layer handoffs must
  quote the consumer signature verbatim.
- Stocked-wall instance FIFTEEN (recorded by TK3): `lieCovPair`'s
  "moving second metric" dissolves via `pureTrace_split` into the SAME
  `gInvDiffRaisedEndoField` endomorphism already windowed — slot
  generality (`moserWin_gInvSlot`), not a new object.

Dispatch: brick B1 (+B2 attempt) of No. 106's floor-deletion design is
OUT (engine `hfloor` → `hstate` swap with `state_le_of_sqrt_floor`
shim in `MaxRegSolutionJointlySmooth.lean` + single call-site rewire in
`LowRegAllOrderJet.lean`; B2 = the a.e.→everywhere `timeH1` producer,
stop-and-report if the closed endpoint `t = T` resists — that outcome
is half of the (a)-fallback trigger and must come back precise, not
forced).  B3/B4 (`LowRegApplyTwo.lean` conjunct swap + `P` cap) remain
queued behind B1/B2.

Honest denominators: unchanged from the TK3 report above (F6 ≈ 72%,
front 2 ≈ 53%, (N) 0%, machinery ≈ 92%, whole project low single
digits).  Route-error counter: 0/3.

## Planner update No. 108 (2026-08-03) - spatialMass RECON ACCEPTED; FRONTIER IS FALSE AS STATED (ROUTE ERROR 1/3); R0 RULED

The spatialMass assembly recon returned (design = `F6_ESTIMATE_RECON.md`
§7, appended today; §7 numbering kept — it supersedes §6's
"correct retraction norm" open question).  Planner spot-verified all
three load-bearing claims before accepting:

1. **`lowreg_spatialMass` is FALSE as stated** (VERIFIED by read of
   `LowRegAllOrderJet.lean:1028-1053`): `FHi` is bound at :1034 with no
   hypothesis and no state ball, while the conclusion demands, for
   EVERY `σ`, summable σ-weighted spectral mass of the fixed
   trajectory — i.e. all-order spatial smoothness.  `FHi x := ⟨·,e⟩ • w`
   with `w ∈ H²∖H³` plants a permanently-`H²` component through
   `liftHiN`'s third summand; summability fails at large `σ`.  Not
   merely unproved — unprovable.
2. **The repair is already stocked at the unique call site** (VERIFIED:
   :1144 binds `hballU`; :1166-1180 builds `hbridge` via
   `liftN_smoothN_coeff`; :1182-1185 passes BOTH to
   `lowreg_forceDriver` and NEITHER to `lowreg_spatialMass`).
   Stocked-wall instance SEVENTEEN, new flavour: the stocked object is
   a *hypothesis*, not a producer.  Repair = brick S0 (statement
   surgery + rewire :1184, zero proof cost).
3. **The ball-order risk is real** (§7.5 verified): `a2_ladder`'s
   `H⁵` ball traces to `master_appCc_jet_le_sharp`'s `hballf` at
   `f (i+m+dc)` (`ConnLapCommutatorCoefficientTame.lean:564`, `:719`),
   reaching `f 5`; the a = 2 trajectory has only `C_tH³ ∩ L²_tH⁴`.

**ROUTE-ERROR COUNTER: 1/3.**  The false frontier statement counts:
it was landed, frozen, and all F6/front-2 percentages were reported
against it; a dispatched prover would have burned a session on an
unprovable goal.  (Recon-killed phantom walls do NOT count; a false
statement in the tree DOES.)  Mitigation: caught pre-dispatch, repair
zero-cost, no proof effort was wasted.

**R0 RULING (made now, provisional until A1d lands): OPTION 2 —
first-exit-time bootstrap inside the energy hierarchy.**  Rationale:
the `H⁵` ball is a FIXED low order independent of the rung `m`, so
only the bottom three scales are circular; close them at the GALERKIN
level, where the energies are finite-dimensional and `ContinuousOn`
(`galerkinEnergy_continuousOn` is stocked) and a first-exit-time
argument is clean.  Option 1 (retract at `H⁵` + continuous induction
on the LIMIT trajectory) stays as fallback — strictly harder because
the limit has less time regularity.  Option 3 (lower the engine ball)
is BLOCKED by §5.1c arithmetic (`t`-windows `0 ≤ t ≤ a−3`,
`1 ≤ t ≤ a−2` empty below `a = 3`) — no session may be spent on it.
Revisit trigger: if A1d's landed form changes which scales are
circular, re-examine before dispatching E1′a.

Accepted brick sequence (§7.6): S0 → A1a/A1b (`c1_jet_tower`/
`c0_jet_tower` Moser towers, new `DeTurck/LowRegC01JetTower.lean`) →
A1c `a1_ladder` → A1d `n_diff_hm_rung` → E1′a/E1′b (new
`HeatSemigroup/LowRegGalerkinEnergy.lean`) → E4 → G4 (largest brick,
new `HeatSemigroup/LowRegGalerkinLimit.lean`) → Z assembly.  E3
parallel-dispatchable.  a₁-arm verdict accepted: SAME TK1/TK2
mechanism, strictly easier (one derivative → lower ladder slot
`H^{m+1}`, m-dependent constants allowed, no smallness, no resolvent
commutator; 2+4 summands).  №103's m = 0,1 handover is OBSOLETE
(`a2_ladder` now unconditional at every rung) — do not implement it.
№104 applies unchanged to the a ≥ 16-gated partial stock
(`RicciConnDiffOrder1TameEnvelope.lean:1240` is `IsMoserWin`
unfolded — one cheap de-gating probe is permitted in A1a before
building fresh, since `appCc_cap_hs_le` de-gated for free).

Sequencing: S0 and Z edit `LowRegAllOrderJet.lean` — WAIT for
floor-brick B1 (in flight) to release it.  No spatialMass brick
touches `LowRegApplyTwo.lean`, so floor bricks B3/B4 can interleave.
`DeTurckRemainderLowBaseAction.lean` is other-lane-claimed: A1a/A1b
go through the public API (both `LowBaseInternal` blocks), no
un-privatizing.

Honest denominators (recon-audited): `lowreg_spatialMass` 0% and
false-as-stated until S0; its closure ≈ 40 of front 2's remaining 47
points; F6 ≈ 72% with the remaining 28% itemized as ONE real estimate
(A1a/A1b), ONE ruling (R0, now made), TWO constructions (E4, G4), no
second k-uniformity wall.  Front 2 ≈ 53%.  (N): 0%.  Machinery ≈ 92%.
Whole HCG project: low single digits.

---

## Executor report — option-(b) bricks B1 + B2: BOTH GREEN, the `t = T` risk is closed (2026-08-03)

**Verdict: GREEN, both bricks.**  Ruling No. 106's first two bricks are landed,
zero `sorry` added, tree green.  `LowRegAllOrderJet.lean` is released and free
for the S0/Z spatialMass bricks.

### B1 — engine floor slot lowered to a state slot

Three files, five edits, no public statement broken.

* `Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegSolutionJointlySmooth.lean`
  — in `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`:
  hypothesis `:1349` is now
  `hstate : ∀ t ∈ Set.Icc (0:ℝ) T, ‖timeH1.toFun u t‖ ≤ 1 / (2 * C)`
  (was `hfloor : Real.sqrt T * ‖u.deriv‖ ≤ 1 / (2 * C)`); the four-line `calc`
  inside `hF_small`'s `hnorm_le` collapsed to `exact hstate t ht_icc` (`:1499`);
  docstring bullet `:1298-1304` rewritten.  `hfloor` had exactly one use
  (grep-verified before and after); `hinit`/`htrace` stay live through `hu0`.
* `Analysis/Parabolic/TimeSobolev/TimeH1Modulus.lean:136` — NEW public producer
  `TimeSobolev.timeH1.state_le_of_sqrt_floor` (18 letters):
  `(u : timeH1 X T) (hinit : u.init = 0) {B : ℝ} (hfloor : √T * ‖u.deriv‖ ≤ B) :
  ∀ t ∈ Icc 0 T, ‖u.toFun t‖ ≤ B`.  This is the deleted `calc`, at its weakest
  form and canonical home (beside `norm_toFun_sub_init_le`, the only lemma it
  uses).  It takes `hinit` rather than `htrace`, keeping `trace0` out of the
  module's dependencies.
* `ShortTime/LowRegAllOrderJet.lean:1553-1556` — the SINGLE repo-wide call site
  derives `hinit` by `timeH1.trace0_apply` and passes
  `u.state_le_of_sqrt_floor hinit hfloor` into the new slot.
  **`lowreg_joint_smooth`'s public statement is unchanged** — it still takes the
  old `hfloor`, so nothing downstream moved and B3–B5 can land later without a
  green-tree gap.  Docstring `:1467-1471` notes the shim.

Deviation from the plan's §6 sketch, deliberate: the producer is stated
generically in `X`/`B` in the timeH1 API module, not in engine-file shape
(`MaxRegSolutionSpace`/`trace0`) in the engine.  `TimeH1Modulus.lean` has
exactly ONE importer repo-wide (the engine), so the canonical home is free.

### B2 — a.e. → everywhere, and the §8 stop-signal did NOT fire

`Analysis/Parabolic/TimeSobolev/TimeH1Modulus.lean:156` — NEW
`TimeSobolev.timeH1.norm_le_of_ae_le` (12 letters):
`(u : timeH1 X T) (hT : 0 < T) {R : ℝ} (hae : ∀ᵐ t ∂timeMeasure T, ‖u.toFun t‖ ≤ R) :
∀ t ∈ Icc 0 T, ‖u.toFun t‖ ≤ R`.  Compiled first try, ~12 lines.

**The closed endpoint `t = T` IS covered, with no weakening to `Ico` and no
appeal to route B.**  `Measure.eqOn_Icc_of_ae_eq` (mathlib
`Measure/OpenPos.lean:194`) differs from the `Ico` sibling used at
`LowRegAllOrderJet.lean:334-348` by exactly one hypothesis, `hne : (0:ℝ) ≠ T`,
discharged by `hT.ne`; its proof is `closure (interior (Icc a b)) = Icc a b`,
which holds precisely when `a ≠ b`.  The `min ‖u.toFun ·‖ R` truncation carries
it from `=` to `≤` (`min_eq_left_iff`), with `ContinuousOn` from
`timeH1.continuousOn_toFun`.  `0 < T` is required honestly (at `T = 0` the a.e.
hypothesis is vacuous); the engine context has it.  `timeMeasure T` is a plain
`def` for `volume.restrict (Icc 0 T)`, so `filter_upwards` crosses the two
spellings by defeq with no unfolding step.

Consequence for §8: the fallback conjunction cannot fire on limb (1).  Route B
(`FieldHa1TimeSupTrace.lean:183` plus a Lo-side `norm_fix_le` mirror) is NOT
needed and stays unused.  Nothing seen in this pass smells like the option-(a)
trigger.  `norm_le_of_ae_le` lands as a standalone producer — no consumer yet;
B5 is its consumer.

### Verification

Focused checks green on all three files; targeted olean refreshes green for
`…TimeSobolev.TimeH1Modulus`, `…HeatSemigroup.MaxRegSolutionJointlySmooth` and
`…ShortTime.LowRegAllOrderJet` (the last pulling the whole intervening chain,
9952 jobs, 0 errors).  The only `sorry` reported anywhere in the chain is the
pre-existing `lowreg_spatialMass` (`LowRegAllOrderJet.lean:1028`), untouched.

Axiom census, baseline taken BEFORE the edits and repeated after:

* `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii` —
  `[propext, Classical.choice, Quot.sound]`, before and after;
* `lowreg_joint_smooth` — `[propext, Classical.choice, Quot.sound]`, before and
  after (stays `sorryAx`-free and independent of `lowreg_spatialMass`);
* `state_le_of_sqrt_floor`, `norm_le_of_ae_le` — `[propext, Classical.choice,
  Quot.sound]`.

Two `unusedSectionVars` warnings surfaced in the engine's focused check at
`:49`/`:66` (private `tensorL2_ext_of_tensorL2Coeff_jsmooth`,
`ccTensorBilinSymm_zero_apply_jsmooth`, both flagging
`[BoundarylessManifold I M]`).  PRE-EXISTING, unrelated to the brick, suppressed
in real builds by the lakefile's `linter.unusedSectionVars = false`; left alone
as out-of-scope for shared private signatures.

### Honest denominators

B1 is a refactor: **0% new mathematics** — a slot swap plus a relocation of an
already-verified `calc`.  B2 is **one small real lemma** whose content is
standard measure-theoretic density; it proves nothing about Ricci flow.  Option
(b) is **2 of 5 bricks**, and they are the two that move no mathematics:
`‖staticForce g g 2‖` is still in the horizon and leaves the tree only with
B3/B4/B5.  Front 3 advances **in design only** — item (C)1's dissolution is not
yet realized in Lean.  (N) `ricci_flow_unif_existence`: **0%**, stated, unproved,
untouched by this pass.  Front 2 ≈ 53%, F6 ≈ 72%, machinery ≈ 92%, whole HCG
compactness project: low single digits — all unchanged.

Next dispatch: B3/B4 in `LowRegApplyTwo.lean` (front-2 shared file, claim after
the front-2 leaf releases), then B5's endpoint wiring, whose `hballU → hstate`
step is now a one-line application of `timeH1.norm_le_of_ae_le`.

## Planner update No. 109 (2026-08-03) - B1/B2 ACCEPTED; (a)-FALLBACK LIMB 1 DEAD; S0+E3 DISPATCHED

B1/B2 acceptance: planner spot-checks pass — `hfloor` has ZERO residue
in `MaxRegSolutionJointlySmooth.lean` (grep), and the two producers
sit at the canonical home `Analysis/Parabolic/TimeSobolev/
TimeH1Modulus.lean` (`state_le_of_sqrt_floor` :136,
`norm_le_of_ae_le` :156) with the module header documenting both.
Executor's before/after axiom census identical (`lowreg_joint_smooth`
stays `sorryAx`-free and `lowreg_spatialMass`-independent); the
`LowRegAllOrderJet` targeted refresh pulled 9952 jobs, 0 errors.  The
canonical-home deviation from the plan's engine-file sketch is
RATIFIED (narrowest-namespace rule; the module has one importer, so
no rebuild cost).

Design consequence: **the option-(a) fallback trigger's limb (1) is
DEAD.**  B2 closed the a.e.→everywhere step at the closed endpoint
`t = T` with no weakening (`Measure.eqOn_Icc_of_ae_eq` needs only
`0 ≠ T`; the `min ‖·‖ R` truncation carries `=` to `≤` via
`min_eq_left_iff`).  The floor-deletion design can now only fail
through B3/B4's `P`-cap arithmetic, which is upper-bound-only — no
remaining identified failure mode.  Fallback route B
(`FieldHa1TimeSupTrace`) stays unused.

Dispatch: S0+E3 are OUT (S0 = widen the false `lowreg_spatialMass`
by `hbridge`+`hballU` per §7.7 and rewire the :1184-area call;
E3 = promote `finiteEigenComboHs_eq_smoothCcToTensorHs` to its
canonical home, delete the two `GalerkinParabolicEnergyDeTurck`
private clones if that file is unclaimed).  Queue after S0/E3 lands:
**A1a/A1b** (the `c1`/`c0` Moser towers — the ONE real estimate left
in F6, new `DeTurck/LowRegC01JetTower.lean`, №104 constraints + the
permitted one-shot de-gating probe of
`RicciConnDiffOrder1TameEnvelope.lean:1240`), then A1c/A1d; floor
bricks B3/B4/B5 slot in opportunistically (small, no file overlap
with the A1 lane).

Honest denominators: option (b) 2/5 bricks (the two that move no
mathematics); front 2 ≈ 53%, F6 ≈ 72%, (N) 0%, machinery ≈ 92%,
whole project low single digits.  Route-error counter: 1/3.

---

## Executor report — bricks S0 + E3: BOTH GREEN; §7.6's E3 target file was impossible (2026-08-03)

**Verdict: GREEN, both bricks.**  No `sorry` added, no `sorry` removed, no
public statement broken.  One deviation from the plan, forced by an import
direction (E3, below).

### S0 — the false frontier is now honestly stated

`ShortTime/LowRegAllOrderJet.lean`, one theorem, three edits.  Exact final
signature of `lowreg_spatialMass` (verbatim binder list, `:1045`–`:1078`):

```lean
theorem lowreg_spatialMass (g : SmoothRiemannianMetric I M)
    {R ρ δ : ℝ} (hρ : 0 < ρ) (hRρ : R ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (FHi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
      (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)))
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) T)
    (hfix : (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
        (tensorHsCongr (I := I) (M := M) g 0 2
          (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num)
          (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)))
    (hbridge : ∀ S : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S‖ ≤ R →
        ∀ (δ' : ℝ) (hδ_lt : δ' < 1)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ')
          (i : TensorEigenIdx (I := I) (M := M) g 0 2),
          (liftHiN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal' FHi
              (smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) S)).coeff i =
            (deTurckSmoothN (I := I) (M := M) g g 2
              (symmS (I := I) (M := M) g S) hδ_lt
              (gFibreOpBound_symmS (I := I) (M := M) g S hδ')).coeff i)
    (hballU : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)),
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (2 : ℝ) ≤ (2 : ℝ) + 2 by norm_num)
        (maxRegDuhamelSolField (I := I) (M := M) (2 : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2)) fHi t)‖ ≤ R)
    (σ : ℝ) :
```

Conclusion and `sorry` body unchanged.  The call site inside
`lowreg_forceJetMass` gained `hRρ`, `hbridge`, `hballU` and nothing else;
`hbridge` was already a `have` there (from `liftN_smoothN_coeff`) and `hballU`
was already one of its binders, so **no producer work was needed** — the
stocked-wall-seventeen reading holds.

**One deviation from §7.7, forced and mechanical:** the frontier needed
`open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (symmS) in` above
it.  `hbridge` mentions `symmS`, and this file does not open that namespace at
file scope — every declaration that needs it opens it locally (`:133`, `:148`,
`:395`, `:518`, `:739`, `:1090`).  §7.7 did not mention this.

`hRρ` is not decoration: `hreal'` certifies fibre-smallness only at radius `ρ`,
while `hbridge`/`hballU` live at radius `R`, so the Galerkin argument cannot use
`hreal'` on the trajectory without `R ≤ ρ`.  The FRONTIER docstring and the
module-header bullet were rewritten to state the widened claim, to record the
`H² ∖ H³` counterexample that made the pre-widening form false, and to keep the
"do not consume downstream except through `lowreg_forceJetMass`" guard.  Grep
confirms, before and after, exactly one consumer repo-wide.

### E3 — promoted, clones deleted, but the plan's target file was impossible

**§7.6 row E3 names `Garding/EigenCombination.lean` as the canonical home.  That
file cannot state the lemma.**  `smoothCcToTensorHs` is defined in
`DeTurck/DeTurckRemainderDefs.lean:90`, and that module **imports**
`Garding.EigenCombination` (its line 7).  The dependency runs
`EigenCombination → DeTurckRemainderDefs`, so the bridge is unstateable in
`EigenCombination.lean`.

Landed instead in `DeTurckRemainderDefs.lean:119` — the lowest module where both
sides are in scope, and the defining home of the right-hand side — as public

```lean
theorem finiteEigenComboHs_eq (g₀ : SmoothRiemannianMetric I M) (F : Finset …)
    (c : … → ℝ) (σ : ℝ) :
    finiteEigenComboHs (I := I) (M := M) g₀ F c σ =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ
        (finiteEigenCombo (I := I) (M := M) g₀ F c)
```

with a docstring.  Name shortened from the plan's
`finiteEigenComboHs_eq_smoothCcToTensorHs` (36 letters) to `finiteEigenComboHs_eq`
(20) to stay inside the project budget; the LHS head symbol still leads, matching
the sibling `finiteEigenComboHs_coeff_eq`.

`GalerkinParabolicEnergyDeTurck.lean` was **not** claimed by another lane, so the
clone deletion landed too: both privates removed, both live uses rewired.  A
census correction — the `:529` clone had **zero** uses; the greps that appeared
to find uses were matching the `gscr_` sibling as a substring.  So E3 removed one
duplicate *and* one piece of dead code.  The `gscr_` clone's three
`set_option`s (`backward.isDefEq.respectTransparency`, two `maxHeartbeats`) were
unnecessary: the copy in the canonical home compiles with none.

### Verification

Focused checks green on all three Lean files; targeted olean refresh of
`…DeTurck.DeTurckRemainderDefs` green (0 errors).  `LowRegAllOrderJet.lean`
sorry census is exactly one (`lowreg_spatialMass`), same as before.  Axiom census
taken **before** the S0 edit and repeated after, byte-identical:
`lowreg_spatialMass` / `lowreg_forceJetMass` / `lowreg_allOrderJet` /
`lowreg_joint_two` = `[propext, sorryAx, Classical.choice, Quot.sound]`;
`lowreg_joint_smooth` = `[propext, Classical.choice, Quot.sound]` (still
`sorryAx`-free).  `GalerkinParabolicEnergyDeTurck.lean` stays sorry-free; its one
`unusedSectionVars` warning (private `gscr_eigenIdxFinset_lambda_closed`) is
pre-existing and suppressed in real builds by `lakefile.toml`.

Tooling note worth keeping: `#print axioms` **does** print through
`lake env lean` / `lake-locked check` in this checkout, contrary to the older
lesson note.  A temporary `#print axioms` block, removed afterwards, is the cheap
way to take a before/after census on a file whose full build is expensive.

Caveat for the next full build: `DeTurckRemainderDefs.lean` is a low module, so
its refreshed olean makes the whole downstream stale.  The change is purely
additive, so intermediate oleans stay content-valid and focused checks above it
are trustworthy.

### Honest denominators

**Nothing was proved.**  S0 is statement surgery: it converts a *false* claim
into a *true-target* claim at zero proof cost, and the `sorry` is untouched.
`lowreg_spatialMass` remains **0% proved** — the only thing that changed is that
everything downstream is now conditional on something that is at least provable.
E3 is API hygiene: one duplicate and one dead private removed, one public lemma
where there were two privates; **0% new mathematics**.

F6 ≈ 72%, front 2 ≈ 53%, machinery ≈ 92% — all unchanged, since neither brick
moves an estimate.  (N) `ricci_flow_unif_existence`: **0%**, stated at
`Evolution/ExtendViaUniqueness.lean:80`, proof not started.  Whole HCG
compactness project: low single digits.

Next per §7.6: **A1a** (`c1_jet_tower`, new `DeTurck/LowRegC01JetTower.lean`), now
unblocked — it was gated on S0 only through the frontier's final signature, which
is now frozen.

## Planner update No. 110 (2026-08-03) - S0+E3 ACCEPTED (WITH TWO PLAN CORRECTIONS); A1a/A1b DISPATCHED

Acceptance: planner grep-verified the widened frontier — `hbridge` at
`LowRegAllOrderJet.lean:1063`, `hballU` at `:1074`, docstring now
states WHY the statement is false without them (H²∖H³ counterexample),
call site rewired, sorry census exactly 1, axiom census unchanged
(`lowreg_joint_smooth` still `sorryAx`-free).  The frontier is no
longer false; it remains 0% proved.  The forced `open … (symmS) in`
deviation is fine (per-declaration open is this file's convention).

Two PLAN CORRECTIONS from the E3 executor (neither counts toward the
route-error counter — plan-file inaccuracies caught at zero cost, not
landed mathematics):
1. §7.6's E3 target file was IMPOSSIBLE: `smoothCcToTensorHs` is
   defined in `DeTurck/DeTurckRemainderDefs.lean` (:90), which IMPORTS
   `Garding.EigenCombination` — the dependency runs opposite to the
   recon's assumption.  Landed at the true lowest home,
   `DeTurckRemainderDefs.lean:119`, as public `finiteEigenComboHs_eq`
   (20-letter budget).
2. The `:529` private clone had ZERO uses — the recon's use-census was
   substring-confused with the `gscr_` sibling.  Both clones deleted
   (`GalerkinParabolicEnergyDeTurck.lean` was unclaimed); one
   duplicate + one dead decl removed.

Two DESIGN NOTES recorded for G4 (from the executor's smell report):
- `hballU` constrains the LIMIT trajectory; `hbridge` fires on the
  radius-`R` ball.  The Galerkin approximants' ball membership comes
  from NEITHER — it is exactly what R0's first-exit-time bootstrap
  must supply at the Galerkin level.  R0's option-2 ruling already
  anticipated this; G4 must NOT try to read the approximants' ball
  off `hballU`.
- Positive coherence: `finiteEigenCombo` IS a `SmoothCcTensor`, and
  E3's `finiteEigenComboHs_eq` is precisely the adapter that lets G4
  apply `hbridge` to Galerkin states.  S0 and E3 compose.

Tooling correction promoted to memory: `#print axioms` DOES print
through `lake-locked check` on this checkout (observed twice today);
the older "suppressed" note was over-general.  The exit-0-can-be-
stale caution stands unchanged.

Dispatch: A1a/A1b are OUT (new `DeTurck/LowRegC01JetTower.lean`;
TK1/TK2-verbatim Moser route, no resolvent commutator; fixed-order-2
private proofs in the read-only action file as reference; one
time-boxed de-gating probe of
`RicciConnDiffOrder1TameEnvelope.lean:1240` permitted; scope excludes
A1c/A1d).  Queue after: A1c `a1_ladder` + A1d `n_diff_hm_rung`
(`LowRegLadderRung.lean`), floor bricks B3/B4/B5 opportunistically.

Honest denominators: unchanged (F6 ≈ 72%, front 2 ≈ 53%, (N) 0%,
machinery ≈ 92%, whole project low single digits).  Route-error
counter: 1/3.

---

## Executor report — bricks A1a + A1b: NOT DONE.  §7.4's "TK1+TK2 verbatim" route is REFUTED (2026-08-03)

**Lead with the failure.**  Neither tower's estimate was proved.  `c1_jet_tower`
and `c0_jet_tower` are stated in exactly `c2_jet_tower`'s shape and are *derived*
from two integrand-level lemmas, `low1Ker_jet` and `selfLow_jet`, each of which
carries one `sorry`.  The reason is not a stuck tactic: **the `IsMoserWin`
vocabulary of `LowRegOpJetWindows.lean` cannot express these summands at all.**

### Why the prescribed route does not exist

A Moser window carries an order-0 *fibre cap* `S` next to its affine jet
envelope, and the product step `moserWin_appRS` is `appRS_hn_sup`, which
**requires a fibre cap on both factors** — it is Gagliardo–Nirenberg
interpolation, `exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le`
(`RemainderCoeffPerOrderJetEnvelopes.lean:862`) takes `ΛS` *and* `ΛT`.

Both `C0` and `C1` contain the **bare connection difference**
`connDiffSection gm g` (equivalently `connDiffLoweredCc`), which is `∇P`:

* `C1`: `linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS` factors it as
  `appCcRS(ricciCometricFourTraceCastG0 g gm, linearizedRicciConnDiffOrder1KernelField g gm)`
  (`RicciConnDiffOrder1TameEnvelope.lean:116`, public), and the kernel splits into
  five permuted copies of
  `connDiffContrInsertionField g gm = reindex(slotExtend²(connDiffSection gm g))`.
  *That split is `private` in three places* — `ricci1_split`
  (`DeTurckRemainderLowBaseAction.lean:12380`) and two copies of
  `kernelField_eq_neg_arm_combination` (`LieFieldJetL2Summed.lean:136`,
  `RicciConnDiffOrder1TameEnvelope.lean:738`) — so it needs promotion or
  re-derivation as part of the currency brick.
* `C0`: even *after* the Palatini refold `lieCov_residual`
  (`RiemannCoefficientPalatiniRefold.lean:9176`), the residual
  `lieCovR4 ⊃ lcvQuad ⊃ lcvQA/lcvQB ⊃ lcvOmega =
  appCcRS(slotInsertEndoCc(fullRaisedEndoField gm g), domDomCongr(connDiffLoweredCc g gm))`
  still contains it.

`∇P` has **no** order-0 fibre bound from `δ ≤ 1/3` — the fibre certificate caps
`P`, not its derivative.  Grep-confirmed: every `*_order0sup_*` producer for a
`∇P`-carrying object (`connDiffContrInsertionField_order0sup_…:982`,
`linearizedRicciConnDiffOrder1KernelField_order0sup_…:1240`,
`raisedKoszul_order0sup_…`) is **ball-based**, because the sup is obtained by
Sobolev embedding *from the ball*.  The only radius-free `order0sup` producers
are for metric-algebraic objects (`cometricCastG0_order0sup_jetL2_radiusFree`).

This is not what TK3 faced.  `topKer_jet`'s three summands are metric-algebraic
times `symmS g T` — the C2 refold pushes *every* connection difference into
curvature and pair traces.  The C2 arm is the coefficient of `∇²` and is
algebraic in the metric; the C0/C1 arms are quadratic in `∇P` and are not.
§7.4's "SAME mechanism, strictly easier" reads the derivative *count* correctly
and the *cap availability* incorrectly.

**Right currency (already in the tree, wrong packaging).**  Every `∇P`-carrying
family has a radius-free per-order engine built on
`antidiagonalTupleGrid_integral_radiusFree`, in which the only capped object is
`P` itself and all higher jets sit inside a combinatorial grid integrated once.
`connDiffSection_lowOrder_jetL2_radiusFree` (`DeTurckVFJetRadiusFree.lean:581`)
is ball-free, affine, and **sharp** at `range (i+2)`.  Its gate
`2·finrank ℝ E + 10 ≤ a` is on a *free internal* order parameter and costs
nothing — `moserWin_sharp` already exploits exactly this.  Two gaps remain:
(i) the public *composite* producers `lieCorr0Field_perOrder_l2_radiusFree`
(`LieCorr0CoeffDiffRadiusFree.lean:3104`) and
`deTurckLieCoeffField_perOrder_l2_radiusFree`
(`DeTurckLieCoeffDiffRadiusFree.lean:273`) are **top-separated at `+2`**, one
order above the tower budget — their `Atop` terms are precisely the heads that
cancel at the tensor level, so the assembly must go through the *pieces*;
(ii) the sharp pieces are `private` (`lc0Base/lc0Diff/lc0Riem/lc0VBAMix_perOrder_rf`),
and the two `lc0*` ones are stated at `range (i+3)`, one order lossier than
their fixed-order-2 siblings already achieve (`lc0VB_h2_rf` reaches order 2 from
`lowJetSq g 3 P`), so the loss is slack, not mathematics.

### Probe outcome: gate is LOAD-BEARING, probe abandoned (~20 min)

`linearizedRicciConnDiffOrder1KernelField_order0sup_perOrder_l2_tameEnvelope_generic`
(`RicciConnDiffOrder1TameEnvelope.lean:1240`) forwards `ha_super` to
`connDiffContrInsertionField_…_generic` (`:982`), which **consumes it twice** —
`antidiagonalTupleGrid_integral_ballUniform_tameWindow g₀ a ha_super hR` and
`deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow g₀ a ha_super`
— and the statement is additionally **ball-based**: `hPball` enters the pointwise
constant `Λ2 = fr²·CA 0·(1 + Cemb²(a+2)R²)`.  Not the `appCc_cap_hs_le`
forwarded-only pattern.  No de-gating is available here.

### What did land (sorry-free)

New `Analysis/Spectral/Intrinsic/DeTurck/LowRegC01JetTower.lean` (+ `.md`):

* `selfLow_split` — **public re-derivation of the private `selfBase_decomp`**
  from public API only (`selfLow_good`,
  `deTurckLieCoeffField_eq_covDerivArm_add_endoArm`, `tail_base_split`).  This is
  the cancellation-preserving grouping
  `rhsSelfLow = (-2)•ricciGoodLow + (deTurckLieCovDerivArmField − edgeLiePairFam)
  + lc0VB + lc0AMix + lc0Riem`.  It matters because the *literal* summands of
  `rhsSelfLow` each cost **two** derivatives of the state; a frontier stated on
  them at `range (i+2)` would be FALSE.  A1b's five honest sub-frontiers are the
  five summands of this identity.
* `c1_jet_tower`, `c0_jet_tower` — both towers in `c2_jet_tower`'s exact shape
  (constants before the state, `range (i+2)`, `δ ≤ 1/3` the only smallness
  input, inert `H^{a+2}` ball).  The path-integral passage (`path_jetL2_le` +
  `Real.sqrt` bookkeeping + `c0_eq`/`c1_eq`) and the `phiMetCurvCoeff` constant
  summand are real and sorry-free; only the integrand windows are open.
* `jetNeg`, `jetAdd` promoted into `LowRegOpJetWindows.lean` (canonical home,
  next to `jetSub`); `moserWin_add`'s inline copy of the sum bound replaced by
  `jetAdd`, and it gained the now-required `omit [BoundarylessManifold I M]`.
  (`c0_jet_tower` deliberately routes through the *pre-existing* `jetSub` so it
  verifies against the current oleans — see the tooling note.)

### Consumer signature A1c should target

`a2_ladder` (`LowRegLadderRung.lean:232`) with the top term deleted, `.a2 → .a1`,
`m+2 → m+1`, and the `κ` binder dropped:

```lean
theorem a1_ladder (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 3 ≤ a)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) (hT : … symmetry …)
        (hδg : …) (hδZ : …),
        ‖smoothCcToTensorHs g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ m : ℕ, ‖smoothCcToTensorHs g₀ (m : ℝ) ((lowBaseData g₀ g₀ T … ).a1 T)‖ ≤
          Clower m * ‖smoothCcToTensorHs g₀ ((m : ℝ) + 1) T‖
```

### Verification and tooling

Focused check green for `LowRegOpJetWindows.lean` (its one new
`unusedSectionVars` warning fixed).  **Tooling blocker**: the targeted olean
refresh `build +…LowRegOpJetWindows` failed **twice**, the second time after a
single `lean` process reached ~7 GB and free RAM hit 252 MB on this 16 GB box.
The heavy module is
`Spectral/Tensor/CovGrad/CurvatureCoefficientDifferenceJetTower.lean`
(15 111 lines); its olean had to be rebuilt because **E3's edit to the low module
`DeTurckRemainderDefs.lean` invalidated the whole downstream chain**, exactly as
the E3 executor warned.  Killing the OOMing process left that olean deleted, so a
rebuild of that one module was required before anything downstream could be
checked again.  Any lane touching this subtree should expect the same and budget
for it.

### Honest denominators

**No estimate was proved.**  `low1Ker_jet` and `selfLow_jet` are 0%.

* A1a (`c1_jet_tower`): tower + path layer + probe + route diagnosis done,
  estimate 0% ⟹ brick ≈ **15%**.
* A1b (`c0_jet_tower`): same plus `selfLow_split` (the non-obvious part — the
  cancellation grouping) ⟹ brick ≈ **20%**.
* **F6: revise DOWN to ≈ 70%.**  The remaining work is no longer "one real
  estimate on a stocked route"; it now provably contains a *currency* brick
  (radius-free siblings of
  `connDiffContrInsertionField_perOrder_l2_topSeparated_generic` and of
  `deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform`, plus
  promotion/sharpening of four `private lc0*_perOrder_rf` lemmas) that §7.3's
  itemization did not contain.
* Front 2 ≈ 53%, (N) `ricci_flow_unif_existence` **0%**, machinery ≈ 92%, whole
  HCG compactness project low single digits — all unchanged.
* **Route-error counter: still 1/3.**  §7.4's route verdict is refuted, but no
  false *theorem* was landed; this is a plan-file prediction corrected before any
  session was burned proving an unprovable goal.  Planner should mark §7.4's
  "TK1+TK2 verbatim" and its `range (i+2)` slack argument as REFUTED and re-scope
  §7.6 rows A1a/A1b behind a new currency brick.

## Planner update No. 111 (2026-08-03) - A1a/A1b PARTIAL ACCEPTED; §7.4 REFUTED; ROUTE ERROR 2/3 (OVERRIDING EXECUTOR); A1-CUR QUEUED

Process note first: the harness process exited while the A1a/A1b
executor was waiting on an olean rebuild, leaving (i) a stale
elaboration lock (dead pid 8964) — REMOVED manually (the script has no
release verb for elaboration locks; this was this lane's own dead
build); (ii) two stale file claims of this lane (`LowRegOpJetWindows`,
`LowRegC01JetTower`, dead pid 12048) — released via
`release -Force -Files`; (iii) other lanes' five stale claims — LEFT
IN PLACE per the never-force-release-others rule; (iv) the
`CurvatureCoefficientDifferenceJetTower` olean deleted by the killed
OOM build — serial `-LeanThreads 1` rebuild RUNNING now.  Until it
lands and `LowRegOpJetWindows` is refreshed and `LowRegC01JetTower`
gets its first clean focused check, the A1a/A1b landings are
PROVISIONAL (the executor's focused check covered `OpJetWindows` only).

Acceptance of the partial: the tower statements (`c1_jet_tower`,
`c0_jet_tower` in `c2_jet_tower`'s exact shape, derived over the two
integrand sorries `low1Ker_jet`/`selfLow_jet`), `selfLow_split` (the
cancellation-preserving public regrouping — load-bearing: a frontier
on `rhsSelfLow`'s LITERAL summands at `range (i+2)` would be FALSE,
each literal summand costs two state derivatives), the path layer,
and the `jetNeg`/`jetAdd` promotions are ACCEPTED as stated, subject
to the pending verification chain.  The de-gating probe was run and
correctly abandoned (gate load-bearing: `ha_super` consumed twice +
ball-based pointwise constant).

**ROUTE-ERROR RULING: counter 2/3.**  The planner OVERRIDES the
executor's "still 1/3".  Reasoning: §7.4 was not a mere plan-file
remark — it was RATIFIED by planner No. 108 and an implementation
session was dispatched on it and partially burned (brick yield
15–20%).  Route error No. 1 (the false `lowreg_spatialMass`) was
counted even though caught pre-dispatch, because it was landed and
frozen; a ratified-and-dispatched impossible route counts a fortiori.
The executor's mitigation is real (the session converted into a deep
route diagnosis + correct tower statements + `selfLow_split`, and no
false mathematics landed) and is recorded, but mitigation does not
zero the count.  Root cause, for the lessons file: the §7 recon
verified the a₁-arm's summand DECOMPOSITION against proofs but not
the CAP AVAILABILITY of each factor — `IsMoserWin` products need
order-0 fibre caps on BOTH factors (`appRS_hn_sup` is
Gagliardo–Nirenberg), and `δ ≤ 1/3` caps `P`, never `∇P`.  The C2 arm
was special because the refold made it metric-algebraic; C0/C1 are
quadratic in `∇P`.  ONE more genuine route error ends this run per
the user's stop-condition.

Consequences applied:
- `F6_ESTIMATE_RECON.md` §7.4 marked REFUTED by planner annotation
  (pointer to the A1a/A1b executor report); §7.6 rows A1a/A1b are
  re-scoped behind the new currency brick.
- **A1-CUR (next Lean dispatch, after the verification chain)**:
  radius-free per-order currency for the `∇P`-carrying families, per
  the executor's inventory — (i) radius-free siblings of
  `connDiffContrInsertionField_perOrder_l2_topSeparated_generic` and
  `deTurckLieArm1Coeff_realizedFam_jetL2_perOrder_ballUniform`, built
  on `antidiagonalTupleGrid_integral_radiusFree` with
  `connDiffSection_lowOrder_jetL2_radiusFree`
  (`DeTurckVFJetRadiusFree.lean:581`, ball-free, sharp at
  `range (i+2)`, free-internal gate) as the base; (ii) promotion or
  public re-derivation of the four `private lc0*_perOrder_rf` pieces,
  sharpening the two `range (i+3)` ones to `range (i+2)` (slack, not
  mathematics — `lc0VB_h2_rf` already reaches order 2 from
  `lowJetSq g 3 P`); (iii) assembly through the PIECES, never the
  `+2` top-separated composites (their `Atop` heads cancel at the
  tensor level); (iv) the private splits `ricci1_split`
  (`…LowBaseAction.lean:12380`, READ-ONLY file — re-derive publicly,
  `selfLow_split` is the template) and `kernelField_eq_neg_arm_…`
  (two copies) re-derived or promoted at their canonical homes.
  Endpoint: prove `low1Ker_jet` and `selfLow_jet`; the two towers
  then go sorry-free with no statement change.

Honest denominators: F6 revised DOWN to ≈ 70% (the remaining work now
provably contains the A1-CUR currency brick that §7.3's itemization
missed).  Front 2 ≈ 53%.  (N): 0%.  Machinery ≈ 92%.  Whole HCG
project: low single digits.  **Route-error counter: 2/3.**

## Planner update No. 112 (2026-08-03) - MACHINE BSOD ROOT-CAUSED; MONOLITH WALL RULED: SPLIT (C0Core RECIPE); SPLIT BRICK DISPATCHED

Incident: the machine BLUE-SCREENED (bugcheck 0x10E, reboot 14:39)
during the `CurvatureCoefficientDifferenceJetTower` olean rebuild.
Event log: FIVE Resource-Exhaustion warnings today, every one
`lean.exe` elaborating THIS module at ~18 GB virtual commit; the fatal
episode ran without a watchdog alongside ~13 GB of app commit and
exhausted the fixed 35 GB commit limit (RAM 15.46 + pagefile 20).

Refined diagnosis from the controlled retry (fresh boot, watchdogged):
killed at `physFree = 0.25 GB` with `commitFree = 19.25 GB` — on a
clean machine the BINDING constraint is PHYSICAL memory (the module's
active working set exceeds total RAM → thrash floor), not commit.
Consequences: (i) enlarging the pagefile is NOT a fix (prevents the
BSOD mechanism but leaves a thrashing, impractical build); (ii) this
15,111-line monolith simply cannot be elaborated as one unit on this
16 GB machine.

RULING: dissolve the wall by the policy-mandated SPLIT — the file is
5x over the project's 3000-line cap, it is unclaimed and unmodified,
its entire upstream replays cheaply (the crashed build reached
[2970/3008] on replays alone), and the C0Core precedent (ledger
PLAN2 No. 91: 12.3k-line monolith, same OOM, 14 chunks, all green,
public endpoint preserved) is directly on point.  Split brick
DISPATCHED: ≤2500-line chunks at section seams, original path becomes
a pure umbrella (downstream imports unchanged), bottom-up chunk
verification, then the two blocked steps — targeted
`+LowRegOpJetWindows` refresh and `LowRegC01JetTower`'s FIRST clean
focused check (expect exactly the two integrand sorries).

Standing machine-safety protocol (all future lanes): NEVER build this
monolith intact (moot after the split); any build that can touch a
heavy module runs under the dual watchdog (kill lean at
commitFree < 3 GB OR physFree < 0.35 GB); trim working sets before
heavy builds; stale elaboration locks after a crash are removed
manually (script has no verb).

Route-error counter: UNCHANGED at 2/3 — this is a
performance/tooling wall (a sanctioned separate failure category),
not a mathematical route error.  Honest denominators: unchanged
(F6 ≈ 70%, front 2 ≈ 53%, (N) 0%, machinery ≈ 92%, whole project low
single digits); this brick is 0% new mathematics.

## Planner update No. 113 (2026-08-03) - A1-CUR RECON ACCEPTED; selfLow_jet FALSE AS STATED (ADJUDICATION SENT TO USER); C1 SMALL-BRICK READY

The A1-CUR design recon returned (`ShortTime/A1CUR_PLAN.md`, 403
lines).  Planner spot-verified before accepting: `selfLow_jet`
(`LowRegC01JetTower.lean:157-175`) is confirmed BALL-FREE (binders =
T, symmetry, δ bounds, hδg/hδZ, i, s only), and `lc0VB_h2_rf`
(`…LowBaseAction.lean:8025`) is confirmed a `private`,
3.2M-heartbeat fixed-order member — the recon's refutation of the
A1a/A1b executor's "(i+3) is slack" claim stands (the witness's
conclusion is QUINTIC in the jet, a different currency).

THE FORK RESOLVES PER ARM:
- **C1 (`low1Ker_jet`): ball-free is CORRECT — small brick.**  C1 is
  LINEAR in `∇P` (five permuted `connDiffContrInsertionField` copies
  per `ricci1_split` + three `lieArm1Piece`s); the radius-free
  engine (`wOmega = appCc(cometricCastG0, wXi)` shape) already lands
  at `range (i+2)` ball-free.  No statement change.  A1-CUR-1 ≈ 1
  session, full handoff in A1CUR_PLAN.md §7.
- **C0 (`selfLow_jet`): FALSE AS STATED.**  Two of `selfLow_split`'s
  five summands are QUADRATIC in `∇P` (`ricciAAArm` inside
  `ricciGoodLow`, `EdgeRicciPairing.lean:227`; and `lc0VB`).  With
  only `‖P‖_∞ ≤ δ`, the `range (i+2)` budget fails at `i = 0`
  (concentrating-bump counterexample: `‖T‖, ‖∇T‖ → 0` in `L²` while
  `‖|∇T|²‖_{L²} → ∞`); corroborated by the tree itself — every
  radius-free engine over a C0-shaped object is top-separated at
  `+2`.  REPAIR (recon option (a), planner-ratified): thread the
  inert `H^{a+2}` ball — already bound by `c0_jet_tower` and
  DISCARDED at the application site (`:295`, used `:313`) — into
  `selfLow_jet`'s statement; the needed Sobolev gate is `a ≥ 1` in
  dim 3, covered by the consumer's existing `3 ≤ a`.  Statement
  surgery, zero proof cost, the S0 pattern.  Do NOT inherit the
  `a ≥ 16` gate of the ball-based `order0sup` producers.
- Piece decisions accepted: PROMOTE the four `lc0*_perOrder_rf`
  (`LieCorr0CoeffDiffRadiusFree.lean:113/164/258/3061`) to a new
  sibling `LieCorr0PieceRadiusFree.lean` (source file is 3410 lines,
  over the cap); PUBLIC RE-DERIVATION of `ricci1_split` (~25 lines,
  no private API); promote the `LieFieldJetL2Summed.lean:136` copy of
  `kernelField_eq_neg_arm_…`, delete the TameEnvelope duplicate.
  Flat ball-uniform producers CANNOT discharge the towers (gated
  `i ≤ a` vs the ungated `∀ i` consumer) — recorded.

**ROUTE-ERROR ADJUDICATION — SENT TO USER (counter held at 2/3
pending their ruling).**  The question: does the false-as-landed
`selfLow_jet` count as route error 3/3 (triggering the user's stop
condition) or as the statement-level RESIDUE of error No. 2?
Planner's recommendation: residue (stay 2/3).  Reasons: same root
cause as No. 2 — ruling No. 104's ball-free doctrine (correct for
C2) was over-extended to the C0/C1 arms by §7.4 AND by the planner's
own A1a/A1b dispatch text, which explicitly mandated "δ ≤ 1/3 as the
only smallness input, ball-free" for both towers; the executor
followed instructions.  Caught within hours by the campaign's own
next design pass, pre-dispatch, zero-cost repair.  Counter-argument
(for 3/3, presented to the user): structural identity with error
No. 1 — a false sorry'd frontier statement landed in the tree.
No new estimate dispatch until the user rules.

Honest denominators: **F6 revised DOWN again to ≈ 60%** (A1-CUR-2 is
3–4 sessions of real estimate work; A1-CUR overall ≈ 10% done).
Front 2 ≈ 50%.  (N): 0%.  Machinery ≈ 92%.  Whole HCG project: low
single digits.

## Planner update No. 114 (2026-08-03) - USER RULING: COUNTER RESET TO 0/3; SEMANTICS CLARIFIED; CAMPAIGN CONTINUES

The user ruled on the No. 113 adjudication: **reset the route-error
counter to 0/3.**  Clarified semantics (record for all future
sessions): the three-error stop-condition is a DRIFT GUARD for
unattended stretches — "这个计数只是为了你在我不在的时候不跑偏太多" —
not a cumulative campaign score.  When the user is present they
re-adjudicate and may reset; counting restarts from each reset.  The
falseness findings themselves (spatialMass, §7.4, selfLow_jet) remain
fully recorded in Nos. 108/111/113 regardless of the counter.

Standing plan unchanged and now unblocked: option-(a) C0 repair
(thread the inert ball into `selfLow_jet`) stays ratified; when the
split brick releases the Lean slot → dispatch ONE executor for
[`selfLow_jet` ball-threading surgery + A1-CUR-1 (C1 radius-free,
A1CUR_PLAN.md §7 handoff)] (same-file bundle), then A1-CUR-2 (C0
estimate, 3–4 sessions) after.  Route-error counter: **0/3**.

## Executor report — CCDJT monolith split (No. 112 brick) (2026-08-03)

**0% new mathematics.**  Every one of the 245 declarations moved
verbatim, statement AND proof.  This is the compile-stabilization
brick that unblocks the A1-CUR estimate work; `(N)` remains 0%.

### Result

`CurvatureCoefficientDifferenceJetTower.lean` (15111 lines) is now a
pure umbrella — module docstring plus imports of 15 chunk modules in
`CovGrad/CurvatureCoefficientDifferenceJetTower/`.  All eleven
downstream consumers are untouched: the 78 public declarations keep
their exact names at `Integral.Connection`, so import transitivity
re-exports the whole API.

Recipe as ruled (C0Core, PLAN2 No. 91): each chunk repeats the
monolith preamble verbatim; `private ` is stripped from the 167
internal declarations, which are wrapped in an internal
`namespace CurvatureCoefficientDifferenceJetTower` that each chunk
`open`s, so the public namespace is unpolluted.  A collision scan
before promoting found only two names shared with
`Analysis/Sobolev/AntidiagonalTupleProductGrid.lean` — in
`DifferentialGeometry.Combinatorics`, which this module does not open
— plus the `iteratedCovGrad_smul_pt/_b` copies already queued for
dedup; the internal namespace keeps all of them contained.  Fourteen
other files' same-named helpers were checked and are all `private` in
their own modules, so nothing outside the chunk directory is affected.

Content preservation was verified mechanically, not by eye: all 15051
body lines reappear verbatim and in order across the chunks, and the
245 declarations appear in identical order with identical names
(generator + checker: `.codex-scratch/ccdjt-split/{split,verify}.py`;
pre-split file kept as `*.before-split.lean`).

### Chunk map and verification

Full table, per-chunk contents, import DAG and memory figures:
`CovGrad/CurvatureCoefficientDifferenceJetTower.md`; brief per-chunk
notes sit beside each chunk.  Sizes 191–2306 lines.  Chunks 1–8 are the
linear spine (`Grid → Lowered → Palatini → PairTrace → TraceGrid →
Envelope → TsTransport → TsRungs`); the residual-integrator region is a
DAG branch off `Envelope`, with `ResidualCells` rooted directly on the
monolith's own 22 imports.

### The real finding: chunk sizing is per-declaration, not per-line

The ≤2500-line rule was necessary but nowhere near sufficient.  Three
things mattered more, and all three cost a failed build to learn:

1. **One declaration owns the peak.**
   `boundedFactorGrid_cappedTopLayer_integral_flat` alone drives the
   Lean working set from the ~3.2 GB import floor to ~7.8 GB, and every
   declaration elaborated after it in the same process inherits that
   high-water mark.  Halving line counts around it achieved nothing; it
   had to be alone in a 302-line file.  By contrast `ResidualCells` —
   823 lines holding BOTH heavy product-cell lemmas — builds in 51 s at
   3.5 GB.
2. **Import closure is part of the memory budget.**  A linear chunk
   chain charges every chunk for everything before it.  The hog needs
   exactly one thing from this module (`cappedTopLayerCell_integral_le`),
   so that lemma and its sibling were pulled into `ResidualCells`, which
   imports only the original 22.  Measurement: the ~3.2 GB floor IS
   those 22 imports and is irreducible; the chunk `.olean`s are noise
   beside it.
3. **Trim before the heavy build** (the No. 112 protocol step).
   `EmptyWorkingSet` across all processes returned ~0.5 GB, and that was
   the entire margin: guarded, the hog then peaked at 7.78 GB with free
   physical bottoming at **0.44 GB**, just above the 0.40 GB floor,
   instead of being killed at 0.34 GB.

`ResidualFlat` therefore sits ~0.05 GB inside the safety margin on this
machine.  Anyone rebuilding it must trim first and run nothing else
concurrently.  Four separate attempts were killed by the watchdog
before the combination above cleared it; the floor was never relaxed.

Two mechanical traps in the source, worth remembering for the next
split: a doc comment containing a blank line (`pureTrace`), which
defeats a naive "walk back to the blank line" prelude finder; and a
dangling `set_option … in` separated from its command by a blank line
(old line 7138), where a chunk boundary severs the modifier from its
command.  Also: the first inter-chunk dependency scan used
`([^ ({:\[]+)` to capture declaration names, which swallows the trailing
newline for any declaration whose name ends its line — it silently
reported the hog as depending on nothing.  Exclude `\r\n`, and strip
block comments before searching for uses.

### Concurrency note (not caused by this brick)

At 15:33:52, mid-brick, commit `7f54201cf "uniform existence consult"`
captured the in-progress split (nine chunk files at their then-current
content, including a `Residual.lean` that has since been re-split).  No
git write command was issued by this executor.  Another lane in this
shared worktree is committing automatically; the working tree is
correct and verified, but the committed snapshot is an intermediate
state and should be superseded by a commit of the final tree.

### Honest denominators

Unchanged by this brick: `(N)` stated, proof 0%; F6 ≈ 70%; front 2
≈ 53%; machinery ≈ 92%; whole HCG compactness project still low single
digits.  This entry moved compile health only.

## Planner update No. 115 (2026-08-03) - SECOND PRO RULING INTEGRATED: ARCHITECTURE VIABLE, NO ITEM UNSOUND; PAPER BRICK P-STOP NOW GATES THE GALERKIN LANE

The user submitted the design-review consult (`CONSULT_UNIF_N_REVIEW.md`)
and brought back the referee verdict.  Recorded as
`ShortTime/UNIF_N_PRO_RULING2.md` (NOTE: `UNIF_N_PRO_RULING.md` is the
FIRST ruling, 2026-07-22 R1τ — a filename collision was caught before
overwrite; the ruling files now mirror the ledger volume convention).

Verdict: **architecture VIABLE, not yet closed; nothing UNSOUND.**
R-1 (floor deletion) SOUND — externally closes the No. 106 design.
G-1 (DeTurck→Ricci conversion) SOUND — Phase C is mathematically clear.
R-2/R-3/R-4/R-5/R-6/G-2 SOUND-WITH-CAVEAT with named smallest repairs.
Dominant risk confirmed = Galerkin bottom-scale bootstrap +
identification with the A1 fixed point (R-2 + R-4).

INTEGRATION (queue and spec changes):
1. **NEW MANDATORY PAPER BRICK "P-STOP"** (Pro's item (i)) — the
   stopped, projected bottom-scale energy proposition in its full
   quantitative form (c* independent of N and rung; no inverse
   inequalities; top-energy coefficients from already-closed LOWER
   norms — the true cap is `‖∇P‖_∞`/H³, never let the nominal H⁵ ball
   into coefficients; per-datum high norms on the RHS only; STRICT
   improvement Φ < R₀²/2 with T = τ₀ from class data; compactness +
   uniqueness for identification).  Folded into P-STOP: R-3's
   non-cancellation check (one frozen-symbol/single-component test that
   the total quadratic `∇P·∇P` C0 symbol is nonzero) and R-5's
   absorption exposure (`δ* = min{1/3, δ_abs(κ, c_par)}`, trajectory
   operator-bound cap moves to δ*; display the pairing algebra once —
   `C(m)` must land on `E_m`/`E_{m−1}`, never on `D_m` or superlinear).
   **P-STOP GATES E1′a/E1′b/E4/G4** — no further Galerkin Lean until it
   is written and verified on paper.  Owner: planner (consult re-check
   if it resists).  If P-STOP holds in the stated form, R-2 + R-4 +
   most of R-5 close together; if false, the Galerkin route is dead as
   designed (Pro's words) and we re-consult BEFORE building.
2. R-4 spec change for G4: ONE approximant sequence and ONE limit for
   all rungs σ (diagonal + uniqueness); the H¹/C⁰ uniqueness chain is
   PART of A2 — add a hypothesis-match audit (uniqueness chain vs the
   Galerkin limit class) to the G4 handoff.
3. R-6 sharpens front-3 G3 into the declaration-by-declaration
   transport audit: every LOW-RUNG constant in the τ₀/radius formulas
   depends only on `(gBase, Λ, ∇_{gBase}^{≤3} g₀)`; per-datum high
   norms only in a-posteriori constants.
4. G-1 opens a new statement-level lane item **PHASE-C**: DeTurck
   vector-field flow + pullback + glue over T < τ₀, sign convention
   fixed, one-sided derivative at t = 0 — mathematically cleared;
   sequence after the A2/A4 endpoints exist.
5. G-2 adapters recorded: rebasing explicitness (the campaign IS the
   `g₀ + u` route — document it in the architecture statement);
   finite-chart transfer adapter; a.e.→representative plumbing
   (exists, conditional on `lowreg_spatialMass`); Icc-solve/Ico-state
   harmless; no measurable selection; no class compactness.
6. **Standing stop-signal list adopted** (RULING2 §(ii), ten signals) —
   every future Galerkin/A1-CUR brick handoff carries it verbatim.

Queue after integration: [in flight: split verification tail] →
[`selfLow_jet` ball-thread + A1-CUR-1] (unchanged; R-3 ratifies both) →
**P-STOP (paper, planner)** → A1-CUR-2 (C0, carries the
non-cancellation certificate) → B3/B4/B5 opportunistic → E1′ (with δ*)
→ E4 → G4 (with the identification audit) → Z → A4 wiring → front-3
transport audit → PHASE-C → (N) assembly.

Repo-hygiene note: commit `7f54201cf` (15:33, user-side, made to push
the consult evidence) froze a MID-SPLIT intermediate tree.  Once the
split verification tail is green, the user should make a fresh commit
of the final tree to supersede it.

Honest denominators: the verdict proves nothing new — percentages
unchanged (F6 ≈ 70% per the split report's baseline, A1CUR-adjusted
≈ 60% per No. 113; front 2 ≈ 50–53%; (N) 0%; machinery ≈ 92%; whole
project low single digits) — but the mathematical risk is now
externally triaged: ONE paper proposition stands between the campaign
and the entire remaining Galerkin lane.  Route-error counter: 0/3.

## Planner update No. 116 (2026-08-03) - MACHINE BSOD No. 2; USER RULING: NO MORE LEAN TODAY; SPLIT TAIL FROZEN AT 5 CHUNKS; P-STOP STARTS

Incident: SECOND bugcheck `0x0000010e` at 16:45 (Resource-Exhaustion
2004 events at 16:26/16:42, `lean.exe` again).  Trigger chain: the
resumed split executor RE-SPLIT the Residual region at 16:07
(invalidating the already-built hog olean), then ran the rebuild
directly through lake-locked — OUTSIDE the planner's dual-watchdog
wrapper — and commit exhaustion crossed the fixed 35 GB ceiling.
The harness process died with the machine; the executor never
appended a phase-2 report.

Salvage state (verified by filesystem inventory, no Lean run):
- 10/15 chunk oleans VALID: spine 1–8 (`Grid → … → TsRungs`, built
  15:16–15:33) + `ResidualCells` (16:09) + `Residual` (16:12).
- MISSING: `ResidualBase`, `ResidualFlat` (the 7.78 GB hog),
  `ResidualFree`, `ResidualWindow`, `ResidualAllOrd`; then the
  umbrella olean; then `LowRegOpJetWindows` refresh (its olean is
  stale, 11:17 pre-E3) and `LowRegC01JetTower`'s first focused check.
- Hog census: `ResidualFlat.lean` holds exactly ONE declaration
  (`boundedFactorGrid_cappedTopLayer_integral_flat`, :57) with exactly
  ONE consumer (`ResidualWindow.lean:85`) — LOAD-BEARING, cannot be
  orphaned from the umbrella.  It must elaborate once more (its
  phase-1 build cleared at 7.78 GB peak / 0.44 GB floor after trim
  with nothing else running — reproducible conditions).
- Locks: this lane's five dead claim tokens + the dead elaboration
  lock force-released/removed; other lanes' stale claims untouched
  (note: PID-reuse after reboot can make a dead claim display
  "running" — ownership is decided by the claim record, not the pid).

STANDING RULE (added to the No. 112 protocol): any build in the
CCDJT subtree runs ONLY through the planner's dual-watchdog wrapper
(commit-free < 3 GB OR phys-free < 0.35 GB ⟹ kill lean); executors
may not invoke raw lake-locked builds there.

USER RULING: no further Lean today.  The 5-chunk tail + umbrella +
OpJetWindows refresh + C01 check are FROZEN pending a user-chosen
quiet window (options presented: pagefile 20→32 GB raise recommended
to make the BSOD mechanism unreachable; watchdog-only also viable).
Meanwhile the campaign advances on the ZERO-LEAN track: the planner
writes P-STOP (`ShortTime/PSTOP_PROPOSITION.md`, per No. 115 /
RULING2 item (i)) — the stopped projected bottom-scale energy
proposition that gates E1′/E4/G4.

Honest denominators: unchanged ((N) 0%; F6 ≈ 60% A1CUR-adjusted;
front 2 ≈ 50%; machinery ≈ 92%; whole project low single digits).
Route-error counter: 0/3 (both BSODs are tooling/resource incidents,
not route errors).

SAME-DAY CORRECTION: the "no more Lean today" answer was a mis-click;
the user's actual ruling is "直接跑" — run the tail now, watchdog-
wrapped, no system-setting change.  Topo order established by import
scan: `ResidualFlat` (hog FIRST, at maximum free memory) → `Window` →
`Free` → `Base` → `AllOrd` → umbrella → `LowRegOpJetWindows` refresh,
one module per invocation, trim before each, dual watchdog
(commit-free < 3 GB OR phys-free < 0.35 GB ⟹ kill) on every step;
`LowRegC01JetTower` focused check follows separately.

## Planner update No. 117 (2026-08-03) - FIVE WATCHDOG KILLS = SQUEEZE PLATEAU; HOG PROOF-REFACTOR BRICK DISPATCHED

Retry campaign result: four planner-wrapped attempts (peaks
7.58 → 8.04 → 8.66 → 8.43 GB, kills at phys-free 0.07–0.27 GB; zero
BSODs — the wrapper held) after the agent-side kill.  The iterative
squeeze plateaued (start-free 7.35 → 8.12 → 9.09 → 9.24 → 9.54 GB
with nothing user-closable left: top consumers are svchost 0.91 GB
and the harness 0.75 GB).  CONCLUSION: the machine's effective runway
with the session ≈ 8.7 GB; the re-split `ResidualFlat`'s elaboration
peak exceeds it (the phase-1 "7.78 GB" figure belonged to the
PRE-re-split file with a different import closure — figures do not
transfer across re-splits; lesson recorded).

Structural response (dispatched): PROOF refactor of the single hog
theorem `boundedFactorGrid_cappedTopLayer_integral_flat` — statement
byte-unchanged; extract `hΛsup_low` (ball→pointwise sup),
`hGNv` (GN interpolation, constants passed as parameters to avoid
re-`choose`), and the GENERIC-in-`b` grid/integrability layer
(`hgrid_eq` + cell integrability — no tensor types, near-zero cost)
into sibling piece files; scope down the section-level
`backward.isDefEq.respectTransparency false` (:54) to only the
pieces that need it (prime suspect for the blowup, together with the
whole-grid `rfl` at :250).  Executor carries an embedded memory
guard on every build (mandatory), success criterion = reassembled
peak well under 6 GB, then completes the frozen chain (Window →
Free → Base → AllOrd → umbrella → OpJetWindows → C01 first check +
census).

Honest denominators: unchanged ((N) 0%; F6 ≈ 60%; front 2 ≈ 50%;
machinery ≈ 92%).  This entire №112–117 arc is compile-health
infrastructure — zero new mathematics.  Route-error counter: 0/3
(resource walls, not route errors).  P-STOP meanwhile at ≈ 65%
(§6 resolved on paper: self-dependent stopped-rung coefficients
REFUTED via the requirement-4 violation, forcing the tower-direct
jet-explicit pairing at rungs 3–5; remaining = write the rung-3..5
pairing + the §7 identification audit).

## Executor report — hog proof refactor (No. 117 brick) (2026-08-03)

VERDICT: **the hog is fixed and green**, and the diagnosis in the brick
was wrong in an instructive way.  `boundedFactorGrid_cappedTopLayer_
integral_flat` now checks at **3.09 GB / 19 s** and builds at
**2.86 GB / 17 s**, against ≥8.7 GB and five kills before.  The
statement is byte-identical — diffed both against the split file and
against `.codex-scratch/ccdjt-split/*.before-split.lean`.  The CCDJT
umbrella built for the first time since the split.  The chain then hit
an UNRELATED wall (below).

### What actually caused the blowup: one `ring`

The three extractions the brick ordered were done in full —
`hΛsup_low` → `ResidualFlatSup.jetSupLow`, `hGNv` →
`ResidualFlatGN.jetGNInterp` (constants as parameters, no re-`choose`),
the whole grid/integrability layer → the tensor-free
`Analysis/Sobolev/BoundedFactorGridIntegral` — and the section-level
`backward.isDefEq.respectTransparency false` was dropped entirely.
**That moved the peak 8.43 → 8.25 GB.  Still killed.**

Rather than extract more blindly, I bisected the declaration with
`sorry`-truncated copies in a scratch root module (six runs, ~20 s
each).  Every prefix — statement, all the `set` constants, the sup/GN
inputs, `set b`, integrability, the `cappedTopLayerCell_integral_le`
application, the grid→double-sum step, and calc steps 1–3 — sat at
**3.08–3.09 GB**.  Adding the last calc step, `by ring`, took it to
**7.95 GB and a kill**.  That `ring` was proving
`A * (B * C) = A * B * C`.  `(mul_assoc _ _ _).symm` closes it, and the
whole declaration lands at 3.09 GB.  One token, ~5 GB.

Mechanism (recorded in `lessons.md` and the chunk-map note): `ring`
identifies atoms up to reducible defeq, and `set`-introduced locals are
let-bound, so they zeta-unfold during that comparison.  The atoms
`gcount i` and `MB i ^ (9 * (i + 2))` unfold through `MB → vol, Lam,
Cgn` into a `dite` around `Exists.choose` of the Gagliardo–Nirenberg
existential, with a symbolic exponent preventing any collapse.  The
same `ring` survives in `jetSupLow`, where the locals are ordinary
parameters, and costs nothing.

RULE for the campaign: **bisect the declaration before splitting the
file.**  Line counts and "obviously heavy" blocks mislead; all three of
the brick's named suspects (the transparency escape, the whole-grid
`rfl`, the `.choose` constant) were innocent.  And never leave a
normalizer (`ring`, `ring_nf`, `field_simp`) below a `set` when the
goal is a fixed rearrangement — name the lemma.

### Verification chain (every build guarded; `-LeanThreads 1`; serial)

| step | result | peak |
|---|---|---|
| `Analysis/Sobolev/BoundedFactorGridIntegral` check / build | GREEN | 1.41 / 0.99 GB |
| `ResidualFlatSup` check / build | GREEN | 2.79 / 2.82 GB |
| `ResidualFlatGN` check / build | GREEN | 3.09 / 2.81 GB |
| `ResidualFlat` check / build (**the criterion**) | GREEN | 3.09 / **2.86 GB** |
| `+ResidualWindow` | GREEN | 3.43 GB |
| `+ResidualFree` | GREEN | 3.24 GB |
| `+ResidualBase` | GREEN | 3.18 GB |
| `+ResidualAllOrd` | GREEN | 3.17 GB |
| `+CurvatureCoefficientDifferenceJetTower` (umbrella) | GREEN | 2.81 GB |
| `+LowRegOpJetWindows` | **KILLED ×2** | 7.60 / 7.95 GB |

None of the four new/edited files needs
`backward.isDefEq.respectTransparency false`; no new `maxHeartbeats`
(the file-level 3200000 / 1600000 moved verbatim into each piece).

Axiom census, all six new/refactored declarations
(`boundedFactorGrid_cappedTopLayer_integral_flat`, `jetSupLow`,
`jetGNInterp`, `rfnsIterCont`, `bdFactorGrid_int_eq`,
`bdFactorCell_int`): exactly `[propext, Classical.choice, Quot.sound]`.
No `sorryAx`.

### THE NEXT WALL (not this brick's, and not caused by it)

`+LowRegOpJetWindows` rebuilt ~140 stale modules over 35 min and then
died on **`DeTurck/DeTurckRemainderTameLipschitz.lean` — 46,927 lines**,
peaking 7.60 GB (kill at 0.37 GB free), and again at 7.95 GB (0.31 GB)
on a trimmed retry.  It does **not** import the CCDJT tree at all
(`grep` count 0), so its staleness is the pre-existing E3
`DeTurckRemainderDefs` invalidation, not this refactor.  Its `.olean` is
now deleted (the standing kill hazard), so **`LowRegC01JetTower`'s first
focused check and the `c1_jet_tower`/`c0_jet_tower` census are blocked
behind it**.  Static census of that file meanwhile: exactly the two
expected `sorry`s, `low1Ker_jet` (:88) and `selfLow_jet` (:176).

That file is three times the size of the CCDJT monolith and is the
natural next split/refactor brick — and the first thing to try on it is
the cheap `sorry`-bisection above, not a split: the CCDJT lesson is that
a 5 GB excess can live in a single tactic call.

Two stale-lock notes: a guard kill leaves
`.lake/codex-locks/lean-elaboration.lock` owned by a dead pid, which
makes the next build refuse to start; `release -Force -Lake` does not
clear it (that releases the Lake lock), the lock directory has to be
removed once the owner pid is confirmed dead.

Honest denominators: unchanged.  **This is 0% new mathematics** — the
statement is byte-identical and nothing was proved that was not proved
before; it is compile-health infrastructure.  (N) 0%; F6 ≈ 60%; front 2
≈ 50%; machinery ≈ 92%.  Route-error counter: 0/3.

## Executor report — TameLipschitz memory probe (2026-08-03)

VERDICT: **no hotspot exists; the weight is DISTRIBUTED, and a split
ruling is required.**  `DeTurckRemainderTameLipschitz.lean` (46,927
lines) was measured, not edited — the file is byte-unchanged and no
statement was touched, because there is nothing local to fix.  The
`ResidualFlat` hypothesis (one runaway tactic holding several GB) is
**refuted for this file.**  The chain therefore remains blocked and
`LowRegC01JetTower` still has no first check.

### Probe map (each run under `lake env lean -M <cap>`, `-LeanThreads 1`, guarded)

| prefix (cut line) | peak lean WS | wall |
|---|---|---|
| 116 — imports/opens only | **3.51 GB** | 24 s |
| 2546 | 4.00 GB | 57 s |
| 2609 | 4.01 GB | 65 s |
| 5079 | 4.25 GB | 105 s |
| 8988 | 4.60 GB | 154 s |
| 12984 | 4.80 GB | 170 s |
| 16002 | 5.30 GB | 186 s |
| 20010 | 5.87 GB | 211 s |
| 23997 | 6.38 GB | 211 s |
| 26340 | 6.57 GB | 227 s |
| 36051 | **> 7.60 GB** (cap hit) | 276 s |
| whole file (solo `check`) | ≥ 8.20 GB, still climbing at kill | killed 292 s |

Zero errors in every probe.  The climb is smooth and monotone — **no
prefix jump anywhere**, which is precisely the stop condition the brick
named.  Two numbers carry the ruling: the **import closure alone costs
3.51 GB** (40% of the budget, 37 imports, before one line of this file
elaborates), and the file's own content adds a near-constant **≈ 0.117 GB
per 1000 lines**, projecting **≈ 8.8–9.0 GB** total against the ~8.7 GB
runway.  The file is 0.1–0.3 GB over the wall — which explains both why it
once built and why five squeeze attempts plateaued.  No tactic swap can
close a ~2 GB gap.

Two diagnostic traps worth recording.  A solo guarded check showed the
log frozen at line 2398 while memory grew 3.87 → 8.20 GB over four
minutes, which reads as "one stuck declaration at :2546"; a probe cleared
:2546 at 4.01 GB.  Lean's streamed stdout under `lake env lean` is
buffered and is **not** a position signal.  And peak memory must be summed
over all `lean`/`lake` processes — a `lake build` runs module jobs in
parallel, so the earlier "7.60 GB on TameLipschitz" from the
`+LowRegOpJetWindows` chain was a whole-machine figure that did not by
itself implicate this module.  (It does: solo it reaches ≥ 8.20 GB.)

### The split lever (data-driven, for the planner's ruling)

Best single move: **lines 10276–17800 — 187 private `nf_*` normal-form
lemmas, 7.5k lines, with ZERO geometric types** (grep-verified: no
`SmoothRiemannianMetric`, `SmoothCcTensor`, `TangentSpace`,
`iteratedCovGrad`, `riemannianFiberNormSq`, `appCc`, `unitModel`,
`ccTensorBilin`, `Manifold`, `ChartedSpace`).  They are pure
`Fin n → … → ℝ` index algebra with 20-hypothesis symmetry bundles and
6-fold nested `Finset.sum` chains.  Extracted to a standalone algebra
module they pay almost **none** of the 3.51 GB geometric baseline — the
same win as `BoundedFactorGridIntegral` in the CCDJT refactor, and the
only available change that *lowers* the baseline instead of dividing it.
This is also exactly what this file's own 2026-07-16 note already
demanded ("split that algebra into coefficient-layer modules").

Other clean boundaries: 116–3013 (Lie path-value layer); 3014–5074
(chart-open section); 5075–10275 (`O1Abstract`); **26571–30633
(`LieCorr0BoundsA`…`F4`, already delimited sections — cheapest mechanical
extraction)**; 30633–46925 (16.3k-line tail with no section markers).
Sizing: ~4 pieces of ~12k lines → ≈ 5.0/5.4/5.8/6.2 GB; ~5 pieces of
~9.4k lines → ≈ 4.6–5.8 GB.  Pull the `nf_*` algebra first.

### Chain outcomes

`+LowRegOpJetWindows` and the `LowRegC01JetTower` check were **not run**:
both sit behind this module's `.olean`, which is still absent, so they can
only reproduce the same kill.  No new monster was discovered in the
OpJetWindows chain because the chain was not re-entered.  Static census of
`LowRegC01JetTower.lean` (356 lines) is unchanged and as expected:
**exactly two `sorry`s, `low1Ker_jet` (:88) and `selfLow_jet` (:176)**;
`c1_jet_tower` (:196) and `c0_jet_tower` (:265) are present.  The axiom
census remains blocked behind the olean.

Honest denominators: unchanged, and **0% new mathematics** — this brick
produced a measurement, not a proof; nothing was proved, nothing was
edited.  (N) 0%; F6 ≈ 60%; front 2 ≈ 50%; machinery ≈ 92%; whole project
low single digits.  Route-error counter: 0/3 (a resource wall, not a route
error).

## Planner update No. 118 (2026-08-03) - HOG FIXED (ROOT CAUSE: ONE `ring`); CCDJT TREE GREEN; NEW BLOCKER = 46.9k-LINE TameLipschitz; PROBE DISPATCHED

ResidualFlat refactor ACCEPTED (planner spot-check: `mul_assoc` at
:206, zero `ring` residue; executor diffed the statement byte-identical
against both the split file and the pre-split backup; census clean).
The hog now checks at **3.09 GB / 19 s** (was ≥ 8.7 GB, five kills).

**ROOT CAUSE — promoted to a STANDING RULE.**  The extractions and the
`respectTransparency` removal moved the peak only 8.43 → 8.25 GB; the
executor then sorry-bisected the declaration and found the entire
blowup in ONE final-calc `by ring` proving `A*(B*C) = A*B*C`.
Mechanism: `ring` compares atoms up to reducible defeq, and
`set`-bound locals are LET-bound, so they zeta-unfold during that
comparison — here through `MB → vol, Lam, Cgn` into a `dite`-wrapped
`Exists.choose` of the GN existential.  Fix: `(mul_assoc _ _ _).symm`.
One token ≈ 5 GB.  RULE: in any context holding `set`-bound locals
that wrap `Exists.choose`/`dite`, do NOT use `ring`/`ring_nf`/
`nlinarith`-family tactics on goals mentioning those locals — use the
explicit rewrite, or `clear_value`/generalize the lets first.  (Same
root as the opacity-discipline heartbeat lesson; now shown to blow
MEMORY too.)  Diagnostic technique validated: sorry-truncation
bisection with ~20 s guarded probe runs — cheap and decisive; use it
BEFORE any split of a heavy file.

Piece map landed: generic `Analysis/Sobolev/BoundedFactorGridIntegral
.lean` (tensor-free, 1.4 GB) + `ResidualFlatSup` (2.8) +
`ResidualFlatGN` (3.1) + reassembled `ResidualFlat` (2.86 build).
`respectTransparency false` is GONE from ResidualFlat (no piece needed
it).  Chain: Window 3.43 / Free 3.24 / Base 3.18 / AllOrd 3.17 /
**umbrella 2.81 — the whole CCDJT tree is green for the first time
since the split**, axiom census exactly `[propext, Classical.choice,
Quot.sound]` on all six touched declarations.

NEW BLOCKER (pre-existing, exposed by the chain): the
`+LowRegOpJetWindows` refresh rebuilt ~140 stale modules, then died
twice (7.60 / 7.95 GB) on `DeTurck/DeTurckRemainderTameLipschitz.lean`
— **46,927 lines**, 3× the CCDJT monolith, no CCDJT import; stale
purely from E3's `DeTurckRemainderDefs` edit; its olean is now
deleted.  `LowRegC01JetTower`'s first check + the tower census are
blocked behind it (static census of C01: exactly the two expected
sorries `low1Ker_jet` :88, `selfLow_jet` :176).  DISPATCHED: probe
brick — pattern-scan for the ring/set-zeta family first, then
sorry-bisection on scratch copies, one-token-style fix if a hotspot,
STOP-and-report for a split ruling if the weight is distributed.

Honest denominators: unchanged; the №112–118 arc remains 0% new
mathematics.  (N) 0%.  Route-error counter: 0/3.

## Planner update No. 119 (2026-08-03) - TameLipschitz PROBE ACCEPTED (DISTRIBUTED WEIGHT); 4-CHUNK SPLIT RULED AND DISPATCHED

(Note: the probe's executor report was appended concurrently with
No. 118 — read entries by date, the interleaving is cosmetic.)

Probe accepted: NO hotspot — a clean prefix ladder shows the import
closure alone at 3.51 GB and content adding ≈0.117 GB per 1000 lines,
smooth and monotone (whole file ≥8.2 GB and climbing at the kill,
projecting 8.8–9.0 vs the ~8.7 runway — over the wall by only
0.1–0.3 GB, which explains its historical builds and the squeeze
plateau).  Zero edits made — correct per the stop condition; the
`ResidualFlat` precedent does not transfer.  Blocking status
CONFIRMED empirically: the `+LowRegOpJetWindows` build itself
attempted TameLipschitz (lake builds only the target's closure).

Two phantom-hotspot traps recorded (lessons.md): block-buffered
stdout under `lake env lean` freezes the log while memory climbs
(falsely accused a declaration the probe then cleared at 4.01 GB);
and peak memory must be SUMMED over all lean/lake processes — the
original "7.60 GB on TameLipschitz" was a whole-machine figure with a
parallel build.  New validated instrument: `lake env lean -M <cap>`
aborts an over-budget probe safely.

RULING: 4-chunk split, sized by the measured slope — each chunk
≤ ~15k lines ⟹ ≈5.3 GB peak (this file's weight is distributed, so
BIG chunks are safe; CCDJT needed fine chunks only because single
declarations spiked).  The tensor-free `nf_*` block (10,276–17,800,
187 private lemmas, zero geometric types) becomes its own MINIMAL-
import chunk (the baseline-lowering move the file's own 2026-07-16
note demanded); `LieCorr0BoundsA…F4` (26,571–30,633) is a natural
seam.  Umbrella preserves the import path; CCDJT recipe + tooling
reused; mechanical content-preservation verification mandatory.
Dispatched with the full chain tail: chunks → umbrella →
`+LowRegOpJetWindows` → `LowRegC01JetTower` first check + census.

Honest denominators: unchanged ((N) 0%; F6 ≈ 60%; front 2 ≈ 50%;
machinery ≈ 92%; the compile-health arc is still 0% new
mathematics).  Route-error counter: 0/3.

## Executor report — TameLipschitz monolith split (No. 118 follow-on brick) (2026-08-03)

VERDICT: **DONE, GREEN, and the frozen chain is unblocked.**
`DeTurckRemainderTameLipschitz.lean` (46927 lines) is now a pure umbrella over
**fifteen** chunk modules.  Worst single Lean process across the whole tree:
**5.26 GB** (the monolith was killed at ≥ 8.20 GB and still climbing).
`+LowRegOpJetWindows` rebuilt to completion (9593 jobs), and
`LowRegC01JetTower` got its **first check ever** — which found two pre-existing
syntax errors, now fixed; it is green with exactly the two expected `sorry`s and
its towers were censused for the first time.

**0% new mathematics.**  Every declaration moved verbatim, statement and proof,
with its `set_option … in` prelude; no `maxHeartbeats` was introduced; no
statement was touched.

### Chunk map (src lines / peak GB / wall s, guarded targeted builds, `-LeanThreads 1`)

| # | chunk | lines | peak | wall | imports |
|---|-------|-------|------|------|---------|
| 1 | `Base` | 4958 | 4.45 | 89 | *(orig 37)* |
| 2 | `O1Alg` | 1307 | **1.40** | 8 | *(7 Mathlib)* |
| 3 | `LieValue` | 3555 | 4.55 | 73 | Base, O1Alg |
| 4 | `M0Defs` | 810 | **1.51** | 13 | *(7 Mathlib)* |
| 5 | `M0Gen1` | 7046 | **2.62** | 39 | M0Defs |
| 6 | `M0Gen2` | 7514 | **2.48** | 23 | M0Gen1 |
| 7 | `Master` | 1216 | 3.76 | 41 | LieValue, M0Gen2 |
| 8 | `BoundsA` | 1860 | 4.14 | 49 | Master |
| 9 | `BoundsB` | 2244 | **5.26** | 186 | BoundsA |
| 10 | `TameL2` | 2894 | 4.34 | 57 | BoundsB |
| 11 | `TameJet` | 2651 | 4.35 | 97 | TameL2 |
| 12 | `Refold` | 2387 | 4.43 | 49 | TameJet |
| 13 | `Dim1` | 2100 | 4.09 | 57 | Refold |
| 14 | `Kernel` | 2606 | 4.14 | 65 | Dim1 |
| 15 | `Envelope` | 3646 | 4.36 | 65 | Kernel |
| — | umbrella | — | 3.39 | 13 | all 15 |

Whole tree, cold and serial: about 15 minutes.

### The lever, and why the chunk count is 15 rather than 4

The probe's ruling was right and it was the *only* thing that mattered: the two
index-algebra layers `O1Abstract` (1.3k lines) and `M0Abstract` (15.4k lines)
carry **zero geometric types**, so they were given modules with **seven Mathlib
imports** instead of the monolith's 37.  36% of the file now pays a ~1.3 GB
baseline instead of the 3.51 GB geometric one and elaborates in 83 s total —
`M0Gen2` is 7514 lines at 2.48 GB, where the same 7514 geometric lines would
have been ~4.4 GB.  Their namespaces are unchanged, so the `Master` call sites
were not touched.

The geometric remainder needed more pieces than the plan's ~4 because **measured
cost is not linear in line count**: `BoundsB` is 2244 lines at 5.26 GB while
`Base` is 4958 lines at 4.45 GB.  The `LieCorr0Bounds*` sections (section-level
`respectTransparency false` + 1.6M heartbeats) cost ~3× per line what the rest
does.  Two rounds of re-splitting were driven by measurement, not by guessing:
a 5322-line `Master` measured 5.79 GB and was cut at `LieCorr0BoundsE1`.

### Name handling (the correctness-critical part)

Of 1076 `private` declarations only **262** are referenced from another chunk —
established by a comment-stripped cross-chunk usage scan, not by promoting
everything.  Those at `IntrinsicSpectral` level are wrapped in the internal
namespace `DeTurckRemainderTameLipschitz` (opened by every geometric chunk); the
ones already inside `O1Abstract`/`M0Abstract` keep their place.  The other 814
stay `private`, byte-identical to the monolith.

A collision scan found 64 of the private names also declared publicly elsewhere,
seven of them in the **bare** `IntrinsicSpectral` namespace, where an imported
homonym out-ranks an `open`ed internal namespace and would silently re-resolve
(`lc0Kappa`, `lc0PbLow`, `lc0IVPerm`, `lc0VFlat`, `lieCorr0Field`,
`lc0KappaField`, `lc0PbLowField`).  The monolith's 1247-module project import
closure was computed: **none of the declaring modules is in it**, so the
promotion is safe.  Recompute if the imports change.

### Content preservation — mechanical

All 46794 body lines reappear verbatim and in order across the fifteen chunks;
1100 declarations in identical order with identical names; `private` stripped on
exactly the 262 promoted names; every chunk balanced; no declaration hides in a
generated header.  Public API: the 24 public signature blocks are byte-identical
and all 24 names still resolve at their original full names (`#check @…`).  The
monolith's 50-line module docstring (which sits above the first declaration)
was moved to the umbrella.  Backup and tooling:
`.codex-scratch/tamelip-split/{*.before-split.lean, analyze, usage, split,
verify}.py`.

### Chain, C01 and census

- `+LowRegOpJetWindows`: **green**, 9593 jobs, 349 s, 5.49 GB whole-machine.
  **No new monster surfaced** — the dry run showed 9584 of 9593 jobs already up
  to date, i.e. TameLipschitz was the only wall left in that chain.
- `LowRegC01JetTower` first check: **two pre-existing syntax errors** at `:65`
  and `:154` — `set_option … in` placed *between* the doc comment and the
  `theorem` keyword (`unexpected token 'set_option'; expected 'lemma'`).  The
  file had never been parsed, because it was written while its chain was broken.
  Fixed by moving the modifier pairs above their doc comments (the order this
  same file already uses at `section Towers`); no statement or proof changed.
  Check then green in 19 s / 3.53 GB with **exactly the two expected `sorry`s**,
  `low1Ker_jet` (:88) and `selfLow_jet` (:176).
- Axiom census, first time possible: `c1_jet_tower` and `c0_jet_tower` =
  `[propext, sorryAx, Classical.choice, Quot.sound]`, and the `sorryAx` enters
  **only** through those two integrands — `selfLow_split`, `c1_eq`, `c0_eq`,
  `selfLow_joint`, `c2_jet_tower`, `rhsLow1_path_joint` and `path_jetL2_le` all
  censused clean.
- Downstream: all three direct consumers of the umbrella (`RHSRefoldTameH2`,
  `SobolevNonlinearityExistence`, `ShortTime/LowRegRHSSymm`) rebuilt green
  (9730 jobs, 23 min, 5.73 GB whole-machine) — the import path is transparent
  to them, no downstream `import`/`open`/name had to change.
- Four moved TameLipschitz public endpoints censused
  `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**.  On the "4
  pre-existing prose hits": all four are prose, but one of them is a **stale
  claim** — the doc comment of
  `rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet` still says "its body
  is `sorry`, and consumers transitively depend on its `sorryAx`", while the
  declaration in fact has a real proof through
  `rawConnLap_fiberNormSq_le_secondCovGrad`.  The census disproves the sentence;
  it should be deleted the next time that region is edited.

### Traps worth carrying forward

- **An `open` emitted inside the internal namespace expires at the next `end`.**
  The first draft lost 30 identifiers this way.  `open`, `variable`, non-`in`
  `set_option`, `attribute` and `local instance` must be pinned to the level
  they had in the monolith.
- `attribute [-instance] … in` (both occurrences here) is a **one-command
  modifier**: it travels with its declaration and must not be replayed in a
  preamble.
- Chunk starts must absorb a `set_option … in` chain separated from its
  declaration by a **blank line** — same trap the CCDJT split recorded.
- A file written while its import chain is broken **has never been parsed**;
  budget a syntax pass for its first check.

### Honest denominators

Unchanged, and this brick is **0% new mathematics** — it moved bytes and
measured memory.  (N) still **0%** (stated at `ExtendViaUniqueness.lean:80`,
proof not started).  F6 ≈ 60%; front 2 ≈ 50%; machinery ≈ 92%; whole project low
single digits.  Route-error counter: 0/3 (a resource wall, plus one pre-existing
syntax slip found by the first check — neither is a route error).

## Planner update No. 120 (2026-08-04) - TameLipschitz SPLIT ACCEPTED COMPLETE; COMPILE-HEALTH ARC CLOSED; PAUSED AT USER REQUEST

Acceptance: the split brick finished IN FULL before the user-requested
stop (the kill interrupted only the umbrella-docstring restoration,
which planner inspection shows was ALSO already completed — the
umbrella carries the full original module docstring + layout note).
Verified state: 15 chunks green (worst single process 5.26 GB, the
two geometry-free index-algebra layers at a ~1.3–1.5 GB baseline);
umbrella green; `+LowRegOpJetWindows` green (9593 jobs, no further
monster — TameLipschitz was the last wall in that chain);
`LowRegC01JetTower` FIRST CHECK GREEN (two pre-existing
never-parsed syntax slips fixed — `set_option … in` between doc
comment and keyword; exactly the two expected sorries `low1Ker_jet`
:88 / `selfLow_jet` :176); census: towers carry `sorryAx` ONLY
through the two integrands; `selfLow_split`/`c1_eq`/`c0_eq`/
`c2_jet_tower`/`path_jetL2_le` clean; four moved TameLipschitz
endpoints clean (and one STALE doc claim found — the
`rawTensorConnLapSmooth_fiberNormSq_le_secondCovGrad_jet` docstring
still says "body is sorry" while the census disproves it; delete on
next edit of that region).  Three downstream consumers rebuilt green
(9730 jobs).  Traps recorded by the executor (internal-namespace
`open` expiring at `end`; one-command `attribute [-instance] … in`;
blank-line-separated `set_option` chains; never-parsed files need a
syntax pass) stand in the report above.

**The №112–120 compile-health arc is CLOSED.**  The Lean lane is
fully unblocked; the mathematical queue resumes at
[`selfLow_jet` ball-thread + A1-CUR-1] per No. 114, then P-STOP
completion gates the Galerkin lane per No. 115.

PAUSED at user request (the user needs the machine): split agent
stopped post-completion, zero lean/lake processes, stale elaboration
lock removed, both of the brick's claims released, ~7 GB free.
Residual on resume: ONE ~13 s umbrella re-elaboration (the docstring
edit changed its hash) folded into the next targeted build; nothing
else pending.  RECOMMENDED USER ACTION: a checkpoint commit of the
final tree (superseding the mid-split snapshot `7f54201cf`) — the
entire verified CCDJT + TameLipschitz restructuring and the C01
syntax fixes are uncommitted, and today produced two machine crashes.
Resume word: 继续.

## Planner update No. 121 (2026-08-04) - RESUMED; [BALL-THREAD + A1-CUR-1] DISPATCHED; P-STOP §6.1: FIRST-EXIT DISSOLVED (R0 SUPERSEDED)

Resumed on the user's word.  Tree unchanged over the pause (HEAD still
`7f54201cf`; checkpoint-commit recommendation stands).  The
[`selfLow_jet` ball-thread + A1-CUR-1] brick is OUT per No. 114/115
(A1CUR_PLAN.md §7 spec; standing stop signals attached; success
criterion = `low1Ker_jet` and `c1_jet_tower` sorryAx-free, file sorry
census = exactly `selfLow_jet`).

**P-STOP §6.1 (paper): the first-exit machinery is DISSOLVED — R0's
option-2 is SUPERSEDED by something strictly simpler.**  Key
observation: `Π_N` commutes with Δ/resolvents/semigroup and is
norm-nonincreasing on every scale, so the ENTIRE A1 fixed-point solve
replays verbatim at the projected level with the SAME constants —
giving the Galerkin approximants an N-UNIFORM, CLASS-uniform
projected state ball AND a projected maximal-regularity bound
`‖U_N‖_{C_tH³} ≤ B₃` (class data).  The C0 tower's `‖∇P‖_∞` cap is
therefore an A-PRIORI class bound for the approximants — not a
stopped radius — and rungs 3–5 close by tower-direct plain Grönwall
(coefficients from {δ*, B₃, class}; per-datum statics on the right
only; downward coupling only; all six Pro requirements met with
margin).  `R₅ := (2Φ₅)^{1/2}+1` is then a per-datum DEFINITION handed
to the `a2_ladder` high rungs.  No first-exit, no stopped system, no
retraction.  E4 simplifies (the projected contraction can replace or
derive the Galerkin ODE construction).  P-STOP ≈ 85%; remaining =
the §7 identification audit + two small Lean-hypothesis reads
(MR engine accepts projected forcing; the A1 Lipschitz lemma is
operator-level reusable).

Design constraint DISCOVERED and sent to the in-flight brick (§6.1
(c)): `selfLow_jet`'s threaded ball must be instantiable at the H³
level — generic `(a : ℕ)` with gate `1 ≤ a`, or a direct pointwise
`‖∇T‖_∞`-cap hypothesis; a hard `3 ≤ a` gate would starve the
Galerkin bottom rungs (they hold `B₃`, not an `H⁵` ball).
A1-CUR-2's handoff must carry the same constraint.

Honest denominators: (N) 0%; F6 ≈ 60% (A1-CUR-1 in flight would move
it); front 2 ≈ 50%; machinery ≈ 92%; whole project low single digits.
Route-error counter: 0/3 (superseding R0 by a simpler sound route is
a refinement, not an error — nothing was built on first-exit).

## Executor report — [`selfLow_jet` ball-thread + A1-CUR-1] (No. 114 brick) (2026-08-03)

**LEAD WITH THE FAILURE: A1-CUR-1 did NOT close.**  `low1Ker_jet` is
still `sorry`.  `LowRegC01JetTower.lean` carries **two** sorries, not
the targeted one.  Part 1 landed in full; Part 2 delivered the
currency layer the estimate consumes, not the estimate.

### Part 1 — C0 statement surgery: DONE, green, 0% new mathematics

`selfLow_jet` widened, verbatim:

```lean
theorem selfLow_jet
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Kk : ℕ → ℝ, (∀ i, 0 ≤ Kk i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        lowJetSq (I := I) (M := M) g i
            (rhsSelfLow (I := I) (M := M) g g T hδg hδZ s) ≤
          Kk i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  sorry
```

**Form chosen: ball, generic gate `1 ≤ a`** — per the coordinator's
P-STOP §6.1 supplement.  The pointwise-`‖∇T‖_∞` alternative was
considered and **rejected**: `c0_jet_tower` would then have to produce
a fibre-Morrey `H^{a+2} → C¹` bridge that does not exist in the tree,
injecting a NEW frontier into `c0_jet_tower` and breaking its
"sorryAx only via `selfLow_jet`" status.  With the ball form
`c0_jet_tower` passes its already-in-scope `hball` through verbatim.
`a ≥ 16` was NOT inherited.

`c0_jet_tower` gained `(ha : 1 ≤ a)` — it previously had **no** gate
and cannot discharge the widened window without one.  Its only current
reference is the axiom census, and its eventual consumer carries
`a2_ladder`'s `3 ≤ a`, so the change is free.  `low1Ker_jet` stays
ball-free.  Docstrings on both record why the ball is required
(quadratic-in-`∇P` summands; ball-free form false by concentration).

### Part 2 — A1-CUR-1: currency layer landed, estimate NOT landed

**No stop-signal was hit.**  No summand of `rhsLow1Coeff` carries two
bare connection differences (verified from the *definitions*:
`ricci1Split`'s five copies carry one `connDiffSection` each;
`lieArm1Piece`'s three arguments likewise).  The Ricci kernel folds at
`atgw(l + 2)`, **not** `(l + 3)`.  The route in `A1CUR_PLAN.md` §7 is
confirmed sound.

What landed, all sorry-free and focus-checked:

* **NEW `Analysis/Sobolev/TensorHilbert/AtgwArmFold.lean`** — the
  generic radius-free composer, extracted once instead of per arm:
  `gridBase`, `foldConst`/`foldConst_nn`, **`atgwFold`** (pointwise
  two-arm Leibniz fold at generic left rank `p`, generic valences and
  generic offsets: `atgw(i'+u+1)` × `atgw(l+v+1)` → `atgw(n+u+v+1)`),
  **`atgwToJet`** (the integration step: pointwise window at offset
  `w` → `K·(∑Kint)·(1 + ∑_{j<n+w}‖∇ʲP‖²)`).  Radius-free and
  **gate-free**.  This is the piece `A1CUR_PLAN.md` §7 budgeted at
  ~225 lines *per arm* and that `LieCorr0CoeffDiffRadiusFree` repeats
  eight times (`b4_*_atgw`); it also serves A1-CUR-2's five C0
  summands.
* **NEW `Analysis/Sobolev/TensorHilbert/RicciOrder1RadiusFree.lean`** —
  `permAppEqRs` (public re-derivation of the read-only-file `private`
  `permApp_eq_rs`), **`ricci1Split`** (the plan's step-1 public
  re-derivation, in `rsDomDomCongrSection` form), `insertAtgw`
  (`connDiffContrInsertionField` window at `+2`, constant
  `finrank²·Ccd l`), **`ricciKerAtgw`**
  (`linearizedRicciConnDiffOrder1KernelField` window at `+2`, constant
  `46·Cins l`).
* **Promotions.**  `rfns_iCG_connDiffSection_atgw_rf`
  (`DeTurckVFJetRadiusFree.lean:968`) `private` → public.
  `slotPermCc`, `kernelField_eq_neg_arm_combination` and the seven
  `kOutPerm*`/`kInPerm*` (`RicciConnDiffOrder1TameEnvelope.lean`)
  `private` → public, docstrings added.  **Plan correction:** the plan
  said to promote the `LieFieldJetL2Summed.lean:136` copy; that module
  is NOT in `LowRegC01JetTower`'s import chain, while the envelope copy
  IS.  The envelope copy was promoted, the other left untouched, no
  duplicate created and no new import added.

Remaining for `low1Ker_jet`, in dependency order (all now small
because the fold is generic):

1. `ricciCometricFourTraceCastG0` `atgw` at `+1` — a valence-`(4,2)`
   clone of `rfns_iCG_cometricCastG0_atgw_rf` (~134 lines); both
   inputs already radius-free.
2. Ricci arm = `atgwFold (u:=0) (v:=1)` against `ricciKerAtgw`, then
   `atgwToJet (w:=2)`.  ~60 lines.
3. Lie arm: `atgw` at `+1` for `deTurckLieTraceCoeff`, at `+2` for the
   three `Ψ`.  **At the tower's call site `g_bg = g₀`**, so
   `lieArm1ConnDiffBgCc g₀ g₁ g₀ = connDiffSection g₁ g₀` is already
   covered; only `lieArm1PsiB` is genuinely new.
4. Assembly via `jetAdd`/`jetSmul` + the `moserWin_sharp`
   `choose`-over-`a` idiom; `IsPathPert` + `pathPert_rad` supply
   `htie`, `Λ₀ = finrank·δ₀` and `lowJetSq g n P ≤ lowJetSq g n T`
   exactly as the engines want.

### Census

`c1_jet_tower`, `c0_jet_tower` → `sorryAx` only via their integrands
(`low1Ker_jet` / `selfLow_jet` respectively); `selfLow_split` clean;
`atgwFold`, `atgwToJet`, `permAppEqRs`, `ricci1Split`, `insertAtgw`,
`ricciKerAtgw`, `rfns_iCG_connDiffSection_atgw_rf`,
`kernelField_eq_neg_arm_combination` all
`[propext, Classical.choice, Quot.sound]`.  Sorry census of
`LowRegC01JetTower.lean`: **two** (`low1Ker_jet`, `selfLow_jet`).

### Honest denominators

* Part 1: **0% new mathematics** — statement repair.  `selfLow_jet`
  (A1-CUR-2) remains **0%**, and its statement is now honest rather
  than false, which is the whole content of the change.
* `low1Ker_jet` (A1-CUR-1): still **0%** — not stated-and-proved.  Its
  dedicated machinery moved ≈ 70% → ≈ **85%**: the generic composer and
  the Ricci-kernel currency exist and are verified; the outer Ricci
  factor, the Lie arm's factors, and the assembly do not.
* A1-CUR as a whole ≈ **30%** (was ≈ 10%).
* `c1_jet_tower` / `c0_jet_tower`: derivations proved, integrands 0%
  ⟹ ≈ 15% / 20%, unchanged.
* **F6 ≈ 62%** (was ≈ 60%): real reusable movement, but the two
  integrand estimates are both still open.
* Front 2 ≈ 50%.  (N) `ricci_flow_unif_existence`: **0%** — not stated
  in the form the campaign targets.  Machinery ≈ 92%.  Whole HCG
  compactness project: low single digits.
* Route errors: none this session; no stop-signal encountered.

### Traps recorded

* Namespace: `ccTensorBilinSymm`/`gFibreOpBound` live under
  `…IntrinsicSpectral.MetricRealization`.  A missing `open` gives
  `Invalid argument name 'I' for function`, not "unknown identifier".
* `Combinatorics.antidiagonalTupleGridWindow` is a plain `def`: `rw`
  on it fails with "Failed to rewrite using equation theorems"; state
  the unfolding as a `rfl`-proved function equality.
* `riemannianFiberNormSq_add_le` concludes `≤ 2a + 2b`, not `2(a+b)`.
* `rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_le` is left-rank-0
  only; the general one is
  `…_rankLeft_le` (`MetricArmCoeffJetTower.lean:2361`).  Both Ricci and
  Lie outer arms need it (left rank 4 and 3).

### Addendum to the executor report — promotion fallout, resolved

Promoting `slotPermCc` / `kernelField_eq_neg_arm_combination` / the seven
permutations broke `LieFieldJetL2Summed.lean` with nine
"a non-private declaration … has already been declared" errors: that
module transitively imports the envelope and carried its own `private`
copies of exactly those names in the same namespace.  **`private` hides
a name from importers; it does not give it a distinct fully-qualified
name for collision purposes.**  Recorded as a durable trap.

Resolved by deleting the nine local copies (the plan's own dedup step,
applied on the other side) and correcting both stale docstrings that
claimed the declarations were "not importable".  A tree-wide scan found
no further `private` copies of the promoted names.

**Final verification: `lake build` of the dedup + census targets —
9599 jobs, completed successfully, 0 errors.**  Census as reported
above: the eight new/promoted declarations clean; `selfLow_split` clean;
`c1_jet_tower`/`c0_jet_tower` carry `sorryAx` only through
`low1Ker_jet`/`selfLow_jet`.  `LowRegC01JetTower.lean` sorry census:
**two** (`:88` `low1Ker_jet`, `:170` `selfLow_jet`).

## Planner update No. 122 (2026-08-04) - SURGERY GREEN + CURRENCY LANDED; A1-CUR-1 COMPLETION BRICK DISPATCHED

Acceptance of the [ball-thread + A1-CUR-1] brick:
- **Part 1 GREEN and RATIFIED**: `selfLow_jet` widened at generic
  gate `1 ≤ a` per the No. 121 constraint; the executor's rejection
  of the pointwise-`‖∇T‖_∞` form is ratified (it would need a
  nonexistent fibre-Morrey `H^{a+2} → C¹` bridge and inject a NEW
  frontier into `c0_jet_tower`; the ball form passes the in-scope
  `hball` verbatim).  `c0_jet_tower` gaining `(ha : 1 ≤ a)` is
  accepted (it had no gate and cannot discharge the window without
  one; no consumers yet; the eventual consumer carries `3 ≤ a`).
- **Part 2 partial, currency ACCEPTED**: the generic `atgwFold`/
  `atgwToJet` composer (supersedes eight per-arm fold duplicates and
  serves A1-CUR-2), the Ricci radius-free window layer, and the
  promotions with the plan correction (envelope copy, not
  `LieFieldJetL2Summed`) are all census-clean; 9599-job build green.
  `low1Ker_jet` itself remains 0% with machinery ≈ 85% and a
  4-step remaining list recorded in the report above.
- Durable lesson accepted into the trap list: `private` does NOT
  give a distinct fully-qualified name — promoting a name collides
  with `private` copies in downstream modules; dedup on promotion
  (cost this session: one ~40 min rebuild).

DISPATCHED: A1-CUR-1 COMPLETION (assemble `low1Ker_jet` per the
4-step list; narrow-the-sorry fallback; success = `low1Ker_jet` +
`c1_jet_tower` sorryAx-free, file census exactly `selfLow_jet`).
A1-CUR-2 inheritance recorded: the two quadratic C0 summands need a
`Λ₁`-capped sibling of the grid workhorse (where the threaded ball
enters — matches P-STOP §6.1(c)); the linear three compose with
`atgwFold` as-is.

Honest denominators (per the report, planner-endorsed): A1-CUR ≈ 30%;
F6 ≈ 62%; front 2 ≈ 50%; `low1Ker_jet` 0% (machinery ≈ 85%);
`selfLow_jet` 0% (statement now honest); (N) 0% (stated at
`Evolution/ExtendViaUniqueness.lean:80`, sorry :98 — the report's
"not stated in the campaign's target form" phrasing is corrected
here: it IS formally stated; the campaign's task is its proof).
Machinery ≈ 92%.  Whole HCG project: low single digits.
Route-error counter: 0/3.

## Executor report — A1-CUR-1 COMPLETION (No. 122 brick) (2026-08-04)

**`low1Ker_jet` is CLOSED, sorry-free.**  `c1_jet_tower` is now
unconditional: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
`LowRegC01JetTower.lean`'s sorry census is **one** — `selfLow_jet`,
brick A1-CUR-2 — down from two.  No statement anywhere was changed and
the fallback "narrow the sorry" clause did not fire.

### What the proof is

`rhsLow1Coeff g g T 0 s` is, definitionally,
`(-2) • linearizedRicciConnDiffOrder1CoeffField g g₁ + deTurckLieArm1Coeff g g₁ g`
with `g₁ = realizedFam g T 0 s`.  Both arms are **linear** in the
connection difference, so both carry a radius-free, gate-free pointwise
`antidiagonalTupleGridWindow` bound at offset `+2` — one derivative of
the state.  `pathPert_rad` at `δ₀ = 1/3` supplies the perturbation data
uniformly on `s ∈ [0,1]` (tie, fibre bound, the order-zero cap
`Λ₀ = finrank·(1/3)` that `atgwToJet` consumes, and
`lowJetSq g n P ≤ lowJetSq g n T`), so no constant sees `s`.
`atgwToJet` at `w = 2` integrates the window into the `range (i+2)`
budget with `Kk i = ∑_{q<i+1} Kw q · (∑_{k<q+2} Kint k)`, manifestly
nonnegative — the `le_abs_self` trick of `topKer_jet` was not needed,
and neither was `moserWin_sharp` (radius-free windows carry no order
gate, so there is nothing to `choose` away).

### Summand → window map

| summand | windows fed in | offsets | fold |
| --- | --- | --- | --- |
| Ricci arm = `appCcRS (fourTrace) (order-1 kernel)` | `fourTrAtgw` × `ricciKerAtgw` | `+1` × `+2` | `atgwFold (u:=0)(v:=1)` |
| each of 14 `lieArm1Piece`s | `dltcAtgw` × slot-extended `Ψ` | `+1` × `+2` | `atgwFold (u:=0)(v:=1)` |
| `Ψ = lieArm1ConnDiffBgCc g g₁ g` | `bgCcEqConn` collapse, then `rfns_iCG_connDiffSection_atgw_rf` | `+2` | — |
| `Ψ = connDiffSection g₁ g` | `rfns_iCG_connDiffSection_atgw_rf` | `+2` | — |
| `Ψ = lieArm1PsiB g g₁ g` | `kappaAtgw` × `sfEndoAtgw` | `+2` × `+1` | `atgwFold (u:=1)(v:=0)` |
| total | `ricci1Atgw`, `lieA1Atgw` | `+2` | 2-subadditivity |

All of it lives in the new
`Analysis/Sobolev/TensorHilbert/Low1KerRadiusFree.lean` (866 lines, 12
public declarations).  Not one line re-derives the Leibniz grid
argument: every fold is a single `atgwFold` call — the payoff of last
session's generic composer.

### The two findings that made the brick small

1. **The Ricci and Lie outer trace factors are the same object.**
   `deTurckLieTraceCoeff g₀ g₁ σ = reindexCoeffGen (ricciArmPrincipalCoeffPure g₀ g₁) σ`
   (`dltcEqPure`, by `ext` / `reindexCoeffFibGen_apply` / `rfl`), and
   `ricciCometricFourTraceCastG0` is a `(1/2)`-combination of four
   reindexings of that same object.  One window (`pureAtgw`) serves both
   arms.  Moreover the **Ricci** factor's `+1` window already existed:
   §9 item 1 budgeted a ~134-line clone of
   `rfns_iCG_cometricCastG0_atgw_rf`, but
   `rfns_iteratedCovGrad_ricciCometricFourTraceCastG0_diagonalProductGrid_le`
   states `C n · ∑_{k<n+1} atg b k`, which *is* `C n · atgw b (n+1)` by
   `rfl`.  `fourTrAtgw` is 12 lines.
2. **`lieArm1PsiB` needed no new geometry, and no promotion out of the
   Lie file.**  It is `appCcRS (raise∘permute κ) (sharpFlatEndoCc)` with
   `κ = lieArm1LoweredBgKappa = -metricConnDiffLoweredCc` (public
   `metricConnDiffLoweredCc_eq_neg_kappa`), whose `+2` window already
   existed as the `private` `b4_mcd_atgw` in
   `LieCorr0CoeffDiffRadiusFree.lean`.  Raise-slot-0 and slot-permute are
   fibre isometries at every jet order via two **public** lemmas
   (`rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq`,
   `riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection`), so
   `lieArm1_rfns_icg_raiseDomDom_eq`, `lieArm1_kappa_add_decomp`,
   `lieArm1PbLow` and `lieArm1LowFix` all stayed private and untouched.

### The one edit outside the new module

`b4_mcd_atgw` (`LieCorr0CoeffDiffRadiusFree.lean:2017`) promoted
`private` → public, docstring extended; nothing else in that file
changed.  The name was collision-scanned tree-wide first (standing
lesson: `private` hides a name from importers but does **not** give it a
distinct fully-qualified name); no collision.  Cost was measured before
committing: the reverse-dependency closure is 61 modules, but only 3 sit
in `LowRegC01JetTower`'s import chain (`DeTurckRemainderLowBaseAction`,
`LowRegOpJetWindows`, the tower), and the rebuild stayed well inside the
memory guard.

### Census

`low1Ker_jet` → `[propext, Classical.choice, Quot.sound]`.
`c1_jet_tower` → `[propext, Classical.choice, Quot.sound]`.
`c0_jet_tower` → `sorryAx`, only through `selfLow_jet`.
`selfLow_jet` → `sorryAx` (unchanged).
`b4_mcd_atgw` and all twelve declarations of `Low1KerRadiusFree.lean`
(`pureAtgw`, `fourTrAtgw`, `dltcEqPure`, `dltcAtgw`, `ricci1Atgw`,
`sfEndoAtgw`, `kappaAtgw`, `psiBAtgw`, `bgCcEqConn`, `pieceAtgw`,
`lieA1Atgw`, `low1Atgw`) → `[propext, Classical.choice, Quot.sound]`.
File sorry census of `LowRegC01JetTower.lean`: **exactly one**.

### Verification

Every check and build ran under the memory guard (background job, 8 s
poll, `-LeanThreads 1`); no trip, no kill.  Focused checks: promoted
module 121 s, new module 24 s, tower 19 s — green, no warnings beyond
the expected `selfLow_jet` sorry.  Final targeted build of the census
target — which rebuilds the promoted module,
`DeTurckRemainderLowBaseAction`, `LowRegOpJetWindows` and the tower —
**completed successfully, 0 errors**.

### Traps recorded (durably, in `Low1KerRadiusFree.md`)

* `foldConst_nn`'s `{u v}` are implicit and unconstrained by its
  hypotheses: fine under a `refine ⟨…⟩` that fixes them, "cannot
  synthesize implicit `v`" in a bare `have`.
* There is no public `riemannianFiberNormSq_neg`; go through the public
  `riemannianFiberNormSq_smul` with `-X = (-1:ℝ)•X`.  After
  `SmoothCcTensor.toSection_neg` the pointwise step needs
  `ContMDiffSection.coe_neg`/`Pi.neg_apply`, mirroring the `add` case.
* `atgwToJet` takes `X` **before** `K`; writing `_ (hK)` binds the proof
  into the `ℝ` slot.

### Honest denominators

* **`low1Ker_jet` (A1-CUR-1): 100%** — stated and proved.
  **`c1_jet_tower`: 100%**, unconditional.  This closes **one of the two**
  integrand frontiers of the low-base jet towers.
* **`selfLow_jet` (A1-CUR-2): 0%** — THE open estimate, unchanged.  Its
  dedicated machinery ≈ 35% → ≈ **45%**: the composer, the integration
  step, `pureAtgw`, `sfEndoAtgw`, `pieceAtgw` and `b4_mcd_atgw` all
  transfer to the three *linear* summands of `selfLow_split`, but the
  `∇P`-capped (`Λ₁`) currency the two **quadratic** summands require —
  the `A·A` arm inside `ricciGoodLow`, and `lc0VB` — does not exist
  anywhere in the tree.  A genuine new currency layer, not packaging;
  the 3–4 session estimate stands.
* `c0_jet_tower`: ≈ **20%**, unchanged.  A1-CUR overall ≈ 30% → ≈ **45%**.
* **F6 ≈ 62% → ≈ 66%.**  Real movement — an integrand estimate that was
  0% is now done and its consumer is unconditional — but the harder of
  the two integrands is untouched.
* Front 2 ≈ **52%**.  Machinery ≈ **93%**.
* **(N) `ricci_flow_unif_existence`: 0%.**  It IS stated
  (`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`); the proof
  is not started, and nothing this session moved it.
* Whole HCG compactness project: low single digits.
* Route-error counter: unchanged, 0/3 — no stop-signal, no failed route.

### What A1-CUR-2 inherits

* `low1Atgw`'s shape is the template: pointwise window at `+2` against
  `gridBase g₀ P x`, then `atgwToJet (w := 2)` plus `pathPert_rad` in the
  tower.  `c0_jet_tower`'s derivation is already written over
  `selfLow_jet` in exactly that shape, with `hball` already threaded.
* At the `c0_jet_tower` call site `g_bg = g₀` too, so the `bgCcEqConn`
  collapse applies to any C0 summand carrying a background arm.
* Of `selfLow_split`'s five summands,
  `deTurckLieCovDerivArmField − edgeLiePairFam`, `lc0AMix` and `lc0Riem`
  are linear and should fall to the currency now in place;
  `(-2)•ricciGoodLow`'s `A·A` arm and `lc0VB` are the quadratic pair
  needing the new `Λ₁` layer.  `LieCorr0CoeffDiffRadiusFree.lean`'s
  ball-uniform siblings (`lc0VB_perOrder_rf`, `lc0AMix_perOrder_rf`) are
  the models for the capped statements.

## Planner update No. 123 (2026-08-04) - A1-CUR-1 ACCEPTED CLOSED: c1_jet_tower UNCONDITIONAL (FIRST TOWER); A1-CUR-2 SESSION 1 DISPATCHED

Acceptance: `low1Ker_jet` PROVED, census `[propext, Classical.choice,
Quot.sound]` — no sorryAx; `c1_jet_tower` 100% UNCONDITIONAL, the
first of the two low-base jet towers.  Planner's independent
pre-notification grep already matched (file sorry census = exactly
`selfLow_jet`).  No statement changed; no stop signal; the
narrow-the-sorry fallback did not fire.  New module
`Analysis/Sobolev/TensorHilbert/Low1KerRadiusFree.lean` (866 lines,
12 declarations); one promotion outside (`b4_mcd_atgw`,
collision-scanned, 3-module rebuild cost measured before committing).
Two brick-shrinking findings recorded: `dltcEqPure` (the Ricci and
Lie outer trace factors are the SAME object — one window serves
both) and `fourTrAtgw` = 12 lines via an `rfl` identity where the
plan budgeted ~134.  `pathPert_rad` at δ₀ = 1/3 supplies tie, fibre
bound, `Λ₀`, and the jet comparison uniformly in `s` — no constant
sees `s`.

Milestone framing (honest): of F6's two integrand frontiers, the C1
side is now CLOSED end-to-end (`low1Ker_jet` → `c1_jet_tower`); the
C0 side (`selfLow_jet`, A1-CUR-2) is the LAST real estimate in the
F6 chain, and its two quadratic summands need machinery that does
not exist in the tree — including the fibre-Morrey `H^{a+2} → C¹`
bridge itself at low gate.

DISPATCHED: A1-CUR-2 SESSION 1 — two deliverables: D1 the `Λ₁`
producer (pointwise `‖∇P‖` cap from the ball at gate `1 ≤ a`, dim 3;
scout-first per walls discipline, the supercritical `a ≥ 16`
producers may NOT be inherited), D2 the `Λ₁`-capped `atgw` sibling
(one ∇P factor absorbed at the cap, the other kept in the grid at
`range (i+2)` — the `range (i+3)` stop signal armed), smoke-tested
on ONE quadratic summand.  Assembly = session 2+.

Honest denominators: F6 ≈ 66% (was 62); A1-CUR ≈ 45%;
`low1Ker_jet`/`c1_jet_tower` 100%; `selfLow_jet` 0% (machinery
≈ 45%); front 2 ≈ 52%; (N) 0% (stated, sorry :98); machinery ≈ 93%;
whole HCG project low single digits.  Route-error counter: 0/3.

## Executor report — A1-CUR-2 SESSION 1 (No. 123 brick) (2026-08-04)

**Both deliverables landed, sorry-free, plus the smoke test.**  No stop
signal: the repaired estimate lands at `range (i+2)`, and no `a ≥ 16`
gate was inherited — the gate is `1 ≤ a`.  `selfLow_jet` itself is
untouched and still `sorry`; `LowRegC01JetTower.lean`'s census is
still exactly one.

### The finding that shaped everything

A purely pointwise/combinatorial repair of the quadratic summands is
**impossible**.  The over-budget term is `∫ |∇^αP|²|∇^βP|²` with
`α + β = n + 2`, `α, β ≥ 1`; at `α ≈ β ≈ n/2` neither factor is capped,
so no inequality `|∇^αP|²|∇^βP|² ≤ CΛ²·(weight ≤ n+1 entries)` holds.
The improvement is an INTEGRAL fact — Gagliardo–Nirenberg with
interpolation endpoint `‖∇P‖_∞` instead of `‖P‖_∞`.

Consequence: **the capped currency is the ordinary radius-free currency
run on the base tensor `∇P` at valence `(0,3)`**, with `Λ₁ = ‖∇P‖_∞` in
the role `Λ₀ = ‖P‖_∞` plays at `(0,2)`.  The whole session follows from
this one observation.

### D1 — the `Λ₁` producer: BUILT (the engine was found, the bridge was not)

Scout result: the fibre-Morrey engine **already exists, public and
ungated** —
`exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
(`Analysis/Sobolev/Embedding/SobolevEmbeddingSharpC0JetSum.lean:717`),
valence-generic, needing only the jets through order `finrank/2 + 1`.
The `a ≥ 16` of
`deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow`
comes from ITS route (`L = 4K+4 ≤ a+1`), not from the embedding — so
the gate was correctly not inherited.  What did NOT exist is the
ball-to-cap bridge; that is D1.  Verbatim:

```lean
theorem gradCapOfBall (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Λ₁ : ℝ, 0 ≤ Λ₁ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤ Λ₁ ^ 2
```

with `Λ₁ = C_emb(g₀)·√3·C₂·R₀`.  A jet-ball sibling `gradCapOfJets` is
the actual content; `gradCapOfBall` is the two-line Hs-ball wrapper.
`1 ≤ a` is exactly `a + 2 ≥ finrank/2 + 2 = 3` in dimension three.

### D2 — the capped currency: BUILT, and it needed an upstream generalization

The grid engines were hard-wired to base valence `(0,2)`.  Generalized
**in place**, with the `(0,2)` statements kept verbatim as one-line
instances, so **no call site anywhere changed** — which was mandatory,
one of the 13 call sites being in the READ-ONLY
`DeTurckRemainderLowBaseAction.lean`:

| file | change |
| --- | --- |
| `JetProductIntegral.lean` | `grid_prod_int_le` valence `{r s}` implicit (inferred from `P`) |
| `.../CurvatureCoefficientDifferenceJetTower/ResidualFree.lean` | new generic `atgGridIntRs`, `bfGridWinIntRs`; the two old names are now their `(0,2)` instances |
| `AtgwArmFold.lean` | `gridBase`/`gridBase_nn`/`atgwFold` base valence implicit; new `atgwToJetRs`, with `atgwToJet` its `(0,2)` instance |

New module `Analysis/Sobolev/TensorHilbert/GradCapAtgw.lean` (11 public
declarations):

* `icgNormComp`, `gradBase_eq`, `gradBase_fun` — the shifted base;
  `gridBase g₀ (∇P) x j = |∇^{j+1}P|²(x)`, one `exact` from the PUBLIC
  `rfns_iteratedCovGrad_comp`.
* `gradCapOfJets`, `gradCapOfBall` — D1.
* `shiftConst`, `atgwShift` — **the base shift**, the one genuinely new
  combinatorial brick: `atgw b (k+1) ≤ shiftConst Λ k · atgw b' k` for
  `k ≥ 1`, given `b 0, b 1 ≤ Λ`, `1 ≤ Λ`.  Proof = partition each
  antidiagonal tuple into parts `= 0`, `= 1`, `≥ 2`; the first two are
  eaten by the caps, the third re-indexes along `Finset.equivFin` into a
  legitimate grid term of the shifted base at weight `≤ m − 1`.  Sharp
  for arms LINEAR in `∇P`.
* `armShift` — an arm's EXISTING window at `bP`-offset `u+2` becomes a
  shifted-base window at level `i+u+1`.  **No arm is re-derived.**
* `atgwCapToJet` — the capped integration step: shifted window at offset
  `w` ⟹ `range (n + w + 1)` in `P`'s jets.  At `w = 1`: `range (n+2)`.
* `atgwCapArm` / `atgwCapFold` — the capped two-arm workhorse, pointwise
  and integrated.  Two arms each carrying one derivative of the state
  land on `range (n+2)` — the same budget the linear summands enjoy.

### Smoke test — `lc0VB`, landed, first build

`Analysis/Sobolev/TensorHilbert/Lc0VBCapWindow.lean`:
`lc0VBCapAtgw` (pointwise, shifted window at `i+1`) and `lc0VBCapJet`

`‖∇ⁱ(lc0VB g₀ g₁)‖² ≤ K i · (1 + ∑_{j<i+2} ‖∇ʲP‖²)`,

against `lc0VB_perOrder_rf`'s `range (i+3)`.  Route:

```
vbMcdArm           atgw bP (m+2)  --armShift-->  atgw b'P (m+1)
ipLowCc (wOmega)   atgw bP (q+2)  --armShift-->  atgw b'P (q+1)
  atgwCapArm + vbSplit      -> lc0VBPass : atgw b'P (n+1)
lc0RiemLive        atgw bP (m+1) ≤ atgw bP (m+2) --armShift--> atgw b'P (m+1)
  armShift + atgwFold(0,0) + lc0VB_eq_app  -> lc0VB : atgw b'P (n+1)
  atgwCapToJet (w = 1)                     -> range (n+2)          ✓
```

Cost: **one** promotion, `b4_wOmega_atgw` (collision-scanned; three
references, all in its own file).  The other six ingredients were
already public.  Not one line of `lc0VB`'s geometry was re-proved.

### The OTHER quadratic summand is NOT reachable this way (route note for session 2)

`ricciAAArm` cannot be handled by shifting its folded window:
`ricciAAKer` is a single arm that is ITSELF quadratic, and the shift is
sharp only when every grid entry of the bound carries a factor — true
for a bound on an arm linear in `∇P`, false for a quadratic one.
Session 2 must descend into `aaKer_eq`'s six `appCcRS` nests
(`DeTurckRemainderLowBaseAction.lean:4400`, all `private` in a READ-ONLY
file) and shift the individual `connDiffContrInsertionField` factors, or
obtain a public two-arm split of `ricciAAKer`.  **This is the single
concrete blocker for the assembly.**

### Census

All new/changed declarations `[propext, Classical.choice, Quot.sound]`:
`grid_prod_int_le`, `atgGridIntRs`, `bfGridWinIntRs`, the two `(0,2)`
compatibility instances, `atgwToJetRs`, `atgwFold`, `atgwToJet`,
`icgNormComp`, `gradBase_eq`, `gradBase_fun`, `gradCapOfJets`,
`gradCapOfBall`, `shiftConst_nn`, `atgwShift`, `atgwCapToJet`,
`armShift`, `atgwCapArm`, `atgwCapFold`, `b4_wOmega_atgw`,
`lc0VBCapAtgw`, `lc0VBCapJet`.  `c1_jet_tower`, `low1Ker_jet`,
`selfLow_split` clean (unchanged).  `c0_jet_tower`/`selfLow_jet` carry
`sorryAx` only through `selfLow_jet` (unchanged).  **File sorry census
of `LowRegC01JetTower.lean`: exactly one (`:272`).**

### Verification

Every build and check ran under the memory guard (background job,
poll, `-LeanThreads 1`); no trip, no kill.  Three full targeted builds
completed successfully: **9404 jobs** (valence generalization),
**9607 jobs** (currency + tower + census), **9608 jobs** (final census
including the smoke test).  Focused checks of the new module: 19–20 s.
Zero new sorries.

### Traps recorded (durably, in `GradCapAtgw.md` / `Lc0VBCapWindow.md`)

* Generalizing a valence in place is FREE of call-site churn when the
  valence can be made implicit and inferred from an explicit argument
  (`grid_prod_int_le`); when it cannot (the valence sits under an `∃`),
  keep the old statement as a one-line instance rather than editing 13
  call sites — one of which was in a read-only file.
* `gridShift` at `m = 0` is FALSE (the shifted window of level `0` is
  empty); the `m = 0` level must be absorbed at the outer window, where
  `1 ≤ atgw b' k` is available.
* `Fintype.sum_equiv`/`Fintype.prod_equiv` along `Finset.equivFin.symm`
  close the re-indexing goals by `rfl` — but only if the tuple is NOT
  `set`-bound (a `set` name blocks the `rfl`).
* `Real.sqrt Λ` is the clean way to feed a `Λ`-shaped cap into an engine
  whose hypothesis is `≤ Λ₁ ^ 2`.

### Honest denominators

* **`selfLow_jet` (A1-CUR-2): still 0%** — not stated-and-proved; the
  estimate is untouched.  Its dedicated machinery ≈ 45% → ≈ **70%**: the
  capped currency exists, is verified, and one of the two quadratic
  summands is already through it end-to-end.  What is missing is
  `ricciAAArm`'s inner split and the five-summand assembly.
* `c0_jet_tower`: ≈ **20%**, unchanged (derivation proved, integrand 0%).
* A1-CUR overall ≈ 45% → ≈ **60%**.
* **F6 ≈ 66% → ≈ 70%.**  Real movement — the last genuinely new estimate
  machinery in the F6 chain now exists and is smoke-tested — but the C0
  integrand is still 0% and it is the last open estimate.
* Front 2 ≈ **54%**.  Machinery ≈ **94%**.
* **(N) `ricci_flow_unif_existence`: 0%.**  Stated at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`; nothing this
  session moved it.
* Whole HCG compactness project: low single digits.
* Route-error counter: unchanged, **0/3** — no stop signal, no failed
  route, no statement changed.

### What session 2 (the assembly) needs

1. A public two-arm split of `ricciAAKer` (or promotion of `aaKer_eq` +
   the six `aa*`), then `armShift`/`atgwCapArm` on each nest.
2. The three LINEAR summands of `selfLow_split`
   (`deTurckLieCovDerivArmField − edgeLiePairFam`, `lc0AMix`, `lc0Riem`)
   through the EXISTING radius-free currency — unchanged, per No. 122.
3. `gradCapOfBall` wired at the `selfLow_jet` call site to produce `Λ₁`
   from the already-threaded `hball`; `pathPert_rad` supplies the other
   cap.  Take `Λ := max (Λ₀²) (Λ₁²) ⊔ 1` so both `gridBase … 0 ≤ Λ` and
   `gridBase … 1 ≤ Λ` and `1 ≤ Λ` hold at once.
4. `jetAdd`/`jetSmul` assembly and `low1Atgw`'s template shape.

## Planner update No. 124 (2026-08-04) - A1-CUR-2 SESSION 1 ACCEPTED (CAPPED CURRENCY COMPLETE, lc0VB SMOKE-TESTED); SESSION 2 (ASSEMBLY) DISPATCHED

Acceptance: both deliverables + the smoke test landed sorry-free (21
new/changed declarations census-clean; three guarded targeted builds
green, 9404/9607/9608 jobs; zero kills; `LowRegC01JetTower.lean`
census unchanged at exactly `selfLow_jet`).  No stop signal — the
capped route lands at `range (i+2)` and the gate is `1 ≤ a`.

Structural finding RATIFIED: the quadratic repair is an INTEGRAL
fact (GN with endpoint `‖∇P‖_∞`), so the capped currency is the SAME
radius-free currency run on the base tensor `∇P` at valence `(0,3)`
with `Λ₁` in place of `Λ₀` — realized as `atgwShift`/`armShift`/
`atgwCapToJet`/`atgwCapArm`/`atgwCapFold` (`GradCapAtgw.lean`), with
NO arm re-derived.  Stocked-instance NINETEEN: the fibre-Morrey
ENGINE was public, valence-generic and UNGATED all along
(`SobolevEmbeddingSharpC0JetSum.lean:717` — the `a ≥ 16` belonged to
the tame producer's own route); only the ball→cap bridge was missing
(now `gradCapOfBall`/`gradCapOfJets`, `Λ₁ = C_emb·√3·C₂·R₀`, and
`1 ≤ a` is exactly the dim-3 supercritical threshold).  The in-place
valence generalization of the grid engines (with `(0,2)` kept as
one-line instances so ZERO call sites changed — one of 13 being in a
read-only file) is the model for future upstream generalizations.

DISPATCHED: SESSION 2 (assembly) — (1) public two-arm split of
`ricciAAKer` (re-derive `aaKer_eq` + six `aa*` from the read-only
file; the identified single blocker), (2) window the five
`selfLow_split` summands (lc0VB done; three linear via existing
currency; A·A via the split + `armShift` per nest), (3) assemble
`selfLow_jet` (`Λ := max(Λ₀², Λ₁²) ⊔ 1` trick; constants before
state; no constant sees `s`).  Success = `selfLow_jet` AND
`c0_jet_tower` sorryAx-free, file census ZERO — the F6 estimate
chain then closes COMPLETELY, leaving only the routine A1c/A1d
assembly bricks before the (P-STOP-gated) Galerkin lane.

Honest denominators (endorsed from the report): `selfLow_jet` 0%
(machinery ≈ 70%); A1-CUR ≈ 60%; F6 ≈ 70%; front 2 ≈ 54%;
machinery ≈ 94%; (N) 0% (stated, sorry :98); whole HCG project low
single digits.  Route-error counter: 0/3.

## Executor report — A1-CUR-2 SESSION 2 (the assembly) (2026-08-04)

**`selfLow_jet`'s `sorry` is gone: the estimate is assembled and proved.
It is NOT yet unconditional — it stands on two `private` per-arm windows
that are still `sorry`.**  Leading with that, because the success
criterion of the dispatch was a sorryAx-free `selfLow_jet` and that was
NOT met.

### Where the work stopped

Two of the six arm-windows the assembly consumes are open:

* `ricciDACap` — the Palatini arm `ricciDALow g₀ g₁ P` inside
  `ricciGoodLow`;
* `lieCovCap` — the pair
  `deTurckLieCovDerivArmField − edgeLiePairFam`.

Both are `private` in `LowRegC01JetTower.lean` (`:249`, `:333`), both are
stated in exactly the form the assembly consumes, and both are per-ARM,
not per-summand: `ricciGoodCap` is proved from `ricciAACap` + `ricciDACap`
through `ccInputSymm`.  File sorry census: exactly two.

Neither is a mathematical obstruction.  `ricciDACap` is missing a leaf
inventory only — the generic structural identity
`refoldKernelContractionMonomialField_eq_mvPairTraceRefold` is public and
holds for an ARBITRARY `(0,4)` argument (the tame layer's hard-wiring to
`G = ∇²(symmS P)` is in its *bound*, not in the identity), so what is
left is capped windows for `mvPairTraceOp`, `slotInsertEndoCc
(fullRaisedEndoField)`, `koszulOp`, plus a `capDdc0` sibling for
`domDomCongrSection` at valence `(0,s)`.  Short brick.  `lieCovCap` is
bigger: `lieCov_residual` is public and reduces the pair to a single
product, and `lieCovPair` should be `appCcRS (pureTrace 2) (pureTrace 4)`
by `rfl` (`bdPureDT` and `pureTrace` are the same field), but the inner
`lieCovR4 = (-(s/2))•lrCurvF T − lrQuadF g₁` needs windows for `lrQA`/
`lrQB`/`lrRiemW1`/`lrRiemW2` that exist only as `private bd*_gridWindow`
in `RiemannCoefficientPalatiniRefold.lean`.  About a session.

### What landed, sorry-free

**The assembly itself** (the dispatch's item 3) — `selfLow_jet` is a
complete proof.  `gradCapOfBall` fixes `Λ₁`; `Λ := max 1 (max (finrank·
(1/3))² Λ₁²)` is chosen before the state and never sees `s`; `P = s•T`
with `s ∈ [0,1]` contracts the `∇T` cap to a `∇P` cap; the five summand
windows are chained by `capSmul`/`capAdd`, transported along
`selfLow_split` by `capCongr`, integrated once by `capJet`, and
`pathPert_rad`'s jet comparison converts `P`'s jets to `T`'s.  Lands at
`range (i + 2)` with gate `1 ≤ a`.  **Neither stop signal fired.**

**The `ricciAAKer` two-arm split** (item 1) — session 1's named blocker.
The six pieces exist twice *privately*: as `aa*` in the read-only
low-base action file, and as `ricQuad*` in the editable
`EdgeRicciPairing.lean`.  Publicizing either set was rejected: the
`ricPerm*` permutations they are built from are duplicated under the same
names in the same namespace inside the read-only file, so exporting them
risks an ambiguity error in a file that cannot be repaired.  Re-derived
instead (the `ricci1Split` precedent) as `aaCoreP`/`aaCore`/`aaKerSplit`
in a new module; `aaKerSplit` is `rfl`.  Zero edits outside the new
files and the tower.

**Four of the six arm windows** (item 2): `ricciAACap`, `lc0AMixCap`,
`lc0RiemCap` new, plus session 1's `lc0VBCapAtgw` consumed directly (its
conclusion IS `HasCapWin` unfolded).

**A reusable arm calculus.**  New module
`Analysis/Sobolev/TensorHilbert/GradCapArms.lean` (323 lines): the
predicate `HasCapWin g₀ P X K` and fourteen closure lemmas
(`capOfArm`, `capOfBnd`, `capApp`, `capAdd`/`capSub`/`capSmul`/`capNeg`,
`capReindex`/`capDdc`, `capSlotExt`/`capIter`, `capMono`/`capCongr`,
`capJet`).  The load-bearing fact is that the capped level `i+1` is
CLOSED under `appCcRS` (`atgwFold` at `(0,0)`), so an arbitrary product
tree of once-differentiated arms stays in budget and only the constants
grow.  This is what made a five-factor nest like `lc0AMix` a 60-line
proof.  New module `SelfLowCapWindows.lean` (482 lines) holds the
summand windows.

### Two corrections to the record

* **`lc0AMix` is NOT linear** (No. 122 and session 1 both listed it among
  the three linear summands).  `amix_refold_rf` is a five-factor nest
  with TWO lowered connection differences; `b4_amix_atgw` lands at
  `atgw bP (i+3)`.  It is a quadratic summand and needed the cap.  Only
  `lc0Riem` of the three was genuinely linear;
  `deTurckLieCovDerivArmField − edgeLiePairFam` is worse than linear
  (each half has a second-derivative head and only the difference is
  controllable).
* **The `a ≥ 16` gate was never in danger.**  It sits in
  `lc0AMix_perOrder_rf`/`lc0Riem_perOrder_rf` because those route through
  `cometricCastG0_order0sup_jetL2_radiusFree`; the capped route uses
  `trace_grid_rf` and `b4_mcd_atgw`, both gate-free.

### Census (explicit)

Full targeted build of the census target: **9610 jobs, successful.**

* `selfLow_jet`, `c0_jet_tower`: `[propext, sorryAx, Classical.choice,
  Quot.sound]` — the two per-arm frontiers, and nothing else.
* `c1_jet_tower`, `low1Ker_jet`, `selfLow_split`: `[propext,
  Classical.choice, Quot.sound]` — clean, unchanged.
* All session-2 declarations clean: `HasCapWin` and the fourteen calculus
  lemmas, `lc0RiemCap`, `lc0AMixCap`, `aaCoreP`, `aaCore`, `aaKerSplit`,
  `ricciAACap`.
* Exactly two declarations in the whole census carry `sorryAx`.
* `LowRegC01JetTower.lean` sorry census: **two** (was one — the single
  `selfLow_jet` sorry became two narrower, strictly more local ones).
* No downstream build was possible: `c0_jet_tower`/`c1_jet_tower` have NO
  consumer in the tree yet (A1c `a1_ladder` and A1d `n_diff_hm_rung` are
  unwritten), so the requested `LowRegLadderRung` check is vacuous.

### Honest denominators

* **`selfLow_jet`: still 0% as an unconditional theorem** — it depends on
  two `sorry`s, so it is not proved.  Its dedicated machinery ≈ 70% →
  **≈ 88%**: the assembly is done, the currency is done, four of the six
  arm windows are done, and the two open ones have identified routes.
* `c0_jet_tower`: ≈ 20%, unchanged (derivation proved, integrand still
  conditional).
* A1-CUR ≈ 60% → **≈ 78%**.
* **F6 ≈ 70% → ≈ 76%.**  Real movement, but the C0 integrand is still not
  unconditional and it is still the last open estimate in the chain.
  F6 also still lacks A1c (`a1_ladder`) and A1d (`n_diff_hm_rung`) —
  routine assembly bricks over the towers, both unwritten (0%).
* Front 2 ≈ **56%**.  Machinery ≈ **95%**.
* **(N) `ricci_flow_unif_existence`: 0%.**  Stated at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  Nothing
  this session moved it.
* Whole HCG compactness project: low single digits.
* Route-error counter: unchanged, **0/3** — no failed route, no statement
  changed, no stop signal.

### Next target

`ricciDACap` first (short, leaf-inventory only), then `lieCovCap`.  With
both, `selfLow_jet` and `c0_jet_tower` become unconditional and the F6
estimate chain closes.

## Planner update No. 125 (2026-08-04) - SESSION 2 ACCEPTED (NARROWED-PARTIAL, 4/6 WINDOWS + ASSEMBLY PROVED); SESSION 3 (CLOSE THE TWO ARMS) DISPATCHED

Acceptance: the sanctioned narrow-the-sorry pattern fired correctly —
`selfLow_jet`'s five-summand ASSEMBLY is proved, standing on exactly
two precisely-scoped private arm windows (`ricciDACap` :240,
`lieCovCap` :315), each with a diagnosed route and leaf inventory.
Census honest and verified (9610-job build): the towers' sorryAx
enters ONLY via those two; all 20+ session-2 declarations clean;
`c1_jet_tower`/`low1Ker_jet` untouched-clean.  The aaKer blocker is
DISSOLVED by `rfl`-split re-derivation (`aaCoreP`/`aaCore`/
`aaKerSplit`), and the executor's REFUSAL to promote is ratified —
the `ricPerm*` names are duplicated in the same namespace inside the
read-only file, so promotion would have created unrepairable
ambiguity (new flavor of the private-FQN trap; recorded).

TWO RECORD CORRECTIONS accepted (plan-file errors, not route errors):
`lc0AMix` is NOT linear (five-factor nest, two lowered connection
differences — went through the cap; only `lc0Riem` of the "three
linear" was genuinely linear, and the lieCov pair is worse than
linear with only the DIFFERENCE controllable); the `a ≥ 16` gate was
never in danger (it belongs to the `cometricCastG0_order0sup` route,
bypassed by the capped route).  Reusable yield: `GradCapArms.lean`
(the capped level `i+1` is CLOSED under `appCcRS` — the load-bearing
calculus that made a five-factor nest a 60-line proof).

DISPATCHED: SESSION 3 — close `ricciDACap` (short: capped windows for
`mvPairTraceOp` / `slotInsertEndoCc (fullRaisedEndoField)` /
`koszulOp` + `capDdc0`; the :5945 refold identity is public and
argument-generic) and `lieCovCap` (re-derive the four `lr*` windows
publicly from the `private bd*_gridWindow` references — cost-measure
rules out promotion in the ~19k-line Palatini file; `lrQuadF` is
quadratic = exactly what the cap is for; no constant sees `s`).
Success = file census ZERO ⟹ **the F6 estimate chain closes**.

Honest denominators: `selfLow_jet` 0% unconditional (machinery
≈ 88%); A1-CUR ≈ 78%; F6 ≈ 76% (still lacking, after the chain:
A1c `a1_ladder` + A1d `n_diff_hm_rung`, both 0%, routine assembly);
front 2 ≈ 56%; machinery ≈ 95%; (N) 0% (stated, sorry :98); whole
HCG project low single digits.  Route-error counter: 0/3.

---

**THIS FILE IS FULL** (3000-line project limit).  The A1-CUR-2 SESSION 3
executor report — **both windows CLOSED, F6 estimate chain CLOSED** — and
everything after it live in **`UNIF_EXISTENCE_PLAN4.md`**, in this directory.
Continue there.
