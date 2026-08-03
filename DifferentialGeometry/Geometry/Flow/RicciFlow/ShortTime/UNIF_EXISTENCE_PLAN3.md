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
