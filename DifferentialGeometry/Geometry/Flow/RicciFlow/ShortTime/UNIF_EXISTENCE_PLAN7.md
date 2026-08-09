# UNIF_EXISTENCE_PLAN7 — the campaign ledger, entry 206+

Continuation of `UNIF_EXISTENCE_PLAN6.md` (167–205; PLAN5 = №142–166,
PLAN4 = №126–141, PLAN3 = №104–125, PLAN2 = №70–103, PLAN = №1–69 — all
frozen).  Rolled 2026-08-07 near the 3000-line cap.  One entry per
landed/ruled brick; re-read this file's TAIL before every append.

## State at rollover (2026-08-07 early morning, after entry 205)

- **Endgame**: (N) `ricci_flow_unif_existence`
  (`Evolution/ExtendViaUniqueness.lean:80`, sorry `:98`) — **0%**.
  Dedicated uniform-existence machinery ≈ **80%**.  Whole HCG ≈ **3%**.
  **Route-error counter 2/3** (№155 a₁-v1 Hölder; #2 = the ΔC0-missing
  bundle of entries 199/200, scored at 203).
- **The overnight Bg arc** (194–205): checkpoint `radialA1HiBg_pair`
  verified; `a1_comm`/`lowA1Bg_comm_bg` landed (194); class-first scout
  adopted (195, gaps G1–G5); affine-C0 feasibility gate FAILED with a
  scaling witness (196 — the diagonal C0 is genuinely quadratic; C0/C1
  asymmetry structural); ruling 197 retracted at 199 (near-miss, gated);
  G5 split landed (198: `IsBgA1At`/`IsBgA2At`); `bgA1_of_refold` landed
  (200) but on the WRONG bundle (ΔC0 missing — route error #2, 203);
  G3 entry `invCoeff_h2_lip_unif` landed (202); B1 landed (204:
  `refoldCoreBg` + `refold_split_bg`, the corrected-bundle total split,
  axiom-clean); B2 STOPPED at its gate (205: the ΔC0 affine packet's
  producer does not exist — a ~400-line tame layer in `LowRegBgH2.lean`,
  mechanical, the three quadratic arms CANCEL in the background
  difference; additivity bridge `a1Hi_add`/`a1Lo_add` landed).
- **Open items**, ranked:
  1. ~~**B2c′**~~ **DONE at entry 206** (2026-08-07): `IsBgA1At`'s core
     fields now name `refoldCoreBg`; `bgA1_of_refold` re-proved
     sorry-free on the registered honest input `BgDeltaPack`
     (`LowRegBgA1Refold.lean`).  Route error #2's CONTENT is repaired;
     the producer is conditional until B2a/B2b land.  **Next = item 2.**
  2. ~~**B2a/B2b**~~ **DONE at entries 207 and 208** (2026-08-07).
     207: `c0Bg_diff_tame` landed sorry-free in `LowRegBgH2.lean`
     (1270 → 1579), axiom-clean; the quadratic-arm cancellation was
     already proved in-file (`bgCorr_eq`), AMix needed a SECOND
     cancellation (205's "AMix already affine" sub-claim is false).
     208: `c0bg_pack` landed sorry-free in `LowRegBgA1Refold.lean`
     (938 → 1494), axiom-clean, so `BgDeltaPack` is a THEOREM and
     `bgA1_of_refold` DROPPED its `hΔ` argument.  **The A1 half of the
     fixed-background lift is produced, unconditionally.**  The square
     clause was free (`a1_comm` is already stated "for ANY bundle"); the
     Lipschitz half needed `c0_bg_pair_h2` TWICE — at `gB` and at the
     diagonal — recombined by `jetSub`.  **Next = item 3, the A2 half**,
     now the sole remaining conjunct of `IsBgLiftAt`.
  3. ~~**A2 half**~~ **DONE at entries 211 and 212** (2026-08-07).
     211: `c2Bg_h2_small` — the `c2_h2_small` Bg sibling — landed
     sorry-free (`LowRegBgC2Small.lean`), the one genuinely missing
     analytic input.  212: `radialA2Bg_pair` + the `(g, gB)` widening of
     `LowRegBgA2Time.lean`'s three `g g` declarations + `bgA2_of_radial`,
     so **`IsBgA2At` is produced**; and `bgLift_of_radial` composes it
     with `bgA1_of_refold`, so the **whole fourteen-field `IsBgLiftAt` is
     a theorem per `(g, gB)`**, conditional only on the three scalar
     dominations `Z ≤ D.zero`, `L ≤ D.slope`,
     `C * D.coeffRadius ≤ D.contract`.  The class-4 stop condition never
     fired; the contraction knob is the RADIUS with `C` bound outside
     `∀ D`.  Class-uniformity is **0%** and is now exactly item 4.
     **Next = item 4, the sole remaining obstruction.**
  4. **G3 lane** (~56 `_unif` Lipschitz/pair nodes; **3 done ≈ 5%**
     after entry 214 — `invCoeff_h2_lip_unif`, `trace24_h2_lip_unif`,
     `pairTrace_h2_lip_unif`): next node **`pairTrace_h2_bdd`**
     (`…C2Lip.lean:1794`), inputs covered and the class-first route is
     SHORTER than the metricwise one (see 214).  209's "mechanical"
     prediction for node 3 scored **TRUE** at 214.  The
     "class-uniform fibre bound for `cometricDoubleTraceField g p`"
     named at 202 was a FALSE WALL — `cometricTrace_rfns_p`
     (`CometricTraceSelfBound.lean:220`) already existed, public and
     rank-generic.  Serves the Z/L→class-fixed seam of `bgA1_of_refold`.
  5. Exhibits at NINETEEN, with **20 proposed at entry 209** (the
     `cometricTrace_rfns_p` false wall) awaiting planner adjudication;
     19 = `refold_low_split` zero consumers.
     Morning review items: counter 2/3 adjudication; the B2a/B2b
     pricing (3 sessions total for B2, was 1–2 — landed at 3); exhibit
     20 adjudication.
- **Standing rules** (unchanged): lake via `scripts/lake-locked.ps1`,
  focused checks `-LeanThreads 4 -LeanMemoryMB 6144`; the six READ-ONLY
  files; №194 monolith rule (`DeTurckRemainderLowBaseLip.lean` 10.8k
  cannot re-elaborate — re-derive from public producers in light files);
  reuse the paused lane's dead-pid tokens; files ≤ 3000 lines; names
  ≤ 20 letters; census additions deferred while census files carry the
  paused lane's claims; campaign delta UNCOMMITTED (user-side item).

---

## 206. B2c′: ROUTE ERROR #2 REPAIRED — `IsBgA1At`'s core fields now name
## `refoldCoreBg`, and `bgA1_of_refold` is re-proved sorry-free on top of the
## registered honest input `BgDeltaPack` (2026-08-07)

**Part-0 audit: 4 confirmed verbatim, 1 stale line number, 1 spec correction.**
(i) B1's exports are exactly as the dispatch states them — `refoldCoreBg`
(`LowRegBgA1Refold.lean:317`) with `C0 = c0CoreData.C0 + (lowCoreDataBg[gB].C0 −
lowCoreDataBg[g].C0)`, `C1 = c0CoreData.C1 + lowCoreDataBg[gB].C1`,
`C2 = lowCoreDataBg[gB].C2`; `refoldCoreBg_diag` (`:388`); `refold_split_bg`
(`:493`).  (ii) the additivity bridge is verbatim: `a1Hi_add`/`a1Lo_add`
(`DeTurckRemainderLowBaseA1Comm.lean:219/:244`), `a1Hi_app`/`a1Lo_app`
(`:179/:193`).  (iii) `refold_aff_bg` is at **`:551`, not `:345`** — B1 inserted
206 lines above it; `:345` was №204's pre-B1 coordinate, content unchanged
(cores = a SUM OF ACTIONS `c0CoreData.a1Hi + oneCoreBg.a1Hi`; clauses =
2 continuity, 2 cores, 2 affine bounds, 1 square).  Consumer census re-verified:
`refold_aff_bg` → only `bgA1_of_refold`; `refold_aff` → only `lowreg_solve_open`.
(iv) `IsBgA1At`'s cores were against `c0CoreData + oneCoreBg`, as №200 says.

**Spec correction the reading forced (dispatch's optimistic branch is FALSE).**
The dispatch suggested `a1_comm hDim g (refoldCoreBg …)` might give the square
for free.  It does not, and the reason is structural: `a1_comm` is an identity
between ONE BUNDLE's two completions, i.e. it lands only at smooth states
`x = ι S`; `IsBgA1At.a1_square` is an identity between the two MAPS
`F.a1Hi, F.a1Lo : H³ → (… →L …)` at an ARBITRARY `x : H³`.  So the summand-square
route is not optional — the packet must carry its own square clause, exactly as
`c0_pack`/`c1_bg_pack` do, and `refold_aff_bg`'s `hcomm` proof is the template.
The `BgDeltaPack` interface below therefore has SEVEN clauses, not six.

**Landed — `LowRegBgA1Refold.lean` (739 → 938 lines).**  Public `deltaCoreBg
g gB` = `⟨lowCoreDataBg[gB].C0 − lowCoreDataBg[g].C0, 0, 0⟩` (the ΔC⁰ passenger
as a bundle); private `refoldBgMid` (the coefficientwise sum of `c0CoreData` and
`oneCoreBg`, `C2 := 0`) with its two field lemmas `refoldMid_split0/1`, both
closed by the single `simp only [refoldCoreBg, refoldBgMid, deltaCoreBg,
oneCoreBg, add_zero]` — the additive split is EXACT and needs only `add_zero`
threading, confirming №204's field spelling.  Public
**`refoldBg_a1Hi_split`/`refoldBg_a1Lo_split`**: the completed action of the
summed bundle equals `(c0CoreData.a1Hi + oneCoreBg.a1Hi) + deltaCoreBg.a1Hi`,
each proved by two `a1Hi_add` (resp. `a1Lo_add`) rewrites — the intermediate
bundle is unavoidable because `a1*_add` is binary and the decomposition is
ternary.  Public **`BgDeltaPack g gB : Prop`**, the registered honest input,
placed in this file (not the lift file) because it mentions only refold-layer
objects and its producer will sit BELOW the lift layer.

**Landed — `LowRegBgLift.lean` (249 → 313 lines).**  `IsBgA1At.a1Hi_core` /
`a1Lo_core` now read `F.a1Hi (ι S) = (refoldCoreBg g gB … S).a1Hi` — ONE bundle,
the one `refold_split_bg` certifies.  `bgA1_of_refold` gains
`(hΔ : BgDeltaPack g gB)`, takes `ρ0 := min ρ1 ρ2`, `Z := Z₁+Z₀`, `L := L₁+L₀`,
and builds `F := ⟨fun x => FHi x + GHi x, fun x => FLo x + GLo x⟩`.
`refold_aff_bg` was NOT restated, so `refold_aff` and the whole
`lowreg_solve_open` chain are byte-untouched.

**One real Lean obstruction, classified typeclass/coercion.**  `norm_add_le _ _`
failed twice with a `Type mismatch` on `@instHAdd (… →L[ℝ] …)
ContinuousLinearMap.add` versus `SeminormedAddGroup.toAddGroup.toAddZeroClass.
toAdd`: writing the CLM sum myself picks the `ContinuousLinearMap.add` path,
while `norm_add_le`'s expected type picks the seminormed path, and the two do
not unify at instance transparency.  Fix (same shape as `refold_aff_bg`'s
`simpa only [FHi] using norm_add_le …`): elaborate `norm_add_le (FHi x) (GHi x)`
with NO expected type via `have hsum := …`, put the affine calc on
`‖FHi x‖ + ‖GHi x‖`, and close with `hsum.trans hx` — `exact`'s defeq check at
default transparency crosses the instance paths that unification would not.
Also: three `show`→`change` replacements to clear the style linter.

**Verification.**  Focused checks GREEN on both touched files; targeted builds
`+…ShortTime.LowRegBgA1Refold` and (via a temporary probe module, since deleted)
`+…ShortTime.LowRegBgLift` both `Build completed successfully`; no `sorry`, no
new `set_option`, no remaining linter warning from either file.  Axiom probes —
`bgA1_of_refold`, `refoldBg_a1Hi_split`, `refoldBg_a1Lo_split`, `deltaCoreBg`,
`BgDeltaPack`, `IsBgA1At` — each `depends on axioms: [propext, Classical.choice,
Quot.sound]`.

**Denominators (honest).**  `ricci_flow_unif_existence`: **0%** (unstated).
Refold-route A1: ≈77% → **≈85%** — the identity half and the consumer-facing
statement are now both correct and proved; the missing 15% is the ΔC⁰ affine
packet itself.  `IsBgA1At` producer: the FIELDS are repaired (route error #2's
content is discharged) and the producer is PROVED **conditionally on a
registered input**; unconditionally it remains **0%** until B2a/B2b land — do
not report the A1 half as produced without that qualifier.  Full `IsBgLiftAt`:
**0%** (A2 half open).  Machinery **≈80%** (+0: the split lemmas are narrow
same-layer identities).  HCG compactness **≈3%**.  Route-error counter stays
**2/3** — this brick repairs #2, it does not add one.

**B2a handoff (unchanged from №205; my reading forces no correction).**  Build
`c0Bg_diff_tame` in `LowRegBgH2.lean` (~400 lines, 1270 → ~1670): ∃ `B0 B1 ≥ 0`
with `lowJetSq g 2 ((lowBaseData g gB T …).C0 − (lowBaseData g g T …).C0) ≤
(B0 R + B1 R · A)²` under `∑_{j<3}‖∇ʲT‖² ≤ R²`, `‖∇³T‖ ≤ A`.  Keep `bgCorrInt`
and `lowC0_bg_eq` PRIVATE — state it on the bare difference.  The three
quadratic arms cancel (`selfBase_decomp`: `ricciGoodLow`/`lc0VB`/`lc0Riem` take
no background argument), so only DLa/DLb (`h2_grid_tame` one-call swap),
Insert (`connLow_tame`), AMix (already linear) survive.  Then B2b `c0bg_pack`
must emit EXACTLY `BgDeltaPack g gB` as now stated in
`LowRegBgA1Refold.lean` — including the square clause, whose necessity is the
spec correction above — and its Lipschitz half rides `c0_bg_pair_h2` with the
`c0CorePair` radial-cutoff plumbing.  When it lands, drop `bgA1_of_refold`'s
`hΔ` argument and the "conditional" wording everywhere.

---

## 207. B2a: the tame ΔC⁰ analytic layer LANDED — `c0Bg_diff_tame` proved
## sorry-free, and the AMix arm needed a second cancellation that №205 missed
## (2026-08-07)

**The cancellation gate PASSES, and it was already proved.**  The dispatch's
first stop condition — "one of the three quadratic arms secretly takes the
background" — does not fire.  `bgCorr_eq` (`LowRegBgH2.lean`, pre-edit `:692`)
is exactly the definition-level verification asked for: it rewrites
`bgCorrFam = rhsSelfLow g gB T − rhsSelfLow g g T` into DLa + DLb + Insert +
AMix with no `ricciGoodLow` / `lc0VB` / `lc0Riem` term surviving.  Nothing had
to be re-derived from `selfBase_decomp`; those three arms take no background
argument, as №205 said.

**Landed — `LowRegBgH2.lean` (1270 → 1579).**  Public
**`c0Bg_diff_tame`**: `∃ B0 B1 : ℝ → ℝ ≥ 0` such that for all `T`, `δ ≤ 1/3`,
`0 ≤ δ`, the two fibre certificates, and `R A ≥ 0` with
`lowJetSq g 2 T ≤ R²` and `lowJetSq g 3 T ≤ A²`,
`lowJetSq g 2 ((lowBaseData g gB T …).C0 − (lowBaseData g g T …).C0)
≤ (B0 R + B1 R·A)²`.  Stated on the BARE difference; `bgCorrInt` and
`lowC0_bg_eq` stayed private, as specified.  No symmetry hypothesis `hT` is
required — the arms that consume symmetry are exactly the ones that cancel.

**Hypothesis-convention correction (statement-correctness first, counter 2/3).**
№206's spelling was `∑_{j<3}‖∇ʲT‖² ≤ R²` + `‖∇³T‖ ≤ A`.  I used the sibling
convention of `c0Coeff_aff` (`LowRegBgC0Core.lean:340`), `lowJetSq g 2 T ≤ R²`
+ `lowJetSq g 3 T ≤ A²`, because the B2b template `c0_core_affine`
(`LowRegBgC0Time.lean:122`) produces exactly that pair from `jet2_le_hs` /
`jet3_le_hs` and the radial cutoff.  The second hypothesis is strictly stronger
than `‖∇³T‖ ≤ A`, so the theorem is weaker and drops in with zero glue.

**Per-arm producers (all verified before consumption).**  DLa and DLb: the
promised one-call swap `h2_of_grid → h2_grid_tame`, over `dlaBg_grid` /
`dlbDiff_grid`.  Insert: `connLow_h2 → connLow_tame`, with `trace_h2` re-read
at `R` (its hypothesis is already the range-3 sum) and the fixed-background
factor `connDiffLoweredCc g gB − connDiffLoweredCc g g` constant.  AMix: see
below.  Assembly `bgCorrFam_tame → bgCorr_tame → c0Bg_diff_tame` via
`bgCorrInt_h2` (which already takes a plain scalar bound) and `fixedBg_h2`.

**№205's AMix sub-claim is FALSE, and the repair is a second cancellation.**
"AMix already affine, a pure restatement" does not hold: `amixForm_h2`'s
envelope is `const(R)·BK(A)·A`, and the `BK` factor is `kappaBg_h2`, whose tame
form `kappaBg_tame` (`LowRegCoeffJets.lean:1700`) is
`√(3(16A² + SF + BP(R)²))`.  It does NOT drop to the range-3 sum, because
`kappa_bg = kappa_self + kappa(g,gB) + pbLow` and `kappa_self` genuinely needs
`∇³P` at `H²`.  Bounding the two AMix normal forms separately therefore gives
`A²`.  What rescues affineness is one level below the arm split: `gB` enters
`lc0AMixHalfRF` only through the single slot
`slotExtendIter (lc0Kappa g g₁ gB)`, linearly, so the background difference
replaces that slot by `lc0Kappa g g₁ gB − lc0Kappa g g₁ g`, in which the
Koszul self-arm cancels; `kappaDiff_h2` (`LowRegInsertH1.lean:194`, public and
already imported) bounds it by an **R-only** constant.  The surviving product
then carries exactly one top derivative, from the `kappaSelf_h2` factor in the
inner slot, so `amixDiff_tame` is `(0 + B1 R·A)²`.  New private helpers
`bgKappa` / `bgAmixHalf` / `amixHalf_bg` / `bgAmix_eq` (mirrors of the private
lemmas at `LowRegBgC0PairH2.lean:47–140`, which are unreachable from here) plus
a private `slotIter_sub` (its public twin in `LieCorr0LowJet.lean:1306` is
outside this file's import closure).  **I score this a corrected sub-claim, not
route error #3** — the arm decomposition, the cancellation gate, and three of
four producers were exactly as dispatched, and nothing landed on a wrong
object; the counter stays **2/3**, but the user may want to adjudicate.

**API collapse instead of duplication (census-driven).**  `dlaDiff_h2`,
`dlbDiff_h2`, `insert_h2`, `amixForm_h2`, `amixDiff_h2` had zero consumers
outside `LowRegBgH2.lean` (the `insert_h2` hits in
`DeTurckRemainderLowBaseC1Lip.lean` are a different private theorem), and their
only in-file consumer `bgCorrFam_h2` is now a five-line wrapper over
`bgCorrFam_tame`.  So they were REPLACED by their tame versions rather than
duplicated: the file grew 309 lines instead of the ~400 budgeted, and
`amixForm_h2`'s 154-line normal-form bound is gone entirely (the difference
route never needs it).  Exhibits do NOT increase; they stay at NINETEEN.
Untouched, still the diagonal quadratic statements: `bgCorr_h2`,
`lowC0_bg_h2`, `lowC1_bg_h2`, `lowData_bg_coeff`, `lowA1_bg_bounds`.

**One real Lean obstruction, classified performance.**  `bgCorrFam_tame` first
hit `(deterministic) timeout at whnf` on the default budget.  Cause: eight
`nlinarith` calls discharging goals of the shape
`Ba0 R ≤ Ba0 R + Bb0 R + Bi0 R + Bm0 R`.  Swapping them for `linarith` put the
declaration well inside the default budget; **no `set_option maxHeartbeats` was
added**.  The cheap assembly pattern worth reusing: bound every arm by the SAME
`V := ΣB0ᵢ R + (ΣB1ᵢ R)·A` (one `pow_le_pow_left₀` each), then
`h2Jet_sum4 … V V V V` and close `4·(4V²) = (4V)²` by `ring`; feeding four
distinct affine bounds into one `nlinarith` is what is expensive.  Also: the
endpoint's proof-term mismatch (`hδ_lt` vs the statement's inline
`lt_of_le_of_lt hδ_le (by norm_num)`) is crossed by `change`, and the style
linter rejects `show` there.

**Verification.**  Focused check GREEN on `LowRegBgH2.lean`; targeted builds
`+…ShortTime.LowRegBgH2` and `+…ShortTime.LowRegBgTime` (the sole downstream
importer, exercised because five public names were removed) both
`Build completed successfully`; no `sorry`, no new `set_option`, no remaining
linter warning.  Axiom probes — `c0Bg_diff_tame`, `amixDiff_tame`,
`insert_tame`, `dlaDiff_tame`, `dlbDiff_tame`, and the untouched
`lowC0_bg_h2` — each `depends on axioms: [propext, Classical.choice,
Quot.sound]`.

**Denominators (honest).**  `ricci_flow_unif_existence`: **0%** (unstated).
Refold-route A1: ≈85% → **≈91%** — the ΔC⁰ packet's ANALYTIC half is done; the
remaining ≈9% is B2b, the packaging half (continuity, square, radial plumbing).
`IsBgA1At` unconditional producer: **still 0%** — `bgA1_of_refold` remains
conditional on the registered `BgDeltaPack` input until B2b discharges it.
Full `IsBgLiftAt`: **0%** (A2 half open).  Dedicated machinery ≈80% → **≈81%**
(+1pp justified: `dlaDiff_tame`/`dlbDiff_tame`/`insert_tame`/`amixDiff_tame`
are a genuinely reusable tame background-difference layer, and the AMix
kappa-cancellation identity is reusable at `H¹` as well).  HCG compactness
**≈3%**.  Route-error counter **2/3**.

**Dedup item recorded (deliberately deferred).**  `bgKappa`, `bgAmixHalf`,
`amixHalf_bg`, `bgAmix_eq`, `slotIter_sub` now exist as private copies in BOTH
`LowRegBgH2.lean` and `LowRegBgC0PairH2.lean`.  Canonical home is
`LowRegInsertH1.lean`, which both import.  Not done here because publishing
`bgAmix_eq` while the private twin still exists in `LowRegBgC0PairH2` makes the
name ambiguous there — the promotion and the two deletions must land together.

**B2b handoff.**  `c0bg_pack` must emit `BgDeltaPack g gB`
(`LowRegBgA1Refold.lean:902`, seven clauses).  Mirror `c0_core_affine`
(`LowRegBgC0Time.lean:122`) line for line: `S := lowRadial g ρ T`,
`R2 := C2·ρ` from `jet2_le_hs` + `lowRadial_norm`,
`A3 := C3·‖ccToHsLin g 2 3 T‖` from `jet3_le_hs` + `lowRadialH3_le` /
`lowRadialH3_core`, feed `c0Bg_diff_tame`, then `a1_diff` against the zero
bundle yields `Z := Ca·B0 R2`, `L := Ca·B1 R2·C3`.  Two things my arm-level
reading forces on B2b: (i) because `deltaCoreBg.C1 = 0` and `.C2 = 0`, the
`a1_diff` input is `lowJetSq g 2 ΔC⁰ + lowJetSq g 2 0`, so a `lowJet_zero`
mirror (`LowRegBgC0Time.lean:81`) is needed; (ii) `c0Bg_diff_tame` carries no
symmetry hypothesis, so `lowRadial_symm` is needed only where the surrounding
`lowCoreDataBg` plumbing already demands it, not for the affine clause.
Continuity clauses ride `c0_bg_pair_h2` (`LowRegBgA1Pair.lean:759`); the square
clause rides an `a1_comm_any` mirror (`LowRegBgC0Time.lean:237`) — per №206,
`a1_comm` itself does not suffice, it only lands at smooth states.  When B2b
lands, drop `bgA1_of_refold`'s `hΔ` argument and the "conditional" wording.

---

## 208. B2b: `c0bg_pack` LANDED sorry-free — `BgDeltaPack` is now a THEOREM and
## `bgA1_of_refold` is UNCONDITIONAL.  The A1 half of the fixed-background lift
## is produced (2026-08-07)

**Part-0 audit: 4 confirmed verbatim, 3 corrections — none of them a real
mismatch, all three in the favorable direction.**

(i) **Home.**  The dispatch's parenthetical "207 implies the C0Time file" is
wrong and the file cannot be the home: imports run
`LowRegBgA1Refold → LowRegBgC0Time`, so `deltaCoreBg` and `BgDeltaPack` are
invisible from `LowRegBgC0Time`.  `c0bg_pack` therefore lives in
`LowRegBgA1Refold.lean`, directly after the predicate it discharges — which is
also the canonical-home reading (producer beside interface, below the consumer
layer).  Everything it needs is in that file's closure: `c0Bg_diff_tame` and
`c0_bg_pair_h2` via `LowRegBgTime`, `a1_diff`/`jet*_le_hs`/`lowRadial*` via the
`DeTurck/` layer, `exists_extend_le` via `DenseExtension`.

(ii) **The square clause was FREE.**  №207 asked for an "`a1_comm_any` mirror".
No mirror was needed: `a1_comm` (`DeTurckRemainderLowBaseA1Comm.lean:164`,
public, in closure) is ALREADY stated "for ANY action bundle", and the private
`a1_comm_any` (`LowRegBgC0Time.lean:237`) is literally `a1_comm` plus
`simp only [incl12, incl32]` — a pre-A1Comm copy.  №206's structural point is
untouched and is why the clause exists at all (`a1_comm` lands only at
`x = ι S`); the lift to arbitrary `x` is `c0_pack`'s density step, transferred
verbatim.  So the one clause 206 flagged as "structurally non-free" cost four
lines.

(iii) **The Lipschitz recipe was incomplete, and the repair is a second
instantiation.**  `c0_bg_pair_h2` is a SINGLE-background Lipschitz estimate,
while `deltaCoreBg` is a background DIFFERENCE.  So it is consumed TWICE — at
`gB` and at the diagonal `gB := g` — and recombined by `jetSub` along
`ΔT.C0 − ΔU.C0 = (bg_gB(S) − bg_gB(V)) − (bg_g(S) − bg_g(V))`.  This is the
exact structural analogue of №207's own AMix repair (bound the difference, not
the two arms), and it costs nothing extra because `c0_bg_pair_h2` already
quantifies over `gB`.  Confirmed verbatim: `c0_core_affine`'s radial block,
`c0Bg_diff_tame`'s `lowJetSq g 2 T ≤ R²` / `lowJetSq g 3 T ≤ A²` convention with
no symmetry, `a1_diff`, the `lowJet_zero` need.

**Landed — `LowRegBgA1Refold.lean` (938 → 1494).**  Five private mirrors of the
zero-bundle block (`zeroBundle`, `zeroBundle_a1`, `iterZ`, `lowJetZ`,
`zeroBundle_pair` — the originals are private in `LowRegBgC0Time`);
`zeroBundle_pair` returns the two `= 0` equalities rather than `‖·‖ = 0`, which
deletes an `opNorm_zero_iff` step at each call site.  Private `c0bg_aff` (the
affine half: `c0_core_affine` with `c0Coeff_aff → c0Bg_diff_tame` and
`c0CoreData → deltaCoreBg`; `Z := Ca·B0 R2`, `L := Ca·B1 R2·C3` exactly as
dispatched; `ρ0 := 1`, since `c0Bg_diff_tame` imposes no radius cap).  Private
`c0bg_pair` (the Lipschitz half: `c0CorePair`'s radial-difference plumbing —
`lowRadial_lip`, `lowRadial_h3_sub`, `Lr := 1 + r₀/ρ` — with the two-background
recombination above; each envelope collapses to `2(P²+Q²)·D²` by `ring` after
`D2 = C2·D`, `D3 = C3·Lr·D`, `N = D`, and the four constants are collected into
`Kc := √(4ΣP²)` so `a1_diff` is fed at `R := Kc·D`).  Public **`c0bg_pack :
BgDeltaPack g gB`**, `c0_pack`'s assembly line for line.  `BgDeltaPack`'s
docstring was rewritten from "registered honest input, not a proved result" to
the proved predicate it now is; the name is kept because it is the interface
`bgA1_of_refold` consumes.

**Landed — `LowRegBgLift.lean` (313 → 306).**  `bgA1_of_refold` lost
`(hΔ : BgDeltaPack g gB)`; the single line `obtain … := hΔ` became
`obtain … := c0bg_pack hDim g gB` and nothing else in the proof moved.  Consumer
census re-verified before editing: `bgA1_of_refold` had ZERO Lean consumers
outside its own file (only docstrings and notes), so the signature change was
free.  Every "conditional" / "registered obligation" qualifier for the A1 half
is gone from both `IsBgA1At`'s and `bgA1_of_refold`'s docstrings; the PDE-honesty
paragraph (`refold_split_bg` reconstructs the arbitrary-background remainder
exactly, so the `deltaCoreBg` summand may not be dropped) is unchanged.

**Two Lean facts worth keeping.**  `incl32_c0` sits in the nested namespace
`…IntrinsicSpectral.LowRegBgC0Core` and needs that prefix from the refold file.
And the `hδZ` slot buried in `lowCoreDataBg` is `zero_fibre_bound` (private in
`LowRegBgTime`), but passing this file's `zero_fb_refold` instead is fine —
definitional proof irrelevance means `simpa only [deltaCoreBg, lowCoreDataBg, …]`
crosses it with no `change`.  No genuine obstruction arose; the two errors in the
whole brick were a missing namespace prefix and one unused `simp` argument.

**Verification.**  Focused checks GREEN on both touched files; targeted builds
`+…ShortTime.LowRegBgA1Refold` and `+…ShortTime.LowRegBgLift` both
`Build completed successfully`; no `sorry`, no `set_option` added (a first-draft
`linter.unusedVariables false` on `c0bg_pair` proved unnecessary and was
removed), no remaining linter warning from either file.  Axiom probes:
`'…IntrinsicSpectral.c0bg_pack' depends on axioms: [propext, Classical.choice,
Quot.sound]` and `'…IntrinsicSpectral.bgA1_of_refold' depends on axioms:
[propext, Classical.choice, Quot.sound]`.

**Denominators (honest).**  `ricci_flow_unif_existence`: **0%** (unstated).
Refold-route A1: ≈91% → **100%** — the A1 half of the fixed-background lift is
produced, unconditionally: `bgA1_of_refold` now takes only `hDim`, `g`, `gB`,
`hK`.  `IsBgA1At` unconditional producer: 0% → **100%**.  Full `IsBgLiftAt`:
**0%** — the A2 half `IsBgA2At` is the remaining conjunct and is untouched; do
not report the lift as produced.  Dedicated machinery ≈81% → **≈82%** (+1pp:
`c0bg_aff`/`c0bg_pair` are a reusable "affine + Lipschitz ⟹ completed packet"
pattern for any background-difference bundle, and the two-background
recombination is the reusable shape for the A2 sibling).  HCG compactness
**≈3%**.  Route-error counter **2/3** — no route error here; the three part-0
corrections were all reading corrections that made the brick cheaper.

**Exhibits stay at NINETEEN** (`c0bg_aff`/`c0bg_pair` are private; `c0bg_pack`
has a consumer, `bgA1_of_refold`).

**Next.**  Item 3, the **A2 half**: `IsBgA2At` needs the contraction bounds.
The B2b shape suggests the same tactic — if the A2 background difference admits
a `c0_bg_pair_h2`-style single-background estimate quantified over `gB`, it can
be consumed twice and recombined, dissolving the two-metric cap question.  A
scout should check that before the old class-4 stop condition is re-litigated.
Item 4, the G3 `_unif` lane (next node `trace24_h2_lip`), remains the seam that
turns `bgA1_of_refold`'s per-metric `Z`/`L` into class-fixed data.

---

## 209. G3 lane node 2: `trace24_h2_lip_unif` LANDED sorry-free — and the
## brick's NAMED missing lemma was a FALSE WALL: `cometricTrace_rfns_p` already
## existed, public and rank-generic (2026-08-07)

No stop condition fired.  The brick is done, but its two halves came out the
opposite way round from the dispatch, and that is the entry's main content.

**(0) PART-0 CORRECTION — part 1 did not exist as a task.**  Entry 202's "Next
node up the lane" named as the ONE missing input a class-uniform pointwise fibre
bound for `cometricDoubleTraceField g p`, "the analogue of `rfns_idEndo_le`", and
priced it as the whole next brick.  It is already in the tree, PUBLIC and
sorry-free:

    theorem cometricTrace_rfns_p (p : ℕ) (g : SmoothRiemannianMetric I M) (x : M) :
        riemannianFiberNormSq g (p + 2) p x
            ((cometricDoubleTraceField g p).toSection x) ≤
          (Module.finrank ℝ E : ℝ) ^ (p + 6)

`Analysis/Parabolic/RicciLinearization/CometricTraceSelfBound.lean:220`
(namespace `…Analysis.Parabolic.TensorSpectral`; argument order `p`, `g`, `x`).
It is RANK-GENERIC, single-metric, and its constant is a PURE DIMENSION constant
— so the dispatch's premise that the bound would have to be `Λ`-expressible via
the metric-equivalence hypothesis is also wrong; no class hypothesis enters.  Its
own route is the private succ EQUALITY `traceSucc_rfns` (same file) on top of the
public `rfns_slotExtendFib_eq`, not a component computation.  The sharper p = 2
case `cometricTrace_rfns` (`:42`) exists too.  Axiom-probed clean here.

**This is an over-count exhibit, proposed as TWENTY** (planner to adjudicate):
the same shape as exhibit 19 — a named load-bearing gap that dissolves on a
grep.  It is NOT a route error: nothing wrong was built, and the honest-input
audit is unaffected.  Counter stays **2/3**.  The recurring lesson (memory note
`ricciflow-agents-overcount-walls`) held again: grep-verify a named missing
lemma against the WHOLE tree, including the `Analysis/Parabolic/` and
`Analysis/Sobolev/` trees, before pricing it as a brick.  Deliberately rejected,
as at 202: `exists_bound_riemannianFiberNormSq_smoothCcTensor`, which
`RemainderCoeffPerOrderJetEnvelopes` still uses internally for this very field
and which cannot be uniformized.

**(1) LANDED — `trace24_h2_lip_unif`** (new `ShortTime/UnifTraceLip.lean`, 493
lines, name 19 letters).  Class-uniform under EXACTLY the ruled pair
(`MetricUniformEquivalentOn univ gBase g Λ` + `∀ a ≤ 3,
MetricCovDerivOrderBoundOn univ a g gBase Λ`; no fourth jet), same `∃ ρ C`
quantifier prefix as node 1.  Both conjuncts of the metricwise
`trace24_h2_lip` (`…C2Lip.lean:1358`, READ-ONLY, never re-elaborated) are
uniformized verbatim, with the private `c2JetSq` abbreviation spelled out.
**Sorry-free** (axiom probe: `propext`, `Classical.choice`, `Quot.sound`).

**(2) The real work was where the dispatch expected none: the slot-insertion
jet tower.**  `D₂ = slotInsertEndoCc g 3 dEndo` and `D₄ = slotInsertEndoCc g 5
dEndo` must be reduced to slot 1, where node 1's `invCoeff_h2_lip_unif` bites.
The monolith does this with private `insertSucc_jet_c2` / `insert3_jet_c2` /
`insert5_jet_c2`.  The public generic
`rfns_iteratedCovGrad_slotInsertEndoCc_le_endo`
(`MetricArmCoeffJetTower.lean:2795`) is the WRONG DIRECTION — it bounds slot `s`
by slot **0**, not by slot 1 — so the succ step had to be rebuilt.  Done here
from three public producers, generic in the slot index:
`tsSlotInsertEndoCc_succ_eq_reindex_slotExtend` (`TsRungs.lean:1172`),
`rfns_iteratedCovGrad_rsDomDomCongr_both_eq` (`MetricArmCoeffJetTower.lean:2706`),
`rfns_iteratedCovGrad_slotExtend_le` (`OperatorFieldFibreNormJet.lean:680`),
giving `insSuccPt → insSuccSq → insSuccJet → ins3Jet (n²) / ins5Jet (n⁴)`.
**Reusable finding worth propagating**: several private helpers of
`MetricArmCoeffJetTower` have PUBLIC `ts…`-prefixed twins in
`CurvatureCoefficientDifferenceJetTower/TsRungs.lean`; check there before
re-deriving.

**Translation table** (all four inputs had class-first siblings):

| metricwise input | class-first sibling |
| --- | --- |
| `invCoeff_h2_lip` | `invCoeff_h2_lip_unif` (node 1) |
| `appRS_h2_h2_h2 g 4 4 2` | `appRS_h22_unif … 4 4 2` |
| `appRS_h2_h2_h2 g 6 6 4` | `appRS_h22_unif … 6 6 4` (valence-generic, verified) |
| `c2JetSq g (cometricDoubleTraceField g p)` | `dtJet` (here) + `volumeReal_cross` |

`dtJet` is the ~25-line parallel-field window: the field is parallel
(`cometricDoubleTraceField_covGrad_eq_zero`), `iteratedCovGrad_eq_zero_of_
covGrad_eq_zero` (`KoszulSectionParallelRaise.lean:44`) kills orders 1 and 2,
and order 0 is `cometricTrace_rfns_p` through
`norm_le_of_pointwise_fiberNormSq_bound_rs`.  Same three-step shape as 202's
`idSlotJet`.

**Closed constant.**  `vol = volCompareC Λ · vol_{gBase}(M)`,
`n = Module.finrank ℝ E`: `A₂ = √(n^8·vol)`, `A₄ = √(n^10·vol)`,
`K₂ = C₂·A₂·(3·Cinv)`, `K₄ = C₄·A₄·(9·Cinv)`, `C = K₂ + K₄`; `ρ`, `Cinv`
inherited verbatim from `invCoeff_h2_lip_unif`.  Lean lesson recorded in the
same-name note: keep the dimension SYMBOLIC inside `A₂`/`A₄` — writing `3^8` and
then `rw [hDim]; norm_num` left the multiplier of `mul_le_mul_of_nonneg_left` as
a metavariable and produced two stray `⊢ 0 ≤ ?m` goals.

**Verification.**  Focused check GREEN (22 s, no warnings); targeted module build
GREEN (9929 jobs); axiom probe through a temporary scratch module, deleted
afterwards.  Files touched: `UnifTraceLip.lean` (new), `UnifTraceLip.md` (new),
`UnifInvCoeffLip.md` (its "Next node" section corrected), this ledger.  All
unrelated dirty files preserved.

**Honest denominators.**  `ricci_flow_unif_existence` **0%** — still unstated in
Lean.  G3 class-uniform radius lane: **2 of ~55 nodes ≈ 4%** (node 1
`invCoeff_h2_lip_unif`, node 2 `trace24_h2_lip_unif`).  `IsBgLiftAt` producer
**0%** (A2 half untouched; unchanged by this brick).  Dedicated uniform-existence
machinery ≈82% → **≈82.5%** (+0.5pp, and only that: the brick consumed a
PRE-EXISTING public fibre bound, so its one genuinely new reusable asset is the
slot-generic jet tower `insSuccJet`/`ins3Jet`/`ins5Jet`, which every later node
carrying a slot-inserted endomorphism will reuse; against a 55-node denominator
a bigger bump would be dishonest).  Whole HCG ≈**3%**.

**Next node up the lane: `pairTrace_h2_lip`** (private, `…C2Lip.lean:1569`), the
first consumer of `trace24_h2_lip` (other call sites `:3969`, `:5230`, `:5348`).
Its inputs are ALREADY fully covered: `trace24_h2_lip` (this brick),
`appRS_h2_h2_h2 g 6 4 2` (`appRS_h22_unif … 6 4 2`), and the diagonal windows
`J₂ = c2JetSq g (pureTrace g g 2)`, `J₄ = c2JetSq g (pureTrace g g 4)` — and by
`pureTrace_toSection` (`PairTrace.lean`, `@[simp]`, `rfl`) the section of
`pureTrace g₀ g₁ s` IS `cometricDoubleTraceFib g₁ s`, so `pureTrace g g p` and
`cometricDoubleTraceField g p` agree and `dtJet` already covers `J₂`/`J₄` after a
one-line `SmoothCcTensor.ext`.  Node 3 should therefore be mechanical
(prediction stated explicitly so the next agent can score it).

---

## 210 (planner, 2026-08-07 pre-dawn). Entry 209 ACCEPTED (exhibit 20
## CONFIRMED); the A2 dossier ADOPTED — R2 is ruling-free; R2-s1 dispatched

**209 accepted.**  `trace24_h2_lip_unif` green; the slot-succ jet tower is
the reusable asset.  **Exhibit 20 CONFIRMED**: 202's "single missing
lemma" existed public (`cometricTrace_rfns_p`,
`Analysis/Parabolic/RicciLinearization/CometricTraceSelfBound.lean:220`,
pure DIMENSION constant — better than Λ-expressible).  Counter unchanged
2/3 (nothing wrong built).  One flag: `UnifTraceLip.lean` carries a
`maxHeartbeats 1600000` mirroring the metricwise theorem — technically
"new" under the standing rule; tolerated as an inherited mirror, noted
for the morning review, not to be repeated without need.

**The A2 dossier (scout, overnight cont. 10) ADOPTED in full**:
- `c2_h2_small` genuinely diagonal, but `topKernel_eq` (PUBLIC,
  `(g g_bg)`, `LowBaseAction.lean:3768`) splits its integrand so that
  `lieRefold2` and `ricciTop` are background-BLIND and CANCEL in the
  `gB − g` difference; the survivor `phi_dev_h2` is PUBLIC and
  two-metric (`LowRegPathSplit.lean:469`).  The consume-twice tactic
  applies one order up from B2b.
- STOP-CONDITION AUDIT (quoted text): it forbids the class-UNIF
  `H⁴ ↔ jet-4` comparison; the per-metric transfer (`a2_pair` via
  `appD2Hs_norm` + `appCc_h2_h3_h1`) consumes 2 coefficient jets with
  `H⁴` as the operator DOMAIN — it does NOT fire.  The guard sits on
  the G3 `_unif` lane, where A2 will be in the identical position to
  A1's Z/L seam.
- TRAPS pre-registered: `D.contract` from the RADIUS knob (`C·r`,
  shrinkable; pick `r ≤ min(ρ, 1/(2C))` ⟹ contract ≤ 1/2), never the
  δ-cap (`κ·3/4` is not automatically < 1); the producer is
  per-`(g, gB)` — `IsBgLiftAt` stays 0% until G3 closes BOTH halves.
- R1 (1 session) gated on un-privatizing `:9493`/`:9656` in a READ-ONLY
  file — MOOT: R2 (2 sessions, ruling-free) proves the identical
  statement and shares items 3–5 with R1.
- Eight ledger-said-diagonal objects verified already two-metric —
  the reason R2 is cheap.  Exhibits: **20**.

**R2-s1 DISPATCHED** (reports 211): item 1 — extract the
`pathIntegralCoeffField` integrand-linearity lemma (~15 lines; proof
inline at `LowRegC2JetTower.lean:99–139`); item 2 — `c2Bg_h2_small`
(~120 lines, new light file): the `(g, gB)` fibre+jet C2 smallness via
the `topKernel_eq` cancellation + `phi_dev_h2` at `gB` and `g` +
`path_add_sub_jet`/`path_add_sub_cap`.  R2-s2 next: `radialA2Bg_pair`
mirror + token-widen the three `g g` decls in `LowRegBgA2Time.lean` +
`bgA2_of_radial` (7 fields, 5 free from `radialA2Bg_lip`).

---

## 211. R2-s1 LANDED, both items: the path-integral integrand-linearity lemmas
## are extracted public, and `c2Bg_h2_small` — the `(g, gB)` C2 smallness in
## both clauses — is proved sorry-free.  The dossier's cancellation claim is
## CONFIRMED against the Lean text (2026-08-07)

**Item 1 — extraction, `LowRegC2JetTower.lean` (319 → 387).**  The inline
`heq` block of `path_add_sub_jet` is now the public theorem

```
path_add_sub_eq : ∫Φ + ∫Ψ − C = ∫(Φ + Ψ − C)
path_sub_eq     : ∫Φ − ∫Ψ     = ∫(Φ − Ψ)
```

(rank-generic `r`, `(r,2)` coefficient fields, same realized segment).  Both
take the combined integrand's joint-smoothness certificate as an explicit
argument, because the `Bg` lane must NAME the two path integrals before
subtracting them.  For the same reason `armConst` — the certificate of a
*constant* family — was un-privatized in the same file; it was the only
blocker to a caller building the `Φ + Ψ − C` certificate itself, and the
monolith's `arm_const` (`:1739`) is private and unreachable.
`path_add_sub_jet`'s public statement is **byte-identical**; its body lost 35
lines and gained one.

*Left on the table, deliberately*: `path_add_sub_cap` (`LowRegPathSplit.lean:337`)
carries a VERBATIM duplicate of the same `heq`.  `LowRegPathSplit` is upstream
of the 13.8k-line monolith, so editing it re-elaborates the whole chain (№194).
Whoever next rebuilds that chain for another reason should move
`path_add_sub_eq` down and let both consumers share it.

**Item 2 — `c2Bg_h2_small`, new file `ShortTime/LowRegBgC2Small.lean` (397
lines), sorry-free, axiom-clean, NO `maxHeartbeats`.**  Statement is
`c2_h2_small` with `lowBaseData g g T` → `lowBaseData g gB T`, binders mirrored
exactly (including the statement-level `let A := …`).

**Certificate audit** (the dispatch asked): `lowBaseData g gB T hδ_lt hδ hδZ`
demands `hδ`/`hδZ` **at `g` alone**; `gB` is a bare parameter appearing in no
hypothesis.  So the Bg statement needs NO extra δ-certificate — none was added.
`phi_dev_h2`'s `g_bg` is free in the same way.

**Both STOP conditions checked against the Lean text and NOT fired.**
(i) `topKernel_eq`'s three-term split has `lieRefold2 g T s` and
`ricciTop g gm T` carrying no `g_bg` **syntactically**, so the background
difference leaves `Dev_gB − Dev_g` and **nothing else** — `kerBgDiff` is two
`rw [show … = _ from topKernel_eq …]` plus `abel`.  The dossier is confirmed,
not merely plausible.  (ii) `phi_dev_h2`'s conclusion is a CONJUNCTION —
fibre-pointwise `≤ (C·R)²` and `∑ i ∈ Finset.range 3 … ≤ (C·R)²`, the latter
being `lowJetSq g 2` after `simp only [lowJetSq, Nat.reduceAdd]` — so it does
cover both clauses.

Assembly (five named pieces, each under the default heartbeat budget):
`c2BgPath` (`c2_eq` + `path_add_sub_eq`, used at both backgrounds) →
`path_sub_eq` → `kerBgDiff` → `devBgCap` (`phi_dev_h2` ×2 recombined by
`riemannianFiberNormSq_sub_le` / `jetSub`) → `pathBoth` (both clauses through
one path integral) → triangle against the diagonal `c2_h2_small` black box.
Constants `Cd = 2(C₁+C₂)`, `C = 2(Cd+C₀)`, `ρ = min ρ₀ ρd`.

**Why the difference route, confirmed empirically**: the direct route (rerun
`c2_h2_small`'s proof at `g_bg := gB`) is mathematically the same single-call
change, but `lieRefold2_h2` `:9493`, `ricciTop_h2` `:9656`, `path_add_sub_h2`
`:2889`, `jet2_fiber` `:2958`, `jet_add` `:3959`, `arm_const` `:1739` are ALL
private in the read-only monolith.  That is exactly the R1 gate 210 called
moot, and it is real.

**Exhibit sweep — five would-be helpers already existed public** and were
reused, none rewritten: `jetSub` and `opJetAdd` (`LowRegOpJetWindows.lean:124`,
`:170`), `riemannianFiberNormSq_add_le`/`_sub_le`
(`CovGradRoughLap/FiberNormSubadditivity.lean:112`, `:141`), `path_jetL2_le`
(`ParametricJetIntegral.lean:331`),
`riemannianFiberNormSq_pathIntegralCoeffField_le_sq`
(`PathIntegralFibreNormTransfer.lean:164`).  Exhibits: **21**.

**Heartbeats**: the first, one-declaration version of `c2Bg_h2_small` needed
`maxHeartbeats 1600000`.  Rather than mirror an option, the proof was split
into `c2BgPath` / `devBgCap` / `pathBoth`; every declaration now fits the
**default 200000**.  No new `set_option` anywhere.  (Signal worth keeping:
`c2_h2_small` itself runs at the default — a Bg sibling needing 8× that was the
tell that the monolithic shape was carrying avoidable cost, not that the
mathematics was harder.)

Full route, four durable Lean lessons and the reuse table are in
`LowRegBgC2Small.md`; the extraction note is appended to
`LowRegC2JetTower.md`.

**Verification**: focused checks green on both touched files; targeted builds
green for `…DeTurck.LowRegC2JetTower` and `…ShortTime.LowRegBgC2Small`; axiom
probes on `path_sub_eq`, `path_add_sub_eq`, `path_add_sub_jet`, `armConst`,
`kerBgDiff`, `c2Bg_h2_small` all report the three standard axioms.

**Numbers**: (N) `ricci_flow_unif_existence` **0%** (still unstated-in-proof at
`ExtendViaUniqueness.lean:98`).  A2 dedicated machinery ≈85% → **≈90%**
(`c2Bg_h2_small` was the one genuinely missing analytic input; what remains for
A2 is the `radialA2Bg_pair` mirror and the `IsBgA2At` field wiring, both
mechanical).  `IsBgA2At` producer **0%** — R2-s2 assembles it.  `IsBgLiftAt`
**0%** (needs BOTH halves; the A1 half is produced since 208, the A2 half is
not).  Uniform-existence machinery ≈80% → **≈82.5% (±0.5)**.  Whole HCG ≈3%.
Route-error counter unchanged at **2/3** — nothing built on an unverified
claim; both dossier claims were checked against the Lean text before use.

**Next = R2-s2**: `radialA2Bg_pair` mirror + token-widen the three `g g` decls
in `LowRegBgA2Time.lean` + `bgA2_of_radial` (7 fields, 5 free from
`radialA2Bg_lip`).  Two constraints this pass forces on it: (i) `c2Bg_h2_small`
carries a statement-level `let A := …`, so the consumption site must ascribe
the expected type in the `have`, exactly as `c2_h2_small`'s consumers already
do; (ii) the contraction knob is the RADIUS (`r ≤ min(ρ, 1/(2C))` ⟹
`D.contract ≤ 1/2`), never the δ-cap — 210's pre-registered trap stands.

---

## 212. R2-s2 LANDED, all three parts: `IsBgA2At` is produced, and with it the
## WHOLE fourteen-field `IsBgLiftAt` per `(g, gB)`.  The A2 half needed no
## refold — the diagonal-only step was a single `c2_h2_small` call (2026-08-07)

**Part 1 — the widening, and the dossier claim CHECKED, not assumed.**  The two
private helpers `a2HiBg_total_le`/`a2LoBg_total_le` (`LowRegBgA2Time.lean`) are
pure token widenings: each body is a `ccToHsLin_dense` density induction whose
only inputs are its own `hcont`/`hcore`/`hbd` hypotheses (`isClosed_le` +
`DenseRange.induction_on` + `rw [← hcore S]`), and neither mentions `lowCoreData`
(the diagonal bundle) at all — only `lowCoreDataBg`.  Entry 210's dossier is
confirmed against the Lean text.

`lowA2Bg_small` had **exactly one** genuine diagonal dependence, the call
`c2_h2_small hDim g`.  Everything else was already background-free
(`lowRadial_norm`/`_symm`, `a2_pair`) or already two-metric (`radialA2Bg_lip
g gB`).  Consumer census beforehand (`rg`, tracked + untracked): `lowA2Bg_small`
had **zero** consumers anywhere and the two helpers only their own enclosing
theorem — so the widening was churn-free, no call site needed a `g g`
instantiation.  `hiAffA2Bg`/`loAffA2Bg`/`affA2Bg_comm`/`affA2Bg_data` were left
diagonal deliberately: mechanical to widen, but no consumer on the critical path.

**Part 2 — `radialA2Bg_pair`, `LowRegBgA2Time.lean` (494 → 543 lines).**  Home
justified by import direction: the statement needs `lowCoreDataBg`
(`LowRegBgTime.lean`) *and* `c2Bg_h2_small` (`LowRegBgC2Small.lean`, a light
DeTurck-only file that must not import the Bg-core layer), and `LowRegBgA2Time`
already imported the former — one added import, no new file.

Stated in **`radialA2_pairR`'s free-cutoff binder shape**, not `radialA2_pair`'s
fixed-ρ one, and this is not cosmetic: `C` must be bound before `r` or the
radius knob of Part 3 is circular.  One theorem, not two — the fixed-ρ variant
has no consumer.  The proof is the diagonal body with `c2_h2_small hDim g` →
`c2Bg_h2_small hDim g gB` and `lowCoreData` → `lowCoreDataBg`; `a2_pair` is
consumed unchanged, being background-BLIND (it quantifies over every
`A : LowBaseActionData g`).  The `let`-ascription trap fired exactly where 211
predicted and was handled by writing the expected type in the `hcoreBd` `have`.
The widened `lowA2Bg_small` body got SHORTER: the ~40-line inline block
collapsed to a three-line `obtain`.

**Part 3 — `LowRegBgLift.lean` (307 → 415 lines), three declarations.**

`IsLowBoundsAt.realizeCc` — the realization certificate at the full class radius
`K.realize`, in the `ccTensorToHs` spelling.  Forced by binder order: the A2
producers take `hreal` at `ρ₀` and *return* a smaller cap, so a theorem whose
conclusion is `∀ D : BgLiftData K, …` needs a `D`-independent radius to start
from.  `BgLiftData.realize` is now its one-line corollary — same statement, same
public name, proof body deleted.

`bgA2_of_radial` — `∃ ρ0 C, 0 < ρ0 ∧ 0 ≤ C ∧ ∀ D : BgLiftData K, D.coeffRadius
≤ ρ0 → (C * D.coeffRadius ≤ D.contract → IsBgA2At g gB K hK D)`.  Two sources
for seven fields: `radialA2Bg_lip` for the two smooth-core read-offs against
`lowCoreDataBg g gB`, `lowA2Bg_small` for the two continuities, the inclusion
square, and the two bounds `≤ C * D.coeffRadius`.  **The knob is the RADIUS and
`C` is bound OUTSIDE `∀ D`** — had `C` been produced per-`D` (a literal mirror
of A1's `Z`/`L`) the domination would be circular.  The δ-cap is not a knob:
`K.threshold ≤ 1/3` is pinned by the realization certificate.  210's trap:
avoided.  Note the radius is not free either — `BgLiftData.state_le_radius`
forces `K`'s state radius down with it.

`bgLift_of_radial` — the conjunction on `ρ0 := min`, built as
`{ toIsBgA2At := …, toIsBgA1At := … }`.  **Per `(g, gB)` the fourteen-field
`IsBgLiftAt` is now a theorem**, conditional on exactly three scalar dominations:
`Z ≤ D.zero`, `L ≤ D.slope`, `C * D.coeffRadius ≤ D.contract`.  The docstring
states in as many words that this is NOT class-uniformity.

**No stop condition fired.**  In particular `a2_pair`'s hypothesis shape
accepted `c2Bg_h2_small`'s output verbatim (both are the fibre-pointwise +
`lowJetSq` conjunction at `(C·R)²`), and the old class-4 guard stayed off, as
210 predicted.  **No new `set_option`**: `radialA2Bg_pair` fits the default
200000 like its diagonal twin; `lowA2Bg_small` keeps only its pre-existing pair.

**Why the A2 half was cheap where A1 was three sessions**: the complete
second-order coefficient is *small at every background* (`c2Bg_h2_small`), so
the bound fields are met by shrinking one radius.  The A1 order-zero arm is not
affine off the diagonal (№196's scaling witness), which is what forced the
refold, `deltaCoreBg`, and the whole ΔC⁰ tame layer.  The asymmetry recorded at
№196 explains the entire cost difference.

**Verification**: focused checks green on both touched files; targeted builds
green for `…ShortTime.LowRegBgA2Time` and `…ShortTime.LowRegBgLift` (10064 jobs,
zero warnings attributable to the touched files); axiom probes on
`lowA2Bg_small`, `radialA2Bg_pair`, `bgA2_of_radial`, `bgLift_of_radial`,
`IsLowBoundsAt.realizeCc`, `BgLiftData.realize` all report exactly `propext`,
`Classical.choice`, `Quot.sound`.

**Numbers.**  (N) `ricci_flow_unif_existence` **0%** — still unstated-in-proof at
`ExtendViaUniqueness.lean:98`; nothing in this brick touches it.  A2 dedicated
machinery ≈90% → **100%** (nothing analytic remains for A2).  `IsBgA2At`
producer 0% → **100% per `(g, gB)`**.  Full `IsBgLiftAt`: **per-`(g, gB)`
PRODUCED (100%) via `bgLift_of_radial`; class-uniform 0%** — the three
dominations `Z`/`L`/`C` are the G3 seam and nothing else in the structure is
open.  Uniform-existence machinery ≈82.5% → **≈85% (±1)**.  Whole HCG ≈**3%**.
Route-error counter unchanged at **2/3**: the one dossier claim this brick
relied on (the two helpers are background-blind) was verified declaration by
declaration before being used.  Exhibits: **21** (nothing new claimed).

**Next**: the G3 `_unif` lane is now the *sole* remaining obstruction to a
class-uniform `IsBgLiftAt` — 2 of ~55 nodes done, next node `pairTrace_h2_lip`
(`…C2Lip.lean:1569`, all inputs covered per №209).  A2 adds one new node to that
lane: a class-uniform version of `bgA2_of_radial`'s `C`, i.e. class-uniform
`c2Bg_h2_small` + `a2_pair` constants.

---

## 213 (planner, 2026-08-07 05:07 — NIGHT CLOSE). Entry 212 ACCEPTED; the
## per-(g,gB) lift is COMPLETE; morning frame

**212 accepted.**  The knob-trap catch (the A2 constant `C` bound OUTSIDE
`∀ D` — a literal A1 mirror would have made the domination circular) is
the kind of statement-correctness the 2/3 counter bought; ratified.
`bgLift_of_radial` is the night's capstone: the FULL `IsBgLiftAt`
produced per-`(g, gB)`, both halves, all axiom-clean, with exactly three
honest per-metric dominations (`Z ≤ D.zero`, `L ≤ D.slope`,
`C·D.coeffRadius ≤ D.contract`) as the visible seam.  The A2 stop
condition NEVER fired — audited twice with quoted text; the feared
class-4/H⁴ wall was a property of the abandoned canonical-completion
route, not of the fibrewise/difference route the lift actually took.

**Overnight arc summary (entries 194–212, ~22:30–05:07).**  11 executor
bricks + 4 read-only scouts/dossiers; ~30 new public declarations, all
`[propext, Classical.choice, Quot.sound]`; 4 new files
(`DeTurckRemainderLowBaseA1Comm`, `UnifInvCoeffLip`, `UnifTraceLip`,
`LowRegBgC2Small`) + `LowRegBgA1Refold`/`LowRegBgH2`/`LowRegBgA2Time`/
`LowRegBgLift` substantially extended; one ledger rollover (PLAN7).
Route errors: #2 scored (203) AND repaired (206–208) the same night;
two near-misses gated pre-landing (199, 210-adjacent).  Exhibits
19 → **21**.  Standing perf idiom established: split declarations,
never add `set_option`.

**Morning review items** (user): (1) counter **2/3** — both dossiers in
the ledger (155 old; the ΔC0 bundle 199/200/203, repaired); reset or
let stand.  (2) Exhibit 20/21 adjudications recorded at 210/211.
(3) `UnifTraceLip.lean` carries a mirrored `maxHeartbeats 1600000`
(tolerated, 210) — optionally split it per the new idiom.  (4) Two
dedup chips: the `bgKappa`-family twins (207, atomic promotion into
`LowRegInsertH1.lean`) and the `path_add_sub_cap` duplicate in
`LowRegPathSplit` (211, wait for a legit monolith rebuild).
(5) **CHECKPOINT COMMIT** — the tree now carries ~16 sessions of
verified uncommitted work including tonight's entire arc.
(6) Next lane by default: G3 node 3 (`pairTrace_h2_lip`, predicted
mechanical, inputs covered) and onward — the ~54-node `_unif` lane is
the sole remaining gap between `bgLift_of_radial` and a class-uniform
lift.

**Honest denominators at night close.**  (N) `ricci_flow_unif_existence`
**0%** (unstated in proof; nothing overnight touches its sorry).
Per-(g,gB) `IsBgLiftAt`: **100% produced** (`bgLift_of_radial`).
Class-uniform lift: **0%** (G3, 2/~56 nodes).  Dedicated
uniform-existence machinery ≈**85%**.  Whole HCG ≈**3%**.

---

## 214. G3 lane node 3: `pairTrace_h2_lip_unif` LANDED sorry-free.  Entry 209's
## "MECHANICAL, all inputs covered" prediction scores TRUE — first-pass green,
## and with NO `maxHeartbeats` where the metricwise sibling needs 1600000
## (2026-08-07)

No stop condition fired.  No input turned out to be uncovered; no private
monolith dependency needed a public re-derivation beyond three-line jet algebra.

**(0) PREDICTION SCORE: TRUE.**  209 predicted node 3 would be mechanical with
all inputs covered.  It was: the file compiled GREEN on the first focused check
(25.9 s), before any repair, and the only edits afterwards were two linter
fixes.  Two refinements to 209's forecast, both in the EASIER direction:

* 209 predicted a "one-line `SmoothCcTensor.ext`" for the identification
  `pureTrace g g p = cometricDoubleTraceField g p`.  It is a bare **`rfl`**.
  `pureDoubleTraceField g₀ g₁ p` (`…JetTower/PairTrace.lean:1317`) and
  `cometricDoubleTraceField g₀ p` (`CovGrad/CometricDoubleTraceField.lean:729`)
  are declared with literally the same three fields once `g₁ := g₀`; structure
  eta + proof irrelevance close it definitionally.
* The metricwise `pairTrace_h2_lip` carries `set_option maxHeartbeats 1600000`.
  The class-uniform version needs **none** — splitting the six reusable steps
  out as private lemmas (`ptSelf`, `ptDiag`, `jetAdd`, `jetAbs`, `pairSplit`,
  `zeroTie`/`zeroHs`) keeps every declaration inside the default budget.  This
  is the 211/212 split idiom paying off a second time; it should now be treated
  as the DEFAULT for this lane, not a fallback.

Also confirmed from the dispatch's verify-list: `appRS_h22_unif … 6 4 2` is the
right instantiation (`Φ : SmoothCcTensor g 4 2`, `W : SmoothCcTensor g 6 4`,
output `appCcRS g 6 4 2 Φ W : SmoothCcTensor g 6 2`), and
`LowBaseInternal.pairTrace_eq` (`…LowBaseAction.lean:9000`) is **public**, so
the pair factorization was reused, not re-derived — the №194 monolith rule never
had to bite.

**(1) LANDED — `pairTrace_h2_lip_unif`** (`ShortTime/UnifTraceLip.lean`,
493 → 784 lines; the file now hosts nodes 2 AND 3).  Class-uniform under
EXACTLY the ruled pair (`MetricUniformEquivalentOn univ gBase g Λ` +
`∀ a ≤ 3, MetricCovDerivOrderBoundOn univ a g gBase Λ`), same `∃ ρ C` prefix as
nodes 1 and 2, `c2JetSq` spelled out as `∑ j ∈ Finset.range 3, ‖…‖ ^ 2` at
valence `(6, 2)`.  **Sorry-free**; axiom probe
`[propext, Classical.choice, Quot.sound]`.

Home justification: `UnifTraceLip.lean` already owns `dtJet`, the diagonal
window producer node 3 consumes, and node 3's only other input is node 2 in the
same file.  A sibling file would have had to re-export `dtJet` or duplicate it.
784 lines is well inside the 3000 cap.

**Name length.**  `pairTrace_h2_lip_unif` is 21 characters (17 letters), one
over the project's 20-character habit — `invCoeff_h2_lip_unif` is exactly 20,
`trace24_h2_lip_unif` is 19.  Kept because the dispatch named it explicitly and
it is the compatibility-visible sibling of `pairTrace_h2_lip`.  If the planner
prefers strict compliance the one-grep rename is `pairTr_h2_lip_unif` (18);
there are as yet **zero consumers**, so the rename is free.

**(2) Translation table** (every input had a class-first sibling already):

| metricwise input | class-first sibling |
| --- | --- |
| `trace24_h2_lip` | `trace24_h2_lip_unif` (node 2, same file) |
| `appRS_h2_h2_h2 g 6 4 2` | `appRS_h22_unif … 6 4 2` |
| `J₂ = c2JetSq g (pureTrace g g 2)` | `ptDiag … 2` = `ptSelf` + `dtJet` + `volumeReal_cross` |
| `J₄ = c2JetSq g (pureTrace g g 4)` | `ptDiag … 4`, same |
| `LowBaseInternal.pairTrace_eq` | reused verbatim (public) |
| `jet3_add_c2` / `jet3_nonneg_c2` (private) | `jetAdd` (here) / inline |

**Closed constant.**  `n = Module.finrank ℝ E`,
`vol = volCompareC Λ · vol_{gBase}(M)`; `ρ`, `Ct` from `trace24_h2_lip_unif`,
`Ca` from `appRS_h22_unif … 6 4 2`:

    A₂ = n^8 · vol,             A₄ = n^10 · vol
    B₂ = √(2·((Ct·ρ)² + A₂)),   B₄ = √(2·((Ct·ρ)² + A₄))
    K₁ = Ca · Ct · B₄,          K₂ = Ca · B₂ · Ct
    C  = 2 · (K₁ + K₂)

`A₂`/`A₄` are the squared windows (node 2 kept them under a `√`), since they are
only consumed as `J ≤ A`; that drops two `Real.sq_sqrt` round trips.  Dimension
symbolic throughout, per node 2's recorded lesson.

**(3) Two findings worth propagating.**

* **The focused check is NOT warning-complete.**  `lake env lean` reported the
  file clean, and the targeted BUILD then flagged `show` used for a
  definitional (zeta) goal change at the endgame.  Fixed by naming the step
  (`have hend : … ; exact hfin.trans hend`).  Add to the standing habits: for a
  new file, read the targeted-build warnings too, not only the focused check.
* **`jetAdd` is now a THIRD copy** of the same three-line subadditivity fact —
  `jet3_add_c2` (private, `…C2Lip.lean:1037`), `jetAdd` (private,
  `UnifInvCoeffLip.lean:304`), and here.  A PUBLIC `lowJetSq`-form version
  exists (`DeTurckRemainderLowBaseH2VB.lean:85`) and was deliberately NOT
  reused: `H2VB` imports the 10.8k `DeTurckRemainderLowBaseLip` monolith, and
  the `Unif…` layer deliberately stops its import closure at `…C2Lip`.
  **Proposed as a dedup chip** (planner to queue, alongside the `bgKappa` and
  `path_add_sub_cap` chips): promote one range-three copy into a light shared
  module under `ShortTime/`.  Not a route error, not an exhibit.

**Verification.**  Focused check GREEN (25.7 s, no warnings).  Targeted module
build GREEN (`Built …ShortTime.UnifTraceLip (23s)`, 9930 jobs with the probe).
Axiom probe through a temporary scratch module, deleted afterwards; zero
`sorryAx` in the whole build output.  Files touched: `UnifTraceLip.lean`
(extended), `UnifTraceLip.md` (node-3 section + "next node" rewritten), this
ledger.  All unrelated dirty files preserved; no commits.

**Next node up the lane: `pairTrace_h2_bdd`** (private, `…C2Lip.lean:1794`) —
the absolute-size sibling, first consumer of `pairTrace_h2_lip` at `:1808`.
The three consumers of `pairTrace_h2_lip` are `pairTrace_h2_bdd` (`:1794`),
`curvMono_h2_lip` (`:1880`, which needs both), and the public `lowJetSq`-form
export wrapper `LowBaseInternal.pairTrace_pair_h2` (`:4655`).  Inputs of
`pairTrace_h2_bdd_unif` are fully covered and the class-first route is SHORTER
than the metricwise one: instead of reading the Lipschitz theorem at `(T, 0)`
against a diagonal window, `LowBaseInternal.pairTrace_eq` gives
`lieCovPair g gm = appCcRS g 6 4 2 (pureTrace g gm 2) (pureTrace g gm 4)`, and
node 3's in-proof `hmov` step already bounds BOTH factors absolutely by `B₂`
and `B₄`, so one `appRS_h22_unif … 6 4 2` call yields `≤ (Ca·B₂·B₄)²` directly.
The only refactor is extracting `hmov` into a standalone private lemma.
Predicted mechanical again.  `curvMono_h2_lip` after it is NOT — it adds the
curvature-refold monomial machinery and carries `maxHeartbeats 1800000`.

**Honest denominators.**  `ricci_flow_unif_existence` **0%** — still unstated in
Lean; nothing here touches its sorry.  G3 class-uniform lane: **3 of ~56 nodes
≈ 5%**.  Per-`(g, gB)` `IsBgLiftAt`: **100%** (`bgLift_of_radial`, unchanged).
Class-uniform lift: **0%** — it needs the whole lane, and 3 nodes do not
produce any endpoint.  Dedicated uniform-existence machinery ≈**85%**
(unchanged: this brick consumed only pre-existing producers; its new reusable
assets are `ptDiag`/`jetAbs`/`pairSplit`, which are lane-internal).  Whole HCG
≈**3%**.

---

## 215 (planner, 05:50). 214 accepted; lane-grind mode; node 4 dispatched

214 accepted: prediction-scoring worked (TRUE, first-check green); the
21-char name tolerated as dispatch-caused (free rename `pairTr_h2_lip_unif`
banked for a cleanup pass); `jetAdd` third copy = dedup chip #3 (with the
H2VB import-closure justification — correctly NOT a route error); the
"focused check is not warning-complete, read BUILD warnings for new files"
finding adopted as lane discipline.  Node 4 (`pairTrace_h2_bdd` class-first,
via `pairTrace_eq` + the extracted `hmov` — predicted mechanical AND shorter
than metricwise) dispatched, reports as 216.  Node 5 (`curvMono_h2_lip`) is
pre-flagged NOT mechanical (curvature-refold monomials) — when the lane
reaches it, a read-only scout goes first; that is likely where the morning
session picks up.

---

## 216. G3 lane node 4: `pairTr_h2_bdd_unif` LANDED sorry-free.  Entry 214's
## prediction scores TRUE on BOTH halves — mechanical, and the class-first route
## really is shorter than the metricwise one: the diagonal window and the
## `(T, 0)` reading both disappear (2026-08-07)

No stop condition fired.  No input turned out to be uncovered.  The `hmov`
extraction did NOT disturb node 3: its docstring and signature
(`UnifTraceLip.lean:688–721`) are byte-identical to the pre-edit text, and its
axiom probe was re-run to confirm it.

**(0) PREDICTION SCORE: TRUE, both halves.**

* *Mechanical.*  Green on the FIRST focused check (24.9 s), before any repair —
  no failed route, no second attempt, no linter fix.  This is the second
  consecutive node where the 211/212 split idiom (private lemmas instead of a
  raised heartbeat budget) kept every declaration inside the default budget:
  the metricwise `pairTrace_h2_bdd` carries `maxHeartbeats 1200000`, the
  class-uniform one carries **none**.  Three nodes in a row now (2, 3, 4) at
  default budget against metricwise siblings at 1.6M / 1.2M.  Treat the split
  idiom as settled lane default.
* *Shorter than metricwise.*  Confirmed against the Lean text, and it is a
  bigger saving than 214 estimated.  The metricwise proof reads its own
  Lipschitz theorem at `(T, 0)` and then adds back the diagonal window
  `J = c2JetSq g (lieCovPair g g)` through `jet3_add_c2`.  The class-first proof
  needs NEITHER: `LowBaseInternal.pairTrace_eq` factors
  `lieCovPair g gT = appCcRS g 6 4 2 (pureTrace g gT 2) (pureTrace g gT 4)`,
  the extracted `movWin` bounds both factors absolutely, and one
  `appRS_h22_unif … 6 4 2` multiplies them.  So the diagonal `lieCovPair g g`
  window never has to be produced at the pair valence at all — the only place
  a diagonal appears is inside `movWin`, at the two TRACE valences, where
  `ptDiag` already gives it as a pure dimension/volume constant.

**(1) LANDED — `pairTr_h2_bdd_unif`** (`ShortTime/UnifTraceLip.lean`,
784 → 913 lines; the file now hosts nodes 2, 3 AND 4).  Same `∃ ρ B` prefix
shape as the metricwise sibling, class hypotheses EXACTLY the ruled pair
(`MetricUniformEquivalentOn univ gBase g Λ` + `∀ a ≤ 3,
MetricCovDerivOrderBoundOn univ a g gBase Λ`).  Conclusion is the ABSOLUTE
`∑_{j<3} ‖∇ʲ (lieCovPair g gT)‖² ≤ B²` at valence `(6, 2)` — no `‖T‖` factor,
mirroring `pairTrace_h2_bdd` (checked at `:1805`, whose conclusion is
`c2JetSq g (lieCovPair g gT) ≤ B ^ 2`).  **Sorry-free**; axiom probe
`[propext, Classical.choice, Quot.sound]`.

**Name length:** `pairTr_h2_bdd_unif` = **18 characters**, inside the 20-char
budget — the dispatch's suggested name, adopted.  215's flag on node 3's
21-char name is not repeated here.

**(2) The one refactor, exactly as 214 specified.**  Node 3's in-proof `hmov`
became the private lemma `movWin` (`UnifTraceLip.lean`, inserted after `zeroHs`,
before node 3).  It takes `gBase g gm`, `hEq`, `hρ`, `hCt`, the node-2
conclusion ALREADY specialized at this `g` (i.e. `htrace g hEq hjet`), and
`(P, htie, hP)`; it returns the two absolute trace windows with the volume
constants written out explicitly.  Everything the old `hmov` inlined moved
inside it — `hzρ`, `hdiag₂`, `hdiag₄`, `hmul`, `hcut` — so node 3's proof body
shrank by ~28 lines and `hmov` is now four lines (`rw [hB₂sq, hB₄sq]`,
`dsimp only [A₂, A₄, vol]`, one `movWin` call).  Node 4 calls `movWin` once.

**Closed constant.**  `n = Module.finrank ℝ E`,
`vol = volCompareC Λ · vol_{gBase}(M)`; `ρ`, `Ct` from `trace24_h2_lip_unif`,
`Ca` from `appRS_h22_unif … 6 4 2`:

    A₂ = n^8 · vol,             A₄ = n^10 · vol
    B₂ = √(2·((Ct·ρ)² + A₂)),   B₄ = √(2·((Ct·ρ)² + A₄))
    B  = Ca · B₂ · B₄

`ρ` is node 2's radius unchanged, and `B₂`/`B₄` are literally node 3's — after
the `movWin` extraction the two nodes share one constant recipe rather than
two parallel copies.  Dimension symbolic throughout.

**(3) Findings worth propagating.**

* **214's "read the BUILD warnings" discipline has a trap: a bare `touch` does
  not trigger re-elaboration.**  Lake keys on a content hash, not mtime, so
  `touch file && lake build +Module` reports success WITHOUT rebuilding and
  therefore without re-emitting that module's warnings — a silent false clean.
  The reliable force is to delete the module's `.trace` and `.olean.hash` under
  `.lake/build/lib/lean/…`; the rebuild then prints `Built … (22s)` and its
  diagnostics again.  Verified that way here: **zero** warning lines mention
  `UnifTraceLip.lean` in the full log.  Add to the standing habits next to the
  214 finding, otherwise that finding is unenforceable.
* **The `let`-bound-constant idiom needs `rw` + `dsimp only`, never `show`.**
  `movWin` states its RHS with the volume expression written out, while the
  callers keep `A₂`/`A₄`/`vol`/`B` as `let`s; the bridge is
  `rw [hB₂sq]; dsimp only [A₂, vol]; exact …`, and `dsimp only [B]` before the
  final `happ`.  Using `show` for the same step is what the build linter flagged
  in node 3.
* No new dedup chip.  Node 4 added no fourth copy of anything; `jetAdd`/`jetAbs`
  are consumed through `movWin`.  The three chips already queued (`bgKappa`,
  `path_add_sub_cap`, range-three `jetAdd`) are unchanged.

**Verification.**  Focused check GREEN (24.9 s, first pass).  Targeted module
build GREEN (`Built …ShortTime.UnifTraceLip (22s)`, 9929 jobs), warnings read
for the touched file after a FORCED re-elaboration — none.  Axiom probes on both
the new theorem and node 3 (re-verified unchanged) through a temporary scratch
module, deleted afterwards along with its build artifacts; zero `sorryAx` in the
whole build output.  Files touched: `UnifTraceLip.lean` (extended + node 3's
proof body rewired), `UnifTraceLip.md` (node-3 helper list, new node-4 section,
"next node" rewritten), this ledger.  All unrelated dirty files preserved; no
commits.

**Next node up the lane: `curvMono_h2_lip`** (private, `…C2Lip.lean:1880`,
`maxHeartbeats 1800000`) — the second consumer of `pairTrace_h2_lip`, needing
BOTH the Lipschitz node and the bound node, which are now exactly nodes 3 and 4.
It stays **pre-flagged NOT mechanical** (curvature-refold monomial machinery,
no class-first sibling yet), and per 215 a READ-ONLY scout goes first; node 4
did not attempt it and found nothing that changes that assessment.  The third
and last consumer of `pairTrace_h2_lip` is the public `lowJetSq`-form export
wrapper `LowBaseInternal.pairTrace_pair_h2` (`:4655`).

**Honest denominators.**  `ricci_flow_unif_existence` **0%** — still unstated in
Lean; nothing here touches its sorry.  G3 class-uniform lane: **4 of ~56 nodes
≈ 7%**.  Per-`(g, gB)` `IsBgLiftAt`: **100%** (`bgLift_of_radial`, unchanged).
Class-uniform lift: **0%** — it needs the whole lane, and 4 nodes produce no
endpoint.  Dedicated uniform-existence machinery ≈**85%** (unchanged: this
brick consumed only pre-existing producers, and its one new reusable asset,
`movWin`, is lane-internal and private).  Whole HCG ≈**3%**.

---

## 217 (planner, 06:15). 216 accepted; the build-trace finding adopted;
## node-5 scout dispatched

216 accepted (two-half prediction TRUE; node-3 signature byte-identical
after the `movWin` extraction; third consecutive node at default
heartbeat).  **Ops finding adopted into lane discipline**: `touch` does
NOT invalidate lake's content-hash trace — "read the build warnings"
requires deleting the module's `.trace`/`.olean.hash` to force
re-elaboration (216's forcing recipe; record in the next `AGENTS.md`
sync).  Node-5 scout dispatched (read-only): `curvMono_h2_lip`
(`…C2Lip.lean:1880`, metricwise `maxHeartbeats 1800000`,
curvature-refold monomials) — inventory its proof inputs, classify each
against the existing `_unif` stock (nodes 3+4 are two of them),
name the gaps, and price the class-first route; NOT an implementation
task.  Its dossier is the expected morning pickup point.

---

## 218 (planner, ~06:50). Node-5 scout adopted: ROUTINE-WITH-SPLITS;
## exhibit 22 CONFIRMED; layer-placement ruling; node 5 dispatched;
## THE LANE BRANCH MAP recorded

**Exhibit 22 CONFIRMED** (the scout's candidate): the "node 5 NOT
mechanical — curvature-refold monomials" pre-flag (from 209, carried by
215/217) was an over-count of HARDNESS: `curvMono_h2_lip` contains zero
curvature analysis — its first step is the PUBLIC `curvMono_eq`
(`LowBaseAction.lean:8985`) rewriting to the same two-factor `appCcRS`
shape node 4 dispatched.  Nothing was built wrong; counter unchanged
2/3.  Also a false wall dodged inside the plan: `rsperm_sub_c2` has the
public twin `rsDomDomCongrSection_sub_cc` (`PairTrace.lean:1671`, in
direct import) — 57 lines saved.

**Placement ruling**: the Λ-free slot/permutation jet layer (~190
lines, needed by node 5 AND lane γ's `dagTop_*`) goes into a NEW
rank/order-GENERIC low leaf under `Analysis/Spectral/Tensor/CovGrad/`
beside `OperatorFieldFibreNormJet.lean` (canonical home; stops a fourth
private copy; the scout confirms genericity costs nothing — all proofs
per-`j`).  `UnifTraceLip.lean` hosts only the class-facing node.

**THE LANE BRANCH MAP** (scout §4, recorded for future sessions): node
5 is the UNIQUE bottleneck to the lane endpoint `a2_pair_lip` (:4593),
but ELEVEN other nodes are independently dispatchable TODAY on nodes
1–4 alone: lane β (`fullSlot_h2_bdd :2376` → `daWeight_pair_lip
:2476`), lane γ (7 nodes: `fullInsert2_pair/bdd`, `connLow_pair/bdd`,
`dagTop_pair/bdd`, + 2 exports), lane δ (10 terminal export wrappers),
lane ε (`invGeomOp_lip :3608`, `principalGeom_lip :3669`,
`phiMet_pair_lip :3949`).  Post-node-5 unlocks: `curv_pair_h2` (~72-line
diagonal specialization) and `lieRefold_pair_lip`, then the chain
daTrans → ricciRad → kernel → c2Diff → c2_pair_lip → a2_pair_lip.

**Node 5 dispatched** (reports as 219) per the scout's brick spec:
generic CovGrad leaf (slot/perm jet layer) → `monoSplit`/`twoArm`
splits → `curvMono_h2_lip_unif` (19 chars) with `ρ := min ρ₁ ρ₂`,
`K₁ := 9·Ca·Cp`, `K₂ := 9·Ca·Bp`, `C := 2(K₁+K₂)`; default heartbeat
target, soft-risk fallback 400000 documented (NOT the metricwise 1.8M).

---

## 219. Node 5: stopped by user pause after all three parts had already landed sorry-free (new leaf `Analysis/Spectral/Tensor/CovGrad/SlotPermJet.lean`; `monoSplit`+`twoArm`; `curvMono_h2_lip_unif`; plus the unlock `curv_pair_h2_unif`) — both files green at DEFAULT heartbeats with no `set_option` added; the full entry 219 was not written, per the pause order (2026-08-07)

---

## 220 (planner, 2026-08-07 morning). USER RULINGS: pause reviewed; the
## STALE-DENOMINATOR correction; G3 COMPRESSED to one master packet

**The user's morning interventions, recorded verbatim in effect:**
1. **PAUSE + "路线太离谱"** — the G3 lane's 56-public-node framing was
   called out.  Pipeline stopped cleanly (node 5's in-flight work had
   already landed green; entry 219).
2. **THE STALE-DENOMINATOR CORRECTION (major):**
   `ricci_flow_unif_existence` **HAS A PROOF**
   (`Evolution/ExtendViaUniqueness.lean:83–112`, consuming
   `lowreg_dt_unif` + `ricci_gauge_of_dt`) — the planner's all-session
   "(N) 0%" refrain was STALE inherited data, never re-verified against
   the Codex-era assembly (entries 167–193).  The ShortTime tree holds
   exactly TWO real sorries: `bg_packet_of_solve`
   (`LowRegBgBootstrap.lean:225` — "the remaining analytic frontier",
   PER-(g,g_bg), taking the same `IsLowBoundsAt` certificate that
   `bgLift_of_radial` takes) and
   `WeylEigenvalueCountingBound.lean:115`.  STANDING RULE (new): step
   zero of every session = re-grep the endpoint's sorry before
   repeating any inherited denominator.  An audit is in flight ((N)'s
   axiom chain; the bootstrap's intended route; whether it consumes
   `bgLift_of_radial`; where class-uniformity actually enters).
3. **G3 COMPRESSION RULING**: continue G3's MATHEMATICS, but abandon
   the 56-public-node mirroring.  Target = ONE public **master uniform
   coefficient packet** (a `bgLift_unif`-shaped endpoint: ∃ class
   formulas `ρ₀ Z L C`, ∀ (g,gB) in the class, the `IsBgLiftAt`
   producer fires at ONE `D : BgLiftData K` built from them), with all
   intermediate class-uniform steps as PRIVATE helpers, and ONLY the
   helpers actually on the constant-consumption path (planner
   suspicion, to be verified by the design scout: the metricwise LIP
   tower may feed only per-metric continuity/core facts — in which
   case the five landed public nodes were on a branch the packet does
   not even need; they stay as banked, harmless public API either
   way).  Sequence: (i) the running audit returns (its consumption map
   pins the packet's exact statement); (ii) a design scout traces
   EXACTLY which scalar constants reach `BgLiftData`'s fields and the
   minimal private-helper set; (iii) one master brick (or two if the
   A1/A2 halves split naturally).

---

## 221 (planner, 2026-08-07 morning). THE (N) AUDIT ADOPTED: one sorry
## (`bg_packet_of_solve`), Weyl off-path; G3 CONFIRMED NEEDED (planner
## suspicion wrong); the seven-step road to (N); denominators corrected

**Audit verdicts adopted in full** (probe lines verbatim in the audit
report; scratch module deleted, tree restored):
- `#print axioms`: (N) reaches `sorryAx` through EXACTLY
  `{bg_packet_of_solve}` (`LowRegBgBootstrap.lean:215`, sorry :225);
  chain: (N) → `lowreg_dt_unif` :248 → `lowreg_dt_of_solve` :229 →
  the sorry; every sibling clean (`ricci_gauge_of_dt`,
  `lowreg_bounds_unif`, `lowreg_solve_unif`, `dt_of_bg_packet`,
  `lowreg_apply_two`, `lowreg_solve_open`, `lowreg_allOrderJet`).
  **Weyl (:115) is OFF (N)'s chain.**  One stale-olean caveat
  (`lowSolve_cross` newer than its olean — rebuild item, not defect).
- **The sorry's statement is known-unprovable as posed**
  (`LowRegBgBootstrap.md` records it): it demands the packet on any
  `T ≤ 1`; the lift delivers only on `T ≤ lowregLiftHorizon' c Z`;
  `lowreg_dt_unif` currently DISCARDS its `IsLowBoundCap` certificate.
  Recorded corrected route = lift-data hypothesis + class-first common
  horizon (`BgLiftData.commonHorizon`, projections already proved).
- **G3 IS NEEDED FOR (N)** — №220's off-path suspicion REFUTED: order
  one is class-uniform via envelope+monotonicity
  (`IsLowBoundCap`/`horizon_le_of_cap`, sorry-free); the lift has NO
  such envelope (`bgLift_of_radial` binds ρ0/C/Z/L per-(g,gB)); (N)'s
  τ₀ is fixed BEFORE `g` ⟹ `D.horizon` needs a class-uniform lower
  bound ⟹ class-uniform C/Z/L/ρ₀.  The №220 compression ruling stands
  as that envelope's ARCHITECTURE.  One unrecorded escape hatch noted,
  not live without a user ruling: a direct-smoothing order-two route
  would dissolve G3 but abandon the `IsRealizedTwo` machinery.
- **The overnight work is ON-PATH**: `bgLift_of_radial`
  (+ refold layer + `c2Bg_h2_small` + `bgA2_of_radial`) is the
  intended coefficient-certificate input — the Bg mirror of
  `lowreg_solve_open`'s pre-trajectory assembly; all probe sorry-free.
  Caveat: zero production consumers yet (the steps below create them).
- **THE SEVEN-STEP ROAD** (1–5 = ports of GREEN diagonal machinery;
  6 = bookkeeping; 7 = G3-compressed): (1) `IsRealizedTwoBg` (widen
  `IsRealizedTwo` `LowRegApplyTwo.lean:111`; sole diagonal term
  `liftForceHi g g T` :154); (2) `bgreg_apply_two` (mirror :256,
  consuming `IsBgLiftAt`'s 14 fields +
  `hTle : T ≤ lowregLiftHorizon' D.contract D.zero` + `force_margin`
  via `IsLowSolveBg.force_le_cap`); (3) `bgreg_solve_open` (mirror
  :617 — assemble `bgLift_of_radial` into `D`); (4)
  `IsAdaptedLowSolveBg` + `bgreg_adapt_open` (mirror
  `LowRegAdaptedSolve.lean:203`); (5) `bgreg_allOrderJet` (mirror
  `lowreg_allOrderJet` `LowRegAllOrderJet.lean:1433` — conclusion is
  field-for-field `BgSmoothPacket`); (6) restate `bg_packet_of_solve`
  with `D` + `hTlift`, re-thread `lowreg_dt_unif`'s
  `T := min (lowregHorizon U) (class lift horizon) 1`; (7) the master
  uniform coefficient packet (№220 architecture) making step 6's class
  lift horizon positive.
- **Denominators corrected (audit's stricter marks adopted)**: (N)
  **0%** (sorryAx ⟹ 0; the real gain is DIAGNOSIS — a single
  localized sorry with a written route); `bg_packet_of_solve`
  machinery ≈**60–65%** (the ledger's ≈85% had not priced steps 1–5);
  G3 ≈9% by the old node count (re-priced after the design scout);
  HCG ≈**3%**.

**Dispatched: the master-packet DESIGN SCOUT** (read-only, feeds 222):
the exact scalar-consumption map (which constants reach
`BgLiftData.zero/slope/contract/coeffRadius` hence `D.horizon`; which
chain produces each — Z/L from the refold-pack chain, C from
`c2Bg_h2_small`+`a2_pair`, ρ₀ from the radius chain), whether the five
landed LIP nodes feed ANY of them, the envelope shape mirroring
`IsLowBoundCap`/`horizon_le_of_cap`, and the minimal private-helper
set behind ONE public endpoint.

---

## 222 (planner, 2026-08-07). MASTER-PACKET DESIGN ADOPTED: no envelope
## trio needed (`IsLowBoundsUnif` is already a literal class packet);
## seven gap clusters, four bricks; road to (N) priced 18–28 sessions

**Design scout adopted in full** (details in its report; the ledger
records the decisions):
- **Consumption map**: `Z`/`L` are radius-functions from the three
  affine packs (`c0_core_affine`/`c1_core_affine`/`c0bg_aff` — all
  expose `Z̄(r)/L̄(r)` BEFORE `ρ,δ,hreal`, which the construction
  needs); `C` from `lowA2Bg_small` ← `a2_pair` + `c2Bg_h2_small`;
  `ρ0` from the four pair radii, bottoming at `inv_coeff_h2` whose
  `_unif` sibling exists.  **The five LIP-lane nodes feed ρ₀ ONLY**
  (constants discarded at `LowRegBgLift.lean:357` and in the packs'
  `exists_extend_le` calls; `pairTr_h2_bdd` zero consumers) — №220's
  suspicion half right: banked inputs for G6/G7, not dead branches.
  (N)'s chain runs at `gB := gBase`, so `_unif` siblings are needed
  only at that instantiation — `rhs1_path_unif`/`phi_dev_h2_unif`
  already have that shape.
- **Gap clusters**: G1 `a1_diff_unif` (routine), **G2
  `c0Coeff_aff_unif` (NON-ROUTINE — `LowRegBgC0Zero/One.lean` ≈2.5k
  lines each, zero `_unif` beachhead; pre-scout mandated)**, G3
  `c0Bg_diff_tame_unif` (medium), G4 `appD2Hs_norm_unif` (routine),
  **G5 `c2_h2_small_unif` (NON-ROUTINE — three private leaves in the
  13.8k Action monolith; №194 discipline applies)**, G6/G7 pair radii
  (routine-medium; consume the five banked LIP nodes).  Radius-shape
  rule: always `∃ ρ̄ > 0, ∀ g ∈ class, ∀ ρ ≤ ρ̄, P_g(ρ)` — never a
  bound against a per-g existential.
- **ARCHITECTURE (the compression lands even simpler than №220
  hoped)**: NO `BgLiftEnvelope`/`IsBgLiftCap`/`liftHorizon_le_of_cap`
  — `exists_lowBounds` already yields a LITERAL class `K`
  (`IsLowBoundsUnif`), so ONE `D : BgLiftData K` serves the class and
  `D.horizon` IS the class lift horizon.  The cap route provably
  cannot carry the lift (`IsLowBoundCap` bounds `outer`/`realize`
  from BELOW; `lowregStateRad_mono` runs the wrong way) — do NOT add
  a `stateCap` field to the settled structure.  Public endpoint =
  ONE theorem `bgLift_unif`
  (`∃ K hKu D, ∀ g (class hyps), ∃ F, IsBgLiftAt g gBase K … D F`).
  Constructive order verified non-circular; `force_margin` is
  discharged by shrinking `K.outer` (an independent knob via
  `lowBounds_small` reparameterization) — NEVER by shrinking the
  coefficient radius (`L̄(r)·r → 0` is NOT available; design risk
  checked and cleared).  Seam into step 6: swap `lowreg_dt_unif`
  from `unif_solve_of_caps` to `unif_solve_of_bounds` and set
  `T := min (D.commonHorizon K) 1` (`commonHorizon_pos` already
  proved).
- **File plan**: gaps in per-home `Unif*.lean` siblings; master file
  `ShortTime/UnifBgLiftPacket.lean` (~250–350 lines; private
  `bgLiftConst_unif` + `lowBounds_small` + arithmetic; public
  `bgLift_unif` only).  **Four bricks**: α = G1+G2+G3 (5–8 sessions,
  G2 dominates), β = G4+G5 (3–4), γ = G6+G7 (1–2), δ = the master
  file (1, after α–γ).  Packet ≈10–15 sessions; **full road to (N)
  ≈18–28** (with №221's steps 1–6 priced 7.5–13).
- **Minor check banked for δ**: `IsBgLiftAt` cores mention
  `D.realize hK` — replacing `hK` by `hKu.bounds g …` rides on
  Prop-irrelevance; `#check` at δ.

**Dispatch** (lowest-risk first): brick γ executor (G6+G7 — routine,
consumes the banked LIP nodes, closes the ρ₀ scalar) ∥ G2 PRE-SCOUT
(read-only — the biggest risk item; its dossier prices brick α before
any Lean).  β and the №221 ports (steps 1–5, independent of the
packet until step 6) queue behind, order per user preference.

---

## 223. Brick γ (G6+G7): STOPPED BEFORE THE FIRST LEAN EDIT.  The
## mathematics is CONFIRMED and trivial — the class floor is
## `min (K.realize) (min 1 (4·Cop)⁻¹)`, and NO Lipschitz constant enters
## any radius — but the chain is 109 nodes with only 6 banked, and the
## entire ready frontier is inside a read-only monolith (2026-08-07)

**LEAD: nothing landed; no Lean file created; no `sorry` added.**  Brick
γ cannot take one step under the never-edit rule.  Full note:
`ShortTime/UnifPairRadii.md`.  `#222`'s 1–2-session price is wrong by an
order of magnitude, and the error is diagnosable: the brick was scoped as
"replace each metric-dependent link with its `_unif` sibling", but only
**6 of 109** links have one.

**The good news first — the design scout's mathematics is vindicated,
and more strongly than it was claimed.**  A full mechanical trace of the
radius provenance of all seven roots (`c0CorePair`, `c1_core_pair`,
`c1_ext_pair`, `c0bg_pair`, `c0Coeff_aff`, `a2_pair_lip`,
`radialA2Bg_lip`), following every `obtain ⟨ρ…⟩` edge transitively:

- **109 nodes, exactly TWO genuine radius sources.**  `inv_coeff_h2`
  (`PrincipalCoeffH2.lean:202`, `let ρ := min 1 (4 * Cop)⁻¹`, banked as
  `inv_coeff_h2_unif` `UnifInvCoeffH2.lean:60`) and `sharp_pair_h2`
  (`DeTurckRemainderLowBaseC1Lip.lean:3972`, `let ρ := 1`, **absolute**).
  Plus the passed-in `ρ₀` at `radialA2Bg_lip`, which `bgA2_of_radial`
  instantiates at `K.realize` — class data.
- **105 of 109** nodes' radius witness is a pure `min` of children's
  radii.  №198's "fully explicit everywhere, no `Classical.choose`" is
  confirmed at every node.
- ⟹ the honest class-uniform floor for all four pair chains at once is
  **`ρ̄ = min (K.realize) (min 1 (4·Cop(gBase,Λ))⁻¹)`**.
- ⟹ **the brick's contingency never fires**: not one node has a
  `1/(4C)`-shaped radius with a per-g `C`.  The single `1/(4C)` in the
  chain is `inv_coeff_h2`'s, whose `C` is `Cop` = class data.  **G6/G7
  need nothing from bricks α/β**, and "radius only, constants stay
  existential per-g" is exactly right.

**The blocker is Lean expressibility, not mathematics.**  Every node
reads `∃ ρ C, 0 < ρ ∧ 0 ≤ C ∧ ∀ …, ‖T‖ ≤ ρ → P(T,U,C)`.  `P` is
downward-closed in `ρ`, but the existential hides the witness, so
`P(ρ̄)` for a pre-chosen `ρ̄` is underivable.  Each node must be
**restated** with the radius quantified before `g` and re-proved (the
body is otherwise unchanged — constants are obtained after
`intro g hclass`).  That is **103 restatements**.  Escapes checked and
closed: no node states a lower bound on its own radius
(`radialA2Bg_lip`'s fourth component is `hρ_le : ρ ≤ ρ₀`, an **upper**
bound); no compactness gives `inf_g ρ_g > 0`; no formal transfer from
`gBase`, since the statements quantify over `SmoothCcTensor g 0 2`.

**THE HARD STOP — the ready frontier is 100 % read-only.**  Bottom-up,
the nodes whose radius children are all banked are exactly ten, and
**every one is inside `DeTurckRemainderLowBaseC2Lip.lean`**:
`fullInsert2_pair` :2858, `fullSlot_h2_bdd` :2376, `lieRefold_pair_lip`
:2150, `pairTrace_bdd_h2` :4685, `pairTrace_pair_h2` :4655,
`phiMet_pair_lip` :3949, `trace1_h2_lip` :4706, `trace2_pair_h2` :5208,
`trace3_h2_lip` :4972, `trace4_pair_h2` :5326.  **No editable-file node
has all children banked.**  Privacy is secondary and survivable — 15 of
G7's 17 monolith nodes are `private` and name `c2Kernel` :4068 /
`c2JetSq` :229 / `fullSlot2` :62, but `curvMono_h2_lip_unif`
(`UnifTraceLip.lean:996`) shows the pattern of unfolding a private def
(`c2JetSq` → `∑ j ∈ Finset.range 3, ‖iteratedCovGrad … j X‖ ^ 2`)
inline; `c2Kernel`/`fullSlot2` are structural and unfold badly.

**Counts.**  G6 94 nodes / 89 to-do (34 read-only, 55 editable);
G7 24 / 18 to-do (17 read-only, all in `C2Lip`, spanning :2150–:4593).
Union to-do 103; 47 read-only, 37 `private`.

**RULING NEEDED (three options, in the note's §4).**  (a) *Preferred* —
lift the never-edit rule **additively** for this job: put each `_unif`
radius sibling inside the monolith right after its metricwise original,
the only place the private statements are expressible and the proof body
reusable rather than copied; purely additive, no existing declaration
changes.  (b) Replay into light `Unif*.lean` files — respects the rule
but copies ~2 400 lines of `C2Lip` internals plus `H2Pair`/`C1Lip`/`Lip`
slices; forbidden by №194 and "no large proof-body copies".  (c)
Dissolve the requirement via №221's unrecorded direct-smoothing
order-two escape hatch — it would retire all 103 nodes at once, and this
finding raises its value considerably.

**RE-PRICING.**  Brick γ under (a): **≈10–20 sessions** (G7 ≈3–5, G6
≈8–15) — comparable to α, not the smallest slice.  Master coefficient
packet: **≈25–40 sessions**, not №222's 10–15.  γ should no longer be
dispatched first: cheapest per node, largest by node count, and gated on
a ruling.  **What δ needs from γ is unchanged in shape** — one `ρ̄ > 0`
gating `D.coeffRadius` in `bgLift_of_radial` — but §2 now hands δ the
exact formula, so δ's arithmetic can be written against a known number;
only the Lean theorem asserting it is missing.

**DENOMINATORS (unchanged where not re-priced).**  (N) **0%** —
`sorryAx` still via `bg_packet_of_solve` (`LowRegBgBootstrap.lean:225`);
this session changed no Lean.  `bg_packet_of_solve` machinery ≈**60–65%**
(№221's mark held; not the older ≈85%).  Brick γ: Lean **0%**, its
scouting/design **done** (the floor formula is now known exactly and the
work list enumerated).  HCG ≈**3%**.

**STANDING LESSON (new).**  A `∃ ρ, P(ρ)` statement is a **one-way door**
for later uniformization — the witness is unrecoverable and
downward-closure buys nothing.  When a radius is expected to become
class-uniform, state it `∀ ρ, 0 < ρ → ρ ≤ ρ̄ → P(ρ)` from the start, or
export the witness as a `def`.  Corollary for planning: price a
"substitute the `_unif` siblings" brick by **grepping the siblings and
counting the links**, and measure the **ready frontier** (children all
banked) and its *editability* — not the leaf count.

---

## 224 (planner, 2026-08-07). γ's STOP accepted (major finding); the
## C2Lip memory-wall assumption REFUTED by direct probe; the radius-layer
## fork framed for the user

**γ accepted as a successful gate** (entry 223): the mathematics is
BETTER than designed — 109 radius nodes, exactly TWO genuine sources
(`inv_coeff_h2`, already banked `_unif`; `sharp_pair_h2` with absolute
ρ = 1), so both floors equal the KNOWN class formula
`ρ̄ = min (K.realize) (min 1 (4·Cop(gBase,Λ))⁻¹)`; 105/109 radii are
verbatim min-passthroughs; G6/G7 need NOTHING from bricks α/β.  The
block is purely architectural: the `∃ ρ` one-way door (standing lesson
adopted) — 103 nodes would need radius-before-`g` restatements, and
the ready frontier sits in files carried as read-only.

**Probe (this entry): `DeTurckRemainderLowBaseC2Lip.lean` re-elaborates
GREEN in 63.8 s under `-LeanThreads 4 -LeanMemoryMB 6144`.**  The
№194 memory wall belongs to `…LowBaseLip.lean` (10.8k) specifically;
C2Lip (5.5k) is NOT a wall.  Its read-only status was inherited claim
etiquette + over-generalization, now amended: **C2Lip = editable with
care** (additive edits only; probe green).  `C1Lip` (6.4k) likely
similar (probe before first edit); `Action` (13.8k), `Lip` (10.8k),
`H2Pair` (9.5k) remain read-only pending probes.

**THE FORK (user ruling requested; pricing per option):**
- **(a) additive in-monolith restatements** — for each needed node,
  add the radius-quantified-before-`g` variant right after the
  metricwise original, PROOF BODY REUSED in place.  Now viable for
  G7 (17 nodes, ALL in C2Lip — est. 2–4 sessions) and the C2Lip/C1Lip
  share of G6; only the true-wall files' nodes (Action/Lip/H2Pair
  share of the 47) fall back to light-file replay.  Revised γ ≈
  **4–8 sessions** (was 10–20 under (b)-only), packet ≈ **17–27**.
- **(b) light-file replay** of ~2 400 lines of monolith internals —
  №194-violating in spirit; only as the fallback for true-wall nodes.
- **(c) the direct-smoothing escape hatch** (№221): obtain the
  order-two packet by parabolic instantaneous smoothing of the
  order-one solve — retires ALL 103 radius nodes AND the α/β constant
  gaps AND №221's steps 1–5 (the adjacent-scale machinery), replacing
  them with one analytic development of UNKNOWN Lean cost; abandons
  `IsRealizedTwo`/all-order-jet.  γ's finding raises its value; a
  READ-ONLY feasibility scout is cheap and prejudges nothing.

**Planner recommendation**: commission the (c) feasibility scout now
(read-only), and — unless the user prefers to wait for it — run a
scoped (a)-trial on G7 (one file, all inputs banked, ~2 sessions) so
the comparison (a)-grind vs (c)-rewrite is made with real numbers on
both sides.  No further dispatch until the user rules.

---

## 225 (planner, 2026-08-07). THE (c) SCOUT RETURNED: (c) viable AND
## CHEAPER — the pivot is that BOTH routes must widen the Galerkin/rung
## ladder, because `IsAdaptedLowSolve` is diagonal-hardcoded; the fork
## re-framed; ONE decisive fact left (gate-constant provenance), probe
## dispatched read-only

**Scout verdict adopted, with the pivot INDEPENDENTLY RE-VERIFIED by
planner reads** (full dossier in the task output; anchors checked:
`IsLowSolveAt`'s `hcore`/`hcont`/`htame` name `coreN g₀ g₀` /
`lowregNfun g₀ g₀` verbatim — `UnifClassBounds.lean:493/:498/:501`;
`lowreg_allOrderJet` takes BOTH `hre : IsRealizedTwo` :1442 AND
`hlo : IsAdaptedLowSolve` :1448; `IsAdaptedLowSolve`
(`LowRegAdaptedSolve.lean:42`) = `IsLowSolveAt ∧ IsRung3Ord g₀ ∧
∃ A B, IsLowGateOrd g₀ A B ∧ Ctop₂·Kcap ≤ A ∧ Kr2+Kr1 ≤ B ∧
∃ ε > 0, A·(δ/(1−δ)²) + B·stateRad + ε < 1` — all at diagonal `g₀`).

**The pivot.**  №221 step 5 (`bgreg_allOrderJet`) consumes an
`IsAdaptedLowSolveBg` that does not exist; producing it means widening
the WHOLE rung/gate chain (`a1PerIdxLin`/`a2PerIdxLin` → `armLadder3`
→ rungs 3/4/5 → `IsHmRungOrd` → `IsLowGateOrd` → `IsLowSolveAt` →
`IsAdaptedLowSolve` → `lowregAllMassAt`/`lowreg_loMass`; ≈4.6k
ShortTime + ≈2.5k Analysis lines) from `g g` to `g g_bg`.  So the
recorded route ALREADY pays route (c)'s main bill — №221 steps 1–5
were under-priced by exactly this.  **Route (c) = the recorded route
MINUS the lift.**
- SHARED by both routes: (c-A) ladder widening, est. 8–18 sessions
  (mitigations: the analytic substrate is already two-metric —
  `lowBaseData (g g_bg)`, `lowRegSeedMass`, `lowregGalSol`,
  `lowregNfun`/`coreN` — the diagonal is an INSTANTIATION; and the
  ladder needs ABSOLUTE bounds at one background, not the Bg-Lipschitz
  bounds that made 205–212 expensive); (c-B) class-uniform absorption
  gate, est. 6–14 (measured good news: gate constants use only LOW
  indices — `Cqa 2`, `Cqa 2·Ka 2`, `Cqb 2·Kb1 1`
  (`LowRegRungThree.lean:645`), index-free κ from `lowData_split` —
  so it LOOKS like ≈8–12 `_unif` nodes at jet order ≤5, not G3's 103).
- (c)-ONLY delta: (c-C) order-2 synthesis + packet assembly, 3–6
  (`fHi : timeL2 H²` via `solFieldAtOrder`-style mass summation,
  carrier `maxRegDuhamelMap 2 … 0 fHi`, `bgreg_forceJetMass` glue).
- RECORDED-route-only extra: master packet 17–27 (№224) + steps 1–3
  lift ports + step 6 rethread.  Net saving of (c) ≈ that entire
  block; the 103 radius restatements, bricks α/β/γ/δ, and the
  read-only-monolith fork of №224 all become MOOT under (c).
  Totals: (c) ≈17–38 (of which 14–32 shared); recorded ≈25–40+.

**Supporting findings** (scout's, spot-anchored):
- t=0 corner FREE: the datum is the ZERO perturbation
  (`IsLowSolveBg.map_eq` uses `0`), manifold closed ⟹ no
  compatibility sequence; `trace_zero` via `maxRegDuhamelMap_trace0`
  (`…/TensorMaximalRegularity/SolutionSpace.lean:638`); matches
  `FORWARD_UNIQUE_PRO_RULING.md:120`.
- The naive mode-decay bootstrap is DEAD IN-TREE and documented:
  `ForcingTimeBootstrap.lean` records the +2-gain/+2-loss STALL, and
  the high-`a` lane's version rests on TWO open sorries — do not build
  on it.  The mechanism that works is the PROVED order-one rung
  ladder: `lowreg_loMass` = `lowregAllMassAt` gives every-σ t-uniform
  spectral mass on the CLOSED slab `Icc 0 T` with NO added horizon
  constraint — literally the ruling's "a-posteriori endpoint bootstrap
  on the fixed horizon".  `lowreg_allOrderJet` is a HYBRID: the lift
  supplies only TYPED scale-2 objects; the analytics is the ladder.
- The Pro ruling (`ExtendViaUniqueness.lean:73–76`,
  `FORWARD_UNIQUE_PRO_RULING.md:120–137`) already PRESCRIBES (c) and
  names re-run horizons as the wrong pattern; the lift's
  `T ≤ lowregLiftHorizon' c Z` is such a horizon, and G3 exists only
  to keep it class-positive.  The ruling's one optimistic spot is
  exactly (c-B).
- Consumer sweep: the lift layer has ZERO non-ShortTime consumers;
  `bgLift_of_radial` and `lowreg_solve_two` are already
  consumer-less.  Under (c): the 206–212 Bg-difference arc,
  `IsRealizedTwo`, `liftForceHi`, `lowregLiftHorizon'`, the five LIP
  nodes, and G3's restatements DIE; the order-one class layer,
  `lowA2Hi`/`lowA2Lo`, `lowSolve_cross`, `dt_of_bg_packet`, and the
  (widened) ladder SURVIVE.  `lowreg_dt_unif` is UNCHANGED under (c)
  (already order-one-only); the recorded route must re-thread it.
- Hybrid rejected: the lift's horizon constraint is intrinsic —
  keeping steps 1–5 cannot retire the packet.  The route-independent
  move is the reverse: (c-A)+(c-B) first, fork deferred.
- Scout caveat: one delegated genericity census had not returned; its
  genericity claims are from its own direct reads.

**ONE DECISIVE FACT LEFT — gate-constant provenance** ((c-B)'s real
size, and whether ANY route works): if every gate constant
(`Ctop₂ Kr2 Kr1 Kcap`, `IsLowGateOrd`'s `A B`, κ) is controlled by
order-≤5 jets + the fibre threshold + `Cop`, (c-B) collapses to
≈8–12 `_unif` nodes and (c) is decisively cheaper; if any needs
unbounded-order geometry, BOTH routes are blocked at the same place —
that would be the true (N) frontier.  Secondary question: whether
`lowreg_adapt_open` hides a T-shrink beyond the thresholds (the gate
inequality itself is horizon-free by the :52–53 shape).  **Probe
dispatched, READ-ONLY** — decision-support audit under the user's
"你可以审计一下" sanction, same category as the (c) scout.  №224's
"no further dispatch until the user rules" continues to bind ALL Lean
work — including the "shared" (c-A): it is 8–18 sessions, and route
(c) formally supersedes the №220/№222 packet ruling, so the user must
re-rule regardless.

**On the probe's return**: assemble the final decision package —
recorded route (≈25–40+, under-priced) vs (c) (≈17–38 incl. shared)
with the gate number filled in — and present for ruling.
Denominators unchanged: (N) **0%** (sorryAx via `bg_packet_of_solve`),
its machinery ≈60–65%, HCG ≈**3%**; this entry changed no Lean.

---

## 226 (planner, 2026-08-07). GATE PROBE ADOPTED: no unbounded-order
## obstruction anywhere — (c-B) collapses to ≈7 `_unif` node families,
## no hidden T-shrink; ONE NEW planner flag (the jet-order budget:
## (N) supplies `a ≤ 3`, the gate chain reads ~6–8) — shared by both
## routes, neutral for the fork; DECISION PACKAGE presented for ruling

**Probe verdict adopted** (full provenance table in the task output;
every gate constant traced to definition sites with line cites):
- **No constant needs unbounded-order geometry of `g`.**  Every leaf
  is a per-`g` `∃ C` (`Classical.choose` at `obtain` time) over
  FIXED-order data — the obstruction is missing statements, not
  missing mathematics.  Highlights: `Cqa` is pure dimension
  (`appCcGdiag j = (2(finrank+1))^j`, hidden behind an `∃`); κ bottoms
  out in `c2_cap`'s explicit `√(4KL²+4KP²+8KR²)` with order-0
  coefficient caps; the absorption thresholds are the explicit
  formulas `δ := 1/(16(A+1))`, `Rcap := 1/(8(B+1))`, `ε := 1/4`
  (`LowRegAdaptedSolve.lean:131/:132/:143` — confirmed);
  `lowregStateRad` is already an explicit class formula
  (`UnifClassBounds.lean:74`).
- **(c-B) = ≈7 `_unif` node families**: (1) supercritical embedding
  at ~6 fixed valences; (2) `moserWin_*` windows at orders ≤ 6;
  (3) jet towers (`low1Ker_jet`, `selfLow_jet_quad`, coefficient-field
  `lowJetSq` bounds, i ≤ 6); (4) order-0 caps (pattern PRECEDENTED:
  `UnifPhiDevH2`/`UnifPhiCurv`/`UnifRicci0` already do this on the
  solve lane); (5) **spectral bridges (`hs_le_jet`,
  `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs`) — the heaviest
  node**: uniform elliptic/Gårding comparison between `g`'s own
  spectral scale and covariant jets at orders ≤ ~6; (6) restate
  `Cqa`/`Cqb` with explicit dimension witnesses; (7) rung/gate
  assembly arithmetic.  Est. 6–14 sessions STANDS, with node 5 the
  risk carrier.
- **No hidden T-shrink** (secondary question resolved):
  `lowreg_adapt_open` pays the gate in STATE RADIUS (`Rcap` fed into
  the producer), not time; `IsAdaptedLowSolve` holds for every
  `T ≤ T₀`; `lowreg_allOrderJet` consumes the "full, unshrunk
  horizon".  On the class lane `lowreg_dt_unif` already fixes
  `T := min (lowregHorizon U…) 1` BEFORE `g` — class-uniform A/B is
  exactly what keeps the adapted lane on that same T.  The (c)
  architecture is self-consistent.
- Probe caveats on record: the ~8 jet ceiling is INFERRED (structure
  verified, leaf-by-leaf count not); rung-4/5 wrapper bridges and
  several `moserWin_*` leaf interiors NOT TRACED (statement shapes
  read, per-order witnesses not).

**NEW PLANNER FLAG — the jet-order budget** (neither scout named it;
planner-verified ground truth): (N)'s statement supplies EXACTLY
`∀ a ≤ 3, MetricCovDerivOrderBoundOn Set.univ a g₀ gBase Λ`
(`ExtendViaUniqueness.lean:89`; docstring self-describes "C³-bounded",
:64/:69) — while the DIAGONAL gate chain reads jets of `g` up to ~6–8.
Mitigations, in order of strength: (i) under the Bg-widening (BOTH
routes) the coefficient fields move to `g_bg = gBase`, whose jets are
FREE at every order — most of the ~8 dissolves; (ii) residual
`g`-dependence above order 3 sits in the spectral bridges + embedding
(families 1/5, and possibly tower slots of 3) — whether `a ≤ 3` +
uniform equivalence suffices there is an ELLIPTIC-COMPARISON question
settled during the (c-B) work itself; (iii) if it bites, the honest
fix is widening (N)'s class to `a ≤ K` for an explicit K ~ 6–9 — a
statement-level user decision (bounded-geometry classes with
finite-order K are standard), not a wall.  SHARED by both routes
(both consume the same gate) ⟹ neutral for the fork; recorded route
strictly worse off (it additionally uniformizes lift constants that
read diagonal-at-`g` fields).  Tracked as the TOP analytic risk of
the shared block.

**THE DECISION PACKAGE (final; presented to the user this entry):**
- Route (c): shared block (c-A ladder widening 8–18 + c-B gate
  ≈7 families 6–14) + (c-C) synthesis 3–6 ⟹ **≈17–38 sessions**.
  `lowreg_dt_unif` untouched; the lift layer retires (zero external
  consumers); prescribed by the project's own Pro ruling.
- Recorded route: the SAME shared block + master packet 17–27 +
  steps 1–3 lift ports + step 6 rethread ⟹ **≈25–40+**, dominated
  on every measured axis.
- Recommendation: **rule (c)**; execution starts with the shared
  block either way, and the lift layer is left IN PLACE (not
  deleted) until (c-C) lands — a natural rollback point.  Next brick
  after the ruling: (c-A) scope scout → first widening brick (the
  probe's family-4 caps or the `IsLowSolveAt`→`IsLowSolveBg`-consuming
  restatements are the natural beachheads).
- Denominator re-basing under (c), honest: the ≈60–65% machinery mark
  was priced against the RECORDED route; under (c) the credited lift
  block leaves the path and the (0%-started) ladder widening enters ⟹
  `bg_packet_of_solve` machinery re-bases to ≈**35–45%** (the proved
  diagonal ladder is the template; the two-metric analytic substrate
  exists; the widening itself is unstarted).  (N) **0%** unchanged;
  HCG ≈**3%** unchanged.  No Lean changed this entry; no dispatch —
  awaiting the user's ruling.

---

## 227 (planner, 2026-08-07). USER RULING: ROUTE (c) ADOPTED — direct
## smoothing; the №220/№222 packet architecture is SUPERSEDED; the
## no-dispatch freeze is lifted; (c-A) scope scout dispatched

**The ruling** (user's explicit choice from the №226 decision package,
recommended option): **裁 (c) — 直接平滑.**  Consequences adopted:
- The №220/№222 master-packet architecture and №221 steps 1–3 & 7
  (lift ports, `IsRealizedTwoBg`, `bgreg_apply_two`,
  `bgreg_solve_open`, the `bgLift_unif` packet) are SUPERSEDED.
  №221 steps 4–5 survive TRANSFORMED: `IsAdaptedLowSolveBg` +
  `bgreg_allOrderJet` are now reached through the shared widening,
  not on top of the lift.
- **Nothing is deleted now.**  The lift layer (`IsBgLiftAt`,
  `bgLift_of_radial`, the 206–212 Bg arc, the five LIP nodes, G3's
  banked `_unif` API) stays IN PLACE untouched until (c-C) lands —
  the agreed rollback point.  G6/G7 radius restatements, bricks
  α/β/γ/δ: cancelled (moot under (c)).
- Execution order: (c-A) ladder widening (diag → `(g, g_bg)`) →
  (c-B) gate `_unif` families (≈7, №226) → (c-C) order-2 synthesis +
  `bg_packet_of_solve` discharge.  `lowreg_dt_unif` stays untouched.
- Standing risk log: the jet-order budget (№226 flag) is settled
  inside (c-B)'s spectral-bridge work; if it bites, the fix is a
  user-approved widening of (N)'s `a ≤ 3` to an explicit `a ≤ K`.

**Dispatched: the (c-A) SCOPE SCOUT** (read-only; its dossier becomes
`ShortTime/ROUTE_C_PLAN.md`, the lane's plan file): dependency-ordered
inventory of the chain `IsLowSolveAt`/`IsAdaptedLowSolve` →
rungs 3/4/5 → `IsHmRungOrd`/`IsLowGateOrd` → `lowregAllMassAt`/
`lowreg_loMass` → the :1433 jet assembly, with per-declaration
widening class ((A) re-instantiate two-metric substrate /
(B) restate + same proof body / (C) proof genuinely uses
diagonality), the SLOT SEMANTICS ground truth (which argument of
`lowregNfun g₀ g₀`/`coreN`/`deTurckSmoothRemainder g g` is the
spectral-scale metric vs the coefficient background, anchored on
`lowBaseData` and on how `IsLowSolveBg` :962 already widens
`IsLowSolveAt` :478), file logistics (expected: NO monolith edits —
the two-metric substrate is public), brick decomposition with
estimates, and the beachhead brick.  PROJECT_MAP.md pointer
unchanged ((N)'s endpoint identity and sorry location did not move;
the route change is internal to this lane and recorded here).
Counter unchanged **2/3**.

---

## 228 (planner, 2026-08-07). SCOPE-SCOUT DOSSIER ADOPTED: zero verified
## class-C, zero monolith edits, universal slot convention; (c-A) = 8
## bricks ≈13–17 sessions; `ROUTE_C_PLAN.md` created; brick 1 dispatched

**Dossier adopted in full** (details now canonical in
`ShortTime/ROUTE_C_PLAN.md`; the ledger records the decisions):
- **Slot semantics ground truth**: slot 1 = state/spectral metric,
  slot 2 = DeTurck background, at EVERY definition site
  (`deTurckSmoothN` :109, `coreN` DenseN:152, `lowRegN` DenseSolve:75,
  `lowregNfun` UnifClassBounds:326, `lowBaseData` :3346,
  `lowregGalSol` :91).  No definitional identity forces the diagonal —
  it is pinned only in theorem STATEMENTS, and `IsLowSolve`'s own
  docstring records the pinning as a design choice already superseded
  by `IsLowSolveBg` on the Bg lane.
- **ZERO verified class-C items** — every suspected diagonal-use
  dissolved on inspection (the C2 kernel already calls two-metric
  `moserWin_phiDev g g`; the c0 tower PRICES `phiMetCurvCoeff g g g`
  as a jet constant rather than cancelling it; no `sub_self` anywhere
  in the read windows).  Residual B? = five unread proof bodies
  (probe at brick start; substrate verified two-metric, so a hidden
  diagonal helper would be a local restatement, not a wall).
- **ZERO monolith edits — VERIFIED**: all needed monolith producers
  (`lowBaseData`, `lowData_split`, `topKernel_eq`, `c0/c1/c2_eq`,
  `selfTopInt`/`selfLowInt`/`rhsSelfTop`) public and two-metric;
  private `c2_cap` reached only through public `lowData_split`.
- **Consumption map at the top**: in `lowreg_allOrderJet`'s proof,
  `hlo` is consumed at EXACTLY ONE point (`lowreg_forceJetMass` :1563);
  the only diagonal item beyond `hlo`/`hre` is `lowregNsec` (:1490),
  whose Bg analog `lowregNsecBg` exists and `BgSmoothPacket.force_coeff`
  is ALREADY stated against it ⟹ `bgreg_allOrderJet` is a
  (B)-restatement.
- **Brick plan** (ROUTE_C_PLAN.md table): 1 `IsBgSolveAt` bundle
  (beachhead) → 2a–2e DT tower/per-index/ladder in-place widenings →
  3/4 rung-3/4/5 Bg siblings (NEW files; diagonal lane byte-stable) →
  5 gate pack → 6 `IsAdaptedLowSolveBg` (carries the absorption-budget
  design flag) → 7 HigherRung Bg → 8 AllOrderJet mirror ending in
  `bgreg_allOrderJet`.  ≈13–17 sessions.  ONE executor at a time
  (DT checks import the 13.8k monolith).
- **Planner design ruling for brick 1** (Mathlib-discipline check): the
  bundle's fields are the CANONICAL Bg pieces
  (`IsLowBoundsAt` + `IsLowSolveBg` + `hTτ` + `hcap`) with
  IsLowSolveAt-shaped projection LEMMAS — not a 17-field parallel
  restatement of `IsLowSolveAt` (no fourth solve predicate).
- Dispatched: **brick 1 executor** (new `ST/LowRegBgSolveAt.lean`).
  Denominators: (N) **0%**; machinery (c)-based ≈**35–45%**; (c-A)
  0/8 bricks; HCG ≈**3%**.

---

## 229 (planner, 2026-08-07). CODEX REVIEW received (compressed-G3
## main + timeboxed T/2-smoothing bypass + Shi/Simon-no + calibration
## correction); reconciliation: written PRE-№225/№226 — the pivot and
## the gate probe invert its ranking; recommendation to user = stay (c)

**The review** (user-forwarded): (1) main route = compressed G3 —
prove only the uniform `ρ₀ C Z L` that `bgLift_of_radial` consumes,
middles private, endpoint `∃ K D, IsLowBoundsUnif ∧ ∀ g hclass, ∃ F,
IsBgLiftAt …`, next node `lieRefold_pair_lip_unif`; (2) ONE timeboxed
bypass test `bg_packet_half_of_solve : IsLowSolveBg … T →
Nonempty (BgSmoothPacket … (T/2))` via metricwise high/low
identification near t=0 + interior parabolic smoothing, strict stop
condition (any new background-aware all-order coupling / restart /
uniqueness base layer ⟹ abandon); (3) Shi/Simon curvature-first: not
chosen; (4) plan correction: G3 alone does not yield `BgLiftData` —
a small `exists_lowBounds_below`/scalar-calibration producer is also
needed.

**Reconciliation (planner, against the post-review evidence):**
- The review's (1) IS the №220/№222 architecture, already adopted
  once and then measured: №223 found the 109-node radius provenance
  with the `∃ρ` one-way door — "middles private" does not dissolve it
  (privacy is irrelevant to the door; the 103 restatements remain),
  and the ready frontier's monolith question stands.  Its next node
  `lieRefold_pair_lip_unif` belongs to that cancelled lane.
- The PIVOT (№225, planner-verified in the Lean text): the all-order
  step is diagonal-hardcoded ⟹ compressed G3 ALSO pays the whole
  ladder widening (it is №221 step 4–5's prerequisite).  The review
  prices compressed G3 without this block.  With it: compressed G3 =
  shared block + packet + lift ports ≈25–40+, vs (c) = shared block +
  synthesis ≈17–38.
- The review's (2) has route (c)'s INTENT (per-`g` high-order
  constants, class horizon kept) but the WRONG mechanism: interior
  parabolic smoothing is the documented in-tree stall
  (`ForcingTimeBootstrap.lean`: +2 gain vs +2 loss; the high-`a`
  variant rests on two open sorries), and the near-t=0 "high/low
  identification" is a weak–strong uniqueness layer the repo lacks —
  the review's OWN stop condition fires on inspection.  Route (c)
  achieves the same goal through the PROVED mechanism (the Galerkin
  rung ladder, `lowreg_loMass`), on the FULL horizon `T` (no `T/2`),
  riding the SAME solution (no identification layer).  The honest
  answer to the stop condition — "does it require background-aware
  all-order coupling?" — is yes, the ladder widening; but the pivot
  makes that block route-independent, so it cannot discriminate.
  Verdict: the timeboxed T/2 gate is unnecessary — its purpose is
  already secured, stronger, by the ruled route.
- The review's (3): agreement (Shi/Simon was never on the table).
- The review's (4): agreement, ALREADY RECORDED — under (c) the
  calibration producer appears as the gate-certificate/K-calibration
  seam (`ROUTE_C_PLAN.md` design flag 1; `LowRegBgBootstrap.md`
  ROUTE STATUS): the endpoint gains a gate hypothesis, discharged at
  the `lowreg_dt_unif` call site with `lowregGateAbsorb`-shaped
  calibration of `K`.  The review's work discipline (compose into
  the endpoint as you go; middles private) is adopted as (c)'s brick
  style regardless.
- **Brick 1 (`IsBgSolveAt`, in flight) is inside the SHARED block** —
  it is spent correctly under BOTH the ruled route and the review's
  ranking; nothing in flight is route-contingent.

**Standing**: the №227 ruling ((c)) remains in force; recommendation
communicated to the user = stay (c); if the user re-rules toward
compressed G3, the shared-block work transfers loss-free.  Counter
unchanged **2/3**.

---

## 230 (planner, 2026-08-07). USER CONFIRMED (c) after the №229
## reconciliation; a GPT Pro OVERALL RULING is incoming (reconcile on
## arrival); B?-bodies probe dispatched while brick 1 runs

- User: "ok 那还是坚持 c 继续,我又问了 pro 整体裁决,之后会发给你."
  The №227 ruling stands CONFIRMED post-Codex-review; execution
  continues.  When the Pro overall ruling arrives, reconcile it
  point-by-point against the ledger evidence (№225–№229 pattern)
  before changing anything; the shared block stays route-independent
  regardless.
- Dispatched (read-only, zero file overlap with brick 1): the
  **B?-bodies probe** — the five unread proof bodies of
  `ROUTE_C_PLAN.md` design flag 3 (C01JetTower Integrand section +
  `low1Ker_jet`; A1PerIndex engine sources :204–207;
  `lowregRung5PathAt` RungClosure:79; `lowregHighRungs`
  HigherRung:110; `lowreg_forceDriver`/`lowreg_spatialMass`
  AllOrderJet:761/:1099).  Verdict per body: B (restate-verbatim) or
  C (genuine diagonal use, exact step cited).  De-risks bricks
  2b/2d/7/8 before they are priced into sessions (the honest-input
  discipline: audit inputs BEFORE consumers).
- In flight: brick 1 executor (`IsBgSolveAt`).  Denominators
  unchanged: (N) **0%**; machinery ≈**35–45%** ((c)-based); (c-A)
  0/8; HCG ≈**3%**.

---

## 231 (planner, 2026-08-07). BRICK 1 LANDED AND ACCEPTED —
## `IsBgSolveAt` green/axiom-clean, zero statement-level deltas;
## brick 2a (DT C2 tower spine) dispatched

- **Brick 1 ACCEPTED** (planner spot-read: structure fields, the
  `hTτ` shape = `lowreg_sol_of_data`'s hypothesis verbatim, the
  dependent `solve : IsLowSolveBg … bounds …` field accepted by Lean
  directly).  `ST/LowRegBgSolveAt.lean` (231 lines):
  `IsBgSolveAt g₀ g_bg K hT hT1 u gforce Rcap` with fields
  `bounds`/`solve`/`hTτ`/`hcap`, plus 15 projections named exactly
  like `IsLowSolveAt`'s fields (`hδ hCtop hB1 hρ hP hreal hδ0 hδ3
  hcore hB0 hcont htame hzero hball hforce`) delivering the diagonal
  statements with the DeTurck slot freed.  Executor: fresh-file
  focused check GREEN warning-free (no stale-olean risk on a
  never-built file); axiom probe on the five substantive projections
  = the three standard axioms; claim released; field map in
  `LowRegBgSolveAt.md`.  Deltas: none at statement level (α-rename
  in `htame` to avoid shadowing `u`; `bounds.hreal` vs `h.hreal`
  bridged by proof irrelevance).  One report nit not propagated: the
  executor cited (N) at the stale `:98` (real site `:83`).
- **(c-A): 1/8 bricks done.**  Brick 2a dispatched: in-place widen
  of `topKerJetSharp` (C2JetTower:270) and `c2JetTowerSharp/Q` +
  `c2_jet_tower` (LadderRung C2 part), with repo-wide diagonal
  call-site fixups (known: `c2SupJet` A2PerIndex:206) and the
  targeted-olean-refresh sequence between upstream and downstream
  focused checks.  B?-bodies probe still in flight.
- Denominators: (N) **0%**; `bg_packet_of_solve` machinery ≈**36–46%**
  ((c)-based; brick 1 is a small step of the (c-A) block); HCG
  ≈**3%**.

---

## 232 (planner, 2026-08-07). B?-PROBE ADOPTED: four bodies clean B;
## ONE genuine class-C cluster found (the C01 towers, brick 2b) with
## repairs identified — the widened difference term is the ΔC0-passenger
## phenomenon again; 2b split and re-priced; execution order updated

**Verdicts adopted** (evidence lines in the probe report):
- **B**: A1PerIndex engines (all slot-1 or metric-free; `a1Arm0/1`
  statements pin `lowBaseData g g` = restatement only);
  `lowregRung5PathAt` (RungClosure:79 — field access + slot-1
  mode/Fatou engines; `lowregForceCont` is stated two-metric and
  applied diagonally); `lowregHighRungs` (HigherRung:110 — but see
  work-list: `galArmVec` is a diagonal-BAKED def);
  `lowreg_forceDriver`/`lowreg_spatialMass` (AllOrderJet:761/:1099 —
  mode-coordinate arguments, force abstract; the only two-slot object
  in `lowreg_forceJetStep` is ALREADY two-metric
  (`deTurckSmoothN_path_coeff_finiteOrder_jetSpectralMass`), applied
  diagonally; neither body touches `lowregNsec`/`coreN`/`lowregNfun`).
- **C — the C01-tower cluster** (brick 2b), three points, all with
  identified repairs and shelf originals:
  (a) `selfLow_split` (C01JetTower:188–224) kills the insertion
  difference `lc0Insert g gm g_bg − lc0Insert g gm g₀` by
  `sub_self` (:211) — widened, it SURVIVES as a sixth summand.  This
  is the ΔC0-passenger phenomenon of route error #2 in new clothing;
  repair = restate from the EXISTING three-metric `tail_base_split`
  keeping the difference term + one window pricing the insertion
  difference for `selfLow_jet(_quad)`.
  (b) `lieA1Atgw`/`low1Atgw` (Low1KerRadiusFree:617/:811): bg-pinned
  windows with NO two-metric original — proof exploits the bg=g₀
  collapse of 2 of 14 Ψ piece-factors.  Repair = free-bg restatement
  on the EXISTING three-metric piece expansion + `psiBAtgw (g₀ g_bg)`,
  plus a NEW grid-window cap for the non-collapsed factors via
  `connDiffSection g₁ g_bg = connDiff(g₁,g₀) + A(g₀,g_bg)` — the
  offset is STATE-FREE (the Bg-tame campaign's pattern).
  (c) C0 caps `lieCovCap`/`lieCovJet` (SelfLowArmCaps:927/:1238, bg
  pinned in the Palatini-residual statement) and `lc0AMixJet`
  (TameLieCorrJets:518, single-metric) — the two-metric template
  `lc0AMixCap (g₀ g_bg)` already exists.
- **Work-list additions** (diagonal-stated helpers the scope scout
  missed; folded into ROUTE_C_PLAN.md rows): `galArmVec` def BODY
  bakes `lowBaseData g₀ g₀` (RungThree:583/:590 — needs a bg-slotted
  analog def, brick 3), `galArmMassHm` (HigherRung:40), `galForceArm`
  (ForceArms:368), `IsRung5Path` (RungClosure:42, pins
  `lowregNfun g₀ g₀` :65), `lowregFatouE3At` (FatouIdent:385),
  `lowreg_projMode_at` (GalerkinIdent:308) — all pure restatements
  (brick 3/7 scope).
- **Consequences**: brick 2b re-scoped into 2b-i (window-layer
  repairs in Low1KerRadiusFree/SelfLowArmCaps/TameLieCorrJets) +
  2b-ii (tower assembly in C01JetTower incl. the sixth-summand
  restatement), priced 2–4 sessions total (was 1–2); (c-A) total
  ≈**14–19** (was 13–17).  Execution order updated to
  2a → 2c → 2b-i → 2b-ii → 2d → 2e (clean B bricks first; 2c depends
  only on 2a).  Design flag 3 RESOLVED.  Brick 2a (in flight) is
  unaffected — its files were scope-scout-read directly.
- Denominators unchanged: (N) **0%**; machinery ≈**36–46%**; (c-A)
  1/8 done; HCG ≈**3%**.

---

## 233 (planner, 2026-08-07). BRICK 2a LANDED AND ACCEPTED — the DT C2
## tower spine is two-metric, zero class-C surprises; brick 2c
## dispatched; one tooling lesson recorded

- **Brick 2a ACCEPTED**: `topKerJetSharp` (C2JetTower:270),
  `c2JetTowerSharp` (:156), `c2JetTowerQ` (:226), `c2_jet_tower`
  (:289, LadderRung) all widened IN PLACE to `(g, g_bg)` — statement
  slots freed (`rhsRefoldTop g g_bg`, `deTurckPhiMetTotal g g_bg g`,
  `(lowBaseData g g_bg T …).C2`), proof deltas pure re-instantiations
  (`moserWin_phiDev g g_bg`, `topKernel_eq g g_bg`,
  `rhsRefoldTop_joint g g_bg`); slot-1 legs untouched.  THREE diagonal
  call sites fixed explicitly (`topKer_jet` C2JetTower:370 — kept
  deliberately diagonal as the compat form; `a2LadderQ` LadderRung:371
  — brick-2e territory; `c2SupJet` A2PerIndex:206); exhaustive grep
  found no other term-level consumer.  Focused checks + targeted
  module builds green on all three files, with the LadderRung build
  transparently rebuilding downstream `SelfLowArmCaps` and
  `LowRegC01JetTower` clean; axiom probes on all four = the three
  standard axioms; claims released; same-name notes updated.  ZERO
  class-C steps — the scope scout's class-B prediction scores TRUE.
- **TOOLING LESSON** (for all future executor briefs):
  `lake-locked.ps1 claim -Files` requires COMMA-separated paths —
  space-separated silently binds only the FIRST file, and `.md` paths
  are silently ignored.
- **(c-A): 2/8 bricks done.**  Brick 2c dispatched (A2 per-index:
  `c2SupJet`, `a2PerIdxJet`, `a2PerIdxLin` in `DT/LowRegA2PerIndex.lean`;
  known downstream diagonal consumers to fix: `armLadder3`
  RungThree:311–313, `armOrder3/4` RungFour/Five).  Denominators:
  (N) **0%**; machinery ≈**37–47%**; HCG ≈**3%**.

---

## 234 (planner, 2026-08-07). BRICK 2c LANDED AND ACCEPTED — the A2
## per-index family (`Cqa`/`Ka` host) is two-metric; first C-repair
## brick 2b-i dispatched

- **Brick 2c ACCEPTED**: `c2SupJet` (:185), `a2PerIdxJet` (:278),
  `a2PerIdxLin` (:411) widened in place to `lowBaseData g g_bg`
  statements; slot-1 helpers (`appCcPerIdxL2`, `icgWinShift`,
  `sqrtAdd2`, `sqrtFinSum`) deliberately untouched.  Three diagonal
  consumer sites fixed (`armLadder3` RungThree:311, `armOrder3`
  RungFour:88, `armOrder4` RungFive:85 — their own statements
  untouched, brick-3/4 territory; adjacent `a1PerIdxLin` calls stay
  single-metric until 2d).  Focused checks + targeted builds GREEN
  (incl. an extra `+RungFive` build leaving the rung olean state
  consistent for other agents); axiom probes clean; claims released.
  ZERO class-C steps.  Durable pattern confirmed: `hshape` rfl
  survives because `LowBaseActionData g` is slot-1-TYPED — widening
  is value-level only, exactly the scout's slot-semantics claim.
- **(c-A): 3/8 rows done (1, 2a, 2c).**  Dispatched **brick 2b-i** —
  the first C-repair brick (№232 points (b)+(c)): free-bg restatement
  of `lieA1Atgw`/`low1Atgw` (Low1KerRadiusFree:617/:811) on the
  three-metric piece expansion (`deTurckLieArm1Coeff_eq_lieArm1Piece_sum`
  :4238) + `psiBAtgw (g₀ g_bg)` (:451), with the NEW state-free
  offset cap for the two non-collapsed Ψ factors
  (`connDiffSection g₁ g_bg = connDiffSection g₁ g₀ + A(g₀,g_bg)`);
  widen `lieCovCap`/`lieCovJet` (SelfLowArmCaps:927/:1238, incl.
  their bg-pinned Palatini-residual upstream if needed); two-metric
  `lc0AMixJet` from the `lc0AMixCap` template (TameLieCorrJets:518).
  Consumer fallout lands in C01JetTower (2b-ii's file) — diagonal
  fixups only.  Denominators: (N) **0%**; machinery ≈**38–48%**;
  HCG ≈**3%**.

---

## 235 (planner, 2026-08-07). PRO OVERALL RULING received (sections
## 一.5/二/三/四 readable; 五–七 GARBLED, re-paste requested) — C1
## adopted; (c-B) RE-SCOPED to absorptive-only (№226's 7-family scope
## REFUTED by Pro's counterexample); phase order REARRANGED c-C0-first;
## STOP-condition discipline recorded

**Adopted point-by-point** (reconciled against №225–№234 evidence):
- **一.5**: `lowreg_loMass`'s `∑' weight·(perModeConv)² ≤ Cσ` with no
  T-shortening is the right mass foundation; `lowreg_allOrderJet` is
  a hybrid — route (c) must write a NEW producer NOT through
  `IsRealizedTwo`, not a `g g → g g_bg` edit of the hybrid.  Aligned
  with brick 8's parameterized design; confirmed.
- **二 (C1) ADOPTED**: the frontier is RESTATED as
  `bg_packet_of_adapt (ha : IsAdaptedLowBg g g_bg K hK hT hT1 u
  gforce) : Nonempty (BgSmoothPacket g g_bg K T)`, replacing
  `bg_packet_of_solve` (which quantifies over ALL `IsLowBoundsAt` K —
  the absorption inequality is NOT derivable there; `lowreg_adapt_open`
  calibrates BEFORE solving, so adaptation is not a free
  post-certificate).  Class-first producer `lowreg_adapt_unif`
  chooses uniform gate bounds/threshold/state cap + a literal common
  `K` BEFORE `g`.  (N)'s statement unchanged; `lowreg_dt_unif`'s
  STATEMENT unchanged; its PROOF BODY rethreads (uniform solve →
  uniform adapted solve).  **Plan-language correction (honest)**: my
  "`lowreg_dt_unif` stays untouched" (№225/№227, ROUTE_C_PLAN) was
  interface-level only — corrected everywhere this entry.
- **三 (jet budget) ADOPTED — №226's (c-B) scope REFUTED**: Pro's
  counterexample (`g_n = e^{2f_n} gBase`, `f_n = n⁻³ sin(n x₁)`:
  in the C³ class uniformly, 4th derivative ~ n) proves NO constant
  truly reading ≥4th-order jets of the VARYING metric can be
  class-uniformized from `a ≤ 3` data.  Correct layering: uniformize
  ONLY what enters absorption smallness (Ā, B̄, δ, state-radius cap)
  and PROVE those read only 0–3 jets of the varying `g`
  (coefficient fields sit at `gBase` after widening — free); leave
  metricwise (chosen after `g`): high-order Grönwall constants,
  per-σ mass bounds `Cσ` (existentially selected after `g`, σ —
  never class-first), high-order Sobolev/jet bridges,
  smooth-reconstruction majorants.  Do NOT copy `IsLowGateOrd` into
  a uniform-everything `IsLowGateBg`; FIRST split the gate into
  absorptive small coefficients vs metricwise high-rung bookkeeping
  (audit where the Grönwall closure actually uses the smallness —
  rung-4/5 bridge factors in B are the suspect bookkeeping part).
  **STOP CONDITION (verbatim discipline)**: if the absorptive
  coefficients themselves need ≥4th jets of `g`, that is a STOP for
  the current (N) statement — changing `a ≤ 3` is a separate
  theorem-level USER ruling, never a mid-implementation edit.
  Honest scoring: №226's flag had the right locus (bridges/embedding)
  but ranked "widen (N)" as first remedy — wrong; the split comes
  first.  (c-B) SHRINKS (absorptive slice + audit), likely cheaper
  than the 6–14 estimate.
- **四 (reorder) ADOPTED**: route (c)'s route-specific risk is the
  escape from `IsRealizedTwo`, so it is tested FIRST: new phase order
  **c-C0 (fixed-metric direct-synthesis feasibility gate — the
  diagonal `bg_packet_of_adapt` prototype on the PROVED diagonal
  ladder, zero widening) → c-A (MINIMAL widening, defined by c-C0's
  consumption map) → c-B (absorptive gate) → c-C (final assembly)**.
  `lowreg_loMass` gives state spatial mass; the packet also needs
  `mode_smooth`/`mode_mass`/`mode_eq`/H²-forcing/carrier — c-C0
  determines whether those come from `hlo` alone.  Brick 2b-i (in
  flight) CONTINUES — the window layer is in every minimal set (the
  per-`g` Bg rung ladder consumes it under C1 regardless).
- **五–七 GARBLED** in transmission (fragments consistent with the
  above; the concrete `IsAdaptedLowBg` interface sketch and the final
  ordering appear to match 二+四).  Re-paste requested; nothing from
  the garbled text was acted on.
- Dispatched: **c-C0 SCOUT** (read-only, parallel-safe with 2b-i).
  Denominators: (N) **0%**; machinery ≈**38–48%** (unchanged — the
  reorder moves risk forward, not progress); HCG ≈**3%**.

---

## 236 (planner, 2026-08-07). c-C0 DOSSIER ADOPTED: verdict (ii) —
## the escape from `IsRealizedTwo` is provable from shelf + TWO new
## lemmas + ONE signature amendment (≈3–4 sessions); the identification
## risk DISSOLVES; the calibration amendment converges exactly with C1

**Adopted findings** (full dossier in the task output; sites verified
by the scout against source):
- **`hre`-inventory closes**: of everything `IsRealizedTwo` supplies,
  the continuity/cap certs are R1 (verbatim from `hlo` fields —
  `lowregNfun` IS `lowRegN g g …` by delta); the coefficient bundles
  `FHi/FLo` + A2 certs are R2 via the existing producer recipe
  (`lowreg_solve_open` :645–689; `refold_aff` is ALREADY the diagonal
  of the 206-arc's `refold_aff_bg` — the refold sublayer of the
  retired lift RE-ENTERS as live shelf); the order-2 carrier is
  `maxRegDuhamelMap 2 hT hT1 0 fHi` with `duhamelCross`/
  `solField_toFun_ae` replacing `ucs`.  Conjuncts existing only to
  run the hybrid's contraction are simply dropped.
- **The KEY identification is a SHELF THEOREM**: `force_hi_id`
  (`LowRegForceHi.lean:373–456`) + `hiN_lowreg` (:299) +
  `tensorHsInclusion_injective`, fed by `hlo.hforce`, with
  mode-blindness from `timeL2Inclusion_maxRegDuhamelSolField`.
- **`fHi` via Nemytskii EVALUATION, not forcing-mass summation**
  (the feared route is an honest-sorry deep leaf and provably the
  wrong way): `w4 := solFieldAtOrder hT.le fLo 4` needs only
  SOLUTION mass at σ=4 (`lowreg_loMass` + Tonelli); then
  `fHi := MemLp.toLp (liftHiN … FHi (w4 t))` — affine growth from
  radial truncation ⟹ `L²ₜ`.
- **Signature amendment = C1 convergence**: `IsAdaptedLowSolve`
  lacks the refold-radius calibration (`hRρ` is solve-PRE); the
  prototype adds `(ρ, hρ, hreal', hcal : stateRad ≤ ρ)` — exactly
  what brick 6's `IsAdaptedLowBg` absorbs per №235.
- **No horizon/slab gap**: same `T` throughout, closed-slab chain,
  t=0 corner free — the entire gain over the hybrid confirmed at
  implementation grain.
- **Work plan (after 2b-i frees the Lean slot)**: c-C0-1
  `duhamel_mode_pin` (generic a.e. cross-scale coefficient pin,
  ~0.5–1); c-C0-2 `lowreg_forceHi2` (fHi + hincl/hfix/hballU,
  ~1–1.5; risk carrier = the `liftHiN` affine/memLp assembly, the
  scout's one unverified step); c-C0-3 the prototype assembly
  (mirror AOJ:1492–1590 + packet packaging, ~1–1.5) — prototype
  lives IN `LowRegAllOrderJet.lean` (1931 lines) for private access
  to `carrier_coeff_pmConv`/`coord_eq_smoothN`.  Minimal-(c-A) list
  banked in the plan (§4 of the dossier).
- Remaining (c-A) bricks (2b-ii, 2d, 2e, 3–8) PAUSE until c-C0
  lands and its consumption map fixes the minimal set (№235 order).
  Denominators: (N) **0%**; machinery ≈**40–50%** (identification
  risk retired); HCG ≈**3%**.

---

## 237 (Codex, 2026-08-07). c-C0 / BRICK 0 PROVED BY DIRECT ORDER-ONE
## FORCING SYNTHESIS; THE №236 `liftHiN` DESIGN IS SUPERSEDED

- New public theorem `lowreg_directJet` in `LowRegDirectJet.lean` is
  proved, focused-green, and axiom-clean with exactly
  `[propext, Classical.choice, Quot.sound]`.
- The checked proof starts from diagonal `IsAdaptedLowSolve`, obtains
  all-order solution mass from `lowreg_loMass`, runs the forcing
  driver directly at order one using `lowReg_force_smooth`, promotes
  the resulting coordinate family spectrally to an H² forcing, and
  constructs the order-two Duhamel carrier, mode pin, state bound,
  exact smooth forcing identity, and realization radius.
- The proof contains no `IsRealizedTwo`, `liftForceHi`, `liftHiN`,
  `lowregLiftHorizon'`, `hbridge`, `hFComm`, or `hA2sq`.  Therefore
  the Brick-0 stop condition did not fire, and the calibration tuple
  predicted in №236 is unnecessary.
- `carrier_coeff_pmConv` was made public in `LowRegAllOrderJet.lean`;
  its statement and proof body are unchanged.
- The next route-(c) task is now determined by the actual consumption
  map: parameterize only the adapted-solve/low-mass/rung chain needed
  by `lowreg_directJet`, then assemble `bg_packet_of_adapt`.  Do not
  resume the old adjacent-scale A1/A2 completion lane or mechanically
  continue the broad 2b-i queue.
- Honest denominators: theorem `lowreg_directJet` **100%**; Brick 0
  **100%**; route-(c) background/adapted endpoint lane ≈**35%**;
  headline `(N)` **0%** until its endpoint no longer transitively
  depends on `sorryAx`; broader dedicated machinery ≈**80%**; HCG
  ≈**3%**.

---

## 238 (Codex, 2026-08-07). EXACT TWO-METRIC ENDPOINT SEAM PROVED;
## BACKGROUND MASS IS NOW THE ONLY INPUT MISSING FROM THE PACKET

- `LowRegDirectJet.lean` now exports `direct_jet_of_mass`.  It takes
  primitive fixed-background solve data at `(g,g_bg)` and the exact
  all-order spatial-mass conclusion, and returns the full order-two
  carrier/forcing packet data on the same horizon.  It has no
  dimension-three hypothesis; dimension enters only in the mass
  producer.  The old `lowreg_directJet` statement remains intact as
  a thin diagonal wrapper.
- `LowRegBgBootstrap.bg_packet_of_mass` is proved.  It combines
  `IsLowBoundsAt`, `IsLowSolveBg`, and the mass input with
  `direct_jet_of_mass`, producing `BgSmoothPacket` on the original
  `T`.  The existing `dt_of_bg_packet` and gauge endpoint therefore
  need no redesign.
- The first fixed-background Galerkin leaf `galN_evalBg` is proved in
  new `LowRegBgForceArms.lean`.  It is a direct use of the already
  two-metric `lowRegN_on_smooth`; no new estimate or lift certificate
  is involved.
- This isolates the remaining analytic dependency exactly as
  `lowreg_loMassBg`.  The force-arm and scalar wrappers are initially
  mechanical; the first genuine obstruction occurs when
  `armLadder3Bg` reaches diagonal `a1PerIdxLin`, whose C01 tower
  currently cancels a background insertion difference by `sub_self`.
- Verification: the direct core, its refreshed module, the new packet
  adapter, and `galN_evalBg` all pass focused checks.  The only warning
  in `LowRegBgBootstrap` is its pre-existing
  `bg_packet_of_solve` `sorry`; the new adapter is complete.
- Honest denominators: `direct_jet_of_mass` **100%**;
  `bg_packet_of_mass` **100%**; fixed-background mass chain ≈**3%**;
  route-(c) background/adapted endpoint lane ≈**40%**; headline `(N)`
  **0%** until the superseded bare-solve frontier is removed from the
  endpoint dependency; broader dedicated machinery ≈**80%**; HCG
  ≈**3%**.

---

## 239 (Codex, 2026-08-07). BACKGROUND FORCE-ARM FRONT COMPLETE;
## NEXT FRONTIER IS THE A1/C01 FIXED-OFFSET INSERTION DIFFERENCE

- `LowRegBgForceArms.lean` now proves `galN_evalBg`, `galArmIdBg`,
  `galArmCapBg`, and `galForceArmBg`.  All four are direct two-metric ports of
  established identities/caps and introduce no new analytic assumption.
- Focused verification is green with four threads and a 6144 MB cap; the new
  module is warning-free and contains no `sorry`.
- `bg_packet_of_mass` is independently axiom-audited with exactly
  `[propext, Classical.choice, Quot.sound]`.  `LowRegDirectJet.lean` and
  `LowRegBgBootstrap.lean` pass their final focused checks after the temporary
  audit commands were removed.
- The next honest producer is not another force-arm wrapper.  `armLadder3Bg`
  reaches diagonal `a1PerIdxLin`; below it, `selfLow_split` removes the sixth
  insertion-difference summand using `sub_self`.  For an independent
  background this summand survives.  Brick 2b-i must first prove the
  fixed-offset background A1/window estimates, and brick 2b-ii must retain and
  price that summand in the C01 tower.
- Honest denominators: the four force-arm producers **100%**; fixed-background
  mass chain approximately **8%**; route-(c) background/adapted endpoint lane
  approximately **42%**; headline `(N)` **0%** while the endpoint still
  transitively uses the superseded `bg_packet_of_solve` `sorry`; broader
  dedicated machinery approximately **80%**; HCG approximately **3%**.

---

## 240 (Codex, 2026-08-07). THE ARBITRARY-BACKGROUND C01 SEAM IS CLOSED

- The fixed-offset A1 window is proved through `bgCcAtgw`,
  `lieA1AtgwBg`, and `low1AtgwBg`; the diagonal declarations remain wrappers.
- The AMix correction is now sharp: `mcdBgAtgw` has offset `n+1`,
  `amixBgAtgw` has offset `n+2`, and `lc0AMixJetBg` gives the full
  arbitrary-background `K0/K2` tame bound.
- The insertion correction is isolated in new `Lc0InsertDiffWindow.lean` as
  `lc0InsDiffAtgw`, also at offset `i+2`.  It uses the exact public field
  identity `lc0InsDiff_eq` and does not depend on the broken/oversized
  `LieCorr0LowJet` route.
- `LowRegC01JetTower.lean` now proves `lieBgJet`, `insBgJet`,
  `selfLowJetQBg`, and `c0JetTowerQBg`.  The last two were implemented by
  generalizing the existing diagonal proof once and retaining the former
  theorem names as compatibility wrappers.
- Focused checks and all direct targeted refreshes are green.  No new `sorry`,
  axiom, or heartbeat override was introduced.
- Brick 2d (`a1PerIdxJetBg`/`a1PerIdxLinBg`) has been source-ported and is the
  current verification target; after that, the remaining conditional mass
  chain is background threading through ladder/rung consumers.
- Honest denominators: the C01 background brick **100%**; the conditional
  theorem `lowreg_loMassBg` remains unstated (**0%**) with about **70%** of its
  dedicated backgroundized machinery available; route-(c) background/adapted
  endpoint lane ≈**50%**; headline `(N)` **0%**; broader dedicated machinery
  ≈**80%**; HCG ≈**3%**.

---

## 241 (Codex, 2026-08-07). A1 AND LADDER BACKGROUND PORTS ARE EXPORTED

- `LowRegA1PerIndex.lean` now provides `a1PerIdxJetBg` and
  `a1PerIdxLinBg`; its focused check is warning-free, its direct targeted
  refresh is green, and the exported `.olean` is fresh.  The old diagonal
  declarations retain their exact original types as compatibility wrappers.
- `LowRegLadderRung.lean` now provides `a2LadderQBg`, `a1_ladder_bg`,
  `a1LadderQBg`, `nDiffHmQBg`, `IsHmRungOrdBg`, and `lowregHmPackBg`.
  Focused verification and the targeted refresh are green; the six new
  declarations have only the standard axioms `[propext, Classical.choice,
  Quot.sound]`.
- The next conditional mass layer is now a mechanical fixed-background port:
  Rung 3/4/5 source work is split into new `LowRegBgRung*.lean` siblings and
  will be verified serially.  The first genuine remaining seam is the later
  class-first absorptive/gate audit, not another C01 coefficient estimate.
- Honest denominators: bricks 2d and 2e **100%**; `lowreg_loMassBg` remains
  unstated (**0%**); its dedicated backgroundized machinery is approximately
  **75%**; route-(c) background/adapted endpoint lane ≈**55%**; headline
  `(N)` **0%**; broader dedicated uniform-existence machinery ≈**80%**;
  HCG ≈**3%**.

---

## 242 (Codex, 2026-08-07). CONDITIONAL BACKGROUND MASS AND PACKET CHAIN CLOSED

- New fixed-background siblings now prove the complete metricwise chain:
  Rung 3/4/5, coherent gate bookkeeping, adapted-solve packaging, Galerkin
  identification, primitive Fatou closure, the common rung-five path, generic
  higher rungs, all-real spatial mass, and the final packet adapter.
- In particular, `lowreg_loMassBg` is now a proved every-real-exponent producer,
  and `bg_packet_of_adapt` combines it with `bg_packet_of_mass` on the same
  horizon.  All new direct modules pass focused checks and targeted refreshes;
  single-worker refreshes were used after one broad stale-dependency refresh
  exposed a high memory peak.
- This closes the conditional implication
  `IsAdaptedLowSolveBg -> Nonempty (BgSmoothPacket ...)`.  It does not choose
  the adapted certificate before the class metric varies.
- Honest denominators: `lowreg_loMassBg` **100%**;
  `bg_packet_of_adapt` **100%**; the metricwise background direct-smoothing
  chain **100%**; class-first `lowreg_adapt_unif` **0%**; headline `(N)` **0%**;
  dedicated uniform-existence machinery approximately **82%**; HCG **3%**.

---

## 243 (Codex, 2026-08-07). CLASS-FIRST ABSORPTION STOP CONDITION FIRED

- The current `IsLowGateOrdBg` cannot be uniformized from the C3 metric class.
  At rung three, its radius coefficient follows
  `Kr1 -> Kb1 1 -> Kc 3 -> fixCdAtgw 3`, hence contains
  `nabla^3 (connDiff g gBase)`.  Since `connDiff` already differentiates `g`,
  this reads the fourth metric jet of the varying metric.  Rungs four and five
  read still higher towers and high-order spectral bridges.
- These quantities are not dead bookkeeping: `lowregRung5PathAtBg` uses the
  common `A,B` budget to absorb each fixed rung.  Neither shrinking the time nor
  merely rebuilding `LowRegBoundData` removes the unbounded coefficient.
- Therefore the route plan's explicit C3 stop condition has fired.  Do not
  prove `lowreg_adapt_unif` from the current gate, do not swap quantifiers, and
  do not silently strengthen `(N)` to four or more jets.
- The smallest honest next design is an absorption-only gate that moves the
  fixed-offset and high-jet terms out of the small top/radius coefficient and
  into metricwise Gronwall terms.  Only after that producer exists does a scalar
  shrink theorem for one common `LowRegBoundData` become meaningful.
- Honest denominators: redesigned absorption-only producer **0%**;
  `lowreg_adapt_unif` **0%**; headline `(N)` **0%**; conditional metricwise
  direct-smoothing chain **100%**; dedicated uniform-existence machinery
  approximately **82%**; HCG **3%**.

---
