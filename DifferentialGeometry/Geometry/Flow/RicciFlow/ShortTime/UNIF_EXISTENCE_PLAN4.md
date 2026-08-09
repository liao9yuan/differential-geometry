# UNIF_EXISTENCE_PLAN4 — continuation of `UNIF_EXISTENCE_PLAN3.md`

`UNIF_EXISTENCE_PLAN3.md` reached the project's 3000-line file limit at the
No. 124 / A1-CUR-2 SESSION 3 dispatch.  This file continues it.  Read PLAN3
first for everything up to and including that dispatch; nothing there is
superseded.

---

## Executor report — A1-CUR-2 SESSION 3 (2026-08-04)

**Both open windows are closed.  `selfLow_jet` and `c0_jet_tower` are
unconditional, so the F6 ESTIMATE CHAIN IS CLOSED: both towers (`c1` from
A1-CUR-1, `c0` from A1-CUR-2) now stand on no `sorry`.**

### Census (explicit)

Targeted build of `…DeTurck.LowRegC01JetTower`: **9610 jobs, successful.**
Axiom census (`ScratchC01Census.lean`, extended): every listed declaration is
`[propext, Classical.choice, Quot.sound]` — in particular `ricciDACap`,
`lieCovCap`, `selfLow_jet`, `c0_jet_tower`, `c1_jet_tower`, `low1Ker_jet`,
`selfLow_split`, and the new `capOfP` / `capOfDP` / `capDdc0`.  **No `sorryAx`
anywhere in the census.**  `LowRegC01JetTower.lean` sorry census: **ZERO**
(was two).  `SelfLowArmCaps.lean` and `GradCapArms.lean`: zero.

### What closed each window

* **`ricciDACap`** (Palatini arm).  As diagnosed: leaf inventory only.
  `refoldKernelContractionMonomialField_eq_mvPairTraceRefold` is public and
  holds for an arbitrary `(0,4)` argument; `mvPairTraceOp g₀ g₀` is state-free
  (`capOfBnd`); `slotInsertEndoCc s (fullRaisedEndoField g₀ g₁)` gets a new
  offset-`+1` window `endoAtgw`; `connLowOp` gets `clAtgw`, and its covariant
  derivative enters at `+2` through `rfns_iteratedCovGrad_covGrad_comm_rs`;
  `∇P` enters through the new `capOfDP`; `domDomCongrSection` at `(0,4)`
  through the new `capDdc0`.  The private `koszulOp` of the read-only
  low-base action module was never named — `clSplit : ∃ Z, ∀ g₁, connLowOp … = … Z`
  is proved by `⟨_, fun _ => rfl⟩` and only state-freeness of `Z` is used.
* **`lieCovCap`** (Lie covariant-derivative edge).  `lieCov_residual` applies
  directly (the `edgeLiePairFam` bridge is `rfl`); `lieCovPair = appCcRS
  (pureTrace 2) (pureTrace 4)` is `rfl` as predicted, with a new generic-valence
  `ptAtgw`; the curvature head is capped because `(-(s/2))•lrCurvF g₀ T =
  (-(1/2))•lrCurvF g₀ P` (new `curvSmul` + new `capOfP`) — the `s`-factor is
  load-bearing, no constant sees `s`; the quadratic `lrQuadF` is six slot
  permutations of `lieCovArm2 ⋆ lrOmegaHat`, both factors one-derivative.

### Correction to session 2's diagnosis (route-error counter unchanged, 0/3)

Session 2 recorded `lrQA`/`lrQB` as having windows "only as private
`bd*_gridWindow`" and priced `lieCovCap` at about a session.  Three of those
four private walls have **public wrappers in the same file**:
`lieCovArm2_l2` (wraps `bdArmSlot2_rfns_le`), `fullRev0_eq` and `omRecover_add`
(wrap the recovery decomposition); and `connLow_rfns` in
`FlatArmCoeffConnectionDifferenceBridge.lean` is the public
`connDiffLoweredCc` ↔ `connDiffSection` fibre-norm bridge.  Only `lrOmegaHat`
had to be re-estimated, from its own public definition (~90 lines).  This is
the same over-count pattern already in memory; the standing rule
"grep for a public wrapper before declaring a wall" now has five instances.

**Cost measure, as mandated:** reverse closure of
`RiemannCoefficientPalatiniRefold.lean` is **170 modules / ~229k lines**
(19.5k + 13.8k + 10.9k + 9.6k + 9.4k-line files among them).  Promotion was
therefore rejected; zero files outside the three claimed ones were touched.

### Files

New `Analysis/Spectral/Intrinsic/DeTurck/SelfLowArmCaps.lean` (1012 lines,
public `ricciDACap`/`lieCovCap` + private leaf inventory) and its `.md`;
`Analysis/Sobolev/TensorHilbert/GradCapArms.lean` +85 lines (`capOfP`,
`capOfDP`, `capDdc0`, private `capBaseLe`);
`Analysis/Spectral/Intrinsic/DeTurck/LowRegC01JetTower.lean` — the two private
stubs deleted, one import added; `ScratchC01Census.lean` extended.
No stop signal fired: nothing landed at `range (i+3)`, nothing inherited
`a ≥ 16`.

### Honest denominators

* **`selfLow_jet`: 0% → 100%** (proved, axiom-clean).  `c0_jet_tower`:
  ≈ 20% → **100%**.  `c1_jet_tower` was already 100%.
* **A1-CUR: ≈ 78% → 100% (brick closed).**
* **F6 ≈ 76% → ≈ 88%.**  The estimate chain is closed; what F6 still lacks is
  **A1c `a1_ladder`** and **A1d `n_diff_hm_rung`** — routine assembly over the
  now-unconditional towers, both **0% (unwritten)** — and after them the
  P-STOP-gated Galerkin lane.
* Front 2 ≈ 56% → ≈ **62%**.  Machinery ≈ **97%**.
* **(N) `ricci_flow_unif_existence`: 0%.**  Stated at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  Nothing this
  session moved it; a closed estimate chain is an input to it, not a part of it.
* Whole HCG compactness project: low single digits.
* Route-error counter: **0/3** — no failed route, no statement changed.

### Next target (A1c)

`a1_ladder`, the `a1` sibling of `a2_ladder`
(`DeTurck/LowRegLadderRung.lean:232`).  `a2_ladder`'s binder shape, adapted to
`a1`, is:

```text
theorem a1_ladder (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a)   -- a2 has 3 ≤ a
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1/3) :
    ∃ (κ : ℝ) (Clower : ℕ → ℝ), 0 ≤ κ ∧ (∀ m, 0 ≤ Clower m) ∧
      ∀ (T) (hT : symmetry) (hδg) (hδZ),
        ‖smoothCcToTensorHs g₀ ((a:ℝ)+2) T‖ ≤ R₀ →
        ∀ m : ℕ, ‖smoothCcToTensorHs g₀ (m:ℝ) ((lowBaseData g₀ g₀ T … ).a1 T)‖ ≤
          κ * (δ / (1-δ)^2) * ‖smoothCcToTensorHs g₀ ((m:ℝ)+1) T‖
            + Clower m * ‖smoothCcToTensorHs g₀ (m:ℝ) T‖
```

i.e. `a2`'s `+2 / +1` top-and-lower pair drops to `+1 / +0`, because `a1`
carries only one derivative of the state; the gate drops from `3 ≤ a` to
`1 ≤ a` (`selfLow_jet`'s gate), and the two tower inputs are `c1_jet_tower`
and `c0_jet_tower` in place of `c2_jet_tower`.  Confirm the exact `.a1`
projection and the operator-norm engine's `appCc_cap_hs_le` arity before
writing it.

## Planner update No. 126 (2026-08-04) - SESSION 3 ACCEPTED: **THE F6 ESTIMATE CHAIN IS CLOSED**; A1c/A1d DISPATCHED

MILESTONE ACCEPTED (planner spot-check: `LowRegC01JetTower.lean` has
ZERO textual sorry occurrences; PLAN4 opened correctly with the PLAN3
pointer).  `ricciDACap` and `lieCovCap` proved; `selfLow_jet` and
`c0_jet_tower` UNCONDITIONAL; with A1-CUR-1's tower this closes the
LAST real estimate of the F6 chain.  Census explicit and clean
throughout (9610-job build; no sorryAx anywhere; neither stop signal
fired).

Mathematical points worth the record:
- The `s`-factor is LOAD-BEARING in `lieCovCap`:
  `(-(s/2))•lrCurvF g₀ T = (-(1/2))•lrCurvF g₀ P` by linearity is the
  ONLY reason the curvature head is capped at all (`lrCurvF g₀ T`
  contains the order-0 jet of `T`, which no cap controls; `|P| ≤ Λ`
  is exactly `hP0`).  No constant sees `s`.
- The read-only file's private `koszulOp` was never even named:
  `clSplit : ∃ Z, ∀ g₁, connLowOp g₀ g₁ = … Z := ⟨_, fun _ => rfl⟩`
  — only state-freeness of the witness is used.  (The opacity
  discipline used offensively.)
- OVER-COUNT INSTANCE (5th of the wall-census pattern, recorded):
  three of session 2's four claimed `lr*` walls had PUBLIC wrappers a
  few hundred lines away (`lieCovArm2_l2`, `fullRev0_eq`,
  `omRecover_add`) plus the public `connLow_rfns` bridge; only
  `lrOmegaHat` needed re-estimation (~90 lines).  Grep for the public
  wrapper before declaring a wall — now with FIVE exhibits.
- The cost-measure rule earned its keep: the Palatini file's reverse
  closure is 170 modules / ~229k lines — promotion correctly refused;
  zero files outside the three claimed were touched.

New: `DeTurck/SelfLowArmCaps.lean` (1012 lines, both windows);
`GradCapArms.lean` gained `capOfP`/`capOfDP`/`capDdc0`.

DISPATCHED: A1c (`a1_ladder`) + A1d (`n_diff_hm_rung`) — the two
routine assembly bricks over the towers, with the executor instructed
to RECONCILE the two recorded `a1_ladder` shapes (the κ-form quoted
above vs the №111-era κ-FREE consumer signature `‖a1 T‖_{H^m} ≤
Clower m·‖T‖_{H^{m+1}}`) by what the downstream hierarchy actually
needs — the a₁ arm is a lower-slot arm, so the κ-free form is
preferred unless the engine algebra forces otherwise.

Honest denominators: `selfLow_jet` 100%; `c0_jet_tower` 100%; A1-CUR
CLOSED; **F6 ≈ 88%** (remaining: A1c/A1d 0% + the P-STOP-gated
Galerkin lane E1′/E4/G4/Z toward `lowreg_spatialMass`); front 2
≈ 62%; machinery ≈ 97%; **(N) 0%** (stated at
`Evolution/ExtendViaUniqueness.lean:80`, sorry :98 — the closed
chain is an INPUT to it, not part of it); whole HCG compactness
project: low single digits.  Route-error counter: 0/3.

---

## Executor report — A1c + A1d (2026-08-04)

**Both bricks landed, both first-try green.  F6's LADDER LAYER IS COMPLETE:
`a2_ladder`, `a1_ladder` and `n_diff_hm_rung` are proved, unconditional and
axiom-clean.**

### Census (explicit)

Targeted build of `…DeTurck.ScratchC01Census` (which pulls in
`LowRegLadderRung`): **9620 jobs, successful**, `GUARD-STATUS: OK`.
`a1_ladder`, `n_diff_hm_rung`, `a2_ladder`, `appCc_cap_hs_le` and the re-gated
`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le` each report
`[propext, Classical.choice, Quot.sound]`.  **Zero `sorryAx` in the whole census
output.**  Textual `sorry` census: `LowRegLadderRung.lean` **0**,
`DeTurckRemainderPrincipalArmOpNorm.lean` **0**.  Focused check of
`LowRegLadderRung.lean`: clean in 20.3 s with **zero warnings**.  No
`maxHeartbeats` added anywhere.

### Shape ruling for `a1_ladder`: **κ-FREE**, as the dispatch preferred

The reconciliation resolves against the PLAN4-tail κ-form, and structurally,
not by taste:

* `A.a1 W = appCc g 2 2 A.C0 W + appCc g 3 2 A.C1 (∇W)`.  The `C1` arm is the
  top slot and sits at order **one**, so the honest top norm is `H^{m+1}`.  The
  proposed `+1 / +0` pair would have put the small constant on `H^{m+1}` and the
  lower one on `H^m` — i.e. it would have claimed the *whole* `a₁` arm is small.
* No smallness exists to claim.  `lowData_split` caps only `A.C2`
  (`K·δ/(1−δ)²`); the C0/C1 towers give jet control with `R₀`-dependent
  constants, never a `δ`-small fibre cap.  A κ-form would have been an
  over-claim, not a stronger theorem.
* The hierarchy wants exactly **one** small constant and it lives on `a₂`.

Landed statement (`LowRegLadderRung.lean:407`):

```text
a1_ladder (hDim : finrank ℝ E = 3) (g₀) (a) (ha : 2 ≤ a) {R₀} (hR₀)
    {δ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1/3) :
  ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
    ∀ T (hT : symmetry) (hδg) (hδZ),
      ‖smoothCcToTensorHs g₀ ((a:ℝ)+2) T‖ ≤ R₀ →
      ∀ m, ‖smoothCcToTensorHs g₀ (m:ℝ) ((lowBaseData g₀ g₀ T … ).a1 T)‖
             ≤ Clower m * ‖smoothCcToTensorHs g₀ ((m:ℝ)+1) T‖
```

and A1d (`:542`):

```text
n_diff_hm_rung (hDim) (g₀) (a) (ha : 3 ≤ a) {R₀} (hR₀) {δ} (hδ0) (hδ_le) :
  ∃ (κ : ℝ) (Clower : ℕ → ℝ), 0 ≤ κ ∧ (∀ m, 0 ≤ Clower m) ∧
    ∀ T (hT) (hδg) (hδZ), ‖T‖_{H^{a+2}} ≤ R₀ → ∀ m,
      ‖N T − N 0‖_{H^m} ≤ κ*(δ/(1−δ)^2)*‖T‖_{H^{m+2}} + Clower m*‖T‖_{H^{m+1}}
```

with `N = deTurckSmoothRemainder g₀ g₀ ·`.  The proof is exactly what §7.3 row
E0e predicted: `rw [lowData_split.1, smoothCcToTensorHs_add]` then
`norm_add_le` over `a2_ladder` and `a1_ladder`, `Clower m := C2low m + C1low m`,
`κ` inherited unchanged.  **E0e is done.**

### Correction to the dispatch: the gate is `2 ≤ a`, not `1 ≤ a`

`1 ≤ a` is the *towers'* gate (`c0_jet_tower`), and it only buys `H^{a+2} ↪ C¹`
for the state.  The ladder additionally has to keep the **coefficient's**
Sobolev jet window inside the a-priori ball.  Binding case, dimension three:
`q = 1, m = 1` needs `∇³ C₁`, whose tower window reaches `‖T‖_{H⁴}`, hence
`a ≥ 2`.  Sharp for this route.  Harmless: `a2_ladder` already demands `3 ≤ a`,
so `n_diff_hm_rung` carries `3 ≤ a` and nothing downstream sees the difference.

### The one non-routine part: the engine advertised `16 ≤ a`, and it was an artefact

A1c was billed routine, and the assembly was; the obstacle was upstream.  The
order-generic **first-order** jet-window engine
`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le`
(`DeTurckRemainderPrincipalArmOpNorm.lean:4660`) carried
`ha_super : 2 * finrank ℝ E + 10 ≤ a` — exactly the `16 ≤ a` inheritance
`A1CUR_PLAN.md:283` told us to refuse, which would have put the whole
hierarchy's a-priori ball at `H^18`.

`ha_super` was **textually dead** in `…_of_lowOrder` and entered
`…_of_highOrder` through **two `omega`s only**, both about a hard-wired band
split rather than about `a`.  The honest requirements are: low half
`q + finrank/2 ≤ a` (coefficient Sobolev window inside the ball); high half
`finrank/2 + m ≤ q` (data sup-window inside the output window) plus
`finrank/2 ≤ a`.  Re-splitting at `finrank/2 + m` makes the halves exhaustive at
`2 * (finrank ℝ E / 2) ≤ a`.  Ten edited lines, one 267 s module build, gate
`16 → 2`.

Cost measure taken first, as mandated: the module has **3 direct importers**
(`DeTurckRemainderRealizeBallUniformSplit`, `LowRegLadderRung`,
`ShortTime/LowRegRemainderH0`) and **no external caller** of the three
declarations; the single internal consumer at `:4768` keeps its own `ha_super`
and now passes the weaker gate by `omega`.  Full record in the new
`DeTurckRemainderPrincipalArmOpNorm.md`.

**This is the 6th exhibit of the over-count pattern, in its dual form.**  The
first five were "a wall that already had a public wrapper".  This one is "a
hypothesis that is advertised but never used".  Same one-line diagnostic:
`grep -c ha_super` over the two proof bodies returned **zero**.  Standing rule
extended: *before accepting an advertised derivative budget, check whether the
binder is actually used.*

### New private helper

`coeffCap` (`LowRegLadderRung.lean:308`) manufactures the engine's uniform
pointwise fibre cap for the first-order coefficients from tower + ball
(supercritical Sobolev needs only `∇ʲ C`, `j ≤ finrank/2 + 1`).  For `a₂` that
cap is `lowData_split`'s smallness clause; for `a₁` no smallness exists, so the
helper produces a merely-existing cap.  `hR₀ : 0 ≤ R₀` turned out not to be
needed and was dropped (weakest-assumptions rule).

### Files

`Analysis/Spectral/Intrinsic/DeTurck/LowRegLadderRung.lean` 294 → **586 lines**
(one import added; `coeffCap` + `a1_ladder` + `n_diff_hm_rung`), and its `.md`
extended; `Analysis/Spectral/Intrinsic/DeTurck/DeTurckRemainderPrincipalArmOpNorm.lean`
re-gated (~10 lines) with a **new** same-name `.md`; `ScratchC01Census.lean`
extended by one import and five `#print axioms`.  Nothing else touched; every
read-only file respected.

### Tooling note

The first engine build was **killed by the memory guard at 232 s** (physical
free memory dipped to 0.386 GB under the parallel job fan-out) — a kill, not a
proof failure.  The retry, with the 9538 upstream jobs already built and nothing
competing, passed in 267 s.  Worth remembering: for a heavy single-module
rebuild, let the fan-out finish (or fail) first, then re-run the one module
alone.

### Honest denominators

* **A1c `a1_ladder`: 0% → 100%.  A1d `n_diff_hm_rung`: 0% → 100%.**
* **F6 ≈ 88% → ≈ 92%.**  The estimate chain was already closed; now the ladder
  layer on top of it is closed too.  What remains in F6 is **only** the
  P-STOP-gated Galerkin lane (E1′/E4/G4/Z toward `lowreg_spatialMass`) — that is
  the whole remaining ~8%, and it is plumbing-plus-analysis, not estimate work.
* Front 2 ≈ 62% → ≈ **64%**.  Machinery ≈ **97%** (unchanged; the re-gating
  widened an existing engine, it did not add one).
* **(N) `ricci_flow_unif_existence`: 0%.**  Still stated-and-unproved at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  Nothing this
  session moved it.  A complete, sharp, axiom-clean dissipation ladder is an
  *input* to (N), not a part of it.
* Whole HCG compactness project: low single digits.
* Route-error counter: **0/3** — no failed route.  One statement *shape* was
  decided (κ-free) and one upstream gate corrected (`16 → 2`); neither is a
  route error, and no existing public statement was weakened.

### Next target

The Galerkin lane, entry `P-STOP §6.1`: brick **E1′**, wiring
`n_diff_hm_rung` into `lowreg_spatialMass`.  It now has its full ladder input.
Consumers should read the ladder shape as: **one** small constant
`κ·δ/(1−δ)²` multiplying `‖T‖_{H^{m+2}}`, everything else on
`Clower m·‖T‖_{H^{m+1}}`, gate `3 ≤ a`, ball `H^{a+2}`, all uniform in the rung
`m`; and `a1_ladder` separately if only the first-order arm is wanted
(κ-free, `‖T‖_{H^{m+1}}`, gate `2 ≤ a`).

## Planner update No. 127 (2026-08-04) - A1c/A1d ACCEPTED: F6 LADDER LAYER COMPLETE; [B3-B5 FLOOR] + [P-STOP FINAL AUDIT] DISPATCHED IN PARALLEL

Acceptance: `a1_ladder` (:407) and `n_diff_hm_rung` (:542) proved
first-try, census-clean (9620-job build, zero sorryAx, zero textual
sorry in both files; downstream 9788-job confirmation green).

Two executor rulings RATIFIED:
- **κ-FREE `a1_ladder`** — the PLAN4-tail κ-form was MATHEMATICALLY
  WRONG for this arm (it would have claimed the whole a₁ arm δ-small;
  `lowData_split` caps only `A.C2`, and the C0/C1 towers give
  R₀-dependent constants, never a δ-small fibre cap).  The hierarchy
  needs exactly ONE small constant and it lives on a₂.  The honest
  form `‖a1 T‖_{H^m} ≤ Clower m·‖T‖_{H^{m+1}}` matches the №111-era
  consumer signature.  (A plan-file shape corrected before landing —
  not a route error.)
- **Gate `2 ≤ a`, not 1** — the towers' `1 ≤ a` buys only the state's
  `H^{a+2} ↪ C¹`; the LADDER additionally needs the coefficient's jet
  window inside the ball (binding case q = 1, m = 1 reaches
  `‖T‖_{H⁴}`).  Sharp, harmless under a2's `3 ≤ a`.

OVER-COUNT EXHIBIT SIX (dual form — "a hypothesis advertised and
never used"): the first-order engine
`exists_appCc_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le`
(`DeTurckRemainderPrincipalArmOpNorm.lean:4660`) advertised
`2·finrank+10 ≤ a` (= 16); `ha_super` was textually DEAD in the low
half and entered the high half only through two `omega`s about a
hard-wired band split.  Re-split at `finrank/2 + m` ⟹ gate 16 → 2 in
ten lines (cost-measured: 3 importers, no external callers of the
three re-gated declarations).  E0e (`n_diff_hm_rung`) is exactly
§7.3's predicted one-`norm_add_le` assembly; κ inherited from a₂
alone.

DISPATCHED IN PARALLEL: [B3-B5] (Lean slot — delete the `Kf`
conjunct + `lowregFloorHorizon`, cap `P` against the engine's
`1/(2C)`, rewire the endpoint through `norm_le_of_ae_le`; success =
grep-proof that order-2 `staticForce` leaves every horizon/radius
formula — the sole recorded failure mode is the cap arithmetic) and
[P-STOP FINAL AUDIT] (read-only — §6.1(a)/(b) Lean-hypothesis reads,
§7 identification audit against the uniqueness chain, ladder-shape
consistency, ending in a §10 PASS/PASS-WITH-ADAPTERS/FAIL verdict
that gates the whole Galerkin lane).

Honest denominators: A1c/A1d 100%; **F6 ≈ 92%** (remaining = the
Galerkin lane only); front 2 ≈ 64%; machinery ≈ 97%; (N) 0% (stated
at `Evolution/ExtendViaUniqueness.lean:80`, sorry :98); whole HCG
project low single digits.  Route-error counter: 0/3.

---

## Auditor report — P-STOP FINAL AUDIT (2026-08-04, read-only)

**VERDICT: PASSED-WITH-ADAPTERS.  The Galerkin lane may be built — but it
is a much smaller lane than scoped, and two of its planned bricks should be
deleted rather than implemented.**  Full record in `PSTOP_PROPOSITION.md`
(now v4, §6.2 / §6.3 / §7 / §8 / §9 / §10).  No Lean was run and no `.lean`
file was touched.

### The three target verdicts

**(a) The MR engine accepts projected forcing: VERBATIM-APPLICABLE.**  The
forcing slot is a bare `timeL2 (tensorHs g r s a) T` throughout
(`maxRegDuhamelSolField` / `maxRegDuhamelMap`, `SolutionSpace.lean:582/:613`);
the only side hypotheses in the family are `0 < T`, `T <= 1` and
`IsCompactOperator (tensorResolventL2 g r s)` — background facts, not
structure on the forcing.  Constants are forcing-generic
(`maximalRegularityOp_norm_le` <= 2, `maximalRegularitySolField_norm_le`
<= (1+T)).  And `Pi_N` on exactly that space ALREADY EXISTS as a CLM:
`timeL2EigenProj` (`HeatSemigroup/TimeL2EigenProjection.lean:189`) with
`norm_timeL2EigenProj_le_one` and — decisive for §7 —
`timeL2EigenProj_tendsto`.  No adapter.

**(b) The A1 Lipschitz input: REUSABLE-AS-STATED, and stronger than v3
assumed.**  The A1 solve is `partial_sol_const`
(`TensorMaximalRegularity/PartialForcingFixedPoint.lean:195`), whose
nonlinearity data are four explicit hypothesis SLOTS (`hLip`, `hsingle`,
`hzero : ‖Nfun 0‖ <= D`, `hsmall : C1*R <= 1/8`) on the ball-restricted
`Nfun : lowerState g0 a R -> H^a`, returning a CLOSED-FORM horizon
`T0 = min 1 (min (1/(64(C2+1)^2)) ((R/4)/(2(D+1)))^2)`.  Nothing is fused
into the proof.  Consequence: `Pi_N o Nfun` satisfies all four with the
SAME `L, C1, C2, D`, so `partial_sol_const` returns the SAME `T0` and the
same `R/4` forcing radius for the projected system.  §6.1's "same radius,
same horizon, N-free" is not an analogy — it is the identical closed
formula in identical inputs.

**(c) Identification: RESOLVED, and the compactness+uniqueness route is not
needed.**  With (b), the projected and unprojected trajectories are fixed
points of maps differing only by `Pi_N`, inside one contraction with
`Lambda <= 1/2` (forced by `partial_sol_const`'s own hypotheses).  Hence
`‖f_N - f_*‖ <= (1-Lambda)^{-1} ‖(Pi_N - 1) Phi(f_*)‖ -> 0` by
`timeL2EigenProj_tendsto`.  The limit IS the A1 fixed point by
construction — no Aubin–Lions, no weak-* extraction, no diagonal
subsequence, no uniqueness theorem.  R-4's "weakest link" dissolves.

A master uniqueness theorem does exist and is proved and used —
`deTurckStrong_unique` (`DeTurck/StrongSolutionUniqueness.lean:90`, callers
at `EdgeStrongData.lean:296`, `SmoothStrongPair.lean:715`), explicitly for
independently supplied pairs.  Its structural hypotheses all MATCH the
Galerkin limit (zero trace, a.e. `timeL2` PDE identity, scale link,
Nemytskii identity, force ball, and `hsingle` = exactly what
`c0Diff_tame` / `bg0_pair_h1` / `a1Sub_lo_tame` produce).  ONE MISMATCH: it
demands a GLOBAL `LipschitzWith L Nfun : H^{a+2} -> H^a`, while the low-reg
nonlinearity is `lowRegN : lowerState g0 1 R -> H^1`, a `Dense.extend` on a
ball subtype.  Recorded as the fallback, not the route.

### The one substantive correction to §6.1

§6.1(ii) claimed `‖U_N‖_{C_tH3 cap L2_tH4} <= B3`.  **Not available.**  The
A1 solve runs at `a = 1`: forcing `L2_tH1` with `‖gforce‖ <= R/4`, field
`L2_tH3` with `‖field‖ <= (1+T)‖gforce‖`.  There is no `L2_tH4` and no
`C_tH3` at `a = 1`; getting them needs the solve at `a = 2`, whose
`hsingle` prefactor is `max‖.‖_{H3}` — one full scale above what the
difference-tame layer delivers.

**Repair, at zero cost:** the C0 cap enters the rung-`k` Gronwall
coefficient QUADRATICALLY (R-3's `grad P . grad P` symbol), so
`A(k)(t) <= class + C‖U_N(t)‖^2_{H3}` is `L1` in `t` with
`int_0^T ‖U_N‖^2_{H3} <= ((1+T)R/4)^2` — N-free and class-uniform.
Gronwall with an `L1_t` coefficient is standard and restricts `T` not at
all.  Every one of Pro's six requirements survives; only `C_tH3` becomes
`L2_tH3`.

### Ladder-shape consistency, and the one open number

§3's arithmetic uses exactly `n_diff_hm_rung`'s landed shape — no mismatch.
§6.1's tower-direct pairing converts to the spectral `H^k` pairing through
bridges that exist in BOTH directions at
`SobolevScale/IteratedCovGradHsJetBound.lean`: `hsJet_le` (`:834`), its
rank-(0,2) form `exists_iteratedCovGrad_sum_le_smoothCcToTensorHs` (`:1021`),
and `hs_le_jet` (`:855`); `lowJetSq` differs from their jet sum by a finite
Cauchy–Schwarz.  All are on `SmoothCcTensor`, and by `finiteEigenComboHs_eq`
(`DeTurckRemainderDefs.lean:119`) Galerkin states ARE smooth cc tensors — so
the towers and the difference-tame layer apply to them directly.  (An
advantage v3 did not record: the approximants are smooth, while the A1
trajectory itself is only `H3`, which is why `lowRegN` had to be a
`Dense.extend`.)

Budget check: at rung `k` the towers' `range (i+2)` window at `i = k-1`
reaches state jets `<= k`, i.e. inside `E_{<=k}` — the coefficient side is
triangular with margin; the a2 arm supplies the single `‖U‖_{H^{k+1}}`
absorbed by the delta*-margin.  §6.1's "coefficient jets <= k+1" was
pessimistic; the true window is `<= k`.

OPEN NUMBER (R-5's, now localized to a binder): `a2_ladder` (`:233`) and
`n_diff_hm_rung` (`:542`) bind `{delta}` BEFORE `exists kappa`, so as stated
`kappa` may depend on `delta` and the choice
`delta* = min{1/3, delta_abs(kappa)}` is formally circular.  Not circular in
substance: `kappa` is inherited unchanged from `lowData_split`
(`DeTurckRemainderLowBaseAction.lean:3841`), whose
`exists K, 0 <= K and forall T ... {delta} ...` puts `K` BEFORE `delta`.
A2-ABS is a binder hoist, not new mathematics — but it is REQUIRED before
absorption is certified.

### Adapter list (the whole remaining Galerkin lane)

* **A — `Pi_N` commutes with the Duhamel family**, modewise, from
  `maximalRegularitySolField_timeModeCoeff` (`MaximalRegularity/Operator.lean:491`)
  and `solModeCoeff` (`:88`, a function of mode `i` alone).  Makes the
  projected trajectory `V_N`-valued, so the energy identity is legitimate.
  **The only load-bearing adapter.**
* **B — `Pi_N o Nfun` inherits `partial_sol_const`'s four slots** with the
  same constants; one line each from `norm_spatialEigenProj_apply_le`.  Tiny.
* **C — fixed-point stability** (the §7 estimate), over `nemytskiiOn_mixed`
  (`PartialForcingFixedPoint.lean:96`), `maxRegDuhamelSolField_dist_le`
  (`ForcingFixedPoint.lean:282`) and `timeL2EigenProj_tendsto`.  Belongs to
  A2 / G-2 adapter 2.  Small.
* **D — A2-ABS**, the `kappa` binder hoist above.  Required.
* **E — C0 tower instantiated at `a = 1`** (ball `H3`).  If `selfLow_jet` is
  threaded at `a = 3`, re-cut the surgery to the `H3` cap.
* **F — paper-side only:** §6.1(ii) reads `L2_tH3`; rung Gronwall runs with
  an `L1_t` coefficient.  Already applied in `PSTOP_PROPOSITION.md`.

### Lane changes (act on these)

* **E4 (Galerkin ODE existence): DELETE.**  There is no ODE to construct;
  the projected trajectory is a `partial_sol_const` output.
* **G4 (compactness / uniqueness plumbing): DELETE.**  Replaced by adapter C.
* **E1'a, the first brick, should be told:** build adapter A, not a Galerkin
  ODE.  It is upstream of B and C and belongs in
  `Spectral/Intrinsic/HeatSemigroup/TimeL2EigenProjection.lean` (where the
  projector already lives), **not** in `ShortTime/`.

### Honest denominators

* **P-STOP (paper): ~55% -> ~90%.**  Remaining ~10% = A2-ABS, plus the fact
  that rungs 3–5 were checked at jet-WINDOW / ladder-shape level rather than
  written out as a displayed derivation.
* **This audit moved no Lean.**  P-STOP is a gate, not a brick.
* **F6 ~92%** (unchanged by paper work; the remaining ~8% is now A/B/C
  instead of E1'/E4/G4/Z).  Front 2 ~64%; machinery ~97%.
* **(N) `ricci_flow_unif_existence`: 0%.**  Stated-and-unproved at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  A passing
  P-STOP does not move it by one line.
* Whole HCG compactness project: low single digits.
* Route-error counter: 0/3.  No stop signal from RULING2 §(ii) fired.

## Planner update No. 128 (2026-08-04) - P-STOP PASSED-WITH-ADAPTERS: GALERKIN GATE OPEN, LANE RE-SCOPED (E4/G4 DELETED)

The P-STOP final audit is ACCEPTED (planner spot-check: the two
load-bearing anchors exist at the claimed locations —
`timeL2EigenProj` `HeatSemigroup/TimeL2EigenProjection.lean:189`,
`partial_sol_const` `PartialForcingFixedPoint.lean:195`).
`PSTOP_PROPOSITION.md` is now v4, status CLOSED — PASSED-WITH-
ADAPTERS.  The Pro-mandated gate (RULING2 item (i)) is OPEN.

The three audit verdicts:
(a) the MR engine's forcing slot is a bare `timeL2` — `Π_N f`
qualifies VERBATIM, and the projector already exists as a norm-≤1 CLM
with a convergence lemma;
(b) the A1 solve `partial_sol_const` has four explicit hypothesis
slots and a CLOSED-FORM horizon `T₀` — `Π_N ∘ Nfun` satisfies all
four with the SAME constants ⟹ literally the same `T₀` (the §6.1
"same radius, same horizon, N-free" is an identity, not an analogy);
(c) IDENTIFICATION NEEDS NO COMPACTNESS OR UNIQUENESS: both
trajectories are fixed points of maps differing only by `Π_N` inside
ONE contraction with `Λ ≤ 1/2`, so
`‖f_N − f_*‖ ≤ (1−Λ)⁻¹·‖(Π_N − 1)Φ(f_*)‖ → 0` by the projector
convergence lemma.  Aubin–Lions, diagonal extraction, and the
uniqueness theorem all DROP OUT of the design (`deTurckStrong_unique`
recorded as fallback only, with its one hypothesis mismatch noted).

One substantive §6.1 correction absorbed at zero cost: the A1 solve
runs at a = 1, so the C_tH³ bound of v3 is not available as stated;
but the C0 cap enters the Grönwall coefficient QUADRATICALLY, so
`A(k)(t) ≲ class + C·‖U_N(t)‖²_{H³}` is L¹ in t with a class bound on
its integral — Grönwall with an L¹ₜ coefficient restricts T not at
all.  All six Pro requirements survive.

LANE RE-SCOPE (the operative consequence): **E4 (Galerkin ODE) and
G4 (compactness/uniqueness plumbing) are DELETED from the queue** —
not deferred, deleted; the remaining Galerkin lane is the adapter
list: **A** (Π_N commutes with the Duhamel family, modewise — the
only load-bearing one; home `TimeL2EigenProjection.lean`, NOT
`ShortTime/`), **B** (the four solve slots project — one line each),
**C** (fixed-point stability = the §7 identification), **D = A2-ABS**
(binder hoist: `{δ}` currently binds before `∃κ` in
`a2_ladder`/`n_diff_hm_rung`, making `δ* = δ_abs(κ)` formally
circular; κ is in substance `lowData_split`'s δ-free `K` — hoist and
certify the absorption), **E** (instantiate the C0 tower at a = 1).
Then E1′ (the hierarchy wiring into `lowreg_spatialMass`) and Z.

Queue: [in flight: B3–B5 floor completion] → [adapters A+B+D (one
brick)] → [C + E1′ wiring] → [Z: `lowreg_spatialMass` assembly] →
A4/endpoint wiring → front-3 transport audit → PHASE-C → (N)
assembly.  P-STOP ≈ 90% (remaining: A2-ABS certification + the
rung-3..5 displayed derivation, both folded into the bricks).

Honest denominators: F6 ≈ 92%; front 2 ≈ 64%; machinery ≈ 97%;
(N) 0% (stated, sorry :98); whole HCG project low single digits.
Route-error counter: 0/3.

---

## Executor report — floor bricks B3 + B4 + B5 (2026-08-04)

**Verdict: GREEN, all three bricks.  Option (b) is COMPLETE.**  The
`√T‖fHi‖ ≤ Kf` machinery and `lowregFloorHorizon` are deleted; the
order-2 static force is out of every horizon/radius formula; the
joint-smoothness engine is fed by the STATE bound.  No `sorry` added,
no `sorry` removed, no public endpoint statement broken
(`lowreg_joint_two`'s signature is byte-identical).

**The one identified failure mode did not fire.**  No. 109 recorded
B3/B4's `P`-cap arithmetic as the sole surviving way for the design to
fail.  It composed exactly as §6 predicted, in five lines.

### B3 — the conjunct is gone

`IsRealizedTwo`'s parameter `Kf` → `Rcap`; its last conjunct
`Real.sqrt T * ‖fHi‖ ≤ Kf` → **`R ≤ Rcap`**.  Final conjunct list
(unchanged except the last): … `hFComm`, then
`(∀ᵐ t ∂timeMeasure T, ‖u.lo.toFun t‖ ≤ R) ∧ R ≤ Rcap`.

Deleted: `lowregFloorHorizon`, `lowregFloorHorizon_pos`, and the two
privates that existed only to feed them — `nonautL2Map_zero` and the
Neumann bound `norm_fix_le` (75 lines).  `lowreg_apply_two` swaps
`hTfloor` for `hRcap : R ≤ Rcap` in the same slot and forwards it.
Scouted before deleting: both privates were file-local with the single
`hfloorHi` consumer; `norm_liftForceHi_le` is upstream API and stays.

### B4 — the exact cap inequality

```lean
set P : ℝ := min (min (min ρ ρN) ((1 - c) / (6 * (L + 1)))) Rcap
have hPcap : P ≤ Rcap := min_le_right _ _
-- discharges IsRealizedTwo's new conjunct:
hRP.trans hPcap : lowregStateRad Ctop B1 ρout P ≤ P ≤ Rcap
```

`lowreg_solve_two` now takes `{Rcap} (hRcap : 0 < Rcap)`; `hPpos`
gains one `lt_min` against `hRcap`, each `hP*` gains one `le_trans`,
and the reported `T₀` drops its third factor back to
`min (lowregHorizon Ctop B0 B1 D ρout P) (lowregLiftHorizon' c Z)`.
The `hmargin` chain is untouched: it reads `P` only through `hPc`.

### B5 — the endpoint reads the state, not the derivative

`lowreg_allOrderJet`'s last conclusion conjunct is now
`∀ t ∈ Icc 0 T, ‖timeH1.toFun u t‖ ≤ Rcap`, produced in three lines
from `hballU` + the new cap through B2's `timeH1.norm_le_of_ae_le`.
`lowreg_joint_smooth`'s slot `hfloor : √T‖u.deriv‖ ≤ 1/(2C)` became
`hstate : ∀ t ∈ Icc 0 T, ‖timeH1.toFun u t‖ ≤ 1/(2C)`, passed straight
to the engine — the B1 shim `u.state_le_of_sqrt_floor hinit hfloor` is
gone, and so is the ~30-line `‖u.deriv‖ ≤ 2‖fHi‖` derivation in
`lowreg_joint_of_re`.  `lowreg_joint_two` instantiates
`Rcap := 1/(2C)`, **not** `1/(4C)`: the factor 2 was the derivative
proxy's cost and there is no proxy now.  `state_le_of_sqrt_floor`
stays as public `timeH1` API (no campaign caller).

### Grep-proof

* `lowregFloorHorizon`: **zero** `.lean` occurrences repo-wide.
* `staticForce`: **zero** occurrences in `LowRegApplyTwo.lean` and
  `LowRegAllOrderJet.lean`.
* `‖staticForce … 2‖` survives in exactly ONE place tree-wide — the
  hypothesis variable `hD` of `norm_liftForceHi_le`
  (`LowRegLiftNTerm.lean:260`), which now has **no consumers**.  Unused
  API, not a horizon.
* `staticForce … 2` as an OBJECT survives at `LowRegForceHi.lean:144,
  215, 284` (the frozen split `liftHiN` and its inclusion naturality).
  The high forcing still *contains* the static field; nothing bounds
  its norm any more.  That is the intended end state (§9 of the plan).

### Census

Targeted builds GREEN: `LowRegApplyTwo` [9984/9984],
`LowRegAllOrderJet` [9985/9985] (first try).  `#print axioms`:

* `lowreg_joint_smooth`, `lowreg_apply_two`, `lowreg_solve_two`:
  `[propext, Classical.choice, Quot.sound]` — **`sorryAx`-free**;
* `lowreg_forceJetMass`, `lowreg_allOrderJet`, `lowreg_joint_of_re`,
  `lowreg_joint_two`: `sorryAx` **only** through `lowreg_spatialMass`.

Campaign sorry census **unchanged**: exactly `lowreg_spatialMass`
(`LowRegAllOrderJet.lean:1047`, `sorry` at `:1088`) + (N) itself.
Zero textual `sorry` in `LowRegApplyTwo.lean`.

### For front 3's constant-exposure sweep

* Item **(C)1 is now DISSOLVED IN LEAN**, not merely in design.  `τ₀`
  is closed in `(Ctop, B0, B1, D, ρ, P, C)`; `D` is the ORDER-1 force
  number already class-bounded via `staticN_h1_le → nZero_unif` with
  producer `unifKsupLeOne` (hypotheses at orders 1–3 only).  No
  `unifKsupLeTwo` is needed; G5's ruling is moot.
  `FRONT3_ASSEMBLY_PLAN.md` §140 and its `:86` `T₀` row are now stale
  and should be re-pointed.
* The residual is unchanged and is now the ONLY individual constant in
  the horizon: `C` = `(hs2_opBound_at_two hDim g).choose`, opaque.
  Brick G3's swap to `hs2_op_bound_unif` (`H2PointwiseUnif.lean:278`)
  is what closes it.  Note the cap level moved from `1/(4C)` to
  `1/(2C)` — G3 should exchange the constant at
  `LowRegAllOrderJet.lean` (`lowreg_joint_of_re`'s `hRcapC` and
  `lowreg_joint_two`'s `Rcap :=`), two sites, both now stated against
  `2 * C`.

### Tooling note for the next Lean executor

The prescribed memory guard (`FreePhysicalMemory < 0.4 GB` → kill
lean) is BELOW this machine's normal working point for the heavy
modules and aborted three otherwise-fine builds.
`DeTurckRemainderLowBaseLip` completes in 239 s while sitting at
0.30 GB physical free; `FreeVirtualMemory` — the actual
commit/OOM predictor — never dropped below 5.2 GB in any run.
Keeping the commit limb hard (`< 3 GB`) and debouncing the physical
limb (or lowering it to a true thrash floor) is what let the builds
finish.  Also: the tree needed ~9600 upstream jobs rebuilt from
missing `.olean`s before either target file could even be checked.

### Honest denominators

Option (b): **5/5 bricks, 100%** — but it is a DELETION; its own
new-mathematics content is ~0%.  What it buys is structural: one of
front 3's ~8 items closed, and the horizon's order-4 dependency gone.
Front 2 ≈ 66% (the floor lane is finished; the frontier is still
`lowreg_spatialMass` + `hRepr`).  F6 ≈ 92%, machinery ≈ 97%,
both unchanged by a deletion.  **(N) `ricci_flow_unif_existence`:
stated at `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`,
proof 0%.**  Whole HCG compactness project: low single digits.

## Planner update No. 129 (2026-08-04) - B3-B5 ACCEPTED: OPTION (b) COMPLETE (5/5); GUARD PROTOCOL AMENDED; ADAPTERS A+B+D DISPATCHED

Acceptance: all three floor bricks GREEN first-try (targeted builds
9984/9985 jobs).  **The user's No. 99 ruling (option (b)) is now
FULLY REALIZED in Lean**: `lowregFloorHorizon` has zero repo-wide
occurrences; the `Kf` conjunct of `IsRealizedTwo` is replaced by
`R ≤ Rcap`; the `P`-cap composed in five lines (`P := min (min (min
ρ ρN) ((1−c)/(6(L+1)))) Rcap` — the sole No. 109-recorded failure
mode never fired); the endpoint runs `hballU → norm_le_of_ae_le →
hstate` with `Rcap := 1/(2C)` — a factor 2 BETTER than the plan's
1/(4C), since the lost factor was the derivative proxy's cost and
the proxy is gone.  Order-2 `staticForce` survives only as (i) the
hypothesis variable of the now-consumerless `norm_liftForceHi_le`
and (ii) the frozen object inside `liftHiN` with nothing bounding
its norm — the intended end state.  Deleted en route:
`norm_fix_le`, `nonautL2Map_zero` (scouted file-local).  Campaign
census unchanged (`lowreg_spatialMass` + (N)).

Front-3 consequences recorded: item (C)1 dissolved IN LEAN — τ₀ is
closed in `(Ctop, B0, B1, D, ρ, P, C)` with `D` the ORDER-1 force
number; `unifKsupLeTwo` unneeded, G5 moot; G3's constant-exposure
swap now has exactly two call sites, both against `2·C`.
`FRONT3_ASSEMBLY_PLAN.md` rows are stale (flagged as follow-up).

**GUARD PROTOCOL AMENDED** (empirical, from this brick): the COMMIT
limb (< 3 GB ⟹ kill) is the true OOM predictor and stays hard; the
PHYSICAL limb is DEBOUNCED (kill only if phys < 0.4 GB over two
consecutive polls AND commit also declining) — this machine sits at
~0.3 GB phys-free routinely under load while commit-free never
dropped below 5.2 GB; the old hard limb aborted three otherwise-fine
builds.  Supersedes the No. 112/116 wording.

DISPATCHED: Galerkin-lane opening brick [adapters A + B + D] per
No. 128 — A: `timeL2EigenProj` commutes with the Duhamel family
(modewise; V_N-valuedness corollary; home `HeatSemigroup/`),
B: the four `partial_sol_const` slots project with identical
constants (same closed-form `T₀`), D: the A2-ABS binder hoist on the
ladder trio (`{δ}` after the `∃`; stop-signal-8 report if any
constant genuinely depends on δ).  Then [C + E + E1′ wiring] → Z.

Honest denominators: option (b) 5/5 (a deletion — ~0% new
mathematics; what it buys is structural).  Front 2 ≈ 66%; F6 ≈ 92%;
machinery ≈ 97%; (N) 0% (stated, sorry :98); whole HCG project low
single digits.  Route-error counter: 0/3.

---

## Executor report — Galerkin-lane opening brick [adapters A + B + D] (2026-08-04)

All three adapters LANDED, sorry-free and axiom-clean.  Two new modules and
one in-place restatement; no `maxHeartbeats`, no new frontier, no `sorry`.

### A — `Π_N` commutes with the Duhamel family (the load-bearing one)

New module `Analysis/Spectral/Intrinsic/HeatSemigroup/EigenProjDuhamel.lean`
(imports `TimeL2EigenProjection` + `TensorMaximalRegularity/SolutionSpace`;
NOT in `ShortTime/`, as dispatched).  Fourteen declarations, all modewise, no
estimate anywhere:

* `spatialProj_coeff` (:70), `spatialProj_lip` (:78) — the indicator formula for
  the truncated eigen-coordinates, and `LipschitzWith 1`;
* `timeProj_modeCoeff` (:86) — the same for `timeModeCoeff` of a truncated
  time-`L²` field;
* `proj_solModeCoeff` (:115), `proj_derivModeCoeff` (:131),
  `proj_homModeCoeff` (:154) — the three per-mode Duhamel coordinates;
* `proj_solField_comm` (:181), `proj_derivField_comm` (:199),
  `proj_homField_comm` (:217), `proj_duhamel_comm` (:236),
  `projDuhamel_zero` (:251) — the field-level commutations, in the exact shapes
  the engine exposes;
* `proj_maxRegOp_deriv` (:267) — the map level;
* `projSol_mode_zero` (:284), `projSol_fixed` (:299) — the `V_N`-valuedness.

The two load-bearing statements, verbatim:

    maximalRegularitySolField a hT (P_N^a f) = P_N^{a+2} (maximalRegularitySolField a hT f)
    maxRegDuhamelSolField a hT hT1 0 (P_N^a f) = P_N^{a+2} (maxRegDuhamelSolField a hT hT1 0 f)

with `P_N^s := timeL2EigenProj g s T N`; note the truncation on the right acts
at the **gained** regularity `a+2`.  The `V_N` corollary the §1 energy identity
consumes has the exact shape

    i ∉ eigenIdxFinset g N → timeModeCoeff (maximalRegularitySolField a hT (P_N^a f)) i = 0

and its operator form `P_N^{a+2} (solve (P_N^a f)) = solve (P_N^a f)`.

Route as dispatched: `solModeCoeff` / `maximalRegularitySolField_timeModeCoeff`
make the solve mode-diagonal, `timeProj_modeCoeff` makes the truncation
diagonal, `timeModeCoeff_injective` closes.  The structural template already
existed — `ShortTime/LowRegSymmPreserve.lean`'s `symmHs_solField_comm` /
`symmHs_duhamel_comm` do exactly this for the block-diagonal symmetrizer; the
projector case is strictly easier.  Nothing was reproved.

Layering note: `spatialProj_coeff` / `spatialProj_lip` belong beside
`spatialEigenProj` in `TimeL2EigenProjection.lean`.  They are parked in the new
module instead because that file has a live downstream chain
(`GalerkinForcingTimeL2Limit` -> `GalerkinLimitUniformMass` ->
`ForcingCoordinateTimeRegularity`, `LowRegAllOrderJet`) and `LowRegAllOrderJet`
is another lane's in-flight file.  Neither is `@[simp]`, so the move is a pure
cut-and-paste whenever that chain is quiet.

### B — the four `partial_sol_const` slots project (green first try)

New module `…/HeatSemigroup/EigenProjPartialSol.lean`: `projNfun` (:53),
`projN_lip` (:61), `projN_zero` (:71), `projN_single` (:83),
`proj_partial_sol` (:124).  Each slot is one line from the projector's norm
bound.  The capstone is written out in full rather than as a corollary, so that
the horizon is visibly the identical closed form

    T0 = min 1 (min (1/(64(C2+1)^2)) ((R/4)/(2(D+1)))^2)

with the same forcing radius `R/4`, the same constants `L, C1, C2, D`, and no
`N` anywhere.  The §6.1 "same radius, same horizon, `N`-free" is now an identity
in Lean.

Home: the bridge module, not beside `partial_sol_const` — pushing the projector
import down into `Analysis/Parabolic/QuasiLinear/` would invert the existing
layering.  It is also where C wants to live: `nemytskiiOn_mixed`,
`maxRegDuhamelSolField_dist_le` and `timeL2EigenProj_tendsto` are all in scope
in that file.

### D — A2-ABS: `κ` hoisted; `Clower` genuinely δ-dependent (NOT a stop signal)

`DeTurck/LowRegLadderRung.lean`, restated in place (no `'`-variants needed:
`n_diff_hm_rung` is the only consumer of the other two, nothing consumes
`n_diff_hm_rung`, and `ScratchC01Census.lean` only `#print axioms` them):

* `a1_ladder` — **fully hoisted**, everything δ-free:
  `∃ Clower, (∀ m, 0 ≤ Clower m) ∧ ∀ {δ} (hδ0) (hδ_le) (T) (hT) (hδg) (hδZ), ball → ∀ m, …`
* `a2_ladder` — **κ hoisted, `Clower` not**:
  `∃ κ, 0 ≤ κ ∧ ∀ {δ} (hδ0) (hδ_le), ∃ Clower, (∀ m, 0 ≤ Clower m) ∧ ∀ (T) (hT) (hδg) (hδZ), ball → ∀ m, …`
* `n_diff_hm_rung` — same shape as `a2_ladder`.

New line handles: `a2_ladder` (:243), `a1_ladder` (:425),
`n_diff_hm_rung` (:565).

Both are `intro`-motion refactors; no estimate was reproved.

The absorption IS certified: `κ` is `lowData_split`'s `K`
(`DeTurckRemainderLowBaseAction.lean:3841`), whose own statement is already
`∃ K, 0 ≤ K ∧ ∀ T hT {δ} …` — δ-free by construction.  So `δ*` may now be
chosen from `κ` without circularity, which was the whole point of A2-ABS.

`Clower` could not be hoisted, and this is a real (small) API limitation, not a
mathematical one.  `Clower` is `appCc_cap_hs_le`'s `Cop`, i.e. the engine
`exists_appCc_secondCovGrad_fibreSmallCoeff_Hs_family_le` evaluated at the fibre
cap `epsC = K*δ/(1-δ)^2`; inside that engine
(`ConnLapCommutatorCoefficientTame.lean:1362`) the lower constant is
`Mbase + sum_{i<j} CEcomm i` with
`Mbase = epsC*(1+Cj0) + (Cgrad + epsC*Cj1) + epsC*Cj0 + 1` — **affine and
monotone in epsC**, the rest epsC-free.  Since `δ ≤ 1/3` gives
`δ/(1-δ)^2 ≤ 3/4`, the δ-free bound `Mbase((3/4)K) + sum CEcomm` exists
mathematically but sits behind the engine's existential.  Calling the engine at
`epsmax = (3/4)K` instead returns the top constant `(3/4)K` and kills the
absorption; rescaling the coefficient to restore the small cap multiplies its
jet-tower constant by `(epsmax/epsC)^2`, δ-dependent again.

Smallest bridge if a fully δ-free `Clower` is ever wanted (deliberately NOT done
— it is a re-proof inside another lane's 1400-line file, not a binder hoist):
`…_Hs_family_le_unif`, the same engine with `(epsmax) (hepsmax : 0 ≤ epsmax)`
bound first and `∀ epsC, 0 ≤ epsC → epsC ≤ epsmax → …` inside, proved by
evaluating `Mbase` at `epsmax` (its three `nlinarith` steps only need
`epsC ≤ epsmax` and nonnegativity).

**Ruling requested from the planner:** this is NOT a RULING2 stop-signal-8
event.  Stop-signal 8 fires when the *absorption* constant depends on δ; κ does
not.  A rung constant fixed after `δ*` is exactly the order of choices of
`PSTOP_PROPOSITION.md` §5 (δ* from κ, then the rung / exit constants).  §6.3's
"one open number κ" is now closed as a binder fact.

### Verification

Focused checks clean on all three files; targeted module builds green in
dependency order (`EigenProjDuhamel` 9227 jobs -> `EigenProjPartialSol` 9541 ->
`LowRegLadderRung` 9619).  Axiom census of all 22 new / changed public
declarations (14 + 5 + the ladder trio): `propext, Classical.choice, Quot.sound`
only — zero `sorryAx`.  No `maxHeartbeats` added; no repo file outside the three
claimed ones was touched.

Two Lean traps worth carrying (both recorded in `EigenProjDuhamel.md`):
`TensorEigenIdx` is ambiguous when both `TensorSpectral` and
`TensorHeatEquation` are open (fix: `open …TensorSpectral hiding
TensorEigenIdx`), and `if i ∈ (F : Finset (TensorEigenIdx …))` has no
`Decidable` instance, so such statements need `open scoped Classical in` placed
**above the docstring**.

### Honest denominators

* Adapters A + B are machinery for the E1′ wiring, not the endpoint.
  `lowreg_spatialMass` is untouched and stays **0% until Z**.
* (N) `ricci_flow_unif_existence`: **0%** — still stated-and-unproved at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  This brick moves
  it by zero lines.
* Galerkin lane (A–E of No. 128): A done, B done, D done (with the κ-only caveat
  above); C and E remain, then E1′.  Call the lane ~55% by adapter count — but C
  is the one with actual analysis in it, so weight accordingly.
* P-STOP's remaining ~10%: the A2-ABS half is now discharged in Lean (binder
  hoist done, absorption certifiable); the rung-3..5 displayed derivation is
  still paper-only.
* Front 2 ~67% (was ~66%); F6 ~92% unchanged (D moved no estimate);
  machinery ~97%; whole HCG compactness project: low single digits.
* Route-error counter: 0/3.

### What the next brick (C + E + the hierarchy assembly) should be told

* Build C beside B, in `EigenProjPartialSol.lean`.  Its solver-side inputs are
  now `projDuhamel_zero` and `projSol_fixed`; its map-side inputs
  (`nemytskiiOn_mixed`, `maxRegDuhamelSolField_dist_le`,
  `timeL2EigenProj_tendsto`) are already in scope there.
* `partial_sol_const` does **not** export its contraction factor
  `Lambda = C1*R*(1+T) + C2*2*sqrt T` (local `set`), so C must re-derive the
  contraction beside it — as §7 predicted.  B guarantees `f_N` and `f_*` live in
  the *same* `R/4` ball on the *same* `T0`, so one modulus covers both.
* For the fixed point's `V_N`-valuedness (needed by the energy identity at the
  *trajectory*, not just at a projected forcing): from `gforce =ae P_N(Nfun …)`
  plus idempotence of `P_N` (one `spatialProj_coeff` line, deliberately not
  stated yet, since nothing in A or B consumes it) one gets
  `P_N gforce = gforce`, and then `projDuhamel_zero` gives `field = P_N field`.
* When the hierarchy consumes the ladder, the new call shape is
  `obtain ⟨κ, hκ, h2⟩ := a2_ladder …` and then
  `obtain ⟨Clower, hC, h⟩ := h2 hδ0 hδ_le` — pick `δ*` between those two lines.
  `a1_ladder`'s constants come out before any δ at all.

## Planner update No. 130 (2026-08-04) - ADAPTERS A+B+D ACCEPTED; [C+E] DISPATCHED

Acceptance: all three adapters sorry-free and census-clean (22
declarations; builds 9227/9541/9619 green).  Highlights ratified:
- A (`EigenProjDuhamel.lean`, 14 declarations): the full commutation
  family with the exponent subtlety recorded (the projector on the
  output acts at the GAINED regularity `a+2`); `projSol_fixed` = the
  V_N-valuedness; template reuse from `LowRegSymmPreserve`.
- B (`EigenProjPartialSol.lean`): `proj_partial_sol` written IN FULL
  so the identical closed-form `T₀` and radius are VISIBLE — §6.1's
  "same radius, same horizon, N-free" is now a Lean identity.
- D: `a1_ladder` FULLY hoisted (constants before any δ);
  `a2_ladder`/`n_diff_hm_rung` hoist κ but honestly NOT `Clower`
  (genuinely δ-dependent through the engine's fibre cap
  `εC = K·δ/(1−δ)²` — affine/monotone in εC).  NOT a
  stop-signal-8 event: signal 8 concerns the ABSORPTION constant κ,
  which is `lowData_split`'s δ-FREE `K` (:3841, itself already
  `∃ K, … ∀ {δ}`), and a rung constant fixed AFTER δ* is exactly
  §5's order of choices.  The absorption is now CERTIFIED in Lean.
  (Smallest bridge if a δ-free `Clower` is ever wanted: an
  εmax-uniform variant of the Tame engine — deliberately not done.)
Two new Lean traps recorded (TensorEigenIdx ambiguity under double
open; `Decidable` for Finset membership needs `open scoped Classical`
above the docstring).

DISPATCHED: [C + E] — C the fixed-point stability
(`‖f_N − f_*‖ ≤ (1−Λ)⁻¹‖(Π_N−1)Φ(f_*)‖`, contraction re-derived
beside `partial_sol_const` since its `Λ` is a local `set`;
convergence via `timeL2EigenProj_tendsto`; field-level corollary;
the V_N-valuedness lemma), E the low-gate C0-tower instantiation
(alias-only if shapes coincide).  After [C+E] the lane is
[E1′ rung derivation + Z assembly] ONLY.

Honest denominators: Galerkin adapters 3/5 → will be 5/5 at [C+E];
`lowreg_spatialMass` 0% until Z; front 2 ≈ 67%; F6 ≈ 92%;
machinery ≈ 97%; (N) 0% (stated, sorry :98); whole HCG project low
single digits.  Route-error counter: 0/3.

---

## Executor report — Galerkin adapters [C + E] (2026-08-04)

C LANDED in full, sorry-free and axiom-clean.  E is a **no-wrapper
verdict**, with one shape mismatch that the [E1′+Z] brick must be told.
No `maxHeartbeats`, no new frontier, no `sorry`, no file outside the two
claimed ones touched.

### C — fixed-point stability (the §7 identification)

Eight new declarations in `…/HeatSemigroup/EigenProjPartialSol.lean`
(now 582 lines) plus one in `EigenProjDuhamel.lean`:

* `spatialProj_idem` (`EigenProjDuhamel.lean:82`) — idempotence of `Π_N`,
  three lines from `spatialProj_coeff` + `tensorHs.ext`.  Parked with the
  rest of the `spatialProj_*` family for the same reason adapter A gave.
* `projN_nemytskii` (:189) — the bridge that collapses the whole argument:
  `nemytskiiOn (Π_N ∘ Nfun) f hf = Π_N (nemytskiiOn Nfun f hf)`.  The
  projector acts pointwise in time, so truncating before or after the
  Nemytskii operator is the same map.
* `forceMap_dist_le` (:256) — the contraction `partial_sol_const` runs
  internally and does not export, re-derived:
  `‖Φ F − Φ F'‖ ≤ (C₁R(1+T) + C₂·2√T)·‖F − F'‖`.
  The retraction `ρt` is dropped (both fixed points sit in the `R/4` ball
  where it is the identity) and the state memberships become hypotheses,
  so no ball bound appears in the statement at all.  Inputs are exactly
  §7's three public ones.
* `lamHalf` (private, :219) — `Λ ≤ 1/2`, a quarter per arm, from
  `hsmall : C₁R ≤ 1/8` and `T ≤ 1/(64(C₂+1)²)`.  Mirrors
  `partial_sol_const`'s `harm1`/`harm2`.
* **`projFix_dist_le` (:357)** — the stability bound, verbatim:

      ‖fN − fstar‖ ≤
        (1 − ((C₁:ℝ)*R*(1+T) + (C₂:ℝ)*(2*Real.sqrt T)))⁻¹ *
          ‖timeL2EigenProj g₀ (a:ℝ) T N fstar − fstar‖

  Its hypotheses are *precisely* `partial_sol_const` / `proj_partial_sol`
  outputs — the two force-ball bounds `‖·‖ ≤ R/4` and the two a.e.
  Nemytskii identities.  The state memberships are rebuilt internally from
  the ball bounds by `field_mem_lower`, so the caller passes nothing extra.
* `projFix_le_two` (:449) — the same with the **absolute** constant `2`:
  the modulus depends on neither `N`, `T`, `R`, `C₁` nor `C₂`.
* `projFix_tendsto` (:495) — `f_N → f_*` in `timeL2`, from any bound
  `‖f_N − f_*‖ ≤ K‖Π_N f_* − f_*‖` plus `timeL2EigenProj_tendsto`.  Stated
  at a generic scale `σ` with abstract `K`, so it carries no duplicated
  hypothesis block.
* **`projField_tendsto` (:515)** — the field-level corollary:

      Tendsto (fun N => maxRegDuhamelSolField (a:ℝ) hT hT1 0 (f N)) atTop
        (𝓝 (maxRegDuhamelSolField (a:ℝ) hT hT1 0 fstar))

  via `maxRegDuhamelSolField_dist_le`'s `(1+T)` Lipschitz bound.  **The
  convergence is in the solve's own norm `L²([0,T]; H^{a+2})`, i.e. at
  `a = 1` in `L²_t H³` — NOT `C_t H³`.**  This is the E1′/Z brick's key
  input and it matches (does not repair) §6.1's corrected claim.
* `projForce_fixed` (:538), `projField_fixed` (:561) — `V_N`-valuedness at
  the *trajectory*: `gforce =ᵐ projNfun(…)` gives `Π_N gforce = gforce` by
  idempotence, and `projDuhamel_zero` then gives `Π_N field = field` at the
  gained regularity `H^{a+2}`.  Stated against an arbitrary
  `u : ℝ → lowerState g₀ a R` rather than `aeSetLift`, so
  `proj_partial_sol`'s output instantiates them directly.

The stability step in one line, for the record: with `Ψ_N f_N = f_N` and
`Ψ_N f_* = Π_N f_*` (that is `projN_nemytskii` at the unprojected fixed
point), `‖f_N − f_*‖ ≤ Λ‖f_N − f_*‖ + ‖Π_N f_* − f_*‖`, and `1 − Λ ≥ 1/2`
divides.  No compactness, no weak-* extraction, no uniqueness theorem.

### E — NO WRAPPER (verdict), plus one shape mismatch

Audited against a throwaway probe module (elaborated green, then deleted).
Three facts:

1. `c0_jet_tower` and `selfLow_jet` are **already** stated at the low gate
   `1 ≤ a`, fully parametric in `(a, R₀)`, with the ball in exactly the
   shape every ladder rung already passes through.
   `c0_jet_tower hDim g₀ 1 le_rfl hR₀` and `selfLow_jet hDim g₀ 1 le_rfl
   hR₀` elaborate as **bare applications** — verified.  A wrapper would be
   vacuous, so none was added (no-vacuous-wrappers rule).  `a1_ladder`
   already calls `c0_jet_tower … a (by omega) hR₀` this way.
2. At `a = 1` the ball order is spelled `((1:ℕ):ℝ) + 2`, and it is **not**
   transportable to the literal `3`: the scale sits in a type index, so
   `norm_num at h` leaves `↑1 + 2` untouched and the `exact` fails
   (verified).  Normalizing it would need a `tensorHs`-scale transport
   lemma — a parallel API for a cosmetic gain.  **Keep `a` symbolic in the
   E1′ rungs**; do not introduce a numeral-spelled variant.
3. **The mismatch.**  `c0_jet_tower`'s ball is a *pointwise* `H^{a+2}`
   bound on a `SmoothCcTensor` representative.  What the A1 solve exports
   at `a = 1` is (i) `∀ᵐ t, field t ∈ lowerState g₀ 1 R`, which unfolds to
   an a.e.-in-`t` **`H²`** bound (verified: `lowerState g₀ 1 R` is a ball
   in `H^{a+1}`), and (ii) `‖gforce‖ ≤ R/4`, giving `‖field‖_{L²_t H³} ≤
   (1+T)R/4`.  Neither is a uniform-in-time `H³` radius, and neither is a
   `SmoothCcTensor`.  So the tower's `R₀` must come from **class data**
   (as No. 128 said), not from the trajectory, and the smooth-representative
   realization is a separate bridge.  This is *not* a new obstruction —
   §6.1's repair already charges the `H³` trajectory norm to an `L¹_t`
   Grönwall coefficient rather than to the tower's ball — but the E1′ rung
   must not be written as if `partial_sol_const` handed it the ball.

### Verification

Focused checks clean on both edited files (one `unusedSectionVars` warning
on `projField_tendsto`, fixed in place with `omit [BoundarylessManifold I
M] in`); targeted module builds green in dependency order
(`EigenProjDuhamel` 9227 jobs → `EigenProjPartialSol` 9541).  Axiom census
of all nine new public declarations: `propext, Classical.choice,
Quot.sound` only — zero `sorryAx`.  Sorry census of both touched files: 0,
unchanged.  Both files well under the 3000-line cap (582 / 334).

### Layering debt (deliberate, one item)

`forceMap_dist_le` mentions no projector; its canonical home is beside
`nemytskiiOn_mixed` in `…/TensorMaximalRegularity/PartialForcingFixedPoint
.lean`.  It is parked in `EigenProjPartialSol.lean` because that file was
read-only for this brick (the dispatch said re-derive, don't edit).
Adapter C is its only consumer; pure cut-and-paste whenever that file is
next opened.

### Honest denominators

* Galerkin adapters: **5/5** (A, B, C, D landed; E ruled no-wrapper with a
  recorded finding).  The lane is now **[E1′ rung derivation + Z assembly]
  only**.
* C was the one adapter with real analysis in it, and it is done — but it
  is still machinery.  `lowreg_spatialMass` is untouched and stays **0%
  until Z**.
* (N) `ricci_flow_unif_existence`: **0%** — stated-and-unproved at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  This brick
  moves it by zero lines.
* P-STOP's §7 half is now Lean-realized; the remaining paper-only piece is
  the rung-3..5 displayed derivation.
* Front 2 ≈ 68% (was 67%); F6 ≈ 92% unchanged; machinery ≈ 97%; whole HCG
  compactness project: low single digits.
* Route-error counter: 0/3.

### What the [E1′ + Z] brick should be told

* The identification is **done and is a hypothesis-free consequence** of the
  two solves: call `projFix_le_two` on `partial_sol_const`'s and
  `proj_partial_sol`'s outputs (same `R`, same `T₀`, same constants), then
  `projFix_tendsto … (K := 2)`, then `projField_tendsto`.  Nothing else is
  needed to pass to the limit.
* Convergence of trajectories is in **`L²([0,T]; H^{a+2})`** — at `a = 1`,
  `L²_t H³`.  Any energy identity written in `C_t H³` must be rewritten;
  §6.1's `L¹_t`-coefficient Grönwall is the intended form.
* For the projected energy identity, the `V_N`-valuedness inputs are
  `projForce_fixed` (forcing) and `projField_fixed` (trajectory), both
  already in `proj_partial_sol`'s output shape; `projSol_fixed` from
  adapter A remains available at the operator level.
* When calling the towers, keep `a` symbolic with `1 ≤ a` and feed `R₀`
  from **class** data.  Do not expect `partial_sol_const` to supply it (see
  E finding 3), and do not normalize the ball order to `3` (finding 2).
* When the hierarchy consumes the ladder, the No. 129 call shape still
  holds: `obtain ⟨κ, hκ, h2⟩ := a2_ladder …` then
  `obtain ⟨Clower, hC, h⟩ := h2 hδ0 hδ_le`, with `δ*` picked between the
  two lines.

## Planner update No. 131 (2026-08-04) - ADAPTERS 5/5 ACCEPTED; [E1′+Z SESSION 1] DISPATCHED (THE FINAL FRONT-2 LANE)

Acceptance of [C+E]: nine new declarations sorry-free and
census-clean; builds green.  Highlights ratified:
- C is the §7 identification IN LEAN: `projFix_dist_le` (:357,
  `(1−Λ)⁻¹` factor), **`projFix_le_two` (:449 — the modulus is the
  ABSOLUTE CONSTANT 2, independent of N, T, R, C₁, C₂)**,
  `projFix_tendsto` (:495), and the [E1′+Z] key input
  `projField_tendsto` (:515) — field-level convergence in the
  solve's own `L²_tH^{a+2}` norm (matches §6.1 v4, does not
  overclaim `C_t`).  `projN_nemytskii` (:189) is the commutation
  that makes the two fixed-point equations subtract.  The
  contraction was re-derived (`forceMap_dist_le` :256) with the
  retraction DROPPED (both fixed points live where it is the
  identity) and memberships as hypotheses.  One layering debt
  recorded (belongs in `PartialForcingFixedPoint.lean`; cut-and-paste
  when next opened).
- E: NO-WRAPPER verdict ratified (the towers are already parametric
  at `1 ≤ a`; a wrapper would be vacuous).  Two carried findings:
  keep `a` SYMBOLIC (the `((1:ℕ):ℝ)+2` scale literal is a type
  index — not normalizable to `3`), and the SHAPE MISMATCH (the
  towers want a pointwise `H^{a+2}` ball on a `SmoothCcTensor`; the
  solve exports a.e.-t `H^{a+1}` + `L²_tH^{a+2}` — `R₀` comes from
  class data / §5-ordered radii, never the solve).

DISPATCHED: [E1′+Z SESSION 1] — Stage 1 the projected rung bounds
(P-STOP §3–§5 in Lean: mode-diagonal energy identity over the
V_N-valued solves, `n_diff_hm_rung` pairing with δ* between the κ
and Clower obtains, the §6.1-v4 L¹ₜ-coefficient Grönwall, zero seed,
per-datum statics right-only, §5 radius ordering), Stage 2 the
all-σ N-uniform mass (hierarchy engine), Stage 3 (budget permitting)
Z: consume the widened `lowreg_spatialMass` hypotheses
(`hfix`/`hbridge`/`hballU` = exactly `partial_sol_const`'s slots at
the campaign instantiation), limit via `projFix_tendsto`/
`tendsto_perModeConv_of_tendsto_timeL2`, Fatou, replace the sorry.
If Z lands, the campaign's Lean sorry census drops to (N) ALONE.

Honest denominators: adapters 5/5 (machinery); `lowreg_spatialMass`
0% until Z; front 2 ≈ 68%; F6 ≈ 92%; machinery ≈ 97%; (N) 0%
(stated, sorry :98); whole HCG project low single digits.
Route-error counter: 0/3.

## Executor report — [E1′ + Z] SESSION 1 (2026-08-04)

**LEAD WITH THE FAILURE.  Z DID NOT LAND, AND IT CANNOT LAND AGAINST THE
CURRENT STATEMENT.**  `lowreg_spatialMass` is **not provable from its present
hypotheses** — a statement gap, not a budget shortfall, and a planner decision
(a second widening) before any executor can assemble Z.  Stage 1 landed only its
two *generic* engine pieces (both sorry-free and census-clean); the
DeTurck-specific rung derivation is blocked behind the same gap.  Route-error
counter unchanged at 0/3 — no Lean route failed; both bricks were green first
try.  The blocker was found by reading the producer chain, not by a failed proof.

### The blocker, precisely

Every route to the conclusion must identify the trajectory with the limit of a
**finite-dimensional** approximation, and the identification needs a
**forcing-ball bound the statement does not carry**.

1. *No bootstrap exists.*  Re-derived this session: the solve gains exactly the
   two derivatives the quasilinear nonlinearity loses
   (`f ∈ L²_tH^k ⟹ U ∈ L²_tH^{k+2}`, then `𝒩(U) ∈ L²_tH^k`), and the cruder
   Duhamel gain (`f ∈ L²_tH^{σ-1} ⟹ sup_t‖U‖_{H^σ} < ∞`) *loses* one relative to
   the nonlinearity.  The all-order mass is genuinely an energy-method theorem,
   exactly as the docstring says.
2. *The energy method needs `V_N`-valued approximants.*  Truncating the **true**
   solution gives an exact identity for the partial sums, but its pairing term is
   `‖𝒩(U)‖_{H^{σ-1}} ≲ Cδ‖U‖_{H^{σ+1}} + C‖U‖_{H^σ}` in **full** norms — the very
   quantity being bounded.  Circular.  On `V_N` all norms are finite a priori and
   the Grönwall closes; the projected system is not optional.
3. *Identification needs the ball.*  Adapter C's `projFix_dist_le` /
   `projFix_le_two` require `‖f_*‖ ≤ R/4` **and** the four `partial_sol_const`
   slots.  The pre-existing high-order analogue
   `galerkinForcing_tendsto_force_timeL2_ofProjFixedPointSymm` likewise carries
   `hgforce : ‖gforce‖ ≤ deTurckForceBallRadiusSymm …`.  Both unavoidable.
4. *`lowreg_spatialMass` has neither.*  No norm bound on `fHi`; no
   `hLip`/`hsingle`/`hzero`/`hsmall`.  `hballU` bounds only the **`H²`** norm of
   the state a.e.-`t`, and that does **not** bound `‖fHi‖`: `liftHiN`'s `H²`
   output is controlled by the state's `H⁴` norm, and `‖U‖_{L²_tH⁴} ≲ (1+T)‖fHi‖`
   — circular.  The unique call site `lowreg_forceJetMass` does not have them
   either.

The statement is not *false* — `Cσ` is existentially quantified after all the
data, so it may depend on `fHi` — it is unprovable as posed.

### The second finding, and why it makes the repair easy

**`lowreg_spatialMass` sits at `a = 2`, but the campaign's contraction solve is
at `a = 1`.**  `lowreg_partial_sol_of_bounds` (`ShortTime/UnifClassBounds.lean:263`)
runs at `((1:ℕ):ℝ)` — forcing `H¹`, field `H³`, forcing ball
`lowregStateRad …/4`.  `fHi` is **not** an `a = 2` fixed point: `force_hi_id`
(`ShortTime/LowRegForceHi.lean:373`) obtains it as the `H²`-level **lift** of the
`a = 1` forcing `fLo`, through `hincl : ∀ᵐ t, incl_{1≤2} (fHi t) = fLo t`.

This is *good* news, because the conclusion is inclusion-invariant:
`timeModeCoeff_timeL2Inclusion`
(`…/MaximalRegularity/TimeL2InterpolationLimit.lean:89`) gives
`timeModeCoeff (timeL2Inclusion hτσ f) i = timeModeCoeff f i`, so the mode
coordinates — hence `perModeConv λᵢ (timeModeCoeff · i)`, the entire content of
the conclusion — are **the same scalar functions of `t`** for `fHi` and for
`fLo`.  The `a = 2` claim is therefore equivalent to the same claim about the
`a = 1` solve, which is exactly where adapters A/B/C already live.

**Recommended widening (planner decision, not taken unilaterally):** add to
`lowreg_spatialMass` (and pass through `lowreg_forceJetMass`) the `a = 1`
partner `fLo`, the lift identity `hincl`, and the `a = 1` forcing-ball bound
`‖fLo‖ ≤ lowregStateRad …/4` together with the `lowreg_partial_sol_of_bounds`
input bundle (`hδ/hCtop/hB0/hB1/hρ/hP/hreal/hcont/htame/hzero`).  All of these
**are already in scope at the call-site chain** — `LowRegApplyTwo.lean:711`
calls `lowreg_partial_sol_of_bounds` with exactly that bundle — so, as with the
first widening, this should cost no producer work.  Without it, Z has no
mathematical content to consume.

### What landed (both sorry-free, census-clean, verified)

**1. `energy_hier_l1_bound` + `galerkin_energy_l1_bound`**
(`…/HeatSemigroup/GalerkinParabolicEnergy.lean`, +160 lines) — the
`L¹_t`-coefficient Grönwall the dispatch named as in-scope.  These are
`energy_hierarchy_explicit_bound_perScale` and
`galerkin_energy_uniform_bound_perScale` with the zeroth-order coefficient
allowed an extra time-dependent summand `A t`, carried through a primitive `S`
(`S 0 = 0`, `0 ≤ S ≤ Sbd`, `S' = A` on `Ico 0 T`); the bound is the
constant-coefficient one inflated by `Real.exp Sbd`, still `N`-uniform and
`t`-uniform on `Icc 0 T`.

This is what §6.1 v4 requires: the C0 cap enters the rung-`k` coefficient
QUADRATICALLY, so `A(k)(t) ≲ class + C‖U_N(t)‖²_{H³}` is `L¹_t` and not `L∞_t`,
and the pre-existing engine's constant `Cmid` could not accept it.

*Route worth carrying:* the substitution `Mk ↦ Mk · exp(−S)` reduces the variable
coefficient to the constant one **exactly**, leaving the dissipation term and the
`√`-seed in place (the seed needs only `e ≤ √e` for `0 < e ≤ 1`, which is where
`0 ≤ S` is spent).  No variable-coefficient Grönwall comparison, no
`image_le_of_liminf_slope_le_deriv_boundary`, no absolute-continuity/FTC
infrastructure.  One new hypothesis relative to the old engine:
`hseed : ∀ k, 0 ≤ seed k`.

**2. `two_mul_sum_ladder_le`**
(`Analysis/Sobolev/Tensor/CrossScaleCauchySchwarz.lean`, +70 lines) —
**P-STOP §3 in Lean.**  From a split `f = fd + fs`, a ladder bound
`‖fd‖_{σ-1} ≤ α‖u‖_{σ+1} + β‖u‖_σ` (the shape `n_diff_hm_rung` delivers) and a
static bound `‖fs‖_σ ≤ D`, it produces

    2 ∑ w^σ · u · f ≤ (2α + ε)·E_{σ+1} + (β²/ε)·E_σ + 2D·√(E_σ)

which **is** the `hclosure` hypothesis of both engines, with `Cδ = 2α + ε`,
`Cmid = β²/ε`, `seed = 2D`.

Recorded consequence: the engines' absorption condition `Cδ < 2` becomes
`2α + ε < 2`, i.e. **`α < 1` with `ε` free in the remaining room** — precisely
P-STOP's `κ·δ*/(1−δ*)² < 1`.  Paper §3 and the Lean engine interface meet with
**no adapter and no constant loss**; `c_par = 1` in the spectral frame is what
makes this exact.  Also: the pairing halves (`abs_sum_crossScale_le`,
`two_mul_sum_sameScale_le_sqrt`) were **already built** in that file — §3 needed
only the composition plus one Young step, not a new Cauchy–Schwarz layer.
`α`, `β` need no sign hypotheses.

### Verification

Focused checks clean on both edited files (two `unusedVariables` warnings on
`two_mul_sum_ladder_le` cleared by *dropping* `hα`/`hβ` — weakest assumptions).
Targeted module builds green: `CrossScaleCauchySchwarz` (8692 jobs),
`GalerkinParabolicEnergy` (8693 jobs).  Axiom census of all three new public
declarations: `propext, Classical.choice, Quot.sound` — zero `sorryAx`.  No
`maxHeartbeats`; no git; no file outside the two claimed ones touched; both files
far under the 3000-line cap (287 / 483).

### Census (explicit)

* `lowreg_spatialMass` — **still `sorry`**, `ShortTime/LowRegAllOrderJet.lean:1088`.
  It is the file's **only** `sorry` (the other 12 hits of the word are prose).
* `lowreg_forceJetMass`, `lowreg_allOrderJet`, `lowreg_joint_two` — unchanged:
  sorry-free wiring, still conditional through `lowreg_spatialMass`.  **Front 2's
  chain is NOT complete**, and the campaign's Lean sorry census did **not** drop
  to (N) alone.
* (N) `ricci_flow_unif_existence` — **0%**, stated-and-unproved at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  This brick moves it
  by zero lines.

### Honest denominators

* `lowreg_spatialMass`: **0%** — unchanged.  Stage 1 (the projected rung
  derivation): **~15%** — the two generic engines the derivation plugs into are
  now built (Grönwall with `L¹_t` coefficient; the §3 closure producer), but the
  DeTurck-specific content — the projected system at the campaign's scale, the
  tower instantiation, the ladder-to-`(α,β,D)` calibration, the §5 radius
  ordering — is untouched and behind the statement gap.  Stage 2: **0%**.
  Stage 3 (Z): **0%, blocked**.
* Galerkin adapters remain 5/5; those plus this brick's two engines are all
  **machinery**, not endpoint.
* Front 2 ≈ **68%** (unchanged; machinery moved, no endpoint did).
  F6 ≈ 92%; machinery ≈ 97%; whole HCG compactness project: low single digits.
* P-STOP: §3's arithmetic and §6.1 v4's `L¹_t` Grönwall are now **Lean-realized**,
  so the remaining ~10% is down to the rung-3..5 *displayed* derivation.

### What the next brick should be told

1. **First, the planner must rule on the widening** (above).  Until
   `lowreg_spatialMass` carries a forcing-ball bound, no executor can close it,
   and any "progress" on it would be frontier-wrapper motion.
2. When widened, work at `a = 1`, not `a = 2`: apply `proj_partial_sol`
   (adapter B) to `lowregNfun`'s slot bundle, get the rung bounds with
   `two_mul_sum_ladder_le` → `galerkin_energy_l1_bound`, then `projFix_le_two` →
   `projFix_tendsto` → `tendsto_perModeConv_of_tendsto_timeL2` → `fatou_sq_mass`,
   and transport to `fHi` with `timeModeCoeff_timeL2Inclusion`.
3. The final assembly is **template work**: lines 1167–1210 of
   `…/HeatSemigroup/GalerkinLimitUniformMass.lean`
   (`deTurckGalerkin_solField_uniformSpatialMass_allOrderSymm`) do exactly the
   `∃ Cσ` → weight domination → `fatou_sq_mass` step and can be mirrored verbatim
   once `hUmass` and `hconv` exist.
4. The remaining *genuine* analytic content, once the gap is closed, is the
   calibration `ladder ⟶ (α, β, D)` at the projected trajectory: producing
   `α < 1` from `κ` and `δ*`, `D` from the per-datum static `‖𝒩(0)‖_{H^σ}`, and
   the primitive `S` from `‖U_N‖²_{L²_tH³}`.  Everything downstream of that
   calibration is now built.

## Planner update No. 132 (2026-08-04) - Z BLOCKER RULED: SECOND WIDENING (S0-bis) APPROVED; ROUTE ERROR 1/3 (NEW COUNT); [S0-bis + Z SESSION 2] DISPATCHED

Session-1 acceptance: the Z blocker is a GENUINE statement defect —
`lowreg_spatialMass` is UNPROVABLE as posed (not false: `Cσ` exists
after all data; but every route to it needs the finite-dimensional
identification, which needs a forcing-ball/fixed-point bundle the
statement lacks; `hballU`'s a.e. `H²` STATE bound does not control
`‖fHi‖` — the `H⁴`-route back is circular).  The four-step blocker
analysis and the a = 2 ⟺ a = 1 equivalence (mode coordinates are
inclusion-invariant, `timeModeCoeff_timeL2Inclusion`; `fHi` is the
`H²` LIFT of `fLo` by `force_hi_id`) are accepted.

**ROUTE-ERROR COUNTER: 1/3 (new count, post-No. 114 reset).**  By
parity with the original spatialMass falseness ruling: the S0-widened
statement was landed, percentages were reported against it, and a
dispatched session partially burned on it (Stage 1 ≈ 15%, Stage 2
0%).  Mitigations recorded: the session still yielded the precise
diagnosis, the zero-producer-cost repair (everything needed is in
scope at the call site `LowRegApplyTwo.lean:711`), and three
sorry-free engine pieces — `energy_hier_l1_bound` /
`galerkin_energy_l1_bound` (the §6.1-v4 L¹ₜ-coefficient Grönwall via
the exact substitution `Mk ↦ Mk·exp(−S)` — no variable-coefficient
comparison, no AC/FTC) and `two_mul_sum_ladder_le` (P-STOP §3 in
Lean; the engines' `Cδ < 2` becomes literally `α < 1` =
`κδ*/(1−δ*)² < 1` — paper and Lean interfaces meet with zero
constant loss).

S0-bis APPROVED (the second widening, same honest-input pattern as
S0): add `fLo`, `hincl`, the `lowregStateRad/4` forcing ball, and
the `partial_sol` input bundle — all present at the unique call
site; rewire; then assemble Z at a = 1 per the session-1 pipeline
(the one analytic step = the `ladder ⟶ (α, β, D)` calibration).
DISPATCHED as [S0-bis + Z SESSION 2].  If Z closes, the campaign's
Lean sorry census drops to (N) ALONE.

Honest denominators: front 2 ≈ 68% (machinery moved, no endpoint);
F6 ≈ 92%; machinery ≈ 97%; `lowreg_spatialMass` 0% (statement to be
made provable, then proved); (N) 0% (stated, sorry :98); whole HCG
project low single digits.  Route-error counter: **1/3**.

## Executor report — [S0-bis + Z SESSION 2] (2026-08-04)

**LEAD WITH THE FAILURE.  Z DID NOT CLOSE, AND A SECOND, INDEPENDENT GAP WAS
FOUND THAT NO PRIOR SESSION RECORDED: the identification layer (adapters B and
C) does not apply to the campaign's solver.**  Adapter C is stated over
`partial_sol_const`, whose nonlinearity must be **globally Lipschitz**; the
campaign's order-one solve is `partial_sol_tame`, and `lowregNfun` is provably
not Lipschitz on its state ball.  So `projFix_le_two` — the whole content of
session-1's "the identification is done and hypothesis-free" hand-off — cannot
be instantiated at the campaign data.  This is a missing-API frontier plus a
**design choice that belongs to the planner** (below), not a failed proof
route; route-error counter unchanged.

S0-bis landed in full, and one genuine step of Z landed with it.

### Part 1 — S0-bis: DONE, and it cost the producer nothing

`lowreg_spatialMass` is **no longer a `sorry`**.  The widening was delivered as
three arguments, not a dozen:

```
    (fLo : timeL2 (tensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ)) T)
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t)
    (hlo : IsLowSolve (I := I) (M := M) g hT hT1 fLo)
```

inserted after `hballU`, everything else unchanged.  The forcing ball and the
`lowreg_partial_sol_of_bounds` input bundle are inside `IsLowSolve`
(`ShortTime/UnifClassBounds.lean`, new): existential background metric,
threshold and six numbers, then the four producer certificates, the horizon cap
`T ≤ lowregHorizon …`, the ball `‖fLo‖ ≤ lowregStateRad …/4`, and the a.e.
Nemytskii identity along `fLo`'s own Duhamel field.  Its satisfiability witness
`isLowSolve_of_sol` takes exactly the arguments and results of the `:711` call.

Propagation: `lowreg_forceJetMass` (same three), `lowreg_allOrderJet` and
`lowreg_joint_of_re` (`fLo`, the transport `hfLo : ∀ᵐ t, f t = tensorHsCongr … (fLo t)`,
`hlo`), and `lowreg_solve_two`, which now exports
`∃ f fLo, IsRealizedTwo … ∧ (∀ᵐ …) ∧ IsLowSolve …`.  **`lowreg_joint_two`'s
statement is byte-identical to before** — the widening is invisible above the
chain, and `lowreg_solve_two` stays axiom-clean, so the honest-input audit is
*discharged*, not deferred.  Two free finds made this cheap: `IsRealizedTwo`
already carried the pointwise inclusion conjunct (No. 7, previously dropped as
`-`), and `hfae` at `:725` was already the transport.

### Part 2 — Z: one step landed, then blocked

`lowreg_spatialMass` is now **proved sorry-free** from a new leaf
`lowreg_loMass` (`LowRegAllOrderJet.lean:1034`) stating the same mass bound
about `fLo`.  That is pipeline step 6 of the session-1 plan, and it is real: by
`hincl` + `Lp.ext`, `timeL2Inclusion … fHi = fLo`; then
`timeModeCoeff_timeL2Inclusion` makes `timeModeCoeff fHi i` and
`timeModeCoeff fLo i` **the same element of `L²(0,T)`**, so the two `perModeConv`
families are literally the same functions of `t`.  The frontier has moved from
`a = 2` to `a = 1`, i.e. to the scale where every piece of Galerkin machinery
already lives.

Steps 1–5 did not land.  The blocker:

* `projFix_le_two` / `projFix_dist_le` / `proj_partial_sol` all require
  `hLip : LipschitzWith L Nfun` (needed to form `nemytskiiOn`, and inherited
  from `partial_sol_const`).
* `lowerState g₀ a R = {x | ‖J x‖ ≤ R}` bounds only the `H^{a+1}` norm.  The
  third arm of the DeTurck tame estimate is `B1·(‖u‖+‖v‖)·‖J(u−v)‖` with `‖u‖`
  the *ambient* `H^{a+2}` norm — unbounded on that set.  Hence no global
  Lipschitz constant exists, and `partial_sol_tame` (not `partial_sol_const`) is
  and must be the campaign's solver.  For contrast, `partial_sol_const`'s
  two-arm `hsingle` **does** imply Lipschitz with `L = C₁R + C₂‖J‖`; the extra
  arm is exactly the quasilinear content `partial_sol_const` cannot express.
* `partial_sol_tame` builds the contraction internally — `Λ` at
  `TameForcingFixedPoint.lean:534`, `hΨ_lip` at `:831`, `Λ ≤ 1/2` at `:575` —
  but exports none of it, and its `L²` Nemytskii is a local
  `(memLp_tame …).toLp` with `memLp_tame` `private`.

**PLANNER DECISION NEEDED.**  Either
(i) build the tame identification layer — public `nemytskiiTameOn` + `coeFn`
beside `nemytskiiOn` in `…/TensorMaximalRegularity/LocalNemytskii.lean`, then
tame analogues of `projN_nemytskii`, `forceMap_dist_le`, `projFix_dist_le`,
`projFix_le_two`, plus `proj_partial_sol_tame` (which is just `partial_sol_tame`
at `projNfun`: `‖Π_N x‖ ≤ ‖x‖` gives the same three constants, and `Π_N ∘ N` is
continuous).  One adapter-C-sized brick, mostly mechanical mirroring; or
(ii) re-derive the campaign's `a = 1` estimate in two-arm form, which the
quasilinear structure appears to forbid.
Recommendation: (i).  Note `forceMap_dist_le`'s existing layering debt (it is
parked in `EigenProjPartialSol.lean`) should be paid off in the same brick.

The second gap is the one already scoped: the base-order-1 rung derivation
calibrated into `(α, β, D)` for `two_mul_sum_ladder_le` and fed to
`galerkin_energy_l1_bound`, then `fatou_sq_mass`.  Untouched — the calibration
was never reached, so there is **no `(α, β, D)` outcome to report**.

### Verification

Focused checks green on all three edited Lean files.  Targeted builds green in
dependency order: `UnifClassBounds` → `LowRegApplyTwo` (9984 jobs) →
`LowRegAllOrderJet` (9985 jobs); the two other `UnifClassBounds` consumers
(`UnifNZeroBound`, `UnifRealizeRadius`) green (9895 jobs).  No
`maxHeartbeats`, no git, no file outside the three claimed ones touched; all
three well under the 3000-line cap.

### Census (explicit — NO, it did NOT drop to (N) alone)

* `lowreg_loMass` — **the new and only front-2 `sorry`**,
  `ShortTime/LowRegAllOrderJet.lean:1034`.  It replaces `lowreg_spatialMass`'s,
  one scale lower.  The file still has exactly one `sorry`.
* `lowreg_spatialMass`, `lowreg_forceJetMass`, `lowreg_allOrderJet`,
  `lowreg_joint_of_re`, `lowreg_joint_two` — all still carry `sorryAx`, now
  through `lowreg_loMass`.  **They did NOT become
  `[propext, Classical.choice, Quot.sound]`.**
* `IsLowSolve` / `isLowSolve_of_sol` / `lowreg_solve_two` / `lowreg_joint_smooth`
  — `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.  That
  `lowreg_solve_two` is clean *after* the widening is the audit proof that the
  new inputs are satisfiable in the campaign.
* (N) `ricci_flow_unif_existence` — **0%**, stated-and-unproved at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  Zero lines moved.

### Honest denominators

* `lowreg_spatialMass`: **proved** (transport only — small but real).
  `lowreg_loMass`: **0%**, and now the whole of F6.  Of its two gaps, the
  identification layer is ~0% and adapter-C-sized; the analytic rung
  derivation/calibration is unchanged at ~15% (the two generic engines exist).
* Front 2 ≈ **69%** (was 68%): one pipeline joint and the statement surgery
  landed; no endpoint did.  F6 ≈ 92%; machinery ≈ 97%; whole HCG compactness
  project: low single digits.
* Front 2's spatialMass chain is **NOT** complete.
* Route-error counter: **1/3**, unchanged.

### What the next brick should be told

1. The frontier is `lowreg_loMass`, not `lowreg_spatialMass`.  Everything above
   it is sorry-free wiring, and `IsLowSolve` gives it every input the session-1
   pipeline named.
2. Rule on the tame-vs-Lipschitz design choice **first**.  Until adapter C has a
   tame form, steps 1–5 of the pipeline have no producer, and any work on the
   calibration cannot be assembled.
3. Do not re-derive the transport (step 6) — it is done.
4. Keep `a` symbolic as `((1 : ℕ) : ℝ)` throughout; the literal `1` is a
   different type index.  `IsRealizedTwo`'s `f` is the one object at `(1 : ℝ)`,
   which is exactly why `hfLo` exists.

## Planner update No. 133 (2026-08-04) - S0-bis ACCEPTED (spatialMass PROVED BY TRANSPORT); TAME GAP RULED OPTION (i); [TAME LAYER + Z SESSION 3] DISPATCHED

Session-2 acceptance:
- **S0-bis GREEN and `lowreg_spatialMass` is now PROVED sorry-free**
  — by transport (`hincl` + `Lp.ext` + `timeModeCoeff_timeL2Inclusion`)
  to the new a = 1 leaf `lowreg_loMass` (`LowRegAllOrderJet.lean:1040`,
  now the SOLE front-2 sorry).  The widening = three binders
  (`fLo`/`hincl`/`hlo : IsLowSolve`), the bundle packaged as
  `IsLowSolve` in `UnifClassBounds.lean` with satisfiability witness
  `isLowSolve_of_sol` (honest-input audit discharged, not deferred);
  `lowreg_joint_two`'s statement unchanged; `lowreg_solve_two` stays
  axiom-clean.  Two free finds made it cheap (the inclusion conjunct
  and `hfae` already existed).
- **SECOND GAP acknowledged and ruled**: adapters B/C target
  `partial_sol_const` (global-Lipschitz `nemytskiiOn`), but the
  campaign's a = 1 solve is `partial_sol_tame`, and `lowregNfun` is
  PROVABLY not Lipschitz (the tame third arm
  `B1·(‖u‖+‖v‖)·‖J(u−v)‖` carries the ambient `H^{a+2}` norm,
  unbounded on `lowerState`).  `partial_sol_tame` builds Λ ≤ 1/2
  internally but exports nothing; its Nemytskii is a private local.
  CLASSIFICATION (executor's, accepted): missing-API frontier +
  design choice — NOT a failed route; counter stays 1/3.  RULED:
  option (i), the tame identification layer (public
  `nemytskiiTameOn` + tame analogues of the C-adapters +
  `proj_partial_sol_tame`, same three constants via projector
  contraction); option (ii) (two-arm re-derivation) appears
  forbidden by the quasilinear structure.
- NEW VERIFICATION LESSON (recorded; the near-miss behind this gap):
  the P-STOP audit's (b) verdict identified "the A1 solve" as
  `partial_sol_const` — a suitable-LOOKING sibling, not the one the
  campaign instantiates.  Rule: before building on a named
  solve/engine, grep the campaign call site and verify it is THE
  instantiated one.

DISPATCHED: [tame identification layer + Z session 3] — Part 1 the
tame API + adapter siblings; Part 2 the calibration
(`ladder ⟶ (α, β, D)`) and the full pipeline to close
`lowreg_loMass`.  If it closes, the campaign census drops to (N)
alone and front 2's chain is COMPLETE.

Honest denominators: `lowreg_spatialMass` 100% (transport);
`lowreg_loMass` 0% (identification layer ~0%, rung/calibration
~15%); front 2 ≈ 69%; F6 ≈ 92%; machinery ≈ 97%; (N) 0% (stated,
sorry :98); whole HCG project low single digits.  Route-error
counter: 1/3.

## Executor report — [TAME LAYER + Z SESSION 3] (2026-08-04)

**LEAD WITH THE FAILURE.  Z DID NOT CLOSE.  `lowreg_loMass` is still the
single front-2 `sorry` (`LowRegAllOrderJet.lean:1052`), and the census did NOT
drop to (N) alone.**  Part 2's calibration was again not reached, and the reason
is a *third* structural finding, not a failed proof route: the Galerkin energy
half of the pipeline has **no order-one producer at all**.  Every piece the
session-1 plan named — the `V_N` ODE system, the mode identification of its
coordinates, and the per-scale closure — exists in this repo only above the
Lipschitz gate `2·finrank ℝ E + 10 ≤ a` (`deTurckGalerkin_solution_existsSymm`
at `GalerkinParabolicEnergyDeTurck.lean:733`, i.e. `≥ 16` in dimension three).
At `a = 1` all three must be built.  Classification: missing groundwork/API,
three bricks; route-error counter unchanged at **1/3**.

Part 1 landed in full, and two genuine steps of Part 2 landed with it.

### Part 1 — the tame identification layer: DONE, axiom-clean, session-2 blocker dissolved

Eleven new declarations, all `[propext, Classical.choice, Quot.sound]`:

* `TensorMaximalRegularity/LocalNemytskii.lean` (122 → 357 lines):
  `timeL2_norm_le_four`, `memLp_tame`, `nemytskiiTameOn`,
  `nemytskiiTameOn_coeFn`.  The first two were `private l2_four` / `private
  memLp_tame` inside `TameForcingFixedPoint.lean`; they are abstract
  time-`L²`/Nemytskii facts, so they were **moved** (private copies deleted, not
  duplicated), with `memLp_tame`'s explicit argument order preserved verbatim so
  `partial_sol_tame`'s two internal call sites needed no edit.
* `TensorMaximalRegularity/TameForcingFixedPoint.lean` (948 → 1046 net; ~190
  lines of private machinery left, ~290 of exported API arrived):
  `nemytskiiTame` + `nemytskiiTame_coeFn` (the geometric wrapper: the state
  operator is `tensorHsInclusion`, whose bound on `lowerState` *is* that set's
  definition), and **`tameMap_dist_le`** — the contraction the solver ran
  internally and did not export, restated in the unretracted form the two fixed
  points need.  `partial_sol_tame`'s statement is byte-identical.
* `HeatSemigroup/EigenProjTameSol.lean` (new, 431 lines): `projN_cont`,
  `projN_tame`, `proj_partial_sol_tame`, `projN_nemytskiiTame`, private
  `lamHalfTame`, `projFixTame_dist_le`, `projFixTame_le_two`.

Free find that halved the brick: `projFix_tendsto`, `projField_tendsto`,
`projForce_fixed`, `projField_fixed`, `projNfun` and `projN_zero` in
`EigenProjPartialSol.lean` carry **no** Lipschitz hypothesis, so the tame lane
reuses them verbatim; only the five estimate-bearing lemmas needed twins.  The
predicted mechanism held exactly: `‖Π_N x‖ ≤ ‖x‖` gives the projected map the
*same* `A, B, C, D`, hence the same closed horizon and the same `Λ ≤ 1/2`.

`forceMap_dist_le`'s layering debt was paid off *in the tame lane* (the tame
contraction lives beside `partial_sol_tame`, not in the spectral file).  The
const-side `forceMap_dist_le` was left where it is — moving it is churn with no
consumer, since **nothing in the repo imports `EigenProjPartialSol.lean`**.

### Part 2 — Z: two steps landed, then blocked on the energy half

New file `ShortTime/LowRegGalerkinIdent.lean` (2 theorems, both axiom-clean,
green first try):

* `lowreg_proj_tendsto` — from `IsLowSolve` alone, `fLo` is the
  `L²([0,T]; H^1)` limit of a sequence of `Π_N`-fixed forcings, at rate
  `2‖Π_N fLo − fLo‖`.  The six numbers are renormalised into `(A, B, C)` exactly
  as `lowreg_partial_sol_of_bounds` does; after `rw [hT₀eq, hBcoe]` the projected
  solve's horizon and `lowregHorizon` are the *same term*, so `hTτ` closes the
  cap directly.
* `lowreg_projMode_tendsto` — the same, descended to every eigen-coordinate at
  every `t ∈ Icc 0 T`.  This is literally `fatou_sq_mass`'s `hconv`.

That is pipeline steps 1–4 of the session-1 plan, at the campaign's own solver.
`LowRegAllOrderJet.lean` now imports the file and `lowreg_loMass`'s docstring
records the state.  **No adapter was introduced**: `lowreg_loMass` was *not*
rewritten to consume a new frontier hypothesis, because the only honest way to
split it would be to assume the Galerkin bound over an existentially-produced
`fseq` — a new over-strong input, no mathematics moved.

Steps 5–6 (the energy hierarchy) did not land.  Precisely: `fatou_sq_mass`'s
second input is an `N`-uniform bound on
`∑_{i ∈ eigenIdxFinset N} w_σ(i)·(perModeConv λᵢ (timeModeCoeff (fseq N) i) t)²`,
and reaching it needs, in order,
(1) the `V_N` Galerkin ODE system for `lowregNfun` — analogue of
`deTurckGalerkin_solution_existsSymm`.  It *should* be reachable at `a = 1`:
on a finite-dimensional ball the tame estimate IS Lipschitz, which is exactly
what `tame_lip_balls` (`TameForcingFixedPoint.lean:64`) already provides;
(2) the identification of that ODE's coordinates with `perModeConv` of the
projected forcing — analogue of `galerkinPerMode_eq_perModeConvSymm`;
(3) the per-scale closure `(Cδ, Cmid, seed, B0)` at base order 1 — analogue of
`deTurckGalerkin_forcing_closure_perScaleSymm` (`…DeTurck.lean:1484`), whose
only route at `a = 1` is `a1_ladder`/`a2_ladder` (`LowRegLadderRung.lean`).
The `ladder ⟶ (α, β, D)` calibration sits *after* (3).  It was never reached, so
there is **no `(α, β, D)` outcome to report** — same as last session.

### Verification

Focused checks green on all five touched Lean files.  Targeted builds green in
dependency order: `LocalNemytskii` (8724 jobs) → `TameForcingFixedPoint` (9537)
→ `EigenProjTameSol` (9543) → `LowRegGalerkinIdent` (9707) → `LowRegAllOrderJet`
(9989).  Because `LocalNemytskii` is low in the tree, every module that imports
it or `TameForcingFixedPoint` *off* that path was also built: the root aggregate
`+DifferentialGeometry` together with `PrincipalTimeH2`, `UnifNZeroBound`,
`UnifRealizeRadius` (10928 jobs, green) and `DeTurckRemainderLowBase{FixedPoint,
Time}` (9619 jobs, green).

One caveat, recorded so the next session does not chase it: a bare `lake build`
does **not** finish in this checkout, and not because of this work.  Its default
target includes `DeclIndex`, which globs every module including
`TensorMaximalRegularity/TimeTameFixedPoint.lean` — a **pre-existing broken
leaf** of the forward-uniqueness lane, last edited 2026-07-25, with no `.olean`
at all, explicitly listed as broken and deliberately excluded from the root
aggregate in `FORWARD_UNIQUE_PLAN.md` (§ "Root-aggregate wiring done here").
Its errors (`:61`, `:74`, `:427`, `:428`, `:644`) are about
`maxRegDuhamelSolField_inclusion_Ha1_ae_pointwise_le` at general `(r,s)` and
mention none of the declarations added here.  A first attempt at a full locked
`lake build` was launched at `-LeanThreads 1`, ran ~50 min without reaching a
failure, and was killed; its stale `lake` and `lean-elaboration` locks were
force-cleared.

No `maxHeartbeats`, no git, no read-only-lane file touched; every file well
under the 3000-line cap.

### Census (explicit — NO, it did NOT drop to (N) alone)

* `lowreg_loMass` — **still the only front-2 `sorry`**,
  `ShortTime/LowRegAllOrderJet.lean:1052` (was `:1040`; +1 import, +12 docstring
  lines).  The file still has exactly one `sorry`.
* `lowreg_spatialMass`, `lowreg_forceJetMass`, `lowreg_allOrderJet`,
  `lowreg_joint_of_re`, `lowreg_joint_two` — all still carry `sorryAx` through
  `lowreg_loMass`.  **They did NOT become `[propext, Classical.choice,
  Quot.sound]`.**
* All eleven Part-1 declarations, plus `lowreg_proj_tendsto` and
  `lowreg_projMode_tendsto` — `[propext, Classical.choice, Quot.sound]`.
* `IsLowSolve` / `isLowSolve_of_sol` / `lowreg_solve_two` — still axiom-clean.
* (N) `ricci_flow_unif_existence` — **0%**, stated-and-unproved at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  Zero lines moved.

### Honest denominators

* `lowreg_loMass`: **0%** — the statement is untouched.  Its *machinery*: the
  identification half went 0% → done; the energy half is ~5% (the two generic
  engines `two_mul_sum_ladder_le` and `galerkin_energy_l1_bound` exist, plus
  `a1_ladder`/`a2_ladder`, but all three order-one producers are unwritten).
  Call the whole supporting apparatus ~35%, and note that last session's "~15%
  rung/calibration" was optimistic: it did not price bricks (1) and (2).
* Front 2 ≈ **71%** (was 69%): a real blocker dissolved and two theorems landed,
  but no endpoint moved.  F6 ≈ 92%; machinery ≈ 97%; whole HCG compactness
  project: low single digits.
* Front 2's spatialMass chain is **NOT** complete.
* Route-error counter: **1/3**, unchanged.

### What the next brick should be told

1. The frontier is unchanged: `lowreg_loMass`.  Everything above it, and now the
   identification below it, is sorry-free.
2. The next brick is **(1)**: the `a = 1` Galerkin ODE system in `V_N` for
   `lowregNfun`.  Build it from `tame_lip_balls` — on `V_N` (finite-dimensional)
   the three-arm estimate gives a genuine local Lipschitz constant, which is what
   Picard–Lindelöf needs.  Do NOT try to lower
   `deTurckGalerkin_solution_existsSymm`'s `2·finrank + 10 ≤ a` gate; that gate
   is about the *Lipschitz* nonlinearity, a different object.
3. Then **(2)** the coordinate identification, then **(3)** the closure, and only
   then the `(α, β, D)` calibration.  Each is its own session.
4. Do not re-derive the transport (session 2) or the identification (this
   session).  `lowreg_projMode_tendsto` is `fatou_sq_mass`'s `hconv`, ready to
   use.
5. Keep `a` symbolic as `((1 : ℕ) : ℝ)`.  Mirror `EigenProjPartialSol.lean`'s
   `open … TensorSpectral hiding TensorEigenIdx`.

## Planner update No. 134 (2026-08-04) - SESSION 3 ACCEPTED (TAME LAYER + IDENTIFICATION DONE; THIRD UNPRICED LAYER = a=1 GALERKIN ENERGY); BRICK (1) DISPATCHED

Acceptance: Part 1 GREEN (11 declarations; `tameMap_dist_le` exports
`partial_sol_tame`'s internal contraction for the first time;
`proj_partial_sol_tame`/`projFixTame_le_two` complete the tame
adapter row; the moved `memLp_tame` preserved argument order so the
solver's call sites were untouched) and the identification half of Z
landed FREE (`lowreg_proj_tendsto`/`lowreg_projMode_tendsto` — the
latter IS `fatou_sq_mass`'s `hconv`).  Part 2 correctly stopped: the
GALERKIN ENERGY half has NO order-one producer — the existing ODE/
closure pieces live behind the `a ≥ 16` LIPSCHITZ-nonlinearity gate
and are not lowerable (different nonlinearity).  Three bricks:
(1) the a = 1 `V_N` Galerkin ODE for `lowregNfun` via `tame_lip_balls`
(:64 — on a ball the tame estimate IS Lipschitz); (2) coordinate ↔
`perModeConv` identification; (3) per-scale closure at base 1 via
the hoisted ladders; then the calibration.  Executor's
classification ACCEPTED: missing groundwork, not a failed route —
counter stays 1/3.  Machinery honesty: `lowreg_loMass`'s apparatus
≈ 35% (session 1's ~15% did not price bricks 1–2).

Build caveat recorded: bare `lake build` cannot finish on this tree
(pre-existing broken leaf `TimeTameFixedPoint.lean`, excluded per
`FORWARD_UNIQUE_PLAN.md`, unrelated) — targeted builds only.

DISPATCHED: brick (1).  Honest denominators: front 2 ≈ 71%;
F6 ≈ 92%; machinery ≈ 97%; `lowreg_loMass` 0%; (N) 0% (stated,
sorry :98); whole HCG project low single digits; counter 1/3.
REALISM NOTE for the reader: "census drops to (N) alone" has slipped
three sessions running, each uncovering an unpriced layer
(identification → tame → Galerkin energy); remaining distance now =
bricks (1)(2)(3) + calibration ≈ 4 sessions IF no further layer
appears.

## Executor report — GALERKIN BRICK (1) (2026-08-04)

**Brick (1) LANDED, sorry-free and axiom-clean, and it is genuinely
unconditional: the `a = 1` `V_N` Galerkin system for `lowregNfun` exists on the
WHOLE interval `[0, T]`, for every `T`, with no smallness whatsoever.**  The
`a ≥ 16` gate was not touched, as instructed.  But the brick also exposed a
**fourth** piece the three-brick count did not price — call it **(1b)** — and
it is stated precisely below.  Classification of (1b): missing groundwork, a
self-contained Grönwall estimate; not a failed route.  Route-error counter
unchanged at **1/3**.

### The mathematics that made it work

One observation carries the whole brick.  `tame_lip_balls` turns the three-arm
estimate into a genuine Lipschitz constant as soon as the argument is bounded
in the **top** norm `H^{a+2}`.  On a truncation that is free: `1 + λᵢ ≤ κ` on
`V_S` gives `‖u‖_{a+2} ≤ √κ ‖u‖_{a+1}`, so the state ball — which by definition
bounds only `‖·‖_{a+1}` — is top-bounded on `V_S`, with radius `√κ · R`.  The
tame nonlinearity is therefore Lipschitz on the *entire* state ball of `V_S`.

That in turn forced the design of the retraction, and this is the part worth
recording.  The retraction must be taken in `H^{a+1}`, **not** `H^{a+2}`:
parabolic maximal regularity gives the Galerkin trajectory an `N`-uniform
`L^∞_t H^{a+1}` bound and only an `N`-dependent `L^∞_t H^{a+2}` one
(`L²_t H^{a+2} ∩ H¹_t H^a ↪ C_t H^{a+1}`, and no better), so an `H^{a+2}`
retraction would be inert only on an `N`-dependent region and would be useless
downstream.  The `H^{a+1}` radial retraction is conjugate to the existing
`ballRetraction` on `H^{a+1}` by linearity, so its `1`-Lipschitz property, its
image bound and its inertness all transfer for free; the only new ingredient is
`‖w‖_{Euclid} ≤ ‖J(Emb w)‖_{a+1}`, which holds because every Sobolev weight at
a non-negative exponent is `≥ 1`.

The resulting coordinate field `−Λ w + Π_S N(retract w)` is globally Lipschitz
with a global affine bound whose linear part is just `‖Λ‖` (the retraction caps
the nonlinearity outright), so `forward_solution_of_lipschitzWith_affineBound`
applies with the zero seed and no horizon condition.

### What landed

New `HeatSemigroup/GalerkinTameSol.lean` (774 lines, 27 declarations, all
`[propext, Classical.choice, Quot.sound]`): the truncated norm comparisons
(`galCoordNormLe`, `galTopNormLe`, `galEmbTopLe`), the retraction
(`galTameRetr`, `galTameStateC`, with `_view`, `_mem`, `_eq`, `_top`,
`galTameState_lip`, `galTameStateC_eq`), the field (`galTameField`,
`galTameBall`, `galTameField_lip`, `galTameField_aff`), and the system
(`galTameForce`, `galTameForce_eq`, `galTameSolOne`).

New `ShortTime/LowRegGalerkinSol.lean` (170 lines): `lowregGalSol`, the `a = 1`
instantiation against `lowregNfun`.  It takes the **six-number producer form**,
not an `IsLowSolve` bundle, deliberately: `IsLowSolve` existentially binds the
six numbers and `hreal`, on which `lowregNfun` depends, so an
`IsLowSolve`-shaped conclusion would have to re-existentialise `Nfun` and would
lose the link to the `Nfun` of `lowreg_projMode_tendsto`.  Brick (2)
destructures `IsLowSolve` once and feeds both.  Only `hδ, hCtop, hB0, hB1, hρ,
hP, hreal, htame` are used — continuity, the zero-state bound `D`, the horizon
cap and the forcing ball are all unnecessary for existence.

### The new piece: brick (1b), state-ball preservation

`galTameSolOne` reports the forcing at the **retracted** state.
`galTameForce_eq` discharges the retraction the instant the trajectory
satisfies `‖J(finiteEigenComboHs … (U N t) 3)‖_{H²} ≤ R` — the true state-ball
condition, `N`-uniform.  Producing that bound is a separate estimate:

    ½ d/dt ‖U‖²_{H²} = −‖U‖²_{H³} + ‖U‖²_{H²} + ⟨U, f⟩_{H²}
                     ≤ −‖U‖²_{H³} + ‖U‖²_{H²} + ‖U‖_{H³}‖f‖_{H¹},

and `‖f‖_{H¹} ≤ D' + (Ctop·lowregOuterRad + B1·R)‖U‖_{H³}` with
`Ctop·lowregOuterRad + B1·R ≤ 1/8` by `lowregOuterRad_small` and
`lowregStateRad_small`, so both `‖U‖_{H³}` terms absorb into `−‖U‖²_{H³}` and
Grönwall from the zero seed gives `‖U(t)‖²_{H²} ≤ D'²(e^{2t} − 1)`,
**`N`-uniformly**.  The ball then holds for `T ≲ log(1 + R²/D'²)/2`, a new
smallness that must be calibrated against `lowregHorizon`.  This is one
session's work and is prerequisite to brick (3), which needs the true forcing.

### Verification

Focused checks green on both new files; targeted builds green in dependency
order (`GalerkinTameSol` 9573 jobs, `LowRegGalerkinSol` 9705 jobs), no warnings
in either new file.  Axiom census run from a temporary `#print axioms` block
(removed afterwards): all 28 new public declarations
`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`.  No
`maxHeartbeats`, no git, no read-only-lane file touched, both files well under
the 3000-line cap.  The bare-`lake build` caveat is unchanged and unrelated.

### Census

* `lowreg_loMass` — **still the only front-2 `sorry`**,
  `ShortTime/LowRegAllOrderJet.lean` (statement `:1000`, `sorry` `:1064`).  The
  file was **not touched**.
* `lowreg_spatialMass`, `lowreg_forceJetMass`, `lowreg_allOrderJet`,
  `lowreg_joint_of_re`, `lowreg_joint_two` — still carry `sorryAx` through
  `lowreg_loMass`.
* (N) `ricci_flow_unif_existence` — **0%**, stated-and-unproved at
  `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at `:98`.  Zero lines moved.

### Honest denominators

* `lowreg_loMass`: **0%** — statement untouched.  Its machinery: identification
  half done; energy half went ~5% → **~30%** (brick (1) done; (1b), (2), (3)
  and the calibration unwritten).  Whole supporting apparatus ≈ **45%**.
* Front 2 ≈ **73%** (was 71%): one of four Galerkin pieces landed, no endpoint
  moved.  F6 ≈ 92%; machinery ≈ 97%; whole HCG compactness project: low single
  digits.
* Route-error counter: **1/3**, unchanged.

### What the next brick should be told

1. Do **(1b)** before (2): the Grönwall `H²` ball bound above.  It is
   self-contained, `N`-uniform, and every later step needs it, because without
   it `galTameForce` is not the true forcing.  The two smallness certificates
   it needs (`lowregOuterRad_small`, `lowregStateRad_small`) already exist and
   are exactly the ones `partial_sol_tame` uses.
2. Then **(2)**: identify `U N t i` with `perModeConv λᵢ (timeModeCoeff (fseq N) i) t`.
   Route: Duhamel for the linear ODE, then the projected fixed-point uniqueness
   of `proj_partial_sol_tame` to match `fseq N`.  `lowreg_projMode_tendsto` is
   already `fatou_sq_mass`'s `hconv`.
3. Do NOT lower `deTurckGalerkin_solution_existsSymm`'s gate, and do not import
   its `deTurckSobolevNHa2Symm` machinery — `GalerkinTameSol.lean` reuses only
   `galerkinCoordEmbed/Restrict/Diag` from that file.
4. `galTameForce_eq` is the bridge; state (1b) in exactly its hypothesis shape
   (`‖galLowView g₀ 1 (finiteEigenComboHs g₀ (eigenIdxFinset g₀ N) (U N t) 3)‖ ≤ lowregStateRad …`).

## Planner update No. 135 (2026-08-04) - BRICK (1) ACCEPTED; FOURTH UNPRICED PIECE (1b); IMPLEMENTATION HELD FOR THE CODEX AUDIT

Acceptance: brick (1) GREEN and UNCONDITIONAL — `lowregGalSol`
(`ShortTime/LowRegGalerkinSol.lean`) exists on all of `[0,T]` for
every `T` with no smallness; 28 declarations, zero sorryAx, builds
9573/9705 green.  The load-bearing design judgment is RATIFIED: the
retraction lives in `H^{a+1}`, NOT `H^{a+2}` — parabolic maximal
regularity gives an N-UNIFORM `L∞_tH^{a+1}` bound but only an
N-dependent `H^{a+2}` one, so an `H^{a+2}` retraction would be inert
only on an N-dependent region (useless downstream).  On a truncation
the top norm is free (`1+λᵢ ≤ κ`), so `tame_lip_balls` makes the
nonlinearity Lipschitz on the ENTIRE `V_S` state ball; the `H^{a+1}`
radial retraction is conjugate to `ballRetraction` by linearity;
`forward_solution_of_lipschitzWith_affineBound` closes.  The
six-number producer form (NOT an `IsLowSolve`-shaped conclusion) is
ratified — re-existentialising would sever the link to
`lowreg_projMode_tendsto`; `htame` is byte-identical to the
`IsLowSolve` field (diffed).

FOURTH UNPRICED PIECE — brick (1b): discharging the retraction needs
the N-uniform `H²` trajectory ball, an UNCONDITIONAL Grönwall
(`½ d/dt‖U‖²_{H²} ≤ −‖U‖²_{H³} + ‖U‖²_{H²} + ‖U‖_{H³}‖f‖_{H¹}`,
forcing coefficient ≤ 1/8 by the existing smallness certificates,
both `H³` terms absorb, `‖U(t)‖²_{H²} ≤ D'²(e^{2t}−1)` N-uniformly).
One session; prerequisite to brick (3).  The four-miss pattern
(identification → tame → Galerkin energy → 1b) now has four
exhibits.

**IMPLEMENTATION HELD.**  Per the user's direction, an independent
Codex audit takes over before further bricks
(`ShortTime/CODEX_AUDIT_HANDOFF.md`, updated post-brick-(1); the
audit's task A hunts the layer pattern to exhaustion, task B
challenges Galerkin necessity, task D re-prices).  The Claude lane
resumes on the audit's verdict.

Honest denominators: `lowreg_loMass` 0% (energy-half machinery
~30%, whole apparatus ≈ 45%); front 2 ≈ 73%; F6 ≈ 92%; machinery
≈ 97%; (N) 0% (stated, sorry :98); whole HCG project low single
digits.  Route-error counter: 1/3.

## Planner update No. 136 (2026-08-04) - CODEX AUDIT ADOPTED: STOP-AND-REDESIGN; ROUTE ERROR 2/3; FEASIBILITY GATE DISPATCHED

The independent Codex audit (`ShortTime/CODEX_LOMASS_AUDIT.md`, 453
lines, read-only, census-verified with 10 fresh `#print axioms`) is
ADOPTED as the governing plan for the `lowreg_loMass` endgame.  Its
§7 verdict: **STOP-AND-REDESIGN the three-brick lane**, keeping the
projected fixed-point layer, Fatou, and the landed towers/ladders.
Findings integrated:
1. The independent Galerkin ODE (brick (1)) is to be DELETED from
   the design — the projected fixed points ARE the approximation
   family.  **ROUTE-ERROR COUNTER: 2/3** — a ratified route was
   dispatched, a full session built it, and the redesign discards
   it.  (The Lean artifacts stay in-tree for now — sorry-free and
   harmless; removal is deferred housekeeping.)
2. `lowreg_loMass` needs a THIRD widening (add `hDim`; repair
   `IsLowSolve`'s missing self-background, δ-range, smooth-core and
   absorption certificates) — audit §4.
3. NEW decisive gap (J3): the C0 tower hides the pointwise `H³`
   radius inside an opaque constant, so the `L¹_t` Grönwall
   coefficient cannot be generated from `L²_tH³`.  The gate brick
   below tests exactly this.
4. `galerkin_energy_l1_bound` needs an `N`-indexed `A N t` variant
   (J5).
5. Honest price: **12–16 sessions, central ≈ 14** (my ≈4 was
   optimistic by ~3× — the audit's re-pricing stands).
Machinery honesty adopted: `lowreg_loMass` dedicated effective
machinery ≈ 30% (brick-(1) output no longer counted).

DISPATCHED: the audit's mandated feasibility gate —
`selfLow_jet_quad` (the C0 jet bound with EXPLICIT quadratic
`‖T‖²_{H³}` dependence, constants before `T`, no `R₀`, no opaque
cap; route hint = replace `gradCapOfBall` by an explicit-norm
variant in the existing capped-arm proof).  PASS ⟹ the redesigned
lane proceeds (next: the lowest tower-direct energy pairing, then
the `IsLowSolve`/δ* producer redesign).  OBSTRUCTION (higher than
quadratic / same-rung radius / cutoff inverse inequality) ⟹ report
exactly — and note that at counter 2/3, a subsequent genuine route
error triggers the user's stop condition.

Honest denominators (audit-calibrated): whole HCG ≈ 3%; (N) 0%
(stated, sorry :98); `lowreg_loMass` 0% (machinery ≈ 30%); front 2
and F6 figures to be re-baselined against the audit's §5 plan at
the next landing.  Route-error counter: **2/3**.

## Executor report No. 137 (2026-08-04) - GATE `selfLow_jet_quad`: FAIL AS SCOPED, LANE PREMISE SOUND; ROUTE-ERROR COUNTER UNCHANGED (2/3)

**Verdict: OBSTRUCTION on the brick as scoped, PASS on the lane's
premise.**  No theorem was added; `LowRegC01JetTower.lean` is
unchanged (nothing was claimed on it).  Full write-up in
`DeTurck/LowRegC01JetTower.md`, section "session N+5".

1. **The audit's route hint is provably dead.**  `gradCapOfBall` is
   indeed the only place `R₀` enters as a magnitude, and that part
   is pure bookkeeping (`Λ = max 1 (max ((n/3)²) (Λ₁²))`, affine in
   `‖T‖²_{H³}`).  But the radius reaches the CONSTANT as a
   polynomial whose degree grows with the jet order: every arm
   window enters through `capOfArm` with `K i * shiftConst Λ (i+1)`,
   `shiftConst Λ k = Σ_{m≤k} Λ^m·count m` is degree `k`, and
   `foldConst` multiplies two arm constants at each product node so
   degrees ADD — `ricciAACap` reaches `Λ`-degree `3(i+1)`, i.e.
   degree `6(i+1)` in `‖T‖_{H³}`, degree six already at `i = 0`.
   The `Λ^m` is structural, not slack: `prodShift` must pay it
   because `(|∇P|²)^m` has weight zero in the shifted base and so
   sits in no shifted window (`antidiagonalTupleGrid b 0 = 1`).
   Target needs `Λ`-degree ≤ 1.  Self-application (`a := 1`,
   `R₀ := ‖T‖_{H³}`) removes `R₀` but yields
   `Poly_{6(i+1)}(‖T‖_{H³})` — an explicitly forbidden shape, so it
   was NOT written under the deliverable's name.  A false PASS was
   available here and was declined.

2. **The audit's stop-condition trigger is NOT met.**  The C0 arm
   algebra does not force a higher power; there is no same-rung
   radius in a Grönwall coefficient and no cutoff-dependent inverse
   inequality.  The five `selfLow_split` summands are (analytic in
   `P`) ⋆ (at most quadratic in `∇P`), and the classical Moser tame
   estimate gives `‖∇ⁱ(arm)‖_{L²} ≲ C(δ)·‖∇P‖_∞·(1+‖P‖_{H^{i+1}})` —
   ONE power of `‖∇P‖_∞ ≲ c‖T‖_{H³}`, exactly the quadratic shape.
   The `(∇P)^{i+2}` terms from the inverse-metric expansion are
   anchored at `‖P‖_∞ ≤ δ ≤ 1/3` (a fixed constant) by
   Gagliardo–Nirenberg, not at `‖∇P‖_∞`.  The capped-grid currency
   cannot see this because it estimates `|∇ⁱ(arm)|²` POINTWISE,
   where that term genuinely has size `|∇P|^{2(i+2)}`.  So
   PSTOP's "the C0 cap enters the rung-`k` coefficient
   QUADRATICALLY" stands, and the redesigned lane's `L¹_t`
   Grönwall coefficient is generable from `L²_tH³`.

3. **The enabling primitives are present and SORRY-FREE**, verified
   by a fresh axiom probe: `exists_gagliardoNirenberg_iteratedCovGrad_l2Norm_le`
   (the `L^∞`-anchored interpolation — the δ-anchor this route
   needs), `exists_moserTameProduct_iteratedCovGrad_l2Norm_le` and
   its `pi` variant, all `[propext, Classical.choice, Quot.sound]`.
   **STALE-DOC HAZARD:** `Analysis/Sobolev/MoserTameProduct.lean`'s
   docstrings still claim the GN half is `sorry`-blocked (on
   `l2jet_logConvex_iteratedCovGrad` /
   `secondCovDeriv_unit_frame_fiberNormSq_le`); both are proved and
   the file has no `sorry` term at all.  This is false-wall
   generator No. 5 — fix before the next brick reads it.

4. **What the next brick must be told.**  NOT a constant refactor.
   The real brick is the TAME C0 BOTTOM: re-derive the five
   `selfLow_split` summands' `L²` jets in the tame currency (one
   `∇P` in `L^∞` = the single `‖T‖_{H³}` power; top jet in `L²`
   inside `range (i+2)`; intermediate jets interpolated at the
   δ-anchor).  Pattern to copy: `AppCcJetWindowTame.lean`'s tame
   per-order C2 layer (`…_perOrder_l2_tame_generic`, conclusion
   already `K i * (1 + ‖P‖_{H^i})`) — re-derived, not instantiated,
   since its own constant is a growing power of its cap.  The
   pointwise arm windows are not reusable: at `i = 0` they already
   read `|arm|² ≤ K 0` (window `= 1`), the `∇P` structure having
   been spent into the constant.  Estimate: several bricks (3–5),
   which pushes the audit's 12–16-session price up rather than
   down.  The audit's own next items (lowest tower-direct energy
   pairing, then the `IsLowSolve`/δ* producer redesign) are
   unaffected and can run in parallel with the tame C0 layer.

Route-error counter: **unchanged at 2/3** — this was a gate that
returned a negative result about a hinted route, which is the gate
working as designed, not a ratified route discarded after
implementation.

Honest denominators: `selfLow_jet_quad` not started (0%), its
dedicated machinery ≈ 20–30% (both GN/Moser primitives exist
sorry-free; the five-summand tame re-derivation untouched);
`lowreg_loMass` 0% (machinery ≈ 30%); (N) 0% (stated,
`Evolution/ExtendViaUniqueness.lean:80`, sorry :98); whole HCG ≈ 3%.

## Planner update No. 138 (2026-08-04) - GATE VERDICT INTEGRATED: PREMISE SOUND, BRICK RE-SCOPED TO THE TAME C0 BOTTOM; COUNTER STAYS 2/3

The feasibility gate (executor report No. 137) is ACCEPTED in full:
- OBSTRUCTION on the brick AS SCOPED: the capped-grid currency's
  constants carry `Λ`-degree `3(i+1)` (degree `6(i+1)` in
  `‖T‖_{H³}` — six already at i = 0), and the degree is STRUCTURAL
  (`prodShift` must pay `Λ^m`; a weight-one m-tuple is `(|∇P|²)^m`
  with weight zero in the shifted base).  The available false PASS
  (self-apply at `R₀ := ‖T‖_{H³}`) was correctly declined.
- The AUDIT'S STOP-CONDITION IS NOT MET: the C0 arm algebra is
  genuinely quadratic (classical Moser tame — one `‖∇P‖_∞` power;
  the `(∇P)^{i+2}` inverse-metric terms GN-anchored at the FIXED
  `δ ≤ 1/3`).  The capped currency cannot see this because it works
  POINTWISE, where the term genuinely has size `|∇P|^{2(i+2)}`.
  PSTOP's premise stands; the `L¹_t` coefficient IS generable from
  `L²_tH³` — via the TAME currency, not the capped one.
- FALSE-WALL GENERATOR #5 (stale docstrings claiming a blocking
  sorry over now-proved inputs) caught before it flipped the
  verdict; cleanup chip pending user-side.
- COUNTER STAYS 2/3: a gate returning a negative on a hinted route
  is the gate WORKING, not a ratified route discarded.

RE-SCOPE (within the audit's framework): the first implementation
brick is the TAME C0 BOTTOM — re-derive the five `selfLow_split`
summands' `L²` jets in the tame currency (one `∇P` in `L∞`, top jet
in `L²` within `range (i+2)`, intermediates GN-interpolated at the
δ-anchor; pattern `AppCcJetWindowTame.lean` re-derived, not
instantiated), then assemble `selfLow_jet_quad`.  Estimated 3–5
bricks — the audit's 12–16-session price adjusts UP accordingly.
The audit's parallel items (third widening design, N-indexed
engine) are unaffected.  SESSION 1 DISPATCHED (tame composition
layer + ≥2 summands, one quadratic + one linear).

Honest denominators: unchanged from No. 137's footer (whole HCG
≈ 3%; (N) 0%; `lowreg_loMass` 0%, machinery ≈ 30%;
`selfLow_jet_quad` 0%, machinery ≈ 20–30%).  Route-error counter:
**2/3**.

## Executor report No. 138-executor (2026-08-04) - TAME C0 BOTTOM SESSION 1: TAME COMPOSITION LAYER BUILT; ZERO SUMMANDS CLOSED END-TO-END

**Verdict: PARTIAL.  The reusable tame layer exists and is sorry-free;
the "≥ 2 summands end-to-end" half of the dispatch was NOT reached, and
the reason is structural, not a time overrun.**  Route-error counter
unchanged (2/3): no ratified route was discarded.

### Where the session failed (leading with it)

Zero of the five `selfLow_split` summands were closed.  The blocker is
**not** the `L²` composition engine — that was built — but the layer
below it: every existing per-arm window (`ricciAACap`, `lc0VBCapAtgw`,
`lieCovCap`, `lc0AMixCap`, `lc0RiemCap`, `ricciDACap`) delivers its
pointwise bound in the `antidiagonalTupleGridWindow` currency, in which
the `∇P` factors have **already been absorbed into the constant**
(at `i = 0` the window is `1`, so the statement reads `|arm|² ≤ K 0`).
Feeding the tame engine requires a *fresh* per-arm Leibniz expansion
exhibiting the explicit factors `∏_j ∇^{c_j}P`.  That is per-arm work in
the fibre-algebra layer and is the bulk of the remaining bricks.

A second, sharper finding: **the tame redistribution is provably not a
pointwise operation.**  For a quadratic arm the generic Leibniz term is
`∏_{j≤q} ∇^{c_j}P` with `∑ c_j = i + 2`, `q ≥ 2`, and one checks directly
that `∏_j |∇^{c_j}P|(x) ≤ Λ₁ · (grid at total order i+1)(x)` is FALSE
pointwise whenever no `c_j` equals `1` (e.g. `|∇²P|²|∇ⁱP|²`).  So no
amount of work inside `HasCapWin`/`antidiagonalTupleGridWindow` can
produce the quadratic constant; the split must happen after integration.
This confirms No. 137's diagnosis at the level of the actual inequality
and rules out the cheapest remaining hope (a pointwise `Λ₁`-prefactored
window).

### What was built (`Analysis/Sobolev/TensorHilbert/TameGridProd.lean`, new)

The `L²` composition layer, valence-generic where possible:

* `gridIntUnit` — the per-antidiagonal grid-product integral with a
  **state-free** constant.  Content: `grid_prod_int_le` with the
  order-zero cap normalized to `Λ₀ ≤ 1`, which collapses its workhorse
  constant `(max Λ₀ (max C 1))^{7i}` to `(max C 1)^{7i}`.  In the C0
  application `Λ₀ = ‖P‖_∞ ≤ finrank/3 = 1`, so the hypothesis is free.
  Deliberately not routed through `atgGridIntRs`, whose additive `1`
  survives the rescaling below and would create a `‖T‖⁴_{H³}` term.
* `gridIntTwo` — two-factor specialization.
* `gridIntGrad` — **the quadratic tame product**, the real content:
  for `c₁ + c₂ = k + 1`, `c₁, c₂ ≥ 1`,
  `∫ |∇^{c₁}P|²|∇^{c₂}P|² ≤ K k · (1 + Λ₁²) · ‖∇ᵏP‖²` with `K`
  state-free.  Used at `k = i + 1` this is exactly the target shape:
  `range (i+2)` budget, constant affine in `Λ₁²`.  The trick is a
  rescaling — normalize `∇P` by `max Λ₁ 1` so the shifted-base grid runs
  at unit cap (state-free constant), then pay the scale back once, which
  costs `Λ₁^{2(q-1)} = Λ₁²` at `q = 2` instead of the capped currency's
  `Λ₁^{7·order}`.
* `gridIntPull` — the other closable case: a Leibniz term carrying a bare
  `∇P` factor gives `Λ₁² · K k · ‖∇ᵏP‖²` directly.
* `gradCapLin` — the `∇P` cap with its `H³` dependence **explicit**,
  `|∇T|²(x) ≤ c·∑_{j<3}‖∇^{1+j}T‖²`.  `gradCapOfJets` fixes `R₀` before
  choosing `Λ₁`, hiding the dependence in an existential — which is why
  the capped currency could not exhibit its own degree.  This is the
  substitution that turns `Λ₁²` into `c‖T‖²_{H³}`.

Constants, exact shapes: `gridIntUnit`/`gridIntTwo`/`gridIntPull` give
`K k` **fully state-free** (background metric + order only).
`gridIntGrad` gives `K k · (1 + Λ₁²)` = state-free `+` state-free `×`
`‖T‖²_{H³}` after `gradCapLin` — i.e. exactly the audit's `K₀ + K₂‖T‖²`.

### The remaining analytic frontier (one, precisely stated)

The Leibniz terms of a quadratic arm split into three classes:

1. some `c_j = 1` → `gridIntPull`. CLOSED.
2. `q = 2` → `gridIntGrad`. CLOSED.
3. `q ≥ 3` **and** all `c_j ≥ 2` → OPEN.

Class 3 first occurs at jet order `i = 4` (it needs
`∑ a_m + b₁ + b₂ = i` with all `a_m ≥ 2` and `b₁, b₂ ≥ 1`).  The
estimate is true: a three-point interpolation with weights `α_j` (anchor
`‖∇P‖_∞`), `β_j` (anchor `‖P‖_∞ ≤ δ`), `θ_j` (top `‖∇^{i+1}P‖_{L²}`)
obeying `c_j = α_j + θ_j(i+1)`, `∑ α_j = 1`, `∑ θ_j = 1` is feasible
exactly when `∑_j (i+1-c_j)/i ≥ 1`, i.e. exactly when `q ≥ 2`.  What is
missing is an interpolation BETWEEN the two two-point
Gagliardo–Nirenberg scales the tree has (`P`-anchored and `∇P`-anchored);
pure `∇P`-anchoring costs `Λ₁^{2q-2}`, pure `P`-anchoring overshoots the
budget by one derivative.  **Planner decision needed:** if the `(N)`
campaign's jet budget really is `∀ a ≤ 3`, class 3 is off the critical
path and the tame C0 bottom needs no new interpolation at all.

### Files

New: `Analysis/Sobolev/TensorHilbert/TameGridProd.lean` (+ `.md` note
with the full route, the three-class analysis, and five durable Lean
lessons — `set μ : Measure M` needs a local `borel` instance;
`integral_congr_ae` leaves an un-beta-reduced goal; `![d₁,d₂] 0` is `rfl`
but `rw`'s closing `rfl` will not see it; `1 + m` vs `m + 1` must be
handled by `obtain ⟨m, rfl⟩`, never `rw [Nat.add_comm]`, because the
index sits in a dependent valence slot; `SmoothCcTensor` has no
`NormedSpace` instance).  `LowRegC01JetTower.lean` untouched, its census
unchanged.

### Verification

Focused check of the new file: green, no errors, no warnings.  Targeted
build `+…TensorHilbert.TameGridProd`: green (9536 jobs).  Axiom census
of all five public declarations (`gridIntUnit`, `gridIntTwo`,
`gridIntPull`, `gridIntGrad`, `gradCapLin`): **clean**,
`[propext, Classical.choice, Quot.sound]`, no `sorryAx` — which also
re-confirms that the whole GN/Moser chain underneath is sorry-free.
Memory guard checked throughout; one debounced phys-free dip to 0.25 GB
recovered on its own, no action taken.  Operational hazard recorded in
`TameGridProd.md`: interrupting a `lake build +Module` on this branch
deletes the olean of the module it was on and leaves the elaboration
lock stale (`release -Token` does not clear elaboration locks — rename
`.lake/codex-locks/lean-elaboration.lock` per the repo's existing
`…interrupted-*` convention and re-run the build to completion).

### Honest denominators

`selfLow_jet_quad`: **still 0%** — not stated in Lean.  Its dedicated
machinery: was 20–30%, now ≈ 40–45% (the `L²` composition layer exists
sorry-free and covers two of the three Leibniz classes; the per-arm
expansions, which are the bulk, are untouched).  `lowreg_loMass` 0%
(machinery ≈ 30%).  `(N)` 0% (stated,
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at :98).  Whole HCG
compactness project ≈ 3%.  Remaining tame-C0 bricks: 3–4 (unchanged from
No. 138's 3–5, one consumed).

## Planner update No. 139 (2026-08-04) - SESSION 1 ACCEPTED (COMPOSITION LAYER GREEN); CLASS-3 RULED ON-PATH (+1 BRICK); SESSION 2 DISPATCHED

Acceptance: the tame composition layer is GREEN (five public
declarations in the new `TensorHilbert/TameGridProd.lean`, census
clean; the load-bearing trick — normalize `∇P` by `max Λ₁ 1` so the
shifted grid runs at unit cap and the scale is paid back ONCE — buys
`Λ₁²` where the capped currency paid `Λ₁^{7·order}`; the constant
shapes are exactly the audit's `K₀ + K₂‖T‖²_{H³}`).  The sharper
structural finding is RATIFIED: the tame redistribution is provably
NOT pointwise (`∏|∇^{c_j}P| ≤ Λ₁·grid(i+1)` fails pointwise when no
`c_j = 1`) — all redistribution happens after integration.  Zero
summands closed (the per-arm Leibniz expansions are the remaining
bulk; the existing arm windows spent their `∇P` structure into
constants and are NOT reusable).

**PLANNER RULING on the class-3 call: ON-PATH, pending explicit
confirmation.**  The executor's "if the (N) budget is ∀a ≤ 3, class
3 never occurs" conflates the INITIAL-DATA jet budget with the TOWER
order `i`: the bottom-rung closure (PSTOP §6.1, rungs k = 3..5)
pairs coefficient jets to order ~k+1 ≤ 6, so tower orders
i ∈ {4,5,6} are consumed and class 3 (q ≥ 3, all c_j ≥ 2, first at
i = 4) occurs there.  The two-GN-scale interpolation lemma is
therefore counted as +1 brick (session-2's executor must CONFIRM the
maximal consumed tower order i* from the §6.1 pairing before
building it — if i* ≤ 3 after all, the ruling reverts and the brick
is dropped).

Operational hazard recorded (from the report): interrupting a
targeted build deletes the in-flight module's olean and leaves a
stale elaboration lock; the ~9500-module rebuilds stem from dirty
upstream files of other lanes.

DISPATCHED: SESSION 2 — per-arm Leibniz expansions with explicit
`∇P` factors (start `lc0VB` + the `A·A` arm), feeding
`gridIntPull`/`gridIntGrad`; classes 1–2 cover their leading terms
regardless of the class-3 question.

Honest denominators: `selfLow_jet_quad` 0% (machinery ≈ 40–45%);
`lowreg_loMass` 0% (≈ 30%); (N) 0%; whole HCG ≈ 3%; tame-C0 bricks
remaining 3–4 (+1 conditional).  Route-error counter: **2/3**.

## Executor report No. 139-executor (2026-08-04) - TAME C0 BOTTOM SESSION 2: `A·A` ARM CLOSED END-TO-END; `lc0VB` NOT REACHED, BLOCKER NAMED; i* = 4 CONFIRMED

**Verdict: PARTIAL, one arm of two.**  `A·A` is closed end-to-end at the
deliverable shape; `lc0VB` was not started and its blocker is one named
missing input (below).  Route-error counter unchanged (**2/3**): no
ratified route was discarded.

### `i*` CONFIRMATION (planner-mandated, No. 139)

**`i* = 4`, so class 3 STAYS on-path — but only barely.**
`PSTOP_PROPOSITION.md` §6.3 BUDGET CHECK is explicit: pairing at rung `k`
costs `‖𝒩(U)−𝒩(0)‖_{H^{k−1}}·‖U‖_{H^{k+1}}`, and the `H^{k−1}` factor is
estimated tower-directly by "the towers' `range (i+2)` window at
`i = k−1`", which "reaches state jets `j ≤ k`".  §6.3 also CORRECTS §6.1's
parenthetical: the window is `≤ k`, not `≤ k+1`.  With the stopped rungs
`k = 3, 4, 5` (§6.1) the tower is consumed at `i ≤ k−1`, so
**`i* = 5 − 1 = 4`** — not `i ∈ {4,5,6}`.

Refinement the planner should record: class 3 needs `q ≥ 3` factors each of
order `≥ 2` at total weight `i + 2`, i.e. `i + 2 ≥ 6`.  At `i* = 4` the
inventory is therefore the SINGLE monomial `c = (2,2,2)`, i.e. `∫ |∇²P|⁶`.
The +1 brick is real but is a one-case brick, not a general interpolation
theory.

### What landed (three new files, all built)

1. `Analysis/Sobolev/MarkedTupleGrid.lean` — the combinatorial layer.
   `markGrid b u w` = the antidiagonal window that REMEMBERS `u` explicit
   factors of weight `≥ 1` (total weight `≤ w + u`).  The load-bearing
   fact is `markGrid_mul`: **the marks ADD under multiplication, at the
   SAME constant `antidiagonalTupleGridWindowMulConst` the unmarked window
   already pays** — the marked currency is free.  Plus `markOne_of_term`,
   the entry shape every `topSeparated` producer already delivers.
   Sorry-free, census clean.
2. `Analysis/Sobolev/TensorHilbert/TameMarkWin.lean` — the arm calculus and
   the `L²` bridge.  `HasMarkWin g₀ P X u K ↔ ∀ i x, |∇ⁱX|²(x) ≤ K i ·
   markGrid (bP x) u i`.  `markFold`/`mkApp` (marks add), `mkOfBnd`,
   `mkOfWin`, `mkOfTop`, and the usual `mkAdd/mkSub/mkSmul/mkNeg/mkMono/
   mkCongr/mkReindex/mkSlotExt`.  **No cap is spent anywhere in the
   calculus**, so the constants are state-free.  Then `markMon` (the
   four-way monomial dispatch) and `markJet` (the bridge out).
3. `Analysis/Sobolev/TensorHilbert/TameArmJets.lean` — the arms.
   `connDiffMark`, `ricciAAMark`, `ricciAAJet`.

### The decisive finding

**The marked window the tame currency needs is not new geometry — the tree
already proves it and then throws it away.**  Every order-one arm has a
`topSeparated` producer presenting `∇ʲX` as

`Ktop·|∇^{j+1}P|² + Kc j·∑_{k<j}|∇^{j−k}P|²·grid(bP)(k+1)`,

every monomial of which carries an EXPLICIT state jet of order `≥ 1` at
total weight exactly `j+1`.  That IS a once-marked window (`mkOfTop`).  The
radius-free window `atgw bP (j+2)` that the tree then weakens to is NOT: it
also admits the bare constant and the unaccompanied top jet `|∇^{j+1}P|²`,
which is precisely the out-of-budget monomial.  So No. 138-executor's
estimate that the per-arm expansions are "the bulk of the remaining work"
was too pessimistic for arms whose factors have `topSeparated` producers.

### `A·A`, end to end

`ricciAAMark` (pointwise): `|∇ⁱ(ricciAAArm g₀ g₁)|²(x) ≤ K i · markGrid
(bP x) 2 i` with `K` **state-free** — no `Λ`, no radius in the statement at
all.  A one-for-one re-run of `ricciAACap` with `capOfArm ↦ mkOfTop`.
Monomial-class inventory: every monomial has two explicit `∇P` factors and
total weight `≤ i+2`; after integration, classes 1 (`gridIntPull`) and 2
(`gridIntGrad`) cover everything except the residual, which is class 3.

`ricciAAJet` (the deliverable):
`‖∇ⁱ(ricciAAArm)‖² ≤ (K₀ i + K₂ i·∑_{j<3}‖∇^{1+j}P‖²)·(1 + ∑_{j<i+2}‖∇ʲP‖²)`
— constants BEFORE the state, no `R₀`, no opaque cap, no higher power, no
`N`, exactly one power of `‖P‖²_{H³}`.  Extra hypothesis: the δ-anchor
`|P|_∞ ≤ 1` (at `finrank = 3` implied by `‖P‖_∞ ≤ finrank/3`).
Compare `ricciAACap`+`capJet`: same LHS, constant of `Λ`-degree `3(i+1)`.

### Where the session stopped: `lc0VB`

`lc0VB = 2•(lc0RiemLive ⋆ lc0VBPass)`, `lc0VBPass = vbMcdArm ⋆
ipLowCc(wOmega g₀ g₁ g₀)`.  `lc0RiemLive` enters at `u = 0` for free.  The
two other factors need `u = 1` and only have unmarked windows
(`b4_mcd_atgw`, `b4_wOmega_atgw`, both `atgw bP (·+2)`).  Both bottom out
in `rfns_iCG_wXi_atgw_rf` (`DeTurckVFJetRadiusFree.lean:1050`), which its
own docstring says goes through the `connDiffLoweredCc ↔ connDiffSection`
fibre-norm identity — i.e. through exactly the arm `connDiffMark` now
marks.  **Next brick = a marked `wXi`.**  One genuine mathematical check
first: `rfns_iCG_wXi_atgw_rf` folds a "`T`-free per-order constant" for the
`g_bg` half, which is `u = 0` and would break the mark count; at the
`lc0VB` call site `g_bg = g₀`, where it should vanish identically — verify
that before building.  If it vanishes, the rest of the chain (`mcd`,
`wOmega`, `ipLowCc`, `vbSplit`, `lc0VB_eq_app`) is mechanical.

### The single frontier

`gridIntHigh` (`TameMarkWin.lean`), `sorry`'d, statement matched exactly to
the residual case so no surgery is needed at the call site: `c₁, c₂ ≥ 2`,
tuple weight `k ≥ 1` with no entry `= 1`, total weight `m+1`.  Inventory
and the "why it is true / what is missing" (interpolation BETWEEN the two
available two-point GN scales) are in the docstring and `TameMarkWin.md`.
First occurs at `m = 5`, i.e. tower order `i = 4`.

### Verification

Focused checks of all three new files: green, no errors, no warnings.
Targeted builds `+…MarkedTupleGrid` (1019 jobs), `+…TameMarkWin` (9538),
`+…TameArmJets` (9572): all green.  Axiom census of every new public
declaration: `markGrid_mul`, `markGrid_mono`, `markOne_of_term`,
`markFold`, `mkApp`, `mkOfTop`, `mkOfWin`, `mkOfBnd`, `connDiffMark`,
`ricciAAMark` — **clean** (`[propext, Classical.choice, Quot.sound]`);
`markMon`, `markJet`, `ricciAAJet` carry `sorryAx` through `gridIntHigh`
and through nothing else.  Memory guard held throughout.

### Honest denominators

`selfLow_jet_quad`: **still 0%** — not stated in Lean.  Its dedicated
machinery: was ≈ 40–45%, now ≈ 60–65% (the marked currency + the `L²`
bridge exist and are reusable for all five summands; one of five summands
is closed end-to-end).  `lowreg_loMass` 0% (machinery ≈ 30%).  `(N)` 0%
(stated, `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at :98).  Whole
HCG compactness project ≈ 3%.  Remaining tame-C0 bricks: 2–3 (the four
other summands, of which `lc0VB`/`lc0AMix` share the `wXi` brick, plus the
`selfLow_jet_quad` assembly) **+1** for `gridIntHigh` (confirmed on-path).

## Planner update No. 140 (2026-08-04) - SESSION 2 ACCEPTED (A·A CLOSED; i* = 4; CLASS 3 = ONE MONOMIAL); SESSION 3 (MARKED wXi) DISPATCHED

Acceptance: `ricciAAJet` closes the A·A arm end-to-end at the exact
deliverable shape (constants before `T`, state-free `K` in the marked
window, no `R₀`/opaque cap/higher power/`N`); the marked-currency
layer (`MarkedTupleGrid.lean` — `markGrid_mul`: marks ADD at the SAME
constant, the marked currency is free; `TameMarkWin.lean` —
`HasMarkWin` + combinators) is census-clean except the three
declarations carrying sorryAx through the DECLARED one-case frontier
`gridIntHigh` (:422–458).

Rulings:
- **i* = 4 CONFIRMED** (from PSTOP §6.3's budget check — the window
  is ≤ k, correcting §6.1's parenthetical; stopped rungs k = 3..5 ⟹
  tower orders ≤ 4).  Class 3 stays ON-PATH but collapses to the
  SINGLE monomial `(2,2,2)` = `∫|∇²P|⁶` — `gridIntHigh` is a
  one-case brick, not an interpolation theory.  №139's +1 stands at
  minimal size.
- **The topSeparated finding is RATIFIED and recorded as over-count
  exhibit SEVEN (throw-away flavor)**: every order-one arm's
  `topSeparated` producer already proves the once-marked window and
  the tree then WEAKENS it to `atgw` (which admits the unaccompanied
  top jet — the out-of-budget monomial).  №138-executor's "per-arm
  expansions are the bulk" was too pessimistic wherever
  `topSeparated` exists.  Rule: before re-deriving an arm expansion,
  check its `topSeparated` producer for the marked form.
- `lc0VB` blocker accepted as ONE named missing input: the marked
  `wXi` (`rfns_iCG_wXi_atgw_rf`, `DeTurckVFJetRadiusFree.lean:1050`),
  with the mandated pre-check that the `g_bg`-half's `T`-free
  constant vanishes identically at the call site (`g_bg = g₀`).

DISPATCHED: SESSION 3 — the marked `wXi` brick (pre-check first),
unlocking `lc0VB` AND `lc0AMix` (shared), plus as many of the
remaining summands as budget allows.

Honest denominators: `selfLow_jet_quad` 0% (machinery ≈ 60–65%);
`lowreg_loMass` 0% (≈ 30%); (N) 0%; whole HCG ≈ 3%; tame bricks
remaining 2–3 (+1 one-case).  Route-error counter: **2/3**.

## Executor report No. 140-executor (2026-08-04) - TAME C0 BOTTOM SESSION 3: PRE-CHECK PASSES BY VANISHING; `wXi` BRICK BUILT; `lc0VB`, `lc0AMix` AND `lc0Riem` ALL CLOSED END-TO-END

**Verdict: COMPLETE on the mandate, plus one of the two stretch
summands.**  Marked `wXi` built; `lc0VB` and `lc0AMix` closed to their
tame `L²` jet bounds; `lc0Riem` also closed, and it came out fully
axiom-clean.  The lieCov pair was NOT attempted — scoped below as its own
brick.  Route-error counter unchanged (**2/3**).

### PRE-CHECK (planner-mandated) — the `g_bg` term does not merely fold small, it is ZERO

`rfns_iCG_wXi_atgw_rf` bounds `wXi`'s `g_bg` half by an arbitrary sup
constant `SBg l` from `exists_bound_riemannianFiberNormSq_smoothCcTensor`.
At the call sites `g_bg = g₀`, and there **the half is the zero tensor**:
`wXi g₀ g₁ g_bg = connDiffLoweredCc g₀ g₁ − connDiffLoweredCc g₀ g_bg`,
and `wXi_self_eq` (`LieCorr0VBRefold.lean:40`) already proves
`wXi g₀ g₁ g₀ = connDiffLoweredCc g₀ g₁` as an EQUATION OF TENSORS.
Call sites confirmed: `lc0VBFormRF` (`LieCorr0VBRefold.lean:110`) uses
`ipLowCc g₀ (wOmega g₀ g₁ g₀)`; `ShortTime/LowRegBgH2.lean:653/710/803`
uses `lc0AMix g₀ g₁ g₀`.  So nothing had to be estimated away — the
marked `wXi` is `connDiffMark` transported along `wXi_self_eq` through
the valence bridge `connLow_rfns`, **at the same state-free constant**.
Over-count exhibit SEVEN in its sharpest form.

### What landed

One new file `Analysis/Sobolev/TensorHilbert/TameLieCorrJets.lean` (640
lines), plus two additions to `TameMarkWin.lean` and two `private`
removals upstream.

New public declarations, with mark counts:
`wXiMark` (u=1) · `mcdMark` (u=1) · `wOmegaMark` (u=1) · `ipLowMark`
(preserves u) · `lc0VBMark` (u=2) · `lc0VBJet` · `lc0AMixMark` (u=2) ·
`lc0AMixJet` · `lc0RiemMark` (u=0) · `lc0RiemJet`; in `TameMarkWin.lean`
`mkIter` (the marked `capIter`) and `markJet0` (the `u = 0` bridge out).

All three `Jet` endpoints have exactly the `ricciAAJet` shape —
`(K₀ i + K₂ i·∑_{j<3}‖∇^{1+j}P‖²)·(1 + ∑_{j<i+2}‖∇ʲP‖²)`, constants
before the state, no `R₀`, no cap, one power of `‖P‖²_{H³}`, δ-anchor
`|P|_∞ ≤ 1` the only extra hypothesis.  `lc0RiemJet` has `K₂ = 0`.

### Three findings the planner should record

1. **`markJet0` (the `u = 0` bridge) is nearly free and is already a
   strict improvement.**  `markGrid b 0 n = atgw b (n+1)` *definitionally*,
   so `atgwToJet` at `w = 1` lands a LINEAR summand on `range (n+1)`.
   The tree's own radius-free route for the same summand
   (`lc0Riem_perOrder_rf`) lands on `range (i+3)` — one order over
   budget.  Consequence: **linear summands never touch `markMon`, hence
   never touch `gridIntHigh`**, and `lc0RiemMark`/`lc0RiemJet` are
   axiom-clean.
2. **`lc0AMix` is quadratic ONLY at `g_bg = g₀`, and this is sharp.**  At
   a general DeTurck background `wXi g₀ g₁ g_bg` keeps a state-free
   summand, so the outer `mcd(·, g_bg)` factor is `u = 0` and the
   five-factor product is `u = 1` — affine, not quadratic, in `∇P`.  The
   endpoint is therefore stated at `g_bg = g₀`, which is what the
   consumer `LowRegBgH2.lean` uses.  A general-`g_bg` version would need
   a `markJet1`; that bridge is mathematically available (a `u = 1`
   window's worst monomial is a lone `|∇^{n+1}P|²`, inside
   `range (n+2)`) but is NOT built and nothing on the current path needs
   it.  Flagging in case the (N) assembly later wants general `g_bg`.
3. **A public theorem may mention a `private` constant in its type.**
   `private` restricts name resolution, not the term.  This let the
   upstream edit be TWO keyword deletions (`b4_mcd_eq`, `b4_phi_atgw` in
   `LieCorr0CoeffDiffRadiusFree.lean`) with the correction operator
   `b4Phi` and its permutations staying private — no new content, no
   line growth on an already over-limit (3419-line) file, no import
   change.  The consumer states its helper with the operator universally
   quantified and lets unification fix it.

### The single frontier — unchanged

`gridIntHigh` (`TameMarkWin.lean`), one case, `(2,2,2)` i.e. `∫|∇²P|⁶`,
first at tower order `i = 4`.  No new frontier was declared this session.

### Verification

Focused check of the new file: green, no errors, no warnings.  Targeted
builds `+…LieCorr0CoeffDiffRadiusFree` (9545 jobs), `+…TameMarkWin`
(9538), `+…TameLieCorrJets` (9574): all green.  Axiom census of every new
public declaration: `mkIter`, `markJet0`, `wXiMark`, `mcdMark`,
`wOmegaMark`, `ipLowMark`, `lc0VBMark`, `lc0AMixMark`, `lc0RiemMark`,
`lc0RiemJet`, and the two newly-public `b4_mcd_eq`, `b4_phi_atgw` —
**clean** (`[propext, Classical.choice, Quot.sound]`); `lc0VBJet` and
`lc0AMixJet` carry `sorryAx` through `gridIntHigh` and nothing else.
Memory guard held throughout (phys-free never below 5.5 GB).

### Not attempted: the lieCov pair (scoped for the next session)

`deTurckLieCovDerivArmField − edgeLiePairFam` is a genuinely different
shape and should be its own brick, not a repeat of this session.  Its
residual identity is `lieCov_residual`
(`RiemannCoefficientPalatiniRefold.lean:9176`):
`(−1)•appCcRS g₀ 2 6 2 (lieCovPair g₀ g₁) (rsDomDomCongr … slotExtendIter
0 4 2 (lieCovR4 g₀ T …))`, where `lieCovR4` carries `∇²T` — ONE factor of
order two, not two factors of order one — and it is stated in the
`boundedFactorGridWindow` currency, not `atgw`.  Expect a `u = 2` window
whose marks have orders `(1, 2)`; the first thing to check is whether
`markGrid`'s monomial inventory at that shape stays inside classes 1–3.
Also still open: the `∇A ⋆ ∇T` arm of `ricciGoodLow`.

### Honest denominators

`selfLow_jet_quad`: **still 0%** — not stated in Lean.  Its dedicated
machinery: was ≈ 60–65%, now ≈ 80% (four of the five summands' arms are
closed end-to-end at the deliverable shape — `ricciAAArm`, `lc0VB`,
`lc0AMix`, `lc0Riem`; the marked currency now has both ends of the bridge
out, `markJet0` and `markJet`).  `lowreg_loMass` 0% (machinery ≈ 30%).
`(N)` 0% (stated, `Evolution/ExtendViaUniqueness.lean:80`, `sorry` at
:98).  Whole HCG compactness project ≈ 3%.  Remaining tame-C0 bricks:
**2** (the lieCov pair + the `ricciGoodLow` `∇A ⋆ ∇T` arm) **+ 1**
(the `selfLow_jet_quad` assembly) **+ 1** (`gridIntHigh`, one case).

## Planner update No. 141 (2026-08-04) - SESSION 3 ACCEPTED (4/5 FAMILIES AT SHAPE; g_bg PRE-CHECK PASSED MAXIMALLY); SESSION 4 DISPATCHED

Acceptance: the mandated pre-check passed in the strongest form —
the `g_bg` half is IDENTICALLY ZERO at every call site
(`wXi_self_eq`, `LieCorr0VBRefold.lean:40`; call sites verified),
so the marked `wXi` required NO new estimate (over-count exhibit
seven, same throw-away flavor).  `lc0VB`, `lc0AMix` (sharp at
`g_bg = g₀` — quadratic ONLY there; general-`g_bg` would be affine
and need a `markJet1`, which nothing on the path needs), and
`lc0Riem` (fully clean, `K₂ = 0`) all CLOSED at the deliverable
shape.  `markJet0` finding recorded: `markGrid b 0 n = atgw b (n+1)`
definitionally, so LINEAR summands land on `range (n+1)` — beating
the tree's own `lc0Riem_perOrder_rf` (`range (i+3)`) and never
touching `gridIntHigh`.  Two upstream `private` removals
(`b4_mcd_eq`, `b4_phi_atgw`) with zero content/import change.
Census: clean except `lc0VBJet`/`lc0AMixJet` via `gridIntHigh`
alone.

DISPATCHED: SESSION 4 — the two remaining arms: the lieCov pair
(genuinely different shape — `lieCovR4` carries ONE order-two factor
`∇²T`, stated in the `boundedFactorGridWindow` currency, not
`atgw`; the marked-currency treatment of a single `c = 2` factor is
the session's design question) and the `ricciGoodLow` `∇A ⋆ ∇T`
arm; goal = leave only the `selfLow_jet_quad` assembly + the
`gridIntHigh` one-case.

Honest denominators: `selfLow_jet_quad` 0% (machinery ≈ 80%);
`lowreg_loMass` 0% (≈ 30%); (N) 0%; whole HCG ≈ 3%.  Route-error
counter: **2/3**.

## Executor report No. 141-executor (2026-08-04) - TAME C0 BOTTOM SESSION 4: lieCov PAIR CLOSED END-TO-END; `∇A ⋆ ∇T` NOT CLOSED, BLOCKER IS A MISSING PRODUCER

**Verdict: one of the two arms closed, one not.**  The lieCov pair is at the
deliverable shape.  The `ricciGoodLow` `∇A ⋆ ∇T` arm (`ricciDALow`) is NOT,
and I am naming the blocker rather than papering it.  Route-error counter
unchanged (**2/3**); no new frontier was declared and no `sorry` was added.

### Where the session failed (leading with it)

`ricciDALow = daContr (dagLowOp ⋆ ∇P)` needs its `(0,4)` argument at `u = 2`,
level `i`.  `∇P` is free (`mkOfDP`, built and green, `u = 1`, constant `1`).
The other factor is `dagLowOp = permCoeff(daPermA) ⋆ covGrad 3 3 (connLowOp
g₀ g₁)`, and the ONLY window the tree has for `connLowOp` is `clAtgw`, an
`atgw bP (i+1)` window.  Read at order `i+1` that is `u = 0` at level
**`i+1`** — one level over budget — so `G` lands at `u = 1` level `n+1` and
the arm integrates onto `range (n+3)`.  A level, once lost, is not
recoverable: demoting a mark COSTS a level, and the level is the budget.

The missing input is one `topSeparated`-shaped radius-free producer

```
|∇ⁱ(covGrad 3 3 (connLowOp g₀ g₁))|²(x)
    ≤ Ktop·bP(i+1) + Kc i·∑_{k<i} bP(i−k)·atg(bP)(k+1)
```

i.e. exactly `mkOfTop`'s input, giving `u = 1` at level `i`.  It is TRUE:
`connLowOp g₀ g₀` is assembled from `g₀`, `g₀⁻¹` and permutations
(`connLowOp = permCoeff(lowPerm) ⋆ (slotInsertEndoCc 2 (fullRaisedEndoField)
⋆ koszulOp)`), hence `∇^{g₀}`-PARALLEL, so `∇(connLowOp g₁) = ∇(connLowOp g₁
− connLowOp g₀)`, and by `sieSplit` the difference is `perm ⋆
slotIns(gInvDiff) ⋆ koszul`, whose derivative carries an explicit `∇P`.  In
Lean the brick decomposes into exactly three obligations:

1. `covGrad (permCoeff g₀ ρ) = 0` and `covGrad (koszulOp g₀) = 0`;
2. `covGrad (slotInsertEndoCc s (fullRaisedEndoField g₀ g₀)) = 0` — the
   frozen half of `sieSplit`;
3. a `topSeparated` window for `covGrad (gInvDiffRaisedEndoField g₀ g₁)`,
   whose exact-weight producer
   `rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le`
   already exists.

Classification: **missing groundwork/API** (a parallelism producer) — not a
mathematical obstruction, not combinatorics.  One focused brick, not a
session.

Two routes were tried and ruled out before stopping:

* **Leibniz through `connLow_app`.**  `∇A ⋆ ∇T = ∇(connDiffLowered) − A ⋆
  ∇²T`.  Both summands individually have a lone `|∇^{i+2}P|²` head, so each
  is `u = 1` at level `i+1` — strictly WORSE than their difference, and
  unlike the lieCov arm there is no exact cancellation identity here.
* **A `markJet1` bridge.**  Cheap, and worth banking:
  `markGrid b 1 n ≤ (n+1)²·atgw b (n+2)` (each `b(c+1)·atg b k ≤ atg b
  (c+1+k)` by `single_factor_mul_antidiagonalTupleGrid_le`, total weight
  `≤ n+1`), and `atgwToJet` at `w = 2` then lands on `range (n+2)` — the
  deliverable budget, with NO `Λ₁` at all.  So a `u = 1` arm at level `n` is
  perfectly tame; it does not rescue `ricciDALow`, whose problem is the
  LEVEL, not the mark count.  For the planner: **affine arms are free.**

### The decisive finding: the dispatched design question does not exist

The brick was dispatched on the reading that `lieCovR4` carries ONE
order-two factor `∇²T`, and that marking a `c = 2` factor was the session's
design question.  That reading is wrong.  `lrCurvF g₀ T = appCcRS (lrRiemW1
g₀) T + appCcRS (lrRiemW2 g₀) T` (`RiemannCoefficientPalatiniRefold.lean:7936`),
and its evaluation `lrCurvF_unitModel_apply` is `T(Rm(g₀)(m0,m1,m2), m3) +
T(m2, Rm(g₀)(m0,m1,m3))`: the **fixed background** Riemann tensor contracted
with `T` ITSELF.  Zero covariant derivatives of the state, linear,
state-free coefficient.  `lieCovPair` is likewise order zero (a pure double
moving trace, `ptAtgw`).  The `∇²T` belongs to `edgeLiePairFam`, the
SUBTRACTED edge, and it is precisely what `lieCov_residual` cancels.
**Over-count exhibit EIGHT**, third in three sessions: read the object's own
evaluation lemma before pricing a derivative order.

The rule the session did settle, since the planner asked: re-reading
`markGrid b (u+1) w = ∑_{c ≤ w} b(c+1)·markGrid b u (w−c)`, a mark is any
factor of order `≥ 1`, not order exactly one.  An order-two factor is the
`c = 1` summand — legal, costing two units of LEVEL.  **Marks are free at
any order; levels are not.**  That is the whole content of the `c = 2`
question.

### The one genuine structural point

The two halves of the residual have DIFFERENT mark counts (`u = 0` curvature
head, `u = 2` `lrQuadF`), and `mkAdd`/`mkSub` need a common `u`.  So the arm
must be split at the TENSOR level.  It splits cleanly along the
sub-linearity of the three structural maps, all already in `PairTrace.lean`:
`slotExtend_sub_cc` (twice) → `rsDomDomCongrSection_sub_cc` →
`appCcRS_sub_right_cc`, after which `neg_smul, one_smul, neg_sub` turns
`(−1)•(A − B)` into `B − A`.  The halves are then bounded by `markJet0` and
`markJet` separately and recombined with `norm_sub_le`.  Reusable pattern:
**an affine-plus-quadratic arm is split, not demoted.**

### What landed

`TameMarkWin.lean` (1062 → 1137 lines), four calculus entries, all
axiom-clean: `mkOfP` (the state itself, `u = 0`; the δ-anchor is genuinely
needed, since `markGrid bP 0 0 = 1` exactly), `mkOfDP` (`∇P`, `u = 1`,
constant `1`, no hypothesis — the free half of the `ricciDALow` arm, banked
for the next brick), `mkDdc`/`mkDdc0` (output-slot permutation is a
marked-window isometry; the currency had `mkReindex` for source slots only,
which blocked every Palatini normal form).

`SelfLowArmCaps.lean` (1012 → 1521 lines, one import added, nothing
de-privatised — the private producers `ptAtgw`/`revEndoAtgw` live in this
file, which is why the marked layer belongs here and not in the Sobolev
tree): `pairMark` (`u = 0`), `curvMark` (`u = 0`), `omegaMark` (`u = 1`),
`lrQuadMark` (`u = 2`), the private `extSub`, and the endpoint `lieCovJet`.

`lieCovJet` has exactly the `ricciAAJet` shape — `(K₀ i + K₂ i·∑_{j<3}
‖∇^{1+j}P‖²)·(1 + ∑_{j<i+2}‖∇ʲP‖²)`, constants before `T`, no `R₀`, no cap,
**no `s`**, one power of `‖P‖²_{H³}`, δ-anchor `|P|_∞ ≤ 1` the only extra
hypothesis.  The `s`-factor trick is load-bearing exactly as in `lieCovCap`:
`curvSmul` turns `(-(s/2))•lrCurvF T` into `(-(1/2))•lrCurvF P`, and only
the perturbation `P = s•T` has a δ-anchored order-zero jet — which is what
`mkOfP` consumes.

### Verification

Focused checks of `TameMarkWin.lean` and `SelfLowArmCaps.lean` green (the
only `sorry` warning is the declared `gridIntHigh` frontier).  Targeted
builds `+…TensorHilbert.TameLieCorrJets` and `+…DeTurck.SelfLowArmCaps`
green.  Axiom census: `mkOfP`, `mkOfDP`, `mkDdc`, `mkDdc0`, `pairMark`,
`curvMark`, `omegaMark`, `lrQuadMark` — clean; `lieCovJet` carries `sorryAx`
through `gridIntHigh` and nothing else (its unmarked half, via `markJet0`,
is clean; only the `lrQuadF` half reaches `markMon`).  `lieCovCap` and
`ricciDACap` unchanged and still clean.

### Census (explicit)

Remaining tame-C0 work: **1** arm (`ricciDALow`, blocked on the `covGrad
connLowOp` parallelism producer) **+ 1** assembly (`selfLow_jet_quad`)
**+ 1** frontier (`gridIntHigh`, one case, `(2,2,2)`, first at tower order
`i = 4`).  It did NOT drop to [assembly + `gridIntHigh`] as the dispatch
hoped.

### Honest denominators

`selfLow_jet_quad`: **still 0%** — not stated in Lean.  Its dedicated
machinery: was ≈ 80%, now ≈ 88% (five of the six summands' arms closed
end-to-end at the deliverable shape — `ricciAAArm`, `lc0VB`, `lc0AMix`,
`lc0Riem`, lieCov; `ricciDALow` is the sixth and is blocked on one named
producer).  `lowreg_loMass` 0% (machinery ≈ 30%).  `(N)` 0% (stated,
`Evolution/ExtendViaUniqueness.lean:80`, `sorry` at :98).  Whole HCG
compactness project ≈ 3%.

### What the next brick should be told

Build the parallelism producer for `covGrad (connLowOp g₀ g₁)` in the
DeTurck low-base layer (obligations 1–3 above).  Then `ricciDAMark` is a
one-for-one re-run of `ricciDACap` with `capOfArm ↦ mkOfTop`, `capOfDP ↦
mkOfDP`, `capDdc`/`capDdc0`/`capIter ↦ mkDdc`/`mkDdc0`/`mkIter` — every
other factor in that tree (`permCoeff daPermA`, `mvPairTraceOp`,
`slotInsertEndoCc (fullRaisedEndoField)` via `endoAtgw`) is already `u = 0`
at level `i` through `mkOfBnd`/`mkOfWin`.  After that the tame C0 bottom is
[assembly + `gridIntHigh`].
