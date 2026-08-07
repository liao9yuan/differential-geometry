# UNIF_EXISTENCE_PLAN6 — the (N) campaign ledger, №167+

Continuation of `UNIF_EXISTENCE_PLAN5.md` (№142–166; PLAN4 = №126–141,
PLAN3 = №104–125, PLAN2 = №70–103, PLAN = №1–69 — all frozen history).
Rolled 2026-08-05 at the 3000-line cap (PLAN5 closed at №166).  One ledger
entry per landed/ruled brick; re-read this file's TAIL immediately before
every append (concurrent-append collisions are routine).

## State at rollover (2026-08-05, after №166)

- **Endgame target**: (N) `ricci_flow_unif_existence`
  (`Evolution/ExtendViaUniqueness.lean:80`, sorry `:98`) — **0%**.  Sole
  front-2 Lean sorry: `lowreg_loMass` (`ShortTime/LowRegAllOrderJet.lean:1052`,
  sorry `:1065`) — theorem **0%**, dedicated machinery ≈ **85%** (№168).
  Whole HCG ≈ **3%**.  Route-error counter **1/3** (№155; №152 user reset).
- **RUNG 3 IS PROVED AND ACCEPTED** (№164/№165): `lowregRung3`
  (`ShortTime/LowRegRungThree.lean`) — N-uniform `E₃ ≤ Φ` on any trajectory
  satisfying its hypothesis block, adapter H as explicit hypothesis naming
  its own constants, `hL2H3` carried as honest input.  Slot map = the Lean
  theorem `armLadderAbs`; the E₄ whitelist held.
- **Fatou stage architecture (№165, adopted)**: instantiate the rung's
  ∀-quantified trajectory at the PROJECTED sequence's mode coordinates
  `c N t i := perModeConv λᵢ (timeModeCoeff (fseq N) i) t` — JOINT-IDENT
  dissolved, no ODE-uniqueness, `galTamePerMode`/`lowregGalSol` off the
  critical path (banked).  The rung's stage role = Fatou's `hbound`;
  `galTameForce_eq`'s `hc` comes from package conjunct 2.
- **F-ladder — THE FATOU STAGE IS CLOSED (№168)**: F1 GAP-CERT ✓ (№166 —
  third widening; all 7 certificate/tame exports landed) → F2 FATOU-IDENT ✓
  (№167 — `ShortTime/LowRegFatouIdent.lean`; all three trajectory conjuncts
  land, endpoint `lowregFatouE3` sorry-free) → F3 FATOU-L2H3 ✓ (№168 —
  `lowregL2H3` in the same file discharges `hL2H3` at a free forcing bound;
  `lowregFatouPack`'s `∀ Bd` antecedent **deleted**, so the pack is now
  conditional on GAP-ADAPTH alone; no fourth widening needed) → F4
  FATOU-ASSEMBLE ✓ (№168 — new `ShortTime/LowRegFatouMass.lean`, endpoint
  `lowregMassLow`: the σ ≤ 3 spectral-mass bound on the LIMIT forcing, at
  `lowreg_loMass`'s **literal** conclusion object, gated on GAP-ADAPTH).
  Next: rungs 4–5 (σ > 3) and GAP-ADAPTH.
- **Registered honest inputs / follow-ups** (do not silently consume):
  - GAP-ADAPTH: the rung's absorption inequality
    `Ctop₂·Cδ + Kr2·R + Kr1·R + ε < 1` — discharge = producer-side smallness
    audit of `lowregStateRad` vs the produced constants, with GAP-ORDER.
  - GAP-ORDER: hoist the rung's ∃-constants above the class parameters
    (mechanically available from the same proof; needed by front 3).
  - ~~`hL2H3`~~ — **DISCHARGED** (№168, `lowregL2H3`).
  - ~~`D`/`hzero`/`hTτ` package exports~~ — **not needed**; F3 consumed none
    of them (№168).  The package stays at three widenings.
  - σ-scope: the Fatou stage delivers σ ≤ 3 only (endpoint `lowregMassLow`,
    №168); ∀σ `lowreg_loMass` stays gated on rungs 4–5 (general-k regrouping
    + a dissipation-export engine variant) and on GAP-ADAPTH.
- **Acceptance discipline** (standing): every substantive brick gets a
  read-only adversarial panel before its outputs are consumed; interface
  bricks whose consumer is the very next brick may defer into that brick's
  panel (№163/№165 precedent — F1 defers into F2's).  Planner pricing
  arithmetic is panel-checked before being ruled (№157).  Executor dispatches
  carry the re-sweep-before-writing rule (exhibits now at SEVENTEEN).
- **Verification discipline**: persisted census — every new public
  declaration gets a `#print axioms` line in `ShortTime/ScratchIdentCensus.lean`
  (ShortTime side) or `DeTurck/ScratchC01Census.lean` (analysis side), run
  green (`[propext, Classical.choice, Quot.sound]` only).
- **User-side standing item**: the ENTIRE campaign delta (incl. the proved
  `lowregRung3` and every load-bearing untracked file) is uncommitted —
  checkpoint commit strongly recommended.

---

## 190. Structural tame chain and class-first low bounds closed (2026-08-06)

The structural chain left open in section 189 is now complete.  The following
dimension-three, class-first declarations are focused-check green, directly
exported, and have axiom audits containing only `propext`,
`Classical.choice`, and `Quot.sound`:

- `rem_h1_unif` combines the uniform top, lower, RHS0, and RHS1 path packets
  with the exact mixed-remainder split.
- `smoothN_h1_unif` and `coreN_tame_unif` transport that estimate through the
  spectral smooth nonlinearity and dense core.
- `coreN_outer_unif` freezes the affine coefficients at an outer radius, and
  `lowRegN_outer_unif` performs the dense extension to the complete lower-state
  ball without changing the three-arm constants.
- `exists_lowBounds` combines `exists_lowRealize`, `exists_lowZero`, and the
  dense tame packet into one literal `LowRegBoundData` selected before the
  class metric.
- `lowreg_bounds_unif` projects that strong packet to the requested
  `IsLowBoundsCap` common-envelope interface.
- `lowreg_solve_unif` composes that envelope with `unif_solve_of_caps`, giving
  one positive horizon and an `IsLowSolveBg g gBase` fixed-point output for
  every class metric and every smaller positive time.

This closes the producer design requested by the consult: all scalar choices
are now made before `g`, the DeTurck background is the fixed `gBase`, and the
varying-metric input stops at background-covariant metric jets through order
three.  No all-rung gate, new foundational class, or consumer-side assumption
was introduced.

The public `(N)` theorem and `ricci_flow_interior_restart` now carry the honest
dimension-three hypothesis, propagated through their only Lean consumer in
`MaximalTime`.  The next genuine frontier is no longer horizon selection or a
consumer wrapper: it is a horizon-preserving realization/bootstrap theorem
from `IsLowSolveBg g gBase` to a smooth geometric Ricci--DeTurck family with
`JointChartGramSmooth`.  Existing `lowreg_joint_of_re` cannot be called
directly because its all-order packet is self-background and materially
richer.  After that bridge, the already proved DeTurck gauge removal and final
`ricci_flow_unif_existence` assembly are local.

**Honest denominators.**  Every declaration listed above: **100%**.
The actual producer `lowreg_bounds_unif` and low solver
`lowreg_solve_unif`: **100%**.  Their dedicated
low-regularity tame/realization/zero machinery: **100%**.  The downstream
`lowreg_dt_unif`: **0%** until its theorem is stated and proved from this
packet; `ricci_flow_unif_existence`: **0%**; whole HCG theorem closure remains
approximately **3%**.  Campaign changes remain uncommitted.

---

## 191. Same-horizon H2 representative exported from the uniform low solve (2026-08-06)

The completed class-first tame/bounds chain was replayed under the current
resource discipline: `MetricLoweringTower`, `morreyRS_unif`,
`coreN_tame_unif`, and `LowRegUnifBounds` all pass focused checks with one Lean
thread and the 6 GB memory cap, with no overlapping Lean process.

`lowSolve_cross` is the first concrete producer inside the remaining bootstrap.
From the supplied fixed-background `IsLowSolveBg` it constructs the canonical
`duhamelCross` on the original horizon, identifies its lower carrier with the
given maximal-regularity solution, and promotes the almost-everywhere lower-
state bound to an every-time `H2` bound on `Icc 0 T` by `crossRepr_ball`.
The theorem is focused-green.  It introduces no new assumption and does not
reselect or shorten the common time.

This is not yet an order-two maximal-regularity lift.  The next honest producer
must construct that fixed-background adjacent-scale lift on the same horizon;
only then can the existing all-order mass/jet assembly be generalized from
self-background `(g,g)` to `(g,gBase)`.

**Honest denominators.**  The four replayed class-first producers and
`lowSolve_cross`: **100%**.  The fixed-background order-two lift and
`bg_packet_of_solve`: **0%**.  Consequently `ricci_flow_unif_existence` remains
**0%** theorem completion; whole HCG project remains approximately **3%**.

---

## 192. Bootstrap interface corrected; arbitrary-background AMix H2 pair landed (2026-08-07)

The previous claim that the `bg_packet_of_solve` interface was settled is
withdrawn.  `IsLowSolveBg` alone does not carry the constants or the certificate
needed by the implemented adjacent-scale contraction.  In particular, the
lift route requires a full background-aware high/low `A1` affine packet,
background-aware `A2` contraction data, a force margin, and
`T ≤ lowregLiftHorizon' c Z`.  The class-first time must be capped by this lift
horizon before the class metric varies.  The corrected design will package
those witnesses explicitly and separate low-solve-to-realization from
realization-to-closed-slab-bootstrap.

The first genuine analytic brick of that correction is now complete:

- `kappa_pair_h2` proves the exact self-background Koszul two-state estimate;
- `pbLow_h2_mul` exposes the linear fixed-background pairing constant at the
  coefficient-jet layer;
- the new sibling `LowRegBgC0PairH2.lean` proves `amixBg_pair_h2`, the full
  arbitrary-background mixed order-zero correction in the same
  `B0 * D3 + B1 * N + B1 * A * N` currency as `c1_bg_pair_h2`.

The mixed arm is one of three pointwise order-zero arms.  The next smallest
producer is the arbitrary-background `DLa` `H2` pair; `DLb + Insert` still
appears to require a higher moving-trace/omega producer.  Only after all three
arms are assembled can the background correction be integrated in time and
used in the explicit high `A1` packet.

**Honest denominators.**  `kappa_pair_h2`, `pbLow_h2_mul`, and
`amixBg_pair_h2`: **100%**.  Full arbitrary-background pointwise order-zero
`H2` pair endpoint: unstated, **0%** (one of three arms complete).  Corrected
explicit lift-package endpoint: unstated, **0%**; its dedicated machinery is
approximately **65%**.  `bg_packet_of_solve` and
`ricci_flow_unif_existence`: **0%**.  Whole HCG project remains approximately
**3%**.

---

## №167 (executor, 2026-08-05) — **F2 FATOU-IDENT DONE.**  The rung now rides
## the PROJECTED sequence: `hUcont`/`hUderiv`/`hUinit` all land, and the
## endpoint `lowregFatouE3` is Fatou's `hbound`, sorry-free

**No failure to lead with.**  Every link of №165's named chain existed and was
reused; nothing had to be re-derived, and the a.e.→∀ seam crossed cleanly.  The
file typechecked on the **first** elaboration pass.

**New file**: `ShortTime/LowRegFatouIdent.lean` (+ same-name `.md`).

**The trajectory.**  `lowregProjMode g₀ fseq N t i := perModeConv λᵢ
(timeModeCoeff (fseq N) i) t`, exactly as №165 scoped it.  `galTamePerMode` and
`lowregGalSol` are confirmed **off the critical path** (banked, untouched).

**Per-conjunct.**
- `hUinit` — `lowregProjMode_zero`, one line (`perModeConv_zero_left`). ✓
- `hUcont` — `lowregProjMode_cont`, one line
  (`continuousOn_perModeConv_timeL2`); needs only `0 ≤ T`. ✓
- `hUderiv` — `lowregModeDeriv`, built from three new producers: ✓
  - `lowregFieldCombo` — the **spatial identification**, a.e.
    `field = finiteEigenComboHs (eigenIdxFinset g₀ N) (lowregProjMode …)`.
    `projField_fixed` (fed conjunct 3) → `coeFn_compLpL` → `spatialEigenProj_apply`
    → `timeModeCoeff_eq_perModeConv_forcing` (reused as instructed, not
    re-proved — exhibit 19 avoided).  The "all modes at once" step is **finite**,
    not countable: `finiteEigenComboHs` reads only the finset, so
    `Filter.eventually_all_finset` suffices.  **This is the piece №165 named but
    did not price, and it is what makes the whole route work.**
  - `lowregForceMode` — the a.e. per-mode forcing identity.  Confirms №165's
    refutation of №164: `galTameForce_eq`'s `hc` is produced by rewriting
    conjunct 2 (a.e. state ball) along `lowregFieldCombo`, with no input from
    the rung.
  - `lowregForceCont` — `tame_lip_balls` at the package's constants
    (`A := Ctop`, `B := B0`, `C := B1`, `Rt := lowregOuterRad`, ball radius
    `√(N+1)·R`) then `galTameForce_contOn`.  Mechanical, exactly as №166
    predicted; `galTameForce_contOn` served directly.

**The a.e.→∀ seam crossed, and how.**  `perModeConv_hasDerivAt` demands a
*globally* `Continuous` forcing.  `Set.IccExtend` supplies the representative,
`perModeConv_timeL2_congr` (the designed crossing) upgrades the a.e. forcing
identity to a **pointwise** identity of convolutions on `[0,T]`, and — the step
worth remembering — the rung's `HasDerivWithinAt … (Set.Ici t) t` still follows
even though `Ici t` leaves the slab, because `hUderiv` is quantified over
`Ico 0 T`: for `t < T` the slab is a neighbourhood of `t` within `Ici t`, so
`HasDerivWithinAt.congr_of_eventuallyEq` transfers.  No seam was blocked.

**Endpoint** (`lowregFatouE3`, compressed): under `hDim`, the nine package
certificates, the package's `fseq` with its a.e. state-ball and a.e. Nemytskii
conjuncts, and `hL2H3`,

    ∃ Ctop₂ Kr2 Kr1 Cδ ≥ 0, ∀ {ε} > 0,
      Ctop₂·Cδ + Kr2·R + Kr1·R + ε < 1 →
        ∃ Φ, ∀ N, ∀ t ∈ Icc 0 T, galerkinEnergy (eigenIdxFinset g₀ N)
          (lowregProjMode g₀ fseq N) 3 t ≤ Φ

— the rung's own shape, so **GAP-ADAPTH stays visible** as an explicit
hypothesis of the produced `∀ ε` statement.  Nothing here discharges it.

**`hL2H3` shape chosen** (F3's contract): the **Bochner** form
`∀ N, ∫ t, galerkinEnergy … 3 t ∂(timeMeasure T) ≤ Bd`, not an interval
integral.  Rationale: F3's route ends at `‖field‖²_{timeL2}`, which *is* an
integral against `timeMeasure T`, so the producer needs no conversion; the
consumer-side conversion to the rung's primitive `Pr` costs three rewrites and
**no integrability hypothesis** (`timeMeasure` is definitionally
`volume.restrict (Icc 0 T)`).  `Pr` is **built here**, not assumed:
`Pr N t := ∫ s in 0..t, IccExtend(E₃)`, with FTC for `hPrcont`/`hPrderiv` and
`integral_add_adjacent_intervals` for `hPrbd`.

**Bonus (in scope, and it is the real F1→F2 acceptance evidence).**
`lowregFatouPack` feeds `lowregFatouE3` straight from
`lowreg_projMode_tendsto`, returning Fatou's `hconv` **and** the `Bd`-indexed
`hbound` from one call.  It compiles, which *proves* F1's widening landed where
F2 needed it: the package's `_htame` (spelled `tensorHsInclusion`) unifies with
this file's `galLowView` spelling with no adapter (`galLowView` is an `abbrev`
for that inclusion), and the six per-`N` conjuncts destructure positionally as
`(hpack N).2.1` / `(hpack N).2.2.1`.  **F4 should consume `lowregFatouPack`.**

**One recorded layering debt** (not a defect): `lowregForceCont`'s
`tame_lip_balls` prelude duplicates `galTameSolOne`'s opening six lines at the
`lowregNfun` instance.  Kept local rather than claiming and rebuilding
`HeatSemigroup/GalerkinTameSol.lean` for a six-line reuse; if a third consumer
appears, extract `∃ K, LipschitzOnWith K Nfun (galTameBall g₀ a R κ)` upstream.

**Verification (persisted).**  Focused check green **and warning-free** (three
`unusedSectionVars` warnings cleaned with `omit [BoundarylessManifold I M] in`;
note the `omit` must precede the docstring, not sit between it and the
`theorem`).  Targeted build `+…ShortTime.LowRegFatouIdent` — "Build completed
successfully", **zero errors**.  `ScratchIdentCensus.lean` re-run green over all
**twenty-nine** censused declarations, `[propext, Classical.choice, Quot.sound]`
only, **no `sorryAx`**; the endpoint's line reads

    'DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregFatouE3'
      depends on axioms: [propext, Classical.choice, Quot.sound]

**Honest denominators.**  F2 is real mathematics, but of the bookkeeping kind:
no new estimate, no new analysis — the content is the spatial identification
plus two filter upgrades.  Machinery ≈**80% → ≈82%**.  The Fatou stage is
**F2 of F1–F4 done**, i.e. the stage is roughly **half** (F1 was 0pp, F3/F4 are
half-sessions).  `lowreg_loMass` theorem **0%** (σ ≤ 3 only, and gated on
`hL2H3` + GAP-ADAPTH; ∀σ needs rungs 4–5).  (N) `ricci_flow_unif_existence`
**0%**.  Whole HCG ≈**3%**.  Route-error counter **1/3**.  Campaign delta still
uncommitted (user-side).

**Next.**  F3 FATOU-L2H3 at the shape fixed above — and note that
`lowregFieldCombo` is already the identification F3's `E₃(c) =ᵃᵉ ‖field‖²_{H³}`
step needs, so F3 no longer has to redo it.

---

## №167a (planner, 2026-08-05) — F1+F2 ACCEPTED (panel: 2×CONFIRMED,
## 1×REFUTED-scoped); pack export gap corrected mid-flight; HANDOFF NOTE

**Panel** (run `wf_8b7893a5-9f1`, 3 read-only verifiers, run concurrently
with the F3+F4 executor):
- `seam-audit` **CONFIRMED** — all three of F2's analytic seams verified in
  the Lean text: the a.e.→∀ derivative transfer (filter correct incl. t=0;
  fails only at t=T which the rung never demands; value matches the rung's
  exact `galTameForce` spelling), the spatial identification (finite
  `eventually_all_finset`, `timeModeCoeff_eq_perModeConv_forcing` consumed
  within its actual hypotheses), and the `hc` ball transfer (defeq-sound
  `lowerState`/`lowerBall`/`galLowView` chain, one radius variable, no
  slippage).
- `hygiene-sweep` **CONFIRMED** — F1's deferred acceptance complete: the
  seven exports sit between `hreal` and `fseq` in both theorems, `_htame`
  byte-identical to the IsLowSolve field, the 11-binder pre-F1 prefix and
  all six per-N conjuncts positionally untouched; 29 census entries all
  target real declarations.  Caveats: №167 under-records the
  `PROJECT_MAP.md` pointer fix (edit real, ledger silent — recorded here);
  pre-existing name `lowreg_projMode_tendsto` is 21 letters (predates the
  budget's enforcement; observation only).
- `endpoint-fitness` **REFUTED (scoped)** — `lowregFatouE3` itself is FIT
  (verbatim the rung instantiated, same constants, gate visible,
  GAP-ADAPTH undischargedly explicit).  The misfit: **`lowregFatouPack`'s
  existential hides its `fseq` and drops conjunct 6 (the seed bound) and
  the a.e. Nemytskii conjunct** — exactly the handles F3's route needs —
  so the pack's `hL2H3` antecedent is undischargeable by any pack
  consumer; №167's "F4 should consume `lowregFatouPack`" is wrong as
  stated.  Also a citation fix: `norm_maxRegDuhamelSolField_zero_le` is
  STATED at `DeTurckQuasilinearExistence.lean:217–220` (zero-seed,
  `≤ (1+T)·‖F‖` in timeL2); `TameForcingFixedPoint.lean:518/:893` are call
  sites.
- **Mid-flight correction sent to the F3+F4 executor**: either widen the
  pack to re-export conjunct 6 + the Nemytskii conjunct for ITS `fseq`, or
  (simpler, panel-verified viable) destructure `lowreg_projMode_tendsto`
  ONCE and feed `lowregFatouE3` directly — never destructure twice
  (incomparable witnesses).  №168 must record the choice.

**HANDOFF NOTE (for the incoming Codex lane — see
`CODEX_TAKEOVER_HANDOFF.md`)**: if №168 is absent below, the F3+F4
executor died mid-flight — its contracts are №167 + the correction above.
If №168 exists, verify its census claims by re-running
`ScratchIdentCensus.lean` before building on it.

**State.**  F1 ✓ F2 ✓ (accepted).  Machinery ≈**82%**.  (N) **0%**;
`lowreg_loMass` **0%**; HCG ≈ **3%**; counter **1/3**.

---

## №168 (executor, 2026-08-05) — **F3 FATOU-L2H3 DONE, F4 FATOU-ASSEMBLE DONE.
## THE FATOU STAGE IS CLOSED.**  `hL2H3` discharged; `lowregMassLow` delivers
## the σ ≤ 3 spectral mass of the limit forcing at `lowreg_loMass`'s own object

**No failure to lead with.**  Both bricks landed on their planned routes; no
route was abandoned, no obstruction found.  The Bochner form №167 chose was the
right contract — the producer ends at `‖field‖²_{timeL2}` and needs **no**
integrability hypothesis and **no** interval-integral conversion, exactly as
priced.  One micro-trap (a `rw` that reports a rewrite failure where the real
cause is a goal already closed) cost one iteration; recorded below.

**Panel correction (1): the choice, recorded as demanded.**  Neither (a) nor
(b) verbatim — a strictly better third option that the panel's own diagnosis
implies.  The panel is right that `lowregFatouPack`'s existential hides its
`fseq` and drops conjunct 6 and the Nemytskii conjunct, so **no external
consumer** can discharge its `∀ Bd, … →` antecedent, and re-destructuring
`lowreg_projMode_tendsto` outside gives incomparable witnesses.  But the
single destructure *already inside* `lowregFatouPack` has every handle.  So the
discharge was applied **there**: `lowregFatouPack`'s `∀ Bd` antecedent is
**deleted**, and the pack now returns Fatou's `hconv` and `hbound`
unconditionally except for GAP-ADAPTH.  This needs no widening (the export
surface shrinks, it does not grow), no second destructure, and leaves F4 able
to consume the pack as №167 intended.  Panel correction (2) accepted: the
citation in this ledger and in the `.md` now reads
`DeTurckQuasilinearExistence.lean:217–220`.

**F3 — `lowregL2H3`** (`ShortTime/LowRegFatouIdent.lean`):

    ‖fseq N‖ ≤ b →
      ∫ t, galerkinEnergy (eigenIdxFinset g₀ N)
        (lowregProjMode g₀ fseq N) 3 t ∂(timeMeasure T) ≤ ((1+T)·b)²

stated at a **free** bound `b`, not hard-wired to `R/4` (weakest assumptions;
no `0 ≤ b` needed and none asked).  Hypotheses are exactly `lowregFieldCombo`'s:
`0 < T`, `T ≤ 1`, and the a.e. Nemytskii identity for some
`u : ℝ → lowerState g₀ 1 R`.  Three steps: (i) a.e. `E₃(c)(t) = ‖field t‖²`
from `lowregFieldCombo` (reused, not redone — №167's prediction held) plus
`finiteEigenCombo_spectral_normSq`, the exponents matched by
`((1:ℕ):ℝ)+2 = (3:ℝ)` rewritten **only in the rpow exponent**, never in the
`tensorHs` type index; (ii) `integral_congr_ae` then `norm_sq_eq_integral`;
(iii) `norm_maxRegDuhamelSolField_zero_le` and `nlinarith` to square.
`lowregFatouPack` instantiates `b := lowregStateRad Ctop B1 ρ P / 4` from
conjunct 6, so `Bd = ((1+T)·R/4)²` as scoped.

**The fourth widening was NOT taken.**  `D`/`hzero`/`hTτ` were sanctioned "if
and only if actually consumed" — they are not.
`norm_maxRegDuhamelSolField_zero_le` is already a closed-horizon statement
whose only `T`-hypotheses are `0 < T` and `T ≤ 1`, both supplied by the pack's
caller.  The package stays at **three** widenings.

**F4 — `lowregMassLow`** (new file `ShortTime/LowRegFatouMass.lean` + `.md`):

    ∃ Ctop B1 ρ P Ctop₂ Kr2 Kr1 Cδ, 0 ≤ … ∧ ∀ {ε} > 0,
      Ctop₂·Cδ + Kr2·R + Kr1·R + ε < 1 →
        ∀ σ ≤ 3, ∃ Cσ, ∀ t ∈ Icc 0 T,
          Summable (fun i => (1+λᵢ)^σ · (perModeConv λᵢ (timeModeCoeff fLo i) t)²)
            ∧ ∑' … ≤ Cσ

Three lines of content: destructure the pack once; dominate
`(1+λᵢ)^σ ≤ (1+λᵢ)^3` by `Real.rpow_le_rpow_of_exponent_le` +
`one_le_one_add_lambda` (the mirror's exact argument,
`GalerkinLimitUniformMass.lean:1175–1188`), with `galerkinEnergy … 3 t`
unfolding to the finset sum by `rfl`; close with `fatou_sq_mass`.  **σ-range,
exactly: `σ ≤ 3` with NO lower bound** — the domination needs only `1 ≤ 1+λᵢ`,
so all of `(-∞, 3]` is covered.  A sibling file rather than more of
`LowRegFatouIdent.lean` (620 lines, far under cap): the split is by abstraction
— identification vs. assembly — and this file carries the ShortTime tree's only
import of `GalerkinCompactness.lean`.

**Limit-object identification — CHECKED, and it is literal.**  The pack's
`hconv` names `perModeConv λᵢ (timeModeCoeff fLo i) t`; `lowreg_loMass`
(`LowRegAllOrderJet.lean:1058–1064`) states its conclusion about the
**syntactically same** expression — same `perModeConv`, same
`timeModeCoeff fLo i`, same `tensorSobolevWeight i σ`, same
`Summable ∧ ∑' ≤ Cσ`, same `∀ t ∈ Icc 0 T`.  **No bridge remains on the limit
object.**  The gap to `lowreg_loMass` is exactly two things: the exponent range
(`σ ≤ 3` vs. every real σ) and the GAP-ADAPTH hypothesis.  Consumption shape
recorded in `LowRegFatouMass.md`; **`LowRegAllOrderJet.lean` untouched, its
`sorry` at `:1065` stands.**

**The one trap worth remembering.**
`rw [norm_sq_eq_integral fld, timeMeasure]` fails with *"Failed to rewrite
using equation theorems for `timeMeasure`"* — but the real cause is that the
first `rw`'s trailing `rfl` already closed the goal (`timeMeasure` is
definitionally `volume.restrict (Icc 0 T)`), so there was nothing for the
second rewrite to act on; the error message names the wrong culprit.  Fix: the
term form `(norm_sq_eq_integral fld).symm`.  Contrast `lowregFatouE3`'s
`hTint`, where `rw [… , timeMeasure, …]` *does* work because a further rewrite
follows it.

**Verification (persisted).**  Focused checks green and warning-free on both
files.  Targeted builds `+…ShortTime.LowRegFatouIdent` and
`+…ShortTime.LowRegFatouMass` — "Build completed successfully", **zero errors**
in both.  `ScratchIdentCensus.lean` widened to **thirty-one** censused
declarations and re-run green, `[propext, Classical.choice, Quot.sound]` only,
**no `sorryAx`**.  The two endpoints' lines read

    'DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregL2H3'
      depends on axioms: [propext, Classical.choice, Quot.sound]
    'DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lowregMassLow'
      depends on axioms: [propext, Classical.choice, Quot.sound]

**Honest denominators.**  The **Fatou stage is CLOSED** (F1 ✓ F2 ✓ F3 ✓ F4 ✓).
But F3 and F4 are bookkeeping-grade, like F2: no new estimate, no new analysis
— the content is one spectral-norm identity, one integral conversion, one
maximal-regularity citation and one weight domination.  Machinery
≈**82% → ≈85%** (the stage was priced as the identification plus two
half-sessions; both half-sessions landed on plan, so the jump is capped at the
+3pp the pricing allows).  `lowreg_loMass` theorem stays **0%** — σ ≤ 3 is not
∀σ, and the remaining gates are rungs 4–5, the general-σ glue, GAP-ADAPTH and
GAP-ORDER.  (N) `ricci_flow_unif_existence` **0%**.  Whole HCG ≈**3%**.
Route-error counter **1/3**.  Campaign delta still uncommitted (user-side).

**Next.**  Rungs 4–5 per the registered plan: the general-`k` energy regrouping
and the dissipation-export engine variant that carry the rung above `σ = 3`.
Ahead of, or in parallel with, that: **GAP-ADAPTH** — the producer-side
smallness audit of `lowregStateRad` against `Ctop₂, Kr2, Kr1, Cδ` — is now the
*only* hypothesis standing between `lowregMassLow` and an unconditional σ ≤ 3
mass bound, and it is the cheaper of the two.

---

## №169 (planner, 2026-08-05, FINAL BEFORE HANDOFF) — F3+F4 landing recorded;
## third-option pack repair RATIFIED; acceptance ASSIGNED to the incoming lane

**F3+F4 landed per №168** (planner has NOT independently panel-verified them
— usage limit; see below).  Ratified on the record:
- The executor's **third-option** resolution of №167a's pack gap — discharge
  the `∀ Bd` antecedent INSIDE `lowregFatouPack` where all handles live,
  shrinking the export surface instead of widening it — is strictly better
  than both options the panel offered, and is consistent with the panel's
  own diagnosis.  RATIFIED.
- `lowregL2H3` at a FREE bound `b` (not hard-wired `R/4`) is the
  weakest-assumptions form.  RATIFIED.
- The claim that `lowregMassLow`'s conclusion hits `lowreg_loMass`'s
  LITERAL object (same expression, same weights, same quantifiers) is the
  single most load-bearing claim of №168 and MUST be independently verified
  before anything consumes it.

**ACCEPTANCE ASSIGNED TO THE INCOMING LANE** (`CODEX_TAKEOVER_HANDOFF.md`):
step zero there already mandates re-running `ScratchIdentCensus.lean` (now
31 declarations) and verifying №168's claims.  Specifically verify:
(1) `lowregMassLow`'s conclusion vs `LowRegAllOrderJet.lean:1058–1064`
token-for-token; (2) the pack's antecedent deletion did not weaken `hconv`;
(3) `lowregL2H3`'s exponent handling (`((1:ℕ):ℝ)+2 = 3` only in the rpow
exponent).  Then proceed per №168's "Next": GAP-ADAPTH first, rungs 4–5
after.

**State at handoff.**  Fatou stage CLOSED (F1–F4 ✓).  Machinery ≈**85%**.
Remaining to `lowreg_loMass`: GAP-ADAPTH (+GAP-ORDER), rungs 4–5, general-σ
glue — ≈4–6 sessions.  Then the (N)-assembly phase ≈4–7.  (N) **0%**;
`lowreg_loMass` **0%**; whole HCG ≈ **3%**; route-error counter **1/3**.
The campaign delta (everything from tame-C0 through the Fatou stage, incl.
two proved endpoint theorems) is UNCOMMITTED — checkpoint commit first.

---

## №170 (Codex takeover, 2026-08-05) — handoff acceptance GREEN;
## GAP-ORDER route corrected and BINDING

**Handoff acceptance.**  The 31-declaration ShortTime census and the
125-declaration analysis census both reran green: every printed declaration
depends only on `[propext, Classical.choice, Quot.sound]`; no `sorryAx` entered
the campaign machinery.  Independent source review accepted all three №169
checks, with one wording correction: `lowregMassLow` and `lowreg_loMass` use the
same limit-object expression modulo bound-variable renaming and the former's
outer `σ ≤ 3` gate, rather than being literally token-for-token identical.
`lowregFatouPack` retains the original `hconv`; `lowregL2H3` rewrites only the
spectral exponent from `((1 : ℕ) : ℝ) + 2` to `3`.

**GAP-ORDER audit.**  The four absorption witnesses really are fixed by
`hDim,g₀` before every solver/class parameter.  The useful cap witness is not
an opaque `Cδ`: it is

    Kcap * (δ / (1 - δ)^2),

where `Kcap` is the `δ`-free witness exported by `lowData_split`.  The
radius-dependent `Kmid` is not a gate coefficient and must remain inside the
later quantifiers.  Binding implementation route:

1. add `galArmMassOrd` in `LowRegRungThree.lean`, exposing
   `Ctop₂, Kr2, Kr1, Kcap` before `R,δ,hreal` and returning `Kmid` after them;
2. add `lowregRung3Ord` with the same four gate witnesses before all numerical
   solver/class parameters;
3. retain `galArmMass` and `lowregRung3` as compatibility wrappers;
4. census both ordered declarations before any consumer uses them.

No protected analysis file needs editing: `lowData_split` already has the
correct binder order.

**GAP-ADAPTH correction.**  It is NOT derivable from an arbitrary
`IsLowSolve`.  The present package records only `0 ≤ δ ≤ 1/3` and the
existing state-radius caps; it neither bounds the ordered arm witnesses by
`Ctop/B1` nor retains the calibrated `δ` and `Rcap`.  The sole producer
`lowreg_solve_two` can be retuned, but its existential result erases those
witnesses.  After GAP-ORDER, the smallest honest next interface is an explicit-
witness sibling package/producer (with a projection to `IsLowSolve`) that keeps
`δ,Ctop,B1,ρ,P` and `lowregStateRad ≤ Rcap`.  The adapted front chooses
`δ` and `Rcap` after the ordered constants and exports the proved absorption
budget.  Do not rewrite public `IsLowSolve`, and do not attempt to recover the
budget from it.

**Honest denominators.**  This acceptance/audit moves no endpoint theorem:
`lowreg_loMass` **0%**, (N) `ricci_flow_unif_existence` **0%**, whole HCG
≈**3%**.  Dedicated machinery remains ≈**85%** until the ordered Lean
interface lands and is verified.  Route-error counter stays **1/3**; the
campaign delta remains uncommitted and should be checkpointed before broader
interface surgery.

---

## №171 (Codex executor, 2026-08-05) — GAP-ORDER LANDED;
## GAP-ADAPTH is STOP-AND-REDESIGN at the frontier input interface

**GAP-ORDER closed.**  `LowRegRungThree.lean` now exports:

- `galArmMassOrd`: `Ctop₂, Kr2, Kr1, Kcap` are chosen from `hDim,g₀`
  before `R,δ,hreal`; the top coefficient is explicitly
  `Ctop₂ * (Kcap * (δ / (1-δ)^2)) + Kr2*R + Kr1*R`; the genuinely
  radius-dependent `Kmid` remains inside the later quantifiers;
- `lowregRung3Ord`: the same four gate constants precede every numerical
  solver/class parameter at the endpoint;
- `galArmMass` and `lowregRung3`: compatibility wrappers, preserving all
  existing consumers.

The focused source check passed without warnings.  The direct module refresh
passed.  `ScratchIdentCensus.lean` now prints 33 declarations; the two ordered
declarations, the two wrappers, and every existing campaign declaration depend
only on `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

**Scoped stop condition — wrong/insufficient statement.**  GAP-ADAPTH cannot
close the current generic theorem

    lowreg_loMass ... (hlo : IsLowSolve ...)

because `IsLowSolve` admits arbitrary existential witnesses satisfying only
`0 ≤ δ ≤ 1/3` and the old state-radius caps.  It erases the selected
`δ,Ctop,B1,ρ,P` and contains neither a calibrated `Rcap` nor the ordered arm
budget.  `lowregMassLow hlo` independently reselects those erased witnesses,
so a free-standing budget certificate about a producer's different witnesses
cannot discharge its gate.  No theorem relates `Kr2+Kr1` to the package's
`B1/Ctop`, and the existing DeTurck threshold controls a different expression.
Trying to prove the gate from arbitrary `hlo` would be unsound.

**Smallest honest redesign (not yet authorized/landed).**  Keep public
`IsLowSolve` unchanged.  Add an explicit-witness sibling package
`IsLowSolveAt` plus `lowreg_solve_two_at`, retaining the present solve fields
and `lowregStateRad ... ≤ Rcap`, with a projection to `IsLowSolve`.  Add an
adapted package that carries the ordered constants and proved absorption
budget; choose `δ` and `Rcap` only after `lowregRung3Ord`'s witnesses.  Then:

1. add an explicit-witness/adapted sibling of `lowregMassLow`;
2. change the still-unproved `lowreg_loMass` binder to the adapted package;
3. propagate that binder through `lowreg_spatialMass`, `lowreg_forceJetMass`,
   `lowreg_allOrderJet`, `lowreg_joint_of_re`, and the unique front-two
   producer path, projecting `.toIsLowSolve` for unchanged machinery.

This is a real theorem-interface correction, not routine local proof repair;
do not introduce a consumer-side assumption or silently strengthen
`IsLowSolve`.

**Honest denominators.**  GAP-ORDER moves dedicated machinery ≈**85% →
≈**86%**.  `lowreg_loMass` theorem remains **0%** (its current statement is
insufficient and rungs 4–5/general-`σ` remain); (N)
`ricci_flow_unif_existence` remains **0%**; whole HCG remains ≈**3%**.
Route-error counter stays **1/3** because this was a statement audit, not a
failed proof route.  The campaign delta is still uncommitted; checkpoint it
before the multi-file adapted-package surgery.

---

## №172 (Codex executor, 2026-08-05) — explicit-package redesign AUTHORIZED
## and BINDING

The user explicitly authorized the interface repair (“add explicit packages”).
The dependency-ordered implementation is:

1. `UnifClassBounds.lean`: add `IsLowSolveAt`, indexed by the exact
   `δ,Ctop,B0,B1,D,ρ,P,Rcap`, with precisely the `IsLowSolve` fields plus
   `lowregStateRad Ctop B1 ρ P ≤ Rcap`; add its exact constructor and projection
   to the unchanged `IsLowSolve`.
2. `LowRegApplyTwo.lean`: factor the existing proof through
   `lowreg_solve_two_at`, exposing `thr` itself and the exact six-number tuple;
   keep `lowreg_solve_two` as the compatibility projection.
3. `LowRegRungThree.lean`: package one chosen ordered witness tuple as
   `IsRung3Ord`; never call `lowregRung3Ord` afresh downstream and pretend the
   reselected witnesses coincide.
4. New `LowRegAdaptedSolve.lean`: define `IsAdaptedLowSolve` from the exact solve,
   the stored ordered rung package, and a proved absorption budget.  Its producer
   chooses

       δ = 1 / (16 * (Ctop₂*Kcap + 1)),
       Rabs = 1 / (8 * (Kr2 + Kr1 + 1)),
       ε = 1/4,

   calls the exact solver at `min Rmax Rabs`, and exports both the endpoint cap
   and the absorption cap.  The elementary budget is `≤ 1/8 + 1/8 + 1/4 < 1`.
5. Add exact-witness projection/Fatou siblings and thread the adapted package
   through the insufficient `lowreg_loMass` consumer chain.  Preserve the
   generic projection/Fatou theorems, `lowregMassLow`, `IsLowSolve`, and
   `lowreg_solve_two` as compatibility APIs.

The endpoint cap and absorption cap must be combined by `min`; replacing the
former would break the joint-smoothness endpoint.  This closes GAP-ADAPTH only
for one metric.  Class-uniform upper bounds for the ordered rung constants are
a separate load-bearing producer required before `(N)` can choose one common
`δ`, radius and horizon.

**Honest denominator before implementation.**  `lowreg_loMass` theorem **0%**;
its dedicated machinery ≈**86%**; `(N)` **0%**; whole HCG ≈**3%**.  The theorem
percentages do not move merely because the new packages compile.

---

## №173 (Codex executor, 2026-08-05) — explicit-package redesign LANDED
## per-metric GAP-ADAPTH closed; all-real-σ frontier remains

The binding redesign in №172 is implemented and verified end to end.

- `IsLowSolveAt` retains the literal solve tuple and a state-radius cap, with a
  projection to the unchanged `IsLowSolve` compatibility API.
- `lowreg_solve_two_at` exports that exact package; `lowreg_solve_two` remains
  the compatibility wrapper.
- `IsRung3Ord` stores one ordered rung-three continuation, and
  `IsAdaptedLowSolve` joins it to the exact solve plus a proved absorption
  budget.  `lowreg_solve_adapt` chooses the calibrated threshold and absorption
  radius after the ordered constants, then uses `min` with the endpoint cap.
- `lowreg_proj_at`, `lowreg_projMode_at`, `lowregFatouE3At`,
  `lowregFatouPackAt`, and `lowregMassLowAt` preserve those same witnesses.
  The exact σ≤3 mass theorem has no remaining gate.
- The adapted package is threaded through `lowreg_loMass`,
  `lowreg_spatialMass`, `lowreg_forceJetMass`, `lowreg_allOrderJet`, and
  `lowreg_joint_of_re`; `lowreg_joint_two` is now the unique adapted producer.
  Its public endpoint conclusion and full horizon are unchanged.

`lowreg_loMass` now proves its `σ ≤ 3` branch with `lowregMassLowAt`.  Its sole
remaining `sorry` is the branch `3 < σ`, requiring rungs 4–5, general-`k`
regrouping, and the higher dissipation export.  Thus `lowreg_loMass` as a theorem
remains **0%**, despite the closed low branch.

The first combined import exposed duplicate proof bodies for the public names
`jetAdd` and `jetSmul` in the H² and operator-window lanes.  The protected,
widely consumed H² declarations remain canonical; the window-local copies are
now `opJetAdd` and `opJetSmul`, with their five source call sites updated.

Verification: all touched implementation files passed focused checks; targeted
builds passed for the adapted producer, exact projection/Fatou/mass modules, and
the full adapted consumer chain.  The 47-declaration census reports only
`[propext, Classical.choice, Quot.sound]` for every proved package declaration.
The separately printed `lowreg_loMass` reports the expected `sorryAx` and no
other new frontier was introduced.

**Next producer.**  Prove the first higher energy rung used in the `3 < σ`
branch, preserving the same `IsAdaptedLowSolve` witnesses; do not reselect
ordered constants.  Separately, `(N)` still needs class-uniform upper bounds for
the ordered rung constants before one common threshold, radius, and horizon can
be chosen across the metric class.

**Honest denominators after implementation.**  Explicit-package/GAP-ADAPTH
machinery for one metric: **100%**.  Dedicated all-order low-mass machinery:
≈**87%**.  `lowreg_loMass`: **0%**; `ricci_flow_unif_existence`: **0%**; whole
HCG compactness: ≈**3%**.  Campaign changes remain uncommitted.

---

## №174 (Codex executor, 2026-08-05) — explicit higher packages and rung four LANDED
## next producer: the ordered q=4/rung-five certificate

The first higher fixed rung is implemented and verified, together with the two
explicit packages that can honestly exist at this stage.

- `energy_l1_diss` and `galRiderDiss` add the metric-generic next-scale
  dissipation export.  They are checked and axiom-clean.  The tower-direct
  sequential proof of fixed rung four did not require this stronger engine, so
  it remains infrastructure for the later generic ladder rather than a hidden
  hypothesis of the fixed rung.
- `IsHmRungOrd` and `lowregHmPack` retain the exact all-order top coefficient of
  `nDiffHmQ`, selected before `δ`, the state, its `H⁵` radius, and the rung.
  This is not a partial common package: q=4 is still missing.
- `LowRegRungFour.lean` proves `galArmMass4Ord`, `lowregRung4Ord`, and packages
  the latter as `IsRung4Ord`/`lowregRung4Pack`.  Its continuation consumes a
  common pointwise rung-three cap and returns a common `E₄` cap on the same
  horizon.  The top `E₅` coefficient depends only on the four ordered gate
  witnesses; the prior cap appears only in the lower affine coefficients.
- `jetSqrtLe`, `jetWinMono`, and `armLadder3` were promoted without statement
  changes so rung four reuses the settled `q ≤ 2` algebra instead of copying it.

**Route correction.**  Rungs four and five do not prove the `3 < σ` branch for
every real `σ`.  They provide the fixed bottom needed to obtain a common `H⁵`
radius.  The generic `nDiffHmQ` ladder must then run for all higher integer
rungs, followed by the existing Fatou/identification step and the choice of an
integer order above the requested real `σ`.

**Binding next sequence.**

1. Prove the tower-direct q=4 arm estimate, `galArmMass5Ord`, the rung-five
   energy endpoint, `IsRung5Ord`, and `lowregRung5Pack`.
2. Only then define the common ordered gate envelope for stored rung-three,
   rung-four, rung-five, and high-rung certificates.  Use nonnegative sums to
   dominate the finite gates and `κ`; do not add a short-lived partial package.
3. Recalibrate the adapted solve once against that common envelope.  Preserve
   the exact solve witnesses; do not call any existential rung producer again.
4. Obtain the common `H⁵` radius, run the generic higher ladder on the same
   horizon, apply Fatou/identification order by order, and fill the `3 < σ`
   branch of `lowreg_loMass`.
5. Hoist the same ordered envelope uniformly over the metric class before `(N)`
   chooses one common threshold, radius, and horizon.

The current exact packages are still internally self-background `(g,g)`, while
some class-uniform producers use `(g,gBase)`.  The fixed-rung work must not be
read as resolving that later two-background policy boundary.

Verification status: focused checks are green for the energy exporter, high
package, promoted rung-three boundary, and complete rung-four module.  The
named export refreshes are green.  The widened 53-declaration ShortTime census
is green: all six new higher-package declarations print only `propext`,
`Classical.choice`, and `Quot.sound`; `lowreg_loMass` remains the sole expected
`sorryAx` control.

**Honest denominators.**  `lowreg_loMass` theorem **0%**; its dedicated
all-order machinery ≈**89%**.  Rung four theorem/package **100%**; rung five
theorem/package **0%**.  Per-metric adapted solve/package lane through rung four
**100%**.  `(N)` `ricci_flow_unif_existence` **0%**; whole HCG compactness
≈**3%**.  Campaign changes remain uncommitted.

---

## №175 (Codex executor, 2026-08-05) — per-metric all-real and strict-open chain CLOSED;
## explicit class-uniform gate boundary LANDED; next producer: `lowreg_gate_unif`

The binding explicit-package route is complete for one fixed metric.

- The same exact projected solve witnesses now pass through rung five, the
  generic higher ladder, Fatou/identification, and every real spatial order.
  `lowreg_loMass` is fully proved; it no longer contains or depends on a
  `sorry`.
- The radius-flexible A2 pair estimate gives a genuine strict contraction:
  `radialA2_pairR`, `lowA2_small_one`, `lowreg_solve_open`,
  `lowreg_adapt_open`, and `lowreg_joint_open` choose a positive
  metric-dependent horizon rather than accepting a vacuous smallness premise.
- `deTurck_rem_repr` is the reusable analysis-layer identity relating the
  symmetrized low-regularity remainder plus frozen connection Laplacian to the
  realized Ricci--DeTurck right-hand side.  `lowreg_dt_open` applies it to give
  every fixed three-dimensional metric a positive self-background
  Ricci--DeTurck horizon with the full joint chart-Gram regularity package.
- `LowRegGateData` stores the common top and radius envelopes.
  `IsLowGateUnif gBase Lambda K` records the required quantifier order: the
  single `K` is fixed before an arbitrary class member and supplies that
  metric's exact `IsLowGateOrd` package.  No producer is asserted by swapping
  the existing per-metric choices.
- The older supercritical initial-data theorem now reuses `deTurck_rem_repr`;
  its duplicated local representation proof was removed without changing its
  public statement.

Verification is green for all new and refactored modules.  The DeTurck
coefficient census contains 129 declarations, and the widened ShortTime census
contains 80 declarations.  Every printed declaration uses only `propext`,
`Classical.choice`, and `Quot.sound`; neither census contains `sorryAx`.

**Exact remaining producer.**  Prove `lowreg_gate_unif`: choose one
`LowRegGateData` from the fixed background, `Lambda`, and the order-at-most-three
class bounds, then prove `IsLowGateUnif` for every member metric.  The first
missing mathematical/API input is a class-uniform bound for the rung-five H6
comparison quantities currently exposed per metric by `hs_le_jet g 2 4` and
`galRepJet_le g 6`.

That first gate is not the whole uniform-horizon problem.  After it lands, the
uniform solve/time-floor package must also hoist the metricwise choices used by
the realization, affine, nonlinearity, `hs2_opBound_at_two`, and strict-time
estimates, and it must make an explicit background-policy choice: retain the
proved self-background `(g,g)` chain via uniform comparison theorems, or rebuild
the relevant estimates over the fixed background `(g,gBase)`.  Do not hide
these gaps in consumer-side assumptions or a larger constants record.

There is also a theorem-shape design boundary.  This low-regularity lane and
`lowreg_dt_open` assume `Module.finrank ℝ E = 3`, while the current statement of
`ricci_flow_unif_existence` is dimension-generic.  A three-dimensional
`lowreg_gate_unif` cannot by itself prove that statement.  Before endpoint
assembly, either specialize `(N)` and its consumers honestly to dimension three
or generalize the low-regularity ladder; this choice is not made here.

**Honest denominators.**  `lowreg_loMass`: **100%**.  Dedicated per-metric
all-real machinery and `lowreg_dt_open`: **100%**.  The explicit
`LowRegGateData` / `IsLowGateUnif` interface: **100%**; its actual producer
`lowreg_gate_unif`: **0%**.  Dedicated low-regularity supporting machinery
toward `(N)`: approximately **90%**.  `lowreg_dt_unif`: **0%**;
`ricci_flow_unif_existence`: **0%**; whole HCG theorem closure: approximately
**3%**.  Campaign changes remain uncommitted.

---

## 184. Final endpoint isolated to one background bootstrap producer (2026-08-06)

The class-first low solve is now connected all the way to the public Ricci-flow
endpoint, with one deliberately visible analytic leaf.

- `stateRad_le_P4` and `realize_h2_bound` replace the opaque
  `hs2_opBound_at_two.choose` comparison by the explicit constant
  `C = 1 / K.realize`.
- `BgSmoothPacket g g_bg K T` is the exact closed-slab order-two packet consumed
  by the existing joint-smoothness endpoint.
- `dt_of_bg_packet`, `lowreg_dt_of_solve`, and `lowreg_dt_unif` are proved on the
  original common horizon.
- `ricci_flow_unif_existence` is now a proved consumer composition through the
  existing DeTurck gauge removal; `MaximalTime` remains green.

The only proof-body `sorry` in the direct route is
`LowRegBgBootstrap.bg_packet_of_solve`.  It must bootstrap
`IsLowSolveBg g gBase K` from order one to an order-two carrier on the same
horizon and provide its all-order closed-slab mode packet.  The already proved
`lowreg_allOrderJet` cannot simply discharge it: that theorem consumes the much
richer `IsRealizedTwo` package, whose producer and forcing identities are
self-background `(g,g)`, whereas the uniform lane is fixed-background
`(g,gBase)`.

The qinz short-time-existence source confirms that the intended endpoint is
genuinely smooth up to `t = 0`: its `JointChartGramSmooth` predicate is joint
smoothness on `Icc 0 T`.  It does not close this uniform leaf because its
quantifier order is per metric (`∀ g₀, ∃ T`) and its construction may choose a
smaller time after the metric and solution are known.

Verification status: the explicit H2 adapter, packet endpoint, direct module
exports, final `(N)` consumer, and `MaximalTime` focused checks pass.  The
axiom path of `(N)` has one `sorryAx`, traced solely to
`bg_packet_of_solve`.

**Honest denominators.**  Class-first bounds and low solve: 100%.  Packet-to-
DeTurck endpoint and gauge/final assembly: 100%.  The theorem
`bg_packet_of_solve`: 0% until proved.  Consequently
`ricci_flow_unif_existence`: 0% theorem completion despite its finished
consumer body.  Whole HCG project: approximately 3%.

---

## 189. Five-piece order-zero tail and class-first RHS0 path closed (2026-08-06)

The last five cancellation-preserving order-zero leaves are now assembled by
`tail_h1_unif`.  Its base and slope functions are selected before the class
metric, it consumes only class metric jets through order three, and it reuses
the exact `tail_h1_parts` decomposition.  The result is focused-green, directly
exported, and its axiom census contains only `propext`, `Classical.choice`, and
`Quot.sound`.

`rhs0_h1_parts` exposes the supplied Ricci/DLa/tail assembly that had previously
been hidden inside the metricwise `rhs0_h1_of_aux`.  The actual class-first
`rhs0_h1_unif` now combines `exists_convex_jets`, `ricci0_h1_unif`,
`dla_h1_unif`, and `tail_h1_unif` without commuting any existential across the
class metric.  `rhs0_path_unif` transports the same affine functions through
the interval integral.  Both endpoints are focused-green, directly exported,
and axiom-audited with only the three standard axioms above.

The next exact chain is structural rather than a new estimate:
`rem_h1_unif` -> `smoothN_h1_unif` -> `coreN_tame_unif` ->
`coreN_outer_unif` -> `lowRegN_outer_unif`.  It must replay the existing
per-metric transports with the newly class-first top, lower, RHS0, and RHS1
witnesses; calling the old existential wrappers would restore the wrong
quantifier order.

**Honest denominators.**  The five-piece tail, order-zero RHS coefficient, and
order-zero path endpoints are each **100%**.  Every theorem in the structural
chain named above is currently unstated and therefore **0%**.  The actual
`lowreg_bounds_unif`, `lowreg_dt_unif`, and `ricci_flow_unif_existence` remain
**0%**.  Dedicated low-regularity supporting machinery toward `(N)` remains
approximately **99%**; whole HCG theorem closure remains approximately **3%**.
Campaign changes remain uncommitted.

---

## 184. Self top coefficient, fixed-curvature action, and class-first RHS1 landed (2026-08-06)

The representation and integration chain left open after section 183 is now
closed.  Every declaration below is focused-green, warning-free, directly
exported, and has a temporary axiom census containing only `propext`,
`Classical.choice`, and `Quot.sound`:

- `phiSelfC`, `phiSelfC_nonneg`, and `phiSelf_grid` give an explicit
  dimension-only pointwise jet cap for
  `deTurckPhiMetTotal g gBase g - ricciArmPrincipalCoeffPure g g`.  The cap is
  `34 * dim^6` at order zero and zero at every positive order.
- `phiCurv_jet_unif` integrates that self coefficient together with the
  class-first order-zero/one grid for `gradSlotCurvCoeff`.  It deliberately
  uses `appRS_h2_unif` in the `H2 operator x H1 curvature passenger -> H1`
  orientation.  Consequently it consumes metric jets only through order three;
  the stronger `H2 x H2` wrapper would incorrectly require a second derivative
  of curvature and fourth metric jets.
- `fixed_curv_h1_unif` composes the coefficient cap with `appCc_h1_unif` and
  selects one spectral `H2 -> H1` action constant before the class metric.
- `rhs1_h2_unif` selects the convex-path packet and both Ricci/Lie order-one
  coefficient functions before the class metric, then reuses the public
  `rhs1_h2_of_aux` assembly.  This removes the quantifier leak retained by the
  older compatibility theorem `rhs1_h2_of_unif`.

The next routine integrations are the path-integrated sibling of
`rhs1_h2_unif` and the class-first top-path split.  The next genuine order-zero
RHS leaf is lower: arbitrary-rank class-first moving traces are needed for the
insertion, vector-bilinear, and mixed Lie corrections, while DLa still needs a
public class-first pointwise factor grid in
`DeTurckLieKernelL2JetBound.lean`.  No metricwise existential wrapper is counted
as a substitute.

Normal focused checks, direct exports, and axiom audits used four Lean threads
under the 6 GB cap, with one elaboration process at a time.  The temporary
orphaned elaboration lock caused by an externally timed-out wrapper was verified
against its dead PID and moved to a recoverable quarantine path before work
continued.

**Honest denominators.**  The four theorem bricks listed above: **100%**.
Class-first joint tame producer: still unstated, therefore **0%**.  Actual
`lowreg_bounds_unif`: **0%**.  Dedicated low-regularity supporting machinery
toward `(N)`: approximately **99%**.  `lowreg_dt_unif`: **0%**;
`ricci_flow_unif_existence`: **0%**; whole HCG theorem closure: approximately
**3%**.  Campaign changes remain uncommitted.

---

## 185. Integrated RHS1/top path and first order-zero leaf landed (2026-08-06)

The two routine integrations left after section 184 and the first genuine
order-zero leaf are now closed.  Every declaration below is focused-green,
warning-free, directly exported, and has an axiom census containing only
`propext`, `Classical.choice`, and `Quot.sound`:

- `rhs1_path_unif` carries the class-first affine order-one coefficient through
  `path_jetL2_le` without changing its two coefficient functions.
- `top_path_h1_unif` combines `top_path_dev_unif`, `appCc_h23_unif`, and
  `fixed_curv_h1_unif`; one radius and both action constants are selected
  before the class metric varies.
- `cometricTrace_rfns_p`, `trace_grid_unif p`, and `trace_h2_unif p` provide
  the arbitrary-rank moving-trace chain.  The generic self-trace proof uses an
  explicit source-slot three-cycle and the exact dimension factor from slot
  extension.  Existing rank-two APIs remain compatibility specializations.
- `h1_low_unif` integrates the shorter `range (i+2)` pointwise window using
  only perturbation `H2`; `connSec_h1_unif` instantiates it for the moving
  connection difference.
- `insert_h1_unif` combines the rank-one moving trace, the fixed-background
  connection packet, the two class-first application estimates, and the exact
  insertion factorization.  Class metric jet three is used only by the fixed
  connection term; the perturbation remains `H2`-only.

Normal checks used four Lean threads under the 6 GB cap, one elaboration
process at a time.  The only source repair was local: numeric `Fin` coercions in
the generic trace permutation were replaced by explicit indices so Lean did
not have to normalize modulo-valued numerals at arbitrary rank.

The active order-zero work now splits cleanly.  The curvature arm is an
`H2` moving trace acting on an `H1` curvature passenger.  DLa needs the real
finite-window class-first pointwise factory in its owning lower layer.  VB and
AMix are being audited against the generic trace package.  No metricwise
existential wrapper is counted as a class-first producer.

**Honest denominators.**  The theorem bricks listed above: **100%** locally.
Class-first joint tame producer: still unstated, **0%**.  Actual
`lowreg_bounds_unif`: **0%**.  Dedicated low-regularity supporting machinery
toward `(N)`: approximately **99%**.  `lowreg_dt_unif`: **0%**;
`ricci_flow_unif_existence`: **0%**; whole HCG theorem closure: approximately
**3%**.  Campaign changes remain uncommitted.

---

## 186. Three-dimensional lowering/Morrey replayed and DLa pointwise factory landed (2026-08-06)

The two mixed-tensor producers requested for the dimension-three public route
have been replayed against the current worktree rather than accepted from old
notes or stale artifacts:

- `lowerCc_jet_rfns` and `lowerCc_jet_norm` give the exact order-zero-through-two
  lowering isometry needed to reuse the covariant Morrey stack for mixed
  tensors.
- `morreyRS_unif` chooses its coefficient before the class metric and retains
  generic tensor valence while fixing `finrank = 3` at the public interface.

Both files are focused-green, exactly exported, and axiom-audited with only
`propext`, `Classical.choice`, and `Quot.sound`.

The DLa lower-layer pointwise factory is now also verified.  The old owner
exports only a small `DLaUniformInternal` extraction surface; the proof itself
lives in `DeTurckLieKernelL2JetBoundUniform.lean`.  Its public
`dla_grid_of_conn` has the class-first order
`δ₀,F → ∃ C → ∀ g₀ g_bg g₁ P`, consumes a fixed connection cap only for
`j < 3`, and produces the DLa coefficient grid for `i < 2`.  The owner and
uniform files are focused-green, their exports are current, and the public
producer's axiom audit contains only the standard three axioms.

All verification in this section used one Lean process, one Lean thread, and a
6144 MB cap.  One exact export outlived its external wrapper timeout; its exact
owned process tree was monitored until natural exit, the stale wrapper lock was
quarantined recoverably, and the fresh target was subsequently imported by the
axiom audit.  No timeout is counted as green by itself.

The next integration is the three-dimensional spectral `H1` DLa cap obtained by
combining this pointwise factory with the existing fixed-background connection
class cap and `h1_grid_unif`.  It is recorded as landed in §187 below.

**Honest denominators.**  `MetricLoweringTower`, `morreyRS_unif`, and
`dla_grid_of_conn`: **100%**.  The spectral/class DLa integration is accounted
separately in §187.  Class-first joint tame producer: still unstated, **0%**.
Actual `lowreg_bounds_unif`: **0%**.  Dedicated low-regularity supporting
machinery toward `(N)`: approximately **99%**.  `lowreg_dt_unif`: **0%**;
`ricci_flow_unif_existence`: **0%**; whole HCG theorem closure: approximately
**3%**.  Campaign changes remain uncommitted.

## 187. Three-dimensional class-first DLa `H1` cap landed (2026-08-06)

The reusable fixed-connection pointwise family `connFix_grid_unif` and the
spectral adapter `dla_h1_unif` are now implemented and verified.  The former
packages the order-zero-through-two connection-difference estimates under one
family `F`, chosen from `(gBase, Λ)` before `g₀` varies.  The latter composes
that family with `dla_grid_of_conn` and the dimension-three `h1_grid_unif`.

The resulting affine coefficient functions are chosen from
`(gBase, Λ, δ₀)` before the class metric varies.  The exact budget is class
metric jets through order three, perturbation low jets through order two, and
one separate perturbation order-three top bound.  There is no class metric jet
four and no curvature-jet input.

The fixed-connection module and `UnifDLaH1.lean` are focused-green without
local warnings and exactly exported using one Lean process, one Lean thread,
and the 6144 MB cap.  `dla_h1_unif` has an explicit axiom census containing
only `propext`, `Classical.choice`, and `Quot.sound`.

The next smallest missing analytic branch is the order-zero cancellation tail
`DLb + lieCorr0`; top-path, lower-path, and RHS1 already have class-first
producers.  The whole joint tame producer is not counted until its public Lean
statement and proof exist.

**Honest denominators.**  `dla_h1_unif`: **100%**.  Dedicated DLa
pointwise-to-`H1` machinery: **100%**.  Order-zero cancellation tail:
**0%** until stated and proved.  Class-first joint tame producer: still
unstated, **0%**.  Actual `lowreg_bounds_unif`: **0%**.  Dedicated
low-regularity supporting machinery toward `(N)`: approximately **99%**.
`lowreg_dt_unif`: **0%**; `ricci_flow_unif_existence`: **0%**; whole HCG
theorem closure: approximately **3%**.  Campaign changes remain uncommitted.

## 188. Class-first `lc0VB` producer verified (2026-08-06)

The next order-zero leaf is isolated in `UnifVBH1.lean`.  Its public
`vb_h1_unif` interface fixes dimension three and chooses both affine
coefficient functions from `(gBase, Λ, δ₀)` before the class metric varies.
The class metric budget is exactly jets one and two; the perturbation input is
the low `H2` radius plus one separate third-derivative top bound.

The implementation replays the cancellation-compatible `vb_tame` factorization
using class-first moving traces, connection lowering, and mixed application
packages.  In particular, the fixed cometric trace inside `ipLowCc` is bounded
by the uniform moving-trace package at the zero perturbation, rather than by
the old compactness witness chosen after `g₀`.

The local replay exposed only proof-shape defects: an unsimplified `|0|`, a
private scalar-jet helper, a zero-tensor jet incorrectly delegated to the
zero-th-derivative simp lemma, and a fixed scalar-square normalization.  These
are now closed using `abs_zero`, `iteratedCovGrad_smul_real`, and `mul_pow`.
The ordinary focused check and the exact module export are green under the
single-thread 6 GB discipline.  A direct axiom audit of `vb_h1_unif` reports
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.  A
persistent LSP probe was also attempted after repeated local diagnostics, but
timed out without actionable proof state and was shut down before verification.

**Honest denominators.**  `vb_h1_unif`: **100%**.  Order-zero cancellation
tail: approximately **15%** (one verified leaf; the remaining leaves and their
joint assembly are open).  Class-first joint tame producer: unstated, **0%**.
Actual `lowreg_bounds_unif`: **0%**.
`ricci_flow_unif_existence`: **0%**; whole HCG theorem closure: approximately
**3%**.  The next action is the smallest remaining class-first cancellation
leaf, preserving the same affine low-radius plus separated-top interface.

---

## 180. Explicit convex-jet packages landed; memory gate paused class instantiation (2026-08-05)

The next independent producer from section 179 is now split at the correct data/proof boundary.

- `CurvActionData` stores the rank-two and rank-three order-zero curvature-action constants;
  `IsCurvActionUnif` fixes them before the class metric varies.
- `ConvexJetData` stores the resulting finite `H²` and `H³` coefficients;
  `IsConvexJetUnif` records both squared covariant-jet estimates along every convex tensor path.
- `convex_h23_of_act` and `convex_jets_of_act` convert the first package to the second using
  `covsum_hs_two`, `covsum_hs_three`, and spectral-norm convexity.  Both are focused-green,
  warning-free, contain no `sorry`, and their temporary axiom census reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

The intended metric-class adapter is routine composition of `unifCurvAction0_of` and
`unifCurvAction3_of`, but its old import closure reached the unrelated residual coefficient
tower and the missing `TsTransport.olean`.  The dependency boundary has therefore been corrected:
the canonical order-zero block was extracted into `UnifCurvatureSup.lean`, the old
`UnifCurvatureJetBound.lean` retains only its compatibility layer, and
`UnifCurvatureJet1Diff.lean` now imports the light core and calls `unifCurvSup`.  The moved and
retained blocks were mechanically compared, the new core is focused-green, and static import
analysis confirms that the chain through `UnifCurvActionZero` is now `TsTransport`-free.

Downstream verification remains paused.  Exporting the new core unexpectedly replayed 9,276
jobs and entered `ConnectionDifferenceArmRfnsBound`; the memory guard stopped the owned process
tree when free physical memory reached 912 MB.  The deleted dependency artifact was restored
from the audit worktree after exact source-hash and Lean-toolchain checks.  There is no remaining
Lean/Lake process or elaboration lock.  This is a performance/verification blocker, not a failed
proof.  Under the fail-closed rule, resume only after explicit user instruction and restart the
interrupted export from the beginning; do not retry under the same memory/dependency conditions.

The next declaration after safe downstream verification is `class_curv_actions`, followed by
the public class-first `convex_h23_unif` wrapper.  Only then should the RHS tame consumers replace
their metric-late convex `H²`/`H³` choices.

**Honest denominators.** Explicit curvature-action-to-convex package layer: **100%**.
Metric-class instantiation of that package: **0%** as a declaration. Class-first joint
H3-to-H1 / H2-to-H1 tame producer: **0%**. Actual `lowreg_bounds_unif`: **0%**.
Dedicated low-regularity supporting machinery toward `(N)`: approximately **94%**.
`lowreg_dt_unif`: **0%**; `ricci_flow_unif_existence`: **0%**; whole HCG theorem closure:
approximately **3%**. Campaign changes remain uncommitted.

---

## 179. Class-first H2/H3 single-tensor grid package closed (2026-08-05)

The routing correction in section 178 is now implemented. The class-first
single-tensor grid branch is distinct from the two-arm product grid used by
`appCc_grad_l2`.

- `rankTwoGridC` / `rank_two_grid_unif` combine the existing rank-two Morrey
  cap, class-first mixed GN coefficient, and the per-cell
  `grid_prod_int_le`. Their constant is chosen before the metric and tensor
  vary and consumes only metric jets of orders one and two.
- `h2GridC` / `h2_grid_unif` cover `k <= 2`; `k = 0` is the honest total-volume
  branch from `volumeReal_cross`, while positive orders use the new producer.
- `h3TopGridC` / `h3_top_grid_unif` cover the total-order-three grid with the
  lower H2 radius separated from the top third-derivative bound.

All six declarations are focused-green without warnings and contain no
`sorry`. A temporary axiom census for the three grid theorems reports only
`propext`, `Classical.choice`, and `Quot.sound`. The exact module artifact is
not refreshed: a guarded target build
replayed the large dependency closure, entered
`ConnectionDifferenceArmRfnsBound`, and crossed the physical-memory floor at
about 1.1 GB free. The interrupted dependency artifact was restored from an
aligned worktree only after exact source-hash and Lean-toolchain equality were
checked. This is a verification/performance boundary, not a theorem error;
do not rerun the same export until the memory/dependency situation changes.

The next source-level analytic adapter is the class-first finite summation
around `grid_h1_le` and `grid_h2_le`. The independent `appCc_grad_l2` branch
still needs the class wrapper around the explicit two-arm coefficient after
that lower module can be exported safely.

**Honest denominators.** Class-first positive-order/H2/H3 single-tensor grid
lane: **100%**. Class-first joint H3-to-H1 / H2-to-H1 tame producer: **0%**.
Actual `lowreg_bounds_unif`: **0%**. Dedicated low-regularity supporting
machinery toward `(N)`: approximately **94%**. `lowreg_dt_unif`: **0%**;
`ricci_flow_unif_existence`: **0%**; whole HCG theorem closure: approximately
**3%**. Campaign changes remain uncommitted.

---

## 178. Finite H3 comparison and class-first GN producer closed (2026-08-05)

The first two analytic leaves identified by the joint-tame audit are now
explicit and verified.

- `covsum_hs_three` gives the finite H3 covariant-sum comparison without an
  all-order curvature family.  It consumes only `IsCurvAction0 g s K0` and
  `IsCurvAction0 g (s + 1) K1`.  The class curvature lane now supplies the
  required fixed ranks two and three through `unifCurvAction0_of` and
  `unifCurvAction3_of`.
- The single-metric mixed-valence interpolation theorem now exposes the exact
  coefficient `gnRsConst n k sqrt(vol)`, while preserving its old existential
  API as a compatibility wrapper.
- `UnifGagliardoNirenberg.lean` proves the two-sided real-volume/radius adapters,
  an explicit class cap for both `sqrt(vol)` and its reciprocal, and
  `gn_rs_unif`.  Its constant is chosen before the class metric, tensor
  valences, tensor, and interpolation rung.

The new class-first GN chain is focused-green without warnings.  A temporary
in-source axiom census reports only `propext`, `Classical.choice`, and
`Quot.sound`.  The large GN source and its one directly missing dependency were
refreshed with `.olean`-only targets; attempts to refresh the new downstream
module were stopped when free physical memory fell below 1 GB, so no broader
targeted-build claim is made for that module.

The two-arm grid used directly by `appCc_grad_l2` now exposes the explicit
per-metric coefficient `gridRsConst`; its old existential API is a compatibility
wrapper and the refactored source is focused-green.  The remaining class wrapper
is finite-sum monotonicity from `gnClassC`.  Its `.olean`-only refresh was stopped
at the memory threshold, so the downstream wrapper has not yet been added.

Routing correction: `h2_grid_int` and `h3_top_grid_int` do not call the two-arm
theorem.  They use GN directly plus the supercritical rank-two pointwise bound.
Their common next producer is a positive-order single-tensor grid theorem built
from `morreyTwoC_spec` and `gn_rs_unif`; the `k = 0` H2 case is a separate
volume branch.  No new Sobolev theorem is needed, but these are distinct
consumer shapes and must not be counted as closed by the two-arm refactor.

**Honest denominators.**  `covsum_hs_three`: **100%**.  Class-first mixed GN
kernel: **100%**.  The joint H3-to-H1 / H2-to-H1 tame producer itself remains
unstated and therefore **0%**.  Actual `lowreg_bounds_unif`: **0%**.  Dedicated
low-regularity supporting machinery toward `(N)`: approximately **93%**.
`lowreg_dt_unif`: **0%**; `ricci_flow_unif_existence`: **0%**; whole HCG theorem
closure: approximately **3%**.

---

## №176 (Codex executor, 2026-08-05) — common-time package split LANDED;
## `lowreg_gate_unif` removed from the lifetime path

The class-uniform gate named in №175 is mathematically too strong for `(N)`'s
order-three class and is not the right next producer for the common lifetime.
The live rung-five coefficient uses `hs_le_jet g 2 4` and
`galRepJet_le g 6`.  The explicit Bochner recursion shows that the H6 hard
comparison reaches curvature-action derivative order four and tensor rank six;
an honest class producer needs curvature jets through five, hence metric jets
through seven by the established Palatini budget.  Order-at-most-three data
cannot supply it.  No theorem named `lowreg_gate_unif` is asserted.

This does not obstruct a uniform low fixed-point time.  The strict-open chain
has deleted the old H2 static-force floor completely; only the H1 zero-state
number `D` remains in `lowregHorizon`.  The common lifetime therefore belongs
below the all-rung energy packages.

The corrected explicit interfaces are now implemented:

- `LowRegBoundData` is the certified threshold plus the six horizon numbers;
- `IsLowBoundsAt g₀ g_bg K` is the exact background-aware analytic input of
  `lowreg_partial_sol_of_bounds`;
- `IsLowSolveBg` retains the fixed-point output at those exact witnesses;
- `lowreg_sol_of_data` runs the existing engine from that package;
- `IsLowBoundsUnif gBase Λ K` fixes one packet before every class member;
- `unif_solve_of_bounds` gives the single positive closed horizon and a low
  solve for every member and every smaller positive time.
- `LowRegHorizonData` / `IsLowBoundCap` weaken literal packet equality to the
  four upper caps and two lower radius floors that horizon monotonicity needs;
- `IsLowBoundsCap` / `unif_solve_of_caps` are the preferred weakest uniform
  interface and assembly, retaining each metric's exact packet.

Both new modules pass focused verification and direct targeted builds;
`UnifClassBounds` also passes its direct targeted refresh.  The narrow package-only
axiom census prints only `propext`, `Classical.choice`, and `Quot.sound`.  The
full campaign census was stopped by the physical-memory guard while loading the
settled all-order lane, not by a Lean diagnostic.  These are honest data/proof/output packages and an
assembly theorem, not the missing coefficient producer.  The actual next
analytic endpoint is `lowreg_bounds_unif : ∃ U, IsLowBoundsCap gBase Λ U`.
Its remaining inputs are class-uniform realization/A2/affine/nonlinearity
constants; the already-proved fixed-background `nZeroC` route supplies the
zero-state slot once those certificates are exposed.

The dimension audit is also settled but not acted on: the Hamilton restart
chain already carries `Module.finrank ℝ E = 3`, so specializing `(N)` would be
mechanically local, but it would narrow the explicitly handed-off generic API.
No endpoint signature changed without that design authorization.

**Honest denominators.**  `lowreg_loMass` and the per-metric all-real chain:
**100%**.  The background-aware common-time interface and conditional assembly:
**100%**; its actual envelope producer `lowreg_bounds_unif`: **0%**.  Dedicated
low-regularity supporting machinery toward `(N)`: approximately **90%**.
`lowreg_dt_unif`: **0%**; `ricci_flow_unif_existence`: **0%**; whole HCG theorem
closure: approximately **3%**.  Campaign changes remain uncommitted.

---

## 177. Explicit realization/zero packages closed; joint tame producer isolated (2026-08-05)

This pass replaces the remaining informal realization and zero-state slots by
explicit data/proof packages without changing the final endpoint statements.

- `LowRegRealizeData` / `IsLowRealizeUnif` / `exists_lowRealize` close the
  finite rank-two realization face.  The predicate records
  `0 <= threshold`, `threshold < 1`, a positive common realization radius, and
  the class-uniform realization theorem.  The route uses the rank-two Morrey
  coefficient and the rank-two, order-zero curvature-action bound; it does not
  assume an all-rank curvature family.
- `LowRegZeroData` / `IsLowZeroUnif` / `exists_lowZero` / `lowZero_nfun` close
  the zero-state face with one nonnegative common `zeroBd` cap while retaining
  each metric's smooth-core continuity witness.
- Both package modules pass focused verification and exact targeted refreshes.
  The narrow package census reports only `propext`, `Classical.choice`, and
  `Quot.sound`; no `sorryAx` enters the exported realization/zero chain.

The remaining analytic endpoint is now a single **class-first joint tame
producer**.  The preferred interface is cap-oriented: each metric keeps an
exact tame packet, while the class package supplies common upper caps for
`top`, `base`, and `slope`, plus a positive lower floor for `outer`.  The exact
packet must carry `hcont`, `Continuous coreN`, and the joint three-arm `htame`
certificate so that the zero package can reuse the same continuity witness.
This producer is not yet stated or proved, so it remains 0%.

A first external consult correctly observed that bounded-curvature theorems of
Shi/Simon type validate the class-first mathematical statement, but they do not
construct `IsLowBoundsCap`.  A live repository audit found no existing
bounded-curvature initial-flow producer: the native Shi/Bernstein declarations
assume a flow, and the available restart path depends on `(N)`.  Therefore a
curvature-first proof would introduce a new major analytic theorem and is not
the selected implementation route.

The producer-only consult prompts are
`CONSULT_UNIF_TAME_PRODUCER.md` and
`CONSULT_UNIF_TAME_PRODUCER_FOLLOWUP.md`.  The follow-up requires an exact A/B/C
decision, a live constant/jet-budget table, and the first three lower-layer Lean
bricks.  The current working hypothesis is Candidate C.  Its first risk is the
finite-rank mixed Sobolev/application layer for the H3-to-H1 top arm and the
H2-to-H1 lower arms; unlike the completed H2 realization route, the H3 tame
comparison may additionally need the rank-three order-zero curvature-action
cap.  This must be proved from the live call graph before adding that finite
rank adapter.

`LowRegBgA2Time` remains a continuation/Galerkin packet and is not part of this
producer.  The phrase "top second-order remainder arm" is used here to avoid
conflating it with that packet.  The invalid all-rung `lowreg_gate_unif` route
also remains excluded because rung five exceeds the order-three varying-metric
jet budget.

**Honest denominators.**  Per-metric all-real chain: **100%**.  Explicit
common-time package and conditional cap assembly: **100%**.  Realization face:
**100%**.  Zero-state face: **100%**.  Class-first tame producer: **0%**.
Actual `lowreg_bounds_unif`: **0%**.  Dedicated low-regularity supporting
machinery toward `(N)`: approximately **92%**.  `lowreg_dt_unif`: **0%**;
`ricci_flow_unif_existence`: **0%**; whole HCG theorem closure: approximately
**3%**.  Campaign changes remain uncommitted.

---

## 181. Three-dimensional class-first application chain closed (2026-08-06)

The public uniform-existence interface is now intentionally specialized to
dimension three.  Generic tensor valences are retained only where that makes
the implementation and the finite consumer table smaller.

The following class-first producer chain is focused-green, warning-free,
directly exported, and has temporary axiom censuses containing only `propext`,
`Classical.choice`, and `Quot.sound`:

- `appCc_h23_unif` closes the rank-`(4,2)` coefficient acting on `∇²U` from
  spectral `H³` to spectral `H¹`.
- `fiberLp3_le_6` exposes the exact finite-volume `L⁶ -> L³` factor, and
  `fiberLp3_le_6_unif` caps it uniformly over the metric class without metric
  jet assumptions.
- `appRS_h1_of` is the supplied-provider mixed `H¹ × H² -> H¹` kernel.  The
  old metricwise `appRS_h1_h2_h1` now calls this kernel; its duplicated proof
  body was removed.
- `appRS_h1_unif` is generic in tensor valence but fixed to dimension three.
  It consumes only metric jets of orders one and two and covers all four live
  mixed consumers plus the lower-path `(0,2,2)` specialization.
- `appCc_h1_unif` converts that specialization from intrinsic mixed `H¹` to
  the exact spectral rank-two `H¹` norm and uses the finite `H²` covariant-jet
  comparison for the passenger.
- `lower_jet_unif` assembles the lower order-zero and differentiated arms with
  the coefficient `C₀ + C₁`.  The extra metricwise Morrey enlargement in the
  old `lower_jet_h1` is no longer present because both class cells produce the
  needed pointwise bounds internally.

Ordinary verification for these medium files used four Lean threads with the
6 GB Lean memory cap.  One short client timeout orphaned only its elaboration
lock after the owned Lean process had already exited; the confirmed stale lock
was moved recoverably before restarting the check.  No overlapping Lean
processes were run.

The next genuine frontier is no longer the lower application layer.  It is the
class-first cap/floor producer for the numerical witnesses still chosen after
`g` in the top-path and RHS tame packets.  Read-only audits are resolving the
exact smallest declaration before another wrapper is added.

**Honest denominators.**  Every declaration listed above: **100%**.
Class-first joint tame producer: still unstated, therefore **0%**.  Actual
`lowreg_bounds_unif`: **0%**.  Dedicated low-regularity supporting machinery
toward `(N)`: approximately **97%**.  `lowreg_dt_unif`: **0%**;
`ricci_flow_unif_existence`: **0%**; whole HCG theorem closure: approximately
**3%**.  Campaign changes remain uncommitted.

---

## 182. Class-first top deviation and explicit coefficient packages landed (2026-08-06)

The top-path constant leak has been reduced to the fixed curvature commutator.
Every declaration in the following chain is focused-green, warning-free,
directly exported, and has a temporary axiom census containing only `propext`,
`Classical.choice`, and `Quot.sound`:

- `invDiff_zero_unif`, `invDiff_slot_unif`, and `invDiff_grid_unif` select the
  inverse-metric derivative-grid constants before both metrics vary.
- `appRS_h22_unif` supplies the dimension-three mixed `H² × H² → H²`
  product cell needed by the order-one coefficient packet.
- `inv_coeff_h2_unif` selects one positive spectral `H²` radius and one
  pointwise/two-jet inverse-coefficient constant before the class metric.
- `h1_grid_unif` and `h2_tame_unif` are the class-first finite-summation
  adapters for the exact affine grid conclusions used by the RHS packets.
- `cometricTrace_rfns` bounds the self-cometric double trace by `dim^6`.
  The explicit extraction interfaces `pcc_rfns_of_bound` and
  `ricci_sub_rfns` then avoid the old metricwise compactness witness.
- `PrincipalCoeffDimBound` gives pointwise and `L²` jet bounds for the
  DeTurck principal, Ricci principal-difference, and trace-Hessian-difference
  coefficients with explicit constants `appCcGdiag i * dim^8` and
  `(10 / 4) * appCcGdiag i * dim^8`.
- `phi_dev_h2_unif` combines those constants with `inv_coeff_h2_unif` and
  selects the unintegrated top-deviation radius and coefficient before `g`.
- `top_path_dev_unif` transports the same class-first estimate through the
  canonical coefficient path integral.

The exact remaining top-path obstruction is now representation-level rather
than analytic.  `gradSwapCurvCoeff` is an opaque choice from the curvature
commutator specification.  Uniform `Rm` and `∇Rm` bounds already exist from
metric jets through order three, but the library lacks a public canonical
readout and one-derivative theorem identifying this coefficient with the
slot-free curvature operator.  The smallest next tensor API is the canonical
`gradSlotCurvCoeff` together with its fibre readout and `gradSlot_cov_eval`;
after that, `phiCurv_jet_unif` feeds `appCc_h1_unif` directly.

In parallel, the RHS branch is being reduced at its primitive coefficient
producers.  The generic class-first `h1_grid_unif` and `h2_tame_unif` are now
available, but the final `rhs0`/`rhs1` coefficient functions must still be
selected before `g`; metricwise existential wrappers do not establish that
quantifier order.

Normal focused checks and direct exports used four Lean threads under the
6 GB cap.  The 1200-line extraction/path files used two threads.  No Lean
processes overlapped.

**Honest denominators.**  Every declaration listed as landed above: **100%**.
Class-first joint tame producer: still unstated, therefore **0%**.  Actual
`lowreg_bounds_unif`: **0%**.  Dedicated low-regularity supporting machinery
toward `(N)`: approximately **99%**.  `lowreg_dt_unif`: **0%**;
`ricci_flow_unif_existence`: **0%**; whole HCG theorem closure: approximately
**3%**.  Campaign changes remain uncommitted.

---

## 183. Class-first coefficient H2 packets and Ricci order-one arm landed (2026-08-06)

The connection-difference and moving-trace coefficient branches now select
their constants before the class metric varies.  The following declarations
are focused-green, warning-free, directly exported, and have axiom audits
containing only `propext`, `Classical.choice`, and `Quot.sound`:

- `sharpFlat_grid_unif` and `connDiff_grid_unif` are the class-first pointwise
  grids for the inverse recovery endomorphism and lowered connection
  difference.
- `trace2_grid_unif` is the class-first rank-two moving-trace grid.  The
  metric-local rank-generic `trace_grid_rf` remains its compatibility API.
- `h2_low_unif` integrates a low-window pointwise grid uniformly over the
  three-dimensional metric class, using only class metric jets one and two.
- `trace2_h2_unif` and `connLow_tame_unif` are the resulting moving-trace and
  affine lowered-connection `H2` packages.
- `ricci1_h2_unif` composes those packages with `appRS_h22_unif`.  Its explicit
  coefficient functions are
  `Capp * (2 * Bt R) * (15 * Bc0 R)` and
  `Capp * (2 * Bt R) * (15 * Bc1 R)`.

The fixed-curvature representation gap recorded in §182 is also closed.
`slotFreeOpCc` is the canonical arbitrary-rank free-slot curvature operator,
`slotFree_cov_eval` identifies its covariant derivative with the slotwise
`∇Rm` action, and `gradSlot_cov_eval` exposes the rank-two result in the exact
spectral `covGrad` vocabulary.  A monolithic proof exceeded the heartbeat
budget; factoring the pointwise curvature identity and smooth-section identity
into separate declarations reduced the same check to about half a minute at
the ordinary 3.2-million proof-heavy setting.

The next two honest producers are independent.  The Lie order-one arm needs a
class-first `H2` cap for `connDiffSection gBase g₀`, using the already proved
pointwise orders zero through two and class metric jets through order three.
The Ricci order-zero arm needs the class-first order-zero/one jet grid for
`gradSlotCurvCoeff`, now enabled by `gradSlot_cov_eval`.  Neither final RHS arm
is counted complete until its theorem is stated and checked.

Normal verification used four Lean threads and the 6 GB Lean memory cap, with
one Lean process at a time.  The fixed-curvature file was treated as a semantic
hotspot; proof factoring, rather than permanent single-threading or an
unbounded heartbeat increase, resolved its performance issue.

**Honest denominators.**  Every declaration listed as landed above: **100%**.
Class-first joint tame producer: still unstated, therefore **0%**.  Actual
`lowreg_bounds_unif`: **0%**.  Dedicated low-regularity supporting machinery
toward `(N)`: approximately **99%**.  `lowreg_dt_unif`: **0%**;
`ricci_flow_unif_existence`: **0%**; whole HCG theorem closure: approximately
**3%**.  Campaign changes remain uncommitted.

---

## 193. Lift packages explicit; moving-trace H3 closed; high-A2 order wall isolated (2026-08-06)

The external re-audit at remote commit `f8e47f859` was checked against the
actual declaration tree.  Two premises were corrected before more consumer
wrappers were added:

- `DenseTameData`, `IsDenseTameAt`, `exists_dense_tame`, and
  `dense_tame_unif` do not exist at this commit.  `UnifDenseTame` exports
  `coreN_outer_unif` and `lowRegN_outer_unif`, which bound the total
  nonlinearity rather than completed operator-valued A1 maps.
- the general dense-extension API is not the obstruction: `exists_extend_le`
  already preserves an affine envelope, and the background time files contain
  the standard dense equalizer argument for compatibility squares.

The corrected class-first package boundary is now explicit and focused-green:

- `BgLiftData` stores the coefficient radius, contraction, affine zero/slope,
  the actual low-solve force cap, the radius sandwich
  `stateRad <= coeffRadius <= K.realize`, the force margin, and the common
  low/lift horizon before the class metric varies.
- `BgLiftOps` is data only, while `IsBgLiftAt` is the metricwise proof
  certificate.  Its fields use the actual `lowCoreDataBg` A1/A2 arms, both
  completed continuity/bound certificates, and both inclusion squares.
- `liftHiNBg`, `lowBaseNBgWith`, and `hiNBg_incl` give the background-aware
  frozen high/low split and its scale compatibility without constructing an
  orbit or reselecting time.

The arbitrary-background pointwise H2 program also advanced:

- `dlaBg_pair_h2` is complete in `LowRegBgC0PairH2`;
- `app_h3_tame`, `inv_slot_pair_h3`, and `trace1_pair_h3` close the previously
  missing moving one-trace H3 producer with the exact
  `D3 + D2 + A * D2` scale;
- `dlbIns_pair_h2` closes the cancellation-preserving `DLb + Insert` H2 arm;
- `lie0_bg_pair_h2` combines all three arms after the exact background split
  and exports the common five-term critical modulus.  The complete pointwise
  arbitrary-background order-zero `H2` pair is therefore closed.

The remaining metricwise A1 chain is mechanical: the path-integrated background C0 pair,
`c0_bg_pair_h2`, `a1Hi_bg_pair`, and `radialA1HiBg_pair`, followed by the
already defined canonical completions `lowA1HiBg` and `lowA1LoBg`.  The later
class-first producer still needs a common radius and affine H2 bound for the
actual `lowCoreDataBg` C0 arm.  `refold_aff_bg` is not a substitute: its core
formula is `c0CoreData + oneCoreBg`, and no theorem in the current tree
identifies that operator with the actual background core required by
`IsBgLiftAt`.

The A2 high arm has one honest unresolved order-budget issue.  The new
dimension-only `hs_two_le_jet` proves the easy covariant-jet2 to spectral-H2
direction.  The existing `appD2Hs_norm` route still needs the hard spectral-H4
to covariant-jet4 comparison.  The class-first packet currently stops at
`covsum_hs_three`; a finite H4 Bochner step introduces differentiated curvature
and naturally asks for a fourth metric jet.  The proposed fixed-background
graph-norm shortcut was audited and does not remove this order: the rough
Laplacian on `(0,2)` tensors has a zeroth-order coefficient containing second
metric derivatives, and squaring it differentiates that coefficient twice.
Equivalently, the intrinsic `H4` commutator contains `nabla^2 Rm`.  The smallest
honest continuation of the canonical adjacent-scale route is therefore a
class-four `covsum_hs_four`/`appD2Hs_norm_unif` producer.  If the class-three
budget remains binding, this part needs a substantive differentiated parabolic
bootstrap for `nabla u`, not another completion wrapper.  Until one of those
two designs is implemented, no class-first A2 existence theorem is to be
claimed.

**Honest denominators.**  The new scalar interface, metricwise certificate
interface, frozen high-force adapter, all three order-zero H2 arms, their full
`lie0` assembly, moving-trace H3 package, and easy H2 comparison: **100%**
individually.  `IsBgLiftAt` existence producer: **0%**.  Full
arbitrary-background A1 pair endpoint: unstated, **0%**; its complete
pointwise order-zero input is now **100%**, while the metricwise path/refold
assembly and class-first actual-core bound remain.  Class-first A2 high
producer: unstated, **0%**; its canonical route is blocked at the hard H4 input
comparison, and preserving class three requires a new differentiated-flow
design.  `lowreg_apply_two_bg`, the background all-order adapter,
`lowreg_dt_unif`, and `ricci_flow_unif_existence`: **0%**.  Dedicated uniform-
existence machinery overall remains approximately **80%**; whole HCG theorem
closure remains approximately **3%**.  Campaign changes remain uncommitted.

---

## 194. Checkpoint verified; arbitrary-background inclusion square landed
## (2026-08-07, overnight session)

**Checkpoint.**  `radialA1HiBg_pair` (`ShortTime/LowRegBgTime.lean:795`) —
the unverified pre-pause proof — focused check GREEN first run (73 s, zero
warnings).  The scalar factorization (`E0 = 2(Fs²+Fb²)+F1²`, radicand
`= E0·D²`, then `sqrt_scale`) and the `simpa only [lowCoreDataBg, T0, U0]`
core refold worked as written.  The metricwise high-A1 core pair is
complete; `LowRegBgTime.md` updated.

**The metricwise inclusion square** (№193's "next missing metricwise
adapter") landed as `lowA1Bg_comm_bg` (`LowRegBgTime.lean`), first-try
GREEN (28.8 s): the arbitrary-background completed square, mirroring the
diagonal `lowA1Bg_comm` density skeleton with the smooth-core square
supplied by the NEW bundle-generic `a1_comm`
(`DeTurck/DeTurckRemainderLowBaseA1Comm.lean`, 18.8 s GREEN + targeted
build 9909 jobs).  Route judgment recorded there and in its `.md`: the
preferred expose-in-place of the private `a1_comm_any` was attempted and
BYTE-REVERTED — the 10.8k-line `DeTurckRemainderLowBaseLip.lean` monolith
dies at the lane's focused-check memory budget
(`lean::memory_exception` @375 s under `-LeanMemoryMB 6144`); the identity
was reassembled from the PUBLIC `a1_pair`/`a1_h3_h2`/`a1_h2_h1` instead
(№162-precedent judgment).  Fold-back note: when the monolith is next
legitimately rebuilt, its private copy should defer to this `a1_comm`
(no import cycle).  No parallel completed maps created; `refold_aff_bg`
untouched; A2 stop condition carried verbatim into `LowRegBgTime.md`.

**Next.**  Class-first A1 (the №193 frontier): one common radius + affine
constants before `g` varies for the actual `lowCoreDataBg` arms, feeding
the `IsBgLiftAt` producer (0%).  Read-only scout dispatched for the
g-dependence inventory of the pair constants and the existing Unif*
uniformization producers before any statement is written.

**Honest denominators.**  `ricci_flow_unif_existence` **0%**; `IsBgLiftAt`
producer **0%**; metricwise `a1Hi_bg_pair` + `radialA1HiBg_pair` +
`lowA1Bg_comm_bg` **100%**; dedicated machinery ≈**80%**; whole HCG
≈**3%**.  Campaign delta still uncommitted (user-side).

---

## 195. Class-first A1 scout adopted: gap ledger G1–G5; IsBgLiftAt is 10/14
## produced; smallest brick = `c0_bg_aff` WITH a feasibility gate (2026-08-07)

Read-only scout over the class layer, the A1 constant injection sites, and
the `IsBgLiftAt` consumer.  Adopted findings (file:line evidence in the
scout's report, key ones repeated here):

- **The lane runs at class 3** (`IsLowBoundsUnif`, `LowRegUnifBounds.lean:48`,
  hypotheses = `MetricUniformEquivalentOn` + `∀ a ≤ 3,
  MetricCovDerivOrderBoundOn`).  Class-first statements must take EXACTLY
  this pair — a 4th jet silently promotes the lane to class 4.
- **`IsBgLiftAt` (`LowRegBgLift.lean:77`, 14 fields): 10 already produced**
  (`a1*_cont/core` by `radialA1HiBg_pair`/`radialA1Bg_pair` + completions;
  `a1_square` by №194's `lowA1Bg_comm_bg`; the A2 cont/core/square by
  `radialA2Bg_lip`).  Frontier = `a1Hi_bound`/`a1Lo_bound` (affine),
  `a2Hi_bound`/`a2Lo_bound` (contraction, BLOCKED by the A2 gate), plus
  `D.coeffRadius` under the three per-`g` radii (G3).
- **`LowRegForceHiBg` needs NOTHING more from A1**: `hiNBg_incl` consumes
  only the two squares — already served.
- **Gap ledger**: G1 = A2 completion constant (blocked: `covsum_hs_four` /
  `appD2Hs_norm_unif` DO NOT EXIST; bootstrap has zero footprint; but the
  A2 walls sit at the completion constant, NOT at coefficient smallness —
  the diagonal `lowA2_small`/`c2_h2_small` machinery exists and
  `refold_low_split` bounds the C2 arm fibrewise by `κδ/(1−δ)²`, diagonal
  only).  G2 = metricwise affine bound for the ACTUAL `lowA1HiBg/LoBg`
  (existing envelopes are polynomial `(1+A²)^…` — wrong shape; the `.md`
  claim that `refold_aff_bg` is no substitute is VERIFIED: its C0 is
  `lowZeroAInt + phiMetCurvCoeff g g g`, not `lowBaseData`'s, and
  `refold_low_split` equates only the total).  G3 = class-uniform lower
  bound for the three coefficient radii (copy `lowRealizeData`'s
  closed-formula pattern, `UnifRealizeRadius.lean:91`).  **G4 = the five
  pair constants `{Bs,B0,B1,O0,O1}` are OFF the critical path if G2 lands
  by the affine route** — recorded so nobody grinds them.  G5 = split
  `IsBgLiftAt` into `IsBgA1At` + `IsBgA2At` (zero external consumers,
  free) so the blocked A2 gate stops entangling the workable A1 half.
- **Smallest brick = `c0_bg_aff`** (arbitrary-background sibling of the
  EXISTING `c1_bg_aff`, `LowRegBgC1Time.lean:157`, which already has the
  target shape): home `LowRegBgH2.lean` beside `lowC0_bg_h2`; producers
  `bgCorr_h2` + private `fixedBg_h2` in hand; the ONE new piece is an
  affine-in-`A` diagonal bound for `selfLowInt g g T` (note
  `phiMetCurvCoeff g g g` is `T`-independent — a pure `B0` constant).
- **FEASIBILITY GATE (scout's honest risk, adopted as a STOP condition)**:
  the diagonal affine C0 bound MAY BE FALSE — plausibly why the refold
  lane exists.  The executor must FIRST derive, on paper from
  `selfLowInt`'s actual definition and the `c1_bg_aff` mechanism, whether
  `jet₂(selfLowInt g g T)` is affine in the `H³` jet at bounded `H²`
  radius, and STOP-and-report if any genuinely quadratic-in-`A` product
  (`∇³T·∇T`, `∇²T·∇²T` with no absorbable small factor) survives.  On
  STOP the alternative is a DESIGN decision reserved for the user:
  restate `IsBgLiftAt`'s core fields against a background-refolded bundle
  + prove the arbitrary-background `refold_low_split` analogue.

**Dispatch order**: BG-1 = feasibility gate + `c0_bg_aff` (or STOP report);
then G5 split + G3 radius formula; then `bgA1_aff` → `IsBgA1At` producer.
A2 (G1) stays at its stop condition — no ruling tonight; the two honest
options with their exact Lean footprints are ready for a morning decision.

---

## 196. BG-1 gate FAILED and the finding is sharp: the diagonal `C0` arm is
## NOT affine in the `H³` jet — `c0_bg_aff` must not be attempted (2026-08-07)

№195's feasibility gate was run on paper before any Lean.  **It fails, and the
failure is a theorem-level fact, not a missing estimate.**  `c0_bg_aff` as
specified is FALSE; no executor should retry it in that shape.  No Lean was
written, no claim taken, no file edited except this ledger and
`ShortTime/LowRegBgH2.md` (full derivation recorded there).

**The quadratic witness.**  `.C0 = selfLowInt g gB T … + phiMetCurvCoeff g gB g`
(`c0_eq`, `DeTurck/DeTurckRemainderLowBaseAction.lean:3807`).  The curvature
summand takes no `T` (`PhiMetSymmetry.lean:232`) — pure `B0`, as №195 guessed.
The integrand of the first summand is `rhsSelfLow` (`…Action.lean:3750`), exactly
five arms by `selfBase_decomp` (`…Action.lean:11165`); **three of them are
quadratic in the connection difference**, i.e. `(algebraic in gm⁻¹) ⋆ ∇P ⋆ ∇P`
with `P = s·T`:

- `lc0VB` = `2 • trace( connDiff(g₁,g₁,g₀) ⊗ ι_{W(g₁,g₀)} )`
  (`DeTurckCoefficients/LieCorr0Core.lean:144`) — connection difference times the
  DeTurck vector field, itself a trace of the same connection difference;
- `lc0AMix`, the mixed connection-difference term (`LieCorr0Core.lean:173`);
- the `ricciAA` half of `ricciGoodLow` (`ricciGood_act_tame`, `…Action.lean:7072`),
  which the tree itself calls "the connection-difference-quadratic Ricci arm …
  both insertions carrying exactly one derivative of the state"
  (`Sobolev/TensorHilbert/SelfLowCapWindows.lean:277`).

`lowJetSq … 2` takes two covariant derivatives, so Leibniz produces
`∇³P ⋆ ∇P` and `∇²P ⋆ ∇²P` — precisely the products №195 named as the STOP
condition — and **neither factor is absorbable**.  The tree's only sup-norm
producer for a derivative of the state is `gradCapLin`
(`Sobolev/TensorHilbert/TameGridProd.lean:492`): `‖∇P‖²_∞ ≤ c‖P‖²_{H³}`, i.e. the
`L^∞` price of ONE derivative is the full `A`, never `R` (`H¹ ⊄ L^∞` at `n=3`);
`‖∇²P‖_∞` would cost `H⁴`, which class three forbids; and `hδ` bounds `‖P‖_∞`
only, no derivative.  Every route leaves both factors priced by `A`.

**Sharpness (why this is not bookkeeping).**  (i) The tree's own `R`-priced
coefficient producers are already quadratic and deliberately sharpened:
`lc0VB_h2_tame` / `lc0AMix_h2_tame` (`…Action.lean:8136`, `:8506`) give
`(D R · A²)²`, `lieCov_h2_tame` (`:10965`) gives `(D R·(A+A²))²`, and
`ricciAAJet` (`TensorHilbert/TameArmJets.lean:298`) — whose docstring advertises
"exactly ONE power of `‖P‖²_{H³}`" against the older `ricciAACap`'s degree
`6(i+1)` — still reads `(K₀+K₂A²)(1+A²)` at `i = 2`.  The one affine arm is
`lc0Riem` (`:7472`, `K(1+A²)`), the fixed-curvature arm.  (ii) A scaling witness
kills the claim outright: `P_λ = ε φ(x/λ)` in one chart at `n = 3` has
`‖P‖_∞ = ε`, `‖P‖_{H²} ≍ ελ^{-1/2}`, `‖P‖_{H³} ≍ ελ^{-3/2}`,
`‖∇²P⋆∇²P‖_{L²} ≍ ε²λ^{-5/2}`; fixing `R` and letting `A → ∞` gives `λ = R/A`,
`ε = R^{3/2}A^{-1/2} → 0` (so `hδ` holds with room), and
`‖∇²P⋆∇²P‖_{L²} ≍ R^{1/2}·A^{3/2}`.  `A^{3/2}` outgrows `B0(R)+B1(R)·A` for every
fixed `R > 0`.  This is the sharp Gagliardo–Nirenberg value of `‖∇²P‖²_{L⁴}` and
it is attained, so no better product estimate exists.

**Why `c1_bg_aff` is affine and `c0` cannot be.**  `c1_bg_aff`
(`LowRegBgC1Time.lean:157`) is not a Leibniz computation: it specialises the
existing pair producer `rhs1_path_tame` (`LowRegRhsOne.lean:203`) at `T' = 0`
after `c1_eq`.  Underneath, the order-ONE coefficient carries exactly ONE
connection-difference factor (`C1 ~ f(gm⁻¹) ⋆ ∇P`), so `∇²C1` gives `∇³P`
(linear in `A`), `∇²P⋆∇P` (priced `R·A`) and `(∇P)³` — at most one factor per
product priced by `A`.  `C0` is the order-ZERO coefficient of the same operator
and necessarily carries the `Γ⋆Γ` half of `Ric = ∂Γ + Γ⋆Γ`; the DeTurck trick
removes second-derivative gauge terms, not first-derivative-squared ones.  The
asymmetry between the two siblings is structural, and G4's "the five pair
constants are off the critical path if G2 lands by the affine route" is now
moot — **G2 cannot land by the affine route.**

**Design menu (user decision, not to be implemented unprompted).**
(a) **Quadratic envelope** `‖C0‖_{H²} ≤ B0(R) + B1(R)·A²`, adapting the consumer.
Nearly assemblable today: four of five arms have `R`-priced coefficient
producers of that shape; the single gap is a coefficient-level
`ricciGood_h2_tame` (only the polynomial `ricciGood_h2_rf` and the action-level
`ricciGood_act_tame` exist), obtainable from `ricciAA_act_tame`/`ricciDA_act_tame`
in the same `(D R·(A+A²))` shape.  Cost ≈ one arm + assembly.  Note
`lowA1_act_tame` (`…Action.lean:11893`) already ships `D R·(A+A²)` downstream, so
a consumer tolerating that shape tolerates (a).
(b) **Affine at the price of one more jet** (`A` bounding `H⁴`) — promotes the
lane to class four, explicitly forbidden by №195.
(c) **The refold route** of №195: restate `IsBgLiftAt`'s core fields against a
background-refolded bundle plus the arbitrary-background `refold_low_split`
analogue.

**Dispatch impact.**  BG-1 is closed as a negative result.  The remaining №195
items are unaffected and independent of this ruling: **G5** (split `IsBgLiftAt`
into `IsBgA1At` + `IsBgA2At`, zero external consumers, free) and **G3**
(class-uniform lower bound for the three coefficient radii, copying
`lowRealizeData`'s closed formula, `UnifRealizeRadius.lean:91`) are both still
executable tonight and neither touches the C0 arm.  `bgA1_aff` → `IsBgA1At` is
blocked on the (a)/(b)/(c) ruling.

**Verification.**  None run — no Lean file was touched.  The two `.md` edits are
notes only.

**Honest denominators.**  `ricci_flow_unif_existence` **0%**; `IsBgLiftAt` /
`IsBgA1At` producer **0%**; `c0_bg_aff` **not implementable as specified** (its
`bgA1_aff` chain toward `IsBgA1At`'s two affine bound fields is blocked pending
the ruling, so that chain is **0%** and the affine framing is retired);
dedicated uniform-existence machinery unchanged at ≈**80%** (the gate landed no
code — a refuted claim removes a false target without adding machinery); whole
HCG ≈**3%**.  Campaign delta still uncommitted (user-side).

---

## 197 (planner, 2026-08-07 overnight). RULING on the №196 menu: route (a)
## adopted — the quadratic shape is the diagonal lane's PROVEN contract; the
## affine fields were a transcription error in a zero-consumer structure

**The unsatisfiability is in the CONSUMER, verified.**  `IsBgLiftAt`'s
`a1Hi_bound`/`a1Lo_bound` (`LowRegBgLift.lean:119–122`) are GLOBAL:
`∀ x : tensorHs …, ‖F.a1Hi x‖ ≤ D.zero + D.slope·‖x‖` — no ball.  Against
№196's scaling witness (`‖∇²P⋆∇²P‖_{L²} ≍ R^{1/2}A^{3/2}` at fixed `R`),
no producer can discharge them for the actual maps.  This is the №108
pattern (statement false/unprovable as posed → statement surgery, a
finding, not a route error), and the structure has ZERO external
consumers (№195 scout, grep-verified), so the surgery is free.

**Ruling: adopt №196 menu option (a) — quadratic `zero + slope·(A + A²)`
bound fields — as a MIRROR of settled architecture, not a new design.**
Grounds: (i) option (b) (buy `H⁴`) is forbidden by №195's own class-3
rule; (ii) option (c) (refold restatement) is a heavier refactor whose
motivation collapses given (iii): the DIAGONAL lane's downstream already
consumes exactly the quadratic shape — `lowA1_act_tame` ships
`D R·(A+A²)` and the self-background lift machinery runs on it (№196).
The affine fields in `BgLiftData`/`IsBgLiftAt` transcribed the wrong
shape from the start.  The Bg lane's contract is therefore restated to
the diagonal lane's proven one; the executor must READ the diagonal
consumption chain (what consumes `lowA1_act_tame`'s bound and how the
horizon algebra uses it) and mirror THAT contract verbatim — not invent
a third shape.  Flagged prominently for morning review; if the user
prefers (c), the surgery is contained in the two Bg files and reversible
(still zero external consumers).

**BG-2 dispatched** (reports as 198): (i) G5 — split `IsBgLiftAt` into
`IsBgA1At` + `IsBgA2At` (conjunction wrapper kept); (ii) the a1 bound
fields restated in the mirrored quadratic contract (scalar layer
`BgLiftData` gains/renames the needed constants; horizon formulas
adjusted per the diagonal template); (iii) G3 — the class-uniform
closed-formula lower bound for the three coefficient radii
(`lowRealizeData` pattern, `UnifRealizeRadius.lean:91`).  Then BG-3 =
the (a)-route producer chain: `ricciGood_h2_tame` (the one named
coefficient gap) → quadratic `c0_bg_quad` → `bgA1_quad` → discharge
`IsBgA1At`'s bound fields.  A2 (G1) unchanged at its stop condition.

---

## 198. BG-2: G5 landed; BOTH ruled-on parts STOPPED at their own stop
## conditions — the diagonal contract is AFFINE, and G3's radii are not opaque
## but un-exposed, bottoming at ONE node whose uniform sibling already exists
## (2026-08-07)

**Lead with the failures.**  Two of the three parts hit stop conditions the
brick itself specified, and neither was improvised past.

**(i) Part 2 STOP — №197's premise is false; the a1 bound fields were NOT
restated.**  The brick required reading the diagonal consumption chain before
touching anything.  Doing so refutes №197's ground (iii) ("the DIAGONAL lane's
downstream already consumes exactly the quadratic shape"):

- The diagonal lift consumer is `lowreg_apply_two` (`LowRegApplyTwo.lean:256`);
  its first-order hypotheses are `hFHiBd`/`hFLoBd` (`:309–312`),
  `∀ x : tensorHs g 0 2 3, ‖FHi x‖ ≤ Z + L * ‖x‖` — the AFFINE shape, which is
  byte-for-byte what `IsBgLiftAt.a1Hi_bound`/`a1Lo_bound` already carried, with
  `Z ↦ D.zero`, `L ↦ D.slope`.  Not a transcription error: a verbatim mirror.
- The horizon algebra is built around exactly that affine split and cannot
  absorb a merged constant.  `lowregLiftHorizon' c Z`
  (`LowRegLiftSmall.lean:282`) absorbs ONLY the `√T`-carrying `Z`; the slope `L`
  is capped by the separate `T`-free margin `6·(2L‖f‖) ≤ (1−c)/2`
  (`lift_aff_margin`, `:354`; consumed as `hmargin`, `LowRegApplyTwo.lean:332`).
  `BgLiftData.horizon = lowregLiftHorizon' contract zero` (`UnifBgLift.lean:64`)
  and `force_margin` (`:58`) mirror these one for one.  Answering the brick's
  sub-question: `horizon` reads `zero` and not `slope`; `slope` is read only by
  `force_margin`; the four `commonHorizon_*` read `zero` only via `horizon`.
- The affine bound is PROVED in the diagonal — `refold_aff`
  (`LowRegBgA1Refold.lean:488`), the `gB = g` case of the already
  arbitrary-background `refold_aff_bg` (`:345`), assembled from `c0_pack`
  (`LowRegBgC0Time.lean:322`) + `c1_bg_pack` (`LowRegBgC1Time.lean:763`), all
  sorry-free.  Decisive: its core identity is against the REFOLDED bundle
  (`c0CoreData + oneCore`), not `lowBaseData`/`lowCoreDataBg`.
- `lowA1_act_tame` (`…Action.lean:11893`) is not counter-evidence.  It is
  private; its only consumer is `remainder_diag_h2` (`:13555`), consumed by
  `DeTurckRemainderLowBaseTime.lean:1767` and `PrincipalResidualH2.lean:186,228`
  — modules that never import `UnifBgLift`.  It also bounds the ACTION
  `a1[T](T)` (the same tensor in both slots), which the affine OPERATOR bound
  implies at `y = x`; it is strictly weaker, not a rival contract.

**Consequence for the ruling.**  №196's scaling witness does not refute the
bound SHAPE; it refutes affine growth *against the un-refolded core*.  The open
design choice is therefore in `IsBgA1At`'s CORE fields, not its bound fields,
and the honest "mirror the diagonal verbatim" move is menu option (c), not (a).
Option (c) is also far cheaper than №197 assumed: `refold_aff_bg` ALREADY exists
at arbitrary background and already discharges bound + core + square for the
refolded split.  What option (c) still needs is the Bg analogue of
`refold_low_split` (whose C2 fibre bound `κδ/(1−δ)²` is diagonal only) — i.e.
the same A2 gate G1 is blocked on.  **Planner revision required before BG-3**;
the BG-3 spec as written (`ricciGood_h2_tame` → `c0_bg_quad` → `bgA1_quad`)
builds the (a) route and is on hold.

**(ii) Part 3 STOP — but the finding is much better than "opaque".**  A
class-uniform lower bound as literally specified ("`ρ_class` sits under the
three per-`g` existential radii") is not a statable proposition: the three radii
are ∃-bound, validity is downward-closed, so the infimum of valid radii is `0`.
The statable G3 is `∃ ρ_class > 0, ∀ g in class, ∀ ρ ≤ ρ_class, P_g(ρ)` — the
shape `inv_coeff_h2_unif` already uses.  Full provenance trace (read-only):

- Every one of the three radii is `min`/verbatim arithmetic all the way down —
  **no** `Classical.choose`, **no** compactness, **no** unquantified cutoff
  anywhere in the radius algebra of `DeTurckRemainderLowBaseLip.lean`,
  `…C2Lip.lean`, `…H2Pair.lean`, `PrincipalCoeffH2.lean`.
- All three converge on ONE bottom node: `inv_coeff_h2`
  (`DeTurck/PrincipalCoeffH2.lean:202`), `let ρ : ℝ := min 1 (4 * Cop)⁻¹`
  (`:229`).  Chains: (A) `radialA1HiBg_pair.ρ₀ = a1Hi_bg_pair.ρ =
  min (c0_bg_pair_h2.ρ) (c1_bg_pair_h2.ρ)`; (B) `radialA1Bg_pair.ρ₀ =
  a1Lo_bg_pair.ρ = min (c0_bg_pair_h1.ρ) (c1_bg_pair_h2.ρ)`, whose
  `selfLow_pair_h1` (`…Lip.lean:9896`) is a five-way `min` (`:9942`); (C)
  `radialA2Bg_lip.ρ = min ρ₀ (a2_pair_lip.ρ)`, verbatim down through
  `c2_pair_lip` → `c2Diff_h2` → `kernel_h2_lip` (`…C2Lip.lean:4283`).  Every
  branch reaches `invCoeff_h2_lip` (`…C2Lip.lean:1147`) → `inv_coeff_h2`.
- The ONLY opaque ingredient is the scalar `Cop`
  (`PrincipalCoeffH2.lean:220`) ← `hs2_op_bound`
  (`Estimates/H2Pointwise.lean:323`) ← `hs2_fiber_sq` (`:166`) ←
  `exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical`
  (`Sobolev/Embedding/SobolevEmbeddingSharpC0JetSum.lean:717`, `choose` + `sup'`
  at `:748–749`) ← compactness at `:559`.  The radius depends on `g` only
  through `Cop`, and on `gB` not at all.
- **That node is already fixed.**  `inv_coeff_h2_unif`
  (`ShortTime/UnifInvCoeffH2.lean:60`) proves the same statement
  class-uniformly with the identical formula `min 1 (4 * Cop)⁻¹` (`:96`) but
  `Cop := hs2OpActionC (morreyTwoC gBase Λ) Kcurv.rankTwo` — `lowRealizeData`
  quality; its closed-form inputs are `hs2_op_bound_action` /
  `hs2_fiber_sq_action` (`Estimates/H2PointwiseUnif.lean:404` / `:251`).
- **The real gap is the uniform LIPSCHITZ/PAIR layer.**  The 54 existing
  `_unif` theorems in `ShortTime/` have reached the *bound* family
  (`trace_h2_unif`, `trace2_h2_unif`, `sharp_h2_unif`, `connLow_tame_unif`,
  `inv_coeff_h2_unif`) and not one `_pair_`/`_lip` node.  Roughly 55 nodes
  (`invCoeff_h2_lip` → `trace24_h2_lip`/`trace1_h2_lip` → the `*_pair_h1/h2/h3`
  families → `a1Hi_bg_pair`/`a1Lo_bg_pair`/`a2_pair_lip`) stand between here and
  G3.  Three of the host files are memory-walled monoliths, so the threading
  must be done as `_unif` siblings in `ShortTime/`, node by node, exactly as the
  existing corpus does.
- **Smallest next brick for G3**: `invCoeff_h2_lip_unif`, the class-uniform
  Lipschitz sibling of `invCoeff_h2_lip` (`…C2Lip.lean:1147`) built on
  `inv_coeff_h2_unif`, homed in a new `ShortTime/UnifInvCoeffLip.lean`.  All
  three chains pass through that one node, so it is the highest-leverage step.
  G3 is a lane, not a brick tail, and should be re-dispatched as one.

**(iii) Part 1 (G5) LANDED, green.**  `IsBgLiftAt` (`LowRegBgLift.lean`) is
split into `IsBgA2At` (7 A2 fields; takes no `BgLiftOps`, since no A2 field
mentions `F` — weakest-assumptions rule) and `IsBgA1At` (7 A1 fields), with
`IsBgLiftAt` kept as `: Prop extends IsBgA2At …, IsBgA1At …`.  All fourteen
field statements are byte-identical to before — the part-2 restatement was NOT
applied — and every field stays reachable through the parent projections.  The
`extends`-on-`Prop` idiom matches `Evolution/Metric/Basic.lean:314`.  Zero
external consumers re-verified including untracked files: only
`ScratchIdentCensus.lean:277`, which does `#print axioms IsBgLiftAt` and touches
no field.

**New public declarations** (census additions deferred, files claimed):
`IsBgA2At`, `IsBgA1At`; `IsBgLiftAt` retained, with new parent projections
`IsBgLiftAt.toIsBgA2At`, `IsBgLiftAt.toIsBgA1At`.

**Verification.**  `LowRegBgLift.lean` focused check GREEN (19.9 s), no
warnings; targeted module build GREEN (10045 jobs).  `ScratchIdentCensus.lean`
could not be checked: it fails on a PRE-EXISTING missing olean for the unrelated
module `LowRegForceHiBg`, not on anything this brick touched.  `UnifBgLift.lean`
was not edited (part 2 stopped), so nothing to re-check there.

**Honest denominators.**  `ricci_flow_unif_existence` **0%**; `IsBgA1At`
producer **0%** (this brick moved contract/wiring only, and the producer route
is now on hold pending the (a)-vs-(c) revision); `IsBgA2At` producer **0%** (G1
gate unchanged); G3 class-uniform radius **0%**, re-scoped from "one brick" to a
~55-node `_unif` lane whose entry node is named above; dedicated
uniform-existence machinery ≈**80%**, unchanged — G5 is a free structural split
that adds no mathematics, and the two stops added evidence rather than
machinery; whole HCG ≈**3%**.  Campaign delta still uncommitted (user-side).

---

## 199 (planner, 2026-08-07 overnight). Ruling 197 RETRACTED (near-miss #2,
## gated before landing); route (c)-verbatim ADOPTED: keep the affine
## contract, refold the core fields; the A1 and A2 frontiers CONVERGE

**Retraction.**  197's premise — "the diagonal contract is quadratic;
mirror it" — is refuted by 198's part-0 read: the diagonal consumer
`lowreg_apply_two` (`LowRegApplyTwo.lean:309–312`) takes the affine
`‖FHi x‖ ≤ Z + L·‖x‖` byte-for-byte, with the horizon algebra absorbing
`Z` (√T) and capping `L` by a `T`-free margin (`lift_aff_margin`,
`LowRegLiftSmall.lean:354`); `lowA1_act_tame`'s `D R·(A+A²)` is a
PRIVATE action bound (same tensor both slots), never the operator
contract, and its consumers never import `UnifBgLift`.  COUNTER
ADJUDICATION: near-miss #2, NOT scored (counter stays 1/3) — the ruling
carried its own part-0 STOP ("if the diagonal contract is not quadratic,
stop for planner revision"), the gate fired, and no wrong statement
landed (the landed-vs-gated line of №154/№157).

**Adopted ruling (route (c), the diagonal's verbatim mirror).**
- KEEP `IsBgA1At`'s affine bound fields — they were the RIGHT contract.
- The maps `BgLiftOps.a1Hi/a1Lo` are DATA: the producer supplies the
  REFOLDED completions, whose affine bound is already proved at
  arbitrary background by `refold_aff_bg` (`LowRegBgA1Refold.lean:345`,
  sorry-free; diagonal case `refold_aff` :488, from `c0_pack`
  `LowRegBgC0Time.lean:322` + `c1_bg_pack` `LowRegBgC1Time.lean:763`).
- RESTATE `IsBgA1At`'s two core fields against the refolded bundle
  (`c0CoreData + oneCoreBg`) instead of `lowCoreDataBg`; the `a1_square`
  field likewise moves to the refolded maps' square.  №196's scaling
  witness stands as the proof that the UN-refolded core admits no affine
  bound — the refold is forced, not stylistic.
- The PDE-level honesty condition is the TOTAL identity (the lift
  consumes `a1 + a2` together): the remaining genuine frontier is the
  Bg analogue of `refold_low_split` (`LowRegBgC0Core.lean:452`, diagonal
  today; its C2 arm fibrewise `κδ/(1−δ)²`).  **This is the SAME gate as
  G1/A2 — the A1 and A2 frontiers converge into ONE: the
  arbitrary-background refold split.**  (c) opens no second frontier.
- Status honesty: №194's `lowA1Bg_comm_bg`/`a1_comm` remain true, banked
  canonical API for the actual bundle; on the (c) route they move OFF
  the lift's critical path (the lift's square is the refolded one).

**BG-3 dispatched** (reports as 200): (i) inventory the refold lane's
Bg-side COMPLETIONS (do refolded completed `metricH3 →L` maps + square +
continuity exist at `g gB`, or only the smooth-core `refold_aff_bg`
level? — read `LowRegBgA1Refold/BgC0Time/BgC1Time` before writing
anything); (ii) restate the two core fields + square of `IsBgA1At`
against the refolded bundle; (iii) discharge all seven `IsBgA1At` fields
from the refold lane at arbitrary background (build the missing
completions if routine — mirror the diagonal's; STOP with the inventory
if they need new analysis).  The shared frontier (Bg `refold_low_split`)
is NOT part of BG-3 — it is the morning's single design item, now
carrying both A1 and A2.

---

## 200. BG-3: route (c) LANDED — `IsBgA1At` is PRODUCED sorry-free at arbitrary
## background; the planned completion-building was unnecessary because
## `refold_aff_bg` was already a completed-level result (2026-08-07)

No stop condition fired.  All three parts landed in ONE file, and the reason the
brick was cheaper than its own spec is a part-0 correction worth recording.

**(0) Inventory verdict — the spec's premise about `refold_aff_bg` was wrong in
our favour.**  The brick (and №198/№199 before it) described `refold_aff_bg`
(`LowRegBgA1Refold.lean:345`) as living "at the SMOOTH-CORE level", with the
Bg-side COMPLETIONS as the thing to build.  Reading the statement refutes that:
its `FHi`/`FLo` are already COMPLETED maps

    FHi : metricH3 g → (metricH3 g →L[ℝ] metricH2 g)
    FLo : metricH3 g → (metricH2 g →L[ℝ] metricH1 g)

— byte-for-byte the two `BgLiftOps` fields — and the theorem already exports, at
arbitrary `g gB`, all five remaining facts: `Continuous FHi`/`Continuous FLo`,
the smooth-core VALUE identities against `c0CoreData g + oneCoreBg g gB`, the
common affine bound `‖F x‖ ≤ Z + L‖x‖`, and the adjacent-scale inclusion square.
That is a 7-for-7 match with `IsBgA1At`.  **Nothing was missing at any
generality**, so PART 2 (mirror the `lowA1HiBg`/`lowA1LoBg` density extension)
was VACUOUS and no `cont_extend_pair`/`ccToHsLin_dense` argument was written.
Exhibit discipline honoured: the match was checked field by field against the
elaborated statement, not against a docstring.

Second part-0 finding: **`a1_square` needed no restatement.**  It is phrased on
the `BgLiftOps` data `F`, so supplying the refolded maps makes it the refolded
square automatically.  Only the two CORE fields actually moved.

**(1) LANDED — core fields restated.**  `IsBgA1At.a1Hi_core`/`a1Lo_core`
(`LowRegBgLift.lean`) now read against `c0CoreData g … + oneCoreBg g gB …`
instead of `lowCoreDataBg g gB …`, at the arguments
`D.coeffRadius_pos.le`, `hK.threshold_nonneg`, `hK.threshold_le_third`,
`D.realize hK` — the exact spelling `refold_aff_bg` produces.  The four bound
and continuity fields are untouched, as ruled.  The docstring records №196's
scaling witness as the reason the un-refolded core admits no affine bound (cited,
not re-derived) and notes that №194's `lowA1Bg_comm_bg`/`a1_comm` stay true and
banked but move off this lift's critical path.

**(2) VACUOUS** — see (0).  No new file was created; `LowRegBgA1Refold.lean` was
not edited and stays at its current size.

**(3) LANDED — the producer.**  `bgA1_of_refold` (`LowRegBgLift.lean`, name 12
letters):

    theorem bgA1_of_refold (hDim : Module.finrank ℝ E = 3)
        (g gB : SmoothRiemannianMetric I M) {K : LowRegBoundData}
        (hK : IsLowBoundsAt g gB K) :
        ∃ ρ0 : ℝ, 0 < ρ0 ∧
          ∀ D : BgLiftData K, D.coeffRadius ≤ ρ0 →
            ∃ Z L : ℝ, 0 ≤ Z ∧ 0 ≤ L ∧
              (Z ≤ D.zero → L ≤ D.slope →
                ∃ F : BgLiftOps g, IsBgA1At g gB K hK D F)

Proof is a direct specialization of `refold_aff_bg` at `ρ := D.coeffRadius`,
`δ := K.threshold`, `hreal := D.realize hK`; the bound fields follow by
`Z + L‖x‖ ≤ D.zero + D.slope‖x‖`, cores and square by `exact`.  **Sorry-free**
(axiom probe: `propext`, `Classical.choice`, `Quot.sound` only).

**The two domination hypotheses are a declared seam, not an assumption
wrapper.**  `refold_aff_bg` binds `Z`/`L` INSIDE its radius quantifier, so they
still depend on `g`, while `BgLiftData.zero`/`slope` are fixed before the class
metric varies.  The statement exposes that rather than hiding it; closing it is
the G3/`_unif` lane's job.  The shape mirrors the diagonal's `lowreg_solve_open`
(`LowRegApplyTwo.lean:645`), which likewise takes the packet before any
trajectory exists and caps its realization radius against `L`.

**Contract seams checked and CLEAN.**  `hDim : Module.finrank ℝ E = 3` is a
hypothesis of the producer, exactly as in the diagonal (`lowreg_apply_two`,
`lowreg_solve_open`, `refold_aff`) — not a new assumption.  Import addition
`LowRegBgA1Refold` into `LowRegBgLift.lean` introduces no cycle: that module's
transitive closure never reaches `UnifBgLift`/`LowRegBgLift`, whose only
importer is the leaf `ScratchIdentCensus.lean`.

**New public declarations** (census additions deferred): `bgA1_of_refold`.  The
seven `IsBgA1At` field statements changed in two places only (`a1Hi_core`,
`a1Lo_core`); `IsBgA2At`, `IsBgLiftAt`, `BgLiftOps`, `BgLiftData` unchanged.

**Verification.**  `LowRegBgLift.lean` focused check GREEN (19.5 s, no
warnings); targeted module build GREEN (10061 jobs) — run because the focused
`lake env lean` exit code alone is not trustworthy.  Downstream
`ScratchIdentCensus.lean` also GREEN (its №198 blocker, the missing
`LowRegForceHiBg` olean, has since been built).  Files touched:
`LowRegBgLift.lean`, `LowRegBgLift.md`, this ledger.  No other file edited; all
unrelated dirty files preserved.

**Honest denominators.**  `ricci_flow_unif_existence` **0%** — the endpoint
theorem is still unstated in Lean and no brick in this lane changes that.
`IsBgA1At` producer **100%** (`bgA1_of_refold`, sorry-free, arbitrary
background) — this is the first of the two lift halves to close.  Full
`IsBgLiftAt` producer still **0%**: it needs the A2 half `IsBgA2At` (G1 stop
condition, unchanged) AND the shared frontier below, and a conjunction with an
unproduced conjunct produces nothing.  G3 class-uniform radius **0%** (unchanged;
~55-node `_unif` lane, entry `invCoeff_h2_lip_unif`).  Dedicated
uniform-existence machinery ≈**80.5%** (+0.5pp: one of the fourteen lift fields
groups — seven of them — went from unproduced to produced, but the brick added
no new analysis, only wiring over machinery that already existed; a bigger
number would be dishonest since the mathematics was banked in `refold_aff_bg`
before tonight).  Whole HCG ≈**3%**.  Campaign delta still uncommitted
(user-side).

**Remaining frontier for the full lift** — exactly two items, as forecast:
1. **The Bg `refold_low_split` analogue** (`LowRegBgC0Core.lean:452` is
   diagonal — signature confirmed single-metric `g`, "same-background"; its C2
   arm is fibrewise `κδ/(1−δ)²`).  This is the PDE-level honesty condition: the
   lift consumes `a1 + a2` together, so refolding A1 alone is only sound once
   the arbitrary-background total-split identity exists.  **A1 and A2 now
   converge on this ONE gate** — it is simultaneously G1.
2. **The G3 radius lane** (class-uniform coefficient radius), independent of
   item 1.

---

## 201 (planner, 2026-08-07 overnight). BG-3 ACCEPTED: `IsBgA1At` producer
## 100%; night queue = refold-split feasibility scout ∥ G3 entry brick

**BG-3 accepted as reported** (entry 200): `refold_aff_bg` was already at
the completed-map level — 7-for-7 with `IsBgA1At` — so `bgA1_of_refold`
is a specialization, sorry-free, axiom-clean, module build green.  The
two DECLARED seams are ratified as the honest interface: (i) `Z`/`L` are
per-`g` (bound inside the radius quantifier) vs `BgLiftData.zero/slope`
class-fixed — the G3/`_unif` lane's job, exposed as domination
hypotheses, not hidden; (ii) the Bg `refold_low_split` gate.  Machinery
80 → **80.5%** accepted with №200's own justification.

**Re-examination of the converged gate's status as a "design item".**
№199 reserved it for the morning because it carried the A2 class-4
choice.  But the refold route's C2 arm is FIBREWISE (`κδ/(1−δ)²`,
`LowRegBgC0Core.lean:483` diagonal) — it does NOT route through the `H⁴`
completion comparison that G1's stop condition guards.  If the diagonal
`refold_low_split` (`LowRegBgC0Core.lean:452`) generalizes to `g gB` by
the SAME mechanism (path integrals with background-corrected arms — the
Bg C0 lane already built `bgCorr_h2`/`fixedBg_h2`), then no design
choice remains and the lift closes at class 3.  Whether it is routine or
needs new analysis is a READ-ONLY question — dispatched as a feasibility
scout (no implementation without its verdict; if new analysis, the
morning dossier gets the precise obstruction instead of a guess).

**Night queue** (scout is read-only, executor holds the one Lean
process): (α) scout — Bg `refold_low_split` feasibility dossier;
(β) executor — G3 entry brick `invCoeff_h2_lip_unif` (the №198-named
highest-leverage node, common bottom of all three radius chains; new
light `ShortTime/UnifInvCoeffLip.lean`, mirroring `inv_coeff_h2_unif`'s
uniformization pattern `UnifInvCoeffH2.lean:60`; №194 rule — re-derive
from public producers, never re-elaborate a monolith).  Reports as 202
(β) and the scout folds into the next planner entry.

---

## 202. G3 entry brick: `invCoeff_h2_lip_unif` LANDED sorry-free — the lane's
## first `_lip` node is class-uniform, and the ONE input with no sibling was the
## identity rank-two coefficient, closed in dimension-constant form (2026-08-07)

No stop condition fired.  One part-0 correction and one genuinely new ingredient
are worth recording.

**(0) Part-0 correction — the brick's premise about "a dropped clause" is
wrong.**  The spec asked which Lipschitz/pair clause of the metricwise bottom
node `inv_coeff_h2` was dropped by `inv_coeff_h2_unif`.  Reading both statements
refutes the framing: `inv_coeff_h2` (`DeTurck/PrincipalCoeffH2.lean:202`) has
exactly TWO clauses — a pointwise order-zero bound and an `L²` jet bound through
order two — and `inv_coeff_h2_unif` (`UnifInvCoeffH2.lean:60`) uniformizes BOTH,
verbatim, with the same `ρ = min 1 (4·Cop)⁻¹`.  Nothing was dropped.  The
Lipschitz layer is a **separate, strictly larger two-endpoint theorem**,
`invCoeff_h2_lip` (`…C2Lip.lean:1147`, PUBLIC), whose statement has no
counterpart inside `inv_coeff_h2` at all.  №198's radius trace is unaffected —
`invCoeff_h2_lip` still calls `inv_coeff_h2` for its radius, so all three chains
still bottom out where №198 said.  What changes is the size of the entry brick:
it is a whole theorem, not a clause.

**(1) LANDED — `invCoeff_h2_lip_unif`** (new `ShortTime/UnifInvCoeffLip.lean`,
564 lines, name 19 letters).  Class-uniform under EXACTLY the ruled pair
(`MetricUniformEquivalentOn univ gBase g Λ` + `∀ a ≤ 3,
MetricCovDerivOrderBoundOn univ a g gBase Λ`; no fourth jet).  Statement shape is
the `∃ ρ C, 0 < ρ ∧ 0 ≤ C ∧ ∀ g in class, …` form №198 identified as the
statable G3, matching `inv_coeff_h2_unif` byte for byte in its quantifier
prefix.  **Sorry-free** (axiom probe: `propext`, `Classical.choice`,
`Quot.sound`).

**The metricwise → class-first translation table** (the reusable output of this
brick; four of five rows were pre-existing siblings nobody had connected):

| metricwise input | class-first sibling |
| --- | --- |
| `inv_coeff_h2 hDim g` | `inv_coeff_h2_unif` `UnifInvCoeffH2.lean:60` |
| `appRS_h2_h2_h2 hDim g 2 2 2` | `appRS_h22_unif` `UnifAppH22.lean:70` |
| `jet3_fiber_c2 hDim g 2 2` (private) | **`morreyRS_unif`** `HCGCompactness/UnifMorreyRS.lean` |
| `hs2_low2 g 2` | `covsum_hs_two` at `IsCurvAction0 g 2 Kcurv.rankTwo` |
| `J0 = c2JetSq g (fullSlot2 g g)` | **none existed** — supplied here |

`morreyRS_unif` is the find worth propagating: it is the class-uniform
MIXED-VALENCE Morrey estimate, i.e. exactly the `_unif` sibling of the private
`jet3_fiber_c2`, generic in `(r,s)`, and it was already sorry-free in the
HCGCompactness tree.  Every later `_lip` node that needs a pointwise-from-jets
step should use it instead of re-deriving one.

**(2) The one genuinely new ingredient: the identity rank-two coefficient.**
`fullSlot2 g g = slotInsertEndoCc g 1 (fullRaisedEndoField g g)` is the identity
`(2,2)` coefficient of `g`, and its `H²` window is the only quantity in the
metricwise proof that is metric-dependent with no closed class bound.  It is
closed here as `idSlotJet`:

    ∑_{j<3} ‖∇^j (slotInsertEndoCc g 1 (fullRaisedEndoField g g))‖² ≤ 27 · vol(g)

using only PUBLIC producers: the field is parallel, so
`iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero`
(`CovGrad/CurvatureCoefficientDifferenceJetTower/Lowered.lean:445`) kills orders
1 and 2 after the slot transfer, and its pointwise fibre norm is a pure
dimension constant by `rfns_idEndo_le`
(`CovGrad/RecoveryEndomorphismJetBound.lean:454`) through
`sharpFlatEndoCc_eq_slotInsert_fullRaised` (`Lowered.lean:313`).  The class step
is `volumeReal_cross`, giving `27 · volCompareC Λ · vol(gBase)`.
**Explicitly rejected route**: `exists_bound_riemannianFiberNormSq_smoothCcTensor`
(the private `bdSharpFlat_tgrid` path in `RiemannCoefficientPalatiniRefold.lean`)
produces a non-explicit metric-dependent constant and CANNOT be uniformized —
that is why the identity term had no sibling before tonight.

**Closed constant.**  With `Kcurv` from `exists_curv_actions gBase hΛ`,
`Ch = h2CovsumC Kcurv.rankTwo`, `vol = volCompareC Λ · vol_{gBase}(M)`:
`Cp = 3·Ch`, `Z = 2·((Cinv·ρ)² + 27·vol)`, `A = √Z`, `C0 = Cmul²·Cp·A²`,
`C = (Cpt+1)·C0`; `ρ` inherited verbatim from `inv_coeff_h2_unif`.

**№194 discipline honoured.**  Four private helpers of the memory-walled
`…C2Lip` monolith (`perm_icg_norm_c2`, `symm_icg_norm_c2`, `insert1_icg_le`,
`perturbSlot2_icg_le`) were RE-DERIVED in the light file from their public
producers — `riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection`,
`iteratedCovGrad_symmS_eq`, `rfns_iteratedCovGrad_slotInsertEndoCc_le_endo`
(`MetricArmCoeffJetTower.lean:2795`), `insert_symmRaise_eq`,
`norm_iCG_cometricRaiseSlot0Field_eq` — not exported from the monolith, which was
never re-elaborated (only its olean is read, for the already-PUBLIC
`invSlot_sub_factor` `…C2Lip.lean:745`).  The `permICG` re-derivation is stated
generically in the rank, unlike the rank-2-only private original.

**New public declarations** (census additions deferred): `invCoeff_h2_lip_unif`.
Everything else in the new file is `private`.

**Verification.**  Focused check GREEN (24 s, no warnings); targeted module build
GREEN (9928 jobs); axiom probe run through a temporary scratch module (since
`lake env lean` suppresses `#print axioms`), which was deleted afterwards.  Files
touched: `UnifInvCoeffLip.lean` (new), `UnifInvCoeffLip.md` (new), this ledger.
All unrelated dirty files preserved.

**Honest denominators.**  `ricci_flow_unif_existence` **0%** — still unstated in
Lean.  `IsBgA1At` producer **100%**; full `IsBgLiftAt` producer **0%** (needs the
A2 half plus the shared Bg `refold_low_split` gate; unchanged by this brick).
G3 class-uniform radius: the ~55-node `_lip`/`_pair` lane now has **1 node
done ≈ 2%**; that is the honest number — the entry node is the highest-leverage
one (all three radius chains pass through it) but it is one node, and the four
sibling-lookups it consumed do not transfer automatically to the nodes above.
Dedicated uniform-existence machinery ≈**80.5%**, UNCHANGED: this brick adds a
class-uniform theorem the lane needs, but it consumed pre-existing `_unif`
producers and one small new dimension-constant lemma, so it is threading rather
than new analysis; a bump would be dishonest against a 55-node denominator.
Whole HCG ≈**3%**.

**Next node up the lane.**  `trace24_h2_lip` (private, `…C2Lip.lean:1358`), the
first consumer of `invCoeff_h2_lip`.  Its inputs are now three-quarters covered:
`invCoeff_h2_lip_unif` (this brick), and `appRS_h22_unif` at `(4,4,2)` and
`(6,6,4)` (it is generic in the valence).  The single remaining gap is the jet
window `c2JetSq g (cometricDoubleTraceField g p)` for `p = 2, 4` — and it is the
SAME SHAPE as the identity term closed here: the field is parallel by the public
`cometricDoubleTraceField_covGrad_eq_zero`, so all that is missing is a
class-uniform POINTWISE FIBRE bound for `cometricDoubleTraceField g p`, the
analogue of `rfns_idEndo_le`.  That one lemma is the next brick, and it is
plausibly reusable for several nodes above (the `*_pair_h1/h2/h3` families all
carry fixed cometric fields).

---

## 203 (planner, 2026-08-07 overnight). (β) G3 entry ACCEPTED; (α) scout
## verdict: ROUTINE + the ΔC0 finding ⟹ ROUTE ERROR #2 SCORED (counter
## 2/3); exhibit 19; repair bricks B1/B2 adopted; B1 dispatched

**(β) accepted** (entry 202): `invCoeff_h2_lip_unif` sorry-free with a
CLOSED class formula; part-0 honestly corrected the dispatch premise
(the Lipschitz layer is the separate public `invCoeff_h2_lip`
(`…C2Lip.lean:1147`), not a dropped clause — №198's trace survives);
`morreyRS_unif` (`HCGCompactness/UnifMorreyRS.lean`) identified as the
reusable pointwise-from-jets producer for every later `_lip` node; №194
honoured (four private monolith helpers re-derived from public
producers).  G3 lane 1/~55 ≈ 2%; next node `trace24_h2_lip` with ONE
missing lemma (class-uniform fibre bound for `cometricDoubleTraceField
g p`, `rfns_idEndo_le`-analogue, plausibly reusable across the
`*_pair_*` families).

**(α) scout verdict on the converged gate: ROUTINE — and a correctness
finding.**  (1) `refold_low_split` has ZERO consumers — **over-count
exhibit 19** (the planner's scout target was mislocated; the
load-bearing object is the ρ-core-level Bg refold identity).  (2) The
C2 arm is NOT a gap: `lowData_split g gB` is already two-metric, the
fibrewise `κδ/(1−δ)²` cap transfers verbatim, NO H⁴ comparison — the
A2/G1 class-4 stop condition genuinely does not fire on this route.
(3) **A2 needs NO refold at all**: `IsBgA2At` is phrased on
`lowCoreDataBg` directly; its blocker is the contraction bound whose
diagonal smallness chain (`lowA2_small`/`a2Hi_total_le`) is pure
density; the remaining Bg question is a `c2_h2_small` sibling — a
MORNING item (the standing A2 stop condition is NOT overturned on a
scout aside).  (4) **THE ΔC0 FINDING**: the true Bg refold bundle is
NOT `c0CoreData + oneCoreBg` — at `gB ≠ g` it misses `appCc ΔC0 S`,
`ΔC0 = (lowBaseData g gB S).C0 − (lowBaseData g g S).C0 =
bgCorrInt g gB S + (phiMetCurvCoeff g gB g − phiMetCurvCoeff g g g)`
(`lowC0_bg_eq`, `LowRegBgH2.lean:893`; vanishes at `gB = g` by
`sub_self`, which is why the diagonal never saw it).

**COUNTER ADJUDICATION: ROUTE ERROR #2, counter 2/3.**  199 ruled the
core fields onto that bundle and 200 LANDED them — a consumer-unusable
statement in the tree (the №155 line).  Mitigations recorded, not
unscoring: 199/200 explicitly declared the PDE-identity gate open, and
`IsBgA1At` has no consumer yet, so nothing built on the wrong fields.
Honest denominators corrected: the refold-route A1 is ≈**70%**, not
100% — `bgA1_of_refold` is true-as-stated but its core fields await the
B2 repair; machinery gives back the +0.5pp → ≈**80%**.

**Repair bricks adopted** (scout's spec): **B1** (dispatched now,
reports as 204) — `refoldCoreBg` (`C0 := c0CoreData.C0 + ΔC0`,
`C1 := c0CoreData.C1 + lowCoreDataBg.C1`, `C2 := lowCoreDataBg.C2`) +
`refold_split_bg` at the ρ-core level, ~200 lines in
`LowRegBgA1Refold.lean`, mirroring :185–310 with the ΔC0 term threaded;
inputs all public (`lowCoreBg_split` `LowRegBgTime.lean:75`,
`c0Core_self` `LowRegBgC0Core.lean:61`, `appCc_add_left`,
`sub_add_cancel`); keep `refoldCore g = refoldCoreBg g g` diagonal
compatibility.  **B2** (next) — the ΔC0 affine packet `c0bg_pack` +
RE-restate `IsBgA1At`'s core fields against `refoldCoreBg` + the third
summand in `refold_aff_bg` + re-prove `bgA1_of_refold` (repairs the
route error; 1–2 sessions; inputs exist at Bg: `lowC0_bg_h2:997`,
`c0_bg_pair_h2:759`, `bg0_pair_h2:462`, completion mirror of
`c0_pack`).  B3 (δ-flexible Bg C1) NOT needed by B1/B2 — parked.
NOTE: PLAN6 approaches the 3000-line cap — roll to PLAN7 before ~2 more
entries.

---

## 204. B1: the corrected Bg refold bundle LANDED sorry-free — `refoldCoreBg`
## + `refold_split_bg`; the ΔC0 formula is PRIVATE, so B1 carries the passenger
## as a bare `C0`-difference and B2 inherits the un-privatizing (2026-08-07)

**Part-0 audit of the №203 spec: 4 confirmed verbatim, 1 confirmed-but-
unusable.**  (i) `lowCoreBg_split` (`LowRegBgTime.lean:75`) — exact, two-metric,
`S = lowRadial g ρ T`, `A = lowCoreDataBg g gB`.  (ii) the diagonal refold layer
`LowRegBgA1Refold.lean:84–310` — `refoldCore`/`refold_zero`/`refold_first`/
`refold_second`/`refold_action`/`refold_split` all as described; `refoldCore` is
a DIRECT `where`-structure, not a bundle-sum, so B1 mirrors the `where` idiom
and no `oneCoreBgΔ` intermediate was introduced.  (iii) `c0Core_self`
(`LowRegBgC0Core.lean:61`) — exact.  (v) `oneCoreBg` has `C0 := 0`,
`c0CoreData` is background-free — exact.  (iv) **`lowC0_bg_eq`
(`LowRegBgH2.lean:893`) is `private`, and so is its `bgCorrInt` summand
(`:816`)** — the formula is as №203 states it, but NEITHER name is usable
outside `LowRegBgH2`.  Per the dispatch's contingency, B1 phrases ΔC0 as the
bare difference `(lowCoreDataBg g gB).C0 - (lowCoreDataBg g g).C0`.  No
mismatch that required a planner ruling; the private-ness is a B2 cost, not a
B1 one.

**True C1 diagonal relation (READ, not assumed):** `oneCore g := oneCoreBg g g`
and `oneCoreBg g gB |>.C1 := (lowCoreDataBg g gB).C1`, both by `def`, so
`oneCore.C1 = (lowCoreDataBg g g).C1` by `rfl` and `refoldCore.C1` is literally
`c0CoreData.C1 + (lowCoreDataBg g g).C1`.  The scout's field spelling for
`refoldCoreBg` is therefore the correct widening — B2's spec needs no revision.

**Landed** (`LowRegBgA1Refold.lean`, 533 → 739 lines): public
`refoldCoreBg g gB` (`C0 := c0CoreData.C0 + ΔC0`,
`C1 := c0CoreData.C1 + lowCoreDataBg[gB].C1`, `C2 := lowCoreDataBg[gB].C2`),
public `refoldCoreBg_diag` (`refoldCoreBg g g = refoldCore g`; `C1`/`C2` are
`rfl`, only `C0` needs `sub_self, add_zero`), public **`refold_split_bg`**:

> for `S := lowRadial g ρ T`, `F := refoldCoreBg g gB hρ hδ0 hδ_le hreal T`,
> `deTurckSmoothRemainder g gB S _ _ - deTurckSmoothRemainder g gB 0 _ _
>  = F.a2 S + F.a1 S`

plus private `refoldBg_c0/c1/c2` (`rfl`) and `refoldBg_first/second/action`.
Route: `lowCoreBg_split g gB` then, on the `a1` arm, the single bridge
`appCc A.C0 S = appCc (A.C0 - D.C0) S + appCc D.C0 S` by
`rw [← appCc_add_left, sub_add_cancel]` (`D = lowCoreDataBg g g`), which hands
the diagonal self-action to the pre-existing `refold_zero`; two `appCc_add_left`
and `abel` close it.  `appCc_sub_left` proved unnecessary.  **No existing
declaration was edited** — `refoldLo_core`'s `:177` `simp only` did NOT need the
`sub_self` rewrite, because it is stated against the untouched `refoldCore`.

**Verification:** focused check green; targeted build
`+…ShortTime.LowRegBgA1Refold` green (`Build completed successfully`); no
`sorry`, no new `set_option`, no linter warning from this file.  Axiom probe:
`refold_split_bg` and `refoldCoreBg_diag` each
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

**Denominators (honest).**  `ricci_flow_unif_existence`: **0%** (unstated).
Refold-route A1: ≈70% → **≈77%** — B1 is the identity half and it also pins
B2's field spelling with a proved theorem, but the expensive half (the ΔC0
affine packet: continuity, affine growth, Sobolev square) is untouched.
Machinery ≈**80%** (no move: B1 is a narrow same-file identity, not a reusable
cross-file producer).  HCG compactness ≈**3%**.

**B2 spec, with the corrections B1's reading forces.**  (a) The `C0` privacy is
now B2's first obligation: `lowC0_bg_eq` and `bgCorrInt` must be made non-
`private` in `LowRegBgH2.lean` (or the ΔC0 bound routed through the already-
public H² siblings named in №203 — `lowC0_bg_h2:997`, `c0_bg_pair_h2:759`,
`bg0_pair_h2:462`), otherwise the affine certificate for ΔC0 cannot be stated.
(b) Build `c0bg_pack` as the completion mirror of `c0_pack` for the ΔC0
passenger.  (c) In `refold_aff_bg` (`:345`) replace the two core clauses
`c0CoreData.a1Hi/a1Lo + oneCoreBg.a1Hi/a1Lo` by the `refoldCoreBg` action, add
the third summand, and keep `refold_aff` as the `g g` diagonal — note
`refoldCoreBg_diag` now makes that diagonal a rewrite, not a `rfl`.  (d)
Re-restate `IsBgA1At`'s core fields against `refoldCoreBg` and re-prove
`bgA1_of_refold` on top of `refold_split_bg`.  B3 stays parked.
NOTE: PLAN6 is at ~2400 lines — roll to PLAN7 with the next entry.

---

## 205. B2 STOPPED at its part-(a) stop condition: `c0bg_pack`'s AFFINE half has
## no producer — the ΔC0 envelope in the tree is opaque-polynomial, not tame.
## Landed the one piece every design needs: `a1Hi_add`/`a1Lo_add` (2026-08-07)

**THE STOP (part-(a) verification mismatch, exactly as the dispatch named
it).**  `c0bg_pack` must deliver `‖F x‖ ≤ Z + L‖x‖` (the affine shape is not
negotiable — it is the №196 shape that `BgLiftData.zero/slope` and
`IsBgA1At.a1Hi_bound` are built from).  The three siblings №203 named deliver
only the LIPSCHITZ half:

- `c0_bg_pair_h2` (`LowRegBgA1Pair.lean:759`) — **usable, and better than
  advertised**: fully public AND already phrased on the bare difference
  `(lowBaseData g gB T).C0 - (lowBaseData g gB U).C0`, so applying it at `gB`
  and at `g` bounds `ΔC0(T) - ΔC0(U)`.  That is `exists_extend_le`'s `hpair`.
- `bg0_pair_h2` (`:462`) — **unusable outside its file**: its conclusion names
  the `private` `bg0PairInt`.  Same defect as `bgCorr_h2` (`LowRegBgH2.lean:950`,
  names the `private` `bgCorrInt`).  Public keyword, private statement.
- `lowC0_bg_h2` (`:997`) — usable but WRONG SHAPE for the affine half: its
  envelope is an opaque `B : ℝ → ℝ` with only `0 ≤ B A` exposed (internally
  `≈ 2√K(1+A²)³`, degree six).  An ∃-bound over an opaque `B` yields no
  affine information to any consumer, so `Z + L‖x‖` cannot be extracted —
  and setting `U = 0` in `c0_bg_pair_h2` gives an `A³` bound, not affine.

So the affine certificate for the ΔC0 passenger is a MISSING PRODUCER, not a
proof-search problem.  Classification: missing groundwork/API (analytic).

**The constructive route (scouted, not built).**  The needed statement is one
new PUBLIC theorem in `LowRegBgH2.lean`, stated on the bare difference so the
`private`s stay private (part (a) answered: **keep them private** — the
smaller honest surface; un-privatizing `bgCorrInt` would make a path-integral
internal permanent public API and still would not fix the shape):

> `c0Bg_diff_tame`: ∃ `B0 B1 : ℝ → ℝ` ≥ 0, ∀ T with
> `∑_{j<3}‖∇^j T‖² ≤ R²` and `‖∇³T‖ ≤ A`,
> `lowJetSq g 2 ((lowBaseData g gB T …).C0 - (lowBaseData g g T …).C0) ≤ (B0 R + B1 R * A)²`.

**The layer is MECHANICAL, not new mathematics — checked arm by arm.**  This
matters because the BG-1 gate (№195, `LowRegBgH2.md`) ruled the FULL `.C0`
non-affine; that ruling does NOT transfer to the DIFFERENCE, because the three
quadratic arms it turns on — `ricciGoodLow g gm`, `lc0VB g gm`, `lc0Riem g gm`
— take **no background argument** (`selfBase_decomp`), so they cancel exactly
in `bgCorrFam`.  What survives (`bgCorr_eq`) is DLa + DLb + Insert + AMix, and
each is already affine-shaped internally:

- DLa/DLb: `h2_grid_tame` (`LowRegCoeffJets.lean:887`) takes the *identical*
  pointwise grid hypothesis as `h2_of_grid`, so `dlaDiff_h2`/`dlbDiff_h2` get
  tame siblings by swapping ONE call (`dlaBg_grid`/`dlbDiff_grid` are public,
  `RiemannCoefficientPalatiniRefold.lean:6652/:3091`).
- Insert: `insert_h2`'s chain is `CA·BC(A)·CO·Bt(A)·AF` with `AF` a CONSTANT
  (the state-free `Fix = connDiffLoweredCc g gB - … g g`, via
  `wOmega_sub_refold`) and `Bt` from `trace_h2`, which consumes only the `H²`
  jet.  Only `BC` (`connLow_h2`) is `H³`-priced, and `connLow_tame` (`:1251`)
  is its tame sibling.
- AMix: `amixForm_h2`'s envelope is literally
  `4·Co·Bt2(A)·Cm·Bt4(A)·Cn·sf₃·BK(A)·Cq·Bt3(A)·sf₂·(4A)` — every `Bt*` is
  `trace_h2` (H²-jet only) and `kappaBg_h2` likewise drops to the range-3 sum
  on its first line, so the envelope is ALREADY `const(R)·A`, i.e. linear.
  Tameness is a restatement, not a new estimate — `amixForm_tame` (`:2338`)
  is the same chain already written out at `range 2`.

Then `bgCorrFam_tame` (the `P = s•T` scaling now splits into an `R` part and an
`A` part), `bgCorrInt_tame` via `path_jetL2_le`, and `fixedBg_h2` as the
constant.  Estimated ~400 lines in `LowRegBgH2.lean` (1270 → ~1670, under the
cap).  Honest size: a SESSION of its own, and `c0bg_pack` is another — its
Lipschitz half still needs the `c0CorePair` radial-cutoff plumbing (`lowRadial`
is nonlinear; `c0CorePair` pays for it with its `L = 1 + r/ρ` factor).
**B2 is a 3-session brick, not 1–2.**

**Landed instead (sorry-free): the bridge every design needs.**
`DeTurckRemainderLowBaseA1Comm.lean` (152 → 271 lines; already imported by
`LowRegBgTime.lean`, so zero import churn) gains, all bundle-generic:
`a1Hi_app`/`a1Lo_app` (each completion realizes `A.a1` on the dense smooth
range, for ANY `A`) and **`a1Hi_add`/`a1Lo_add`** (`F.C0 = A.C0 + B.C0`,
`F.C1 = A.C1 + B.C1` ⟹ `F.a1Hi = A.a1Hi + B.a1Hi`), plus a private `a1_jetQ`
factored out of `a1_comm` (which now reuses it, net simpler).  Why this is on
the critical path under EVERY ruling: an affine packet is assembled summand by
summand and produces a SUM of `a1Hi`s, whereas `refoldCoreBg` is ONE bundle
whose `C0`/`C1` are those sums; since `a1Hi` is a `LinearMap.extendOfNorm`,
that identification is not definitional.  (c) needs it twice and the
`refold_aff` diagonal needs it once.  Verification: focused check GREEN,
targeted build GREEN, axiom probe on `a1Hi_app`/`a1Hi_add`/`a1Lo_add` = the
three standard axioms.  Nothing else was edited; `refold_aff_bg`,
`IsBgA1At`, `bgA1_of_refold` are UNTOUCHED.

**Planner decision requested.**  Either (i) dispatch the tame ΔC0 layer as its
own brick B2a (route above), then B2b = `c0bg_pack`, then B2c = (c)+(d); or
(ii) let `bgA1_of_refold` carry the affine ΔC0 estimate as an explicit honest
input so that `IsBgA1At`'s FIELDS can be corrected to `refoldCoreBg` now —
this repairs the consumer-unusable statement (the actual content of route
error #2) at the cost of a conditional producer.  Not taken unilaterally:
unrequested scope widening is what scored errors #1 and #2.

**Denominators (honest).**  `ricci_flow_unif_existence`: **0%** (unstated).
Refold-route A1: **≈77%** (unchanged — B2 landed no part of the four; the new
additivity API is enabling, not progress on the packet).  `IsBgA1At` producer
on the CORRECT fields: **0%** — `bgA1_of_refold` is still stated against
`c0CoreData + oneCoreBg`, i.e. route error #2 is NOT yet repaired.  Full
`IsBgLiftAt`: **0%** (A2 half open).  Machinery **≈80%** (+0 — `a1Hi_add` is
small and generic but the ΔC0 analytic layer it was meant to serve is now a
known-missing ~400-line producer, which is a net-honest wash).  HCG
compactness **≈3%**.
NOTE: PLAN6 is at ~2500 lines — roll to PLAN7 with the NEXT entry.

---

---

# THIS LEDGER IS CLOSED (entries 167-205).

Rolled 2026-08-07 near the 3000-line cap.  **The active ledger is
`UNIF_EXISTENCE_PLAN7.md`** (entry 206+; its header carries the
state-at-rollover, the open-item ranking, and the standing rules).
Do not append here.
