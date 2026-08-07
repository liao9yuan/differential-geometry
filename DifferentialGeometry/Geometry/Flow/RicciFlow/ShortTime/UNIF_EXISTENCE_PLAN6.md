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
