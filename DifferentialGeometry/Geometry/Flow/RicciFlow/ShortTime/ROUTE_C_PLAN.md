# ROUTE_C_PLAN.md — route (c): direct smoothing for `bg_packet_of_solve`

Created 2026-08-07 by the planner from the (c-A) scope-scout dossier.
Authority: user ruling `UNIF_EXISTENCE_PLAN7.md` №227 (route (c) adopted;
№220/№222 packet + lift ports superseded).  Ledger context: №225 ((c)
feasibility), №226 (gate-constant probe), №227 (ruling), №228 (this plan).
This file is the lane's running source of truth: update the brick STATUS
column and the status log as bricks land; do not restart settled bricks.

## Goal

Discharge the ONE sorry on (N)'s axiom chain:
`bg_packet_of_solve` (`LowRegBgBootstrap.lean:215`, sorry :225):
given `hK : IsLowBoundsAt g g_bg K` and
`hsol : IsLowSolveBg g g_bg K hK hT hT1 u gforce` on `T ≤ 1`, produce
`Nonempty (BgSmoothPacket g g_bg K T)` — the order-two closed-slab packet
on the SAME horizon.

Route (amended by the Pro overall ruling, ledger №235 — C1 + reorder):
the frontier is RESTATED as `bg_packet_of_adapt`
(`ha : IsAdaptedLowBg g g_bg K hK hT hT1 u gforce` →
`Nonempty (BgSmoothPacket g g_bg K T)`), replacing
`bg_packet_of_solve` (unprovable as posed: the absorption inequality
is not derivable from arbitrary `IsLowBoundsAt K`; adaptation is
solve-PRE calibration, not a free post-certificate).  Phases, in
EXECUTION ORDER:
- **(c-C0)** fixed-metric feasibility gate: the DIAGONAL
  `bg_packet_of_adapt` prototype on the proved diagonal ladder —
  from `IsAdaptedLowSolve` alone (no `IsRealizedTwo`), build the
  packet fields (H² forcing rep, order-2 carrier, `mode_smooth`,
  `mode_mass`, `mode_eq`, bounds).  Zero widening; tests the
  route-specific risk FIRST.  Its consumption map DEFINES minimal
  (c-A).
- **(c-A)** minimal widening of the adapted-solve/rung/gate/mass
  chain `(g,g)` → `(g,g_bg)` (per-`g` statements only — NOT uniform);
- **(c-B)** the ABSORPTIVE gate only: split `IsLowGateOrd` into
  absorptive small coefficients vs metricwise high-rung bookkeeping;
  class-uniformize ONLY Ā/B̄/δ/state-cap and PROVE they read ≤3 jets
  of the varying `g` (STOP condition below); build
  `lowreg_adapt_unif` (class-first: uniform gate bounds + literal
  common `K` before `g`).
- **(c-C)** final assembly: `bgreg_allOrderJet` → `bg_packet_of_adapt`,
  and RETHREAD `lowreg_dt_unif`'s PROOF BODY (uniform solve →
  uniform adapted solve; its THEOREM STATEMENT and (N)'s statement
  stay unchanged — "untouched" claims in earlier entries were
  interface-level only).
The lift layer (`IsBgLiftAt`, `bgLift_of_radial`,
LowRegBgLift/A1Refold/C2Small/A2Time, G3 `_unif` nodes) stays in
place UNUSED until (c-C) lands (rollback point); do not delete or
edit it in this lane.

## Slot semantics (scout-verified ground truth)

Universal convention at every definition site: **slot 1 = state/spectral
metric** (Sobolev scale, eigenbasis, state ball, fibre bounds,
realization); **slot 2 = DeTurck background/coefficient metric**, entering
only through `deTurckRicciRHS g_bg` / `deTurckSmoothRemainder`.  Widening
= free slot 2; every space stays on `g₀`.  No definitional identity forces
the slots equal — the diagonal is pinned only in THEOREM statements.
Substrate already two-metric (class A, no work): `deTurckSmoothRemainder`,
`deTurckSmoothN`, `coreN`, `lowRegN`, `lowregNfun`, `coreN_tame`,
`lowRegSeedMass`, `nZero_eq_static`, `lowregGalSol`, `lowBaseData`,
`lowData_split`, `topKernel_eq`, `c0_eq/c1_eq/c2_eq`, `rhsRefoldTop(_joint)`,
`rhsLow1PathIntegral`, `moserWin_phiDev`, `phiMet_cap`, `lowregGateAbsorb`,
`IsAllRungPath`, `lowregMassOfEnergy`, and the whole
`LowRegBoundData`/`IsLowBoundsAt`/`IsLowSolveBg`/`lowreg_sol_of_data`
input layer.  Scout verdict: **zero verified class-C (genuine
diagonal-use) items; zero monolith edits needed** (all monolith producers
public and two-metric).

## Phase (c-A): the widening bricks (≈13–17 sessions)

One executor at a time (heavy DT checks import the 13.8k monolith).
| # | brick | files | class | est | STATUS |
|---|---|---|---|---|---|
| 1 | `IsBgSolveAt` bundle: fields = (`bounds : IsLowBoundsAt`, `solve : IsLowSolveBg`, `hTτ`, `hcap`); projection lemmas named/shaped like `IsLowSolveAt`'s fields (slot 2 freed) so rung mirrors port near-verbatim.  NOT a 17-field re-statement. | NEW `ST/LowRegBgSolveAt.lean` (231) | B | 0.5–1 | **DONE** (№231: green, warning-free, axiom-clean; 15 projections; zero statement-level deltas) |
| 2a | DT tower spine, in-place widen: `topKerJetSharp`, `c2JetTowerSharp/Q`, `c2_jet_tower` (proof edits = re-instantiations `moserWin_phiDev g g_bg`, `topKernel_eq g g_bg`, `rhsRefoldTop_joint g g_bg`, `lowData_split g g_bg`); fix 2–6 diagonal call sites per lemma (extra `g` argument). | `DT/LowRegC2JetTower.lean` (387), `DT/LowRegLadderRung.lean` (957, C2 part) | B | 1 | **DONE** (№233: green, axiom-clean, zero class-C; 3 diagonal call sites fixed: `topKer_jet` :370, `a2LadderQ` :371, `c2SupJet` A2PerIndex:206) |
| 2b-i | Window-layer C-point repairs (№232): free-bg A1 window, sharp AMix background difference, and combined Lie residual. | `Analysis/Sobolev/TensorHilbert/Low1KerRadiusFree.lean`, `…/TensorHilbert/TameLieCorrJets.lean`, `DT/LowRegC01JetTower.lean` | **C-repair** | 1–2 | **DONE** (№240: `bgCcAtgw`/`low1AtgwBg`, `mcdBgAtgw`/`amixBgAtgw`/`lc0AMixJetBg`, and `lieBgJet` green) |
| 2b-ii | Exact C0 split, sharp insertion difference, and arbitrary-background C0/C1 quadratic towers with diagonal wrappers. | `…/TensorHilbert/Lc0InsertDiffWindow.lean`, `DT/LowRegC01JetTower.lean` | **C-repair**+B | 1–2 | **DONE** (№240: `lc0InsDiffAtgw`, `insBgJet`, `selfLowJetQBg`, `c0JetTowerQBg`, `c1JetTowerQBg`; focused checks and targeted refreshes green) |
| 2c | A2 per-index: `c2SupJet`, `a2PerIdxJet/Lin`. | `DT/LowRegA2PerIndex.lean` (499) | B | 1 | **DONE** (№234: green, axiom-clean, zero class-C; consumers fixed diagonally: `armLadder3` RungThree:311, `armOrder3` RungFour:88, `armOrder4` RungFive:85) |
| 2d | A1 per-index: `a1Arm0/1`, `a1PerIdxJet/Lin` (engines cleared B by №232 probe). | `DT/LowRegA1PerIndex.lean` (1049) | B | 1–2 | **DONE** (№241: `a1PerIdxJetBg`/`a1PerIdxLinBg` focused-green, axiom-clean, targeted refresh green) |
| 2e | Ladder assembly: `a2/a1_ladder`, `a2/a1LadderQ`, `nDiffHmQ`, widen `IsHmRungOrd` (:935 `deTurckSmoothRemainder g g`) + `lowregHmPack`. | `DT/LowRegLadderRung.lean` | B | 1 | **DONE** (№241: six Bg declarations focused-green and axiom-clean; targeted refresh green) |
| 3 | Rung-3 Bg siblings: `galN_evalBg`, `galArmIdBg`, `armLadder3Bg`, `galArmVecBg` (№232: the diagonal `galArmVec` DEF bakes `lowBaseData g₀ g₀` in its body — bg-slotted analog def needed), `galArmMassOrdBg`, `galForceArmBg` (ForceArms:368 restatement); then `lowregRung3OrdBg`/`IsRung3OrdBg`/pack (Grönwall closure verbatim; `lowRegSeedMass g g_bg` is A). Diagonal `LowRegRungThree.lean` stays byte-stable. | NEW `ST/LowRegBgRung3*.lean` | B | 2–3 | **DONE**: all five rung-three declarations and `galArmVecBg` are focused-green; both direct modules refreshed; ordered `Kcap` is selected by `lowData_split g₀ g_bg` before `δ` |
| 4 | Rung-4/5 Bg: mechanical mirrors of brick-3 template. | NEW `ST/LowRegBgRungFour.lean`, `ST/LowRegBgRungFive.lean` | B | 2 | **DONE**: both five-declaration siblings are focused-green and targeted-refreshed; their `.olean`s are fresh and the diagonal files remain unchanged by the ports |
| 5 | Gate pack Bg: `IsLowGateOrdBg` + `lowregGatePackBg`. | NEW `ST/LowRegBgRungPack.lean` | B | 0.5 | **DONE**: metricwise Bg gate package focused-green and targeted-refreshed; reuses unchanged `rungGate_le`; makes no class-first uniformity claim |
| 6 | `IsAdaptedLowSolveBg` (= brick-1 bundle ∧ `IsRung3OrdBg` ∧ gateBg + absorption budget) + producer from a GIVEN solve.  **DESIGN FLAG** below. | NEW `ST/LowRegBgAdapt.lean` | B | 1 | **DONE (metricwise)**: package, projections, absorption lemma, and given-solve producer are focused-green/refreshed; the distinct class-first absorptive producer remains 0% |
| 7 | HigherRung Bg: `lowregRung5PathAtBg`, `lowregHighRungsBg` (+ `galArmMassHmBg` HigherRung:40), `lowregAllRungsAtBg`, `lowregAllMassAtBg` (reuse `IsAllRungPath`, `lowregMassOfEnergy` unchanged; №232 cleared the bodies B).  Also restate: `IsRung5Path` (RungClosure:42, pins `lowregNfun g₀ g₀` :65), `lowregFatouE3At` (FatouIdent:385), `lowreg_projMode_at` (GalerkinIdent:308). | NEW | B | 2 | **DONE (conditional/metricwise)**: Galerkin, Fatou/path closure, higher rungs, `lowregAllRungsAtBg`, `lowregAllMassAtBg`, and `lowreg_loMassBg` are focused-green and refreshed; this does not produce the adapted certificate class-first |
| 8 | Direct endpoint seam: `direct_jet_of_mass` consumes primitive two-metric solve data plus the exact `lowreg_loMassBg` output; `bg_packet_of_mass` packages it as `BgSmoothPacket`, and `bg_packet_of_adapt` supplies that mass from an adapted solve. | `ST/LowRegDirectJet.lean`, `ST/LowRegBgBootstrap.lean` | B | 1–2 | **DONE (metricwise)**: direct core, every-exponent background mass, and adapted-to-packet consumer are focused-green and refreshed; class-first adapted-solve production/rethreading remains outside this seam |

Consumption anchor (proved Brick 0): `direct_jet_of_mass` consumes primitive
two-metric solve data plus one `hspatial` hypothesis in exactly the shape of
`lowreg_loMassBg`.  `bg_packet_of_mass` supplies every `BgSmoothPacket` field
from that result, and `bg_packet_of_adapt` now closes this metricwise endpoint
chain.  The remaining lane is the class-first production of an adapted solve
and rethreading the uniform consumer through it; no completed A1/A2 lift maps
or high-scale realization certificate are endpoint inputs.

## Phase (c-B): the ABSORPTIVE gate only (re-scoped by №235; est. drops)

Pro's counterexample (`g_n = e^{2f_n} gBase`, `f_n = n⁻³ sin(n x₁)`)
proves constants reading ≥4th jets of the VARYING `g` cannot be
uniformized from the C³ class — and they need not be.  Steps:
1. **Gate split audit**: where does the Grönwall closure actually use
   the smallness `A·(δ/(1−δ)²) + B·stateRad + ε < 1`?  Separate the
   absorptive small coefficients from metricwise high-rung
   bookkeeping (rung-4/5 bridge factors inside B are the suspect
   bookkeeping).  Do NOT build a uniform-everything `IsLowGateBg`.
2. **≤3-jet audit of the absorptive slice**: after widening,
   coefficient fields sit at `gBase` (free); the varying-`g` readers
   left in Ā/B̄/δ/state-cap are the rung-3-level spectral bridges
   (`hs_le_jet` n=2, `galRepJet_*`) and the supercritical embedding —
   verify they read ≤3 jets of `g`.  **STOP CONDITION: if any
   absorptive coefficient needs ≥4th jets of `g`, halt — changing
   (N)'s `a ≤ 3` is a separate theorem-level USER ruling, never a
   silent implementation edit.**
3. Uniformize the absorptive slice only; keep metricwise: high-order
   Grönwall constants, per-σ `Cσ` (existentially selected after
   `g`, σ), high-order bridges, reconstruction majorants.
4. `lowreg_adapt_unif`: class-first producer choosing uniform gate
   bounds/threshold/state cap + a literal common `K` before `g`,
   emitting `IsAdaptedLowBg` per `g` (the C1 architecture).
Useful precedents: `UnifPhiDevH2`/`UnifPhiCurv`/`UnifRicci0`
(order-0 caps), `inv_coeff_h2_unif`, explicit `Cqa` dimension witness.

**STOP CONDITION FIRED (2026-08-07).**  The current metricwise gate is not an
absorption-only package.  Already at rung three its `Kr1` path contains
`Kb1 1 -> Kc 3 -> fixCdAtgw 3`, hence `nabla^3 (connDiff g gBase)`.  Since
`connDiff` already differentiates `g`, this reads the fourth metric jet of the
varying metric.  Rungs four and five read still higher towers.  These constants
are genuinely used in the common absorption budget, and shortening `T` does
not change that budget.  Therefore the C3 class cannot produce the current
`IsLowGateOrdBg` class-first.  Do not state `lowreg_adapt_unif` from this gate
and do not strengthen `(N)` silently.  The next design decision is a sharper
absorption-only decomposition that moves the fixed-offset/high-jet terms into
metricwise Gronwall coefficients, or an explicit user-approved change of
theorem hypotheses.

## Phase (c-C0) result + (c-C): synthesis and endpoint

(c-C0) — **DONE**.  The implemented feasibility gate is
`lowreg_directJet` in the new `ST/LowRegDirectJet.lean`.  It starts
from the existing diagonal `IsAdaptedLowSolve` and directly produces
the complete order-two forcing/carrier data needed by the smoothing
endpoint.  The actual checked chain is:

1. `lowreg_loMass` feeds a direct order-one forcing driver based on
   `lowReg_force_smooth`;
2. the driver produces a single smooth coordinate family with all
   time-jet/spatial masses;
3. spectral synthesis promotes that family to an order-two
   time-`L²` forcing;
4. `duhamel_mode_pin` identifies the promoted carrier with the
   order-one `duhamelCross` representative;
5. `direct_state_bound`, `direct_force_coeff`, and `direct_radius`
   provide the closed-slab state cap, the exact smooth forcing
   identity, and the realization radius.

This route does **not** consume a calibration tuple, completed A1/A2
maps, `IsRealizedTwo`, `liftForceHi`, `liftHiN`, or
`lowregLiftHorizon'`.  The earlier №236 `liftHiN` prototype was a
false detour and is superseded.  `carrier_coeff_pmConv` was promoted
from private to public without changing its statement or proof.
Focused verification is green and the axiom audit is exactly
`[propext, Classical.choice, Quot.sound]`.

The consumption map now fixes (c-A): parameterize only the diagonal
adapted-solve/low-mass/rung path actually read by `lowreg_directJet`.
Do not resume the adjacent-scale A1/A2 completion lane.

(c-C): the `(g, g_bg)` assembly `bgreg_allOrderJet` →
`bg_packet_of_adapt`, then rethread `lowreg_dt_unif`'s proof body
through `lowreg_adapt_unif` (statement unchanged).
The next serial task is the smallest background-aware adapted-solve
producer exposed by this checked consumption map.

## Design flags

1. **RESOLVED → C1 (№235, Pro ruling)**: the frontier is
   `bg_packet_of_adapt` over `IsAdaptedLowBg`; the calibration lives in
   the class-first `lowreg_adapt_unif` (uniform gate bounds + literal
   common `K` before `g`); `lowreg_dt_unif`'s proof body rethreads,
   statement unchanged.  Brick 6 builds `IsAdaptedLowBg` to exactly
   this consumption shape.
2. **RESOLVED → the №235 layering + STOP condition** (supersedes the
   №226 "widen (N) if it bites" remedy): only the absorptive slice is
   uniformized, with a mandatory ≤3-jet audit; if the audit fires,
   HALT and escalate — (N)-hypothesis changes are theorem-level user
   rulings.
3. **B? bodies — RESOLVED (№232 probe)**: four of five clean B
   (A1PerIndex engines; RungClosure:79; HigherRung:110; AllOrderJet
   :761/:1099 — force abstract, no `lowregNsec`/`coreN`/`lowregNfun`
   touched).  The fifth (C01 towers) held the one genuine C cluster —
   now scoped as bricks 2b-i/2b-ii with identified repairs (the
   `sub_self` insertion-difference at C01JetTower:211; the Ψ-collapse
   windows `lieA1Atgw`/`low1Atgw`; the C0 caps).  (c-A) total re-priced
   ≈14–19 sessions; order 2a → 2c → 2b-i → 2b-ii → 2d → 2e.

## Verification discipline

`./scripts/lake-locked.ps1 claim/check/release`; focused checks
`-NoLakeLock -LeanThreads 4 -LeanMemoryMB 6144`; ONE Lean process at a
time (DT checks import the 13.8k monolith — slow, plan sessions
accordingly); no `set_option`/`maxHeartbeats` (split declarations); names
≤ 20 letters; files ≤ 3000 lines; no monolith edits; no git commits; new
Bg siblings in NEW `ST/LowRegBg*` files, diagonal lane byte-stable except
the in-place DT widenings of bricks 2a–2e.

## Status log

- 2026-08-07 (№228): plan created from the scope-scout dossier; brick 1
  dispatched.
- 2026-08-07 (№231): brick 1 DONE and accepted — `IsBgSolveAt` +
  15 diagonal-shaped projections (`ST/LowRegBgSolveAt.lean`, 231 lines),
  green/warning-free/axiom-clean; constructible from `lowreg_sol_of_data`
  via `⟨hK, hsol, hTτ, hcap⟩`; zero statement-level field deltas (details
  in `LowRegBgSolveAt.md`).  Brick 2a dispatched.  B?-bodies probe
  (design flag 3) still in flight.
- 2026-08-07 (№232): B?-probe adopted — 4/5 bodies clean B; the C01
  towers hold the ONE genuine class-C cluster (three points, repairs
  identified, shelf originals exist); brick 2b split into 2b-i/2b-ii and
  re-priced; brick 3/7 rows enriched with the probe's work-list
  additions; (c-A) ≈14–19 sessions; order 2a → 2c → 2b-i → 2b-ii →
  2d → 2e.  Brick 2a still in flight.
- 2026-08-07 (№233): brick 2a DONE and accepted — the four C2-tower
  declarations widened in place, zero class-C surprises, three diagonal
  call sites fixed, targeted builds green incl. transparent downstream
  rebuild of SelfLowArmCaps + C01JetTower.  TOOLING: `lake-locked.ps1
  claim -Files` needs COMMA-separated paths (space-separated binds only
  the first; `.md` paths silently ignored).  Brick 2c dispatched.
- 2026-08-07 (№234): brick 2c DONE and accepted (A2 per-index
  two-metric; zero class-C).  Brick 2b-i (window C-repairs) dispatched.
- 2026-08-07 (№235): PRO OVERALL RULING reconciled and adopted — C1
  (frontier → `bg_packet_of_adapt` + `lowreg_adapt_unif`;
  `lowreg_dt_unif` proof-body rethread), (c-B) re-scoped to the
  absorptive slice with the ≤3-jet audit + STOP condition (№226's
  7-family scope refuted by the `e^{2f_n}` counterexample), phase
  order rearranged **c-C0 → c-A(minimal) → c-B → c-C**.  Plan
  sections rewritten accordingly.  2b-i continues (in every minimal
  set); c-C0 scout dispatched.  Pro sections 五–七 arrived garbled —
  re-paste requested before acting on them.
- 2026-08-07 (№236): c-C0 scout GO — verdict (ii): shelf + 2 new
  lemmas (`duhamel_mode_pin`, `lowreg_forceHi2`) + the calibration
  amendment, ≈3–4 sessions; the `IsRealizedTwo`-escape risk
  DISSOLVED (identification = shelf `force_hi_id` route; `fHi` via
  Nemytskii evaluation on `solFieldAtOrder`, not forcing mass).
  (c-C0) section rewritten with sub-bricks; remaining (c-A) bricks
  paused pending c-C0's consumption map.  Queue after 2b-i lands:
  c-C0-1 → c-C0-2 → c-C0-3.
- 2026-08-07 (Codex takeover): c-C0/Brick 0 DONE.  The proved public
  theorem is `lowreg_directJet`; focused verification and the axiom
  audit are green.  The proof uses a direct order-one forcing driver
  plus spectral H² promotion and contains none of the forbidden lift
  dependencies or equivalent high-scale certificates.  The №236
  calibration/`liftHiN` design is superseded.  Background widening is
  now restricted to this theorem's actual adapted-solve/low-mass/rung
  call graph; the older broad 2b-i queue is not resumed automatically.
- 2026-08-07 (№238): the direct endpoint was factored at the exact background
  seam.  `direct_jet_of_mass` is proved with primitive `(g,g_bg)` solve data
  plus all-order spatial mass; `lowreg_directJet` is now its diagonal wrapper.
  `bg_packet_of_mass` is proved and constructs `BgSmoothPacket` on the same
  horizon from `IsLowSolveBg` plus that mass.  The first background forcing
  leaf `galN_evalBg` is also green in new `LowRegBgForceArms.lean`.  The sole
  remaining endpoint input is therefore `lowreg_loMassBg`; its first genuine
  non-mechanical obstruction remains the A1/C01 insertion-difference seam at
  `armLadder3Bg`.  Headline `(N)` remains 0%; route-(c) background/adapted
  lane is approximately 40%.
- 2026-08-07 (№239): the mechanical background force-arm front is complete.
  `galN_evalBg`, `galArmIdBg`, `galArmCapBg`, and `galForceArmBg` all pass
  focused verification in `LowRegBgForceArms.lean` without new assumptions.
  The next declaration `armLadder3Bg` is intentionally not stated yet: its
  A1 input still depends on the diagonal C01 cancellation by `sub_self`.
  The serial next producer is the fixed-offset background A1/C01 estimate in
  brick 2b-i, followed by the retained insertion-difference bound in 2b-ii.
- 2026-08-07 (№240): bricks 2b-i/2b-ii DONE.  The previously identified C01
  seam is now closed by sharp `range (i + 2)` AMix and insertion windows,
  `lieBgJet`, the exact seven-term `selfLow_split_bg`, and the proved
  `selfLowJetQBg`/`c0JetTowerQBg` towers.  The old diagonal C0 endpoints remain
  compatibility wrappers.  All focused checks and the required targeted
  refreshes are green.  Brick 2d source port is in flight; the next serial
  producer after it is the background ladder/rung assembly, not another C0
  estimate.  Headline `(N)` remains 0%; route-(c) background endpoint lane is
  approximately 50%.
- 2026-08-07 (№241): bricks 2d/2e DONE.  `a1PerIdxJetBg`/
  `a1PerIdxLinBg` and the six arbitrary-background ladder declarations pass
  focused checks, axiom probes, and targeted refreshes; diagonal declarations
  retain their exact former types as wrappers.  The conditional per-metric
  Rung 3/4/5 ports are now in flight in separate Bg siblings.  This is still
  infrastructure: `lowreg_loMassBg` is unstated (0%) and headline `(N)` is 0%.
- 2026-08-07 (Codex rung-three brick): brick 3 DONE.  `galArmVecBg`,
  `armLadder3Bg`, `galArmMassOrdBg`, `lowregRung3OrdBg`, `IsRung3OrdBg`, and
  `lowregRung3PackBg` pass focused verification; the two direct modules were
  refreshed serially.  The ordered cap proof calls `lowData_split g₀ g_bg`
  directly, so `Kcap` remains outside the later `δ` binder.  Rung three is
  100%; the verified rung-3/4/5 subphase is about 33%; `lowreg_loMassBg` and
  headline `(N)` remain unstated/unproved (0%).
- 2026-08-07 (Codex rung-four/five bricks): brick 4 DONE.  The five public
  declarations in each of `LowRegBgRungFour.lean` and
  `LowRegBgRungFive.lean` pass focused verification and targeted refresh;
  both export files are fresh.  The ports preserve the ordered absorption
  binders and change only the fixed-background slots and their already proved
  Bg dependencies.  The verified rung-3/4/5 subphase is now 100%, while
  `lowreg_loMassBg` and headline `(N)` remain unstated/unproved (0%); the
  broader route-(c) background/adapted machinery is approximately 60%.
- 2026-08-07 (Codex metricwise gate brick): brick 5 DONE.
  `IsLowGateOrdBg` stores the exact rung-3/4/5 and arbitrary-background
  high-rung certificates for one `(g,g_bg)`, while `lowregGatePackBg` selects
  their two scalar sum envelopes.  Focused verification and the targeted
  refresh are green.  This is 100% of the metricwise bookkeeping brick but 0%
  of the still-unstated class-first absorptive gate theorem;
  `lowreg_loMassBg` and headline `(N)` remain 0%.
- 2026-08-07 (Codex Galerkin-identification brick): the production APIs
  `lowreg_proj_atBg` and `lowreg_projMode_atBg` are focused-green and the
  direct module refresh is green.  All spectral spaces, projections, heat
  operators, and eigenmodes stay on the state metric; only `lowregNfun` uses
  the independent background.  Compatibility-only endpoints were not ported.
  This identification brick is 100%, while brick 7 remains partial;
  `lowreg_loMassBg` and headline `(N)` remain unstated/unproved (0%).
- 2026-08-07 (Codex higher-rung brick): `galArmMassHmBg` and
  `lowregHighRungsBg` are focused-green; the single-thread targeted refresh is
  green and fresh. The exact path consumes `IsRung5PathBg`; no AllRungs
  endpoint was added. The minimal HigherRung brick is 100%, while brick 7
  remains partial; `lowreg_loMassBg` and headline `(N)` remain 0%.
- 2026-08-07 (Codex adapted-packet endpoint): brick 8 is DONE metricwise.
  `bg_packet_of_adapt` consumes one `IsAdaptedLowSolveBg`, obtains
  `lowreg_loMassBg`, and calls the proved `bg_packet_of_mass` with the stored
  bounds and solve projections.  Focused verification and the single-worker
  targeted refresh are green.  The old bare-solve `bg_packet_of_solve` sorry
  remains visible; the class-first adapted-solve producer/rethreading and
  headline `(N)` remain 0%.
- 2026-08-07 (Codex class-first absorption audit): **STOP CONDITION FIRED**.
  The complete metricwise adapted-to-packet chain is green, but its current
  rung-three absorption envelope already depends on the fourth jet of the
  varying metric through `fixCdAtgw 3`; rung four/five depend on still higher
  jets.  The C3 class therefore cannot supply one common `A,B` for
  `IsLowGateOrdBg`.  The next honest frontier is a redesigned
  absorption-only gate, not scalar shrinkage, time shrinkage, or another
  wrapper.  `lowreg_adapt_unif` and headline `(N)` remain 0%.
  The review prompt is recorded in `ROUTE_C_ABSORB_CONSULT.md`.
