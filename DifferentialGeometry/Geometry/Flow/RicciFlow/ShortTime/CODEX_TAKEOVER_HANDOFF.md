# Codex handoff: TAKE OVER the (N) uniform-existence campaign (2026-08-05)

Context for the operator: the Claude lane has driven this campaign through
ledger №167 (active ledger `UNIF_EXISTENCE_PLAN6.md`; PLAN5 = №142–166
closed).  At handoff time TWO tasks may still be in flight from the Claude
side: an executor for bricks F3+F4 (would report as №168 in PLAN6) and a
read-only acceptance panel for F1/F2.  The prompt below is robust to both
outcomes — Codex must verify the actual state first, trust nothing stale.
Copy everything below the line into the Codex session.

---- PROMPT BEGINS ----

You are TAKING OVER as planner+executor of a Lean 4 / mathlib campaign:
uniform low-regularity Ricci–DeTurck short-time existence, black box (N)
`ricci_flow_unif_existence` (`DifferentialGeometry/Geometry/Flow/RicciFlow/
Evolution/ExtendViaUniqueness.lean:80`, sorry `:98`).  The previous lane's
state is fully written down; your first job is to re-verify it, your second
is to continue it.

## Ground rules (non-negotiable)

- Repo: `E:\testdifferential-geometry-ste-align`, branch
  `codex/short-time-existence-align`.  Read `AGENTS.md` at the repo root
  first — it is the standing instruction set.  The old checkout
  `E:\testdifferential-geometry` is STALE; never edit it.
- All Lake via `./scripts/lake-locked.ps1`: `claim -Files ...` before
  editing; `check -Token <t> -Files <f> -NoLakeLock -LeanThreads 1` for
  focused checks; `build -NoLakeLock -LeanThreads 1 +Module.Name` targeted;
  `release -Token <t>` after.  NEVER a bare `lake build` of the root — a
  pre-existing broken leaf (`TimeTameFixedPoint.lean`) makes it fail.
- ONE Lean process at a time, `-LeanThreads 1`.  This is a 16 GB machine
  with two prior BSODs from concurrent/heavy elaboration.  Memory guard for
  heavy builds: kill lean if commit-free < 3 GB (hard); physical-free limb
  debounced (two consecutive 8 s polls AND commit declining).  After any
  kill/crash, remove `.lake/codex-locks/lean-elaboration.lock` only after
  confirming the pid is dead.
- Never force-release claims you did not create (several other lanes hold
  claims with dead pids — leave them; their files are READ-ONLY to you:
  `DeTurckRemainderLowBaseAction.lean`, `DeTurckRemainderLowBaseH2Pair.lean`,
  `DeTurckRemainderLowBaseC2Lip.lean`, `RHSRefoldPathIntegral.lean`,
  `RicciLinearizationConnDiffUniformBounds.lean`).
- No new `maxHeartbeats`.  Files ≤ 3000 lines.  Theorem names ≤ 20 letters,
  Mathlib casing.  Do not rewrite public definitions.
- git: the ENTIRE campaign delta (many sessions of verified work, including
  proved theorems and load-bearing UNTRACKED files) is uncommitted.  FIRST
  RECOMMENDATION TO THE OPERATOR: make a checkpoint commit before any new
  work.  If authorized to commit, do it as step zero.

## Step zero: verify the actual state (trust artifacts, never prose)

1. `git status --short` — establishes which files exist/are modified.
2. Read `ShortTime/UNIF_EXISTENCE_PLAN6.md` — the ACTIVE ledger.  Its
   rollover header is a self-contained state summary; then read the TAIL.
   - If entry №168 exists: bricks F3+F4 (the Fatou-stage close) landed —
     read their report; the stage may be done.
   - If №168 does NOT exist: F3+F4 were in flight at handoff and may have
     died — their full contracts are spelled in №167 (the `hL2H3` Bochner
     form + `Bd = ((1+T)R/4)²` route for F3; the `fatou_sq_mass` mirror of
     `GalerkinLimitUniformMass.lean:1167–1210` consuming `lowregFatouPack`
     for F4).  Re-dispatch/execute them per those contracts.
3. Re-run BOTH census files and READ the output — this is the campaign's
   verification currency (`lake env lean` exit-0 can be false-green; trust
   `#print axioms`, never docstrings or ledger prose):
   - `ShortTime/ScratchIdentCensus.lean` (ShortTime side, 29+ lines)
   - `DifferentialGeometry/Analysis/Spectral/Intrinsic/DeTurck/ScratchC01Census.lean`
   Every line must print `[propext, Classical.choice, Quot.sound]` — any
   `sorryAx` is a regression to investigate before proceeding.
4. Front-2 sorry census must be exactly TWO real sorries:
   `lowreg_loMass` (`ShortTime/LowRegAllOrderJet.lean:1052`, sorry :1065)
   and (N) itself (`ExtendViaUniqueness.lean:98`).  Grep to confirm.
5. An F1/F2 acceptance panel may not have completed at handoff.  Treat its
   job as YOURS on first contact with those files: before consuming
   `lowregFatouE3`/`lowregFatouPack` (F2) downstream, independently verify
   the a.e.→∀ derivative seam in `lowregModeDeriv`
   (`ShortTime/LowRegFatouIdent.lean`) and that `lowregFatouPack`'s two
   conjuncts really are `fatou_sq_mass`'s `hconv`/`hbound` shapes
   (`Analysis/Spectral/Intrinsic/GalerkinCompactness.lean:28–34`).

## What is PROVED and accepted (spot-check, then rely on)

- **`lowregRung3`** (`ShortTime/LowRegRungThree.lean:746–785`) — the rung-3
  closure: N-uniform `E₃ ≤ Φ` for ANY trajectory satisfying its hypothesis
  block; adapter H is an explicit hypothesis naming the theorem's own
  constants (`Ctop₂·Cδ + Kr2·R + Kr1·R + ε < 1`, `R = lowregStateRad`);
  `hL2H3` (the `∫E₃` budget) is carried as an explicit honest input.  The
  slot map is itself a Lean theorem (`armLadderAbs`).
- **The Fatou identification** (F2, `ShortTime/LowRegFatouIdent.lean`):
  the projected sequence's mode coordinates
  `c N t i := perModeConv λᵢ (timeModeCoeff (fseq N) i) t` satisfy the
  rung's trajectory block; endpoint `lowregFatouE3` = the rung riding the
  projected sequence.  KEY architecture (№165): no ODE-uniqueness anywhere;
  `lowregGalSol`/`galTamePerMode` are banked but OFF the critical path.
- The identification package `lowreg_proj_tendsto`/`lowreg_projMode_tendsto`
  (`ShortTime/LowRegGalerkinIdent.lean`) after THREE widenings exports:
  constants, nine certificates (δ-range, `Continuous coreN`, `hreal`, tame
  fields `B0`/`hcont`/`htame`), and six per-N conjuncts (Π_N-fixedness,
  a.e. state ball, a.e. Nemytskii, zero seed, PDE, forcing ball ≤ R/4).
  Destructuring is positional.

## The roadmap (honest pricing; ~4–6 sessions to `lowreg_loMass`)

UPDATE AT HANDOFF: **F3+F4 LANDED (№168) — the Fatou stage is closed.**
`lowregL2H3` discharges `hL2H3`; `lowregMassLow`
(`ShortTime/LowRegFatouMass.lean`) is the σ ≤ 3 mass bound claimed to hit
`lowreg_loMass`'s LITERAL conclusion object, gated only on GAP-ADAPTH.
YOUR FIRST VERIFICATION TASK (№169): re-run the census (31 declarations)
and independently verify №168's three load-bearing claims listed in №169
before consuming either endpoint.  Then:

1. **GAP-ADAPTH** (≈1, do first — cheapest and now the only gate on the
   σ ≤ 3 bound): producer-side smallness audit of `lowregStateRad` vs
   `Ctop₂/Kr2/Kr1/Cδ`; use GAP-ORDER's hoisted restatement.
2. **Rungs 4–5** (≈2–3): generalize the rung-3 pattern.  Known needs:
   a general-`k` regrouping of `armLadderAbs` (its constants are already
   `ℕ→ℝ` families) and a NEW engine variant — `galerkin_l1_single` exports
   only `sup_t E_k`, but rung k+1's `hL2H3`-analogue needs `∫E_{k+1}`
   (a dissipation-export variant; the engine's proof drops the dissipation
   term at `GalerkinParabolicEnergy.lean:151–153` — keep it instead).
   Upward ordering: rung k may use the previously proved `R_{k−1}` bounds
   (PSTOP §5).
3. **∀σ assembly** (≈1–2): interpolate/glue the three rungs into
   `lowreg_loMass`'s ∀σ-real conclusion; weight domination `(1+λ)^σ ≤
   (1+λ)^3` handles σ ≤ 3 (F4's argument); σ ∈ (3,5] from rungs 4–5.
4. **Registered honest inputs — discharge before or at assembly**
   (`PLAN6` header lists them; do NOT silently consume):
   - GAP-ADAPTH: the absorption inequality.  Discharge = producer-side
     smallness audit of `lowregStateRad` vs the rung's actual constants;
     use GAP-ORDER first (hoist the rung's ∃-constants above the class
     parameters — mechanically available from the same proof, the panel
     verified the witnesses are class-parameter-free).  THIS IS THE MAIN
     MATHEMATICAL RISK ITEM: if the radius cannot clear the constants,
     front-3's radius chain needs retuning (+1–2 sessions).
   - `D`/`hzero`/`hTτ` package exports: two more binders by the F1 pattern
     if a consumer needs the horizon cap.
5. Then `lowreg_loMass`'s own proof (the Fatou glue at general σ), which
   discharges front 2.  AFTER that: the (N)-assembly phase (≈4–7): front-3
   τ₀ inputs (`unifKsupZero/One` exist), chart-Gram C∞, PHASE-C
   DeTurck→Ricci conversion (Pro-ruled SOUND, unstarted), endpoint wiring.

## Disciplines that repeatedly saved this campaign (adopt them)

- **Check-first**: every substantive brick gets an adversarial read-only
  verification pass BEFORE its outputs are consumed.  Two true breakers
  (№155 JOINT-A1TOP; the №157 rider draft) were pricing arithmetic that
  LOOKED right — both caught by independent symbolic walks of the pairing.
  Never rule on pricing arithmetic (what multiplies `E_{k+1}`, what Young
  absorbs) without an independent re-derivation against the ACTUAL Lean
  interfaces (`two_mul_sum_ladder_le`'s hladder shape, the engine's
  `Cδ < 2` gate).
- **The E₄-whitelist test**: at rung k, the ONLY constants allowed on
  `E_{k+1}` are {Cq·Cδ*, K_R·R, K_R^{a₁}·R, 2ε}.  Any other constant
  landing there = the route is wrong, stop.
- **`jet₃` is priced by the class radius, NEVER by `√E₃`** — else the C₀
  slots go cubic and blow the `∫E₃` budget (the deep reason for the №157
  per-group split: C₁ keeps `S = range q`, C₀ uses `S = range (q−1)`).
- **Exhibit discipline** (17 over-count exhibits): before writing ANY
  "missing" producer, sweep the tree INCLUDING untracked files
  (`git status --short` first, then grep the worktree) and including the
  TensorHilbert/parametric layer; a private wrong-shaped near-miss does not
  count as existing, but a public lemma 273 lines above it might (exhibit
  16).  Both directions: also do not re-derive what exists.
- **Statement-last for endpoints**: an endpoint's numerical hypothesis must
  name the constants the proof actually produces; writing the statement
  first is the adapter antipattern.
- **Honest denominators in EVERY report**: theorem % separate from
  machinery %; `lowreg_loMass` is 0% until its sorry is gone regardless of
  machinery; (N) is 0%; whole HCG ≈3%.  Never let a green local tree read
  as global progress.
- **Ledger discipline**: one entry per landed/ruled brick, appended to
  `UNIF_EXISTENCE_PLAN6.md`; re-read the tail immediately before every
  append; same-name `.md` notes for every touched Lean file (route,
  reused/adapted/found, pass/fail — no command logs).
- **Route-error counter**: currently **1/3** (№155).  Semantics (user's
  ruling, №114): it is an unattended drift guard — score genuine route
  errors honestly (a consumer-unusable landed statement counts; a
  pre-adoption refuted draft does not), and stop driving at 3/3 until the
  user re-adjudicates.

## Lean traps specific to this tree (each cost a session or nearly)

- `lake env lean` exit-0 can be cached-stale AND can suppress
  `#print axioms` output — errors are real, SUCCESS is untrustworthy;
  verify with targeted `lake build` + census runs.
- Never `ring`/`ring_nf`/`nlinarith` on goals mentioning `set`-bound
  locals that carry `Exists.choose` — one such `ring` cost 8.4 GB and a
  BSOD chain; use explicit `mul_assoc`/`calc`.  `set` bodies also poison
  `linarith` — `clear_value` + clear the defining equalities.
- Never `norm_num` a per-index bound (it unfolds `iteratedCovGrad` and
  destroys the window shape).
- At Prop-slot defeq seams (`δ<1` proof terms, `4 2` vs `(2+2) 2`), apply
  lemmas with `exact`/defeq, NOT `rw` (kabstract fails).
- The a.e.→∀ crossing for per-mode ODEs is `perModeConv_timeL2_congr` +
  `Set.IccExtend` + `HasDerivWithinAt.congr_of_eventuallyEq` (the pattern
  is in `lowregModeDeriv`, `LowRegFatouIdent.lean`).
- A `have` quantifying over implicit variables is a LEMMA (per-declaration
  heartbeats); statement-only binders need underscore prefixes.
- Concurrent Lean builds crash heavy modules and evict oleans (transient
  false-fails — wait and retry, `-LeanThreads` low).

## Paper references

- `ShortTime/PSTOP_PROPOSITION.md` (v5+) — the design document; §6.4 with
  its two dated correction blocks is the rung-pricing authority; §10 lists
  adapters (H in its widened per-group form).
- `ShortTime/CODEX_LOMASS_AUDIT.md` — the prior Codex audit (J-map);
  superseded in parts by №148/№151/№165 but the completeness-hunt method
  stands.
- MSM135 (GSM Ricci-flow texts under `RicciFlow/`) — cite the book for
  theorem numbers.

## Reporting back to the user

End every session with: what landed (with census evidence), what failed and
why (classification: mathematical / missing-API / typeclass / coercion /
performance / tooling), the smallest next brick, and the honest nested
denominators ((N) 0% until its sorry is gone; `lowreg_loMass` theorem % and
machinery % separately; whole HCG ≈3%).  Prose, not tables.  Update the
memory of record: `UNIF_EXISTENCE_PLAN6.md` is the single source of truth.

---- PROMPT ENDS ----
