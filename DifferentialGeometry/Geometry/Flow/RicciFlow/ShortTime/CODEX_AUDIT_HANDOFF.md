# Codex handoff: independent audit of the `lowreg_loMass` endgame (2026-08-04)

Copy everything below the line into the Codex session.  Context for the
operator: the Claude lane has driven the (N) uniform-existence campaign
through ledger entries No. 104–134; the last three sessions each uncovered
a previously-unpriced layer in the final lane (identification → tame
Nemytskii → a = 1 Galerkin energy), so an INDEPENDENT audit is wanted
before more implementation.

UPDATE (2026-08-04, post-draft): brick (1) has LANDED green — new
`HeatSemigroup/GalerkinTameSol.lean` + `ShortTime/LowRegGalerkinSol.lean`;
the a = 1 `V_N` system `lowregGalSol` exists unconditionally on all of
`[0,T]` (28 declarations, zero sorryAx).  Load-bearing design choice to
audit: the retraction was taken in `H^{a+1}`, NOT `H^{a+2}` (parabolic MR
gives only an N-uniform `L∞_t H^{a+1}` bound, so an `H^{a+2}` retraction
would be inert only on an N-dependent region).  AND the brick exposed a
FOURTH unpriced piece, "brick (1b)": discharging the retraction needs the
N-uniform `H²` trajectory ball via an unconditional Grönwall
(`‖U(t)‖²_{H²} ≤ D'²(e^{2t}−1)`, `H³`-absorption coefficient ≤ 1/8 from
the existing smallness certificates) — prerequisite to brick (3).  The
Claude lane is HOLDING all further implementation pending this audit.
Remaining claimed distance: (1b) → (2) → (3) → calibration.  The
four-miss pattern (identification → tame → Galerkin energy → 1b) is
exactly what task A below must hunt to exhaustion.  The audit is
read-only and safe to run now; any implementation must respect
`lake-locked` claims.

---- PROMPT BEGINS ----

You are taking over as an INDEPENDENT AUDITOR of a Lean 4 / mathlib
differential-geometry campaign.  You were not involved in building it;
your value is fresh eyes.  Be adversarial: the campaign's own history
shows six "wall over-count" incidents (claimed blockers that had public
wrappers or dead gates) AND three consecutive under-pricing incidents
(each "final" session found a new missing layer).  Both failure modes are
documented; hunt for both.

## Ground rules

- Repo: `E:\testdifferential-geometry-ste-align`, branch
  `codex/short-time-existence-align`.  Read `AGENTS.md` at the repo root
  first — it is the standing instruction set (Lake only via
  `./scripts/lake-locked.ps1`; single Lean process, `-LeanThreads 1`;
  memory guard: kill lean if commit-free < 3 GB, physical limb debounced;
  no `lake build` of the root — a pre-existing broken leaf
  `TimeTameFixedPoint.lean` makes it fail; targeted builds only; never
  touch files claimed by other lanes — run `./scripts/lake-locked.ps1
  status` first; no new `maxHeartbeats`; files ≤ 3000 lines).
- THE AUDIT ITSELF IS READ-ONLY on `.lean` files.  You may run focused
  checks and `#print axioms` scratch probes (they need a claim on the
  scratch file only).  You may write ONE deliverable file:
  `DifferentialGeometry/Geometry/Flow/RicciFlow/ShortTime/CODEX_LOMASS_AUDIT.md`.
- Every claim you make: file:line evidence.  Every "X is missing": grep
  for public wrappers, sibling engines, and dead gates before asserting.
  Every "use engine Y": verify Y is THE engine the campaign instantiates
  (grep the call site), not a suitable-looking sibling — this exact
  mistake (auditing `partial_sol_const` when the campaign runs
  `partial_sol_tame`) cost a session.

## State you must independently re-verify (do not trust the ledger)

Read `ShortTime/UNIF_EXISTENCE_PLAN4.md` (entries No. 126–134 and the
executor reports; PLAN3/PLAN2/PLAN of the same directory are frozen
history) for the claimed state, then CHECK it:

1. Campaign sorry census.  Claimed: the ONLY front-2 `sorry` is
   `lowreg_loMass` (`ShortTime/LowRegAllOrderJet.lean:~1052`), and the
   black box (N) `ricci_flow_unif_existence` is stated at
   `Evolution/ExtendViaUniqueness.lean:80` with its `sorry` at `:98`.
   Verify by grep + `#print axioms` on `lowreg_spatialMass`,
   `lowreg_forceJetMass`, `lowreg_allOrderJet`, `lowreg_joint_two`,
   `lowreg_joint_smooth`, `c1_jet_tower`, `c0_jet_tower`, `a1_ladder`,
   `a2_ladder`, `n_diff_hm_rung` (expect: sorryAx only via
   `lowreg_loMass` where claimed, clean elsewhere).
2. The F6 estimate chain closure (both towers unconditional) and the
   floor deletion (no `lowregFloorHorizon` anywhere; order-2
   `staticForce` only in the two documented vestiges).
3. The statement of `lowreg_loMass` itself: is it PROVABLE as posed, and
   is it SUFFICIENT for its consumer (`lowreg_spatialMass` was proved
   from it by mode-coordinate transport)?  The campaign has already had
   to widen this frontier family twice (S0: `hbridge`/`hballU`;
   S0-bis: `fLo`/`hincl`/`IsLowSolve`).  Audit the CURRENT hypothesis
   list against the intended proof route below — if a third widening
   will be needed, better to find it now.

## The intended remaining route (audit its correctness AND completeness)

Paper design: `ShortTime/PSTOP_PROPOSITION.md` (v4, PASSED-WITH-ADAPTERS)
and the second Pro referee ruling `ShortTime/UNIF_N_PRO_RULING2.md`.
Landed machinery: the adapter layer (`HeatSemigroup/EigenProjDuhamel.lean`,
`EigenProjPartialSol.lean`, `EigenProjTameSol.lean`,
`ShortTime/LowRegGalerkinIdent.lean` — note `lowreg_projMode_tendsto` is
`fatou_sq_mass`'s `hconv`, ready), the hoisted ladders
(`DeTurck/LowRegLadderRung.lean`: `a2_ladder` κ-first, `a1_ladder`
κ-free), the L¹ₜ Grönwall (`HeatSemigroup/GalerkinParabolicEnergy.lean`:
`galerkin_energy_l1_bound`), and the pairing interface
(`Analysis/Sobolev/Tensor/CrossScaleCauchySchwarz.lean`:
`two_mul_sum_ladder_le`, whose `α < 1` is the absorption).

The claimed remaining distance (ledger No. 134): three bricks + one
calibration, each ≈ one session —
(1) the a = 1 `V_N` Galerkin ODE for `lowregNfun` from `tame_lip_balls`
    (`TameForcingFixedPoint.lean:64`), global on the `IsLowSolve`
    horizon (`ShortTime/UnifClassBounds.lean`);
(2) coordinate ↔ `perModeConv` identification (analogue of
    `galerkinPerMode_eq_perModeConvSymm`);
(3) the per-scale closure at base order 1 from the hoisted ladders;
then the calibration `ladder ⟶ (α, β, D)` feeding
`two_mul_sum_ladder_le` → `galerkin_energy_l1_bound` → N-uniform all-σ
mass → `lowreg_projMode_tendsto` → `fatou_sq_mass` → `lowreg_loMass`.

## Audit tasks (in priority order)

A. COMPLETENESS HUNT — the headline question.  Walk the pipeline
   backward from `lowreg_loMass`'s conclusion to the landed pieces and
   list EVERY lemma-shaped joint that does not yet exist, with its
   producer/consumer signatures.  The three prior misses were all of
   the form "a named step silently assumed an interface that was not
   there" (a fixed point that was not Lipschitz; an energy engine that
   was gated; an identification that needed a ball).  Specifically
   check: does the per-scale closure (3) actually compose with
   `two_mul_sum_ladder_le`'s `hclosure` shape at a = 1?  Do the mass
   summands of the hierarchy match `lowreg_loMass`'s `perModeConv`
   object (the R-4 clarification says the STATE's mass, via continuous
   mode convolutions — check which object the statement's conclusion
   actually speaks about)?  Does the calibration have all its inputs
   (κ from the hoisted `a2_ladder`; δ*; `Clower`; the per-datum static
   `‖𝒩(0)‖`; the primitive `S` from `‖U_N‖²_{L²_tH³}`) PRODUCIBLE at
   a = 1 from `IsLowSolve` data?
B. NECESSITY CHALLENGE.  Session 1 argued (blocker analysis) that no
   bootstrap exists and truncating the true solution is circular, so a
   `V_N` Galerkin construction is unavoidable.  Re-derive or refute
   that argument.  If a Galerkin-free route exists (e.g. a smoothing/
   semigroup route to the all-σ mass of the a = 1 fixed point using the
   tree's interior-smoothing machinery), the three-brick lane may be
   deletable — that would be the single most valuable finding.
C. STATEMENT AUDIT of `lowreg_loMass` (task 3 above) and of
   `IsLowSolve`'s fields vs `partial_sol_tame`'s ACTUAL hypothesis
   slots (grep the instantiation at `UnifClassBounds.lean:~263`).
D. PRICE the corrected lane in sessions, honestly (the campaign's
   history: estimates have been optimistic by ~2× on this lane).
E. SPOT-CHECK the six-exhibit over-count list in reverse: are any of
   the "landed" pieces weaker than advertised (e.g. a lemma whose
   statement quantifies differently than the report claims)?  Pick the
   three most load-bearing (`tameMap_dist_le`, `projFixTame_le_two`,
   `galerkin_energy_l1_bound`) and read their STATEMENTS against what
   the pipeline needs from them.

## Deliverable

`ShortTime/CODEX_LOMASS_AUDIT.md`, house style, file:line everywhere:
§1 census verification results (pass/fail per item);
§2 the completeness map (every missing joint, named);
§3 the necessity verdict (Galerkin unavoidable / avoidable via …);
§4 statement audit (third widening needed? exact binder list if so);
§5 the corrected brick plan with honest session pricing;
§6 discrepancies found in landed pieces (or "none");
§7 a one-paragraph verdict: CONTINUE AS PLANNED / CONTINUE WITH
   CORRECTIONS (list) / STOP AND REDESIGN (why).
End with the single next concrete brick you would dispatch, with its
full handoff (consumer signature verbatim, producer inventory,
verification recipe).  Honest denominators throughout ((N) is 0% and
stays 0% regardless of this audit; whole HCG compactness project: low
single digits).

---- PROMPT ENDS ----
