# TimeH1Modulus.lean — the `√t` Hölder-½ time modulus

Executor session (Opus 4.8) on worktree `C:/Users/liao9/.codex/worktrees/e87b/...`,
branch `codex/analytic-producers-e87b` @ `922dbc4ac`.  This is **ruling item 1**
of the six-item R1τ frontier in
`Geometry/Flow/RicciFlow/ShortTime/UNIF_N_PRO_RULING.md` — the generic `timeH1`
`√t`-modulus lemma.  It is consumed later by **item 5** (the fixed-horizon
representative), and replaces the naked `ContinuousWithinAt` δ used at
`Analysis/Spectral/Intrinsic/DeTurck/MaxRegSolutionJointlySmooth.lean:1138`.

## What was delivered

Two public theorems, in namespace `DifferentialGeometry.Analysis.Parabolic.TimeSobolev`:

1. `integral_norm_Icc_le (f : timeL2 X T) (ht : t ∈ Icc 0 T) :`
   `∫ s in Icc 0 t, ‖f s‖ ≤ √t · ‖f‖`
   — the sharp-horizon (`√t`) companion of the existing whole-horizon (`√T`)
   `TimeSobolev.integral_norm_le` (`BochnerL2.lean:278`).

2. `timeH1.norm_toFun_sub_init_le (u : timeH1 X T) (ht : t ∈ Icc 0 T) :`
   `‖u.toFun t − u.init‖ ≤ √t · ‖u.deriv‖`
   — the main deliverable: the explicit ½-Hölder modulus.  Stated in the
   carrier's own currency (`u.init` = value at 0 = `trace0 X T u`; `u.deriv` =
   the time-`L²([0,T];X)` field = `timeDeriv X T u`; both defeq via the `rfl`
   simp lemmas `trace0_apply`/`timeDeriv_apply`), matching the ruling's item-1
   wording exactly.  Weakest carrier hypotheses: only `t ∈ Icc 0 T` (the carrier
   already fixes `X` a real Hilbert space).

## Route (feasible, implemented)

Carrier facts reused from `TimeH1.lean` (no re-derivation of absolute
continuity — the FTC increment already exists):
- `toFun_apply` + `abel` gives `u.toFun t − u.init = ∫ s in 0..t, u.deriv s`
  (equivalently the committed `toFun_sub_toFun` with `t₀ = 0`, `toFun_zero`).
- `intervalIntegral.integral_of_le` (`0 ≤ t`) → integral over `Ioc 0 t`.
- `norm_integral_le_integral_norm` → `∫_{Ioc 0 t} ‖deriv‖`.
- `setIntegral_mono_set` (`Ioc 0 t ⊆ Icc 0 t`) → `∫_{Icc 0 t} ‖deriv‖`.
- `integral_norm_Icc_le` → `√t · ‖deriv‖`.

`integral_norm_Icc_le` is a faithful copy of `BochnerL2.integral_norm_le` but on
the **sub-measure** `timeMeasure t`: `L¹ ⊆ L²` Hölder nesting
(`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, total mass `= t`) plus one
monotonicity step `eLpNorm ⇑f 2 (timeMeasure t) ≤ eLpNorm ⇑f 2 (timeMeasure T)`
(`eLpNorm_mono_measure` with `timeMeasure t ≤ timeMeasure T` from
`Measure.restrict_mono`).  The `√t` (not `√T`) is exactly what makes this a
modulus that vanishes as `t → 0` — the whole point of item 1.

## Reuse audit

No existing `√t` modulus anywhere (grepped TimeSobolev + ShortTime): `TimeH1.lean`
has only `norm_toFun_le` (bounds `‖toFun t‖`, not the difference, and with `√T`)
and `norm_toFun_le_norm`.  So this is genuinely new, not a duplicate.  Canonical
home of `integral_norm_Icc_le` would be `BochnerL2.lean` next to `integral_norm_le`;
kept in this additive leaf per the dispatch guardrail (do not edit committed-clean
tracked files — `TimeH1.lean`/`BochnerL2.lean` are both clean).

## Verification status

**GREEN — verified sorry-free (2026-07-23).**  `scripts/lake-locked.ps1` is
absent in this worktree, so verification was the CLAUDE.md-sanctioned read-only
form `LEAN_NUM_THREADS=4 lake env lean …/TimeH1Modulus.lean` (imports built;
fresh file ⟹ no stale-olean false-green risk).  Result: exit 0, no errors, no
warnings.  `#print axioms` on both theorems =
`[propext, Classical.choice, Quot.sound]` (the sanctioned trio; no `sorryAx`, no
extra axioms).  Concurrency note: a fully quiet window was caught by the poll
waiter, but 2–3 Codex `lean.exe` had respawned by the time each check launched,
so both checks ran with mild concurrency — acceptable because concurrency risks
only false *failures* (thread exhaustion), never false passes; both runs
produced clean, meaningful output.  Temporary `#print axioms` lines were stripped
after the green.

All Mathlib primitives were also confirmed present with matching signatures
against `.lake/packages/mathlib` before writing: `eLpNorm_mono_measure (f) (ν ≤ μ)`,
`AEStronglyMeasurable.mono_measure`, `Ne.lt_top`, `Lp.eLpNorm_ne_top`,
`ENNReal.rpow_ne_top_of_nonneg`, `ENNReal.toReal_mono`, `setIntegral_mono_set`,
`intervalIntegral.integral_of_le`.  The proof mirrors the already-verified
`integral_norm_le`/`norm_toFun_le` in the same file family.

## Honest accounting

(N) `ricci_flow_unif_existence` remains **0%** (unstated in Lean terms; this is
pure supporting infrastructure).  This brick is 1 of 6 R1τ ruling items and is
the shallowest (generic functional-analytic modulus, no geometry).  It does not
by itself move (N); item 2 (the decisive second-order tame estimate) is the
route test, and items 3–6 remain.

---

## 2026-08-03 — option-(b) bricks B1/B2: two state-bound producers added

`OPTIONB_FLOOR_PLAN.md` bricks B1 and B2 (planner ruling No. 106) both landed
their producer lemma in THIS file.  The file is now "pointwise-in-time state
bounds for `timeH1`", not only the `√t` modulus.

* `state_le_of_sqrt_floor` (`:136`) — B1's extracted producer.  From
  `hinit : u.init = 0` and a horizon floor `√T · ‖u.deriv‖ ≤ B` it gives
  `∀ t ∈ Icc 0 T, ‖u.toFun t‖ ≤ B`.  Stated for a generic real `B` (no `C`, no
  positivity): it is exactly the four-line `calc` that used to live inside
  `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`, lifted to
  its weakest form.  Proof = `norm_toFun_sub_init_le` + `Real.sqrt_le_sqrt`.
* `norm_le_of_ae_le` (`:156`) — B2.  From `0 < T` and
  `∀ᵐ t ∂timeMeasure T, ‖u.toFun t‖ ≤ R` it gives the bound at EVERY
  `t ∈ Icc 0 T`, the closed endpoint `t = T` included.

### Home choice (deviation from the plan's sketch, deliberate)

`OPTIONB_FLOOR_PLAN.md` §6 sketched `state_le_of_sqrt_floor` in engine-file
shape (`MaxRegSolutionSpace`, `trace0`).  It is stated here instead, generic in
`X` and `B`, because (i) this is the canonical home — beside
`norm_toFun_sub_init_le`, the only lemma it uses — and (ii) the rebuild cost is
nil: `TimeH1Modulus.lean` has exactly ONE importer repo-wide
(`MaxRegSolutionJointlySmooth.lean`), so editing it is as cheap as editing the
engine.  `hinit : u.init = 0` is taken instead of `htrace` (weaker, and keeps
`trace0` out of this module's dependencies); the single consumer derives it with
`timeH1.trace0_apply` at its call site.

B2's canonical home would be beside `continuousOn_toFun` in `TimeH1.lean`, but
that file has 7 direct importers; placed here (next to `state_le_of_sqrt_floor`,
the sibling state bound) per the brick's fallback instruction.

### The `t = T` endpoint — the identified design risk, CLOSED

B2's only real risk was whether the a.e.→everywhere upgrade reaches the closed
endpoint.  It does, with no weakening to `Ico`:
`MeasureTheory.Measure.eqOn_Icc_of_ae_eq` (mathlib `Measure/OpenPos.lean:194`)
takes exactly one extra hypothesis over its `Ico` sibling, `hne : (0:ℝ) ≠ T`,
discharged by `hT.ne`; it is proved from `closure (interior (Icc a b)) = Icc a b`,
which holds precisely for `a ≠ b`.  The `min ‖u.toFun ·‖ R` truncation trick
(precedent: `LowRegAllOrderJet.lean:334-348`, which used the `Ico` sibling)
transports it to a `≤` statement: the truncation agrees a.e. with the norm, both
are `ContinuousOn (Icc 0 T)`, hence they agree at every point, and
`min_eq_left_iff` reads that off as the bound.  No `Ico` fallback, no route-B
`H¹`-floor fallback needed.  Note `timeMeasure T` is a plain `def` for
`volume.restrict (Icc 0 T)`, so `filter_upwards` crosses the two spellings by
defeq without an unfolding step.

### Verification

**GREEN.**  Focused check of this file passed (no errors, no warnings), the
module olean was refreshed by a targeted build, and the whole downstream chain
through `LowRegAllOrderJet` rebuilt clean.  `#print axioms` on
`state_le_of_sqrt_floor` and `norm_le_of_ae_le` = `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`.  Both lemmas compiled on the first attempt.

### Honest accounting

Zero new mathematics.  `state_le_of_sqrt_floor` is a relocation of an existing
verified `calc`; `norm_le_of_ae_le` is one small real lemma (~12 lines) whose
content is standard measure-theoretic density.  (N) stays **0%**.
`norm_le_of_ae_le` has NO consumer yet — it lands as a standalone producer for
option-(b) brick B5.
