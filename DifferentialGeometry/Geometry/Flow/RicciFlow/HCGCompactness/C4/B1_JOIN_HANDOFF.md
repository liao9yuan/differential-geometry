# B1 JOIN (C3 producer join → C2 smoothness → lbl397 assembly) — GPT kickoff prompt

**Supersedes `STEPC_B1_HANDOFF.md` (its task (A) and most of (B)/(D) landed).
Paste everything below the line into the new session. Self-contained.**

---

Work in `E:\testdifferential-geometry` (Lean 4 / Mathlib, branch `short-time-existence`).
All Lake ops go through `scripts/lake-locked.ps1` (`claim` before editing, `check`/`build`,
`release` after; never call `lake` directly; `status` first — several sessions are active, and
there may be stale locks from dead pids: confirm the pid is dead before `release -Force`).
Read `CLAUDE.md` first. NEVER push. Same-name `.md` notes for findings. Report = math conclusion
+ where stuck, in prose; honest % of the whole project (~20–25%; one lemma is a small fraction).
Trust `lake build` over `lake env lean` for SUCCESS claims (cached false-greens exist; axiom
probes are also suppressed under `lake env lean`).

**Read these live notes end-to-end before coding** (they are the ground truth of what exists):
`…/C4/StepCCenterOfMass.md` (all implementation updates), `…/C4/StepCAveraging.md`,
`Comparison/HalfSqDistGrad.md`, `…/C4/StepBApproxIso.md`, `…/C4/CHAPTER4_PLAN.md`.

## Current state (verified, all 0-sorry — do NOT rebuild)

- **lbl394** (local metric + transition limits): `StepBLocalMetrics.exists_metricLimit_normalCoord`,
  `StepBTransition.exists_transitionLimit_normalTransition` (+ `contDiffOn_normalTransition`,
  `StepBInputs.normalChartAt_contMDiffAt_infty` — the `C∞` chart inverse).
- **lbl399 at `C∞`**: `StepBApproxIso.comp_cInf_id_on` on the Faà-di-Bruno engine
  `…/HCGCompactness/MapConvergenceComp.lean` (two-parameter `A_ℓ∘B_k → id` in `C∞` on compacts).
- **Hopf–Rinow properness**: `Comparison/HopfRinowProper.lean`; `exists_proper_realization` closed.
- **lbl411 one-summand gradient**: `Comparison/HalfSqDistGradMain.grad_halfSqDist`
  (`grad(½d(·,pt)²) q = -exp_q⁻¹ pt` under source/smallness/non-self hypotheses; the moving-base
  inverse-exponential `diagExpInv` chain is done). Supporting: `HalfSqDistGrad.lean`, `HalfSqDistGradVar.lean`.
- **C1 + wrapper**: `…/C4/StepCInputs.lean` (`StrictDistInput` = the lbl413 Hessian honest input),
  `…/C4/StepCCenterOfMass.lean` (`CenterInput`, `centerOfMass` def, `.mem/.min/.unique/.dist_le`,
  `.expInv_eqn` and `.expInv_eqn_local` — the book equation `Σ μᵢ exp_cm⁻¹ qᵢ = 0` with an
  `∃ ρ` bridge that discharges the gradient hypotheses from source/smallness/differentiability).
- **Averaging analytic layer**: `…/C4/StepCAveraging.lean` (`centerAverage`, `centerAverageOn`,
  `activeFill`, the `→id` uniform machinery `unif_tendsto*`/`unif_two_index*`/`unif_two_id_fill`,
  and the data-packaged `centerAverage.unifTwoIdDataOn`).
- **POU/cage layer**: `…/C4/StepCAveragePOU.lean` (chart-level `→id` convergence facts
  `chartSymmIdConv`/`chartPtsConv`, the `hatSourceBall`/`hatSourceCage` compact-source geometry from
  `InjRadiusDecayInput`, and `NetLimitData` routing `hatPOU_active_data` into `unifTwoIdDataOn`).

## The remaining gap to lbl397 (B1), in the notes' own words

`StepCAveraging.md`: "This is still not the full C3 partition-of-unity construction. The next
producer layer must combine the finite POU weights with concrete local forward/inverse maps from
the Step-A/Step-B geometry on the covered source set, prove the pointwise active-map radius facts
and strict-convexity hypotheses for the filled family there, pass `NetLimitData.hatPOU_active_data`
directly to `centerAverage.unifTwoIdDataOn`, and prove the active local-map convergence on the
regions selected by the bundled support bridge."

Plus: **C2 (lbl430, smooth dependence of `cm`)** is not started as a Lean endpoint, and
**`…/C4/StepB1ApproxIso.lean` (lbl397) does not exist**.

## Tasks, in order

**(1) C3 producer join** (new `…/C4/StepCProducers.lean` or extend `StepCAveragePOU.lean`):
instantiate the abstract averaging with the CONCRETE local maps. The local maps are the book's
`F_{kℓ}^α = H̄_ℓ^α ∘ (H̄_k^α)⁻¹` — in this codebase, compositions of `expMapDiffeo`/`normalChartAt`
across two manifolds of the sequence (the same shape as `StepBInputs.normalTransition`, but
`M_k → M_ℓ`; check `StepBTransition`/`GoodCovering*` for the existing cross-manifold map producers
before defining a new one). Obligations, all on the covered source set:
- the active local maps and the target point land in the chosen small ball (radius facts — from
  `hatSourceBall`/`hatCage*` + the Step-A cover radii);
- source/smallness/differentiability for every active summand (what `expInv_eqn_local` and
  `grad_halfSqDist` consume — differentiability comes from `normalChartAt_contMDiffAt_infty`-side
  smoothness of `halfSqDist`, already available in the `HalfSqDistGrad*` layer);
- `StrictDistInput` supplied for the filled finite family (it is the lbl413 honest input — thread
  it, do not prove it);
- active local-map `→id` convergence on the selected regions: this is EXACTLY lbl399 =
  `comp_cInf_id_on` (`C∞`) / the `C⁰` corollaries — wire it in (note `StepCAveraging.lean` does not
  yet import `MapConvergenceComp`; add the import at the consumer, not by editing the engine).
Acceptance: a theorem `averaged map → id uniformly (two-index) on the covered compact source`,
i.e. `NetLimitData.hatPOU_active_data → centerAverage.unifTwoIdDataOn` fully discharged for the
concrete maps. Targeted build green, axiom-print `[propext, Classical.choice, Quot.sound]`.

**(2) C2 = lbl430, smooth dependence of `cm`** (extend `Comparison/CenterOfMass.lean` +
`C4/StepCCenterOfMass.lean`): IFT on the gradient equation `Σ μᵢ exp_q⁻¹ qᵢ = 0`.
Ingredients: `grad_halfSqDist` (done), the nondegenerate-Hessian input (extend `StrictDistInput`
with the Hessian-lower-bound field if the IFT needs the quantitative form — still lbl413, still
honest), and the manifold IFT pattern used in `StepBInputs.normalChartAt_contMDiffAt_infty`
(pointwise Banach IFT via `(fderiv …).IsInvertible`; that file documents the `TangentSpace` defeq
trap — read its `.md`). Book: chapter4.tex around `lbl430` (L2709+). Acceptance: `cm` is `C^p` in
(weights, points) on the relevant domain, stated `U`-relative.
This brick is the riskiest; if the manifold-IFT plumbing for the implicit function (not inverse
function) is missing, STOP and report the smallest missing lemma (likely a product-manifold
implicit-function wrapper) rather than building a broad framework.

**(3) lbl397 = B1 assembly** (new `…/C4/StepB1ApproxIso.lean`): `F_{kℓ;r} := centerAverageOn …`
is a diffeomorphism onto its image and an `(ε,p)`-approximate isometry on `B(O_k,r)` for
`k,ℓ ≥ k₀(r,ε,p)`. Consumes (1)+(2), the `→id` convergence, `IsApproxIsometryOn`/
`BookApproxIsometryData` (`ApproxIsometryDefs.lean`), the composition bounds F5/F6
(`ApproxIsometryCompHigher.comp_cov_le`/`comp_cov_accum`), and lbl394. Follow the book's proof
(chapter4.tex L1622–1881) literally; state it against the Step-A cover data
(`GoodCoveringSeq`/`StepAInputs`). Acceptance: the lbl397 statement as one Lean theorem with only
the documented honest inputs; update `CHAPTER4_PLAN.md` B1 checkbox.

**(4)** After (3): update the same-name `.md`s + `CHAPTER4_PLAN.md` critical path. The next
consumer is Step D (D1/D2 gluing on the direct-limit; `DirectLimit.lean` F9–F13 are done).

## Constraints / coordination

- Off-limits (other sessions own or settled): the variation/`HalfSqDistGrad*`/`diagExp*` layer
  (consume its public theorems only); Ch3 P-track (`RicBound*`, `MetricPreconv*`,
  `PointedConvergence`, `AllTimes*`, `FlowLimit*`, `SolutionPullback`); settled Step-B files
  (`StepBInputs`, `StepBLocalMetrics`, `StepBTransition`, `StepBApproxIso`, `MapConvergenceComp` —
  import, don't edit); the sphere/space-form files (`RoundShape`, `ConstCurvature`,
  `PullbackNaturality*` — a live parallel session).
- Honest-input discipline: lbl413 (`StrictDistInput`, extendable with a Hessian field) and the
  existing Step-A inputs (`InjRadiusDecayInput`, `ExpInverseDerivBoundInput`, `lbl395`) are the
  ONLY honest inputs. Everything else is proved. No new `sorry`.
- Naming: ≤20 letters, conclusion-first (`CLAUDE.md` rules); new reusable lemmas go in the lowest
  suitable layer (general Riemannian → `Comparison/`; HCG-specific → `C4/`).
- Stop conditions: three genuinely different failed routes on one theorem, a missing-API wall
  (report the smallest bridge lemma), or a statement that contradicts the book — then report per
  `CLAUDE.md` (theorem, goal, error, routes tried, suspected obstruction, GPT-consult prompt).
