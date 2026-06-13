# P3 EXECUTION PLAN — metric preconvergence + window upgrade (MSM135 lbl351 → 3.10 input)

**Audience: implementing agent (Opus session / subagent) with NO memory of the
planning session.  Written 2026-06-11 by the planning (Fable) session.**

---

## PLANNER ACCEPTANCE + WORKFLOW NOTE — Step 4b-ii core (2026-06-13)

ACCEPTED (own build + axioms): `tangentConst_basis_expand` + `bz_eq_tangentConst`
(commit 78a119b0) — the constant-`M` algebra core, AXIOM-CLEAN, green 3866 jobs.
The de-risked insight is now realized in Lean: `bz` (norm-bridge basis) = the
chart-constant `tangentConstInChart` frame = a z-independent combo of the
`finBasis` frame. **Every mathematical risk in P3 is now retired and verified.**

**WORKFLOW RULING: dispatch the rest of 4b as ONE end-to-end session, not
per-helper.** Rationale: fine per-helper slicing was the correct cadence WHILE
mathematical risk was live (it surfaced the pointwise ruling, the
`exists_eq_at_gen` simplification, and the constant-`M` insight each at the
right moment). That risk is now gone — the remaining 4b is pure wiring (the
per-slot bridge `bz(I0 q)=V^{I0}_q(z')` with patch-domain bookkeeping, the
tower-carrier identity, the uniform-on-patch extraction, the global chart-cover
diagonal, the finite-cover `hnorm` assembly). Slicing it further is inefficient
and risks an inconsistent half-state. ONE focused session, end to end, to land
`metricPreconvInf`.

## PLANNER ACCEPTANCE — assembly Step 4a (2026-06-13)

ACCEPTED (own build + axioms): `componentConv_covDeriv_of_chartCInf`
(commit 6c8e5e12) — the pointwise Gap-B endpoint, a≥1 covariant-tower
component convergence at a point, general order, frame-general basis.
AXIOM-CLEAN, green 3866 jobs. **The hardest mathematical content of P3 is
now done.** The pointwise RULING was correct and the `exists_eq_at_gen`
simplification made the section choice a one-liner (only fix: its arg is
`n : ℕ∞`).

REMAINING = Step 4b only → `metricPreconvInf` (still unstated, 0%). Two
sub-assemblies, both API-complete:
- **4b-i (global diagonal):** `exists_chart_cover` + `exists_diag_subseq`
  over the countable cover (`hstep` = per-chart `exists_tower_conv`) → one φ
  carrying tower data on every chart.
- **4b-ii (uniform hnorm):** `metricDerivNorm_le_compSq_uniform` (ric_bound
  finite-cover pattern) → `hnorm` → `metricCInfConvOnCompacts_of_normConv`.
  **DE-RISKED (executor scout + planner first-principles check, HIGH conf):**
  the norm-bridge basis `bz_i(z) = Σ_j M_{ij}·frame_j(z)` with `M` the
  CONSTANT (z-independent) `basisE↔finBasis` change of basis in `E` — because
  both `bz_i(z)` and the coordinate frame `frame_j(z)` are `e.symmL(z)`
  (linear) applied to a fixed `E`-vector. So `component0S bz` is a
  constant-coefficient combo of the uniformly-convergent coordinate-frame
  carriers (`bumpTowerCarrier_all`'s `MapCInfConvOnCompacts`, order-0 slice);
  uniform-on-K convergence transfers with NO z-varying-basis obstruction.
  This does NOT reopen the pointwise RULING (the THEOREM stays pointwise —
  `component0S bz` uniform is still ill-typed); uniformity is recovered HERE,
  downstream, exactly as the RULING said. No missing API.

## PLANNER ACCEPTANCE — assembly Steps 1-3 (2026-06-13)

ACCEPTED (own build + axioms): `exists_framePairs_diag` (1-rest),
`framePairs_pinned` (2), `exists_tower_conv` (3) — all AXIOM-CLEAN, green
3866 jobs. The per-chart `hpairs → all-orders tower C∞ conv on U` pipeline is
done; the RULING held (machinery delivers `MapCInfConvOnCompacts`, no
uniform-through-expansion lemma built). Commits f0dc74fd, fa535664, b316fea8.

REMAINING = Step 4 only (metricPreconvInf still 0%/unstated). Two pieces:
(4a) `componentConv_covDeriv_of_chartCInf` POINTWISE (per the RULING) —
`exists_tower_conv` + `tendsto_of_cInf` at `extChartAt x₀ x` + the multilinear
`b (I0 q)`-expansion; carrier↔`component0S … metricCovDeriv` via
`component0S_apply`+`metricCovDeriv_eq_covDerivOfField` (both rfl).
**SIMPLIFICATION (planner, verified):** the flagged "section-value-at-a-point
fiddle" is a ONE-LINER — `ContMDiffSection.exists_eq_at_gen x (b (I0 q))`
(SectionRealized.lean:204, sig `(p)(v) : ∃ σ, σ p = v`) gives `V_q` with
`V_q x = b (I0 q)` directly; do NOT route through `exists_section_eqOn_compact`
+ chart coordinates of `b (I0 q)` (harder). (4b) `metricPreconvInf`: global
chart-cover diagonal (`exists_chart_cover` + `exists_diag_subseq`) → one φ
carrying tower data on every chart, then finite good-frame cover
(`metricDerivNorm_le_compSq_uniform`, ric_bound pattern) → `hnorm` →
`metricCInfConvOnCompacts_of_normConv`. No missing API.

## PLANNER ACCEPTANCE + RULING — assembly Step 1 (2026-06-13)

ACCEPTED (own build + axioms): `exists_cInf_subseq_finiteFamily`
(ComponentConvAssembly.lean — the finite n²-fold C∞ diagonal) — AXIOM-CLEAN,
green 3866 jobs.

**RULING — uniform-vs-pointwise endpoint shape (resolves the executor's flagged
subtlety; HIGH confidence, signatures traced + independently spot-checked):**
The executor flagged that `componentConv_covDeriv_of_chartCInf` should be UNIFORM
because `bumpTowerCarrier_all` delivers `MapCInfConvOnCompacts` and `hnorm` needs
uniform-on-K. **This is WRONG.** The norm bridge's component basis
`bz = (…).toBasisAt hz` (MetricPreconvBridge.lean:102-103) is POINT-DEPENDENT, so a
`TendstoUniformlyOn` of `component0S bz (…)` is ILL-TYPED, not just unnecessary.
RULING: state `componentConv_covDeriv_of_chartCInf` **POINTWISE**, mirroring
`componentConv_covDeriv_zero` (MetricPreconvDiag.lean:613-636) at general order `a`
(fixed `x`, frame-general basis, fixed `I0`, `Filter.Tendsto`). The uniform-on-K of
`hnorm` is a SEPARATE finite good-frame cover step (`metricDerivNorm_le_compSq_uniform`,
the `ric_bound` pattern) — already the plan of record. NO conversion lemma is
missing; building a TendstoUniformlyOn-through-the-expansion lemma would be wasted,
ill-typed effort. The misleading note in ComponentConvTower.md is now struck through
and corrected. Remaining real work: (1) `componentConv_covDeriv_of_chartCInf` for
a≥1 (pointwise: `tendsto_of_cInf` + multilinear expansion); (2) the finite good-frame
cover lemma → `hnorm`; both API-complete.

## PLANNER ACCEPTANCE LOG — Gap B (2026-06-13)

Planner re-verified (own build + `#print axioms`, not just executor report):
- `metricPreconv_gInf` (MetricPreconvDiag.lean) — C1b: subsequence + smooth
  limit metric `gInf` w/ pointwise CLM convergence. **AXIOM-CLEAN.** The gInf
  gate is fully discharged (consumes `smoothMetric_of_localCoeff`).
- `bumpTowerCarrier_all` (ComponentConvTower.lean) — the all-orders
  covariant-tower component-convergence induction. **AXIOM-CLEAN.**
- `exists_chart_engineInput_family` (shared-χ finite-family engine input).
  **AXIOM-CLEAN.**  ComponentConvTower builds green (3854 jobs).

STATE: P3 machinery ~85% (limit-metric construction + tower induction DONE).
`metricPreconvInf` endpoint still UNSTATED (0%).  REMAINING = the 4 assembly
steps in ComponentConvTower.md "REMAINING": (1) diagonal→one φ, (2)
limit-pinning, (3) feed `hbase_of_framePairs`→`bumpTowerCarrier_all`, (4)
finite-cover extraction → `componentConv_covDeriv_of_chartCInf` → `metricPreconvInf`.
"No missing API" per the executor scout.  Then C-II-final discharges the gInf
scaffold (`MetricPreconvBridge.lean`) → `SourceMetricCPConvOnWindow`.

---

## 0. Mandatory reading before any edit

1. `CLAUDE.md` (repo root) — especially: lake-locked workflow, surgical
   changes, fail-loud, naming, same-name `.md` notes.
2. `DifferentialGeometry/Geometry/Flow/RicciFlow/HCGCompactness/MetricPreconv.md`
   — the full scouting record for this plan (routes, located bridges, the
   rejected alternative, the order-1 route in detail).  THIS plan and that
   note together are the spec.
3. `HCGCompactness/MetricCovDerivTimeDeriv.md` — the P2 tower machinery you
   will reuse, including its "Lean gotchas" section (smul elaboration,
   `respectTransparency`, def-unfold via `simp only [name]` not `rw`).
4. Skim: `HCGCompactness/MapConvergence.md` (the Euclidean AA engine you will
   consume — do NOT edit MapConvergence.lean; another agent owns that area),
   `HCGCompactness/ArzelaAscoli.md`.

## 1. Context (one paragraph)

The HCG chain (MSM135 Ch3): P1 (eq 3.3) ✅ and P2 (eq 3.4 structure,
`covOrderBound_of_soln` in `RicBound.lean`) ✅ produce, for a sequence of
pulled-back flow metrics `gSeq k t` against a background `gRef`, uniform
bounds `(B_r)`: `∀ r K compact, ∃ C, MetricCovDerivOrderBoundOnWindow K β ψ
gSeq gRef r C`, plus the time-derivative family `∂ₜ(∇ᵖg) = -2∇ᵖRc` with
uniform norm bounds.  P3 must convert these into a convergent subsequence:
spatial `C^∞`-on-compacts, uniformly in `t` on the window — the shape
`SourceMetricCPConvOnWindow` (PointedConvergence.lean:777) that the Thm 3.10
assembly (P4) consumes.  Deliberate deviation from the book (recorded in
MetricPreconv.md): NO `q ≥ 2` mixed time derivatives — the consumer does not
need them; `q = 1` supplies time equicontinuity.

## 2. Brick sequence

Work bricks IN ORDER; each brick = one focused session/subagent run.  After
each brick: focused check green → targeted build → update the same-name `.md`
→ commit (do NOT push).  If a brick fails 3 genuinely different routes on one
theorem, STOP and report per CLAUDE.md (theorem, goal, error, tried, suspected
obstruction) back to the planning session.

### Brick A1 — order-1 covariant→coordinate conversion ✅ DONE
**(2026-06-11, commit 5f1da4c3; ACCEPTED by planning session: sorry-free,
targeted build green, axiom-clean, quantifier discipline verified.  See
MetricPreconv.md for the as-implemented route + 7 new gotchas.)**
**File**: NEW `HCGCompactness/MetricPreconv.lean` (import: MetricCovDerivLinear,
MetricCovDerivTimeDeriv, Tensor0SRiemannian.Comparison, Bundle.PartialMfderiv.FixedBase,
AllTimesBounds; copy the HCG variable block from MetricCovDerivTimeDeriv.lean,
include `set_option backward.isDefEq.respectTransparency false`).

Target (shape may be adjusted, math content not):
```lean
/-- Chart-model first derivative of a tower-component scalar, bounded by the
next two covariant orders.  s_p^V(y) := (covDerivOfField gRef A0 p) y (V·y). -/
theorem fderiv_comp_le_tower
    (gRef : SmoothRiemannianMetric I M)
    (A0 : Tensor0SField 2) (p : ℕ)
    (V : Fin (p + 2) → ContMDiffSection I E ∞ (TangentSpace I))
    {x₀ : M} {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) :
    ∃ CV : ℝ, 0 ≤ CV ∧ ∀ y ∈ Kc, ∀ Cp Cp1 : ℝ,
      (∀ z ∈ Kc, √(normSq0S gRef z (p+2) (covDerivOfField gRef A0 p z)) ≤ Cp) →
      (∀ z ∈ Kc, √(normSq0S gRef z (p+3) (covDerivOfField gRef A0 (p+1) z)) ≤ Cp1) →
      ‖fderiv ℝ (writtenInExtChartAt I 𝓘(ℝ,ℝ) x₀
          (fun z => (covDerivOfField gRef A0 p) z (fun a => V a z)))
        (extChartAt I x₀ y)‖ ≤ CV * (Cp1 + Cp)
```
(`CV` collects gRef/chart/slot data only — k-independent when applied to a
metric SEQUENCE.  Restate freely, e.g. with the bound hypotheses before `∃ CV`;
keep the quantifier discipline: **constants before the varying field** — this
was the load-bearing lesson of the P2 `ric_bound` engine.)

Route (detailed in MetricPreconv.md "Order-1 route in detail"):
1. `‖fderiv F z‖` via a finite basis of directions `v` (finite-dim `E`;
   `‖L‖ ≤ Σ |L (b i)| * ‖coord i‖`-style, or `ContinuousLinearMap.opNorm_le_bound`
   with basis expansion of the argument).
2. Per direction: `extDerivFun_tangentConstInChart_eq_fderiv`
   (Bundle/PartialMfderiv/FixedBase.lean:69) — valid at every `y` in the chart
   source, NOT just the center.
3. Bump-globalize the chart-constant direction field (pattern:
   `Geometry/Connection/Realization/SmoothSectionsLocal.lean`;
   `extDerivFun_congr_nhds` says extDerivFun only sees the germ).
4. Step decomposition `totalNabla0SFun_apply_section` +
   `nabla0SFun_eval_smooth_slots` (exactly as in
   `MetricCovDerivTimeDeriv.lean`, `covDerivOfField_eval_smoothAt` — copy that
   theorem's hdec block) rewrites the directional derivative as
   `s_{p+1}` − Σ corrections.
5. Bound each term by `abs_apply_le_sqrt_normSq0S`
   (Tensor0SRiemannian/Comparison.lean, end of file) + sup of the slot/direction
   fields' gRef-norms on `Kc` (continuous on compact; `IsCompact.exists_bound`-style).

### Brick A2 — all-orders conversion (the induction) ✅ DONE
**(2026-06-11, commit 423b4e1a + constants-first FIX 39befdee; ACCEPTED:
sorry-free, targeted build green, axiom-clean.  Endpoint
`iteratedFDeriv_comp_le_tower`, FINAL SIGNATURE: `∃ CV, 0 ≤ CV ∧ ∀ A0, ∀ y ∈
Kc, ∀ b, … ≤ CV * ∑_{q ≤ p+r} b q` — `CV` precedes `∀ A0`, so it is
k-independent on a metric sequence.  Consumers must apply CV first, then the
field.  A1 (`fderiv_comp_le_tower`) keeps the per-`A0` shape — no consumers;
USE A2 (r = 1) instead.  Helpers exported for B: `towerStep`,
`fderiv_chartRep_eq_towerStep`, `contDiffAt_chartRep`,
`covDerivOfField_eval_contMDiff`, `writtenInExtChartAt_real_apply`.)**
**File**: same `MetricPreconv.lean`.

Target: for every `r`, `iteratedFDeriv ℝ r` of the chart representative of
`s_0^V = (A0 ·)(V·)` on an inner compact is bounded by a constant (chart/gRef/
slot data) times `max` of the covariant-order bounds `≤ r`.  Induction on `r`
with A1 as the step; the slot family grows by bump-globalized chart-constant
fields and Christoffel updates `∇_X V_a` (use
`TensorLieDeriv.covSection` — committed in
`Tensor/RSTensor/NablaOnTensors/Connection/Tangent.lean` — with
`leviCivitaConnectionOfMetric_contMDiffCovariantDerivative` from
`Geometry/Connection/LeviCivita/Smooth/Connection.lean`).
State the invariant for ALL ∞-section slot tuples with the constant depending
on the tuple's own data (MetricPreconv.md "Brick A refined design") — do NOT
try to keep a closed finite tuple family.
The `iteratedFDeriv (r+1) = fderiv of iteratedFDeriv r`-side: use
`iteratedFDeriv_succ_eq_comp_left`/`norm_iteratedFDeriv_fderiv`-style Mathlib
lemmas; if curry traffic explodes, the MapConvergence.md note records that the
Taylor-series field route (`ftaylorSeries.fderiv`) avoided curry rewriting —
reuse that trick.

### Brick B — chart-local extraction ✅ DONE (diagonal reassigned to C)
**(2026-06-11/12; ACCEPTED: foundation c3d7bc03+6c308e3f, producer chain
de3a2ace+bf8d994f+14fcbac1; sorry-free, targeted build green 3845 jobs,
endpoints `exists_chart_engineInput` + `exists_chart_cInfConv` axiom-clean.
Per-chart subsequence + C^∞ limit component delivered.  The atlas×component
diagonal was correctly identified as coupled to C's formulation and is
REASSIGNED to Brick C-I below — see the planner ruling.)**

**File**: same `MetricPreconv.lean`.

For a SEQUENCE `gSeq : ℕ → SmoothRiemannianMetric I M` with `(B_r)`-type
bounds (∀ r K ∃ C ∀ k — note quantifier order!), produce on each chart ball:
bump-extended component functions `Φ k : E → ℝ` (n² components per chart),
`ContDiff ⊤` ✓, all-orders compact bounds ✓ (Brick A2) → feed
`exists_cInf_subseq` (MapConvergence.lean:254) → subsequence + `ContDiff ⊤`
limits + `MapCInfConvOnCompacts`.  Then the standard diagonal: countable atlas
(σ-compact M: `exists` countable chart cover — if no in-tree lemma, take the
charts at a dense sequence; check `SigmaCompactSpace` API) × n² components ×
one subsequence via `Filter`-free explicit diagonal (the AA file's
`arzelaAscoli_subseq_*` proofs contain the extraction pattern — mimic).

### PLANNER RULING (2026-06-12): B↔C boundary

Brick B ends at the per-chart endpoint `exists_chart_cInfConv` (DONE).  The
atlas×component diagonal is REASSIGNED to Brick C (the executor's analysis is
accepted: the diagonal's stability hypotheses are dictated by C's convergence
formulation, and the global limit object is C1 — one design unit).  Brick C is
split into two execution units:

### Brick C-I — countable diagonal + global limit object
**STATUS (2026-06-12): C0 ✅ ACCEPTED (a36b7933, `exists_diag_subseq` in
MetricPreconvDiag.lean, proved exactly as design-fixed; sorry-free, build
green, axiom-clean).  C1a/C1b ✅ ACCEPTED (5656ee51,
`metricPreconv_gInf` in MetricPreconvDiag.lean; sorry-free, targeted build
green 3848 jobs, axiom-clean).  The live tree already contains the C1a/C1b
brick, so the earlier "dispatch C1a/C1b" kickoff request is superseded.  C-II
final still has to turn the pointwise `gInf` limit plus the scaffold hypotheses
into the final `MetricCInfConvOnCompacts` / window input.  C-II-final-B0 ✅
ACCEPTED (c2510190): `exists_engine_frameCInfConv` and
`exists_engine_frameCInfConv_eq_gm` re-expose the engine's order-0
C∞-on-compacts frame-component convergence and pin its limit to `gm`; targeted
build green 3848 jobs, axiom-clean.  C-II-final-B1 ✅ ACCEPTED (61584c6e):
`componentConv_covDeriv_zero` proves the covariant-tower component bridge at
order `a = 0` in any fibre basis; targeted build green 3848 jobs, axiom-clean.
C-II-final-B2 ✅ ACCEPTED (33d34fb7): `MapCInfConvOnCompacts.fderivApply` gives
the reusable derivative-closure of the Euclidean `C∞`-on-compacts convergence
notion; targeted build green 2323 jobs, axiom-clean.  Producer-(2) / tower
recursion ✅ ACCEPTED (1fd3844c, c83af74f, 01ba8309, f2402e95):
`Tensor.Coordinates.nabla0SFun_eval_coordFrame` proves the rank-general
coordinate covariant-step component formula; `metricCovDeriv_succ_apply_section`,
`metricCovDeriv_succ_component_coordFrame`, and the preferred section recursion
`metricCovDeriv_succ_eval_smooth_slots` specialise it to the metric covariant
tower; targeted builds green 3440/3629 jobs, axiom-clean.  ComponentConvTower
foundation ✅ ACCEPTED (6cded1f2, 20f88d78, c861bc7b, ff6cf674):
`MapCInfConvOnCompacts.congr` supplies locality; `chartRep_towerScalar_contDiffOn`
and `bumpTowerScalar_contDiff` supply global smooth carriers; `bumpFderiv_eq_chartTowerStep`
and `bumpTowerStep_chartConv` close the directional convergence step using the
existing A2 `fderiv_chartRep_eq_towerStep` germ identity plus B2.  Targeted build
green 3847 jobs, axiom-clean.  ComponentConvTower induction ✅ ACCEPTED
(57412cb9, 73f46522, 3ef86455, 1f4926a1, 0473472d, 45034b41, 70726247;
notes b4e4eaf9/1a5100a7): `bumpTower_slotExpand_conv`,
`MapCInfConvOnCompacts.sub`, `bumpTowerStep_split`,
`bumpTowerStepScalar_contDiff`, `bumpTowerCons_conv`, `bumpTowerCarrier_step`,
and `bumpTowerCarrier_all` prove the all-orders/all-section-tuples bump-carrier
convergence induction from an order-0 base.  Targeted build green 3854 jobs,
axiom-clean; planner cleanup locally scopes the one uniform-context
unused-variable linter warning in `bumpTower_slotExpand_conv`.  Frame data +
base reduction ✅ ACCEPTED (8b3bcc87, 2d9b4a2b; note 9d1a4693):
`exists_frameData` resolves the `hspan` coefficient-smoothness risk using the
Mathlib local-frame coefficient API, and `hbase_of_framePairs` reduces the
order-0 base for arbitrary section pairs to the diagonalised frame-pair
convergence `hpairs`.**
**File**: `MetricPreconvDiag.lean`.

C0 (the abstract diagonal — design FIXED by the planner, prove as stated
modulo naming):
```lean
theorem exists_diag_subseq
    (P : ℕ → (ℕ → ℕ) → Prop)
    (hstep : ∀ n : ℕ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P n (φ ∘ ψ))
    (hsub : ∀ n : ℕ, ∀ φ ψ : ℕ → ℕ, StrictMono ψ → P n φ → P n (φ ∘ ψ))
    (hextend : ∀ n : ℕ, ∀ φ : ℕ → ℕ, ∀ m : ℕ,
      P n (fun k => φ (k + m)) → P n φ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n : ℕ, P n φ
```
Classical nested construction: refine per item via `hstep`, diagonal
`ψ k := φ_k k`; item `n` holds on the tail `k ≥ n` (a subsequence of `φ_n`,
via `hsub`), recover the full sequence by `hextend`.  NOTE the `hextend`
direction: tail-satisfaction implies full — convergence-type `P`
(`∀ε ∃k0 ∀k≥k0` shapes, `MapCPConvOn`/`MetricCPConvOn`) satisfies both
stabilities trivially.  Put C0 in the HCG layer (it is generic order/sequence
combinatorics; `extraction_forall_of_frequently` is the Mathlib building
block if useful, but the hand-rolled nested construction is acceptable).

C1a: countable atlas of a σ-compact manifold: countable compact exhaustion
(`SigmaCompactSpace`) + finite chart subcovers per compact → a countable
family of (chart, inner-compact) pairs covering `M`.
C1b: apply C0 over (charts × n² components) with `hstep :=
exists_chart_cInfConv` (its `(B_r)` inputs restrict to subsequences ✓) →
ONE subsequence, all chart-components converge; define the global limit
`(0,2)`-field from the limit components (overlap consistency = uniqueness of
pointwise limits); symmetry pointwise; positive-definiteness from the `hlow`
lower bound; package `gInf : SmoothRiemannianMetric I M` (check the
constructor's smoothness field shape FIRST; the limit components are
`ContDiff ⊤` from the engine).

### PLANNER RULING 2 (2026-06-12): the gInf packaging gate

C-I stopped correctly: the inverse-componentize bridge (chart-component
limits → `SmoothRiemannianMetric`) does not exist (confirmed: the project
documents `TensorL2 → SmoothRiemannianMetric` as "the gate, NOT available",
NonlinearitySpectral.lean:53).  Decision among the executor's three options:

- Option 2 (reformulate the limit object) REJECTED — `SourceDomainMetricData.
  limitMetric`/`metricPreconvInf` demand `SmoothRiemannianMetric`; these are
  ported stable interfaces (keep public adapters stable).
- **Option 1 ACCEPTED as the mainline**: build the bridge as a dedicated
  foundational brick (C-G below).  It is NOT a detour: mathematically it IS
  the "we have thus constructed a limit metric" sentence of the lbl351 proof,
  and it has a SECOND consumer — Ch4 Thm 3.9 (`metricCompactness`) must
  construct its limit metric the same way.
- **Option 3 ACCEPTED as the parallel scaffold for C-II only**: C-II's
  endpoints take `gInf` + component-convergence as hypotheses; when C-G
  lands, C1b discharges them.  C-G and C-II can run in PARALLEL.

### Brick C-G — the metric realization bridge ✅ DONE
**(2026-06-12, commit dc003c71; ACCEPTED: sorry-free, build green 2685 jobs,
`DifferentialGeometry.Geometry.smoothMetric_of_localCoeff` axiom-clean.
KEY: `isVonNBounded` was discharged by the EXISTING
`MetricExistence.posDef_isVonNBounded` — no new analytic input; only the
`contMDiff` field was real content (LocalFrame route, tangent-trivialization
symm-frame of `Module.finBasis`).  The C-I blocker's "inverse-componentize
bridge does not exist" was over-scoped: ~210 lines.  C1a/C1b are now accepted
via `metricPreconv_gInf`.
Acceptance note on %-reporting: keep "Lemma 3.11 endpoint = 0% (unstated)"
SEPARATE from its machinery (~70%); whole-HCG ~25-35% theorem-weighted.)**

### Brick C-G — original spec (kept for reference)
**File**: NEW, at the realization layer — suggest
`DifferentialGeometry/Geometry/Metric/SmoothMetricFromCoeff.lean` (NOT under
HCGCompactness; Thm 3.9 will import it too).

Target shape (pointwise data + local component smoothness ⇒ bundled metric;
do NOT put coordinate transformation laws in the bridge — the consumer
supplies the intrinsic pointwise object, well-definedness is the consumer's
limit-uniqueness):
```lean
theorem smoothMetric_of_localCoeff
    (inner : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsymm : ∀ x v w, inner x v w = inner x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < inner x v v)
    (hcoeff : ∀ x₀ : M, ∃ u ∈ 𝓝 x₀, ∀ i j,
      ContMDiffOn I 𝓘(ℝ,ℝ) ∞ (fun y => inner y (frame_u i y) (frame_u j y)) u)
      -- frame_u = the localFrame of a trivialization/chart at x₀; fix the
      -- exact phrasing against contMDiffOn_iff_localFrame_coeff
    : ∃ g : SmoothRiemannianMetric I M, ∀ x v w, g.inner x v w = inner x v w
```
Route: the `contMDiff` bundle-section field of `ContMDiffRiemannianMetric`
(Hom-bundle section) via Mathlib's LocalFrame criterion
(`contMDiffOn_iff_localFrame_coeff` / `IsLocalFrameOn.contMDiffOn_of_coeff` —
the CLAUDE.md local-coordinate route, valid for any VectorBundle, Hom bundles
included); `symm`/`pos` pointwise; the `isVonNBounded` field — CHECK Mathlib's
`ContMDiffRiemannianMetric` mk-helpers first (finite-dimensional fibres:
von Neumann bounded = metrically bounded; there may be a constructor that
derives it — if a genuinely new analytic input appears here, STOP and report).
First step for the executor: read `Mathlib/Geometry/Manifold/VectorBundle/
Riemannian.lean` constructor + any `.of_…` helpers BEFORE writing the
statement, and adjust the target shape to the cheapest faithful form.

### Brick C-II — norm bridge + the P3 endpoints
**(SCAFFOLD MODE per Ruling 2: endpoints parameterize
`gInf : SmoothRiemannianMetric I M` + component-convergence hypotheses;
C-G and C1b have landed; C-II-final must wire their outputs through these
scaffold endpoints.)**
**STATUS (2026-06-13): C-II scaffold ✅ ACCEPTED as proof-verified
(68a63a7f; targeted build green 3856 jobs; four endpoints axiom-clean:
`metricDerivNorm_le_compSq`, `metricCInfConvOnCompacts_of_normConv`,
`exists_subseq_hconv`, `windowPreconv_of_perTime`).  C-II-final-A ✅ ACCEPTED
(66c70d9a; targeted build green 3856 jobs; `metricDerivNorm_le_compSq_uniform`
and the specialization `metricDerivNorm_le_compSq` axiom-clean).  The
constants-first seam is closed: good-frame witnesses `basisE`, `u'`, and `Cu`
are now bound before `∀ gk gInf`, so they depend only on `gRef`, `a`, and `x`.**

**NEXT FRONTIER (C-II-final-B, theorem boundary inputs):** the `Nat.rec`
covariant-tower convergence induction is closed as `bumpTowerCarrier_all`, frame
data is closed as `exists_frameData`, and the base algebraic reduction is closed
as `hbase_of_framePairs`.  `componentConv_covDeriv_of_chartCInf` is still not
stated/proved.  It now needs two concrete boundary inputs: (1) the B0 diagonal
producing `hpairs`, i.e. diagonalise `exists_engine_frameCInfConv` over the
`n²` frame pairs into one subsequence `φ`, with `A0Seq k = metricTensorField
(gSeq (φ k))` and the B0 bump data aligned; and (2) pointwise extraction from
order-0 `C∞` convergence plus a fixed multilinear basis-vector expansion to the
`component0S b (metricCovDeriv …)` shape.  The smallest next target is the B0
diagonal to `hpairs`; do not claim `componentConv_covDeriv_of_chartCInf` until
`hpairs`, extraction, and the final theorem all check.**
**File**: same or split `MetricPreconvBridge.lean` if > ~900 lines.

C2: component convergence ⇒ `MetricCPConvOn K hK p (gSeq∘φ) gInf gRef`
(PointedConvergence.lean:425; norm = `metricDerivNorm` of the DIFFERENCE
tower).  Bridge: `metricCovDeriv`/`covDerivOfField` is LINEAR in the field
(`MetricCovDerivLinear.lean`), so the difference tower = tower of the
difference; then the two-sided component↔normSq0S bounds
(`RicBoundGoodFrame.lean`: `exists_goodFrame_compBound`,
`sqrt_tower_le_compL2`, `compL2_tower_le`) convert sup-component differences
to `metricDerivNorm` differences.  Endpoint:
```lean
theorem metricPreconvInf ... :
    ∃ φ, StrictMono φ ∧ ∃ gInf : SmoothRiemannianMetric I M,
      MetricCInfConvOnCompacts (I := I) (fun k => gSeq (φ k)) gInf gRef
```

### Brick D — window-uniform time upgrade ✅ DONE
**(2026-06-12, commit ee9d8ab0; ACCEPTED: sorry-free, targeted build green,
both endpoints axiom-clean.  `windowPreconv` = the 3ε upgrade, conclusion
verbatim in `SourceMetricCPConvOnWindow` quantifier shape;
`timeLipschitz_of_hasDerivAt` consumes verbatim the `hevComp_of_solutions`
output shape (P2→D interface exact).  The abstract `hconv`/`hgLip`/`hInfLip`
boundaries are Brick C's wiring: dense-time diagonal → hconv; P2
`ric_bound_field`+(B_a) → the Ev-bound → hgLip; limit continuity → hInfLip.
Reusable: ℓ²-triangle/vector-MVT lemmas, `metricDerivNorm_triangle`,
`metricDerivNormSupOn_le_of_forall`.  See WindowPreconv.md.)**

**File**: NEW `HCGCompactness/WindowPreconv.lean`.

Inputs: `gSeq : ℕ → ℝ → SmoothRiemannianMetric I M`, window `[β,ψ]`, the
`(B_r)`-window bounds (P2 output `covOrderBound_of_soln` shape), and the
q = 1 time-derivative family
(`hevComp_of_solutions` output: `HasDerivAt (fun r => metricCovDeriv (gSeq k r)
gRef p x v) (((-2)•nablaRicReal ...) v) s`) with its norm bound (from
`ric_bound_field` + `(B_p)`).  Steps:
1. Time-Lipschitz of `t ↦ component/metricDerivNorm` from the q=1 bound (MVT
   on ℝ — scalar, easy).
2. Countable dense time set `T ⊆ [β,ψ]`; per `t ∈ T` apply `metricPreconvInf`;
   diagonal over `T`.
3. Equicontinuity in `t` upgrades pointwise-in-`T` convergence to uniform on
   `[β,ψ]` (classical 3ε; the limit family `gInf t` extends continuously to
   all `t` — define `gInf t` for all `t` as the limit, continuity from the
   uniform Lipschitz bound).
Endpoint: the window analogue of `MetricCInfConvOnCompacts` with
`∀ t ∈ Icc` uniform — match `SourceMetricCPConvOnWindow`'s quantifier shape
(ε first, then `k0`, then `∀ t ∈ Icc`) so P4 can consume it directly.

### NOT in P3 scope
- `hShi` realization (BBS track — ANOTHER ACTIVE SESSION owns
  StarSum2/Multilinear; do not touch).
- The `PointedCGHMaps`/pullback layer (P4).
- The q ≥ 2 mixed bounds (deliberately skipped).

## 3. Coordination rules (multi-agent, CRITICAL)

- ALL lake operations via `./scripts/lake-locked.ps1` (claim → check →
  targeted build → release).  NEVER bare `lake`.
- Files currently owned by the OTHER session (do not edit, do not claim):
  `MapConvergence.lean`, `IsometryCompactness.lean`, `Lemma45*.lean`,
  `ApproxIsometry*.lean`, `StarSum2.lean`, `Tensor/Multilinear/Tensor.lean`,
  `DomDomCongrSection.lean`, `CovariantDerivativeAlong.lean` (check
  `./scripts/lake-locked.ps1 status` before claiming anything).
- Check `git status --short` at session start; only stage YOUR files when
  committing; never push (the user pushes).
- If a needed upstream olean is missing/stale mid-build because of the other
  session, wait and retry — do not force-release their locks.

## 4. Known traps (cost real time in P1/P2; do not rediscover)

- `set_option backward.isDefEq.respectTransparency false` is REQUIRED
  (file-level) for Tensor0SField smul/coe_smul elaboration.
- Section-level `c • field` under application: pin with a named def
  (HSMul metavariable trap).
- Unfold project defs with `simp only [defName]` (equation lemma), never
  `rw [defName]`.
- Reindex/`domDomCongr` value identification: `show`-cast into the
  `ContinuousMultilinearMap.domDomCongr (...) (... x)` form (precedent
  `metricCovDerivNorm_eq_iterCov`), simp with `domDomCongr_apply` does NOT fire.
- Namespaces: `contMDiffAt_localFrame_coeff` is ROOT (not
  `Bundle.Trivialization.…`); `prod_mem_nhds` is root; inside
  `DifferentialGeometry.HCGCompactness` a bare `Trivialization.foo` may
  resolve via `open Bundle` — use `_root_.` when unsure.
- `∞ + 1 = ∞` via `ENat.coe_top_add_one`; `(2 : WithTop ℕ∞) ≤ ∞` via
  `WithTop.coe_le_coe.2 (le_top : (2:ℕ∞) ≤ ⊤)`.
- Renames: `abs_add`→`abs_add_le`, `pow_le_pow_left`→`pow_le_pow_left₀`,
  `Function.update_of_ne` (not `update_noteq`).
- Stale oleans: after ANY signature change upstream, targeted-build it before
  checking downstream (`lake env lean` reads oleans only).
- Heartbeat blowups on giant calc terms → `set` small abbreviations.

## 5. Acceptance criteria (per brick)

- **Constants-first, STRICT form** (lesson from the A2 fix 39befdee): a
  uniform constant must be `∃`-bound BEFORE every parameter that varies along
  the sequence — INCLUDING the theorem's own outer parameters.
  `(A0 : Field) → ∃ C, …` is WRONG for sequence use even when the proof's
  `C` is morally `A0`-independent: after `choose`, `C` is a function of `A0`.
  The correct shape is `∃ C, ∀ A0, …`.  Check every `∃`-statement against
  this before accepting.

- Focused check green; targeted build of the new module green; no new `sorry`
  (an honest precisely-stated `sorry` is acceptable ONLY with a frontier note
  in the `.md` and explicit report).
- `#print axioms` clean on the brick endpoint (propext/Classical.choice/
  Quot.sound only) when the brick claims "proved".
- Same-name `.md` updated: what was proved, what was reused, exact blocker if
  failed.  No verification logs in the note.
- Report back with honest nested %: brick % → P3 % → Lemma 3.11 % → HCG %.
