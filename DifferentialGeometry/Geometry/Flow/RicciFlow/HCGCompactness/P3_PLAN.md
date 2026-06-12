# P3 EXECUTION PLAN — metric preconvergence + window upgrade (MSM135 lbl351 → 3.10 input)

**Audience: implementing agent (Opus session / subagent) with NO memory of the
planning session.  Written 2026-06-11 by the planning (Fable) session.**

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

### Brick B — chart-local extraction + diagonal
**STATUS (2026-06-11/12): foundation ACCEPTED (c3d7bc03 + 6c308e3f, sorry-free,
build green, axiom-clean): `bumpMul_contDiff`, `norm_iteratedFDeriv_bumpMul_le`
(`∀ i ≤ r` hypothesis shape — matches `exists_cInf_subseq.hbdd`).  ENDPOINT
NOT STATED (0%).  Remaining = the metric producer (~150-200 lines, route
fully scouted in MetricPreconv.md: nested Euclidean bumps, `gg_k :=
χ₁·(chart rep of (gSeq k).inner(E_i,E_j))`, `Φ_k := χ·gg_k`, Bg from the
FIXED A2 CV via `metricCovDeriv_eq_covDerivOfField` + the `(B_r)` hypothesis)
+ `exists_cInf_subseq` per chart/component + the atlas × n² diagonal.**

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

### Brick C — limit reassembly + norm bridge
**File**: same or split `MetricPreconvBridge.lean` if > ~900 lines.

C1: limit components → a global smooth `(0,2)`-field `gInf`; symmetry from
pointwise limits of symmetric; positive-definiteness from the lower bound
`hlow` (∃ δ > 0 per compact, from eq 3.3); package as
`SmoothRiemannianMetric I M`.  Check the constructor's fields first
(`SmoothRiemannianMetric` def) — if local-chart construction is awkward,
build the `Tensor0SField` first and add the metric structure.
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

### Brick D — window-uniform time upgrade
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
