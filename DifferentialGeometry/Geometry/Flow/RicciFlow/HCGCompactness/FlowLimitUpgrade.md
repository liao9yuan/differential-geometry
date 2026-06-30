# FlowLimitUpgrade.lean — P4 assembly skeleton (MSM135 Thm 3.10 upgrade)

Plan: `C:\Users\liao9\.claude\plans\fluffy-coalescing-leaf.md`.

## Landed + verified (2026-06-17, axiom-clean, build green 3789 jobs)

- `FlowLimitData X mc` — bundles the P4 frontier ingredients given the time-zero
  conclusion `mc : MetricCompactnessConclusion (X.atZero)`: `L` (Brick A, limit
  flow), `maps` (Brick B), `scalar` (Brick E), `hσsrc`/`hσtgt`/`refMetric`
  (Brick C inputs), `conv` (Brick D, the window norm-bridge output).
- `flowLimit_upgrade` — PROVES the upgrade arrow: assembles `FlowLimitData`
  through the already-built `SmoothCGHConverges.ofRestrictPullback` →
  `CompactnessConclusion X`. **Brick F's core (correctly feeding the keystone
  constructor) is DONE.**
- `smoothFlowLimitInput_of_flowLimitData` — produces the theorem-facing
  `SmoothFlowLimitInput X` (previously assumed at 4 sites, never produced) from a
  per-`mc` `FlowLimitData` builder.

So the P4 assembly is verified; the previously-opaque `upgrade` is now a proved
theorem modulo the explicit honest frontier fields.

## The `FlowLimitData` builder (2026-06-21, axiom-clean, build green 3789 jobs)

`cghMaps_of_hL0 X mc L hL0 : PointedCGHMaps X L mc.subseq` — the **Brick-A →
Brick-B handoff** and the last missing producer of the `maps` field. Given the
limit flow `L` with `hL0 : L.atTime 0 = mc.limit` (Brick A's output contract),
the time-zero comparison maps `mc.maps` transport along `hL0.symm` to
`PointedRiemannianCGMaps (X.atZero) (L.atTime 0) mc.subseq`, which
`pointedCGHMaps_of_atZero` (Brick B) carries to the spacetime maps. The `▸`
transport is over the `L`-index of `PointedRiemannianCGMaps`; it introduces **no
axiom** (`#print axioms cghMaps_of_hL0 = [propext, Classical.choice,
Quot.sound]`, no `sorryAx`).

**Design decision (item #3 of the work list).** No verbose re-typed
`flowLimitData_of_…` wrapper was added. With `cghMaps_of_hL0` in hand,
`FlowLimitData`'s **own anonymous constructor IS the builder** — the structure-
instance syntax infers the frontier field types from the supplied `maps`:

```lean
flowLimit_upgrade X mc
  { L := L
    maps := cghMaps_of_hL0 X mc L hL0   -- Brick A+B, the only non-frontier field
    scalar := …      -- Brick E (honest frontier input)
    hσsrc := …; hσtgt := …; refMetric := …   -- Brick C inputs
    conv := … }      -- Brick D (honest frontier input, consumes hShi)
  : CompactnessConclusion X
```

A positional 5-argument builder would only restate the verbose field types and
duplicate `cghMaps_of_hL0 X mc L hL0` five times (CLAUDE.md: shortest correct
implementation, no redundant adapters). The honest frontier fields stay as
`FlowLimitData` fields (item #4), so the structure itself is the intended input
interface; `cghMaps_of_hL0` is the producer that makes it constructible.

## Remaining — discharge the `FlowLimitData` fields (the per-brick work)

- **Brick A** (`L`): the limit Ricci flow on `mc.limit.M` with metric `gInf`
  (Lemma 3.11 output) + `IsSolutionOn` (limit-is-a-solution — HARD). Build `L`
  so that `L.atTime 0 = mc.limit` (then Brick B's `rmaps := hL0 ▸ mc.maps`).
- **Brick B** (`maps`): ✅ DONE — `pointedCGHMaps_of_atZero` (2026-06-21, build
  green). **The feared manifold-type-identification wall does NOT exist**:
  `PointedFlowData.atTime` preserves `M`/topology/charted/basepoint
  *definitionally* (Basic.lean:72, only `metric` changes), so the time-0
  `PointedRiemannianCGMaps` over `L.atTime 0` transport field-for-field to
  `PointedCGHMaps X L subseq` by defeq — a 4-field copy, no casts. Consume it
  with `rmaps := hL0 ▸ mc.maps` where `hL0 : L.atTime 0 = mc.limit` (Brick A).
- **Brick C** (`hσsrc`/`hσtgt`/`refMetric`): σ-compactness of the open
  source/target + a reference metric. Mechanical.
- **Brick D** (`conv`): apply `winGInfOfSol` to the pulled-back flows `Φ_k* g_k`,
  bridge the source-domain `derivNormSupOn` to Lemma 3.11's `metricDerivNormSupOn`
  on `M_∞`. The keystone bridge; consumes `hShi` (honest input).
- **Brick E** (`scalar`): `ScalarPullbackTendsto` from `C^∞` metric convergence.

## ▶ RESUME HERE (paused 2026-06-21) — executing the approved `g_∞` plan

Approved plan: `C:\Users\liao9\.claude\plans\fluffy-coalescing-leaf.md` (the `g_∞`/`conv`/`L`
engine, Route 2 = bump-extend + AA once on `M_∞`). Execution order: P1.1→P1.2→P1.4→P1.3→P1.5,
then P2 (L+PDE), P3 (scalar+wiring).

DONE + verified (GREEN, sorry-free, axiom-clean):
- restriction-invariance: `metricDerivNorm_restrictOpen` + `metricDerivNormSupOn_restrictOpen`
  (`MetricDerivNormRestrict.lean`).
- **P1.1** `SmoothRiemannianMetric.convexComb` + `convexComb_inner` + `convexComb_eq_left_on`
  (NEW `Geometry/Metric/ConvexCombination.lean`).

**P1.2 DONE (2026-06-29, fixed + build-verified, 2941 jobs).** `SmoothRiemannianMetric.bumpExtendOpen`
+ `bumpExtendOpen_inner_of_mem` + `bumpExtendOpen_eq_gU_on` in `Geometry/Metric/BumpExtend.lean`
(`χ·(gU ext-by-0) + (1−χ)·R` total metric on `M`, via `smoothMetric_of_localCoeff` +
`ContMDiffOn.smul_section_of_tsupport`). NOTE: the file had been left BROKEN by a prior stale-lock
session (grep showed "0 sorry" but `lake build` revealed error-recovery sorries). Three bugs fixed:
(1) `extZeroForm`'s `dite (x∈U)` needed `Decidable (x∈U)` → added `open scoped Classical`;
(2) `bumpForm_symm` wrongly carried `omit [FiniteDimensional ℝ E]` (its proof needs FD via
`bumpForm_apply`) → removed; (3) `extZeroForm_of_mem` left an unclosed `X=X` (rw motive cast on the
dependent CLM/subtype-tangent type) → closed term-mode with
`DFunLike.congr_fun (DFunLike.congr_fun (dif_pos hx) v) w`. LESSON: a grep "0 sorry" on an untracked
file from a dead pid is NOT a green signal — always `lake build` before trusting it.

NEXT = **P1.4** (SolWindowData on `V=bump≡1` nbhd, Shi via P1.3 pullback-naturality), then **P1.3**
(Shi-tower pullback transfer — hardest, de-risked by `MetricCovDerivPullback.lean` bricks), **P1.5**
(conv bridge via restriction-invariance + sup corollary, `refMetric := restrictOpen R`, `gRef := R`).

## 3.10 ⇐ 3.9 wiring plan (CORRECTED SCOPE 2026-06-21 — follows MSM135 §lbl352)

The upgrade IS the book's "compactness for solutions from compactness for metrics"
(§lbl352). **BBS/Shi is a CITED input, not a proof obligation** — see
[[bbs-off-critical-path-310-from-39]]. Theorem 3.9 (lbl334) ASSUMES `|∇ᵖRm|≤Cₚ ∀p`;
the `|Rm|≤C₀ ⟹ |∇ᵖRm|≤Cₚ` bridge is cited (Shi, Thm lbl1118/1120). So `hShi`
(`MovingShiBoundOn`) and Theorem 3.9 (`metricCompactness`) enter as honest CITED inputs.

Book steps and their Lean status:
1. Theorem 3.9 at t=0 → maps Φ_k with Φ_k^*g_k(0)→g_∞ : **input** (`mc`).
2. Apply Lemma 3.11 + AA (lbl351) to Φ_k^*g_k(t) on M_∞ : `winGInfOfSol` — **DONE**.
   Output `WindowGInfOut`: `∃φ gInf, ∀ε ∃k0 ∀k≥k0 ∀t, metricDerivNormSupOn K p (gSeq(φk)t)(gInf t) gRef < ε`.
3. Assemble into solution convergence : `flowLimit_upgrade` — **DONE**.
4. "limit is a solution" : `ricci_continuous_in_metric_time` — **DONE** (one-sentence Ricci-continuity).

**THE ONE REMAINING FRONTIER = the norm bridge (old "Brick D"), now precisely pinned:**
`winGInfOfSol` gives the covariant norm for TOTAL metrics on M_∞; the `conv` field needs
it on the per-k SourceDomain SUBTYPE (Φ_k is a `PartialDiffeomorph`, so Φ_k^*g_k only
lives on the source `U_k`). Bridge = **restriction-invariance of `metricDerivNormSupOn`**:
the covariant metric-derivative norm is local ⇒ unchanged by `restrictOpen` to an open
submanifold. Building block: `covDerivAlong_restrict_eq_leviCivita`
(`Comparison/Variation/CovariantChainRule.lean:187`). NOT built at the norm level. This is
the only genuine missing lemma; the rest (`SolWindowData` for Φ_k^*g_k from the cited Shi
bounds, threading `hσsrc`/`hσtgt`/`refMetric`) is pullback bookkeeping.

Remaining work, in order: (a) `metricDerivNorm`/`metricDerivNormSupOn` restriction-invariance
lemma; (b) `SolWindowData` builder for the pulled-back flows (cited `hShi` → `H0`/`Hcov`/`Hlip`);
(c) `conv` producer = `winGInfOfData` ∘ (b) bridged by (a); (d) wire through `flowLimit_upgrade`.

### Progress + the conv-field frontier (2026-06-21)

- **(a) DONE, verified.** `metricDerivNorm_restrictOpen` (pointwise, via "Koszul is local":
  `OpenSubtypeNaturality.lean` bracket/Koszul/connection restriction) + **`metricDerivNormSupOn_restrictOpen`**
  (sup level, `MetricDerivNormRestrict.lean`). Both axiom-clean, targeted build green.

- **(c) is the genuine multi-session frontier (stuck, 3 routes).** The blocker: `derivNormSupOn`
  (PointedConvergence.lean:1424) = `metricDerivNormSupOn (sourceCompactSet Φ k K) p (pullbackMetric t)
  (limitMetric t)(referenceMetric t)`, where `ofRestrictPullback` fixes `limitMetric = restrictOpen(L.metric)`
  (✓ a restrictOpen) and `pullbackMetric = Diffeomorph.pullbackMetric (restrictOpen g_k)(sourceTargetDiff)`
  — a **pullback, NOT a restrictOpen**. So (a) bridges the limit/reference metrics but **not** the pullback
  metric. The covariant norm comparison of the *varying-manifold* pullbacks `Φ_k^* g_k` to the *fixed-limit*
  `gInf` requires bringing the pullbacks onto a common fixed manifold for the Arzelà–Ascoli. Three routes,
  all multi-session, no project shortcut:
  1. **sup-corollary direct** — FALSE: `pullbackMetric` is a `Diffeomorph.pullbackMetric`, the restriction
     tools don't touch it.
  2. **bump-extension to L.M** — define total `gSeq k = χ_k·(Φ_k^*g_k) + (1−χ_k)·gRef` via a compact
     exhaustion `C_k ⊆ source_k` (have `source_exhausts.subset`) + smooth bumps; then `restrictOpen(gSeq k)=
     pullbackMetric` on `C_k`, apply `winGInfOfData` + (a). **No metric-extension/convex-combination
     `SmoothRiemannianMetric` constructor exists** — the bundle-smoothness of `gSeq k` is the new work.
  3. **restrict-to-fixed-source + patch** — for each `K`, take `m` with `K ⊆ source_m`; for `k ≥ m`,
     `restrictOpen(pullbackMetric_k, source_m)` is total on `source_m`; run `winGInfOfSol` on `M := source_m`,
     bridge by (a), then patch the per-`m` limits into one `L.metric` (uniqueness of C^∞ limits). Needs
     `SolWindowData` on `source_m` for the restricted pullbacks + the L-consistency/patching.
  Route 3 avoids bump-smoothness (cleanest; the `k<m` truncation is handled by setting those terms to
  `restrictOpen(L.metric)`), but every route bottoms out at the SAME step: **assembling the single limit
  metric `g_∞ = L.metric` on all of `M_∞` from the per-source-domain Arzelà–Ascoli limits** (`winGInfOfSol`
  produces a limit *per domain*; identifying them as one global `g_∞` needs a global extension or a
  patching/uniqueness argument). That is exactly the book's **Step D** metric assembly ("these metrics form
  a Riemannian metric `g_∞` on `M_∞` via the coordinate charts", chapter4.tex:89–91 — glossed as "not hard
  to see"). So the 3.10⇐3.9 wire bottoms out NOT on BBS and NOT on new analysis (Lemma 3.11 + AA are done),
  but on the **`g_∞` assembly** — a genuine multi-session construction. STUCK here after 3 routes; recommend
  a dedicated session on Route 3 (restrict-to-`source_m` + winGInfOfSol-per-domain + patch via C^∞-limit
  uniqueness), reusing the now-complete `metricDerivNorm(SupOn)_restrictOpen`.

## Design notes

- `FlowLimitData` is parameterized by `mc` because `maps`/`conv`/`refMetric` all
  reference the limit manifold + subseq from `mc`. The fields use the
  `letI : … := L.topology / sourceDomTop maps k` instance pattern mirroring
  `SourceDomainMetricData.ofRestrictPullback`.
- Per the approved plan (scope = "frontiers as inputs"), `hShi` and the Thm-3.9
  conclusion stay honest inputs (`mc` is the Thm-3.9 conclusion; `hShi` enters
  Brick D's `winGInfOfSol` application).
- The user chose to EXPAND `SmoothFlowLimitInput` (vs the producer route); the
  full expand+rewire of `SolutionCompactness.lean`'s structure + 4 consumers is
  Brick F-final. For now `smoothFlowLimitInput_of_flowLimitData` bridges to the
  existing structure without touching consumers.
