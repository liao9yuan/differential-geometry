# MetricPreconvBridge.lean — P3 Brick C-II (SCAFFOLD MODE)

**Status (2026-06-12): IMPLEMENTED + verified — focused check + targeted build
green (3854 jobs); `#print axioms` clean = `[propext, Classical.choice,
Quot.sound]` on all four endpoints.**

Scaffold mode per `P3_PLAN.md` PLANNER RULING 2: the limit metric `gInf` is a
HYPOTHESIS (its construction is the foundational brick C-G); C-II's endpoints are
parameterized by `gInf : SmoothRiemannianMetric I M` (or `ℝ → SmoothRiemannianMetric`
for the window) plus component / per-time convergence hypotheses.  When C-G + C1b
land, C1b discharges those hypotheses.

Does NOT edit `MetricPreconv.lean` or `WindowPreconv.lean` (both imported, not
touched).

## What's proved (all sorry-free, axiom-clean)

### `metricDerivNorm_le_compSq` — C2 norm bridge (local)
At a good-frame patch around `x` (the `exists_goodFrame_compBound` output,
`RicBoundGoodFrame.lean`), for any two metrics `gk, gInf`:
```
∃ basisE u' Cu, IsOpen u' ∧ x ∈ u' ∧ u' ⊆ baseSet ∧ 1 ≤ Cu ∧
  ∀ z ∈ u', ∀ hz : z ∈ baseSet,
    metricDerivNorm a gk gInf gRef z ≤
      Cu * √(∑ I0, (component0S (localFrame z) (metricCovDeriv gk gRef a z) I0
                  - component0S (localFrame z) (metricCovDeriv gInf gRef a z) I0)^2)
```
with `Cu = ((3/2)(dim E + 1))^(a+2)`.  Route: the reverse two-sided bound of
`exists_goodFrame_compBound` (`normSq0S ≤ C^s · Σ component0S²`) applied at
`s = a+2`, `A = metricDiffCovDerivAt a gk gInf gRef z`; `√(C^s·Σ) = √(C^s)·√Σ ≤
C^s·√Σ` (since `C^s ≥ 1`); and `component0S` is additive over the fibre subtraction
defining `metricDiffCovDerivAt` (the per-metric difference form — proved by `rfl`,
this is the "MetricCovDerivLinear/component-additivity" content the plan named).

This is the genuine "sup-component differences → metricDerivNorm differences"
content.  C1b applies it on a FINITE good-frame cover of a compact `K` (same
pattern as `ric_bound`) to convert per-metric frame-component convergence (the
Arzelà–Ascoli engine output) into `metricCInfConvOnCompacts_of_normConv`'s
`hnorm` input.

### `metricCInfConvOnCompacts_of_normConv` — the spatial P3 endpoint (scaffolded)
```
(hnorm : ∀ p K, IsCompact K → ∀ ε>0, ∃ k0, ∀ k≥k0, ∀ a≤p, ∀ x∈K,
   metricDerivNorm a (gSeq k) gInf gRef x < ε)
 → MetricCInfConvOnCompacts gSeq gInf gRef
```
The `sSup` lift: control `metricDerivNormSupOn K p (gSeq k) gInf gRef` by `ε/2 < ε`
via `metricDerivNormSupOn_le_of_forall` (WindowPreconv).  This is the
`metricPreconvInf`-shaped spatial endpoint with `gInf` supplied.

### `exists_subseq_hconv` — the dense-time diagonal wiring
```
(e : ℕ → ℝ)
(hstep : ∀ n φ, StrictMono φ → ∃ ψ, StrictMono ψ ∧
   ∀ ε>0, ∃ k0, ∀ k≥k0, ∀ a≤p, ∀ x∈K,
     metricDerivNorm a (gSeq ((φ∘ψ) k) (e n)) (gInf (e n)) gRef x < ε)
 → ∃ φ, StrictMono φ ∧ ∀ n, ∀ ε>0, ∃ k0, ∀ k≥k0, ∀ a≤p, ∀ x∈K,
     metricDerivNorm a (gSeq (φ k) (e n)) (gInf (e n)) gRef x < ε
```
ONE subsequence along which spatial convergence holds at every dense time `e n`.
`hstep` is exactly the `exists_diag_subseq` (C0) refinement hypothesis; the
subsequence-stability (`hsub`, via `StrictMono.le_apply`) and tail-stability
(`hextend`, a `Nat` tail shift + `Nat.sub_add_cancel`) of the convergence property
are discharged inline; C0 does the diagonal.

### `windowPreconv_of_perTime` — the window capstone (interface check)
Composes `exists_subseq_hconv` with `windowPreconv` (Brick D, verbatim) for
`S = Set.range e`: from uniform time-Lipschitz of `gSeq`/`gInf` (`hgLip`/`hInfLip`),
a dense enumeration `e`, and the per-time refinable `hstep`, produces ONE
subsequence `φ` with window-uniform `C^p` convergence
(`metricDerivNormSupOn ... < ε`, `∀ t ∈ [β,ψ]`).  This TYPE-CHECKS my
`exists_subseq_hconv` output against `windowPreconv`'s EXACT `hconv` shape, so the
P3 assembly fits once C-G + C1b land.

## The hypothesis shapes I settled on (for the planner to validate against C-G + C1b)

1. **`metricDerivNorm_le_compSq` consumes nothing new** — it is a packaged
   consequence of `exists_goodFrame_compBound`.  Its OUTPUT is the per-patch
   inequality C1b uses; the per-metric frame-component `component0S (localFrame z)
   (metricCovDeriv g gRef a z)` is exactly what the Brick-B/AA engine converges
   (modulo the coordinate-frame ↔ trivialization-localFrame identification, which
   is C1b's responsibility — see boundary note below).

2. **`metricCInfConvOnCompacts_of_normConv` consumes** uniform-on-compacts pointwise
   `metricDerivNorm` convergence (`hnorm`).  C1b produces `hnorm` from a finite
   good-frame cover of `K` + `metricDerivNorm_le_compSq` + per-metric component
   convergence.

3. **`exists_subseq_hconv` / `windowPreconv_of_perTime` consume** the per-time
   REFINABLE spatial preconvergence `hstep` (`∀ n φ mono, ∃ ψ mono, [spatial conv
   of gSeq(φ∘ψ) at e n]`).  C1b supplies this: at each fixed time `e n`, the metric
   sequence `fun k => gSeq k (e n)` has the `(B_r)` bounds, so the per-chart AA
   extraction (`exists_chart_cInfConv`) refines any subsequence to a spatially
   convergent one — exactly the `hstep` shape.  The diagonal-over-times then comes
   for free from C0.

## Boundary left to C1b / C-G (NOT in this scaffold)
- Constructing `gInf` (the C-G inverse-componentize gate).
- The coordinate-frame ↔ trivialization-localFrame identification and the FINITE
  good-frame cover of a compact (to turn `metricDerivNorm_le_compSq` per-patch
  bounds + per-chart AA component convergence into the uniform-on-`K` `hnorm` of
  `metricCInfConvOnCompacts_of_normConv`, and the per-time `hstep`).  This is the
  same finite-cover pattern as `ric_bound`'s engine.
- The per-time `hstep` itself (the AA extraction at each dense time), which is C1b
  applied per time.

## Lean gotchas
- `component0S` of the fibre subtraction `metricDiffCovDerivAt = metricCovDeriv gk
  − metricCovDeriv gInf` splits as a difference of `component0S` by `rfl` (matches
  the WindowPreconv note: `component0S` add/sub are definitional).
- `exists_goodFrame_compBound`'s reverse bound takes args `z hz hzu' s A` with
  `hz : z ∈ baseSet` BEFORE `hzu' : z ∈ u'`.
- `hextend` (C0 `P`): `hk0 (k - m)` yields `metricDerivNorm a (gSeq ((fun k =>
  φ(k+m)) (k-m)) …)` — an UNREDUCED redex; `rw [k-m+m = k]` fails to match.  Fix:
  `simp only [Nat.sub_add_cancel (show m ≤ k by omega)] at hval` (simp beta-reduces
  first, then cancels).
- `StrictMono.le_apply : k ≤ ψ k` (implicit index) for the `hsub` reindex.

## Progress (honest, nested)
- C-II scaffold: **complete + verified** (4 endpoints, axiom-clean).  The genuine
  norm-bridge content (`metricDerivNorm_le_compSq`) + the spatial endpoint + the
  dense-time wiring + the verified compose with `windowPreconv`.
- P3 (metric preconvergence → `SourceMetricCPConvOnWindow`): A1✅ A2✅ B✅ D✅
  C0✅ C-II✅(scaffold).  REMAINING: C-G (gInf gate) + C1a/C1b (atlas + finite
  good-frame cover discharging C-II's hypotheses).  P3 ≈ 65% (the analytic engine
  is done; the foundational gInf gate + cover plumbing remain).
- Lemma 3.11 / Thm 3.10 input: P1✅ P2✅ P3 in progress → ≈ 75% when P3 lands.
- Whole HCG compactness project (MSM135 Ch3 + Ch4): ≈ 35–40%.
