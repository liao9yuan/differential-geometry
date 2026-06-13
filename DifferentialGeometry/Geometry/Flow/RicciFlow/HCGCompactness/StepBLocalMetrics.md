# StepBLocalMetrics.lean — B-metric local metric limits (`lbl394` metric part, 2026-06-13)

## Status: generic theorem COMPLETE; HCG `β`-wrapper deferred on two named B-input gaps

**Verification PASSED**: focused check + targeted build green (no warnings); axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`) for `exists_metricLimit_on`.

## Delivered
- `exists_metricLimit_on` — generic model-coordinate local metric limit. From
  `IsOpen U`, `∀k ContDiffOn ℝ ⊤ (gLoc k) U`, derivative bounds on compacts ⊆ `U`
  (constants before `k`), and per-`k` uniform equivalence `½‖v‖² ≤ gₖ(z)(v,v) ≤ 2‖v‖²`,
  produces a subsequence `φ`, a limit `gInf`, `ContDiffOn ℝ ⊤ gInf U`,
  `MapCInfConvOnCompacts U (gLoc∘φ) gInf`, and the **retained** equivalence
  `½‖v‖² ≤ gInf(z)(v,v) ≤ 2‖v‖²` on `U` (so `gInf` is positive definite there).
  Proof: `exists_cInf_subseq_on` for the convergence; the equivalence passes to the
  pointwise limit (`tendsto_of_cInf`, evaluation continuity `fun_prop`,
  `ge_of_tendsto`/`le_of_tendsto`). Target `E →L[ℝ] E →L[ℝ] ℝ` is finite-dim
  automatically (no `InnerProductSpace E` in scope, so no slow synthesis).

## HCG `β`-indexed wrapper — deferred, with the exact missing inputs

The book sequence is `gLoc k = normalCoordMetric (X.obj k) (c k)` for a per-`k` chart
center `c k : (X.obj k).M` (same `β`, different manifolds `M_k`), on the **fixed** ball
`vec E^β`. Wiring `NormalCoordMetricBoundInput` (B-input) into `exists_metricLimit_on`
needs two facts the current input does NOT provide — neither should be faked:

1. **Smoothness.** `exists_metricLimit_on` needs `∀ k, ContDiffOn ℝ ⊤ (normalCoordMetric
   (X.obj k) (c k)) U`. `NormalCoordMetricBoundInput` has only derivative *bounds*, no
   `ContDiffOn` field. Worse, the realized `expMapDiffeo` is a `PartialDiffeomorph … 1`
   (only `C^1`), so even proving the field is real work (the metric pullback is `C^∞`
   mathematically, but the realized normal-coordinate API exposes `C^1`). **Smallest
   fix:** add a `metric_smooth : ∀ k x, ContDiffOn ℝ ⊤ (normalCoordMetric (X.obj k) x)
   (ball 0 (radius k x))` field to `NormalCoordMetricBoundInput` (honest book-external),
   OR upgrade the normal-coordinate `expMapDiffeo` API to `C^∞`.
2. **Uniform radius.** `exists_metricLimit_on`'s `U` is fixed across `k`, but the input's
   `radius k (c k)` is per-`k`. Need `∃ R > 0, ∀ k, Metric.ball 0 R ⊆ ball 0 (radius k
   (c k))`, i.e. a uniform lower bound on the radii (the book's `vec E^β` has a fixed
   radius `205 e^{20cC} λ^α`). **Smallest fix:** a `radius_lb` field or a Step-A lemma
   giving the uniform `R`.

Both are Step-A / B-input follow-ups (the planner's "full Step-A β wiring is too much"
clause). The generic engine is ready to consume them the moment they exist.

## Next
The `β`-wrapper is a thin application once (1) and (2) land. B-trans (`StepBTransition`)
has the same `C^1`-vs-`C^∞` smoothness dependency for `normalTransition`.

## HCG wrapper DELIVERED by honest exposure (2026-06-13, frontier-1 push)

`exists_metricLimit_normalCoord` (new `section HCGNormalCoord`) wires
`NormalCoordMetricBoundInput` + `c : ∀ k, (X.obj k).M` into `exists_metricLimit_on`.
**Verification PASSED** (focused check + targeted build green; axiom-clean
`[propext, Classical.choice, Quot.sound]`). Fixed-`β` only (one center sequence), NOT
the finite diagonal over all `β`.

The two frontier-1 facts are **honestly exposed as explicit hypotheses** (bare
statements, not renamed predicates), per the planner's "proving OR honestly exposing"
clause:
- `hsmooth : ∀ k, ContDiffOn ℝ ⊤ (normalCoordMetric (X.obj k) (c k)) U` — the genuine
  smoothness; blocked on the foundational gap below.
- `hdom : ∀ k, U ⊆ ball 0 (input.radius k (c k))` — uniform domain containment.

The bound side uses `input.metric_deriv` (with `M = input.metricC r`) and `metric_equiv`
directly; the slow nested-CLM synthesis under `InnerProductSpace E` needs
`set_option synthInstance.maxHeartbeats 800000` (scoped). The wrapper is a thin, honest
application — the moment a `ContDiffOn ⊤` producer for `normalCoordMetric` lands, B-metric
completes for a fixed `β`.

### Frontier-1 root gap (audited 2026-06-13)
`normalCoordMetric` is a pullback via `mfderiv (expMapDiffeo)`. The forward exp has only
`expMap_contMDiffAtN_of_norm_lt` (per-order `C^n`, radius `δ_n` **depends on `n`** via
`exists_unified_chartFlow_data_nat … n`) and `expMap_contMDiffAt_zero` (`C^1` at `0`). No
single-radius `ContMDiffOn ⊤` exists. The exact missing **foundational** theorem
(already flagged in `JacobiVariation.md:172`): `expMap` is `ContMDiffAt ∞` on a *uniform*
small ball ("the per-`N` radius is a construction artifact — bigger"). That unblocks
`expMapDiffeo : PartialDiffeomorph … ∞`, the inverse chart `C∞`, and both `normalCoordMetric`
/ `normalTransition` smoothness.
