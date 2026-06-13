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

### Frontier-1 root gap — corrected after ODE-layer audit (2026-06-13)

The `n`-dependent radius in the old finite-order route is real:

```
exp ContMDiffAt ⊤  ⟸  chart-flow Φ ContDiffOn ⊤ on a fixed ball
   (expMap_contMDiffAtN_of_norm_lt → contMDiffAt_infty)
chart-flow Φ ContDiffOn ⊤  ⟸  exists_chartPhase_…_combined_nat  [only the _nat form exists]
combined_nat radius  ⟸  exists_contDiffOn_flow_Cnat = flowCkPred_all n  [domain is n-DEPENDENT]
```

`exists_contDiffOn_flow_Cnat` (`VariationalMapContDiffOnK.lean`) is `flowCkPred_all n`, a
strong induction (`flowCkPred_base`=C¹ Picard–Lindelöf; `flowCkPred_step` via the augmented
flow `augVF`). `FlowCkPred n` returns an **existential** neighbourhood, and
`flowCkPred_step`'s box is built from the augmented flow's own IH neighbourhood — so this
route shrinks the domain with `n`.

However, the stronger fixed-box ODE theorem is already present and verified:

- `IsLocalFlow.contDiffOn_top`
  (`DifferentialGeometry/Analysis/ODE/Flow/HigherRegularity/ContDiffOnTop.lean`);
- `IsLocalFlow.contDiffOn_top_local`
  (`DifferentialGeometry/Analysis/ODE/Flow/HigherRegularity/ContDiffOnTopChartLocal.lean`).

Planner check passed for `ContDiffOnTop.lean`, and `#print axioms` for both the global and
local top-order flow theorems is clean (`propext`, `Classical.choice`, `Quot.sound` only).
So the next frontier is **not** a new linear-ODE smoothness theorem.  It is the wiring
frontier:

1. apply `IsLocalFlow.contDiffOn_top_local` to the geodesic chart-phase flow of
   `chartPhaseVF` on the existing nesting box;
2. package this as the missing `combined_inf` chart-flow theorem;
3. push through the existing off-zero bridge to obtain forward `expMap ContMDiffAt ∞` /
   `ContDiffOn ℝ ⊤` on a uniform ball.

The inverse `normalChartAt`/`expMapDiffeo : PartialDiffeomorph … ∞` upgrade remains the
next downstream inverse-function-theorem wiring step after the forward theorem lands.
