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

### Frontier-1 root gap — FULL CHAIN TRACED (2026-06-13, frontier-1 attack)

The `n`-dependent radius is **not** an exp-layer artifact; it traces to an undischarged
ODE smooth-dependence input. Chain:

```
exp ContMDiffAt ⊤  ⟸  chart-flow Φ ContDiffOn ⊤ on a fixed ball
   (expMap_contMDiffAtN_of_norm_lt → contMDiffAt_infty)
chart-flow Φ ContDiffOn ⊤  ⟸  exists_chartPhase_…_combined_nat  [only the _nat form exists]
combined_nat radius  ⟸  exists_contDiffOn_flow_Cnat = flowCkPred_all n  [domain is n-DEPENDENT]
```

`exists_contDiffOn_flow_Cnat` (`VariationalMapContDiffOnK.lean`) is `flowCkPred_all n`, a
strong induction (`flowCkPred_base`=C¹ Picard–Lindelöf; `flowCkPred_step` via the augmented
flow `augVF`). `FlowCkPred n` returns an **existential** neighbourhood `U` (line 1813), and
`flowCkPred_step`'s box `ball x₀ ρ ×ˢ Ioo (t₀-T)(t₀+T)` is built from cap/nesting data that
depends on the augmented flow's own neighbourhood from the IH — so **the domain shrinks
with `n`**. The flow `Φ` itself is `n`-independent; only the proven-smooth domain shrinks.

The **C∞-on-a-fixed-box theorem already exists**: `exists_contDiffOn_flow_Cinfty`
(`VariationalMapContDiffOnK.lean:1956`) gives `ContDiffOn ℝ ∞ Φ U` on one fixed box — **but
it takes the hypothesis**
`hLsp : ∀ j, ContDiffOn ℝ j (spatialPieceFn Φ) (fixed nesting box)`
(the spatial piece of the flow's `fderiv` = variational linear map, smooth at every order
on ONE box). The authors' own docstring calls `hLsp` "the smooth-parameter-dependence
content of the variational linear ODE … the sole remaining mathematical input." Grep
confirms **`hLsp` is discharged nowhere** for any flow.

### THE EXACT MISSING THEOREM (foundational API frontier — hard stop)

> For the geodesic chart-phase flow `Φ` of `chartPhaseVF`, discharge
> `hLsp : ∀ j, ContDiffOn ℝ j (spatialPieceFn Φ)` on the **single fixed** nesting box from
> `exists_flow_nesting_data` — i.e. a **uniform-domain** all-orders smoothness for the
> variational/augmented flow (the existing `flowCkPred` induction gives only order-dependent
> shrinking neighbourhoods via the `augVF` recursion).

Mathematically true (the linear variational ODEs all live over one fixed base-flow domain
with bounded coefficients on a compact region), but it requires a genuinely new
uniform-domain ODE smooth-dependence argument, NOT a quick lemma. Once `hLsp` is proved for
`chartPhaseVF`, `exists_contDiffOn_flow_Cinfty` → a `combined_inf` chart-flow theorem →
`expMap ContMDiffAt ∞` on a uniform ball → `expMapDiffeo : PartialDiffeomorph … ∞` (+ the
`C∞` inverse function theorem for the inverse chart) → both wrappers' `hsmooth` discharge.
`exists_contDiffOn_flow_Cinfty` is the ready consumer; `hLsp` is the one blocking input.
