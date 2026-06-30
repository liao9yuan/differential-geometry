# StepBInputs.lean — Step B honest input (S6 / lbl418), native rebuild

## 2026-06-22 — added `C∞` normal chart inverse (section `NormalChartInftySmooth`)

`normalChartAt_contMDiffAt_infty` / `normalChartAt_contMDiffOn_infty`: the normal chart inverse
is `C∞` (was only `C¹`), via a fresh Banach IFT at `∞` on `extChartAt q ∘ expMap` (chart centred
at the image point `q`, so `extChartAt`-invertibility is at its centre via
`isInvertible_mfderiv_extChartAt`). The per-point equiv is taken from
`(fderiv ℝ (extChartAt q ∘ expMap) v₀).IsInvertible` (genuinely `E ≃L E`) to dodge the
`TangentSpace 𝓘(ℝ,E) (χ q) = E` defeq wall the `mfderiv`-composite hit in the `HasFDerivAt` slot.
Added `import …Comparison.ExpBallDiffeo` (for `exp_isLocalDiffeomorphOn_ball`). Consumed by
`StepBTransition.contDiffOn_normalTransition`. See `StepBTransition.md` (2026-06-22) for the full
route + soundness note (ball-`C∞` is off the ChainedFlowContinuity sorries).

2026-06-09. Rebuilt the S6 exp⁻¹-derivative honest input on the NATIVE
normal-coordinate API (`Geometry.Riemannian.NormalCoordinates.expMapDiffeo` /
`normalChartAt`), replacing the never-compiling `GeometricInputs.lean` section that
referenced the nonexistent `RicciFlower.Coordinates.NormalChartData`.

Contents (statement-level, no sorry):
- `normalTransition X x y : E → E` — `normalChart_y ∘ exp_x` (total; junk outside).
- `NormalTransitionDerivBound X x y p C` — `‖iteratedFDeriv p ...‖ ≤ C` on the chart
  overlap (z ∈ exp_x-source, image ∈ normalChart_y-source).
- `ExpInverseDerivBoundInput X` — the book-external Jacobi/Rauch input (`derivC`,
  nonneg, per-(k,p,x,y) bound). Verification passed.

`GeometricInputs.lean` is now a pure umbrella import (StepAInputs + StepBInputs);
the tree has no committed-broken file from this layer anymore.

## Step B audit corrections (2026-06-09)
- **B0 (book L1413, |∇ᵉRm| ≤ C ⟹ |∂ᵐ g| ≤ C̃ in normal coordinates) does NOT exist.**
  CHAPTER4_PLAN's "[x] = Lemma 3.11 (`MetricAllTimesConclusion`)" was a conflation
  with the TIME-window AllTimesBounds machinery. Spatial B0 is genuine remaining work
  (a per-chart elliptic/ODE estimate chain) and is B1's main missing producer.
- **Chart scale:** the native `expMapDiffeo` source is *some* open neighbourhood of 0
  (choice); `injRadius` API (`injOn_expMap_eball_of_lt_injRadius`) gives only
  INJECTIVITY on the eball, not "diffeo on the full λ-ball". Widening the chart to
  the λ-ball scale = the lbl383 item-3 frontier (inj + local diffeo ⟹ ball diffeo).

## Step B remaining map
B1 (`lbl397`) ⟸ B0 (missing, real work) + this input + item-3 chart-scale + lbl390
windows (done). B2/B3 analysis on top; B4 local-diffeo brick independent; B5/B6 gated
on the F3 engine interface (see Lemma45CovariantAbstract).

## B-input brick — `lbl395` normal-coordinate metric honest input (2026-06-13)

Added the `lbl395` honest input (STEPB_PLAN Planner Ruling Q1), sibling to
`ExpInverseDerivBoundInput`. **Verification PASSED** (focused locked check + targeted
module build green; sorry-free). Only definitions/predicates/a structure were added —
**no theorem endpoint was introduced**. Axiom audit on the one concrete `def` that
carries content, `normalCoordMetric`, is clean: `[propext, Classical.choice,
Quot.sound]` (the `Classical.choice` is inherited from `expMapDiffeo`'s
`Classical.choose`; no `sorryAx`).

### What was added (all in `StepBInputs.lean`)
- **`normalCoordMetric Y x : E → (E →L[ℝ] E →L[ℝ] ℝ)`** — the model-coordinate
  pulled-back normal-coordinate metric `(H_x)^* g`, where `H_x := expMapDiffeo g x`.
  Defined *concretely* (NOT as supplied chart-data) by mirroring
  `Geometry/Metric/Pullback.lean : Diffeomorph.pullbackInner`: at `z`,
  `(ContinuousLinearMap.precomp ℝ D).comp ((g.inner (H_x z)).comp D)` with
  `D := mfderiv 𝓘(ℝ,E) I H_x z`, so the value is the bilinear form
  `(u,v) ↦ g_{H_x z}(dH_x u, dH_x v)`. Off the chart domain `D` is junk; the bounds
  apply only on the relevant ball (parallel to `normalTransition`).
- **`NormalCoordMetricEquivOn Y x U`** — `½‖v‖² ≤ g(z)(v,v) ≤ 2‖v‖²` on `U`
  (quadratic-form form of `½δ ≤ g ≤ 2δ`).
- **`NormalCoordMetricDerivBound Y x U p C`** — `‖iteratedFDeriv ℝ p (normalCoordMetric
  Y x) z‖ ≤ C` on `U`.
- **`NormalCoordMetricBoundInput (X : PointedRiemannianSeq)`** — constants-first honest
  input: `metricC : ℕ → ℝ` (+ nonneg) listed first and uniform over `k,x`; per-center
  `radius` (the book `min{c₁/√C₀,r₀}` scale, `radius_pos`); `metric_equiv` and
  `metric_deriv` stated on `Metric.ball 0 (radius k x)` only.

### Design decisions (why this shape)
- **Concrete map, NOT a chart-data record.** STEPB_PLAN step 7 anticipated possibly
  needing a separate `H_k^α`/pulled-back-metric chart-data record. It was NOT needed:
  `Diffeomorph.pullbackInner` already establishes that `g.inner pt : TₚM →L TₚM →L ℝ`
  composes cleanly with `mfderiv` via `.comp`/`ContinuousLinearMap.precomp` (the
  `precomp` route avoids the `SeminormedAddCommGroup` instances `bilinearComp` would
  demand on `TangentSpace`). So `normalCoordMetric` is a genuine pullback, mirroring
  `normalTransition`. This keeps the honest input free of realization-hypothesis fields
  and gives B-metric a real bilinear-form-valued map to feed to (localized) AA.
- **Target = `E →L[ℝ] E →L[ℝ] ℝ`** (Q3's "equivalent continuous bilinear-form target"),
  reusing the project's canonical pullback-bilinear type rather than CMM currying.
- **No `radius_subset_source` / total-`univ` claim.** The B-input brick records exactly
  the local metric control Step B will consume; source containment/nested-domain
  bookkeeping belongs to the Step A item-3 data and the later B-loc bridge.
  `Set.univ`/`IsometryDerivBounds` is deliberately avoided (B-loc).
- `½` and `2` are hardcoded (the book gives exactly these); the dimensional gap between
  the operator-norm `‖iteratedFDeriv‖` and per-component `|∂^α g_ij|` is absorbed into
  the honest constant `metricC p`.

### Lean lesson
- `iteratedFDeriv ℝ p` over the nested `E →L[ℝ] E →L[ℝ] ℝ` codomain with
  `InnerProductSpace ℝ E` in scope blows the default `synthInstance` budget (20000 hb,
  `SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)`). It is slow-but-terminating; the project
  standard `set_option synthInstance.maxHeartbeats 800000` fixes it. Scope it to the one
  declaration (`NormalCoordMetricDerivBound`) — an unscoped top-level option trips the
  `linter.style.setOption` guard on a fresh build.

## B-metric smoothness producer - accepted 2026-06-13

`normalCoordMetric_contDiffOn` is now proved in `StepBInputs.lean`: for every pointed
Riemannian manifold `Y` and center `x`, there is a radius `delta > 0` such that
`normalCoordMetric Y x` is `ContDiffOn Real top` on
`Metric.ball 0 delta inter (expMapDiffeo Y.metric x).source`.

The proof closes the five planned geometry/bundle steps:

- `expMapDiffeo_contMDiffOn_ball` compares the C1 `PartialDiffeomorph` realization with
  the forward C-infinity `expMap` on the ball.
- `normalCoordMetric_apply` exposes scalar evaluation as
  `g_(H_x z) (dH_x z v) (dH_x z w)`.
- the private pushforward-section lemma uses
  `ContMDiffOn.contMDiffOn_tangentMapWithin` and a constant tangent section.
- `ContMDiffOn.clm_bundle_apply2` assembles the metric section with the two pushed-forward
  vectors.
- two `contDiffOn_clm_apply` reductions and `contMDiffOn_iff_contDiffOn` package the
  scalar entries as an `E ->L[Real] E ->L[Real] Real`-valued map.

Verification passed: focused locked check and targeted module build were green.  The
public axiom audit for `expMapDiffeo_contMDiffOn_ball`, `normalCoordMetric_apply`, and
`normalCoordMetric_contDiffOn` is `[propext, Classical.choice, Quot.sound]` only.

Impact: the B-metric smoothness hypothesis is no longer the frontier.  The remaining
fixed-center wrapper work is domain/radius bookkeeping: relate the existential
`delta_k` from `normalCoordMetric_contDiffOn` to the fixed model domain `U` used by
`exists_metricLimit_normalCoord`, using the Step-A fixed-scale/radius data.  That is a
uniform-domain input, not another smoothness theorem.

## 2026-06-13 (session 5): named-radius producers landed (axiom-clean, focused checks GREEN)

Now imports `GaussLemmaPullback` and opens `…Geometry.Riemannian` (for `expMapC2Radius` and
`mem_expMapDiffeo_source_of_norm_lt_radius`).

- Extracted the reusable core `normalCoordMetric_contDiffOn_of_smooth (hU : IsOpen S)
  (hf : expMapDiffeo C∞ on S) : ContDiffOn ⊤ (normalCoordMetric Y x) S`.  The opaque-radius
  `normalCoordMetric_contDiffOn` is now a 3-line specialization of it (no duplicated bundle proof).
- `expMapDiffeo_contMDiffOn_expBall` / `normalCoordMetric_contDiffOn_expBall`: smoothness on the
  **named** ball `Metric.ball 0 (expMapC2Radius Y.metric x)` (no `∩ source` — component 4 of
  `expMapC2Radius` absorbs it via `mem_expMapDiffeo_source_of_norm_lt_radius`; ∞-smoothness via the
  new `expMap_contMDiffAt_infty_of_norm_lt_radius`).  This is the radius anchoring that closes
  HARD-STOP #1 from `StepBLocalMetrics.md`.
- `contDiffOn_normalCoordMetric_of_subset_expBall`: reduces the `hsmooth` hypothesis of
  `exists_metricLimit_normalCoord` to the single containment `hsub : ∀ k, U ⊆ ball 0 (expMapC2Radius
  (X.obj k).metric (c k))` (via `.mono`).  `hsub`'s statement needs `letI` for `(X.obj k).M`'s
  instances since `expMapC2Radius` takes them as typeclass args (unlike `normalCoordMetric`, which
  bundles them internally — so its `∀ k …` conclusion needs no `letI`).

Remaining: the β-wrapper assembly in `StepBLocalMetrics.lean` (fixed `U`, `hdom`, feed `hsub` from
`Item3RadiusInput`'s `ρ ≤ expMapC2Radius`).  No smoothness/geometry frontier remains; gated only on the
honest-input `radius_lb` wiring.  Full detail in `StepBLocalMetrics.md` (session-5 UPDATE).
