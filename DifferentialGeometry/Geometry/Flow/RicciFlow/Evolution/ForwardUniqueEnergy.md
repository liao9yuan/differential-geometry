# ForwardUniqueEnergy.lean — Route-K brick K3 (moving triple-energy differentiation)

Companion note for
`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ForwardUniqueEnergy.lean`.
Governing ruling: `ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §5 (brick K3) and §3
(moving `g₁(t)` carrier).  Consumes `Evolution/ForwardUniqueFields.lean` (brick FIELDS).

## Status

Focused check: PASS.  Targeted module build: PASS (no warnings from this file).
Axiom audit: all 10 public declarations depend on exactly
`[propext, Classical.choice, Quot.sound]`.  Zero `sorry`.
The one honest open input is the joint-smoothness hypothesis `hdens` (see
"Regularity input for differentiating under the integral"); it is a hypothesis of the
endpoint, not a `sorry`.

## Scope

K3 does **no analytic estimation**.  Its four jobs, per the ruling:

1. differentiate the three pointwise moving norms `|h₀₂|²`, `|A₀₃|²`, `|S₀₄|²`;
2. differentiate the moving volume form;
3. differentiate under the compact integral;
4. assemble the exact rate.

Jobs 2 and 3 are *both* discharged by one green producer,
`DifferentialGeometry.Integral.Measure.first_var_joint`
(`Analysis/Integration/Measure/FamilyLocal.lean:223`).  Job 1 is the only genuinely new
mathematics in this file.

## Producers consumed (all from GREEN files)

* `Integral.Measure.first_var_joint` — differentiation under the moving-volume integral on an
  **open time window**.  It internally localizes the global `first_variation_of_volume`
  (`Analysis/Integration/Measure/Family.lean:1094`) with a smooth time retraction, so K3 does
  not have to supply the global-in-time `MetricFamilyRegularAt` / `FunctionRegularAt`
  packages.  This is what `MovingEdgeEnergy.movingEnergy_deriv` consumes as well.
* `Integral.Measure.riemannianMeasureFamily`, `Integral.Measure.traceTimeDerivMetric`,
  `Integral.Measure.chartGramMatrix` — the moving measure, the volume-variation scalar
  `½ tr_g(∂ₜg)`, and the chart-Gram regularity currency.
* `Tensor0SBundle.hasDerivWithinAt_normSq0S_ricciFlow`
  (`Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean:828`) — the rank-uniform
  component-level moving-norm product rule.  Also `basisInv_time`, `basisInvMetric_real`,
  `basisInvMetric_symm`, `ricReactionContract`, `tensor0SComponent`, `normSq0S`, `inner0S`
  from the same layer.
* `metricRicciAt` (`Geometry/Curvature/Metric.lean:87`, `PDE.RicciFlow` abbrev in
  `Basic/Core.lean:126`) — the canonical `(0,2)` Ricci **fiber tensor**.
* `ForwardUniqueFields`: `metricDiffAt`/`connDiffLowAt`/`rmDiffLowAt` and
  `metricDiffSq`/`connDiffSq`/`rmDiffSq`.

`Analysis/Spectral/Intrinsic/DeTurck/MovingEdgeEnergy.lean` was read as **design evidence
only** and is not imported.  It is genuinely un-compilable in its current state: 16 of its
`ContMDiffOn` hypotheses spell the model-with-corners notation with `U+1D4B0` (`𝒰`,
script capital U) instead of `U+1D4D8` (`𝓘`).  Anyone reviving that file must fix that first.

## Design decisions

### Why `Q : Tensor0SSpace 2` and not the CLM `ricciTensor`

`Integral.Connection.ricciTensor` (`Curvature/CurvatureOperator/RicciConnection.lean:221`)
sits in a section carrying `[InnerProductSpace ℝ E]`, `[NeZero (Module.finrank ℝ E)]`,
`[BoundarylessManifold I M]`.  Consuming it would drag the known-wrong model-space
`InnerProductSpace ℝ E` into every K3/K4 consumer (the same trap recorded as dedup item 1 in
`ForwardUniqueFields.md`).  `metricRicciAt` lives on the plain-`NormedSpace` block that
`ForwardUniqueFields` already uses, and it is already a `Tensor0SSpace 2 I x`, which is
exactly the shape the reaction contraction wants.  **Rule of thumb for this lane: reach for
`Geometry/Curvature/Metric.lean` names, not `CurvatureOperator/RicciConnection.lean` names.**

### The rank-uniform moving norm derivative

`hasDerivWithinAt_normSq0S_ricciFlow` is already rank-uniform but is stated with component
arrays, a chosen basis, an inverse-metric component family and its time derivative.  The
`(0,2)`-only invariant repackaging `movingNorm_time` exists in the broken `MovingEdgeEnergy`
file.  This file re-derives the **rank-`s`** invariant form directly from the green producer:

* `movingReact0S g x s Q W` — the metric-variation term, in the canonical `Module.finBasis`;
* `normSq0S_moving_deriv` — `∂ₜ|T|²_{g} = movingReact0S(g,Q,T) + 2⟪∂ₜT, T⟫_g` when `∂ₜg = −2Q`.

Ranks `2`, `3`, `4` are then three instantiations with the *same* carrier speed `Q = Ric₁`.
Basis independence is not proved separately: `normSq0S_moving_deriv` exhibits
`movingReact0S` as a genuine derivative, so uniqueness of derivatives gives it for free (the
`reactInBasis_eq` argument in the design evidence).

**Layering caveat for the planner.** `movingReact0S` + `normSq0S_moving_deriv` are generic
tensor facts with no Ricci-flow content; their canonical home is
`Tensor/RSTensor/FiberMetric/Tensor0SMetricDeriv.lean`, not this Ricci-flow file.  They live
here only because this brick was scoped to one new file.  Moving them up is a cheap,
mechanical follow-up, and it would also let the broken `MovingEdgeEnergy.movingNorm_time` /
`movingMetricReact` be replaced by the `s = 2` instance instead of a parallel API.

### Hypothesis shape for the `A₀₃` / `S₀₄` speeds — the resolved fork

Only `h₀₂`'s speed is determined by the metric equations:
`∂ₜh₀₂ = −2(Ric₁ − Ric₂)`, so `metricDiffDot` is a **`def`**, proved correct by
`metricDiff_hasDerivAt` from the two Ricci-flow `HasDerivAt`s.  `∂ₜA₀₃` and `∂ₜS₀₄` are the
K1 and K2 outputs and cannot be produced here.  They enter as *plain `∀`-quantified*
arguments — no new predicate class:

```lean
(Adot : ℝ → (x : M) → Tensor0SSpace 3 I x)
(Sdot : ℝ → (x : M) → Tensor0SSpace 4 I x)
(hA : ∀ (x : M) (v : Fin 3 → TangentSpace I x),
   HasDerivAt (fun r : ℝ => connDiffLowAt (g₁ r) (g₂ r) x v) (Adot t x v) t)
(hS : ∀ (x : M) (v : Fin 4 → TangentSpace I x),
   HasDerivAt (fun r : ℝ => rmDiffLowAt (g₁ r) (g₂ r) x v) (Sdot t x v) t)
```

The **invariant** (`∀ v`, slot-vector) shape was chosen over the componentwise
(`∀ I₀ : Fin s → Idx`, frame-indexed) shape that K1's
`ChristoffelEvolutionEquationInFrameOn` uses, because (i) it needs no local frame, frame
domain, or `x ∈ u` side condition, (ii) it feeds `normSq0S_moving_deriv` directly, and
(iii) the componentwise form is recoverable from it by plugging basis vectors, while the
converse needs a frame-to-basis bridge.  K1/K2 will therefore owe one small adapter from
their frame-component statements to this invariant form — that adapter belongs on the
K1/K2 side, where the frame hypotheses already live.

Consequence: `forwardUniqueRate` carries `Adot`/`Sdot` in its signature, i.e.
`forwardUniqueRate g₁ g₂ Adot Sdot t`, not the ruling's schematic
`forwardUniqueRate g₁ g₂ t`.  This is the same deviation the design evidence already makes
(`movingRate g_bg g₀ g₁ t` carries its background metric).  **The alternative considered and
rejected**: define the rate with a raw `deriv (fun r => forwardUniqueDensity g₁ g₂ r x) t`
and add a separate `forwardUniqueRate_eq` identifying it.  That keeps the literal ruling
signature and makes `forwardUniqueEnergy_hasDerivAt` need *no* PDE hypotheses at all, but it
pushes job 1 (differentiate the three moving norms) out of K3, which is precisely what the
ruling assigns to K3.  Downstream cost of the two options differs by exactly one rewrite.

### Regularity input for differentiating under the integral

`first_var_joint` needs the scalar integrand jointly `ContMDiffOn … ∞` on `U ×ˢ univ`.  For
the metric difference alone this is derivable from chart-Gram smoothness of the two metrics
(that is `MovingEdgeEnergy.movingNorm_smooth`), but `connDiffSq`/`rmDiffSq` additionally
require the chart-Gram → Christoffel → Riemann smoothness chain, which does not exist as a
joint `(t,x)` statement.  So joint smoothness of `forwardUniqueDensity` is taken as one
explicit hypothesis `hdens`.  **This is the honest open regularity input of K3** and the
K-lane owes a producer for it.

Note the asymmetry that follows: only the **carrier** `g₁` needs chart-Gram joint smoothness
(for the moving measure).  `g₂`'s chart-Gram smoothness is *not* a hypothesis of
`forwardUniqueEnergy_hasDerivAt`, even though the mission sketch listed it — it is an
ingredient of `hdens`, not of the differentiation step.  Weakest-assumptions discipline says
do not demand it here.

### Volume term left as `traceTimeDerivMetric`

Under Ricci flow `½ tr_{g₁}(∂ₜ g₁) = −scal(g₁)`, so the volume term is `−scal · density`.
That identification is *not* performed: it needs `tr_g Ric = scal` plus the flow equation,
and `traceTimeDerivMetric` is what `first_var_joint` produces verbatim.  If the Grönwall
brick prefers `−metricScalarAt (g₁ t) x`, the bridge lemma
`traceTimeDerivMetric g₁ t x = −2 · metricScalarAt (g₁ t) x` is a small separate item.

## Public API

* `movingReact0S`, `normSq0S_moving_deriv` (generic tensor layer — see layering caveat)
* `metricDiffDot`, `metricDiff_hasDerivAt`
* `forwardUniqueDensity`, `forwardUniqueEnergy`
* `forwardUniqueDensityDot`, `forwardUniqueRate`, `density_hasDerivAt`
* `forwardUniqueEnergy_hasDerivAt`

## Lean lessons carried in / learned

* Carried from `ForwardUniqueFields.md`: **`rw` on `Tensor0SSpace` fiber algebra is
  unreliable — use the lemma as a term.**  `Tensor0SSpace.smul_apply` and
  `Tensor0SSpace.sub_apply` are applied here as `have h : <lhs> = <rhs> := Tensor0SSpace.…`,
  never as `rw [Tensor0SSpace.smul_apply]`.
* The `Fin 2` slot idiom in the whole `Tensor0SMetricDeriv` layer is
  `fun a : Fin 2 => if a = 0 then X else Y`, so the Ricci-flow PDE hypotheses are stated in
  that shape and the conversion to a generic slot vector `v` is one
  `funext a; fin_cases a <;> simp`.
* Only **one** error in the whole first pass, and it was `•` vs `*`: after
  `Tensor0SSpace.smul_apply` the goal carries a real `ℝ`-scalar action `(-2 : ℝ) • (a - b)`
  with `a b : ℝ`, which `ring` will not close.  `simp only [smul_eq_mul]` first, then `ring`.
* The rank-generic step went through with no coercion or transparency trouble: the final
  `exact hbase.hasDerivAt (by simp)` matched `movingReact0S` against the raw
  `ricReactionContract` application through the tactic-`let` bindings by plain defeq — no
  `simpa only [movingReact0S, gInv, ric]` unfolding was needed.  Likewise
  `(hT fun a => basis (I0 a)).hasDerivWithinAt` matched the `tensor0SComponent` component
  statement definitionally, so the `Fin s`-slot bookkeeping cost nothing.
* Higher-order unification into `first_var_joint` (`?f p.1 p.2 =?= density g₁ g₂ p.1 p.2`,
  `?g_fam p.1 =?= g₁ p.1`) resolves by first-order approximation; no `(f := …)` /
  `(g_fam := …)` hints were needed.
* `HasDerivAt.congr_deriv` is the right closer for "same function, rewrite the derivative
  value": `hbase.congr_deriv hval` where `hval : <first_var_joint's rate> = forwardUniqueRate`.
  Unfolding the goal's `forwardUniqueEnergy` was unnecessary — it is eta/delta-defeq to
  `first_var_joint`'s `fun s => ∫ …`, so `exact` absorbs it.

## What K3 does NOT do

No estimate, no Grönwall, no coercivity, no integration by parts.  The next bricks are
`forwardUniqueRate_le` (needs K1's `|∂ₜA|` bound, K2's divergence-form `∂ₜS` decomposition,
`TensorConnLapLoweredIBP`, and Young), then edge-Grönwall via `edgeGronwall_zero`, then
integral-zero-to-metric-equality.  This file is not yet wired into any aggregate import.
