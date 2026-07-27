# `ForwardUniqueSup.lean` — the slab-uniform input layer of the (B) endgame

Lane: `ricci_flow_forward_unique` (black box (B)).  Companion notes:
`ForwardUniqueAssembly.md` (the bundle + provenance ledger), `ForwardUniqueWiring.md` (the five
residual hypotheses), `ForwardUniqueDensReg.md` (the joint-regularity tower),
`ForwardUniqueRmBounds.md` / `ForwardUniqueRateLe.md` / `ForwardUniqueConnBound.md` (the
pointwise estimate producers).

## Outcome — 2026-07-26, seventh pass (curvature-tower slab sup)

`nablaKRmSlabSup` is written as the rank-uniform compact-slab wrapper around
`nablaKRmChartJoint`.  It keeps the norm metric `gN` independent of the
curvature metric `gC`, so ranks five and six will provide exactly the
`|∇Rm₂|²` and full `|∇²Rm₂|²` background inputs of `rmDotRemSq_le`.

Focused verification and the targeted export refresh passed.
This own-curvature bound does not by itself control the cross-lowered field
`P` in `sdecRem`; the latter needs its separate `g₁`-derivative regularity
wrapper.

## Outcome — 2026-07-26, eighth pass (cross-curvature slab sups)

`crossRm1SlabSup` and `crossRm2SlabSup` are written as the compact-slab
wrappers around `crossRm1ChartJoint` and `crossRm2ChartJoint`.  Their four
metric roles are independent.  The remainder uses
`(gN, gL, gC, gD) = (g₁, g₁, g₂, g₁)`, so these are exactly the rank-five and
rank-six bounds for the cross-lowered curvature `P`.

Focused verification and the targeted export refresh passed.

The same pass also adds `metricEquivSlab`, which combines the two already
proved one-sided comparison constants into a single `C ≥ 1` satisfying the
standard two-sided metric-equivalence predicate.  This is the form needed to
compare cross-metric tensor norms in the remainder.

`metricDiffSlabSup` records the remaining closed-slab scalar bound used by the
quadratic curvature term.  It is a direct compactness wrapper around the
already proved joint regularity of `metricDiffSq`; it passed focused and
targeted verification with the rest of this pass.

## Outcome — 2026-07-26, sixth pass (`∇Ric` slab sup)

`nablaRicSlabSup` now supplies a closed-slab constant for
`|∇^{gC} Ric(gC)|²_{gN}` directly from the two chart-Gram packages.  Its two
metric roles are intentionally separate: `(gN,gC) = (g₁,g₂)` is precisely the
`B₁` input of `connDiffDot_normSq_le`.

The proof is the generic `normSqSlabSup` instantiated with
`nablaRicChartJoint`; no new estimate is introduced.  Focused verification and
the targeted module build passed, the touched file is warning-free, and the new
endpoint has exactly `[propext, Classical.choice, Quot.sound]`.

This completes step 3/4 of the `hadot` continuation.  `fuAdotSlab` remains the
last wiring step for that field.  The theorem `ricci_flow_forward_unique`
remains unproved (0%); its dedicated machinery remains about 90%, and the whole
HCG compactness program remains about 10%.

## Outcome — 2026-07-26, fifth pass (DERIVATIVE-LAYER + audit of the residue)

**The named brick is delivered; the audit of what it buys says it is NOT sufficient, and the
previous pass's "nothing else stands between `fuSlab_of_gram` and an unconditional `hbounds`"
is wrong.**  `remLe` and `adotLe` are unchanged (still the two arguments of `fuSlab_of_gram`),
and nothing in this file or in `ForwardUniqueWiring.lean` was edited.

Delivered: `partRiemWithin` / `partRicciWithin` (+ `ricciWithinM`, `partRiemWithinM`,
`partRicciWithinM`) in `Analysis/Parabolic/RicciLinearization/
RicciDifferenceMeanValueWithin.lean`, 0 sorry, warning-clean, targeted build green.  See that
file's `.md`: the layer is free — `partialDerivWithin` is rank-agnostic, so arbitrarily many
spatial derivatives of any tower member cost one line each.

### The second gate (the reason neither field falls yet)

`normSqSlabSup` consumes `hA`: the components of the tensor family **on the chart frame of
`x₀`, at nearby points `p.2`**,

```
(t, x) ↦ A t x (fun i => chartBasisVecFiber x₀ (K i) x)   jointly C∞-within  (J ×ˢ univ) at (t, x₀)
```

For `A t x = metricRicciAt (g₂ t) x` that reading exists (`rm04ChartMap` / `rmChartComp`
pattern, `Evolution/ForwardUniqueDensReg.lean`).  For `A t x = metricNabla0S (g₂ t) Ric₂ x`
— `adotLe`'s `B₁` — it does **not**: there is no lemma anywhere in the tree writing a covariant
derivative's chart-frame components as `∂(chart component) − Γ·T − Γ·T` at an off-centre point.
The tower's `∂Ric` layer supplies the first summand and `christWithinM` the Christoffel factor;
the missing piece is the *identity that assembles them*.

Exactly the same gate blocks `remLe`: `sdecRemFam`'s `roughLap(Rm₂)` slab sup is
`normSq0S`-of-`covDiv0SField(metricNabla0S …)`, one derivative further along the same road.

### The route, with every ingredient located and checked (do not re-scout)

Target lemma, off-centre on `chartLeviCivitaGoodSet α`:

```
metricNabla0S g Ric x (fun a : Fin 3 => chartBasisVecFiber α (K a) x)
  = partialDeriv (K 0) (fun y => chartRicciTensor g α (K 1) (K 2) y) (extChartAt I α x)
    − ∑ m, chartChristoffel g α (K 0) (K 1) m (extChartAt I α x)
             * chartRicciTensor g α m (K 2) (extChartAt I α x)
    − ∑ m, chartChristoffel g α (K 0) (K 2) m (extChartAt I α x)
             * chartRicciTensor g α (K 1) m (extChartAt I α x)
```

* **The Leibniz formula is already proved**: `nabla0SFun_eval_coordFrame_moving_raw`
  (`Geometry/Coordinates/NablaComponents/Tensor0S.lean:361`) gives, for an arbitrary *moving*
  slot family `V : Fin s → (x : M) → TangentSpace I x`,

  ```
  nabla0SFun s cov X α x₀ (fun a => V a x₀)
    = extDerivFun (fun p => α p (fun a => V a p)) x₀ (X x₀)
      − ∑ a, α x₀ (Function.update (fun b => V b x₀) a ((cov (V a) x₀) (X x₀)))
  ```

  with four purely local hypotheses.  Its own consumer `nabla0SFun_eval_coordFrame`
  (`…/CoordFrameStep.lean:51`) is the **discharge template**: `hV` from the frame's
  `MDifferentiableAt`, and `hVmodel`/`hcoord` from the two *public*
  `tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt` /
  `…_coord_mdiffAt_center_of_contMDiffAt`
  (`Tensor/RSTensor/NablaOnTensors/Regularity/Tensor0S.lean:100,110`), which need only
  `ContMDiffAt` of the slot section — true for `chartBasisVecFiber α ·` at every `x` in `α`'s
  base set (`chartBasisVec_alpha_mdifferentiableAt`, `ChartBridge/Hessian.lean:1155`).
  Only `hpair` needs its own argument at a non-centre base point.
* **Do NOT go through** `nabla0SFun_eval_coordFrame` / `nabla0SFun_two_eval_coordFrame`'s
  *conclusions*.  They are conditional on `ModelDerivEqCoordDeriv0SAt`, whose own docstring
  calls it "the remaining analytic/chart-identification bridge"; grep confirms **no producer
  exists** in the tree, so that whole family is frontier-shaped.  The `_moving_raw` form is
  unconditional — use it directly.
* `totalNabla0SFun_apply_section` (`Tensor/RSTensor/NablaOnTensors/HigherOrder.lean:231`)
  descends `metricNabla0S g T x (Fin.cons (X x) slots)` to `nabla0SFun`.  The global smooth
  section `X` through `e^α_{K0}` at `x` is
  `exists_globalSmooth_chartBasisVec_ext_alpha`
  (`Geometry/Connection/ChartBridge/RiemannBasisIdentityOffCentre.lean:141`) — a bump-cut
  `χ • chartBasisVecFiber α j`, already used by the off-centre Riemann identity.
* The two `Γ`-terms: `LeviCivita_chartBasisVec_alpha_basis_apply`
  (`ChartBridge/Hessian.lean:1293`, public) is exactly
  `∇_{e^α_i} e^α_j (x) = ∑_k Γ^k_{ij}(α, ϕ_α x) • e^α_k(x)` **off-centre**; multilinearity of
  `Ric x` then turns each into `∑_m Γ · chartRicci`.
* The `extDerivFun` term → the tower's `partialDeriv`: the worked pattern is
  `extDerivFun_pairing_chartBasisVec_alpha_apply` /
  `extDerivFun_chartBasisVec_alpha_apply_of_mem` (`private`, `ChartBridge/Hessian.lean:1058`,
  `:1020`); `mfderiv_chartBasisVecFiber`
  (`Analysis/Integration/DivergenceTheorem/TangentAction.lean:191`) is the boundaryless form.
* The scalar being differentiated is identified by `ricciTensor_chartBasisVec_alpha_eq`
  (`ChartBridge/RiemannBasisIdentityOffCentre.lean:524`, public):
  `ricciTensor g x (e^α_p x) (e^α_q x) = chartRicciTensor g α p q (ϕ_α x)` for
  `x ∈ chartLeviCivitaGoodSet α`.  **This was the piece the previous notes assumed missing; it
  exists.**

**Scratch-probe result (fifth pass, so the next session does not have to re-check it).**  A
throwaway file in the lane's own namespace `DifferentialGeometry.PDE.RicciFlow`, with the lane's
`open`s and its `[InnerProductSpace Real E]` variable block, importing `ForwardUniqueSup` +
`Geometry/Coordinates/NablaComponents/Tensor0S` + the two `ChartBridge` files: all six
ingredients `#check` and the **displayed target statement elaborates**, with `sorry` as the only
warning.  So there is *no* section-variable / instance-diamond obstruction — the
`NormedSpace`-vs-`InnerProductSpace` trap recorded elsewhere in this lane does not bite here
(`nabla0SFun_eval_coordFrame_moving_raw` is stated over `NormedSpace 𝕜 E`, which the lane's
`InnerProductSpace Real E` supplies), and the `ChartBridge` lemmas already *require*
`InnerProductSpace ℝ E`, i.e. they are stated in the lane's own section.  The three `ChartBridge`
conclusions land in `Integral.DivergenceTheorem.chartRicciTensor` / `chartChristoffel` — the
**same** chart objects the `Within` tower produces, so no third bridge is needed between them.
Namespace note: `ricciTensor_chartBasisVec_alpha_eq`, `LeviCivita_chartBasisVec_alpha_basis_apply`
and `exists_globalSmooth_chartBasisVec_ext_alpha` live in
`DifferentialGeometry.Integral.Connection`; `totalNabla0SFun_apply_section` and the two
`tangentFieldModelInChart_…` producers live in `Tensor0SBundle`.

**The same bridge discharges `adotLe`'s `hNR₁`/`hNR₂`**, which are the *other* unproduced
hypothesis of `connDiffDot_normSq_le`: `chartNablaRic` is `ricciCovDerivCompInFrame`
(`Evolution/Connection/Components.lean:461`), which is *definitionally* the right-hand side of
`nabla0SFun_eval_coordFrame_moving_raw` at `V := (frame a, frame b)` — the `extDerivFun` term
and the two connection terms match term by term, with no chart conversion needed at all.  So
one bridge lemma pays for both `B₁` and `hNR`.

### `adotLe`'s remaining input list, audited against the code (not against notes)

`connDiffDot_normSq_le` (`ForwardUniqueConnBound.lean:1404`) — note its `hB₁` is
`normSq0S (g₁ t) x 3 (metricNabla0S (g₂ t) Ric₂ x) ≤ B₁`, i.e. **`|∇Ric₂|²`, one derivative,
rank 3** — the "`|∇²Ric₂|²`" of the previous notes is a misreading.

| input | status |
| --- | --- |
| `Ric₁ Ric₂ : Tensor0SField … 2` + `hRicᵢ` | **available** — `ricciSection` (`Geometry/Curvature/Riemann/Basic/Sections.lean:583`) at `metricCov gᵢ`, `metricCov_smooth`; `ricciSection_apply` → `ricciCurvatureAt` → `metricRicciAt` |
| `S`, `hS : IsRmDiffField` | **available** — `fuSfield`, `fuSfield_apply` is `rfl` |
| `frame`/`hframe`/`hu`/`hx` | **available** — `chartFrame I x`, `chartFrame_isFrame` (`C¹`, which is what is asked), base set of the trivialization |
| `gInv₁ gInv₂` + `hgInvᵢ` | **available** — `chartFrameInv`, `localFrameInv_of_mem` + `basisInvMetric_real` |
| `hΓ` | **available** — `fuGamma`/`gamma_of_gram` + `coeff_bilinOfComp` |
| `hA` | **available** — `connDiffVec_hasDerivAt` fed by the same `hΓ` |
| `Λric`, `B₃` | **available** — `ricciSlabSup` |
| `Λ`, `hΛ0` | **available** — `metricCompSlab` |
| `nablaRicᵢ` + `hNRᵢ` | **MISSING — the bridge above** |
| `B₁` | **MISSING — the bridge above + `partRicciWithinM` + a new `nablaRicChartJoint`** |

The RHS arithmetic is clean: `nablaRmDiffSq (g₁ t) S x` is *definitionally*
`normSq0S (g₁ t) x 5 (metricNabla0S (g₁ t) S x)`, which is `hadot`'s own second term, and
`metricDiffSq + connDiffSq ≤ dens`.  So once the bridge exists, `adotLe` is
`connDiffDot_normSq_le` plus a `max`-of-two-constants `linarith`.

### Honest size of the residue

The bridge is **not** a ≤150-line local lemma, but every ingredient above is already proved, so
it is assembly, not new mathematics.  Estimated shape of the next session:

1. `nablaRicChartComp` (the displayed identity) — new file
   `Evolution/ForwardUniqueNablaChart.lean`, ≈200–300 lines.  Only genuinely new sub-goal:
   `hpair`, i.e. `ContMDiffAt (fun p => Ric p (e^α_{K1} p, e^α_{K2} p)) x` at a **non-centre**
   base point; `ricciTensor_chartBasisVec_alpha_eq` reduces it to smoothness of
   `chartRicciTensor g α · · ∘ extChartAt I α`, which the settled tower already gives.
2. `nablaRicChartJoint` — in `ForwardUniqueDensReg.lean`, the `rmChartJoint` template verbatim,
   with `partRicciWithinM` for the derivative summand and `christWithinM` for the two
   `Γ`-summands.  ≈100 lines.
3. `nablaRicSlabSup` (here) = `normSqSlabSup` at that family.  ≈25 lines.
4. `fuAdotSlab` (Wiring) = `connDiffDot_normSq_le` at `chartFrame`/`chartFrameInv`/`ricciSection`
   /`fuSfield`, plus the `max`-of-two-constants arithmetic.  ≈200 lines; `hNR` comes from
   step 1 read in `ricciCovDerivCompInFrame` form.

`remLe` needs steps 1–3 one derivative further (`roughLap Rm₂`, i.e. `covDiv0SField` of
`metricNabla0S` of the `(0,4)` curvature — `partRiemWithinM` is the tower half of it) **plus**
the R13 evaluation identities for `sdecRemFam`'s four summands, which are a separate and
larger problem (see §"`remLe`: blocked beyond sups").

## Outcome — 2026-07-26, fourth pass (FINAL-FIELDS)

**`volLe` and `reactLe` are CLOSED unconditionally at the constructed carriers; `Λ` is closed
too; `hbounds` is short exactly TWO fields (`remLe`, `adotLe`), and `fuSlab_of_gram`
(`ForwardUniqueWiring.lean`) assembles the other four modulo those two.**

A scratch `example` machine-checks that
`forward_unique_of_gram … (fuSlab_of_gram … hrem hadot) (energyEdgeCont …)` closes
`ricci_flow_forward_unique`'s **verbatim** statement, so the endpoint discharge is a one-liner
once `hrem`/`hadot` have producers.  0 `sorry`, warning-clean, ten endpoints 3-axiom.

### The three corrections this pass forced

1. **`volLe` never needed the drift's joint continuity.**  The previous note's "route unchanged:
   port `traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv` into the lane's currency" was
   the long way round.  `fuTraceRd` (already `private` in the wiring, from the second pass)
   *is* the bridge in the lane's currency, and it makes the drift `−2·tr_{g₁}Ric₁` — a scalar
   the **Ricci sup already controls**.  `tracePairSq_le` (new, here) pays the one dimension
   factor and `volSlabSup` returns `C_V = √(n·B)`.  Nothing is integrated, nothing is
   differentiated, no `RealizedMetricFamily` currency appears.  **`volSlabLe` (the old
   compactness wrapper with the `hdrift` regularity hypothesis) is DELETED** — it was unused
   and its assumption is now superseded; `slabBound`, its only real content, stays.
2. **`Λ` is NOT a sphere-bundle compactness problem.**  The previous note claimed the pointwise
   comparison `g₁ ≤ Λ·g₂` "needs a separate compactness argument on `Icc a c × unit sphere
   bundle`, or a Grönwall-type comparison".  It needs neither: `abs_apply_le_sqrt_normSq0S`
   with **both slots equal to `v`** returns `|g₁(v,v)| ≤ √(|g₁|²_{g₂})·√(g₂(v,v))·√(g₂(v,v))`,
   and the two square roots multiply back to `g₂(v,v)`.  So `Λ = √(sup |g₁|²_{g₂})` and
   `metricSlabSup g₂ g₁` (roles exchanged) is the sup.  `metricComp_le` / `metricCompSlab`,
   ~15 lines each.  **`Λ` was a `normSq0S` sup all along.**
3. **`movingReact_le` was never needed.**  The rank-2 cite in
   `Analysis/Spectral/Intrinsic/DeTurck/MovingEdgeEnergy.lean:643` is false-green (that file has
   no olean) and was **not** imported.  The bound is reproved in-lane at every rank in ~150
   lines, and the operator-bound→`normSq0S` Cauchy–Schwarz step the note said was "still owed"
   turned out to be unnecessary: taking the ON frame *first* makes the components of `Q`
   directly bounded by `√(|Q|²_g)`, so no operator bound ever appears.

### `reactLe`: the route that worked

`movingReact0S` is frame-pinned to `Module.finBasis`, so it carries no bound by itself.  Three
steps:

* `reactOrtho` (private) — run `normSq0S_moving_deriv` (canonical basis, giving `movingReact0S`)
  and `hasDerivWithinAt_normSq0S_ricciFlow` (an **arbitrary** basis, giving
  `ricReactionContract`) on the *same* function `r ↦ |W|²_{g r}` with the carrier frozen, and
  match them with `HasDerivAt.unique`.  The frame's inverse metric at `t` is the identity: from
  `MetricInverseInBasis`'s own first equation, `∑_k gInv i k · G k j = δ` collapses under
  `hON` to `gInv i j = δ i j` — no external uniqueness lemma is needed.
* `ricReactAbs_le` (private) — a crude but hypothesis-free array bound at the identity inverse
  metric: `|δ| ≤ 1`, `|ric| ≤ Bq`, `|c| ≤ N`, triangle inequality throughout.  No re-indexing
  bijection, no `Function.update`, no cancellation: the constant `2·card²·s·n²·Bq·N²` is
  wasteful and that is fine, the field only needs *a* slab constant.
* `movingReactAbs_le` (public) — the two glued, with `abs_apply_le_sqrt_normSq0S` supplying both
  component bounds: `|movingReact0S (g t) x s Q W| ≤ 2·s·n^{2s+2}·√(|Q|²_{g t})·|W|²_{g t}`.

`reactSlabLe` then sums ranks 2/3/4 against `metricDiffSq_le_dens`/`connDiffSq_le_dens`/
`rmDiffSq_le_dens`, giving `C_R = (4n⁶ + 6n⁸ + 8n¹⁰)·√Λric`, and `fuReactSlab` (wiring) fires it
at `ricciSlabSup g₁ g₁` and (B)'s own PDE field.

### What is left, and why both remaining fields are one brick

`remLe` and `adotLe` are **not** two independent problems any more:

* `adotLe`'s producer `connDiffDot_normSq_le` now has three of its four background constants —
  `Λric` and `B₃` from `ricciSlabSup`, `Λ` from `metricCompSlab`.  The fourth,
  `B₁ ≥ |∇²Ric₂|²_{g₁}`, needs chart components of `metricNabla0S (g₂ t) Ric₂`, i.e. a
  `∂(chart Riemann)` layer.  (Its `hΓ`/`hA` inputs are available via `fuGamma`; what remains
  besides `B₁` is instantiation plumbing — the local frame, the `gInv`/`nablaRic` component
  families, and the `connSpeed`/`connDiffDot` identification.)
* `remLe` at `sdecRemFam` needs the four summands identified tensorially (per ruling R13) and
  the identification consumes a `roughLap(Rm₂)` slab sup.

**Both bottom out on the same missing layer**: `partRiemWithin` / `partRicciWithin` in
`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValueWithin.lean` (mirroring the
existing `partChristWithin`), plus the `normSq0S_jointContMDiffOn` feed for the resulting
`∇Ric` / `ΔRm` chart components.  That single derivative brick unblocks both fields; nothing
else does.

## Outcome — 2026-07-26, third pass (SLAB-2)

**`hedge` is DISCHARGED; `fluxLe` is now produced at the constructed carrier; `hbounds` is
still short four fields.**  `forward_unique_of_gram`'s residual list drops from **two**
hypotheses to **one**.

* `energyEdgeCont` (this file) **is** the wiring's `hedge`, from (B)'s two chart-Gram fields
  alone.  Machine-checked against `forward_unique_of_gram` in a scratch `example`: the
  planner's discharge of that slot is a one-liner.
* `ricciSlabLe` (`ricciLe`) was already unconditional; `fuFluxSlab`
  (`Evolution/ForwardUniqueWiring.lean`) is now `fluxLe` at `fuUflux`, unconditional, using
  the three background sups below.
* `volLe`, `remLe`, `reactLe`, `adotLe` remain open — see §"Field-by-field discharge table"
  and §"What is still missing".

0 `sorry`; focused check and targeted module build green, warning-clean; every public endpoint
3-axiom clean.

### What the closed-edge upgrade bought

`ForwardUniqueDensReg.lean`'s brick `normSq0S_jointContMDiffOn` lost its `IsOpen J` hypothesis
(third pass, see `ForwardUniqueDensReg.md`), so it now fires on `J := Icc a c`.  The
§"The closed-edge blocker" of the previous pass is therefore **RESOLVED**, and this file adds
the sup layer it was blocking:

| new endpoint | delivers |
| --- | --- |
| `normSqSlabSup` | brick + `normSqSlabBound`: any moving fibre norm with closed-edge chart components is bounded on `Icc a c ×ˢ univ` |
| `metricSlabSup` | `B_g ≥ \|g₂\|²_{g₁}` |
| `rm04SlabSup` | `B ≥ \|Rm(∇^{gC}) lowered by gL\|²_{gN}`, three metric roles independent — `(g₁,g₂,g₂)` is `B₂`, `(g₁,g₁,g₂)` is `B_P` |
| `ricciSq_le_rm04` | `\|Ric₂\|²_{g₁} ≤ n⁴·\|Rm(∇²) lowered by g₁\|²_{g₁}` (from `metricRicci_eq_trace_cross` + `normSq0S_domDomCongr` + `traceNormSq_le`) |
| `ricciSlabSup` | `B₃ ≥ \|Ric₂\|²_{g₁}`; with `g₂ := g₁` this is `adotLe`'s `Λric` and `reactLe`'s only background norm |
| `energyEdgeCont` | the wiring's `hedge` |

### `hedge`: the route

`forwardUniqueEnergy g₁ g₂ t = ∫ dens(t,·) dμ_{g₁ t}` moves **both** the integrand and the
measure, so the edge is a moving-measure statement.  The dominated-convergence layer already
exists: `integral_family_cont`
(`Analysis/Integration/Measure/FamilyContinuity.lean:203`) takes purely `C⁰` hypotheses on an
**arbitrary compact** time set and returns `ContinuousOn (fun t => ∫ f t dμ_{g t}) K`.  So the
proof is: restrict (B)'s fields to `Icc a c` with `c := (a+b)/2`, feed
`dens_jointContMDiffOn (J := Icc a c) |>.continuousOn` as the integrand input, and widen
`ContinuousWithinAt … (Icc a c) a` to `Ico a b` through `Icc a c ∈ 𝓝[Ico a b] a`.  **No new
integration theory was needed** — the only thing that had been missing was the closed-edge
`C⁰` regularity of the *density*, which is exactly what the DensReg upgrade supplies.
`first_var_joint` / `first_variation_of_volume` are structurally unusable here: they are
hard-gated on `IsOpen U` through `exists_time_retract`.

## What is still missing (the four open fields)

* **`volLe`** — needs joint continuity of `traceTimeDerivMetric g₁` on `Icc a c ×ˢ univ`.
  Unlike every other background quantity this is *not* a chart-Gram statement: the trace is
  computed in the chart **centred at `x` itself**, and its time derivative at `t = a` is
  one-sided.  Route unchanged: port `traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv`
  (`Evolution/Volume.lean`, stated in `RealizedMetricFamily` currency) into the lane's
  `ℝ → SmoothRiemannianMetric I M` currency, then use `ricciSlabSup` for the scalar-curvature
  sup.  This is now the *cheapest* of the four.
* **`reactLe`** — still needs a bound on `movingReact0S`, which is frame-pinned to
  `Module.finBasis`.  The №47 basis-free reading (`fuReactDeriv`, `private` in
  `ForwardUniqueWiring.lean`) exhibits `movingReact0S (g t) x s Q W` as
  `deriv (fun r => normSq0S (g r) x s W) t`, i.e. basis-free — so the intended shortcut is
  `HasDerivAt.unique` against the same derivative computed in a `g`-orthonormal basis, which
  transports `movingReact_le` (`Analysis/Spectral/Intrinsic/DeTurck/MovingEdgeEnergy.lean:643`,
  rank 2, for the parallel `movingMetricReact`) to `movingReact0S` at every rank.  Not
  attempted in this pass.  `ricciSlabSup` already supplies the `sup |Ric₁|²` it will consume,
  but note `movingReact_le` takes an **operator** bound `|Q(v,w)| ≤ B|v||w|`, not a
  `normSq0S` bound — a Cauchy–Schwarz step is still owed.
* **`adotLe`** — `connDiffDot_normSq_le` (`ForwardUniqueConnBound.lean:1404`, 0-sorry) is
  instantiable: its `hΓ` is `fuGamma` rewritten through `coeff_bilinOfComp`
  (`ForwardUniqueConnDot.lean:587`) and its `hA` is `connDiffVec_hasDerivAt`
  (`ForwardUniqueConnDot.lean:418`) fed by the same `fuGamma` — the previous note's claim that
  `hΓ`/`hA` are missing is **stale**.  Of its four background inputs, `Λric` and `B₃` are now
  `ricciSlabSup`.  The two genuinely missing ones are:
  - `B₁ ≥ |∇²Ric₂|²_{g₁}` — needs chart components of `metricNabla0S (g₂ t) Ric₂`, i.e. a
    `∂(chart Riemann)` layer.  `RicciDifferenceMeanValueWithin.lean` has `partChristWithin`
    (the `∂Γ` layer) but no `partRiem`/`partRicci`; adding one is the smallest brick.
  - `Λ` with `∀ v, (g₁ t)(v,v) ≤ Λ·(g₂ t)(v,v)` — a *pointwise metric comparison*, not a
    `normSq0S` sup, so `normSqSlabSup` does not produce it.  It needs a separate
    compactness argument on `Icc a c × unit sphere bundle`, or a Grönwall-type comparison from
    the two PDEs.
* **`remLe`** — unchanged and the hardest: two of `sdecRemFam`'s four summands
  (`lowOfComp g₁ b (rmDotRem …)` and `gapDot g₁ g₂ (uhlRm2Vec …)`) are built from a raw
  component array and a bare pointwise trilinear family, neither of which carries **any** norm
  bound anywhere in the tree.  This is a planner decision (re-express `sdecRemFam` through
  tensorial carriers?), not a sup problem.

## What the wiring actually asks for

`forward_unique_of_gram` (`ForwardUniqueWiring.lean:561`) leaves

```
hbounds : ∀ c ∈ Ioo a b, ∃ C_A C_R C_Ric C_V C_U C_rem,
  ForwardUniqueSlab g₁ g₂ (connSpeed g₁ g₂ (fuAvec g₁ g₂)) (fuSfield g₁ g₂)
    (fuUflux g₁ g₂) (fuRem g₁ g₂) a c C_A C_R C_Ric C_V C_U C_rem
```

and all six fields of `ForwardUniqueSlab` (`ForwardUniqueAssembly.lean:229`) quantify over the
**open** `Ioo a c`.  Two facts about that shape drive everything below.

1. `Ioo a c` accumulates at `a`, so a uniform constant on it needs control **up to the closed
   initial edge** `t = a`.  Compactness therefore has to be applied on `Icc a c`, not on an
   interior subslab.
2. The carriers are the *constructed* ones of `ForwardUniqueWiring.lean`, not the abstract ones
   the older ledger entries were written against.  In particular `Uflux = fuUflux = sdecUflux`
   and `rem = fuRem = sdecRemFam`, which are **not** `rmDiffFlux` / `lapDiffRem`.

## Field-by-field discharge table

| field | needed at | producer | sup consumed | status |
| --- | --- | --- | --- | --- |
*(fourth pass: `volLe` and `reactLe` moved to DONE; see §"Outcome — fourth pass".)*

| `ricciLe` | — | `ricciSlabLe` (here) ← `ricciDiff_eq_trace` + `normSq_ricciTraceRep` + `ricciDiffSq_le` + `rmDiffSq_le_dens` | **none** | **DONE, unconditional, `C_Ric = n⁴`** |
| `volLe` | `traceTimeDerivMetric g₁` | `fuVolSlab` (Wiring) ← `volSlabSup` + `tracePairSq_le` (here) ← `fuTraceRd` | `ricciSlabSup` | **DONE, unconditional given (B)**, `C_V = √(n·B)` |
| `fluxLe` | `sdecFlux g₁ g₂ Rm₂ P` | `fuFluxSlab` (Wiring) ← `fluxSlabLe` (here) ← `sdecFluxSq_le` (here) ← `fluxNormSq_le` + `reLowerPairSq_le` (here) + `connDiffSq_le_dens` | `rm04SlabSup` ×2, `metricSlabSup` | **DONE at the constructed carrier, unconditional given (B)** |
| `remLe` | `sdecRemFam` | **none** | needs a `roughLap(Rm₂)` sup | **OPEN** — R13 identities + the `∂(chart Riemann)` layer |
| `reactLe` | `movingReact0S` | `fuReactSlab` (Wiring) ← `reactSlabLe` ← `movingReactAbs_le` (here) ← `reactOrtho` + `ricReactAbs_le` | `ricciSlabSup` | **DONE, unconditional given (B)**, `C_R = (4n⁶+6n⁸+8n¹⁰)√Λric` |
| `adotLe` | `connSpeed … fuAvec` | `connDiffDot_normSq_le` (`ForwardUniqueConnBound.lean:1404`; **planner correction: that file is 0-sorry since β4, commit `24dc9ac50` — the ":496 live sorry" claim was read from the .md's historical disproof section, not the code**) | `Λric` ✓, `Λ` ✓ (`metricCompSlab`), `B₃` ✓ (`ricciSlabSup`), `B₁ = |∇²Ric₂|²` ✗ | **OPEN on `B₁` alone** (plus instantiation plumbing); `hΓ`/`hA` available via `fuGamma`, `Λ` closed in the fourth pass |

## What is in the file

### 1. The compactness engine (the piece `ForwardUniqueWiring.md` names as missing)

* `slabBound F hF : ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc a c, ∀ x, |F t x| ≤ C` from
  `ContinuousOn (fun p => F p.1 p.2) (Icc a c ×ˢ univ)`.  `IsCompact.exists_bound_of_continuousOn`
  on `isCompact_Icc.prod isCompact_univ`; the two-sided conclusion is what `volLe` needs.
* `slabBound_ioo` — the same on `Ioo a c`, the interval the bundle quantifies over.
* `normSqSlabBound` — the shape the five sub-producers consume: one constant `B` with
  `|A t x|²_{g t} ≤ B` on the whole subslab.

**Relocation TODO.**  `slabBound` / `slabBound_ioo` mention neither `I` nor any bundle; they are
pure topology (`compact × compact → bounded`).  Their canonical home is a topology layer, not
this lane.  They are kept here only because the lane is the sole consumer today.

### 2. `ricciLe`, unconditionally

`ricciSlabLe g₁ g₂ t x : |Ric₁ − Ric₂|²_{g₁} ≤ n⁴ · forwardUniqueDensity g₁ g₂ t x`.

No background norm, no compactness, no hypothesis at all.  The reason: `ricciDiff_eq_trace`
(`ForwardUniqueRatePro.lean:256`) exhibits the Ricci difference as the `g₁`-trace of a *slot
permutation* of the very carrier `S₀₄` whose norm is the curvature third of the density, and
`normSq_ricciTraceRep` says that permutation is a fibre isometry — so `ricciDiffSq_le` applies
with background coefficient `B = 0`, and `rmDiffSq_le_dens` finishes.  This is the only one of
the six fields that is genuinely free.

### 3. `volLe`

`volSlabLe g₁ hdrift : ∃ C_V ≥ 0, ∀ t ∈ Ioo a c, ∀ x, ½·traceTimeDerivMetric g₁ t x ≤ C_V`.

Exactly the route the ledger records ("compactness of `Icc a c` applied to
`traceTimeDerivMetric`").  The input is a *regularity* statement — joint continuity of the
volume drift up to the closed edge — not a restatement of the conclusion, so this is not an
adapter wrapper.

Discharging `hdrift` is a separate obligation: `traceTimeDerivMetric g_fam t x` is
`trace(G(t,x)⁻¹ · Ġ(t,x))` computed in the chart **centred at `x` itself**, so its joint
continuity is not a chart-Gram statement.  The intended route is the Ricci-flow identity
`traceTimeDerivMetric = −2·scal`, for which `Evolution/Volume.lean` has
`traceTimeDerivMetricAt_eq_neg_two_scalar_of_metricDeriv` — but only in the
`RealizedMetricFamily` / `ScalarRealizesRicciTraceInFrame` currency, not the lane's
`ℝ → SmoothRiemannianMetric I M`.  Porting that bridge is the next concrete step for this
field; it then needs the same closed-edge curvature sup as everything else.

### 4. `reLowerPairSq_le` and `sdecFluxSq_le`

`reLowerPairSq_le g T K x : |reLowerPair g T K|²_g ≤ n^{s+4} · |T|²_g · |K|²_g`.

This is the genuinely new algebraic content of the pass.  `reLowerPair` is
`metricTraceFirstTwoField g (domDomCongr (reLowerPerm2 s) (T ⊗ K))`; the bound is
`traceNormSq_le` ∘ `normSq0S_domDomCongr` (permutation is an isometry) ∘ `normSq0S_product`
(the product multiplies fibre norms *exactly*).  Nothing in the tree bounded this carrier
before, and it appears in **both** `sdecFlux` and `sdecRem`.

`sdecFluxSq_le` then gives the `fluxLe` estimate at the carrier the wiring builds:

```
|sdecFlux g₁ g₂ Rm₂ P|²_{g₁} ≤ 32·n⁵·|A₀₃|²·B₂ + 8·n¹⁰·|A₀₃|²·(B_P·B_g)
```

with `B₂ ≥ |Rm₂|²_{g₁}`, `B_P ≥ |P|²_{g₁}`, `B_g ≥ |g₂|²_{g₁}` named arguments.  Both summands
carry `|A₀₃|²_{g₁} = connDiffSq`, so `connDiffSq_le_dens` turns the whole thing into
`C_U · density`; `fluxSlabLe` does exactly that and is the `fluxLe` field verbatim, with

```
C_U = 32·n⁵·B₂ + 8·n¹⁰·B_P·B_g.
```

Its three nonnegativity side conditions are precisely what `normSqSlabBound` returns next to
each sup, so the field is one closed-edge sup away from being unconditional.

**Correction to `ForwardUniqueAssembly.md`'s ledger.**  It names `fluxNormSq_le` /
`rmFluxNormSq_le` as the producer of `fluxLe`.  That is wrong for the constructed carrier:
`rmFluxNormSq_le` bounds `rmDiffFlux`, whereas `fuUflux = sdecUflux = sdecFlux` is
`lapDiffFlux(Rm₂) − reLowerPair g₁ P (lapDiffFlux g₁ g₂ g₂)`, and the subtracted defect had no
bound at all.  Same correction applies to `remLe` (`rmRemNormSq_le` bounds `lapDiffRem`, not
`sdecRemFam`).

## ~~The closed-edge blocker (why no background sup is produced here)~~ — RESOLVED 2026-07-26

*Historical.*  The blocker below was discharged in two steps: `christoffelWithin` /
`riemannWithin` (`RicciDifferenceMeanValueWithin.lean`, ruling R12) removed the two-sided
`ContDiffAt` demand, and the third pass of `ForwardUniqueDensReg.lean` removed `IsOpen J`
from the brick and re-threaded `connChartJoint`/`rmChartJoint` against `christWithinM`/
`riemWithinM`.  The four `private` helpers named at the end of this section were **deleted**,
not made public: their `Within` replacements are public in the `Within` file.  Kept for the
record of what the obstruction was.

### The obstruction, as it stood

Every remaining field needs `sup_{Icc a c × M}` of a **curvature-type** background quantity
(`|Ric₁|²`, `|Rm₂|²`, `|∇²Ric₂|²`, `|∇²Rm₂|²`, the scalar curvature).  The route is
`normSq0S_jointContMDiffOn` (`ForwardUniqueDensReg.lean:216`) + `slabBound`.  It does not close,
for a precise reason:

* (B)'s own regularity field is `h1smooth : ContMDiffOn … (Ico a b ×ˢ baseSet)` — smoothness in
  time only **one-sidedly** at `t = a`.
* The joint Cramer chain (`chartGramDet_jointContMDiffOn`, `chartGramAdj_jointContMDiffOn`,
  `chartInvGram_jointContMDiffOn`) is stated for an **arbitrary** `J : Set ℝ`, so it survives
  the closed edge.  Good.
* The joint **Christoffel/Riemann** tower does not.  `GenJointGram`
  (`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValue.lean:401`) demands
  `ContDiffAt` in `(s, y)` jointly at every `s₀ ∈ S`, i.e. a **two-sided** time neighbourhood;
  `gen_joint_christoffel` / `gen_joint_riemann` inherit that.  With `S = Ico a b` and `s₀ = a`
  the hypothesis is strictly stronger than `h1smooth`, so the tower cannot be fed at the edge.
* Consequently `normSq0S_jointContMDiffOn` is stated with `hJ : IsOpen J`, and the lane's own
  consumers (`connChartJoint`, `rmChartJoint`, `dens_jointContMDiffOn`) all live on `Ioo a b`.

**The smallest unblocking step** is a `ContDiffWithinAt` version of the joint Christoffel/Riemann
tower — `GenJointGramWithin`, plus `gen_joint_christoffel`/`gen_joint_riemann` restated with
`ContDiffWithinAt … (S ×ˢ interior target)`.  `Ico a b ×ˢ U` is `UniqueDiffOn`, and only the
*spatial* derivatives are taken, so the mathematics is routine; the cost is re-threading the
chain rules of `RicciDifferenceMeanValue.lean` (~700 lines of tower).  That file is outside this
lane and was not touched.

Two smaller, private-visibility obstacles sit on the same path and should be fixed when the
tower is:

* `genGram_of_joint`, `jointOnM`, `christJoint`, `riemJoint` are **`private`** in
  `ForwardUniqueDensReg.lean`.  Any background-norm sup producer outside that file needs all
  four; re-deriving them would be a straight duplication of ~80 lines.
* `gen_joint_ricci` is `private` in `RicciDifferenceMeanValue.lean` (its body is three lines over
  the public `gen_joint_riemann`, so this one is cheap to work around).

## `remLe`: blocked beyond sups

`fuRem = sdecRemFam = sdecRem g₁ g₂ P b (rmDotRem …) (uhlRm2Vec …)`, i.e. four summands
(`ForwardUniqueSdec.lean:659`):

1. `lowOfComp g₁ b R₀` with `R₀ = rmDotRem …` — a raw **component array**, not a tensor with a
   fibre norm.  Bounding `|lowOfComp g b R₀|²` needs componentwise control of `rmDotRem`, which
   is built from the Uhlenbeck component families `Rm04ᵢ`, `Bᵢ`, `ricciOneUpᵢ`.
2. `gapDot g₁ g₂ Rm2dot` with `Rm2dot = uhlRm2Vec …` — a **bare pointwise family** (`∂ₜRm₂` as a
   trilinear map).  There is no continuity, no smoothness and no norm bound available for it;
   this is the same class of object that already blocks `hpair`/`hrest`/`hrem` in the wiring.
3. `(reLower g₂ g₁ − id)(Δ₁P)` — needs a `reLower`-defect bound against `metricDiffSq`;
   `traceDiffNormSq_le` (`ForwardUniqueRmBounds.lean:641`) is the right shape but is stated for
   the trace, not for `reLower`.
4. `tr₁(reLowerPair g₁ (∇¹P) (lapDiffFlux g₁ g₂ g₂))` — **this one is now available**:
   `reLowerPairSq_le` + `traceNormSq_le`.

So `remLe` is not a sup problem: summands 1 and 2 need new estimate machinery whose inputs
(component arrays, a bare `∂ₜRm₂` family) do not carry norms yet.  Recommended next planner
decision: whether `sdecRemFam` should be re-expressed through tensorial carriers before any
bound is attempted.

## Lean lessons from this pass

* `slabBound`'s statement mentions no `I`, so Lean's automatic section-variable inclusion drops
  it: call sites must write `slabBound (M := M) …`, **not** `(I := I)`.  The error message
  ("Invalid argument name `I`") is the tell.
* `isCompact_univ (α := M)` does not elaborate in this Mathlib (the binder is `X`); the robust
  form is the ascription `(isCompact_univ : IsCompact (univ : Set M))`.
* `sdecFlux g₁ g₂ T P x = lapDiffFlux … x - reLowerPair … x` is **`rfl`**: `Tensor0SField`
  subtraction evaluates pointwise definitionally, so no `fieldSub_eval` rewrite is needed.
* Rank arithmetic across `reLowerPair`: the product has rank `s + 1 + 3` and the trace consumes
  rank `(s + 2) + 2`.  These are defeq, so `exact`/`refine` cross the gap, but a `rw` on the
  exponent would not — state the conclusion at `n ^ (s + 4)` and close with `exact`, never with
  `rw`.
* `MultilinearSection.domDomCongr_apply` is `rfl` and `@[simp]`; `normSq0S_product` is stated
  directly on `MultilinearSection.product … x`, so no `_apply` rewriting is needed on that side.
* A fourth private copy of `exists_onFrame` / `onFrame_inv` had to be made (copies now live in
  `ForwardUniqueRmBounds.lean`, `ForwardUniqueConnBound.lean`, `ForwardUniqueRatePro.lean` and
  here).  **Dedup TODO**: promote one public pair to
  `Tensor/RSTensor/Tensor0SRiemannian/` and delete the four.

## Verification

Focused check green and warning-free; targeted module build green; zero `sorry`.
`#print axioms` on every public endpoint — the original seven plus `normSqSlabSup`,
`metricSlabSup`, `rm04SlabSup`, `ricciSq_le_rm04`, `ricciSlabSup`, `energyEdgeCont` — returns
exactly `[propext, Classical.choice, Quot.sound]`.

The module is now reachable from the root aggregate **transitively**: `ForwardUniqueWiring.lean`
imports it (for `fuFluxSlab`), and the aggregate imports the wiring.  No edit to
`DifferentialGeometry.lean` was made.

## Next targets, in order of leverage

*(Rewritten 2026-07-26 after the fourth pass.  Items 0/2 below are now DONE; the list has
collapsed to a single brick.)*

0. ~~`volLe`~~ **DONE** (`fuVolSlab`); the `Volume.lean` port was never needed.
1. ~~The `ContDiffWithinAt` joint Christoffel/Riemann tower (closed edge).~~  **DONE** (R12 +
   the DensReg third pass).
2. ~~`movingReact_le` (plan №25)~~ **DONE** in-lane at every rank (`movingReactAbs_le`), and
   `reactLe` with it (`fuReactSlab`).
3. ~~`Λ`, the pointwise metric comparison.~~  **DONE** (`metricCompSlab`); it was a `normSq0S`
   sup, not a sphere-bundle problem.
4. ~~`partRiemWithin` / `partRicciWithin`~~ **DONE** (fifth pass, plus `ricciWithinM`,
   `partRiemWithinM`, `partRicciWithinM`).  The claim attached to it here — "nothing else
   stands between `fuSlab_of_gram` and an unconditional `hbounds`" — was **wrong**: those are
   chart *coefficient* statements, and a chart-*frame component* formula for a covariant
   derivative is a second, independent gate.  See §"The second gate" at the top.
5. ~~`nablaRicChartComp` → `nablaRicChartJoint` → `nablaRicSlabSup`~~ **DONE**.
   These supply `adotLe`'s `B₁`; the existing `nablaRicReal_frame` supplies
   `hNR₁`/`hNR₂`.  Remaining for this field: the single `fuAdotSlab` wiring
   theorem.  Separately, `remLe` still needs the full rank-five/rank-six
   curvature derivative sups plus the R13 identities.
