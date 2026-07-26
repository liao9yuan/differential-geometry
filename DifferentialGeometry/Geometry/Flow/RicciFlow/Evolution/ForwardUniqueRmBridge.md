# `ForwardUniqueRmBridge.lean` — Route-K brick K2.6b (the R4 bridge)

Companion note for
`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ForwardUniqueRmBridge.lean`.
Governing decision: `ShortTime/FORWARD_UNIQUE_PLAN.md` №13, **planner ruling R4**
(the lowering mismatch).  Predecessors: `ForwardUniqueRmDot.lean` (K2.1 + K2.6-core),
`ForwardUniqueRmDiff.lean` (K2.0/K2.3), `Evolution/Uhlenbeck.lean:727` (the interface).

## Outcome: **(B)** — deliverable 1 GREEN and complete; deliverable 2 partial, precisely classified

17 public declarations (13 theorems + 4 defs) + 3 private helpers, **0 sorry**, no new
instances, no axioms, no notation.  Focused check PASS; targeted module build PASS
(`✔ Built … ForwardUniqueRmBridge`); `#print axioms` on all 17 public declarations is
exactly `[propext, Classical.choice, Quot.sound]`.

**The R4 escalation did NOT fire** — see "Answer to the escalation question" below.

## Deliverable 1 (COMPLETE): own-metric `(0,4) → (1,3)` evolution conversion

The key design decision, and why it is cheap: the **inverse metric is only ever used at the
frozen time `t`**.  A naive route ("differentiate `g(r)♯`") needs the derivative of the
inverse metric family (`Tensor0SMetricDeriv.lean`'s `basisInv_time`, which is `HasDerivAt`
only and would have forced either a `HasDerivWithinAt` re-proof of matrix inversion in this
file or a strengthened two-sided hypothesis on the metric).  That is avoidable:

1. `raiseAt_lower` — for **one** metric, `raiseAt g x basis (fun l => g(V, basis l)) = V`.
   Apply it with the *frozen* metric `g t` to the *moving* vector `V r`: the reconstruction
   holds for every `r` with time-independent coefficients `basisInvMetric (g t) x basis`.
2. The frozen-lowered components `r ↦ (g t)(V r, basis l)` are then shown differentiable by
   writing `(g t) = (g r) + ((g t) − (g r))` and expanding `V r` in the basis: the second
   piece is a sum of products `basis.repr (V r) p · D_p(r)` where `D_p(t) = 0`.
3. `mulVanish_deriv` — a product whose second factor **vanishes at the base point** needs
   only *continuity* of the first factor.  Proved through `hasDerivWithinAt_iff_tendsto_slope`
   (`slope (f·A) t r = f r · slope A t r` when `A t = 0`).

So the honest analytic input beyond the interface and the metric PDE is exactly
`ContinuousWithinAt V s t` — strictly weaker than the differentiability being concluded.
This is `vecCurve_deriv`, the analytic core; everything above it is bookkeeping:

* `metricRm04At_inner` — `Rm04(X,Y,Z,W) = g(Rm¹³(X,Y)Z, W)` for the own metric (the
  single-metric version of `rmDiffLowAt_eq_lowerTri`'s internal step `h₁`);
* `rmVec_deriv` — the invariant curvature instance;
* `rmVecComp_deriv` — consumes `Riemann04BTensorWithRicciDriftEvolutionInFrameOn` verbatim
  (one realization hypothesis `hreal`, saying the interface's component family *is* the
  own-lowered curvature — the same benign status as K2A's `hL₁`/`hL₂`), and concludes the
  `(1,3)` `HasDerivWithinAt` with speed
  `g(t)♯(roughLap − 2·B-comb − Ricci drift) + 2Ric(Rm¹³, ·)` raised;
* `rmDiffVec_deriv` — **the endpoint**: the difference of the two per-flow conversions is
  the derivative of `rmDiffVec` from `ForwardUniqueRmDot.lean`, i.e. *literally* the `hRm`
  hypothesis of `rmDiffLow_hasDerivAt`, hence (through that adapter) K3's `hS`.

Everything is stated with `HasDerivWithinAt … s t` for an arbitrary set `s`, so the caller
instantiates `s := D.carrier` (interface convention) or `s := univ`
(`hasDerivWithinAt_univ`, the `HasDerivAt` convention of `rmDiffLow_hasDerivAt`).

**What this retires:** the flow-2 half of the R4 mismatch at the `∂ₜ` level.  `rmDiffVec_deriv`
consumes only each flow's **own**-lowered interface and **own** metric PDE; no mixed lowering
appears.  The `hreal` fallback of `rmLowComp_deriv` is *not* needed on this path.

## Deliverable 2 (PARTIAL): the `[g₁♭, Δ₂]` commutator

### What is proved

* `metricNabla0S_self` — `∇^g g = 0` at the field level (the mission's "find or prove the
  small lemma"); the field-level companion of `nabla_metric_zero`, obtained through
  `totalNabla0SFun_apply_section` and the section-existence idiom.
* `nabla2_metric1` — **`∇²g₁ = −lapDiffFlux g₁ g₂ g₁`**, i.e. `∇²g₁ = −(∇¹ − ∇²)g₁`.
  This is the mission's "`∇²g₁ = −(A-action on g₁)`" *in the lane's own vocabulary*, and it
  makes the algebraicity free: `lapDiffFlux` is already known to be the algebraic action of
  the connection difference (`nabla0SFun_sub_cov`), with the quantitative form
  `lapDiffFlux_eval` / `fluxNormSq_le` already proved in `ForwardUniqueRmBounds.lean`.
  **No new estimate is needed for `∇²g₁`.**
* `sharpFlat` + `sharpFlat_self` + `mixLow_eq_rm04` — the carrier mismatch identified as a
  concrete operator: the `g₁`-lowered Riemann tensor of `g₂` (the background field `T₂` that
  K2.3's flux differentiates) is the own-lowered `Rm04₂` with its **last slot precomposed by
  the endomorphism `Φ = g₂♯ ∘ g₁♭`**, and `Φ = id` when the metrics agree.  This replaces the
  prose description of the gap by a checked identity.
* `lapCommFlux`, `lapCommRem`, `lapComm_eq_div_flux`, `lapComm_self` — the divergence-form
  organization: for any rank-indexed field operator `L`,
  `Δ_g(L T) − L(Δ_g T) = div_g(∇(LT) − L(∇T)) + (div(L ∇T) − L(div ∇T))`.

### Answer to the escalation question (ruling R4's stop gate)

R4 said: *"ESCALATION: if the ∇A-terms cannot be organized in divergence form on the
Tensor0S stack → short Pro re-consult."*

**They can, and the organization is structural — the gate should not fire.**
`lapComm_eq_div_flux` shows that for *any* operator `L` the commutator with `Δ_g = div_g ∘ ∇^g`
splits into `div_g(first-order ∇-defect) + (first-order div-defect)`, by exactly the
regrouping that `lapDiff_eq_div_flux` used in K2.3 (there the "content" was likewise not in
the identity but in the algebraicity of `U` and `R`).  No second derivative of the
`g₁♭`-gap and no derivative of the difference carrier can appear, because both carriers are
manifestly **first-order Leibniz defects**.

So the remaining work is *not* a route question and *not* a mathematical obstruction.  It is
one concrete missing computation, stated next.

### The one remaining frontier (classified: missing API / slot-bookkeeping, not mathematics)

> **Compute the first-order Leibniz defect of the re-lowering operator**, i.e. show
> `lapCommFlux g₂ (reLower g₁ g₂) T = −(∇²g₁-action on the lowered `T`)`, and likewise for
> `lapCommRem`.

Difficulty: the `(0,s)` stack has no `∇` of a mixed `(1,1)` field, so `Φ` cannot be
differentiated directly (`NablaOnTensors/Connection/Endomorphism.lean` is about *chart*
connection endomorphisms, not endomorphism fields — checked).  The workable route is to
represent the last-slot precomposition as a `g₂`-trace of a tensor product,

```
reLower g₁ g₂ T = domDomCongr τ (metricTraceFirstTwoField g₂ (domDomCongr σ (g₁ ⊗ T)))
```

(with `σ : Fin (2+s) ≃ Fin (2+s)` moving `g₁`'s second slot and `T`'s last slot to the front,
`τ` restoring the output slot order), and then differentiate through the three layers.  **All
three ingredients exist and were located:**

| step | lemma | file |
| --- | --- | --- |
| `∇` through `domDomCongr` | `totalNabla0SFun_domDomCongr` | `Tensor/RSTensor/NablaDomDomCongr.lean:110` |
| `∇` through the metric trace | `nabla_metricTraceFirstTwo0S` (+ `traceNablaShuffle`, `nablaRealizes_metricTraceFirstTwo`) | `Tensor/RSTensor/MetricTrace/NablaTraceGen.lean:504, 876, 997` |
| `∇` through the product (Leibniz) | `nabla0SFun_product_eval` (+ `nabla_product_zero_of_zero`) | `Tensor/RSTensor/ContractionLeibniz.lean:122, 289` |

plus `metricTraceFirstTwoField_product` / `_domDomCongr_gen` for the algebraic side.  The
cost is the slot bookkeeping (the two permutations, the `metricTraceInput` compatibility
condition of `_domDomCongr_gen`, and the lift of the *evaluated* `nabla0SFun_product_eval`
to a field identity via the `TotalNabla0SRealizes` layer) — estimated a few hundred lines,
i.e. its own brick.  It was deliberately **not** started here rather than left half-done or
hidden behind a hypothesis-shaped wrapper.

Deliberately **not** done: no `reLower` `def` was added, because an unverified slot layout
would be a polished public name with no checked content (house rule).  `mixLow_eq_rm04`
pins the intended semantics precisely enough for the next brick to define it correctly.

## Part 3 (the composed statement) — not attempted

It is gated on deliverable 2; `rmDiffComp_deriv`'s generic `T₁ T₂` instantiation is
unchanged and still available.

## Lean lessons from this pass

* **`Module.Basis`, not `Basis`.** `Basis.coord_apply` is `Module.Basis.coord_apply` in this
  Mathlib; the unqualified name fails with "Unknown identifier".  Dot notation
  (`basis.coord_apply l v`) is the robust form.
* **`Continuous.comp_continuousWithinAt` does not exist**; the available composition is
  `ContinuousAt.comp_continuousWithinAt`, so write
  `clm.continuous.continuousAt.comp_continuousWithinAt h`.
* **`HasDerivWithinAt.congr` direction.** `h.congr hs hx` rewrites the *goal's* function into
  `h`'s: `hs : ∀ y ∈ s, gGoal y = fKnown y`.  Passing the equalities symm-ed is the natural
  mistake here.
* **Do not `rw` an eta-expansion into the goal** (RmDot's recorded lesson, reconfirmed):
  `hv : Fin.cons (X x) (Fin.tail v) = v` must be rewritten *into the specialised `_apply`
  fact* (`rw [hv] at hsec`), never into a goal that still contains `v` inside `Fin.tail v`.
* **Vanishing-factor product rule.** Mathlib's `HasDerivWithinAt.mul` wants both factors
  differentiable; when one factor vanishes at the base point only continuity of the other is
  needed, and `hasDerivWithinAt_iff_tendsto_slope` + `slope_def_field` + `ring` proves it in
  ~8 lines.  Worth relocating to the analysis layer.
* The `Tensor0SSpace`-vs-CMM instance diamond did **not** bite in this file: every crossing
  is either `rfl` (`rmDiffVec … X Y Z = riemannOp … − riemannOp …`) or goes through
  `ContinuousMultilinearMap.ext`.  Field-level algebra (`abel`, `sub_eq_zero`) is well
  behaved, as `ForwardUniqueRmDiff.md` reported.
* Elaboration cost is modest (~15–20 s); `synthInstance.maxHeartbeats 1000000` is needed on
  the declarations mentioning `riemannOp` (inherited from `ForwardUniqueRmDot`'s CLM-tower
  budget problem), not elsewhere.

## Reuse / adaptation record

* **Reused directly:** `tensor02_expand` (`ForwardUniqueConnDot.lean:201`, public);
  `metricRm04At`, `riemannOp`, `riemannCurvature04At_apply_const`,
  `riemannCurvatureAux_tangentConst_eq_riemannOp` (the `rmDiffLowAt_eq_lowerTri` bridge
  pattern); `rmDiffVec` (`ForwardUniqueRmDot.lean`); `metricNabla0S`, `covDiv0SField`,
  `roughLap0SField`, `covDiv0SField_sub`, `lapDiffFlux` (`ForwardUniqueRmDiff.lean`);
  `basisInvMetric`, `tangentFlatEquiv_gen`, `tangentFlatEquiv_apply_gen`
  (`Tensor/RSTensor/CotangentRiemannian.lean`, `TangentRiemannianRealized.lean`);
  `nabla_metric_zero`, `metricTensorField` (`Tensor/RSTensor/MetricCompatibility.lean`);
  `leviCivitaConnectionOfMetric_isMetricCompatible`
  (`Geometry/Connection/LeviCivita/KoszulFormula.lean:1109`) — note `metricCov g` **is**
  `leviCivitaConnectionOfMetric g` definitionally, so no adapter was needed;
  `totalNabla0SFun_apply_section`, `ContMDiffSection.exists_eq_at_gen`;
  `Riemann04BTensorWithRicciDriftEvolutionInFrameOn`, `riemann04RicciDriftInFrame`,
  `FourComp`, `MatrixComp` (`Uhlenbeck.lean`).
* **Inspected and deliberately NOT used:** `basisInv_time`
  (`Tensor0SMetricDeriv.lean:527`, the `∂ₜg⁻¹ = −g⁻¹ġg⁻¹` producer) — it is `HasDerivAt`-only
  and the frozen-time reconstruction above removes the need for it entirely; and
  `inverseMetric_derivative_solve` (`Evolution/Metric/Covariant.lean:241`) for the same
  reason.  `LoweringIntertwinerRS` (`…/TensorDirichletCurrentGreenIdentityRS.lean`) is the
  *own*-metric lowering intertwiner (and is itself `sorry`-backed at `r > 0`), so it does not
  apply to the cross-metric commutator.
* **Copied privately (relocation TODO — protocol forbade editing existing files):**
  `metField0` (RmDot's private `metricField_slot0`, 3 lines).

## Relocation TODO for the campaign-end cleanup

* `raiseAt` / `raiseAt_eq` / `raiseAt_lower` → next to `basisInvMetric` in
  `Tensor/RSTensor/CotangentRiemannian.lean` (generic fiber-metric algebra, no Ricci-flow
  content).
* `metricNabla0S_self` → next to `nabla_metric_zero` in
  `Tensor/RSTensor/MetricCompatibility.lean` (it is the field-level form of that theorem)
  — this depends on `metricNabla0S` itself being relocated, which
  `ForwardUniqueRmDiff.md` §"Items for the planner" already logs.
* `mulVanish_deriv` → one-variable calculus layer (`Analysis/…`); it is not geometric.
* `sharpFlat` → the fiber-metric layer next to `tangentFlatEquiv_gen`.
* `metField0` → delete once RmDot's `metricField_slot0` is made public or relocated.
