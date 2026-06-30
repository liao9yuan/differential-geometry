# SolutionPullback.lean — P1.4: the pulled-back Ricci-flow solution `Φ^* S`

End goal context: this file builds `isSolutionOn_pullback` (the full 9-field
`IsSolutionOn` for `t ↦ Φ^*(S.metric t)`), which `SolWindowData.mk` consumes
(`hS : ∀ i, IsSolutionOn (S i)`) to feed `winGInfOfData` → the **conv field**
(g_∞ assembly), the last gap of MSM135 Ch4 Thm 3.10 ⇐ 3.9 (HCG compactness).

## VERIFIED (build green, 3877 jobs) — bundle-section pullback frontier CROSSED

**2026-07-01 — the continuity frontier is DONE.**  The keystone
`Tensor0SFamilyContinuousOnSet.pullback` (in `Curvature/Realized/MetricFamilyContinuity.lean`)
LANDED (verified) and is consumed here.  Last session's "bundle-section pullback frontier / three
coded route failures" was a FALSE wall: the survey missed the converse builder
`tensor0SFamilyContinuousOnSet_of_chartBasisComp`, which already existed in that file.  With it,
`pullback` is ~30 lines and all three continuity fields fall out.

Fully-done IsSolutionOn fields (7): `equation`, `scalarCont`, `scalarTime`, `ricciNormSpace`,
`ricciCont`, `rm04Cont`, `smoothConnection`.  Plus `smoothMetric` 3/4 (`coeff`, `coeff_cont`,
`metricTensor_cont`).  REMAINING (the SMOOTH-transport frontier, below): `frameCompSmooth`
(smoothMetric's 4th sub-field) and `ricciNormGrad`.  Reusable bricks banked: `metricScalarAt_pullback`,
`metricRicci_pullback_eval`, `metricRm04_pullback_eval`, `scalar_pullback`, `ricciNorm_pullback`,
and `Tensor0SFamilyContinuousOnSet.pullback` itself.

The three continuity consumers (all via `pullback` + `Tensor0SFamilyContinuousOnSet.congr`, `ext slots`,
`compContinuousLinearMap_apply`): `metricTensor_cont` (+ `metricTensorField_apply` + `pullbackMetric_inner`,
with a `hm : (sop).family.metric t = pullbackMetric (S.family.metric t) Φ := rfl` to expose the metric),
`ricciCont_pullback` (+ `metricRicci_pullback_eval`), `rm04Cont_pullback` (+ `metricRm04_pullback_eval`,
the `(0,4)` analog of `metricRicci_pullback_eval` via `metricRm04_apply`/`metricRm04StdAt_apply` +
`metricRm04Std_pullback`).  `smoothConnection_pullback` needs NO transport — it's the general
`leviCivitaConnectionOfMetric_contMDiffCovariantDerivative` of `Φ^*g_t`.


- `solutionOn_pullback S Φ` — the data `{ base := { metric := t ↦ Φ^*(S.base.metric t) } }`.
  Needs `[SigmaCompactSpace M][T2Space M]` (for `Diffeomorph.pullbackMetric`).
- `pullback_coeff_eq` (private) — the pointwise coeff identity
  `((Φ^*S).family.metric t).inner x X Y = (S.family.metric t).inner (Φx)(dΦX)(dΦY)`
  (funext + `Diffeomorph.pullbackMetric_inner`).  **Needs `[SigmaCompactSpace N][T2Space N]`
  too**, because `S.family` invokes `SolutionOn.metricCompatible` →
  `leviCivitaConnectionOfMetric_isMetricCompatible` (on N).
- **`metricVariationEquation_pullback`** (the `equation` field) — sorry-free.  THE analytic
  heart.  `intro t x X Y` (NB: `RegularTime D` is a bundled subtype — 4 binders, NO `ht`);
  `rw [hcoeff (= pullback_coeff_eq), hric]; exact hS.equation t (Φx)(dΦX)(dΦY)`.  `hric`
  bridges the Ric value: `toTensorField_apply` (both sides) → `show metricRicciAt …` (defeq:
  `.ricciAt` unfolds to `metricRicciAt`) → `metricRicciAt_apply_eq_ricciTensor` (both sides)
  → `ricciTensor_pullback` (the hard-won P1.3 M≃N Ricci naturality).
- `metricFamilySmoothOn_pullback` — `coeff` ✓ and `coeff_cont` ✓ (both: `rw
  [pullback_coeff_eq]; exact hS.smoothMetric.coeff (Φx)(dΦX)(dΦY)` — the fixed point/vectors
  make this a pure rewrite, NO composition).  `metricTensor_cont` + `frameCompSmooth` = sorry
  (the bundle frontier below).
- **`metricScalarAt_pullback`** (in MetricCovDerivPullback.lean, next to `ricciTensor_pullback`) —
  the reusable scalar-curvature naturality `metricScalarAt (Φ^*g) x = metricScalarAt g (Φx)`.
  Mirrors `normSq0S_pullback_eval_of_orthonormal`'s setup (`dPhi`/`basis'`/`hON'`/`hinv`/`hinv'`
  via `metricInverseInBasis_of_orthonormal`+`identityInvMetric`), then `metricTracePair0SAt_eq_sum_basis`
  both sides + per-summand `metricRicciAt_apply_eq_ricciTensor` + `ricciTensor_pullback`.
  GOTCHAS: needs `set_option maxHeartbeats 400000`; `congr 1` whnf-times-out on the tensor
  terms → use a `have hric … ; rw [hric]` instead.
- **`scalar_pullback`/`scalarCont_pullback`/`scalarTime_pullback`** (the `scalarCont`+`scalarTime`
  fields) — sorry-free.  `scalar_pullback` = `simp only [SolutionOn.scalar, SolutionFamily.scalar,
  solutionOn_pullback]; exact metricScalarAt_pullback …` (needs `maxHeartbeats 1000000` — the
  `metricScalarAt`-of-two-`pullbackMetric`-structures defeq is heavy).  `scalarCont_pullback`:
  rewrite to the EXPLICIT `g ∘ f` form (`(fun p => S.scalar p.1 p.2) ∘ (fun q => (q.1, Φ q.2))`)
  so `hS.scalarCont.comp` matches SYNTACTICALLY — do NOT leave it as `fun q => S.scalar q.1 (Φ q.2)`
  (that makes `.comp` reduce `metricScalarAt` and time out).  `scalarTime_pullback`: fixed `x`,
  `rw [heq]; exact hS.scalarTime htK hKsub (Φx)`.

## CONTINUITY FRONTIER RESOLVED — the "three coded route failures" were a FALSE wall

Last session reported a "genuine three-strike" on the bundle-section pullback transport (three coded
routes — `continuousAt_totalSpace`, `clm_bundle_apply`+pullback-bundle, `.congr`/section-from-components
— each failing).  **That was wrong: the converse builder already existed.**
`tensor0SFamilyContinuousOnSet_of_chartBasisComp` (in `Curvature/Realized/MetricFamilyContinuity.lean`,
since 2026-06-13) builds bundle continuity FROM frame-component continuity — exactly the "section
continuous ⟺ frame components continuous" tool route 3 claimed was missing.  With it,
`Tensor0SFamilyContinuousOnSet.pullback` is ~30 lines (now landed there, verified).  Lesson: a survey
that concludes "no converse builder exists" must `grep` the realized-curvature continuity file before
declaring a wall — the three "coded failures" all attacked the predicate from the WRONG side (trying to
deconstruct total-space continuity) instead of the component-CONSTRUCTOR side.

## THE REMAINING FRONTIER — SMOOTH-transport (`frameCompSmooth`, `ricciNormGrad`)

`frameCompSmooth` (smoothMetric's 4th sub-field) reduces (in-code, after `pullbackMetric_inner`) to:
`ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞ (fun p => (S.family.metric p.1).inner (Φ p.2) (dΦ(frame i p.2))
(dΦ(frame j p.2))) (D.regular ×ˢ u)` — joint `(t,x)` smoothness of the metric coefficient with
`dΦ`-pushed frame inputs across `Φ`.  This is a genuine SMOOTH-transport gap (NOT a false wall like the
continuity one — checked):
- The continuity proof used `Tensor0SFamilyContinuousOnSet.eval_continuous`, which has a BASE MAP `b`
  and parameter space `P` (so `b := Φ`, `P :=` time×source works).  The smooth analog
  `TensorMultilinear.contMDiff_section_apply` (BundleSmoothEval.lean:477) is SINGLE-MANIFOLD / SPATIAL
  ONLY — no base map, no time parameter.  So the clean `pullback`-mirror does not transfer.
- The alternative (push the `M`-frame to an `N`-frame on `Φ '' u`, then `hS.smoothMetric.frameCompSmooth`)
  needs a pushforward-`IsLocalFrameOn`-under-a-diffeomorphism lemma — does NOT exist in-tree (only
  CHART-pushforward frames exist).

Smallest unblock options (pick at execution): (a) build the SMOOTH analog of `eval_continuous` — a
joint `(t,x)` `ContMDiffOn` section-eval with a base map `b : P → N` and `ContMDiff` vector inputs
(mirror `eval_continuous`'s proof but `ContMDiff`), feeding a jointly-`ContMDiff` metric tensor section
over `N` built from `hS.smoothMetric.frameCompSmooth` via Mathlib `contMDiffOn_iff_localFrame_coeff`;
or (b) build `pushforward IsLocalFrameOn` under `Φ` (`dΦ ∘ frame ∘ Φ⁻¹` is a C∞ local frame on `Φ '' u`)
and compose `hS.smoothMetric.frameCompSmooth` with `(t,x) ↦ (t, Φ x)`.  `ricciNormGrad` is the other
smooth field: gradient-field naturality (`grad(Φ^*g)(f∘Φ) = dΦ⁻¹(grad g f ∘ Φ)`) + bundle smoothness —
a separate smooth-transport piece.

Both are flagged here per the handoff ("if that becomes a new smooth-transport frontier, stop and report
cleanly rather than adding polished assumptions"), not pushed with assumptions.

## Honest denominator

P1.4 ≈ **7/9 IsSolutionOn fields fully verified** + `smoothMetric` 3/4 — done: `equation` (analytic
heart, the only one needing the hard `ricciTensor_pullback`), `scalarCont`, `scalarTime`,
`ricciNormSpace`, **`ricciCont`, `rm04Cont`** (via the now-landed `pullback`), **`smoothConnection`**
(general LC smoothness), and `smoothMetric` `coeff`/`coeff_cont`/**`metricTensor_cont`**.  Remaining =
`frameCompSmooth` + `ricciNormGrad` (the SMOOTH-transport frontier above) → then assemble
`isSolutionOn_pullback`.  Reusable bricks banked: `Tensor0SFamilyContinuousOnSet.pullback` (the keystone),
`metricScalarAt_pullback`, `metricRicci_pullback_eval`, `metricRm04_pullback_eval`, `scalar_pullback`,
`ricciNorm_pullback`.  P1.4 is one brick of the g_∞ conv field, itself the last gap of 3.10⇐3.9, itself
part of Ch4 HCG (~25% overall).

## Verification

`lake-locked check`/`lake env lean` reports real ERRORS reliably but is FALSE-GREEN on closure;
the `lake-locked build +…SolutionPullback` (3875 jobs) is authoritative (1 sorry-warning =
metricFamilySmoothOn_pullback's 2 bundle fields).  NEVER run a second Lean process alongside a
build (olean corruption — see [[lake-env-lean-false-green]]).
