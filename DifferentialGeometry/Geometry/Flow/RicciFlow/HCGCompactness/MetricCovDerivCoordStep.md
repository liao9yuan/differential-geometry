# MetricCovDerivCoordStep.lean — coordinate-frame recursion for the metric covariant tower (P3 Gap B)

**Status (2026-06-13): DONE + verified** — focused check + targeted build (3629
jobs) green; both lemmas `#print axioms` clean (`propext, Classical.choice,
Quot.sound`).

## What landed

Two lemmas turning the `metricCovDeriv` tower's `a → a+1` step into an explicit
coordinate-frame component recursion, the algebraic heart of the single-`φ`
Gap-B induction.

- `metricCovDeriv_succ_apply_section (h gRef a X x slots)`:
  `metricCovDeriv h gRef (a+1) x (Fin.cons (X x) slots) =
   nabla0SFun (a+2) (leviCivita gRef) X (metricCovDeriv h gRef a) x slots`.
  One-line `rw [metricCovDeriv_succ, metricCovDerivStep_apply,
  totalNabla0SFun_apply_section]` — the existing `MetricCovDerivLinear` rfl
  lemmas (`metricCovDeriv_succ`, `metricCovDerivStep_apply`) handle the
  `(a+2)+1 = (a+1)+2` index juggling, so NO Nat-cast pain.  This is the
  general-`a` analogue of `metricCovDeriv_one_apply_section`.

- `metricCovDeriv_succ_component_coordFrame (h gRef a x I0)` with
  `I0 : Fin (a+3) → CoordinateIdx E`:
  `component0S (coordinateFrameAt_toBasis x) (metricCovDeriv h gRef (a+1) x) I0 =
     coordDeriv0SAt (coordinateFrameAt x (I0 0)) x (metricCovDeriv h gRef a) (tail I0)
     − Σ_p Σ_k Γ^k_{(I0 0)(tail I0 p)} · coordComponent0SAt (metricCovDeriv h gRef a x)
                                            (update (tail I0) p k)`,
  the `Γ` being `christoffelAlongInFrame` of the `gRef` Levi-Civita connection.
  Proof = producer (2) `nabla0SFun_eval_coordFrame` (from `CoordFrameStep.lean`)
  specialised to `α = metricCovDeriv h gRef a`.

## Route / Lean gotchas

- The leading derivative slot of `nabla0SFun` needs a GLOBAL `ContMDiffSection`,
  but the coordinate frame is only local.  Resolved by the SAME pattern as
  `metricCovDeriv_one_eval_localFrame`:
  `(coordinateFrameAt_isLocalFrame x).exists_contMDiffSection_eqOn_nhd` gives a
  global `sec` agreeing with `coordinateFrameAt x ·` near `x`; use `X := sec (I0 0)`.
- Both producer (2)'s directional term (`coordDeriv0SAt`, = `mfderiv … (X x)`)
  and its Christoffel term (`christoffelAlongInFrame … (X x) …`) depend on the
  leading slot ONLY through `X x`.  So the bridge back to the actual frame value
  is a single rewrite `hsecx : sec i x = coordinateFrameAt x i x`:
  `simp only [hsecx]` clears the Christoffel directions; a small `hcd`
  (`simp only [coordDeriv0SAt]; rw [hsecx]`) clears the directional term.  No
  germ/derivative bridge needed — that is the payoff of producer (2) being a
  pure pointwise-direction formula.
- Slot reshaping `(fun q => coordinateFrameAt x (I0 q) x) =
  Fin.cons (sec (I0 0) x) (fun p => coordinateFrameAt x (tail I0 p) x)` by
  `funext`/`Fin.cases`; the `succ` branch closes with `Fin.cons_succ` then `rfl`
  (`Fin.tail I0 p ≡ I0 p.succ`).

## Placement

New file in HCGCompactness importing `MetricCovDerivLinear` (tower rfl lemmas +
`metricCovDeriv`) and `Geometry/Coordinates/NablaComponents/CoordFrameStep`
(producer 2).  `metricCovDeriv_succ_apply_section` could fold into
`MetricCovDerivLinear` next to `metricCovDerivStep_apply`; kept here to avoid
rebuilding that file's dependents during the Gap-B push.

## Next (Gap B remaining)

The convergence induction `componentConv_covDeriv_of_chartCInf` now has its
per-step algebra: feed this recursion's directional term to **B2**
(`MapCInfConvOnCompacts.fderivApply`) and its Christoffel sum to **mulLeft+sum**
(producer 3) + IH, along the single `φ` from B0
(`exists_engine_frameCInfConv`).  Then finite-cover `hnorm`
(`metricDerivNorm_le_compSq_uniform`) → `metricPreconvInf`.
