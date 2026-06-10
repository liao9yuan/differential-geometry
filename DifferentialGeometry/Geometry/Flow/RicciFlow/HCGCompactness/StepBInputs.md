# StepBInputs.lean — Step B honest input (S6 / lbl418), native rebuild

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
