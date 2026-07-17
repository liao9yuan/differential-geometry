# StepB1MetricBridge

## Verified producer state

The source-chart coefficient lane is focused-green.

- `MapCInfConvOnCompacts.pullbackAlong` packages moving evaluation of a
  bilinear-form field, convergence of the derivative of a moving map, and the
  polynomial pullback contraction.
- `pullback_sub_norm` gives the order-zero perturbation estimate used by the
  direct all-pairs comparison.
- `HasStageJetData.coeff_tail` proves, on the retained `C0` core and under the
  honest smaller-source-ball point hypotheses already required by the stage
  jet tail, that the actual target-stage metric pulled back by the actual
  stage chart map is uniformly close to the source-stage normal metric.  It has
  one common rectangular tail in the source and target stage indices.
- `HasStageJetData.chart_conv` converts the retained all-order stage jet tail
  into `MapCInfConvOnCompacts` convergence to `id` along arbitrary cofinal
  source/target stage sequences, assuming eventual source membership on the
  fixed coordinate set.
- `HasStageJetData.pb_conv` combines that chart convergence with the retained
  moving normal metrics.  A compactly nested pair
  `closure V ⊆ W ⊆ interior (C0 alpha)` supplies the honest buffer needed
  to patch the finite prefix and apply the moving pullback theorem.  The actual
  pullback coefficients converge in `C^infinity` on `V` to `gInf alpha`.
- `HasStageJetData.pb_jet_tail` applies the generic bad-sequence extraction to
  obtain one rectangular all-pairs threshold through every requested finite
  derivative order on a compact `K ⊆ V`.

No new `MetricCompactnessInputs` field, endpoint radius assumption, glued
weight family, or chart selector was introduced.  A route through uniform
continuity of nested continuous-linear-map spaces was rejected because it
exposed an unnecessary instance diamond; the checked order-zero proof instead
uses the existing H6 `metricC 1` bound and a segment mean-value estimate.

## Next honest seam

The all-order theorem is conditional only on the local geometric premise it
actually needs: a rectangular tail on which the fixed larger coordinate patch
maps back into the smaller source ball.  The producer-owned intrinsic/source
buffer lane should discharge that premise on the finite local cover.  Once it
does, finite maximization over source charts gives the global compact source
tail.

After that local premise is wired, the remaining metric work is:

1. combine convergence of the pullback coefficients and the source-stage
   coefficients to obtain the finite-order coefficient difference directly;
2. convert those coordinate derivatives into the intrinsic
   `tensor02CovDerivNormWith` bounds on the finite chart cover;
3. repeat the bridge for the exact local inverse, not for the approximate
   reverse stage map.

The first item is local convergence algebra.  The second is the genuine new
chart-to-intrinsic covariant-tensor bridge.  The third depends on the separate
exact-inverse convergence lane.

## Honest accounting

- `HasStageJetData.coeff_tail`, `chart_conv`, `pb_conv`, and `pb_jet_tail`:
  proved and focused-green (100%).
- Arbitrary finite pullback-coefficient jets to the retained limit metric:
  proved (100%) once the stated local rectangular source premise is supplied.
- Direct arbitrary-order comparison with the moving source metric: theorem not
  yet stated (0%); its dedicated coefficient-convergence machinery is about
  80%.
- Chart-to-`tensor02CovDerivNormWith` producer: not started (0%); its dedicated
  local coefficient machinery is now available, but the intrinsic conversion
  remains open.
- Concrete `StepB1RawInput` producer: 0%.
- Textbook Step B1 theorem: 0%.
- Repository-wide rounded machinery estimates remain the project-map figures:
  about 95% for Step-B/B1, 87% for Chapter 4, and 60% for the whole HCG
  program.  These are infrastructure estimates; the HCG endpoint theorems
  remain 0%.
