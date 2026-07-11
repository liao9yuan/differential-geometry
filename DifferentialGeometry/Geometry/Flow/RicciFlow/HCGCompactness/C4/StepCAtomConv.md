# StepCAtomConv

## 2026-07-09 quadratic readout convergence

- Added the calculus producer taking simultaneous `C^infty` convergence of a
  bilinear-form field and a vector-valued coordinate map to convergence of
  `B(v,v)`.
- Added the fixed smooth scalar postcomposition used by the intrinsic Step-C
  bump atoms.
- The remaining Step-C frontier is to supply, on one shared finite-hat
  subsequence, the concrete transition-map convergence inputs and then join
  them to the already extracted origin metrics.
- Added `normalMetric_zero`, the origin-only moving-centre metric extraction,
  and its finite-slot common-subsequence form.  The origin-only route avoids
  the unavailable uniform lower bound for full normal-coordinate domains.
- Added the overlap formula for intrinsic atoms and the concrete conditional
  `stepCAtom_conv` producer from one shared metric/transition subsequence.
- Added `cutRaw_conv`, `rawWeights_conv`, and `cutWeights_conv`.  The last
  theorem proves its own uniform denominator bound: covered atoms force one
  base-killed raw numerator to be at least `1/2`, and this passes to the limit.
- The finite-dimensional composition wrapper avoids the continuous-linear-map
  `ProperSpace` instance diamond without adding an artificial hypothesis.
- Added the totalized `seqCenterD`, eventual live/dead center equalities, and
  chart-pulled sequence atoms.  `seqAtom_live_conv`, `seqAtom_dead_conv`, and
  `seqAtoms_conv` use tail locality to give every finite slot its honest limit;
  dead slots are zero and never require artificial transition-domain inputs.
- Added `LiveSlot` and `existsLiveMetric0`, so origin metrics are extracted on
  exactly the finite live subtype along one further subsequence of `L.phi`.
- Added `seqAtomChart_smooth`, routing source-atom smoothness through the
  globally smooth intrinsic atom and the exponential chart's smooth ball.
- The canonical tail-locality lemma lives in `MapConvergenceDeriv.lean` as
  `MapCInfConvOnCompacts.congr_eventually` and was independently verified.
- The live/dead wrappers, finite-slot assembly, and live origin-metric
  extraction passed focused verification. The former upstream Derivation wall
  was repaired on 2026-07-10; this module and the downstream atom package now
  also pass targeted builds.
- Added `seqCenterD_subseq` and `seqAtomChart_subseq`, the reindex adapters used
  to keep final strict-subsequence expressions in public `L.subseq` form.

## Progress accounting

- This metric/atom/weight convergence sub-brick: 100%.
- `StepB1RawInput` producer theorem: 0% (not yet stated or proved).
- Dedicated Step-B1 machinery: about 63%.
- Chapter 4 machinery: about 66%.
- Whole HCG compactness machinery: about 46%.
- Conditional and final compactness endpoints: 0%.
