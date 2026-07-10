# StepCAtomConv

## 2026-07-09 quadratic readout convergence

- Added the calculus producer taking simultaneous `C^infty` convergence of a
  bilinear-form field and a vector-valued coordinate map to convergence of
  `B(v,v)`.
- Added the fixed smooth scalar postcomposition used by the intrinsic Step-C
  bump atoms.
- This closes the algebraic composition part only.  The remaining Step-C
  frontier is to supply, on one shared finite-hat subsequence, the concrete
  normal-coordinate metric-at-centre and transition-map convergence inputs.
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
- Verification status: focused verification passed without warnings.

## Progress accounting

- This metric/atom/weight convergence sub-brick: 100%.
- `StepB1RawInput` producer theorem: 0% (not yet stated or proved).
- Dedicated Step-B1 machinery: about 58%.
- Chapter 4 machinery: about 62%.
- Whole HCG compactness machinery: about 45%.
- Conditional and final compactness endpoints: 0%.
