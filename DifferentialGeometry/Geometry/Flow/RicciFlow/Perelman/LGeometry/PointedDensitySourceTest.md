# PointedDensitySourceTest

## Role

This module is the source-manifold change-of-variables adapter for the weighted
compact-chart theorem `redDensity_wgt_lim`.  It keeps one fixed nonnegative
model-coordinate weight and evaluates that weight through the inverse pointed
parametrization on each approximating manifold.

## Route

- Derive compact common-chart volume-density convergence, measurability, and a
  uniform bound from `ConvOut.volDens_compOn`, exactly as required by the
  weighted dominated-convergence producer.
- Apply `redDensity_wgt_lim` in the fixed preferred chart.
- Use `riemVol_param_lint`, `paramDens_src_eq`, and the left-inverse identity
  for `mapChartParam` to identify every approximating source integral.
- Use `riemVol_chart_lint` and the right-inverse identity for `extChartAt` to
  identify the limit integral.

The theorem does not assume compact-test convergence, tightness, total-mass
convergence, or no-mass-loss.

## Verification

Warning-free focused verification passed with one Lean thread after the exact
upstream `PointedDensityTest` refresh.  A direct axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  No named refresh or broader
build was run for this module.

## Remaining bridge

The next genuine fixed-space `C_c` step is a finite preferred-chart assembly:
pull the nonnegative and negative parts of a compactly supported real test
function into finitely many preferred charts, multiply them by a subordinate
partition of unity, apply `redDensity_src_wgt` chartwise, and sum.  That bridge
must also state the common fixed-space finite measures explicitly before
`mass_tendsto_of_cc` can apply; it must not assume compact-test convergence or
mass capture.

## Progress

- `redDensity_src_wgt`: theorem endpoint and dedicated source adapter 100%,
  warning-free focused GREEN and standard-three-axiom clean.
- Global fixed-space `redDensity_cc_lim`: not stated or proved, 0%; dedicated
  finite-chart assembly machinery is approximately 45%.
