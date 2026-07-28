# ChartBasisMetric

## 2026-07-27 extraction

The chart-basis metric evaluation and tangent-vector recomposition identities
were moved unchanged from `ChartMetric.lean` into this lower module.  Both use
only the chart Gram construction, so the module avoids the unrelated
Hessian/Laplacian and curvature import chain.

The focused source check passes without warnings.  `ChartMetric.lean` imports
this module and retains the same public declaration names.

