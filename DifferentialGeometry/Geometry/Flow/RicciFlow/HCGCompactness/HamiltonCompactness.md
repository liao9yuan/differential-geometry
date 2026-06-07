# HamiltonCompactness

Source used: MSM135 Chapter 3 theorem "Compactness for solutions"; MSM135 Chapter 4 was checked to identify the true proof backend.

Introduced theorem: `compactnessSol`.

`compactnessSol` is now the public solution-facing wrapper for MSM135 Theorem 3.10. It deliberately requires the metric time-zero compactness inputs, explicit spacetime derivative input, and a smooth-flow upgrade backend; it no longer claims compactness from only a zeroth-order curvature bound and basepoint injectivity.

`hamiltonCompactness` is now only a compatibility wrapper for the older local interface that still carries a separate `NoncollapseInput`. That noncollapse datum is not part of Theorem 3.10 itself; it belongs to the Section 12 route that will later produce injectivity/volume control from Perelman's theorem.

Honest frontier: the only HCG compactness `sorry` has been moved to `MetricCompactness.metricCompactness`, the metric Cheeger-Gromov compactness/direct-limit/Arzela-Ascoli frontier. The solution theorem reduces through that theorem plus explicit derivative and smooth-flow upgrade inputs.

2026-05-27 review update: after the pointed Riemannian rename, this file still remains a thin wrapper over `compactnessSol`.

2026-05-27 injectivity update: the public solution wrappers now carry `[I.Boundaryless]` because the real `FlowBaseInjBound` hypothesis uses normal-coordinate injectivity radius.

2026-05-28 legacy-input clarification: `_hinj : InjInput` and `_hnoncollapse : NoncollapseInput` are retained only for older wrapper compatibility. The contentful injectivity-radius input consumed by the theorem is `hflowInj : FlowBaseInjBound`.

Verification: focused checking passed.
