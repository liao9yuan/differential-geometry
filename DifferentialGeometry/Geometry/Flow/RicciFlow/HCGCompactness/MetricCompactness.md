# MetricCompactness

Source used: MSM135 Definition 3.5 and Theorem 3.9.

Introduced definitions: `PointedRiemannianCGMaps`, `MetricSourceDomain`, `MetricSourceData`, `MetricSourceCPConvOn`, `MetricCGConvergenceData`, `PointedRiemannianCGConverges`, `MetricCompactnessConclusion`, and `metricCompactness`.

Honest frontier: `metricCompactness` is the single HCG compactness `sorry`. It represents the Cheeger-Gromov compactness theorem, direct-limit/exhaustion construction, and smooth Arzela-Ascoli upgrade for pulled-back metrics.

2026-05-27 review update: the metric compactness layer now consistently uses the pointed Riemannian names. `MetricSourceData` also dropped its public `smoothPlus` field; source-domain `∞ + 1` is derived locally from the stored smooth manifold instance only at the low-level norm supremum.

2026-05-27 injectivity update: `metricCompactness` now carries `[I.Boundaryless]` because its `BaseInjBound` hypothesis is the HCG wrapper around the normal-coordinate injectivity-radius backend.

Verification: passed with the expected single `sorry` at `metricCompactness`.
