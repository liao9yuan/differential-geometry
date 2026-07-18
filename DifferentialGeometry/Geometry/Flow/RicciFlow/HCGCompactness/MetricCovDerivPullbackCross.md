# MetricCovDerivPullbackCross

## 2026-07-16: cross-model metric tower and norm naturality

The cross-model B/C intrinsic seam is now supplied at the metric-only layer.
The checked public API consists of:

- `metricCovDeriv_pullbackCross`, transporting the full background
  metric-covariant derivative tower through a diffeomorphism between different
  manifold models;
- `metricDiffCovDerivAt_pullbackCross`, transporting the difference of two
  metric towers;
- `normSq0S_pullbackCross_eval_of_orthonormal`, transporting the pointwise
  squared norm of any already-related covariant tensor;
- `metricDerivNorm_pullbackCross`, combining the preceding results into the
  pointwise metric-difference seminorm equality.

The tower proof is the metric-valued cross-model sibling of the established
same-model induction.  Its connection-correction terms use
`metricCov_pullbackCross`; its scalar derivative term uses a private
cross-model chain-rule specialization, since the existing public scalar helper
is same-model only.  No arbitrary-base tensor naturality API and no new
endpoint assumptions were introduced.

Focused verification and the targeted producer refresh passed without local
warnings or `sorry`.
