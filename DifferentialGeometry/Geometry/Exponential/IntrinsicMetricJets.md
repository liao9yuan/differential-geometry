# IntrinsicMetricJets

## Role

This module is the geometry-layer bridge from intrinsic Jacobi launch jets to
ordinary Frechet derivatives of the intrinsic framed pullback metric.

## Status

The initial implementation defines the endpoint Gram jet and proves its
order-zero Gram identity. A trial global operator-valued smoothness wrapper was
removed after it exposed an avoidable elaboration wall: H6 already has
open-ball smoothness for the selected chart metric and equality with the
intrinsic metric there, which is the smaller honest interface.

The source now also proves `intrMetric_diag_jet`, identifying a repeated
direction evaluation of `iteratedFDeriv intrFrameMetric` with the corresponding
endpoint Gram jet. The apparent `whnf`/`isDefEq` performance wall was a real
instance mismatch: this file redundantly carried `[NormedSpace Real E]` beside
`[InnerProductSpace Real E]`, while `intrFrameMetric` canonically uses
`InnerProductSpace.toNormedSpace`. Removing the redundant binder eliminated the
timeouts without raising heartbeat limits. The affine composition is made
explicit at `z + 0 • a`, avoiding a separate basepoint unification search.

After refreshing `IntrinsicJacobiJets`, the endpoint identity required only a
local normalization repair: one `intrLaunchJ_at` rewrite normalizes both equal
metric slots, and the endpoint equality is closed through
`intrFrame_apply`, `expMapIntrinsic_def`, normal-frame linearity, and the
definition of `intrLaunch3`.

The complete source is focused-green with no local diagnostics.

## Next target

Exact-refresh this module, then focused-check
`H6MetricJet.intrMetric_deriv_le`, which transfers the diagonal estimate to
the full operator norm by polarization.

## Accounting

`exists_h6NormalData` is now stated but unverified and therefore remains
theorem-level 0%. `intrMetric_diag_jet` is proved and focused-verified; the
all-order H6 metric-jet route is about 90% complete in source.
