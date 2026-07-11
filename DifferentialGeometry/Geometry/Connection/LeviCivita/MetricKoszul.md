# MetricKoszul

## Role

This module is the realization bridge between the model-space metric-jet
algebra in `Metric/TensorInner/MetricKoszul.lean` and the canonical
Levi--Civita connection.  It must remain connection-facing: it does not define
a second primitive Christoffel symbol.

## Current state

- `const_flat_eq_koszul` identifies the lowered Levi--Civita derivative of
  constant model-space vector fields with the coordinate Koszul covector.
- `const_cov_eq_koszul` raises the equality through an explicit coercive
  metric.
- `const_flat_eq_nhds` and `const_cov_eq_nhds` replace global coefficient
  equality by equality on a neighborhood of the evaluation point. This is the
  locality API needed after bump-extending a metric from an open ball.

Focused verification and the targeted build of the enlarged module passed
without proof or style warnings.

## Frontier

Consume `const_cov_eq_nhds` with the total bump extension of the normal-ball
metric. The remaining geometric bridge is then the cross-model pullback
naturality identification for the normal-ball diffeomorphism, rather than an
open-subtype constant-field theorem.
