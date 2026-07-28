# Rm04OperatorBound

## 2026-07-27 intrinsic curvature-operator estimate

Added the reusable pointwise estimate `riemannOp_sq_le`.  It bounds
`|R(J,V)V|_g^2` by the intrinsic fiber norm of `metricRm04At`, the squared
lengths of `J` and `V`, and one explicit dimension factor.  The statement has
no exponential-map, radial-coordinate, compactness, or Ricci-flow hypotheses.

This is dedicated H6 machinery, not the H6 radius-profile theorem itself.  The
next consumer is the intrinsic Jacobi ODE estimate in `IntrinsicGronwall`.
Focused verification passed without diagnostics.  The first exact refresh also
passed; a final no-warning refresh remains after removing an unused private
`Fintype` binder.

## 2026-07-27 sharp sectional adapter

Added `riemann_quad_le`, the dimension-free scalar companion to
`riemannOp_sq_le`.  Given an orthonormal basis and a pointwise bound

`sqrt (normSq0S metricRm04At) <= K`,

it proves

`g(R(J,V)V,J) <= K * g(J,J) * g(V,V)`.

The theorem deliberately consumes the pointwise bound rather than importing
the higher `Rm04GlobalBound` package from the volume-comparison layer.  The CGT
Rauch wrapper will supply that pointwise premise via `hRm q`, avoiding an import
cycle and preserving the curvature module as the canonical lower home.

The new theorem is focused- and exact-green with no local diagnostics.  Its
export is current for the geometric endpoint-positivity consumer.

## 2026-07-27 canonical lowered-curvature readout

Promoted the lower-layer identity `rm04_eq_inner`, which identifies
`metricRm04StdAt g q J V V W` with the metric pairing of `W` and
`riemannOp (LeviCivita g) q J V V`.  This is the canonical adapter needed by
the CGT pullback-metric curvature estimate; it avoids importing a
HCG-specific duplicate into the geometry layer.

Focused verification passed without diagnostics.  The declaration itself and
its dedicated machinery are 100%; the pullback quadratic-curvature consumer
remains unstated (0%) until it is added to `CGTPullbackMetric`.

Honest accounting:

- `riemann_quad_le`: theorem 100%; dedicated machinery 100%.
- intrinsic geometric endpoint positivity: theorem 0%; dedicated machinery
  about 75%.
- `intrLoop_ge_cgt`: theorem 0%.
- whole HCG supporting machinery: about 61%.
