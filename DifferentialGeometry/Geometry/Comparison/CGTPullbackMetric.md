# CGTPullbackMetric

## State — 2026-07-27

`intrPullBall`, `intrExpOn`, and `intrPullMetric` package the intrinsic framed
exponential ball as a genuine smooth Riemannian manifold whenever the ambient
exponential is a local diffeomorphism on that ball.  Whole-ball injectivity is
deliberately absent: the CGT argument needs a multi-sheeted pullback ball.

`intrExpOn_mfderiv` identifies the restricted differential with the ambient
intrinsic framed exponential differential, and `intrPullMetric_inner` proves
that the packaged metric is exactly `intrFrameMetric`.  The new
`intrPull_rm04` theorem then specializes the checked cross-model local
pullback naturality theorem: the lowered Riemann tensor is exactly the ambient
tensor evaluated on the four intrinsic framed exponential differentials.
`intrPull_pathLen` is the corresponding path-length naturality theorem for the
actual packaged `intrPullMetric`; the specialization avoids hidden
metric-instance choices at the CGT call site.

The current source is focused- and exact-green (`3862/3862`) and sorry-free.
The artifact contains `intrPull_rm04`, `intrPull_pathLen`, and the sharp
quadratic-bound addition.

Next producer:

1. apply the new quadratic bound to the pullback Jacobi endpoint pairing used
   by the Rauch--Whitehead comparison.

The local curvature transport is now API work already completed.  The next
genuine mathematical frontier is the Rauch/Whitehead strict-convexity theorem
used by the finite-orbit center in paper Lemma 4.6.

## Sharp pullback curvature quadratic bound

Added `intrPull_quad_le`.  At one point of the CGT pullback ball it transfers
the ambient pointwise `sqrt (normSq0S metricRm04At) <= K` hypothesis to

`gPull (R(J,V)V, J) <= K * gPull(J,J) * gPull(V,V)`.

The proof uses the canonical lower `rm04_eq_inner`, `intrPull_rm04`, and
`riemann_quad_le`.  It does not compare full tensor norms, choose a pullback
orthonormal basis, assume completeness of the open pullback ball, or require
connectedness.  Focused verification passed without diagnostics.

Honest accounting:

- CGT pullback metric packaging: theorem/API 100%, focused and exact current;
- local cross-model curvature transport: theorem/API 100%, focused and exact
  current;
- CGT-specific curvature identity: theorem/API 100%, focused and exact current;
- CGT pullback path-length naturality: theorem/API 100%, focused and exact
  current;
- sharp pullback curvature quadratic bound: theorem/machinery 100%, focused
  and exact current;
- pullback Jacobi endpoint positivity: theorem 0%, dedicated machinery about
  90%;
- paper Lemma 4.6: theorem 0%, dedicated machinery about 70%;
- pointwise CGT producer: theorem 0%, dedicated machinery about 65–70%;
- sequence `InjRadiusDecayInput` producer: theorem 0%;
- unconditional Theorem 3.9: theorem 0%;
- whole HCG supporting machinery: about 61%.
