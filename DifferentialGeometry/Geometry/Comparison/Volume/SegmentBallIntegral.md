# SegmentBallIntegral

## Mathematical route

The regular exponential image of `SegInt ∩ gBall` is contained in the
corresponding intrinsic ball.  `segBall_reg_zero` shows that the complement of
this image inside the intrinsic ball has zero Riemannian volume.  Therefore
signed set integrals over the ball agree with signed set integrals over the
regular image.  Combining this null-set replacement with
`segBall_int_polar` gives a full signed sphere-by-radius formula on an
intrinsic ball.  A separate support form replaces a global integral by the
same regular image when the integrand is supported in the ball.

These are measure-theoretic producers for the direct weak distance-Laplacian
proof.  They do not state or assume that endpoint.

## Verification

Focused verification passes without warnings.  The first check failed only on
three local elaboration shapes: reducing an image-membership goal, naming the
measurable universal set, and choosing the set-only integrability monotonicity
lemma.  The mathematical route and public assumptions were unchanged.

The ambient manifold binder now states the smooth grade actually used by the
proofs.  Its earlier outer-top annotation accidentally exported the stronger
analytic grade and blocked the smooth radial-integral consumer.  Focused
reverification now passes without warnings, and the downstream-required
targeted named refresh also passes.

## Project status

All formal P1c endpoints remain unstated and therefore 0% complete.  This file
only advances dedicated Laplacian-comparison machinery.
