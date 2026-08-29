# BishopIntrinsicDeriv

## Mathematical route

`intrDen_deriv_le` differentiates the intrinsic Jacobi density on a
nonconjugate radial segment.  The checked Bishop ratio monotonicity at model
curvature zero makes the logarithmic density derivative no larger than the
Euclidean value `d / t`; the Jacobi Gram determinant formula then converts
this into the stated derivative inequality.

The auxiliary linear-independence argument is local: nonconjugacy makes the
intrinsic exponential differential injective, so it preserves an orthonormal
normal frame after radial scaling.  The Wronskian input is obtained from the
existing intrinsic Jacobi equation and zero initial fields.

That argument is exported as `intrJacobi_li`, with the same local hypotheses
as the former private helper.  Downstream radial-density consumers can now
reuse the nonconjugacy-to-linear-independence bridge directly instead of
duplicating its proof.

## Reuse

The proof reuses `intrRatioOfFrame`, `hasDerivAt_denRatio`,
`hasDerivAt_symmDen`, `hypMeanCurv_le`, the public orthonormal-frame
independence lemma, and the intrinsic Jacobi smoothness/ODE API.  It introduces
no new curvature or regularity assumptions.

## Verification

After exporting `intrJacobi_li`, focused verification passes without warnings,
and the explicit named module refresh also passes.  The declaration is ready
for downstream signed polar integration.
