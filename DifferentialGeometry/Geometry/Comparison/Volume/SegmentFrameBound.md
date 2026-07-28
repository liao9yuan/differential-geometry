# SegmentFrameBound.lean

## Purpose

`expDens_le_hyp` assembles the sharp transverse Jacobi-density comparison with
the radial Gauss split and changes from the adapted frame to any supplied
pointwise `g`-orthonormal basis.

## Status

The theorem and its private change-of-frame helper are complete and focused
verification passes. The theorem includes the one-dimensional case without a
positive-transverse-dimension assumption.

The original `normalBasis` statement was rejected because the comparison layer's
independent model norm and the inner-product-induced norm are mathematically
equivalent but not definitionally equal. Applying `normalBasis` would therefore
change the `ModelWithCorners` type through the known topology diamond. The
invariant basis-parameter statement avoids that representation problem and adds
no geometric hypothesis: every finite-dimensional metric tangent fiber has such
a basis.

The private proof builds the normalized radial-plus-transverse adapted basis,
uses constant-frame densities to show the change-of-basis determinant has
absolute value one, then combines `jacDens_basis`, `radialJac_eq_vel`, and
`velJac_density_split`. In dimension one, the transverse Gram matrix is handled
directly as the unique empty matrix.

## Project position

- `expDens_le_hyp`: 100%; dedicated machinery: 100%.
- `segBall_vol_le`: 100%; its dedicated machinery is 100% and the endpoint is
  exact-verified in `SegmentPolar.lean`.
- `segBall_vol_rel`: theorem completion remains 0% while its body is still a
  `sorry`; dedicated strict-domain, area, radial-scaling, and cross-integral
  machinery is about 85%.
- `volInput_of_bg`: still transitively depends on the SegmentPolar frontiers, so
  unconditional endpoint completion remains 0%.

## 2026-07-27 radial-density scaling

Added `expDens_scale`.  For `t > 0`, an orthonormal full launch basis `B`, and
an orthonormal transverse frame `v` perpendicular to `u`, it identifies

`t^(n-1) * D_full(t•u, B, 1) = D_trans(u, v, t)`.

The empty transverse case `n-1 = 0` is included.  The proof uses the existing
private `fullDens_eq_trans` at `t•u`, then the public all-time
`transDens_scale`; it adds no geometric or consumer assumption.  Source
verification passes without warnings after the owning root lane refreshed the
newly exported `transDens_scale` artifact.
