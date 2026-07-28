# JacobiGram.lean

## 2026-07-17 Gram determinant calculus

Added the reusable curve-level objects `curveGram`, `curveGramDeriv`,
`curveMixedGram`, and `curveDensity`.  For a finite field family, the module
now proves Hermitian symmetry, the quadratic-form identity, positive
definiteness from fibrewise linear independence, positivity of the determinant
and density, and derivative formulas for the Gram matrix and its square-root
determinant density.

When the mixed Gram matrix is symmetric, `gramDeriv_eq_two` and
`hasDerivAt_symmDen` expose the factor-two form used by radial Jacobi/Riccati
arguments.  Focused verification and the explicitly named module build passed
without new warnings.

This is determinant calculus only.  On the selected normal-coordinate source,
linear independence should be a short consequence of the invertible
`expMapDiffeo` differential after the radial time-scaling bridge.  The
substantial Bishop--Gromov producer still missing is the shape-operator trace
Riccati inequality derived from the Ricci lower bound.

## 2026-07-27 Rectangular Gram congruence

Added `curveGram_rect` at the curve-Gram layer.  It allows distinct finite
source and target index types and proves that a recombination matrix
`C : Matrix ι κ ℝ` transforms the target Gram matrix to
`Cᵀ * curveGram V * C`.  The proof is the direct bilinear expansion and does
not use comparison geometry.  Focused verification passed.

This reusable algebra lemma is complete (100%).  It removed the square-index
restriction from the pole-normalization route.  `curveDensity_pole` was
subsequently proved in `SegmentPole.lean`; the active volume frontier is now
the L6/L7 segment-polar assembly.  The unconditional time-zero
`MetricCompactBase` endpoint remains 0%, since volume is only one of its
producer fields.

## 2026-07-27 Density continuity

Added `curveDensity_cont`.  Metric compatibility gives continuity of every
Gram entry from the same first-order curve/field hypotheses as
`hasDerivAt_gram`; product-topology continuity of the finite matrix, determinant
continuity, and square-root continuity then give continuity of `curveDensity`.
No linear-independence or determinant-positivity assumption is needed.

Focused verification passed without warnings.  This producer is complete
(100%).  Its immediate role is the endpoint step in the segment comparison:
prove the density inequality on `Ioo 0 1`, where the Jacobi family is
independent, and pass to `t = 1` from the left even if that endpoint is
conjugate.  `segBall_vol_le` itself remains unproved (0%); its dedicated
segment-polar machinery is about 58--62%.
