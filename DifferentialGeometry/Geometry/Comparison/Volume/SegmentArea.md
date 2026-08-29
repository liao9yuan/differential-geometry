# SegmentArea

## Mathematical route

`expJacDensity_nonneg` records the canonical sign projection for the
exponential Jacobian density.  The density is the square root of the Jacobi
Gram determinant, so nonnegativity is immediate and requires no geometric
hypothesis beyond those of the definition.

The signed exponential change-of-variables layer uses this lemma to simplify
the finite density `ENNReal.ofReal expJacDensity` back to a real scalar.

## Verification

Focused verification passed without warnings.  The theorem uses no new
assumptions or axioms; the two ambient instances unused by this projection are
explicitly omitted.
