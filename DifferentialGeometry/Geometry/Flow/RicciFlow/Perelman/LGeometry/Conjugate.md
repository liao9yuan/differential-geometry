# L-conjugate points

## Definition layer

`IsLConj` records both that `(Z, tau)` lies in the positive joint domain of
the L-exponential map and that its initial-tangent differential at `Z` is not
injective.  Keeping domain membership in the predicate prevents the totalized
off-domain value of `lExp` from creating artificial conjugate points.

The kernel-witness theorem `isLConj_iff` is finite-dimensional-free linear
algebra.  `isLConj_iff_jac` then uses the existing `lExpJacobi_eq` bridge to
identify the kernel with nonzero initial-tangent regularized L-Jacobi fields
vanishing at square-root time `sqrt tau`.  At a positive-domain nonconjugate
point, `lExpDeriv_inj` gives injectivity and `lExpDeriv_surj` uses equal finite
dimension to give surjectivity.

## Verification and frontier

Focused verification passes without warnings.  The module contains no
`sorry`, `admit`, new axiom, reference-tree import, or additional foundational
interface.

No first-conjugate-time infimum or index-positivity statement is introduced
here.  The next mathematical frontier is the endpoint-zero regularized
index/second-variation layer: the current dynamic Green and second-variation
theorems require a strictly positive lower backward-time endpoint, whereas
this conjugacy API is based at backward time zero.

Honest progress remains: `redVolume_anti` is unstated and unproved (0%);
the broader L4 phase is about 75--80%; dedicated L-geometry machinery is about
50--55%; reusable generic prerequisites are about 90%.
