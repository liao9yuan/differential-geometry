# GramInvUniformEigenvalueLowerBound

## 2026-07-14 uniform low-regularity input

`chartInvGram_unif_lb` transfers the fixed-background compact-chart
Rayleigh lower bound to an arbitrary family that is pointwise
`Lambda`-equivalent to the background metric.  The proof realizes coordinate
vectors as one-covariant tensors and applies the intrinsic covector norm
comparison, so no matrix-inversion continuity argument is duplicated.

`chartInvGram_pou_lb` takes the finite minimum of those constants over the
canonical active `chartAtlasPOU_finset`.  Its conclusion supplies one positive
ellipticity constant simultaneously for every family member and every active
compact chart support.

This is the quantitative uniform-ellipticity producer required by a
low-regularity Ricci--DeTurck solver.  It does not provide that solver or a
uniform existence time.  The uniform low-regularity existence theorem remains
0%; its dedicated coefficient/input machinery is about 15% after this lemma.

Both family-uniform theorems pass focused verification without new warnings.
