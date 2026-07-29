# BoundedGeometry

## 2026-07-26 curvature recursion projection

Added `curvCovDeriv_succ`, the cheap public successor equation for the
dependent static curvature tower.  It is definitionally true and focused- and
exact-verified.  Downstream arity bridges can now rewrite or evaluate this
projection without unfolding the raw `Nat.rec`.

## 2026-07-28 arbitrary-slot curvature bound

Added `curv_apply_le` and `HasCurvDerivBound.apply_le`.  They project the
canonical `normSq0S` bound for `nabla^k Rm` to an estimate on arbitrary tangent
slots, using the frame-free tensor Cauchy-Schwarz theorem.  No new geometric
assumption was introduced.

Added `curvOne_apply` and `HasCurvDerivBound.nablaRiemannOp_le`.  The former
identifies the first lowered curvature derivative with the metric pairing
against the pointwise vector-valued covariant derivative of the Riemann
operator.  The latter cancels that final metric-length factor and gives the
dimension-free vector norm bound needed by the differentiated Jacobi equation.
The data structure and its hypotheses are unchanged.

Added the matching order-zero pair `curvZero_apply` and
`HasCurvDerivBound.riemannOp_le`.  They identify the lowered Riemann tensor with
the metric pairing against `riemannOp` and derive its dimension-free vector
norm bound by the same quadratic cancellation.  This supplies the C0 estimates
for the four lower curvature terms in `jacVarForce`; one of those terms carries
the scalar coefficient two.

Focused verification passed, and the exact artifact is current (`3930/3930`).
This closes the routine H6 C0/C1 norm-to-vector projection gap.
`NormalRadiusProfile` and
`exists_h6NormalData` remain theorem-level 0%; their dedicated all-order
Jacobi/metric-jet machinery is about 53%, the native H6 producer machinery is
about 68%, and the whole HCG compactness machinery is about 62%.  The
unconditional compactness endpoint remains theorem-level 0%.

## 2026-07-25 time-slice projection

`FlowDerivBounds.at_time` now restricts the existing spacetime
curvature-derivative bounds to `SeqBoundedGeometry` at any carrier time.  This
is a direct projection, not a new analytic assumption.  Focused verification
passed.

The projection is 100% complete.  It removes the separate time-zero packaging
gap once a genuine `FlowDerivBounds` producer is available; it does not itself
prove the Hamilton source bounds.  `ham3_cgh_limit` remains theorem-level 0%,
and whole HCG supporting machinery remains about 60%.

Source used: MSM135 Definition 3.8 and the bounded-curvature assumptions in Theorems 3.9 and 3.10.

Introduced definitions: `curvCovDerivStep`, `curvCovDeriv`, `curvDerivNormSq`, `curvDerivNorm`, `HasCurvDerivBound`, `BoundedGeometry`, `SeqBoundedGeometry`, `HasSpacetimeCurvBound`, `HasSpacetimeCurvDerivBound`, `SpacetimeCurvBound`, `FlowDerivBounds`, and `FlowDerivativeInput`.

Design note: bounded geometry is derivative-order indexed. `HasCurvDerivBound` is no longer an opaque predicate: it unfolds to a global pointwise bound on `curvDerivNorm`, defined from the canonical metric Riemann tensor, iterated `totalNabla0S`, and the metric-induced `normSq0S`. The flow derivative bound is a spacetime family of spatial curvature-derivative bounds on the time-slice metrics.

2026-05-27 correction, updated 2026-07-09: removed the vague curvature-bound axioms. The canonical conditional solution-compactness route needs `FlowDerivativeInput` and concrete `FlowUpgradeData`; the former exact-conclusion `SmoothFlowLimitInput` package has been deleted. The curvature-bound fields have concrete norm content.

Verification: passed.

2026-07-08 volume-comparison bridge: added `rm04Bound_of_curv0`,
`rm04Bound_of_geom`, and `rm04Bound_of_seq`.  These show that the zeroth-order
`HasCurvDerivBound`/`BoundedGeometry` inputs supply
`VolumeComparison.Rm04GlobalBound`, the named global Rm04 predicate consumed by
the local ball-volume comparison endpoint.  This is only the curvature-bound
producer bridge; it does not yet apply the full volume theorem to pointed
metric objects or instantiate `VolumeComparisonInput`.

Verification: passed for `BoundedGeometry.lean`.

2026-07-08 D6 input threading: added `SeqBoundedGeometry.subseq`, the
reindexing wrapper that carries uniform curvature-derivative bounds through a
subsequence.  This supports later D6 assembly after Step A/D diagonal
subsequences; it does not prove the volume-comparison producer from bounded
geometry.

Verification: passed for `BoundedGeometry.lean`.
