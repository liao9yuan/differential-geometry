# Cone slices

`ConeSlice.lean` implements the Euclidean radial-cone step used in the Sakai
convex-stratum route.  `coneDeriv` is the derivative of `(x,t) ↦ t • f x`.
If the base derivative is injective, the scale is nonzero, and the radial
vector is outside the derivative range, then this cone derivative is
injective.  `exists_cone_slice` and `exists_cone_image` turn that fact into a
local embedded slice of dimension `finrank F + 1`, before or after an ambient
partial diffeomorphism.

`radial_not_range` is the genuine first-order transversality producer: a
nonzero radial vector at a local minimum of squared norm cannot lie in the
parameter derivative range.  `radial_local_min` transports a distance
minimizer through a radial chart whose coordinate norm equals distance.  The
finite-dimensional cone endpoints infer source completeness and do not carry
a redundant `CompleteSpace` assumption on that source.

Focused verification, the targeted module build, the root aggregate check,
and direct axiom inspection passed.  The main cone-image endpoint depends only
on `propext`, `Classical.choice`, and `Quot.sound`; the current full-project
build is pending.

The local dimension-growth theorem `exists_slice_succ` is now stated, proved,
and verified; this file supplies its finite-dimensional cone producer.  The
uniform diagonal branch and minimizing-logarithm bridge are supplied by
`DiagInvBranch.exists_source_tube` and `Comparison/MinimizingBranch.lean`.
The maximal dense-stratum theorem and the Soul theorem remain unstated and
therefore 0%.
