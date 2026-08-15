# Immersed slice images

`ImmersedSlice.lean` supplies the finite-dimensional inverse-function bridge
used by the convex-stratum construction.  A smooth map on an open set whose
derivative is injective at a point restricts to a smaller open neighborhood on
which it is injective and whose image is an `IsEmbeddedSlice` of the source
dimension.

The construction complements the derivative range, augments the map to a
local diffeomorphism, and uses that diffeomorphism as the exact affine slice
chart.  The returned neighborhood contains the requested point and remains
inside the original smoothness domain, so the conclusion is not vacuous.  The
statement uses finite-dimensional completeness through inference and does not
carry a redundant `CompleteSpace` assumption on the source model.

This is the Euclidean immersion-to-slice producer used by radial cones.  It
does not produce the maximal convex stratum.  Focused verification, the
targeted module build, the root aggregate check, and direct axiom inspection
passed.  The theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`; the current full-project build is pending.

The convex-stratum theorem and the Soul theorem remain unstated and therefore
0%.  This file belongs to the dedicated local machinery for the now-verified
`exists_slice_succ` dimension-growth step.
