# Embedded slices

`EmbeddedSlice.lean` gives a metric-free local model for the smooth stratum
needed in convex shaving.  `IsEmbeddedSlice I d N` says that every point of
`N` has a smooth ambient coordinate neighborhood in which `N` is exactly a
finite-dimensional affine subspace of dimension `d`.  The local equality is
stored through `PartialEquiv.IsImage`, so it controls both inclusions and does
not depend on a chart sending the chosen point to zero.

The affine direction carries an explicit `FiniteDimensional` witness.  This
prevents an infinite-dimensional direction whose `finrank` defaults to zero
from masquerading as a zero-dimensional slice.  Empty sets still satisfy the
predicate, as for the usual empty submanifold convention; applications that
need a stratum must separately prove nonemptiness.

The file proves the basic semantic checks.  Every finite-dimensional affine
subspace of the standard model is an embedded slice.  Every open subset of a
finite-dimensional boundaryless manifold is a full-dimensional embedded
slice, and conversely every full-dimensional embedded slice is open.  Every
embedded slice is locally closed, even when the ambient model is not assumed
finite-dimensional.  The `image`, `inter_open`, and `image_inter` adapters
transport slices through ambient partial diffeomorphisms and open
restrictions.  `exists_param` extracts an exact local Euclidean
parameterization with injective derivative.

The maximal-dimension layer defines `sliceDims`, `maxSliceDim`, and
`maxSliceLocus`.  Singleton slices make the dimension set nonempty whenever
the carrier is nonempty, `IsEmbeddedSlice.dim_le` bounds it by the ambient
dimension, and `max_slice_dim_mem` proves that the supremum dimension is
attained.  `IsEmbeddedSlice.of_germ` glues exact local germs, which is the
metric-free input used to show that the maximal locus is itself an embedded
slice.

The implementation reuses the existing restricted-partial-diffeomorphism
constructor from `Geometry/Coordinates/ChartRegistration.lean`; it does not
depend on Mathlib's incomplete general smooth-embedding interface.

Focused verification, the targeted module build, and the root aggregate check
passed.  Direct axiom inspection of the new maximal-dimension endpoints reports
only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`.
Independent review found no mathematical or architectural blocker.  The
current full-project build is pending.

This file supplies the metric-free representation layer.  The verified
`max_stratum_spec` in `Comparison/ConvexStratum.lean` now assembles a nonempty,
embedded, relatively open and dense, connected, totally convex maximal locus.
The textbook-facing `exists_max_stratum` statement is also verified and adds
the local `IsTotallyGeodesic` conclusion.  The convex-stratum theorem is 100%.
The Soul theorem remains unstated and 0%, with dedicated machinery
approximately 48--52%.  The whole B1 lane is approximately 30--34%, and the
whole post-HCG Poincare program approximately 18--22%.
