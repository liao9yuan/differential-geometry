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

The implementation reuses the existing restricted-partial-diffeomorphism
constructor from `Geometry/Coordinates/ChartRegistration.lean`; it does not
depend on Mathlib's incomplete general smooth-embedding interface.

Focused verification, the targeted module build, and the root aggregate check
all passed without warnings.  Direct axiom inspection of the new
parameterization endpoint reports only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx`.  Independent review found no mathematical
or architectural blocker.  The current full-project build is pending.

This is representation groundwork for the convex-stratum theorem, not that
theorem itself.  `exists_convex_stratum` remains unstated and 0%.  Its
dedicated smooth-stratum machinery is now approximately 45%, including the
verified local dimension-growth theorem.  The Soul theorem remains unstated
and 0% with dedicated machinery approximately 38--40%.  The whole B1 lane
remains approximately 22--25%, and the whole post-HCG Poincare program remains
approximately 15--20%.
