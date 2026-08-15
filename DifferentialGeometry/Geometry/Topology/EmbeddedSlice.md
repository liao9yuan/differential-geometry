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

The file proves three semantic checks.  Every finite-dimensional affine
subspace of the standard model is an embedded slice.  Every open subset of a
finite-dimensional boundaryless manifold is a full-dimensional embedded
slice, and conversely every full-dimensional embedded slice is open.  Every
embedded slice is locally closed, even when the ambient model is not assumed
finite-dimensional.

The implementation reuses the existing restricted-partial-diffeomorphism
constructor from `Geometry/Coordinates/ChartRegistration.lean`; it does not
depend on Mathlib's incomplete general smooth-embedding interface.

Focused verification of the new file, its targeted module build, and the root
aggregate check all passed without warnings.  Direct axiom inspection of all
four public theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx`.  Independent review found no mathematical
or architectural blocker; its only import-precision finding was removed and
the focused, targeted, and root checks were rerun successfully.  Full-project
verification is pending.

This is representation groundwork for the convex-stratum theorem, not that
theorem itself.  `exists_convex_stratum` remains unstated and 0%.  Its
dedicated local groundwork is now approximately 15--20%, while the Soul
theorem remains unstated and 0% with dedicated machinery approximately
34--35%.  The whole B1 lane remains approximately 22--25%, and the whole
post-HCG Poincare program remains approximately 15--20%.
