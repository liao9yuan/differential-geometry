import RicciFlower.VectorBundle.Equiv

/-!
# Compatibility wrapper for vector-bundle equivalences

The active RicciFlower tree keeps the canonical definitions of `VectorBundleHom`,
`VectorBundleEquiv`, and their API.  This legacy import path re-exports that module
so downstream `DifferentialGeometry.*` files do not define a second copy of the same
global declarations when imported together with `RicciFlower.*`.
-/
