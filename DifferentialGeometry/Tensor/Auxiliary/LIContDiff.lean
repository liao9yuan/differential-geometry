import RicciFlower.Tensor.Auxiliary.LIContDiff

/-!
# Compatibility wrapper for linear-isometry ContDiff lemmas

RicciFlower owns the active tensor auxiliary API in the mixed import graph.  This
legacy path re-exports `RicciFlower.Tensor.Auxiliary.LIContDiff` to avoid defining
`LinearIsometry.comp_contDiff_iff` twice.
-/
