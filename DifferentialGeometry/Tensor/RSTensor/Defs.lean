import RicciFlower.Tensor.RSTensor.Defs

/-!
# Compatibility wrapper for realized tensor definitions

The RicciFlower RSTensor definitions are canonical in the mixed RicciFlower and
measure import graph.  This legacy path re-exports them so older
`DifferentialGeometry.*` modules can be imported without defining duplicate
global tensor objects.
-/
