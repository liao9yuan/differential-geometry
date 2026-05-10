import RicciFlower.Tensor.Alternating.Comp

/-!
# Compatibility wrapper for alternating-map composition

The RicciFlower tensor tree is canonical in the mixed RicciFlower/measure import
graph.  This legacy path re-exports the RicciFlower module to avoid duplicate
global declarations such as
`ContinuousAlternatingMap.compContinuousAlternatingMap₂`.
-/
