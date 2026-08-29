# TangentAction

## 2026-08-29: support in the scalar argument

`action_tsupp_le` records the representation-independent support fact needed by
compactly supported weak Green formulas: the tangent action of a smooth vector
field on a scalar function is supported inside the scalar function's
topological support.  Outside that support the scalar function is locally zero,
so its manifold derivative vanishes.

Focused verification passed without warnings.  This is a reusable support
lemma, not a P1c Laplacian endpoint; no new axiom, assumption, instance,
notation, or placeholder was introduced.
