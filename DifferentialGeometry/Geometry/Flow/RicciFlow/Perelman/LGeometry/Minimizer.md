# Minimizing regularized L-curves

## Implemented surface

`lRegIndex_nonneg_var` proves nonnegativity for the transverse field of a
supplied smooth fixed-endpoint variation when its parameterized regularized
action has a genuine local minimum.

`lRegIndex_nonneg` upgrades this to every globally `C^8` tangent field along
the central regularized L-curve that vanishes at both endpoints. Its minimizing
hypothesis states directly that regularized action has a local minimum along
every smooth fixed-endpoint variation of the curve; it is not a supplied
semidefiniteness assumption or a frontier wrapper.

The proof realizes the field by the generic compactly supported geodesic-spray
flow, applies the variation-level second-derivative theorem, and then uses
`lRegIndex_congr` on the open interval. This last step handles endpoint
derivatives honestly rather than rewriting them from closed-interval equality.

## Verification and next frontier

Focused verification passes without warnings. The arbitrary-field index
nonnegativity theorem is complete. Compact-manifold existence of an actual
L-minimizer is a separate L5 frontier. The generic tree already contains
metric-valued absolute continuity, vector-valued `timeH1`, a weak-plus-uniform
`timeH1.compact_subseq`, and the genuine WeakSpace lower-semicontinuity theorem
`timeQuad_weak_lsc`. The L-specific `lAction_subseq` now also supplies a C0
subsequence for every uniformly action-bounded family on a compact manifold,
and `lAction_subseq_fix` preserves common endpoints. The generic adapters
`timeH1.ofContDiffOn` and `chartTimeH1` realize a C1 curve first in a linear
space and then in one fixed manifold chart.

What remains is the geometric realization layer: a canonical manifold-valued
H1/AC competitor representation, finite-chart localization and an overlap weak
chain rule, identification of the assembled weak chart velocity with
`lVelocity` and the moving quadratic action, and the Tonelli regularity
upgrade. Until that representation is chosen, adding `IsLAdmissible` or a
minimizer-existence wrapper would hide rather than solve the frontier.

`redVolume_anti` remains unstated and unproved at **0%**;
`lRegIndex_nonneg_var` and `lRegIndex_nonneg` are **100%**;
`exists_lMinimizer` is **0%**, with its dedicated direct-method machinery about
**35--45%**. Dedicated L-geometry machinery overall is approximately
**68--72%**, reusable generic prerequisites are approximately **97--99%**, and
the full Poincare program remains approximately **3--5%**.
