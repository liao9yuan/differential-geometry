# Minimizing branch

This module connects the Hopf--Rinow minimizing-vector selection to a local
diagonal inverse branch. The source-tube theorem gives uniform control near
the zero section, while continuity of the Riemannian extended distance makes
the selected minimizing vector small for point pairs near the diagonal.

`DiagInvBranch.minimizingVec_seg` keeps every nonnegative contraction of the
selected minimizing vector in the source, `minimizingVec_mem` records its
endpoint, and `inv_eq_minimizingVec` identifies the selected inverse with that
minimizing vector.  The framed projections `framed_symm_norm`,
`framed_smul_eq_join`, and `framed_smul_mem` then give, uniformly near the
diagonal, the exact norm-distance identity, the minimizing-join identity, and
source membership for every contraction.  Together these results remove the
moving-center quantifier gap that a pointwise normal-ball radius cannot
address.

Focused verification, the targeted module build, the root aggregate check,
and direct axiom inspection passed.  The public endpoints depend only on
`propext`, `Classical.choice`, and `Quot.sound`; the current full-project build
is pending.

This is branch-control infrastructure rather than the convex-stratum theorem.
It is consumed by `RiemannianMetricComplete.exists_slice_succ`, whose local
dimension-growth conclusion is verified.  The maximal dense-stratum theorem
and the Soul theorem remain unstated and therefore 0%.
