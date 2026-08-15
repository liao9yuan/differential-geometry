# Diagonal inverse branches

`DiagInvBranch.lean` packages a smooth inverse of the two-point intrinsic
exponential map near a chosen diagonal point.  The new
`DiagInvBranch.exists_source_tube` theorem makes its source control uniform:
there are a neighborhood `A` of the center and a number `δ > 0` such that, for
every `y ∈ A`, each tangent vector at `y` whose Riemannian length is less than
`δ` lies in the source of the diagonal inverse branch.

The proof works in a tangent-bundle trivialization, takes a product
neighborhood around the zero section, and uses a local operator-norm bound for
the trivialization.  This is genuine uniform moving-center control, rather
than a collection of pointwise normal-ball radii.

Focused verification, the targeted module build, the root aggregate check,
and direct axiom inspection passed.  The endpoint depends only on `propext`,
`Classical.choice`, and `Quot.sound`; the current full-project build is pending.

This theorem feeds the minimizing-branch adapters and the verified local
dimension-growth theorem `exists_slice_succ`.  It does not prove the maximal
dense convex-stratum theorem or the Soul theorem; both remain unstated and 0%.
