# Intrinsic ball diffeomorphisms

`IntrinsicBallDiffeo.lean` upgrades fixed-first intrinsic exponential branches
to all-order framed partial diffeomorphisms and packages controlled whole-ball
charts.

`ExpInvBranch.exists_radial_ball` now shrinks any framed branch containing the
origin to a positive model ball on which the branch agrees with the complete
intrinsic framed exponential and satisfies the exact radial identity
`riemannianEDist p (B z) = ENNReal.ofReal ‖z‖`.  The proof reuses the existing
small-vector minimizing theorem and the normal-frame isometry; it does not
assume that an arbitrary inverse branch is globally minimizing.

Focused verification, the targeted module build, the root aggregate check,
and direct axiom inspection passed.  The new endpoint depends only on
`propext`, `Classical.choice`, and `Quot.sound`; the current full-project build
is pending.

This is a local exponential-coordinate producer.  It does not by itself solve
the uniform moving-center branch problem needed for the convex-stratum
dimension-growth theorem.  That separate moving-center problem is now handled
by `DiagInvBranch.exists_source_tube` and the minimizing-branch adapters.
