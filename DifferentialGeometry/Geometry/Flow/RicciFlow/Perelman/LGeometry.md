# Perelman L-geometry umbrella

`LGeometry.lean` is the import-only public entry point for the fixed-manifold
Perelman L-geometry modules.  Its terminal imports expose the foundational
definitions, square-root reparameterization, moving-metric and first-variation
identities, regularized ODE/L-exponential construction, and the pullback and
parabolic-scaling naturality chains.  The terminal second-variation import now
also exposes the regularized and ordinary L-Jacobi predicates, the square-root
Jacobi bridge, the differential-of-`lExp` Jacobi theorem, the symmetric
L-index form and Green identity, and the natural-input fixed-endpoint capstone
`lLength_second_var`.

The public entry point also exposes `lRegJacobi_unique`, the fixed-chart
initial-value uniqueness theorem for regularized L-Jacobi fields, and the
domain-aware L-conjugacy API `IsLConj`, including its kernel and Jacobi-field
characterizations and the nonconjugate differential bijectivity lemmas.

`RegIndex.lean` adds the nonsingular square-root-time index density and form,
their symmetric and Green identities with an allowed endpoint at `s = 0`, the
Jacobi boundary formula, and the almost-everywhere square change of variables
back to the ordinary `lIndex`.

`RegAction.lean` adds the direct square-root-time Lagrangian and action,
their compatibility with ordinary L-length, first variation with internally
produced compact domination, joint regularity of the Euler residual, and the
fixed-endpoint formula `lRegAction_second`.  The latter remains valid when an
endpoint is `s = 0` and produces all Jacobi and index-density integrability
inside the proof.  Its compact-slab coercivity and family-uniform
action-to-energy bounds feed the compactness layer without assuming scalar
curvature is nonnegative.

`Minimizer.lean` starts the honest minimizing layer with
`lRegIndex_nonneg_var`: for an actual smooth fixed-endpoint variation whose
regularized action has a local minimum at the central parameter, its diagonal
regularized index is nonnegative.  This is a direct second-derivative
necessary condition, not a semidefiniteness assumption.  The arbitrary-field
theorem `lRegIndex_nonneg` realizes a smooth zero-endpoint field by a genuine
fixed-endpoint variation and transfers the same conclusion.

`ActionCompact.lean` adds `lAction_subseq`: every family of regularized curves
with one action bound on a fixed compact parameter interval and compact target
has a uniformly convergent subsequence.  It derives uniform equicontinuity from
one family-wide reference-energy budget and the reference Riemannian distance;
equicontinuity is not supplied as an assumption.  The corollary
`lAction_subseq_fix` also proves that two common endpoints are preserved by the
limit.

Focused verification passes without warnings after targeted refreshes of the
new terminal modules.  The umbrella contains no declarations and introduces
no additional assumptions.  L-minimizer existence is still a separate global
frontier: the C0 subsequence, generic vector-valued H1 compactness, and generic
quadratic weak lower semicontinuity are available.  `timeH1.ofContDiffOn` and
`chartTimeH1` also cover linear and single-chart C1 realization.  What is still
missing is finite-chart localization, a weak chain rule on overlaps, and the
chart-independent identification of weak velocity with `lVelocity` and the
moving L-action.  A Tonelli regularity upgrade is a further independent
frontier.  `exists_lMinimizer` and `redVolume_anti` therefore both remain
unproved (0%).
