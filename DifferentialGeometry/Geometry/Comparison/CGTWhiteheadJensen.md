# CGTWhiteheadJensen

## State — 2026-07-28

This module closes the strict-Jensen consumer of the localized Whitehead
producer.

`intrBranch_hess_pos` proves positive definiteness of the inverse-branch
half-energy Hessian at every controlled short endpoint.  The zero launch is
handled by the branch Hessian at the base point.  For a nonzero launch, the
inverse differential is decomposed into perpendicular and radial parts:
`intrExt_pair_pos` controls the perpendicular Jacobi endpoint form, the radial
Hessian is the metric square, and Hessian symmetry removes the cross terms.

`intrCore_jensen` chooses the single fenced minimizing join supplied by
`exists_fenced_min` and proves, for every center point in the radius-`a` core,
strict midpoint Jensen convexity of the true `CenterOfMass.halfSqDist`.  At
each interior point of a join it:

- obtains the true-distance inverse-branch germ from `intrCore_dist_germ`;
- applies `intrBranch_hess_pos` to the nonzero join velocity;
- transfers the Hessian to the second derivative along the geodesic;
- obtains strict convexity on `[0,1]` and then invokes
  `CenterOfMass.jensen_of_strict`.

For the propeller consumer, `IsCoreMinJoin` now records the selected fenced
minimizing join together with core containment.  `intrCore_jensen_min`
returns that data and the Jensen conclusion in one call, while
`coreJoin_len` identifies its path length with the actual pullback
Riemannian distance.  The original public `intrCore_jensen` statement remains
unchanged as a wrapper.

The pullback ball receives only its local Euclidean-ball connectedness
instance and the metric induced by the pullback Riemannian metric.  The
inherited Euclidean subtype metric is scoped out while the theorem is
elaborated; otherwise `halfSqDist` would denote the wrong distance.  No
complete-space instance is assigned to the pullback ball, and no global
`ConnectedSpace M` hypothesis is added.

The direct selected-branch-energy route remains invalid at a cut point; the
proof uses the already verified true-distance germ instead.  A naive final
rewrite through the subtype's default distance also failed for the same metric
coherence reason and was replaced by an explicit pullback-Riemannian distance
identification.

Focused verification and exact targeted refresh passed.  Direct axiom audits
for `intrBranch_hess_pos` and `intrCore_jensen` report only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

Honest accounting:

- `intrCore_jensen`: theorem 100%, dedicated machinery 100%;
- paper CGT Lemma 4.6: native finite-family theorem 100%, dedicated machinery
  100%;
- `intrLoop_ge_cgt`: theorem 0%, dedicated machinery about 90%;
- pointwise CGT producer: theorem 0%, dedicated machinery about 85%;
- sequence `InjRadiusDecayInput` producer: theorem 0%;
- unconditional Theorem 3.9: theorem 0%;
- whole HCG supporting machinery: about 64%.

The propeller assembly is now closed in `CGTPropeller.lean`.  The next
frontier is the multiplicity-sensitive area step for `intrLoop_ge_cgt`: turn
the pointwise inverse-fibre `encard` lower bound into a Jacobian integral lower
bound.  This is a measure-theoretic area interface, not another Whitehead,
center, or loop-transport theorem.
