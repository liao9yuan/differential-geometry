# CGTWhitehead

## State — 2026-07-27

This module implements the complete-extension part of the native
Cheeger--Gromov--Taylor Whitehead argument.

The intrinsic exponential pullback metric on `intrPullBall R` is incomplete.
`intrExtMetric` blends it into the canonical flat metric on the whole model
space, agrees with the pullback metric through the closed radius `3R/4` ball,
and is complete.  The construction uses the compactly supported cutoff
`intrCut`; it does not manufacture a false complete instance on the open
pullback ball.

`intrExtJoin` is the canonical Hopf--Rinow minimizing join for this complete
extension.  `intrExtJoin_fenced` is focused-green and proves the first-hit
fence: when both endpoints have norm at most `a` and `4*a < R`, the join stays
strictly inside radius `3R/4` on `[0,1]`.  The proof compares a reparametrized
prefix in the extension and pullback metrics and obtains the contradiction
`3R/4 <= 3a`.  The reparametrization is used only to compare prefix lengths;
it is not exposed as a geodesic.

`exists_fenced_ext` is the ambient model-space result: it returns the complete-
extension minimizing geodesic, its smoothness, global geodesic equation,
endpoints, strict fence, and exact arc-length/distance equality.

The canonical `exists_fenced_min` is now also focused-green and returns one
fixed subtype-valued join
`intrPullBall R → intrPullBall R → ℝ → intrPullBall R`.  For every pair in the
radius-`a` core it is globally smooth, agrees with `intrExtJoin` on `[0,1]`,
stays below radius `3R/4`, and is a pullback geodesic on `[0,1]`.  The
construction uses a smooth bounded time clamp which is the identity on a
strictly larger time interval.  Thus the nonlinear clamp is never claimed to
preserve the geodesic equation globally; endpoint germs transfer the equation
only on the required closed interval.  `intrExt_restrict` and
`intrPull_geo_of_ext` are the checked open-agreement metric/geodesic bridge.

`intrCore_edist_eq` is now focused-green.  For two points in the radius-`a`
core with `4*a < R`, it proves that the true pullback extended distance equals
the true complete-extension extended distance.  One inequality codrestricts
the fenced complete-extension minimizer.  For the other, a hypothetically
shorter pullback path is confined to the agreement ball by
`intrPull_dist_zero`; its pullback and extension lengths then agree, a
contradiction.  Thus the incomplete carrier is no longer the actual-distance
seam.  This theorem does not assert uniqueness of the minimizer or smoothness
of distance at a cut point.

Connectedness policy is fixed: do not add global `[ConnectedSpace M]` to the
CGT producer or to the HCG input.  The finite-center pullback ball is an open
Euclidean ball subtype and may receive its own connected instance from
`Metric.isConnected_ball`.  If a legacy ambient theorem genuinely requires
connectedness, restrict it to `connectedComponent p`; radial paths provide
membership via `pathComponent_subset_component`.  Add distance or exponential
restriction adapters only when a concrete consumer needs them.  Component
restriction solves connectedness only, not the incompleteness of
`intrPullBall R`.

Verification:

- `GeodesicConvexity.minJoin_arcLength` and `minJoin_pathLen`: focused and
  exact current;
- `intrExtJoin_fenced`: focused-green;
- `exists_fenced_curve`, `exists_fenced_ext`, and canonical subtype
  `exists_fenced_min`: focused and exact current;
- `intrCore_edist_eq`: focused-green;
- direct axiom audit for `intrCore_edist_eq` reports only `propext`,
  `Classical.choice`, and `Quot.sound`;
- no new assumption, `sorry`, `admit`, or axiom was introduced.

## Exact remaining Whitehead frontier

The smallest producer that closes the real-distance/Jensen seam is a
true-distance branch germ for the complete extension.  In schematic form:

```text
intrCore_dist_germ:
  pt,q ∈ intrCore R a
  → ∃ B : ExpInvBranch gExt hExt pt,
      minimizingVec gExt hExt pt q ∈ B.hom.source
      ∧ branchEnergy gExt B =ᶠ[𝓝 q]
          (fun z ↦ 1/2 * (riemannianEDistOf gExt pt z).toReal^2)
```

Together with `intrCore_edist_eq`, metric agreement, `branchHess_jacobi`,
`intrPull_pair_pos`, and `strictConvex_geo_on`, this is sufficient to prove
`intrCore_jensen` without changing `halfSqDist` or the center API.

The missing mathematics inside this germ is the localized Whitehead
short-cut theorem: every minimizing join between core points is the unique
short minimizer (equivalently, the chosen minimizing endpoint is not a cut
point and its inverse branch remains minimizing on a neighborhood).  The
present tree has no cut-time/cut-locus alternative or local Whitehead
globalization theorem from which to derive it.

Three honest routes were checked:

1. Direct `ExpInvBranch` calculus on `intrPullBall R` is unavailable because
   the carrier is incomplete; installing completeness there would be false.
2. The complete extension now carries the true distance, but a selected
   fenced minimizer and branch openness do not exclude a second minimizing
   branch.  At such a point `branchEnergy` is only an upper support for the
   minimum of branch energies, which cannot imply strict Jensen.
3. Restricting to a connected component fixes only connectedness.  Existing
   normal-ball/Gauss uniqueness requires an injectivity radius at the moving
   center and is therefore circular here; no CAT/Whitehead globalization API
   exists in the project or Mathlib.

This is a substantial missing geometric producer, not a coercion or
typeclass blocker.  The next implementation should formalize the localized
short-cut/unique-minimizer theorem itself, rather than add a consumer
assumption or another center wrapper.

Honest accounting:

- complete-extension and first-hit-fence producer: theorem 100%, dedicated
  machinery 100%;
- `exists_fenced_min`: theorem 100%, dedicated machinery 100%;
- pullback strict Jensen theorem `intrCore_jensen`: theorem 0%, dedicated
  machinery about 78–82%;
- paper CGT Lemma 4.6: theorem 0%, dedicated machinery about 77–81%;
- pointwise CGT producer: theorem 0%, dedicated machinery about 71–75%;
- sequence `InjRadiusDecayInput` producer: theorem 0%;
- unconditional Theorem 3.9: theorem 0%;
- whole HCG supporting machinery: about 61%.

The next genuine frontier is `intrCore_dist_germ`, specifically its localized
short-cut/unique-minimizer proof.  Hessian-to-strict-convexity is already a
consumer once that germ exists; the metric, distance, and selected-geodesic
transfers are no longer frontiers.
