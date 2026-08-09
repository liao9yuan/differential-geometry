# CGTWhitehead

## State — 2026-07-28

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
- localized short-bigon injectivity `intrCore_short_inj`, the public
  regular-and-unique producer `intrCore_minimizingVec_regular_unique`, and the
  true-distance germ `intrCore_dist_germ`: focused and exact current;
- branch-Hessian positivity `intrBranch_hess_pos` and the true-distance strict
  Jensen consumer `intrCore_jensen`: focused and exact current;
- direct axiom audits for `intrCore_edist_eq`, `intrCore_short_inj`,
  `intrCore_minimizingVec_regular_unique`, `intrCore_dist_germ`,
  `intrBranch_hess_pos`, and `intrCore_jensen` report only `propext`,
  `Classical.choice`, and `Quot.sound`;
- no new assumption, `sorry`, `admit`, or axiom was introduced.

## Whitehead and Jensen lane closed; exact next producer

The hard localized Whitehead seam is now closed.  `intrCore_short_inj` proves
injectivity among all controlled short minimizing launches.  Its proof uses a
compact minimal bad-pair set, endpoint first variation at both corners, exact
length-ratio reparametrization of the resulting smooth periodic geodesic, and
the strict-convexity contradiction for the explicit origin energy
`z ↦ (1 / 2) * ‖z‖ ^ 2`.  The strict scale `L > 2*a`, fence
`a + L < 3*R/4`, and curvature slack are derived from the existing strict
hypotheses; there is no `3*a` or `4*a` curvature inflation.

`intrCore_minimizingVec_regular_unique` packages the exact hard producer
requested by consumers: the selected minimizing launch is nonconjugate and is
the unique launch attaining both the endpoint and the true minimizing length.
`intrCore_dist_germ` then obtains an `ExpInvBranch`, proves eventual selected
minimizer membership by finite-dimensional compactness, and identifies
`branchEnergy` with the true half-squared `riemannianEDistOf` germ.

The implementation is split by abstraction boundary:

- `CGTWhiteheadBase.lean` contains the extension, fence, distance-transfer, and
  Jacobi-positivity base;
- `CGTWhiteheadBigon.lean` contains the localized Klingenberg/Whitehead proof;
- `CGTWhiteheadProducer.lean` contains the two public consumer-facing
  endpoints;
- `CGTWhiteheadJensen.lean` contains branch-Hessian positivity and the strict
  Jensen endpoint;
- `CGTWhitehead.lean` is the stable umbrella import.

The rejected routes remain rejected for the same reasons: a selected branch
alone is only an upper support at a cut point; the pullback ball is incomplete;
global connectedness does not imply minimizing uniqueness; and monodromy or
proper-local-diffeomorphism would hide the same short-bigon theorem in an
unproved homotopy-length or properness premise.

`intrCore_jensen` is now proved.  It combines `intrCore_dist_germ`,
`branchHess_jacobi`, the perpendicular/radial Hessian decomposition,
`intrPull_pair_pos`, second derivatives along the fixed fenced join, and
`jensen_of_strict`.  Its local connectedness instance is the Euclidean open
ball's connectedness; its distance is explicitly the pullback Riemannian
distance, and no false completeness instance is introduced.

The propeller assembly is now closed in `CGTPropeller.lean`.
`intrIter_family` is the paper-facing intrinsic form of CGT Lemma 4.6, and
`intrFiber_count_ge` propagates its finite base-fibre family across the short
target ball using Lemma 4.5.  The next frontier is the
multiplicity-sensitive area step for `intrLoop_ge_cgt`, not more Whitehead
geometry.

Honest accounting:

- complete-extension and first-hit-fence producer: theorem 100%, dedicated
  machinery 100%;
- `exists_fenced_min`: theorem 100%, dedicated machinery 100%;
- `intrCore_minimizingVec_regular_unique`: theorem 100%, dedicated machinery
  100%;
- `intrCore_dist_germ`: theorem 100%, dedicated machinery 100%;
- pullback strict Jensen theorem `intrCore_jensen`: theorem 100%, dedicated
  machinery 100%;
- paper CGT Lemma 4.6: native finite-family theorem 100%, dedicated machinery
  100%;
- `intrLoop_ge_cgt`: theorem 0%, dedicated machinery about 90%;
- pointwise CGT producer: theorem 0%, dedicated machinery about 85%;
- sequence `InjRadiusDecayInput` producer: theorem 0%;
- unconditional Theorem 3.9: theorem 0%;
- whole HCG supporting machinery: about 64%.

The smallest remaining interface must convert a pointwise inverse-fibre
`encard` lower bound into a Jacobian-integral lower bound.  Existing image
area inequalities count the image once, and the exact area formula assumes an
injective source.
