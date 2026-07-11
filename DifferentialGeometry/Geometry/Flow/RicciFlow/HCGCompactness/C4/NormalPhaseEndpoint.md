# NormalPhaseEndpoint

## Role

This is the merge layer between the quantitative normal-coordinate phase flow
and the project's intrinsic moving exponential.  It consumes the checked
geodesic naturality and interval-uniqueness producers; it does not define a
second intrinsic inverse.

## Verified state

- `normal_enorm` supplies the Riemannian tangent-enorm formula under the
  endpoint layer's explicit suppression of the model tangent norm instances.
- `normalTangent` sends `(u,v)` to
  `⟨exp_x u, d(exp_x)_u v⟩`; `normalPair` sends a pair of normal coordinates to
  the corresponding ambient pair.
- `normal_launch_mfd` identifies the launch derivative of a pushed phase curve
  with `d(exp_x)_u v`.
- `normal_end_eq_intr` transports the bilateral phase trajectory through the
  quarter-ball normal diffeomorphism and identifies its time-one value with
  `expMapIntrinsic`.
- `normal_end_eq_diag` is the exact commutative-square statement with
  `diagExp`.
- `exists_normal_diag` packages one positive bilateral flow ball, the
  quantitative `OpenPartialHomeomorph`, its explicit positive target-ball
  radius, and the commutative square with `diagExp`.
- `normal_inv_eq` proves that this model branch agrees with the existing
  `diagExpInv` whenever the existing branch identities hold and both tangent
  vectors satisfy the concrete `expDiffeoRadius` smallness conditions.
- `DiagExpDerivative.diagExpInv_diagExp` supplies the complementary
  source-side germ identity, so the two branches are now formally compatible on
  every verified overlap.

Focused verification passed without local warnings, `sorry`, or `admit`.
The public declarations' axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`.

## Review disposition

The external review recommended geodesic-spray naturality.  The live project
already had the equivalent lower-level producer
`CovariantDerivativeAlong.covAlong_natCrossAt`: it handles an arbitrary
along-curve field by a local extension plus a residual vanishing at the point.
`Geodesic.geoEq_mapCrossAt` and `geodesicOn_mapLocal` then provide the required
pointwise/open-set naturality.  This closes the review's arbitrary-velocity
objection without introducing a parallel spray API.

An attempted move of `normal_enorm` into `PointedEmetric.lean` was rejected and
fully reverted: importing the norm-reconciliation layer there reintroduced the
tangent norm instance diamond that `PointedEmetric` is designed to avoid.

## Frontier

The next target is no longer geodesic, endpoint naturality, or branch uniqueness.
The genuine design gate is sequence-uniform domain reconciliation.  The
quantitative branch has an explicit uniform model target ball, while
`exists_diagInvDom_inf` exposes only a pointwise open germ for the privately
chosen qualitative `diagExpIFT` branch.  Its openness supplies no uniform
radius, so the whole quantitative ball cannot be placed in that germ from the
current API.

Two honest routes remain: refactor the canonical/readout branch package to
consume the transported quantitative partial homeomorphism, or add a new
quantitative theorem proving explicit containment in the existing IFT source
and target.  A pointwise shrink, a finite minimum at one index, or an assumption
renaming this containment does not solve `StepB1RawInput`.

## Project position

- `StepB1RawInput` producer: unstated/unproved, 0%.
- Textbook B1 theorem: unstated/unproved, 0%.
- Quantitative normal-coordinate `diagExp` branch theorem
  (`exists_normal_diag`): proved, 100%.
- Uniform theorem identifying the whole branch with totalized `diagExpInv`:
  unstated/unproved, 0%.
- Dedicated normal-coordinate quantitative branch machinery: about 92%.
- Step B/B1 infrastructure: about 73%.
- Chapter 4 infrastructure: about 72%.
- Whole HCG compactness infrastructure: about 49%.
