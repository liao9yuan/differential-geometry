# H6NormalCoord

## 2026-07-27 combined control radius

`exists_intr_control` is focused-green. It takes the minimum of the independently
checked intrinsic half/two radius and intrinsic local-diffeomorphism radius, so
one sequence-uniform positive model ball now carries both conclusions at every
stage and center. Restriction is pointwise and introduces no new geometric
assumption.

`H6BallData` now retains the half/two estimate on the exact relative ball used
to construct its whole-ball chart. This removes the final zero-order assembly
ambiguity: the metric estimate and branch can no longer come from unrelated
radius choices. Verification of the downstream `H6NormalData` source is waiting
only for the coordinated refresh of the new `exists_intr_control` export.

## 2026-07-27 intrinsic ODE chain

The unclamped intrinsic route now has checked lower producers:

- `riemannOp_sq_le`: pointwise `metricRm04At` fiber norm controls
  `|R(J,V)V|_g^2`;
- `intrJacobi_ode`: sequence curvature bounds plus constant geodesic speed give
  the covariant Gronwall ODE with constant `sqrt(dim) * R * g_p(u,u)`;
- `intrJacobi_bounds`: all regularity, frame, and initial-value obligations are
  already automatic.

`intr_rm04_of_seq` was aligned with the stronger `Ico 0 1` package; its proof
is unchanged because `SeqBoundedGeometry` is pointwise global.  The H6 relative
profile theorem is still not stated (0%).  The new focused-green
`exists_intr_radii` closes the unclamped zero-order geometry: one `r0 > 0`
works for every sequence member and center, and the total intrinsic framed
pullback metric satisfies the half/two estimate on `ball 0 r0`.  Its proof uses
the scalar quarter budget, `intrJacobi_ode`, `intrJacobi_bounds`, and
`intr_metric_jacobi`; it does not intersect the radius with `expRadiusGp`,
`framedJacobiRadius`, or a qualitative agreement ball.

## Purpose

This module is the native producer boundary between radial Jacobi estimates
and the Chapter-4 `NormalCoordMetricBoundInput` API. It must not introduce a
replacement geometric assumption.

## Status

Implementation resumed on 2026-07-18. The public `normalCoordMetric` now is the
canonical orthonormally framed pullback metric. `H6NormalCoord.lean` records its
exact endpoint-Jacobi formula and converts two-sided framed Jacobi estimates to
`NormalCoordMetricEquivOn`; the obsolete raw-coordinate aliases were removed.

`Geometry/Exponential/NormalFrame.lean` now constructs, at every center `x`, a
chosen continuous linear equivalence `normalFrame : E ≃L T_xM` and proves

`g_x(normalFrame v, normalFrame w) = <v,w>`.

`Geometry/Exponential/FramedNormalCoordinates.lean` defines the genuine
normal chart `z |-> exp_x(normalFrame z)`, its inverse, its differential, and
the exact equivalence between model balls and `g_x` tangent balls. The public
`normalCoordMetric` is the pullback metric of that chart, equals `innerSL Real`
at the center, and is the endpoint Gram form of radial Jacobi fields launched
through the same frame. Its framed Jacobi API consumes the intrinsic
`expRadiusGp` rather than the raw `expMapC2Radius`.

The first shared migration brick is now checked: `injRadius` measures
injectivity of the actual global framed exponential map. The two raw
`expMapDiffeo` source helpers needed by the Gauss radius layer retain their
legacy explicit instance signature in an isolated section, avoiding the
`NormedSpace` instance diamond. `ExpBallDiffeo` has been rewritten against the
same framed map and its focused check passes. `StepBInputs.normalTransition`
now delegates to the same generic `framedTransition`; the full Step-B input
file also passes a focused check after keeping its raw chart-inverse proof
pointwise rather than calling the newly framed ExpBall theorem.

The local zero-order producer is now checked. `exists_equiv_ball` uses
smoothness of the framed pullback metric and
`normalMetric_zero = innerSL Real` to choose, for each center, a positive radius
inside `expRadiusGp` on which the metric satisfies the exact H6 half/two
Euclidean comparison. This proof does not use Rm04 and makes no sequence-uniform
claim.

`exists_equiv_radii` packages those per-center choices for an entire pointed
sequence and is focused- and target-green. Its radius still depends on both `k` and `x`;
this is useful pointwise data, but it does not change the quantifier-order gap
for `NormalRadiusProfile`.

The quantitative zero-order producer is now focused- and target-green. `FramedRm04Bound`
states the radial Rm04 bound on the explicit
`framedJacobiRadius = expRadiusGp / 26`; `framed_rm04_of_seq` supplies it from
`SeqBoundedGeometry.C 0`. `framed_rm04_bounds` proves arbitrary-vector endpoint
bounds, including the required positive rescaling of each launch direction.
Finally, `exists_rm04_radii` chooses one sequence-independent `r0 > 0`, makes
the scalar Gronwall error at most one quarter, and proves
`NormalCoordMetricEquivOn` on
`ball 0 (min (framedJacobiRadius Y x) r0)` for every sequence member and every
center. There is no new geometric assumption or endpoint wrapper in this
chain.

## Corrected feasibility diagnosis

The old raw-coordinate feasibility diagnosis is obsolete. The current
`normalCoordMetric Y x` uses `normalFrame`, and at the origin
`normalMetric_zero` gives

`normalCoordMetric Y x 0 = innerSL Real`.

Consequently local coercivity follows from continuity. What does not follow
from this pointwise argument is the quantifier order required by
`NormalRadiusProfile`: one fixed positive ratio must work for every sequence
member and every center after multiplication by the CGT decay profile.

The Jacobi/Rm04 and scalar-budget portions of the zero-order producer are no
longer frontiers. The remaining quantifier-order gate is the pointwise clamp
`framedJacobiRadius Y x = expRadiusGp Y.metric x / 26`. The current
`expRadiusGp` contains `expMapC2Radius`, which is a qualitatively chosen local
inverse radius. CGT injectivity cannot lower-bound that arbitrary choice.

There is a second independent quantifier issue in the current record boundary.
`NormalCoordMetricBoundInput.radius` is downward closed: any valid record can
be restricted to an arbitrarily smaller positive radius. Consequently a
positive `NormalRadiusProfile.ratio` cannot be produced for an arbitrary
supplied `hb`; H6 must choose the controlled radius together with the metric
bound record (or return a combined bounds/profile package). The profile is not
a post-processing theorem about the current unconstrained record.

`InjectivityRadius.exp_dom_of_inj_rad` now closes the first canonical-branch
subproblem: every vector in a framed model ball strictly below `injRadius`
belongs to the natural `expDomain`. This uses injectivity against the origin
and the totalized exponential's center value outside its domain. It does not
put the ball in the selected `framedExpDiffeo.source`.

The finite-time smooth-flow gate is now closed at source level. The exact-green
generic theorem `ODE.flow_slice_smooth` propagates smooth dependence along a
compact reference trajectory. `Exponential.lift_isIntegral` identifies the
complete intrinsic velocity lift with the globally smooth basepoint-free
spray, `velocityLift_one` proves its time-one slice is globally smooth, and
`intrinsicExp_smooth` projects this to the complete intrinsic exponential; the
whole continuation/identification module is focused- and exact-green.
The H6 branch no longer needs to upgrade the old long finite chart-chain
continuity proof. `intrinsic_jacobi` and `intrinsic_jacobi_one` now give the
global intrinsic Jacobi equation and the exact time-one differential identity.
The remaining native gate is architectural: the ordinary framed exponential
used by `injRadius` and `expRadiusGp` is chart-fixed, while CGT and the new
Jacobi API control the intrinsic exponential. A canonical migration or a
single justified geometric-branch design is required before Rm04 and
injectivity can construct the radius-controlled partial diffeomorphism. Do not
replace it by an endpoint wrapper or synonym assumption on
`NormalRadiusProfile`.

The HCG completeness boundary is now explicit rather than hidden.
`intr_metric_eq` threads `MetricComplete Y` into the intrinsic total-map
metric and identifies it with the existing HCG normal-coordinate metric on the
transferred branch. `exists_intr_eq_ball` extracts the corresponding positive
agreement ball. Both are focused-green. This is a migration bridge only: its
radius is pointwise and qualitative, so it does not solve the relative-profile
quantifier.

At the geometry layer, `intrFrame_mfderiv` is source/focused-green and
identifies the differential of `intrinsicFramedExp` with the time-one
intrinsic Jacobi variation. `IntrinsicFramedJacobi.lean` now contains the
derived differential and pullback-metric endpoint formulas; its focused check
waits only for the narrow upstream artifact refresh.

## Honest progress

- Per-center orthonormal normalizer and exact radial norm correspondence: 100%
  proved and checked.
- Framed chart, inverse chart, differential, pullback metric, and framed Jacobi
  bridge: 100% proved and checked.
- Per-center zero-order `NormalCoordMetricEquivOn` producer theorem: 100%
  proved and focused-checked.
- Sequence-wide pointwise radius-choice theorem: 100% proved and
  focused-checked; it deliberately makes no uniform lower-bound claim.
- Sequence-uniform clamped zero-order metric producer: 100% proved and
  target-checked. It gives one curvature radius `r0`, but still intersects it
  with the pointwise `framedJacobiRadius`.
- Intrinsic radius, injectivity, and whole-ball-branch infrastructure: 100%
  proved; the existing checked artifacts precede the latest combined-radius
  projection, whose source is focused-green.
- Branch-parametric consumer migration: about 35%. The first center/readout
  layer is migrated in source; its ordered Gate-4 verification is waiting on
  an unrelated exact writer.
- Native all-order `NormalCoordMetricBoundInput` producer theorem: 0%; its
  dedicated machinery is about 35%, because the high-order curvature-to-metric
  jet induction has not been formalized.
- Overall native H6 producer machinery: about 55%; the final
  `exists_h6NormalData` theorem is unstated and therefore 0%.
- Unconditional MSM135 Theorem 3.9: 0%. Conditional Theorem 3.9 remains 100%;
  whole HCG compactness machinery remains about 60%.

## Next target

Resume from the live gates in `H6_RADIUS_CONSULT.md`:

1. verify the already migrated Gate-4 legacy-provider consumer chain in its
   recorded dependency order;
2. parameterize the selected diagonal/root equation by the same chart family,
   recheck it under `legacyChartFamily`, and only then instantiate it with the
   H6 provider;
3. prove the independent fixed-tube all-order curvature-to-coordinate-metric
   jet induction and assemble `exists_h6NormalData`.

The principal mathematical frontier is item 3. It must remain a direct
quantitative producer, not a new input record or an assumption equivalent to
the desired metric-jet bounds.

## Migration audit

The migration is provider-based, not a new parallel normal-coordinate API.

1. Move the generic `exists_diffeo_of_injOn` theorem to a cycle-free
   local-diffeomorphism file and re-export it from `ExpBallDiffeo`.
2. Give `injRadius` intrinsic framed-map semantics. The chart-fixed backend
   may remain temporarily under an explicit compatibility name.
3. Add a `NormalBallChart`-style interface carrying a radius, a partial
   diffeomorphism, ball-to-source containment, and agreement with the total
   intrinsic framed map.
4. Make the current qualitative branch implement that interface and migrate
   consumers while keeping the selected route green.
5. Construct the H6 provider from `hd.decay`, the uniform `r0`, and the generic
   glue, then switch consumers once.
6. Remove `NormalRadiusProfile.le_exp_radius` and legacy `expRadiusGp` source
   proofs from the endpoint path. Do not attempt to prove a uniform lower
   bound for that qualitative legacy choice.
7. Prove the all-order metric-jet producer and assemble `H6NormalData`.

The generic frame, intrinsic exponential, endpoint Jacobi, pullback metric,
and zero-order estimates are settled and should be reused rather than rebuilt.
