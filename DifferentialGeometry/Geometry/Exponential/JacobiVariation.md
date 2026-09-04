# JacobiVariation

## Raw-domain time-one derivative bridge (2026-08-30)

### Mathematical route

`radial_jacobi_dom` extends the existing time-one radial-variation chain-rule
identity from the small C2-radius neighborhood to every velocity in the raw
exponential domain.  Its only geometric input is the domain-local smoothness
theorem `expMap_contMDiffAt`; the affine-line derivative and manifold chain rule
are exactly the route already used by `radial_jacobi_one`.

The statement deliberately omits completeness, pseudo-emetric, Ricci, metric
norm, nonzero-dimension, target Hausdorff, and sigma-compact hypotheses.  It is
the small derivative adapter needed before identifying the raw exponential
Jacobian with the existing `curveDensity`; it does not introduce a second
exponential-domain or density hierarchy.

### Verification

Source implementation is complete and statically reviewed.  Focused Lean
verification is pending because the newly exported domain-smoothness artifact
has not yet been refreshed, and this source-only window explicitly forbids
checks or builds.

### Progress

The theorem itself remains formally unverified (0% accepted completion); its
dedicated source implementation is complete apart from verification (about
90%).  The raw local-polar/Bishop endpoint remains unstated (0% theorem
completion); this lemma is one small prerequisite for its area-density bridge.

## Raw-domain Jacobi package on the open segment (2026-08-30)

### Mathematical route

`radial_jacobi_on` supplies exactly the three inputs used by the local mean
comparison on `Ioo 0 1`: differentiability of the radial variation field, the
same property for its covariant derivative, and the pointwise Jacobi equation.
Its input is only pointwise membership of `t • x` in the raw `expDomain` on
`Icc 0 1`; it has no completeness, pseudo-emetric, metric-norm, Ricci, or
small-radius premise.

At each interior time, openness of `expDomain` gives a small fiber ball around
`t • x`.  Smooth time and transverse clamps agree with the identity as germs
at the chosen time and at the zero variation parameter, while their global
image stays in that ball.  Thus `expMap_contMDiffAt` makes the clamped joint
variation globally smooth.  For every clamped slice,
`expMap_smul_eq_max` identifies the raw radial curve locally with a maximal
geodesic, so the existing curvature-commutation proof yields the Jacobi
equation.  Germ congruence then transports all three conclusions back to the
unclamped raw radial curve and variation field.  The proof deliberately stops
on `Ioo 0 1`: the comparison consumer does not need the endpoint at zero.

Two private proof bricks keep this route local to the canonical API:
`exists_dom_clamps` is the open-set clamp construction, and
`jacobiAt_of_var` extracts the Jacobi equation from a smooth geodesic
variation.  No new public domain or Jacobi hierarchy is introduced.

### Verification

The source has been written and statically reviewed with no placeholders.
Focused verification was not run in this source-only window: the required
`Smoothness.Domain` artifact is currently missing, and a named refresh was
explicitly reserved for the upstream integration sequence.

### Progress

`radial_jacobi_on` is formally unverified (0% accepted theorem completion);
its dedicated source route is complete pending elaboration (about 85%).  The
raw compact-closure Bishop endpoint remains unstated (0% theorem completion);
this theorem is one local Jacobi producer for that larger endpoint.

## Raw pole derivative and endpoint regularity (2026-08-30)

### Mathematical route

`radial_jacobi_d0` proves that the covariant derivative at `t = 0` of the raw
radial variation field determined by `x + s • w` is `w`.  No domain hypothesis
is needed: zero is always in `expDomain`, and `isOpen_expDomain` together with
`exists_dom_clamps` supplies a globally smooth joint variation agreeing with
the raw one as a germ at the pole.  The proof then follows the established
`intrinsic_jacobi_d0` mechanism: commute the two covariant derivatives, identify
the launch velocity with `x + σ s • w`, and differentiate this affine germ at
the zero variation parameter.

`radial_jacobi_reg0` is the only additional endpoint bridge.  It gives
`DifferentiableAt` for the raw variation field and for its first covariant
derivative at `t = 0`.  Together with `radial_jacobi_on` on `Ioo 0 1`, these are
the endpoint regularity facts needed by future closed-interval Jacobi ODE and
index-form arguments.  No endpoint `IsJacobiAt`, consumer predicate, or second
raw-domain hierarchy is introduced.

Both declarations omit completeness, pseudo-emetric, metric-norm, Ricci,
nonzero-dimension, and sigma-compact assumptions.

### Verification

The source is complete and statically reviewed with no placeholders.  Focused
verification remains pending for the same upstream reason: the
`Smoothness.Domain` artifact is missing, while this parallel window forbids a
named refresh.

### Progress

Both new public declarations are formally unverified (0% accepted theorem
completion); their dedicated source route is complete pending elaboration
(about 85%).  They do not by themselves state or prove the compact-closure
local Bishop endpoint, which remains 0% complete as a theorem.

## Pointwise raw-domain regularity (2026-08-30)

### Mathematical route

`radial_jacobi_reg` weakens the regularity input to the single pointwise fact
`t • x ∈ expDomain g p`.  Openness of the raw exponential domain and
`exists_dom_clamps` produce time and variation clamps agreeing with the
identity as germs at `t` and `0`.  The clamped launch map stays in the domain,
so `expMap_contMDiffAt` makes the joint variation smooth.  The existing
variation-field regularity theorems give differentiability for the clamped
field and its covariant derivative; `chartRep_congr_curve` and
`covDerivAlong_congr_curve` transport both results through the germ agreement.

The theorem deliberately does not produce `IsJacobiAt` and carries no
completeness, pseudo-emetric, metric-norm, Ricci, curvature, nonzero-dimension,
or sigma-compact hypothesis.  The old `radial_jacobi_reg0` public signature is
preserved as the specialization at zero using `zero_mem_expDomain`, deleting
its duplicate clamp proof.

### Verification

The source is complete and statically reviewed with no placeholders.  Focused
verification was deliberately not run because the shared verification window
belongs to P2 and this task is source-only.

### Progress

`radial_jacobi_reg` remains formally unverified (0% accepted theorem
completion); its dedicated source implementation is about 90% complete pending
elaboration.  The compact-closure local Bishop endpoint remains unstated (0%
theorem completion); this is one pointwise regularity producer for its raw
Jacobi/index-form infrastructure.

## Focused verification repair (2026-08-30)

The complete file now passes focused verification without warnings.  The local
repairs use the project-native derivative and tangent-space interfaces: the
mixed-derivative germ equalities are explicitly typed before evaluation at
`1`, the scalar estimate uses `abs_add_le`, and the clamp identity is closed in
its actual additive orientation.

The public radial Jacobi statements retain their original weak assumptions.
Their proofs split on `finrank ℝ E = 0`: in zero dimension, differentiability
and tangent-fiber equalities follow from subsingleton elimination; in positive
dimension, private helpers reuse the existing nonzero-dimensional curvature
and commutation machinery.  This avoids adding `NeZero` to any public theorem.

The four radial Jacobi producers in this file are now verified theorem
endpoints (100%).  The later compact-closure local Bishop theorem remains
unstated (0% theorem completion); this file supplies only its dedicated raw
Jacobi and endpoint-regularity infrastructure.

## Focused regression (2026-09-01)

The current source, including `radial_jacobi_reg` and its pole specialization
`radial_jacobi_reg0`, again passes focused verification without warnings.  No
source repair or artifact refresh was needed.

## Arbitrary radial horizon (2026-09-01)

`radial_jacobi_on` and its positive-dimensional helper now quantify an implicit
upper endpoint `L`.  Raw exponential-domain membership is required on
`Icc 0 L`, and the two regularity conclusions and Jacobi equation hold on
`Ioo 0 L`.  No positivity hypothesis on `L` is needed: for an empty or reversed
open interval the result is vacuous, while the proof at an interior point uses
only its positive time and pointwise domain membership.  All occurrences of
`1` representing a derivative direction remain unchanged.

This is the lowest-layer interval generalization consumed by arbitrary-horizon
raw minimizing-geodesic arguments.  It introduces no new predicate or wrapper
and retains inference for existing unit-horizon call sites through their domain
hypothesis.

Focused verification passes without warnings.  No artifact refresh or build
was run.  The generalized producer is complete; it does not change the
completion status of any downstream comparison endpoint until those consumers
are checked.
## Generic radial interval artifact handoff (2026-09-01)

The implicit-horizon form of `radial_jacobi_on` is warning-free focused GREEN,
and its explicitly named module refresh passed.  The refresh replayed unrelated
dependency linter warnings but the target module was clean.  The generic raw
injectivity consumer may now read the new declaration shape.

## Raw Jacobi equation at the pole (2026-09-01)

The private clamped-variation construction now proves its three regularity and
Jacobi conclusions on `Icc 0 L`.  At the clamp center it reuses the native
`raw_radial_geo_at` theorem, so the proof no longer needs positive time or a
maximal-geodesic rescaling just to establish the geodesic equation.  The public
`radial_jacobi_on` statement retains its established `Ioo 0 L` interface, while
the new `radial_jacobi_at0` exposes exactly the missing pole equation without
adding completeness or a positive-finrank assumption.

Focused verification passes without warnings.  No artifact refresh was run:
the next consumer has not yet been source-written, and parallel audit work was
still active.  This closes the pole-Jacobi producer only; the P1b injectivity
endpoints remain unstated and therefore remain at 0% theorem completion.
