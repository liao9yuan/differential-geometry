# P1 COMPARISON-GEOMETRY PLAN

This is the single phase-specific execution plan for Poincare Phase P1.  The
whole-program authority remains
`../Flow/RicciFlow/POINCARE_PLAN.md`.  The implementation order is strict:
P1a, then P1b, then P1c.  P1d/Toponogov is outside this campaign except for
recording the dependency boundary exposed by P1c consumers.

The target denominator is the set of comparison statements actually consumed
by Morgan--Tian's P2/P3 route, not a complete textbook comparison-geometry
library.  A theorem endpoint counts as complete only when its final statement
is present, proved, focused-check green, and directly axiom-audited.  Existing
machinery is accounted for separately.

## Ownership and verification

- Work only in the current checkout.  Protect all existing dirty files and all
  active or stale claims owned by other work.
- Search `DifferentialGeometry/` first.  `RFreference/` and
  `RicciFlow/Morgan-Tian/` are read-only references for theorem shape and proof
  route; they are never imported into the native tree.
- Claim every Lean file before editing.  Use focused no-global-lock checks;
  refresh an explicitly named module only when a downstream import needs a new
  exported declaration or has a stale-olean failure shape.
- Every edited `Foo.lean` has a synchronized `Foo.md` recording route, reuse,
  blocker if any, and pass/fail without command transcripts.
- The main coordinator alone edits this plan.  P1 work does not edit
  `Perelman/LGeometry/` files.

## P1a -- Bishop--Gromov and required volume comparison

### Acceptance target

Freeze the exact Morgan--Tian P2/P3 consumers and match each to a native,
axiom-clean producer.  Reuse the checked `BishopBall`/normal-ball ratio,
packing, polar/Jacobian, and ball-volume machinery.  Add only a missing stronger
statement, thin adapter, or genuine producer required by those consumers.

### Running status (2026-09-01, exact consumer set closed)

- Project-used theorem endpoints: **100%** (eight of eight).  The seven earlier
  global/complete, packing, small-radius, continuity, and strict-rigidity
  endpoints remain checked.  The eighth endpoint `ball_vol_le_eucl` now gives
  the incomplete-ambient compact-buffer Euclidean upper bound under Ricci
  nonnegativity only on the compared ball.
- Dedicated native machinery for this exact eight-endpoint denominator:
  **100%**.  The chart-independent compact continuation and minimizing-ray
  coverage, raw exponential smoothness and image-measure layer, compact raw
  segment locus, raw Jacobi/no-conjugacy chain, transverse density comparison,
  full-density factorization, pole normalization, and Haar/model-ball
  normalization are all proved and focused verified.  Every export needed by a
  downstream module has an exact named refresh, and the unified 196-declaration
  audit is warning-free and standard-three-axiom clean.
- One actual P3 use is genuinely incomplete-ambient: Morgan--Tian's `volcomp`
  explicitly allows noncomplete flows and invokes the Chapter 5 `flowlimit`
  chain.  Its nonnegative curvature-operator hypothesis narrows the exact
  formalized project need to the local `Ric >= 0` Euclidean absolute upper
  bound used by that flow-limit route.  A separate incomplete-ambient
  two-radius ratio theorem, the arbitrary-negative-lower-bound model theorem,
  and a primitive packing endpoint are textbook-generality extensions, not
  part of this campaign's denominator.
- Current action: P1a is closed.  `BishopRawDensity.lean` is warning-free
  focused GREEN and refreshed through `rawSpeed_sq`, `raw_ratio_anti`,
  `raw_density_le`, `rawDens_eq_trans`, and `rawDens_le_zero`.
  `SegmentBallEuclideanUpper.lean` is warning-free focused GREEN and refreshed
  through `ball_vol_le_eucl`.  The final unified audit directly prints all six
  declarations and reports only `propext`, `Classical.choice`, and `Quot.sound`.

### Remaining-frontier route audit

- **Local compact-closure form.**  The project-used absolute endpoint is now
  checked as `ball_vol_le_eucl`: compact closure of a strictly larger buffer
  ball and nonnegative Ricci curvature on the compared ball imply its volume is
  at most the Euclidean model-ball volume.  The proof uses the checked raw
  minimizing-exponential coverage, compact raw segment locus, noninjective image
  inequality, raw radial Jacobi/no-conjugacy chain, full-density comparison, and
  pole/Haar normalization.  It requires neither `CompleteSpace M` nor a global
  Ricci predicate.  The classical incomplete-ambient two-radius inequality
  `Vol(B(p,R))*s^n <= R^n*Vol(B(p,s))` remains a separate extension: it cannot
  be inferred from two one-sided absolute upper bounds and is not a ninth
  project-used endpoint.
- **Equality rigidity.**  Three native routes were checked.  Direct tightness of
  the three inequalities in `segBall_vol_le_explicit` and a strict-defect
  contrapositive both reduce to the equality/strictness case of the traced
  matrix Riccati inequality; the radius-ratio route instead needs a shell
  derivative theorem for the polar ball integral before reaching the same
  radial equality.  The smallest common producer is an equality
  characterization for `Analysis.trace_sq_le_mul`, followed by a geometric
  equality-or-strict lemma for `mean_riccati_le`.  Those bottom two layers are
  checked and axiom-clean as `trace_sq_eq_iff`, `mean_sq_eq_iff`, and
  `mean_riccati_eq_iff`.  The radial propagation, strict Jacobian/model-volume,
  pole-Haar, Euclidean normalization, curvature-coordinate, and
  sectional-to-Ricci bridges are all warning-free focused-check and
  named-refresh green.  The final `segBall_lt_of_sec` endpoint is included in
  the common direct audit and depends only on the standard logical axioms.

## P1b -- Cheeger lemma and CGT injectivity

P1b starts only after P1a closes or reaches a precisely recorded genuine
blocker.  The known P0 chain `intrInj_ge_cgt -> injDecay_of_bg -> flowInj_of_vol`
must be reused and must not be reopened.  The acceptance target is the exact
additional P2/P3 injectivity statement, if any.

### Running status (2026-09-01, exact consumer set under post-migration re-audit)

- Project-used theorem endpoints: **0%** (zero of two separately counted
  endpoints are yet proved in their exact local-on-balls P3 shape).
- Dedicated native machinery: **about 99%**.  The Whitehead/Jensen/propeller
  stack, `intrInj_ge_cgt`, `injDecay_of_bg`, and `flowInj_of_vol` are
  source-complete with no `sorry`/`admit`; the realized P0 chain is historically
  axiom-clean.  The new `intrInj_ge_cgt_on` radial-local strengthening is
  warning-free focused-check and named-refresh green while preserving the old
  global API.  The quantitative `intrInj_ge_vol` assembly is also focused- and
  named-refresh green; it combines local-radial CGT with the existing ball and
  pull-volume upper bounds.  Its current public interface accepts an ambient
  extended-ball curvature bound; `intrFrame_mem_eball` creates the radial input,
  and `framedExp_not_conj` eliminates a redundant public nonconjugacy premise.
  It still exposes completeness and local-diffeomorphism.  The common direct
  audit is green for all 28 P1a/P1b declarations, with only the three standard
  logical axioms.  The sequence-level producers still use global
  curvature/bounded geometry, while P3 supplies bounds separately on each fixed
  bounded ball.  The new raw local route is independently warning-free focused
  GREEN through radial local-diffeomorphism, canonical lift fencing,
  pull-volume/multiplicity, complete-extension joins, nonconjugacy, core
  distance equality, branch-Hessian positivity, pinned injectivity, and the
  exact raw-ball integral formula.
- Exact endpoints: E1 has global nonnegative Ricci curvature, compact closure
  of a relevant larger ball, and full-curvature/volume control only there, and
  concludes a point injectivity lower bound; E2 propagates a uniform base
  injectivity/noncollapse bound to a uniform injectivity bound on each fixed
  bounded ball.  P2 has no direct P1b call.  Most P3 inputs are complete
  kappa-solutions, but the `volcomp` use at `temp2kappa:2668` explicitly allows
  an incomplete ambient and prevents completeness from being imposed globally.
- Current action: retain the raw normal-map route and close only its final
  endpoint-facing gaps.  E1 is implementing compact `rawCore_short_inj`, then
  the actual-distance germ `rawCore_dist_germ`; strict Jensen, unique center,
  raw orbit/fiber count, and quantitative CGT assembly follow in that order.
  E2 is implementing the exact compact-buffer two-radius `rawBall_vol_rel`
  from `rawBall_integral_eq` and the arbitrary-curvature radial comparison.
  These three source lanes are mutually exclusive and permit focused checks
  only; no named refresh or broader build may run until they reach a common
  boundary.  Existing P0/global Hamilton consumers remain closed and are not
  being reopened.

### Remaining-frontier route audit

The live post-migration audit gives three genuinely different routes.

1. **Raw Jacobi producer followed by a raw CGT specialization.**  Use
   `mem_expDom_of_cpt` for compact-buffer raw-domain coverage, prove a
   curvature-controlled pointwise injectivity theorem for the differential of
   `framedExpMap`, and package it as local diffeomorphism on a tangent ball.
   Then specialize the checked Whitehead/Jensen/collision argument to the raw
   normal map and conclude with `framedInjRadius`.  This is the shortest native
   route and preserves the checked intrinsic/complete API.
2. **Abstract normal-map kernel.**  Refactor the CGT proof around a package of
   domain, smoothness, radial coverage, local-diffeomorphism, curvature, and
   pull-volume hypotheses, then instantiate it for both intrinsic and raw
   normal maps.  This can avoid proof duplication, but it changes a large
   checked layer and is justified only if the direct raw specialization proves
   structurally repetitive.
3. **Complete local extension.**  Extend or modify the metric outside the
   compact buffer to a complete auxiliary metric, apply the intrinsic CGT
   theorem, and transfer balls, volume, curvature, exponential maps, and
   injectivity radius back to the original metric.  The repository does not
   currently provide the required complete-extension-and-transfer package, so
   this route creates substantially more groundwork than Route 1.

The live gap is no longer representation, raw-domain existence, or
curvature-to-local-diffeomorphism.  `rawJacobi_ne_of_rm` assembles the closed
raw Jacobi equation, pointwise `Rm04` estimate, parallel frame, and covariant
Gronwall argument; `rawExp_mfderiv_inj`, `framed_mfderiv_inj`, and
`framed_locdiff_rm` provide the exact differential and IFT consequences without
ambient completeness.  E1 still needs a raw CGT collision/flat-loop
specialization and an all-launch-vector pull-volume upper bound; E2
additionally needs bounded-ball local volume/injectivity propagation.  No
endpoint is counted until those exact consumer statements are formally stated
and proved.

## P1c -- Laplacian comparison, Busemann, splitting, and soul

P1c starts only after P1b closes or reaches a precisely recorded genuine
blocker.  The expected order is the weakest reusable Laplacian-comparison
producer, then Busemann, then the Cheeger--Gromoll splitting endpoint, adjusted
only if the exact P3 consumers give a shorter native route.  The global
authority also assigns the Cheeger--Gromoll soul theorem to P1c as a separate
classical endpoint; it is not a corollary of splitting.  Missing distance
smoothness, cut-locus, barrier/weak-Laplacian, ray compactness, Hessian-trace,
or soul/exhaustion infrastructure must be isolated as the smallest native
bridge rather than replaced by a parallel hierarchy.

### Running status (2026-08-29, exact consumer and native-asset audits frozen)

- Laplacian-comparison endpoint: **100%**.  `dist_lap_distrib` is formally
  stated and proved on the punctured manifold under nonnegative Ricci curvature
  and positive transverse dimension; it is warning-free focused/named-refresh
  green and direct-axiom clean.
- Busemann weak-Laplacian endpoint: **100%**.  `busemann_lap` is formally
  stated and proved for a supplied minimizing ray; focused/named-refresh and
  direct-axiom checks are green.  The stronger `narrows` gradient-direction
  extension remains separate unfinished machinery.
- Cheeger--Gromoll splitting endpoint: **0%**.
- Cheeger--Gromoll soul endpoint: **0%**.
- Dedicated native machinery: **about 76--79%** across the whole four-endpoint P1c
  denominator.  Separately: the Laplacian endpoint's dedicated machinery is
  **100%**, the weak Busemann endpoint **100%**, splitting **84--87%**, and soul
  **5%**.  The broader Busemann package needed by `narrows`, including the
  almost-everywhere unit-gradient/asymptotic-ray direction, is about **75%**.
  The canonical compact-test predicate `IsLapLEDistribOn`, its restriction
  theorem, and `lapDistrib_of_smooth` are now checked.  Noncompact Green second
  identity and signed chart-integral transport are also checked.  The direct
  distance-specific polar route now additionally has signed function-level
  exponential change of variables, signed restricted-set polar evaluation, its
  `SegInt` specialization, the radial Jacobian scaling identity and derivative
  inequality, one-dimensional weighted integration by parts, a setwise
  full-measure regular-segment image in each ball, and compact-test annulus
  localization away from the pole.  `dist_grad_radial` now also proves that
  distance is differentiable on the nonzero regular minimizing exponential
  image and identifies its gradient with the outgoing unit radial velocity.
  `dist_green` now gives the noncompact compact-support weak Green identity for
  distance, and `dist_action_radial` identifies its action integrand pointwise
  on the nonzero regular minimizing locus.
- Current action: the distance-specific polar route and weak Busemann endpoint
  are closed.  The supplied-line splitting route has checked line-to-ray,
  Busemann-pair, weak-addition, pair-Laplacian, and compact-smooth-test Lipschitz
  energy producers.  The earlier arbitrary-continuous strong-minimum target was
  too broad for the exact consumer: the Busemann pair is intrinsically
  two-Lipschitz, so its local chart `W^{1,2}` witness can be built directly by
  cutoff and the Euclidean Lipschitz theorem.  `buse_pair_memW1p` is now
  warning-free focused-check green.  The sign-preserving smooth-test density
  theorem `MemH01.nonneg_approx` and the normalized metric coefficient package
  `exists_metric_coeff` are also warning-free focused-check and named-refresh
  green.  The
  formerly missing nonsmooth chart Green/energy compatibility theorem is now
  checked as `chart_super_of_lap`: it identifies the distributional inequality
  with the weighted coefficient bilinear form, and both its warning-free
  focused check and explicit named refresh are green.  The downstream zero-set
  propagation `buse_pair_eq_zero` and local weak-solution assembly
  `busemann_chart_sol` are now also warning-free focused and named-refresh
  green.  The signed-test bridge `IsSolution.bilin_eq_zero_smooth`, the public
  density extension `weak_eq_of_smooth`, and
  `IsSolution.to_homogeneous` are now warning-free focused/named-refresh green.
  Thus the weak-solution interface mismatch is closed.  The compact-free
  difference-quotient chain through `homSol_memW2` and its chart application
  `busemann_chart_h2` are now warning-free focused/named-refresh green.
  `homSol_diff_id` gives the first differentiated equation in the exact
  `D_j(D_l u)` order needed downstream.  The generic scalar-source chain is now
  checked through `srcSol_diff_id`, `srcDiff_weak_eq`, `homDiff_memWkp`, and
  `srcSol_memWkp_on`.  The latter performs the honest nested-inner-domain
  induction and proves `W^{m,2}` source regularity implies local `W^{m+2,2}`
  solution regularity.  `srcEq_restrict` supplies the required restriction of
  the actual `H_0^1` weak equation without extra compactness assumptions.  The
  homogeneous specialization `homSol_memWkp_on` and the actual chart/manifold
  Busemann consumers `busemann_chart_wkp`, `busemann_chart_cdiff`, and
  `busemann_smooth` are now warning-free focused/named-refresh green.  The
  converse bridge `lap_le_of_distrib` recovers a pointwise Laplacian upper bound
  from the compact-test inequality when the source is continuous; its focused
  check and named refresh are green.  The Bochner-side algebraic bridge
  `cov_zero_of_frob` is likewise focused/named-refresh green.  Pointwise
  harmonicity `busemann_lap_zero`, Bochner parallelism `busemann_grad_par`, the
  parallel-section geodesic bridge `intrinsic_intCurve`, generic complete-flow
  smoothness `curveAt_contMDiff`, and the six-interface Busemann flow module are
  now all warning-free focused and named-refresh green.  In particular the flow
  is global and jointly smooth, obeys the additive law, and translates the
  Busemann value exactly.  The live frontier is now the explicit zero-level-set
  product equivalence, followed by fixed-time flow diffeomorphisms and metric
  preservation.  Upgrading the algebraic product equivalence to a manifold
  diffeomorphism exposes the first genuine design/API blocker: the existing
  regular-level manifold construction is specialized to `MorseModel (m+1)`,
  whereas this endpoint is stated over an arbitrary finite-dimensional model
  `E`.  The next common audit will include all newly exported declarations.
  The general Euclidean `visc_div_le_integral` remains a distinct larger
  deferred API.
- P1d boundary: record exact Toponogov assumptions consumed downstream,
  including any used by the soul route; do not implement P1d in this campaign.

### Exact dependency order and acceptance boundary

1. **Ray producer.**  On a complete connected noncompact Riemannian manifold,
   every chosen basepoint admits a unit-speed minimizing ray with
   `dist (gamma s) (gamma t) = t - s` for `0 <= s <= t`.  This is a properness
   and compactness result, not a Toponogov theorem.
2. **Busemann metric producer.**  For such a ray,
   `dist (gamma t) x - t` decreases to a finite limit, the limit is
   one-Lipschitz, and its value on `gamma s` is `-s`.  General smoothness is not
   an acceptance requirement; local Sobolev regularity is used downstream.
3. **Weak Laplacian bridge.**  Under nonnegative Ricci curvature, first prove
   the distance-specific compact-test inequality directly on the measurable
   minimizing-segment domain.  The checked function-level exponential and
   polar formulas reduce it to the radial Jacobian differential inequality and
   one-dimensional integration by parts.  The existing non-sharp Calabi bound
   remains an alternate input for the larger viscosity route and is sufficient
   for the later escaping-pole decay once a distributional comparison exists.
4. **Supplied-line splitting.**  Complete plus nonnegative Ricci curvature and
   a minimizing line must yield a global Riemannian isometry with a product by
   `Real`, aligned with the supplied line.  A diffeomorphism alone is too weak.
   The proof still needs elliptic regularity/maximum principles, Bochner, and
   the parallel-gradient flow realization.
5. **Soul.**  This remains independent of splitting: nonnegative sectional
   curvature must produce compact totally convex/totally geodesic soul data and
   a normal-bundle diffeomorphism; positive sectional curvature supplies the
   point-soul/Euclidean specialization actually used in P3.  No native
   soul/normal-bundle/exhaustion chain currently exists.

### Direct polar-distance route

1. `expJac_map_eq`, `expJac_lintegral`, and `segInt_lintegral` promote the
   set-level area formula to function-level change of variables on every
   measurable injective exponential domain.  `setLIntegral_polar` and
   `segInt_polar` then expose the sphere-by-positive-radius integral with the
   Euclidean radial power carried by `volumeIoiPow`.
2. `integral_polar_prod`, `integral_polar`, `setIntegral_polar`,
   `expJac_integrable`, `expJac_integral`, `segInt_integral`, and
   `segInt_int_polar` are the checked signed Bochner/Fubini layer needed for the
   distributional pairing.  `expJacDensity_nonneg` is the canonical density
   sign lemma used by the change-of-variables proof.
3. `expJac_radial` is the checked bridge
   `expJacDensity (r • u) * r ^ (n - 1) = C * curveDensity r` for a transverse
   orthonormal Jacobi frame.  `intrDen_deriv_le` supplies its exact derivative
   and Ricci-zero upper bound, while `neg_mul_deriv_le` supplies the favorable
   weighted one-dimensional integration-by-parts inequality.
4. `segBall_reg_zero` proves that the complement of the regular minimizing
   exponential image inside each ball is volume-null.  `tsupp_dist_bounds`
   places every compact test supported away from the pole inside one finite
   positive-radius annulus.
5. The genuine first-order bridge is checked: `dist_green` gives the noncompact
   compact-support weak Green identity, while `dist_grad_radial` and
   `dist_action_radial` identify its action integrand on `Exp(SegInt)`.  The
   signed `volumeIoiPow` initial-segment integration-by-parts/exhaustion bridge
   and its polar reassembly are now checked as `radial_pairing_le` and
   `dist_pairing_le`.
6. `dist_lap_distrib` assembles the formal compact-test distributional
   comparison on `{p}ᶜ`.  Focused verification, the downstream-required named
   refresh, and the common direct axiom audit are green.  Existing
   `weak_grad_of_lip` remains compact-manifold-only; the larger cutoff and
   countable-chart alternatives are no longer on the immediate route.

### Supplied-line splitting frontier

The metric and weak inputs before the strong-minimum step are checked.
`IsMinimizingLine` supplies exact positive and negative minimizing rays;
`buse_pair_nonneg`, `buse_pair_zero`, and `buse_pair_line` give the two
Busemann functions' pointwise sum properties; `IsLapLEDistribOn.add` supplies
canonical weak addition; and `buse_pair_lap` proves that their sum has
distributional Laplacian at most zero.  All focused checks and required named
refreshes are green, and the common axiom audit is clean.

The splitting consumer does not require a new arbitrary-continuous
distributional strong-minimum principle.  Its Busemann pair is already
intrinsically two-Lipschitz.  `IsLapLEDistribOn.neg_int_le_energy` and
`lip_energy_nonneg` are focused-check green and convert the checked
distributional inequality into the correctly signed intrinsic energy
inequality against nonnegative smooth compact tests.  `buse_pair_memW1p` gives
the cutoff/chart local `DeGiorgi.MemW1p 2` witness and is warning-free focused-
check green.  This removes the old continuous-to-Sobolev regularity
gap without changing the splitting assumptions.

Three genuinely distinct native routes were audited for the remaining
chartwise weak-supersolution bridge:

1. **De Giorgi/Harnack.**  `weak_harnack_on_ball` requires
   `DeGiorgi.IsSupersolution`.  Local `MemW1p 2` is now available by the
   Lipschitz cutoff route, but no public theorem identifies its chart weak
   derivatives with the intrinsic energy pairing or with
   `bilinFormOfCoeff`.  The existing Harnack theorem also assumes dimension
   strictly greater than two, which is sufficient for the exact 3-dimensional
   Morgan--Tian consumer but not yet for a dimension-free splitting theorem.
2. **Harmonic replacement or mollification.**  Harmonic replacement already
   assumes `MemW1p 2`.  Local `L1` mollification exists, but no
   order-preserving variable-coefficient commutator converts the distributional
   inequality to smooth supersolutions; the Friedrichs and H1 approximation
   APIs already assume global `L2` weak derivatives or weak-solution data.
3. **Viscosity or heat flow.**  The viscosity tree lacks local-uniform limit,
   sum, and strong-minimum stability for these Busemann limits.  The available
   strong parabolic maximum principle and heat semigroup are compact/smooth or
   compact-`L2` results and cannot consume a noncompact linearly growing
   Lipschitz distributional supersolution.

The exact coefficient is `rho * g^-1`, represented by
`weightedInvGramOnEuclid`.  The smallest honest producer sequence was:

1. a nonsmooth local chart Green/divergence adapter identifying the compact
   smooth-test distributional inequality with the chart weak-gradient bilinear
   form;
2. a nonnegative smooth-compact density theorem for nonnegative `MemH01`
   tests, since the existing defining approximation need not preserve sign;
3. an elliptic-coefficient package for `rho * g^-1`, including inverse
   coercivity and the normalization consumed by the native weak Harnack API.

The local strong-minimum endgame is already checked as `super_zero_ball`:
for a normalized coefficient in dimension greater than two it uses
`weak_harnack`, constant shifts, an essential-infimum bound from continuity,
zero integral, and open positive measure to propagate an interior zero across
the quarter ball.  `super_zero_on_ball` is also warning-free focused-check and
named-refresh green and uses the existing normalized coefficient and
supersolution scaling API to give the same conclusion on every positive-radius
ball.  The sign-preserving density and normalized-coefficient producers are
checked; the chart bridge `chart_super_of_lap` is also warning-free focused and
named-refresh green.  Thus these are producer inputs to the checked consumer,
not new splitting assumptions.  Global propagation is only
the open-and-closed zero-set argument in `ConnectedSpace`; it does not require
a chart-overlap chain.  Adding `MemW1p`, coefficient data, or a supersolution
witness as a splitting hypothesis would merely move the frontier and is
forbidden.

That propagation is checked as `buse_pair_eq_zero`.  Around every
zero it chooses one ball compatible with both the checked local `W^{1,2}`
witness and compact chart containment, applies the checked chart bridge and
checked arbitrary-ball strong minimum, and pulls the resulting quarter-ball
zero set back to the manifold.  The proof then uses continuity, the line-base
zero, and connectedness.  The declaration is warning-free focused and
named-refresh green.

The post-minimum-principle regularity stage has also been source-audited.  Once
the Busemann pair is identically zero, the two individual Busemann functions
can be made opposite weak supersolutions for the same metric coefficient, hence
a local `DeGiorgi.IsSolution`.  The formerly private proof that an arbitrary
Lipschitz Euclidean function is in `W^{1,2}` on a finite-radius ball has now
been extracted to the canonical Euclidean Sobolev layer as
`memW1p_ball_of_lip`; it and the generic manifold producer
`raw_memW1p_of_lip` are warning-free focused/named-refresh green, and the
shortened pair consumer is focused green.  After pair zero, the negative
summand supplies the missing subsolution sign and the two chart supersolutions
assemble a local `DeGiorgi.IsSolution`.  That assembly is checked as
`busemann_chart_sol`, with warning-free focused and named-refresh verification.
The genuine next
analytic frontier is larger: no checked native
headline currently promotes a local smooth-coefficient `IsSolution` to a
smooth representative on a smaller ball.  `loc_nonsmooth_solution` supplies
approximant `H²` bounds but not the compactness/bootstrap/representative
assembly.  Even after that promotion, the Bochner endgame separately needs a
Busemann eikonal theorem and zero-Frobenius-Hessian/parallel-gradient bridges.
None of these missing producers may be added as assumptions to the splitting
statement.

### Deferred viscosity-to-distributional route audit

1. **Direct Euclidean divergence-form theorem.**  In a Euclidean chart, prove
   `visc_div_le_integral` for a smooth positive density and a smooth symmetric,
   locally uniformly elliptic coefficient field: a lower-test viscosity bound
   for `rho^-1 div(A grad u)` implies the nonnegative compact-test integral
   inequality.  Existing `densityOnEuclid`, `weightedInvGramOnEuclid`, their
   smoothness/positivity/ellipticity results, the public noncompact chart
   formulas, and finite compact-support partition-of-unity reduction cover the
   geometric transport.  No native or Mathlib theorem supplies the analytic
   Euclidean implication itself.
2. **Inf/sup-convolution and mollification.**  This route needs viscosity
   preservation, semiconvex approximation, Alexandrov almost-everywhere second
   differentiability, and a limit theorem.  The repository's mollifier and
   Friedrichs tools start from weak/Sobolev information and would therefore be
   circular; the required viscosity/semiconvexity APIs are absent.
3. **Dirichlet or harmonic replacement.**  A comparison proof would need local
   classical Dirichlet solvability, interior/boundary regularity, and
   viscosity-versus-weak comparison.  The native elliptic tree has weak
   De Giorgi infrastructure but not this classical replacement chain, so this
   route is strictly larger than Route 1.

The obstruction on this general route is therefore missing PDE groundwork, not
a coercion or typeclass problem.  `visc_div_le_integral` remains a substantial
analytic development.  It is no longer the immediate P1c lemma because the
distance-specific polar proof has a strictly smaller faithful dependency
surface.  No theorem-shaped assumption or consumer wrapper has been added in
its place.

The P1d boundary is exact.  Constructing a line in an at-infinity limit for
Morgan--Tian `topsplit`, including the required distance-gradient direction,
uses their length-comparison/Toponogov input.  Their source proof of the soul
theorem also calls that comparison theorem.  P1c records both dependencies but
does not implement either P1d producer.

## Program accounting

- Final theorem `poincare_of_inputs`: **0%** (not declared).
- P1a theorem endpoints: **100%** (eight of eight); P1b: **0%** (zero of two);
  P1c: **75%** (three of four independently counted endpoints: Laplacian, weak
  Busemann comparison, and supplied-line metric splitting are complete; Soul
  remains 0%).  Across P1a--P1c this is eleven of fourteen endpoints, **78.6%**.
  Do not collapse these distinct denominators into a misleading single
  percentage.
- Whole P0--P9 program infrastructure: retain the global authority's current
  **15--25%** estimate; P1 audit or helper work must not inflate it.

## Dependency table

This table is filled from live source evidence during each phase.

| Phase | Morgan--Tian consumer | Exact assumptions/conclusion | Native producer | Classification | Verification/axioms |
|---|---|---|---|---|---|
| P1a | MT 1.34; 5.6; 8.10 | Complete/global metric; Ricci lower bound; compare two radii, then upper/lower volume bounds give packing | `segBall_vol_rel`, `segBall_vol_le`, `segBall_card` | checked producer | focused checks passed; direct axiom print has only standard logical axioms |
| P1a | MT 9.11, 9.59--9.63 | Complete; global `Ric >= 0`; power-law ratio and Euclidean absolute upper bound | `segBall_vol_pow`, `segBall_vol_le_euclidean` | checked producer plus thin zero-curvature adapter | focused/named-refresh checks passed; the common direct axiom audit reports only standard logical axioms |
| P1a | MT 5.9--5.11, 5.15; P3 `volcomp` | Compact closure of a strictly larger buffer ball and `Ric >= 0` on the compared ball; conclude the Euclidean absolute upper bound needed in the incomplete-ambient flow-limit route | `ball_vol_le_eucl`, using `minExp_of_cptBall`, `rawBall_vol_le_int`, `rawDens_le_zero`, and `normalHaar_eq` | checked endpoint | focused verification and exact named refresh are green; the 196-declaration unified audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The separate local two-radius theorem remains a textbook extension, not a ninth project-used endpoint |
| P1a | MT 9.66 | a sufficiently small radius has Euclidean-normalized volume within any prescribed relative error; no audited consumer needs a public abstract limit | `framedDens_zero`, `framedDens_haar`, `exists_ball_ratio`, `exists_euclid_ratio` | checked producer and endpoint | focused checks passed; both normalization theorems and the endpoint are axiom-clean |
| P1a | MT 9.66 | continuity in radius, used to choose a half-model-volume radius | `segBall_vol_cont` via polar integral, sphere-null, and dominated convergence | checked endpoint | focused/named-build verification passed; common axiom audit has only standard logical axioms |
| P1a | MT 9.56 | global strict positive sectional curvature makes every positive-radius intrinsic ball strictly smaller than its Euclidean comparison ball | checked bottom equality chain and radial propagation `transDens_eq_rigid`; checked general strict producers `expJac_lt_of_ricci` and `segBall_vol_lt`; checked smooth-manifold `normalHaar_eq`, `gBall_model_eucl`, `rm04_eq_inner_riem`, and sectional-to-Ricci bridges; exact wrapper `segBall_lt_of_sec` | checked endpoint | all dependencies and `SegmentBallEuclideanStrict` itself are warning-free focused/named-refresh green; common direct audit reports only `propext`, `Classical.choice`, and `Quot.sound` |
| P1b E1 | MT `volinj`; `basicconv`; `2ndmfdconv`; P3 `flowlimit` and the local `basicconv` use | Global `Ric >= 0` is available in every actual P3 use; a relevant larger ball has compact closure and a uniform local `|Rm|` bound; a smaller ball has `Vol >= epsilon*r^n`; conclude `inj(p) >= delta(n,epsilon)*r`. Ambient completeness cannot be required because of `temp2kappa:2668` | checked `intrInj_ge_cgt_on` and `intrInj_ge_vol`; the completeness-free raw chain is checked through radial Jacobi nonvanishing/local diffeomorphism, canonical lift fencing, pull-volume/multiplicity, complete-extension minimizing joins, `rawCore_min_regular`, `rawBranch_hess_pos`, and `rawExt_pinned_inj`; `flowInj_of_vol` realizes the stronger complete/global-bounded-geometry special case | exact local endpoint missing | every listed raw prerequisite is warning-free focused GREEN and every artifact with a real downstream consumer is exactly refreshed. The next genuine producer is compact short-bigon exclusion (`rawCore_short_inj`), followed by actual-distance strict Jensen, center of mass, and the quantitative raw CGT assembly; no ambient-completeness wrapper is permitted |
| P1b E2 | MT `mfdconv` proof, then P3 `flowlimit` | On each fixed bounded ball: compact closure and uniform curvature-derivative bounds; uniform positive base inj/noncollapse; conclude a uniform positive inj lower bound throughout that ball, allowing incomplete ambient manifolds | `injDecay_of_bg` gives the complete global special case; the local raw-polar chain is checked through `rawExp_inj_seg`, measurable strict segment domain, exact image identification, and `rawBall_integral_eq`, with `BishopRawDensity` providing the radial density comparison inputs | conditional producer; exact local-on-balls endpoint missing | the complete special case and raw integral machinery are focused/named green and direct-axiom clean. The exact next theorem is the two-radius local comparison `rawBall_vol_rel`; its source lane must add only the smallest arbitrary-radius density bridge actually absent from the checked API |
| P1c ray | MT `ends`, `prelim.tex:1093-1124` | complete connected noncompact manifold and chosen point; obtain a unit-speed minimizing ray with exact pairwise distance on nonnegative times | checked `properSpace_riemMetric`, `IsMinimizingRay`, and `exists_minRay` | checked producer | `MinimizingRay` is warning-free focused/named-refresh green and the common audit reports only the three standard logical axioms; no Toponogov dependency |
| P1c Laplacian | MT weak distance comparison, `prelim.tex:887-908,958-1000` | under `Ric >= 0`, distance from a pole satisfies the compactly supported distributional upper inequality needed for escaping-pole limits | `dist_lap_distrib`, assembled from the checked radial/Riccati chain, signed polar change of variables, compact-support Green identity, `radial_pairing_le`, and `dist_pairing_le` | checked endpoint | endpoint is warning-free focused and named-refresh green; the common direct audit reports only `propext`, `Classical.choice`, and `Quot.sound` |
| P1c Busemann | MT `prelim.tex:1128-1178`, especially `Blambda` | finite decreasing limit, one-Lipschitz continuity, value `-s` on the ray, and weak `Delta B <= 0`; `narrows` additionally needs a.e. unit-gradient/asymptotic-ray direction | checked metric core plus `busemann_lap`, obtained from escaping-pole `dist_lap_distrib` and compact-support dominated convergence | checked weak endpoint; stronger `narrows` extension missing | endpoint is warning-free focused/named-refresh green and the 58-declaration common audit reports only standard logical axioms; local Sobolev/unit-gradient/asymptotic-direction machinery remains for `narrows` |
| P1c splitting | MT `prelim.tex:1528-1606`, `line`; the supplied-line result is the P1c consumer | supplied unit-speed minimizing line plus complete connected `Ric >= 0` gives an aligned global Riemannian product | `busemannMetricSplit`, assembled from the checked Busemann harmonic/parallel chain, complete gradient flow, smooth regular zero level, `busemannProdDiffeo`, induced level metric, product metric, and the horizontal/vertical/mixed differential identities | checked endpoint | final module is warning-free focused and explicitly named-refresh GREEN; the 148-declaration common audit reports only `propext`, `Classical.choice`, and `Quot.sound`; constructing a line from two ends for `topsplit` remains P1d-dependent and is not part of this endpoint |
| P1c soul | MT `prelim.tex:1295-1321`, `soul`; actual P3 uses at `temp2kappa:2293,3581,3612,3714,3727` | the actual consumers need only the positive-sectional-curvature point-soul specialization, the resulting three-dimensional Euclidean diffeomorphism, and neck separation/isotopy consequences | sectional-curvature, Hopf--Rinow, Busemann, Morse-flow, and point-normal-coordinate assets are checked, but there is no genuine total-convexity, soul-existence, point-soul, or Euclidean-diffeomorphism producer | missing project-used producer; endpoint 0% | the first source-faithful endpoint-moving angle-at-infinity lemma invokes `lengthcompar`/Toponogov twice, an exact P1d boundary; a standalone convexity predicate would not close or materially advance this endpoint |

## Status log

- 2026-08-27: plan created after confirming that the historical
  `VOLUME_COMPARISON_PLAN.md` is absent.  P1a consumer/native/axiom audits are
  starting; P1b and P1c remain intentionally undispatched.
- 2026-08-27: froze the P1a consumer table from Morgan--Tian Chapters 1, 5, 8,
  and 9.  Added and focused-checked `hypRadVol_zero`, `segBall_vol_pow`,
  `curve_cauchy_speed`, and `curve_lim_of_compact`.  The attempted framed
  density value-one normalization was rejected as false: the chart model basis
  is not generally orthonormal, so its positive determinant factor must be
  carried through the small-ball calculation.  P1b and P1c remain undispatched.
- 2026-08-27: audited three equality-rigidity routes and the local
  compact-closure route.  The local obstruction is not the already-built
  compact-tail limit theorem alone: current segment-polar definitions are tied
  to complete-only intrinsic geodesics.  Equality rigidity has a smaller common
  algebraic entry point at the equality case of `trace_sq_le_mul`; its geometric
  continuation is the equality-or-strict case of `mean_riccati_le`.
- 2026-08-27: focused/named-build/axiom verification passed for
  `framedDens_zero`, `framedDens_haar`, `endpointCont_of_lim`,
  `endpointCont_compact`, and `geo_Ioo_extend_cpt`.  `segBall_vol_cont` and
  `trace_sq_eq_iff` pass focused checks; their remaining export/axiom checks and
  the downstream `exists_euclid_ratio` check are serialized behind the shared
  B2 elaboration window.  Claims remain held during that coordination window.
- 2026-08-27: rechecked the exact MT 9.56/9.66 use.  No P2/P3 consumer requires
  a public abstract small-ball `Tendsto` theorem: 9.56 consumes the already
  checked finite-radius Euclidean upper bound, while 9.66 needs one small-radius
  lower bound (the epsilon endpoint) plus radius continuity and an intermediate
  value argument.  Also localized the incomplete-manifold route to
  `minExp_of_cptBall`, but recorded that it still needs a phase-lift/maximal-ray
  bridge and would not by itself remove `CompleteSpace` from segment-polar
  integration.
- 2026-08-27: official focused verification and direct axiom capture passed for
  `exists_ball_ratio` and `exists_euclid_ratio`; both use only the standard
  logical axioms.  This closes the fifth of eight P1a project-used endpoints.
- 2026-08-27: `segBall_vol_cont` passed focused and named-module verification
  after mechanical local style cleanup.  The common P1a audit then passed for
  all six checked volume endpoints and all three compact-tail bridges, with only
  `propext`, `Classical.choice`, and `Quot.sound`.  Separately,
  `trace_sq_eq_iff`, `mean_sq_eq_iff`, and `mean_riccati_eq_iff` are checked and
  axiom-clean dedicated machinery; the final volume-rigidity endpoint remains
  unstated and therefore 0%.
- 2026-08-27: source-written but deliberately uncredited pending validation:
  radial equality propagation (`transDens_eq_rigid`), its strict-Jacobian
  contrapositive (`expJac_lt_of_ricci`), strict positive-Ricci model-volume
  comparison (`segBall_vol_lt`), and the low sectional-to-Ricci bridges.  Three
  focused passes on `SegmentPolar` exposed only local elaboration/coercion
  repairs.  A fifth focused pass and the explicit named refresh then succeeded
  (3980/3980), so `transDens_eq_rigid`, `segBall_vol_le_int`, and
  `gBall_model_int` are verified exported producers; direct axiom audit is
  still pending.  The exact next normalization brick is the pole-density/model-
  Haar pushforward identity `normalHaar_eq`; endpoint completion remains six of
  eight and dedicated machinery is about 95%.
- 2026-08-27: the first focused pass on `SegmentPolarRigidity` reported no
  error in `expJac_lt_of_ricci`; `segBall_vol_lt` initially had four local
  elaboration issues.  Three were discharged immediately.  The remaining
  open-set-positivity call did not consume either the inferred or explicitly
  installed parent instance in two further passes, so it has now been rewritten
  to call the existing additive-Haar instance's `open_pos` field directly.
  The fourth focused pass then completed warning-free, so both strict producers
  are locally verified.  Neither is yet credited as the final MT endpoint:
  the new module still needs a named refresh when its exports are consumed,
  direct axiom audit, and the separate Euclidean model-ball normalization.
- 2026-08-27: `normalHaar_eq` passed a warning-free focused check and its
  explicitly named `BishopPolarFramed` refresh (3905/3905).  The downstream
  `gBall_model_eucl` normalization has now been source-written without new
  Ricci, metric-realization, or dimension assumptions; it remains 0% as a
  checked theorem until its own focused verification.
- 2026-08-27: the new radial equality proof had raised `SegmentPolar.lean` to
  3034 lines, past the repository limit.  The declaration
  `transDens_eq_rigid` was therefore moved verbatim (statement, docstring,
  attribute wrapper, and proof unchanged) to the dedicated
  `SegmentPolarEquality.lean`; the base file is now 2883 lines.  The old
  location was green; the edited base then passed a warning-free focused check
  and named refresh (3980/3980), and the new equality module passed its own
  warning-free focused check and named refresh (3981/3981).  Direct axiom audit
  remains pending.
- 2026-08-27: the first focused pass on `gBall_model_eucl` reached the intended
  proof and exposed only local elaboration issues: two unqualified sphere
  names, zero-curvature `if True` simplification, ENNReal multiplication versus
  measure scalar action, an under-specified `normalHaar_eq` invocation, and a
  missing explicit `Nontrivial E` witness for the Haar closed/open ball lemma.
  These are being repaired statically; no named refresh was run.  The exact
  MT 9.56 wrapper `segBall_lt_of_sec` is source-written but remains a 0%
  endpoint pending all dependency checks, its own focused verification,
  refresh, and axiom audit.
- 2026-08-27: two subsequent focused passes on `gBall_model_eucl` reduced the
  local failures first to ENNReal scalar-action normalization and a manifold
  smoothness mismatch, then to the latter alone.  Source inspection showed that
  `omega` is the analytic outer top whereas `infinity` is the smooth grade, so
  `IsManifold.of_le` cannot manufacture the former from the latter.  The real
  issue was the overly strong global analytic binder in
  `BishopPolarFramed.lean`; it has been weakened to the smooth grade used by the
  framed normal-coordinate API, and the impossible consumer-side instance has
  been removed.  Both producer and consumer are source-written with unchanged
  public consumer assumptions, but remain unchecked after this correction.
- 2026-08-27: the first focused pass after the grade correction stopped at the
  producer binder because this file's open ENNReal scope parsed an unqualified
  infinity symbol as `ENNReal` rather than `WithTop ENat`.  The downstream
  diagnostics were all cascades from that first type mismatch.  A second pass
  showed that a result type ascription does not override scoped notation
  selection, so the binder now uses the notation-free coercion of the top ENat
  grade into `WithTop ENat`.  No refresh or consumer check was run, and the
  smooth-manifold generalization still awaits re-verification.
- 2026-08-27: the notation-free smooth-manifold `BishopPolarFramed` source then
  passed a warning-free focused check and its explicitly named refresh
  (3905/3905).  The downstream `gBall_model_eucl` proof elaborated completely;
  its only diagnostics are local unused-section-variable warnings for
  `T2Space M` and `SigmaCompactSpace M`.  Per project rules its refresh was not
  run; the theorem is being wrapped in the corresponding `omit` before a final
  focused recheck.
- 2026-08-27: after the declaration-local `omit` cleanup,
  `SegmentBallEuclideanUpper.lean` passed a warning-free focused check and its
  explicitly named refresh (3981/3981).  Thus `gBall_model_eucl` is now a
  checked producer, while the exact MT 9.56 theorem endpoint remains 0% until
  the curvature bridges and `segBall_lt_of_sec` itself are checked and
  axiom-audited.
- 2026-08-27: `CoordRm04Bridge.lean` passed a warning-free focused check and
  its explicitly named refresh (3746/3746).  The next `SectionalRicci` focused
  pass stopped at its file-level manifold binder because bare smooth-infinity
  notation was unavailable without the ContDiff scope; all subsequent errors
  were cascades.  Its binder is being replaced by the same notation-free smooth
  grade used above; no sectional refresh or rigidity check was run.
- 2026-08-27: after the binder correction, the next `SectionalRicci` pass
  reached the proof bodies and stopped only because `exists_perp_pos` was not
  in its import cone.  Its canonical home is the native
  `Comparison.Variation.PerpFrame` module, already used by the volume-comparison
  stack.  The file is gaining that single direct import; no sectional refresh
  or rigidity check was run.
- 2026-08-27: with the direct `PerpFrame` import, `SectionalRicci.lean` passed a
  warning-free focused check and its explicitly named refresh (3933/3933).
  `SegmentPolarRigidity.lean` then reached only two identical Euclidean-volume
  type mismatches: theorem-local `InnerProductSpace` creation had made
  `MeasureSpace.toMeasurableSpace` diverge from the earlier private borel
  instance.  The two Euclidean theorems are now in a narrow section that installs
  the inner-product instance before fresh local borel instances, matching the
  checked normalization module.  Public assumptions are unchanged; no rigidity
  refresh was run.
- 2026-08-27: the first Euclidean-section reordering still inherited the
  file-level private measurable instance, so the same two `volume` diamonds
  remained.  The corrected route now scopes the original borel instances to a
  `General` section containing only the non-Euclidean strict theorems; the
  disjoint `Euclidean` section installs `InnerProductSpace` before its sole
  fresh borel pair.  An explicit `@volume` route was rejected because the
  chosen inner-product measure instance still consumes the ambient measurable
  instance and exposes the same diamond.  The scoped route preserves every
  public assumption and awaits a focused recheck.
- 2026-08-27: the disjoint-scope route still produced the same two measure
  diamonds, so the third distinct route split the Euclidean adapters at their
  natural abstraction boundary.  `SegmentPolarRigidity.lean` now contains only
  `expJac_lt_of_ricci` and `segBall_vol_lt` (236 lines).  The unchanged
  `segBall_vol_lt_eucl` and exact `segBall_lt_of_sec` wrappers occur exactly once
  in the new 82-line `SegmentBallEuclideanStrict.lean`, whose global
  `InnerProductSpace` binder precedes its sole borel instance pair exactly as in
  the checked Euclidean Upper module.  The import graph is acyclic, public
  theorem statements are unchanged, and both modules await focused/named
  verification before the common axiom audit.
- 2026-08-27: the split resolved the instance diamond.
  `SegmentPolarRigidity.lean` passed a warning-free focused check and its
  explicitly named refresh (3982/3982).  `SegmentBallEuclideanStrict.lean`
  then elaborated both Euclidean wrappers successfully; its only diagnostic is
  an unused lambda binder at line 79.  Per the warning-clean acceptance rule no
  named refresh was run.  This is a routine static linter repair, not a theorem
  or API blocker; the strict endpoint remains formally 0% until the repaired
  module is warning-free, refreshed, and included in the direct axiom audit.
- 2026-08-27: after replacing the unused lambda binder by `_`,
  `SegmentBallEuclideanStrict.lean` passed a warning-free focused check and its
  explicitly named refresh (4045/4045).  Both exact Euclidean wrappers are now
  checked; the endpoint remains conservatively outside the completed count only
  until the common direct axiom audit runs.
- 2026-08-27: `P1AxiomCheck.lean` passed its expanded focused audit in 77.0s.
  All 20 printed endpoints and producer/continuation bridges, including
  `segBall_lt_of_sec`, depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.  P1a therefore closes at seven of eight project-used endpoints
  (87.5%).  The sole remaining theorem endpoint is the local compact-closure
  Bishop--Gromov form (0%); its three genuinely different attempted routes and
  exact missing groundwork are recorded above.  P1b may now start without
  reopening this blocker.
- 2026-08-27: all eight P1a file-claim tokens were released after the final
  static diff review.  P1b then started, in phase order, with three mutually
  exclusive read-only xhigh tasks: exact Morgan--Tian consumers, native
  producer/axiom coverage, and minimal adapter scouting.  No P1b Lean file is
  claimed or edited until the consumer and producer maps are merged.
- 2026-08-27: the frozen P1b source audit found two, and only two,
  comparison-geometry endpoints in the P2/P3 dependency closure: pointwise
  local volume-to-injectivity (`volinj`) and base-to-bounded-ball injectivity
  propagation.  P2 has no direct use.  Five P3 `flowlimit` applications and
  one `basicconv` application use curvature bounds separately on each fixed
  bounded ball.  The `temp2kappa:2668` application explicitly permits
  incomplete ambient flows, so the exact endpoints must use compact closure of
  the relevant balls rather than global completeness.  All actual P3 inputs do
  have global nonnegative curvature operator, hence global `Ric >= 0` is an
  honest common denominator-control hypothesis.
- 2026-08-27: `intrInj_ge_cgt_on` was added at the native CGT layer with the
  radial-local Rm bound already consumed by the Whitehead/propeller proof.  The
  old `intrInj_ge_cgt` signature and its two external P0 call sites remain
  unchanged as a compatibility theorem.  The file passed a warning-free
  focused check and explicitly named refresh (4061/4061).  This is dedicated
  machinery, not completion of E1; the next producer is the explicit
  volume-denominator assembly `intrInj_ge_vol`.
- 2026-08-27: the first focused pass for the source-written
  `intrInj_ge_vol` stopped before theorem elaboration because the new module
  declared `RiemannianBundle` before disabling the two competing tangent-space
  normed instances.  This produced a local inner-product/PseudoEMetricSpace
  instance cascade and terminal `whnf` heartbeat failures; no named refresh was
  run.  The static repair is to use the already checked `CGTInjectivity` header
  ordering.  The mathematical volume-denominator route is unchanged, and E1
  remains 0% until the exact compact-closure hypotheses are discharged.
- 2026-08-27: after that header-only repair, `CGTVolumeInjectivity.lean`
  passed a warning-free focused check (27.2s) and its explicitly named refresh
  (4072/4072).  `intrInj_ge_vol` is now checked dedicated machinery; it still
  does not close E1 because its complete ball-volume producer and explicit
  `hloc`/nonconjugacy premises are stronger than the incomplete compact-closure
  Morgan--Tian use.
- 2026-08-27: two smaller native bridges were then isolated.  The first
  Coordinates attempt incorrectly stated ambient membership in `Metric.ball`
  while assuming only `PseudoEMetricSpace`, and referred to an out-of-scope
  unqualified `riemannianEDist`; that focused check failed and no refresh or
  Jacobi check ran.  After restating it as `intrFrame_mem_eball` entirely at the
  `edist` layer, `IntrinsicFramedCoordinates.lean` passed warning-free focused
  verification (46.7s) and named refresh (3818/3818).  The derivative bridge
  `framedExp_not_conj` in `IntrinsicFramedJacobi.lean` then passed warning-free
  focused verification (22.8s) and named refresh (3831/3831).  These remove the
  metric-ball-to-radial and redundant-nonconjugacy adapter gaps; they do not
  provide incomplete-ambient compact-tail minimizing coverage.
- 2026-08-27: `intrInj_ge_vol` was then restated with the weaker ambient
  `Metric.eball` curvature input and with nonconjugacy generated internally
  from `hloc`; its explicit denominator and conclusion were unchanged.  The
  revised module passed warning-free focused verification (24.0s) and named
  refresh (4073/4073).  The expanded common axiom audit then passed in 103.5s:
  all 28 P1a/P1b declarations, including `injDecay_of_bg`,
  `injDecay_realizes`, and `flowInj_of_vol`, depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- 2026-08-28: the proposed compact-eball producer `frame_mem_expDom` was
  rejected before creating Lean source.  The live raw domain is represented by
  a witness for the fixed-chart vector field `geodesicVectorFieldChart g x`;
  outside the initial chart source that field is zero, while compact closure of
  an intrinsic eball supplies no chart-source containment.  Three distinct
  routes were assessed: a source-contained theorem that does not cover MT, a
  global chart-independent witness/domain redesign, and a larger base-geodesic
  domain with downstream migration.  Hence P1b closes at a genuine
  foundational API/design blocker with both exact endpoints still 0% and its
  dedicated checked machinery about 94%; P1c may now start after P1b claims are
  released.
- 2026-08-28: P1c scope was reconciled with the newer global authority before
  implementation.  Besides Laplacian comparison, Busemann, and splitting,
  `POINCARE_PLAN.md` assigns the Cheeger--Gromoll soul theorem to P1c as an
  independent fourth endpoint because P3 uses both the positive-curvature
  point-soul consequence and soul basepoints for noncompact kappa-solutions.
  Any Toponogov input exposed by that route is recorded as the P1d boundary and
  is not implemented here.
- 2026-08-28: the exact P1c consumer and native-asset audits were frozen.  The
  native tree already has the smooth Calabi upper-support producer needed for
  the distance comparison, so another smooth Laplacian wrapper would be
  duplicate infrastructure.  It has no minimizing-ray/Busemann layer and no
  barrier-to-intrinsic-weak-Laplacian theorem; splitting also lacks the weak
  elliptic regularity, parallel-gradient, and product-isometry chain, while the
  soul endpoint has no dedicated native chain at all.  The first implementation
  brick is therefore the properness-based `exists_minRay`, followed by the
  metric Busemann limit.  All four formal endpoints remain 0%; whole-P1c
  dedicated machinery is estimated at 15--25%, with the narrower checked
  Calabi/distance-Laplacian submachinery at 80--90%.
- 2026-08-28: `MinimizingRay.lean` now supplies the properness/compact-direction
  ray producer, and `Busemann.lean` supplies the finite decreasing metric limit,
  one-Lipschitz estimate, and value `-s` along the ray.  Both modules passed
  warning-free focused verification and explicit named refresh.  The separate
  `DistanceBarrier.lean` packages the existing Calabi support as an honest
  epsilon-relaxed upper barrier and also passed warning-free focused/named
  verification.  The expanded common audit passed for all 39 printed
  declarations with only `propext`, `Classical.choice`, and `Quot.sound`.
  These are verified producers, not formal P1c endpoints: all four endpoints
  remain 0%, while whole-P1c dedicated machinery is now estimated at 20--30%.
  The next concrete producer is barrier-to-lower-test viscosity, followed by
  local-uniform stability and the intrinsic weak bridge.
- 2026-08-28: `GradientRegularity.lean` now supplies the local smooth
  subtraction rule `laplacian_sub_at`, and `LaplacianViscosity.lean` uses it
  with the native minimum theorem to prove
  `IsLapLEBarrierAt.to_viscosity`.  Both passed warning-free focused checks and
  explicit named refreshes.  The common audit now covers 41 declarations and
  again reports only `propext`, `Classical.choice`, and `Quot.sound`.  This is
  checked analytic infrastructure, not the formal Laplacian endpoint: that
  endpoint remains 0%.  The next brick is the canonical compact-test
  distributional predicate plus its smooth Green adapter, after which the
  genuine viscosity-to-distributional theorem remains the single analytic
  frontier.
- 2026-08-29: the canonical distributional layer is now checked.
  `green_second_of_supp` supplies the noncompact compact-support Green identity;
  `IsLapLEDistribOn` records the exact Morgan--Tian nonnegative compact-test
  inequality; and `lapDistrib_of_smooth` proves the smooth pointwise adapter
  with only a locally integrable right-hand side.  Public noncompact signed
  chart formulas (`integral_eq_chart`, `integral_model`, and `integral_euclid`
  with indicator variants) preserve all old compact API signatures.  Every
  module passed warning-free focused verification and the required named
  refresh, and the common audit now covers 46 declarations with only
  `propext`, `Classical.choice`, and `Quot.sound`.  Three routes to the remaining
  viscosity-to-distributional implication were assessed; all expose the same
  missing Euclidean PDE theorem `visc_div_le_integral` or a strictly larger
  absent regularity hierarchy.  All four formal P1c endpoints therefore remain
  0%; whole-P1c dedicated machinery is about 25--30% and Laplacian-specific
  machinery about 75--80%.
- 2026-08-29: after auditing the general viscosity theorem against two shorter
  alternatives, P1c selected the distance-specific polar route.  New checked
  producers are `expJac_map_eq`, `expJac_lintegral`, `segInt_lintegral`,
  `setLIntegral_polar`, `segInt_polar`, and the exported `expJac_radial`.
  Focused checks and required named refreshes are green.  The aggregate audit
  covers the first three change-of-variables declarations and
  `expJac_radial`, bringing it to 50 declarations with only `propext`,
  `Classical.choice`, and `Quot.sound`; the two latest polar adapters await the
  next audit pass.  All four formal P1c endpoints remain 0%.  Whole-P1c
  dedicated machinery is about 30%, and Laplacian-specific machinery is about
  80--85%.  The next producer is the radial-weight derivative inequality,
  followed by one-dimensional integration by parts.
- 2026-08-29: the direct polar route has now discharged the routine signed and
  radial-calculus layer.  Checked producers are `integral_polar_prod`,
  `integral_polar`, `setIntegral_polar`, `expJacDensity_nonneg`,
  `expJac_integrable`, `expJac_integral`, `segInt_integral`,
  `segInt_int_polar`, `intrDen_deriv_le`, and `neg_mul_deriv_le`; their focused
  checks and every required named refresh are green.  `segBall_reg_zero` gives
  the setwise null complement of the regular minimizing exponential image in a
  ball, and `tsupp_dist_bounds` gives a positive finite annulus containing any
  compact test support away from the pole; both are also warning-free focused
  green, with `segBall_reg_zero` named-refreshed.  This advances dedicated
  machinery only: all four P1c endpoints remain 0%, whole-P1c machinery is
  about 30--35%, and Laplacian-specific machinery about 88--92%.  The first
  remaining geometric producer is distance differentiability with radial
  gradient on `Exp(SegInt)`.  The first remaining analytic producer is the
  noncompact compact-support weak Green/radial-pairing identity.  Three routes
  were audited (distance-specific polar, noncompact Rademacher--Sobolev, and
  regular-locus cutoff); only the first has the smallest faithful dependency
  surface, but it still requires those two genuine producers.
- 2026-08-29: `dist_grad_radial` discharged the first remaining geometric
  producer.  Its double-`branchRadius` sandwich uses the reversed minimizing
  tail and proves both differentiability of distance and the exact outgoing
  unit radial gradient on nonzero `SegInt`; focused verification and the named
  refresh are warning-free green.  The four formal P1c endpoints remain 0%.
  Whole-P1c dedicated machinery is about 32--36%, Laplacian-specific machinery
  about 90--93%, and the next producer is exclusively the noncompact
  compact-support weak Green identity before signed polar assembly.
- 2026-08-29: the direct polar route is complete.  `radial_pairing_le` proves
  the signed weighted inequality on almost every initial minimizing ray;
  `dist_pairing_le` performs the model-Haar Fubini reassembly; and
  `dist_lap_distrib` is the formal punctured-manifold distributional distance
  comparison.  The smooth-grade binders in `SegmentRayInterval`,
  `SegmentIntegral`, and `SegmentBallIntegral` were corrected from accidental
  analytic outer-top annotations without strengthening consumer assumptions.
  Every edited module is warning-free focused green, all downstream-required
  named refreshes are green, and the 52-declaration common audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  P1c is now one of four
  endpoints complete (**25%**); whole-P1c dedicated machinery is about
  **38--42%**.  The next concrete target is the project-used Busemann weak
  Laplacian endpoint via escaping integer poles.
- 2026-08-29: `busemann_lap` closes the weak Busemann endpoint for a supplied
  minimizing ray.  It applies `dist_lap_distrib` at escaping integer poles,
  removes the constant shift by compact-support divergence, passes the left
  side by dominated convergence, and squeezes the reciprocal-distance right
  side to zero on the compact test support.  The theorem is warning-free
  focused and named-refresh green, has no heartbeat override or frontier
  assumption, and the final 58-declaration common audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  P1c is now two of four formal endpoints
  complete (**50%**), while the stronger `narrows` unit-gradient/asymptotic-ray
  extension remains unfinished machinery.  The next formal endpoint is the
  supplied-line Cheeger--Gromoll splitting theorem.
- 2026-08-29: the supplied-line route now has checked canonical line data and
  all pre-maximum-principle Busemann producers.  `IsMinimizingLine.pos_ray` and
  `.neg_ray` expose the two rays; `buse_pair_nonneg`, `buse_pair_zero`, and
  `buse_pair_line` give the metric sum facts; `IsLapLEDistribOn.add` is the
  generic weak algebra bridge; and `buse_pair_lap` gives the exact
  distributional superharmonic sum.  Focused and required named checks are
  warning-free green, and the expanded 58-declaration audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  Splitting itself remains
  unstated (**0%**); its dedicated machinery is about **25--30%**.  Direct
  De Giorgi/Harnack, harmonic-replacement/mollification, and viscosity/heat
  routes all fail at documented missing APIs.  The smallest next lemma is a
  weighted chart bridge from the continuous distributional inequality to local
  `W^{1,2}` `DeGiorgi.IsSupersolution`; this is a substantial analytic producer,
  not a local elaboration issue.
- 2026-08-29: the exact Busemann consumer removes the earlier need for an
  arbitrary continuous-to-Sobolev theorem.  `IsLapLEDistribOn.neg_int_le_energy`
  and `lip_energy_nonneg` are warning-free focused green, and
  `buse_pair_memW1p` is warning-free focused green using intrinsic
  two-Lipschitz control, a smooth chart cutoff, and Euclidean weak derivatives.
  `super_zero_ball` is also warning-free focused green and closes the local
  normalized-coefficient strong-minimum argument in dimension greater than
  two.  All three new modules needed by the common audit were explicitly named-
  refreshed, and the expanded 62-declaration focused audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  Splitting itself remains
  unstated (**0%**); its dedicated machinery is
  about **35--40%**.  `MemH01.nonneg_approx` and `exists_metric_coeff` are now
  warning-free focused/named-refresh green, so the live frontier has narrowed to chart weak-
  energy compatibility for `weightedInvGramOnEuclid` and its closure from
  nonnegative smooth tests to arbitrary nonnegative `H₀¹` tests.  Neither may
  be moved into the splitting statement as a new assumption.
- 2026-08-29: `MemH01.nonneg_approx` is warning-free focused/named-refresh green and returns
  one limit witness together with pointwise nonnegative smooth compactly
  supported approximants converging in the function and every weak-gradient
  component `L²` norm.  `exists_metric_coeff` is warning-free focused/named-refresh green and
  constructs the normalized positive-scalar `ρ g⁻¹` coefficient on every chart
  ball with compact closure in the chart target.  `laplacian_chart_div` and
  `chart_div_test_le` are also warning-free focused green, so the smooth-test
  distributional inequality now reaches the exact Euclidean chart-divergence
  form.  The remaining analytic lemma is the honest weak-derivative integration
  by parts and `H₀¹` closure producing `DeGiorgi.IsSupersolution`; splitting
  itself remains unstated (**0%**).
- 2026-08-29: `super_zero_on_ball` is warning-free focused/named-refresh green.  It transports
  the checked unit-ball strong minimum through the existing normalized
  coefficient and supersolution scaling theorems, with no new analytic or
  splitting assumption.  Once the chartwise `IsSupersolution` bridge is green,
  the local Busemann-pair zero propagation can therefore use an arbitrary small
  chart ball directly.
- 2026-08-29: `chart_super_of_lap` is source-written with no new frontier
  hypothesis.  It constructs compactly supported smooth coefficient extensions,
  applies weak-coordinate integration by parts, and closes arbitrary
  nonnegative `H₀¹` tests using `MemH01.nonneg_approx` and bilinear-form
  continuity.  It remains **0% complete** until its first focused check passes;
  no elaboration was started while the shared guard was occupied.
- 2026-08-29: `buse_pair_eq_zero` is source-written with the exact supplied-line,
  `Ric >= 0`, and dimension-greater-than-two assumptions already consumed by
  the native weak-Laplacian and strong-minimum chain.  Its local chart proof and
  global clopen propagation add no new splitting hypothesis.  It remains **0% complete**
  until `chart_super_of_lap` and its own focused check pass.  Splitting itself
  remains unstated (**0%**), with dedicated machinery conservatively held at
  about **35--40%** pending those gates.
- 2026-08-29: `chart_super_of_lap` passed warning-free focused verification
  after three local elaboration-only repair rounds, then its explicit named
  refresh completed GREEN (8766/8766).  The proof has no `sorry` and introduces
  no new analytic or splitting hypothesis.  The live gate is now the focused
  verification of `buse_pair_eq_zero`; splitting itself remains unstated
  (**0%**) and its dedicated machinery remains conservatively **35--40%** until
  that consumer is checked.
- 2026-08-29: the local Busemann-pair Sobolev proof was factored at its canonical
  layers without changing its public consumer statement.  The Euclidean
  `memW1p_ball_of_lip` producer and manifold `raw_memW1p_of_lip` adapter both
  passed warning-free focused verification and their required named refreshes;
  the shortened `buse_pair_memW1p` consumer then passed warning-free focused
  verification.  This is checked dedicated machinery only: the splitting
  theorem remains unstated (**0%**) and the next gate is still
  `buse_pair_eq_zero`.
- 2026-08-29: `busemann_chart_sol` is source-written in its dedicated comparison
  module with the exact supplied-line, completeness, connectedness, dimension,
  and `Ric >= 0` inputs already required downstream.  It uses one checked local
  Sobolev witness, pair-zero to obtain the negative witness, one normalized
  coefficient, and two checked chart supersolution bridges; it introduces no
  wrapper predicate or new frontier hypothesis.  It remains **0% verified**
  until `buse_pair_eq_zero` and its own focused verification pass.
- 2026-08-29: `buse_pair_eq_zero` and `busemann_chart_sol` both passed
  warning-free focused verification and their explicitly required named
  refreshes (9055/9055 and 9056/9056).  They introduce no new splitting
  assumption and contain no placeholders.  Splitting itself remains unstated
  (**0%**); its checked dedicated machinery is now about **45--50%** and the
  smallest live analytic producer is the local smooth-coefficient weak-solution
  to smooth-representative bridge.
- 2026-08-29: the expanded common `P1AxiomCheck` passed warning-free with 70
  direct declarations.  The canonical Euclidean/manifold Sobolev producers,
  nonnegative `H₀¹` density, normalized coefficients, arbitrary-ball strong
  minimum, chart supersolution bridge, Busemann-pair zero propagation, and local
  Busemann weak solution all depend only on `propext`, `Classical.choice`, and
  `Quot.sound`; no project axiom or `sorryAx` appears.
- 2026-08-29: the post-weak-solution regularity audit found a genuine local PDE
  frontier, not an adapter mismatch that can be hidden.  The De Giorgi solution
  uses an explicit `MemW1pWitness.weakGrad`, whereas the current Nirenberg
  `SmoothEllipticBilinearForm.IsWeakSolution` evaluates the classical `fderiv`
  of the nonsmooth function.  Its smooth route assumes the desired smoothness;
  its approximation route additionally assumes global `L2`, a classical-
  derivative weak equation, and a uniform mollified-source bound; and the
  checked chart difference-quotient chain is packaged with `[CompactSpace M]`.
  None is an honest consumer of the local noncompact Busemann solution.  The
  smallest canonical analytic producer is therefore a witness-based interior
  `IsSolution`-to-`W^{2,2}` difference-quotient theorem, followed by
  differentiated-equation bootstrap.  A routine interface repair is being
  separated from that mathematics: the Busemann chart producer must retain the
  already proved positive scale and its equality with the weighted inverse
  metric coefficient.  Independently, the supplied-ray compactness route is
  now directed at `exists_asymp_ray`: unit initial directions of minimizing
  segments to escaping poles have a compact-sphere subsequential limit whose
  ray gives the exact global Busemann distance-support inequality.  This does
  not use P1d/Toponogov.  Until focused verification is green these are active
  producers, not completed machinery; endpoint and percentage accounting are
  unchanged.
- 2026-08-29: `busemann_chart_data`, `exists_asymp_ray`, and
  `busemann_grad_sq` are now checked and included in the common audit.  The
  chart producer retains the normalized coefficient scale; the asymptotic-ray
  producer retains a unit initial direction and a global Busemann support; and
  the eikonal theorem proves unit squared gradient norm under the weakest
  actual pointwise input `MDifferentiableAt`, with no Ricci or global
  smoothness assumption.  Their focused checks and required named refreshes
  are warning-free green.  The expanded 73-declaration `P1AxiomCheck` is also
  warning-free green and every printed declaration depends only on `propext`,
  `Classical.choice`, and `Quot.sound`.  Formal P1c endpoints remain two of
  four (**50%**); splitting itself remains unstated (**0%**).  Checked
  splitting-dedicated machinery is about **55--60%**, whole-P1c machinery
  about **64--68%**, and the whole P0--P9 program remains about **15--25%**.
  The smallest genuine frontier is still a witness-based local
  `DeGiorgi.IsSolution`-to-`W^{2,2}` interior regularity producer, followed by
  differentiated-equation bootstrap; eikonal geometry is no longer part of
  that blocker.
- 2026-08-29: the first witness-regularity interface gap is closed.
  `exists_smooth_cutoff` is now the public canonical compact-in-open cutoff;
  `IsSolution.bilin_eq_zero_smooth` writes an arbitrary signed smooth test as
  the difference of two nonnegative smooth tests; `weak_eq_of_smooth` extends
  the equality by the existing `H₀¹` density argument; and
  `IsSolution.to_homogeneous` exposes the equality-form weak solution consumed
  by difference quotients.  All three edited producer modules are
  warning-free focused green, their required named refreshes are green, and
  the expanded 77-declaration audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  Formal P1c endpoints remain two of
  four (**50%**); splitting remains unstated (**0%**).  Splitting-dedicated
  machinery is now about **58--62%**, whole-P1c machinery about **65--69%**,
  and the whole P0--P9 program remains **15--25%**.  The exact next producer is
  a compact-free, witness-native local difference-quotient energy bound; the
  local `W^{2,2}` theorem is still unstated (**0%**) even though its dedicated
  generic machinery is about **80%** complete.
- 2026-08-29: the compact-free local `W^{2,2}` producer is now complete.
  `homSol_dq_bound`, `homSol_second`, and `homSol_memW2` assemble the global
  witness, standard-test square bound, quantitative master inequality, and
  difference-quotient weak-limit theorem.  `busemann_chart_h2` applies this
  chain on an inner chart ball, and `homSol_diff_id` proves the first
  differentiated divergence-form equation in the required weak-partial order.
  Every exporting module is warning-free focused/named-refresh green.  The
  expanded 88-declaration `P1AxiomCheck` is warning-free green, and every
  printed declaration depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.  Formal P1c endpoints remain two of four (**50%**); splitting
  and soul remain unstated (**0%** each).  Splitting-dedicated machinery is now
  about **66--70%**, whole-P1c machinery about **68--71%**, and the whole
  P0--P9 program remains about **15--25%**.  Three independent route audits
  agree that the smallest honest next producer is a compact-free local
  `W^{2,2}` estimate for a divergence-form equation with `W^{1,2}` vector
  source; compact resolvent/domain-power and mollification routes would add
  larger independent frontiers.
- 2026-08-29: the fixed-order scalar-source bootstrap is now complete.
  `hasWeakDiv_of_parts` and `weakRHS_eq_integral` lower the differentiated
  vector source to a scalar `L²` pairing.  `srcSol_substOn`,
  `src_master_nonsmooth`, and `srcSol_memW2` give the corresponding compact-free
  scalar-source `W^{2,2}` estimate.  `homDiffField`, `homDiffSource`,
  `homDiff_hasDiv`, and `homDiff_weak_eq` then identify the differentiated
  homogeneous equation with source `rho * homDiffSource`, with the positive
  sign fixed by the weak-divergence convention.  Finally `homSol_memW3`
  assembles the canonical chosen derivatives and proves `W^{2,2} -> W^{3,2}`
  on the inner set.  Every new exporting module is warning-free focused and
  explicitly named-refresh green.  The expanded 101-declaration common axiom
  audit is warning-free green, and every printed declaration depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.  Formal P1c endpoints remain
  two of four (**50%**), and
  splitting and soul remain unstated (**0%** each.  Splitting-dedicated
  machinery is about **70--74%**, whole-P1c machinery about **69--72%**, and
  the whole P0--P9 program remains about **15--25%**.  A separate all-order
  audit found no multi-index obstruction: the next smallest producer is the
  differentiated weak equation for a nonzero scalar source, followed by a
  nested-inner-domain induction to all Sobolev orders.
- 2026-08-29: the all-order scalar-source bootstrap is now complete.
  `srcSol_diff_id` differentiates the actual scalar-source weak equation,
  `srcDiff_weak_eq` packages each chosen first derivative with source
  `D_l f + rho * homDiffSource`, and `homDiff_memWkp` proves the coefficient
  source has the required arbitrary Sobolev order.  `srcEq_restrict` localizes
  the actual equation to any smaller open set.  Finally `srcSol_memWkp_on`
  carries out structural induction on the source order with one precompact
  intermediate domain at each successor step.  All four exporting modules are
  warning-free focused and explicitly named-refresh green, with no new
  assumptions, predicates, or axioms.  Formal P1c endpoints remain two of four
  (**50%**); splitting and soul remain unstated (**0%** each.  Splitting-
  dedicated machinery is about **76--80%**, whole-P1c machinery about
  **72--75%**, and the whole P0--P9 program remains about **15--25%**.  The next
  smallest producer is the homogeneous specialization, followed immediately by
  local all-order and smooth Busemann chart regularity.
- 2026-08-29: the homogeneous and smooth Busemann specialization is now checked.
  `homSol_memWkp_on` specializes the scalar-source induction without adding a
  compactness hypothesis; `busemann_chart_wkp`, `busemann_chart_cdiff`, and
  `busemann_smooth` turn the actual supplied-line Busemann weak solution into a
  globally smooth function.  `lap_le_of_distrib` supplies the necessary
  continuous-source distribution-to-pointwise converse, and `cov_zero_of_frob`
  turns the later zero Frobenius energy into vanishing covariant derivative.
  All are warning-free focused and explicitly named-refresh green.  Formal P1c
  endpoints remain two of four (**50%**), with splitting and soul unstated
  (**0%** each); splitting-dedicated machinery is about **82--85%**, whole-P1c
  machinery about **75--78%**, and the whole P0--P9 program about **15--25%**.
  The next smallest producer is pointwise harmonicity of the supplied-line
  Busemann function, then the Bochner parallel-gradient conclusion.
- 2026-08-29: the supplied-line flow and raw product-coordinate layers are now
  checked.  `busemann_lap_zero`, `busemann_grad_par`, `intrinsic_intCurve`,
  `curveAt_contMDiff`, and `curveAtDiffeo` give the harmonic/parallel complete
  flow.  `busemannFlow_line` identifies its sign with the supplied line, while
  `busemannProdEquiv`, `busemannProdHomeo`, and `busemann_deriv_ne` give a
  universe-polymorphic algebraic and topological product over the raw zero
  subtype.  Every exporting module is warning-free focused and explicitly
  named-refresh GREEN.  The formal splitting theorem remains unstated
  (**0%**); splitting-dedicated machinery is about **86--88%**, whole-P1c
  machinery about **77--80%**, and the whole P0--P9 program remains about
  **15--25%**.  A generic regular-level manifold/diffeomorphism cannot yet use
  the current Morse API because both `IsCriticalPointAt` and `LevelSetSpace`
  are restricted to `Type` and `RegularSublevel` is specialized to
  `MorseModel`; narrowing P1c's universes would be an unacceptable public
  regression.  Independently, the bottom APIs for flow metric preservation are
  present, and the active next producer is the connection-level theorem that
  the spatial differential of a complete parallel flow is parallel.  The
  expanded common axiom audit will run only after that producer chain settles.
- 2026-08-29: the generic connection-level flow producer is now checked.
  `curveAt_mfderiv_par` proves, by a two-parameter smooth variation and
  commuting covariant derivatives, that the spatial differential of a
  complete parallel flow is parallel along every orbit.  Its focused check and
  explicit named refresh are both warning-free GREEN; the common axiom audit
  has been extended but remains deferred until the immediately downstream
  metric-preservation producer settles.  This is checked dedicated machinery,
  not a completed splitting theorem: the formal splitting endpoint remains
  unstated (**0%**), splitting-dedicated machinery is about **88--90%**,
  whole-P1c machinery about **79--81%**, and the whole P0--P9 program remains
  about **15--25%**.  The next smallest lemma is `curveAt_inner_eq`, followed
  by equality of the fixed-time pulled-back metric.
- 2026-08-29: the parallel-flow metric chain is now checked through its
  Busemann specialization.  `curveAt_inner_eq` uses metric compatibility and
  `curveAt_mfderiv_par` to prove constancy of the inner product of two spatial
  differential fields; `curveAt_pullback_eq` packages this as fixed-time
  pullback-metric equality; and `busemannFlow_inner` specializes the result to
  the supplied-line gradient flow.  Both exporting modules are warning-free
  focused and explicitly named-refresh GREEN.  The formal splitting endpoint
  remains unstated (**0%**); splitting-dedicated machinery is about
  **90--92%**, whole-P1c machinery about **80--82%**, and the whole P0--P9
  program remains about **15--25%**.  A fresh regular-level audit found that
  the existing Morse charts, manifold instance, inclusion, and factor theorem
  are mathematically sufficient; the next smallest API step is their surgical
  universe generalization, followed by invariance of `IsCriticalPointAt` under
  `ModelWithCorners.transContinuousLinearEquiv`.
- 2026-08-29: the regular-level model bridge is now checked.  `SublevelSpace`
  and `LevelSetSpace`, the public Morse manifold declarations, and the
  regular-level chart/manifold/inclusion/factor API are universe-polymorphic;
  every generalized module is warning-free focused and explicitly
  named-refresh GREEN.  `isCrit_trans_iff` proves, without any differentiability
  hypothesis, that critical-point status is invariant under
  `ModelWithCorners.transContinuousLinearEquiv`.  This closes the former
  `Type 0`/model-change API gate without adding a global instance, wrapper
  predicate, or splitting assumption.  The formal splitting endpoint remains
  unstated (**0%**); splitting-dedicated machinery is about **92--94%**,
  whole-P1c machinery about **82--84%**, and the whole P0--P9 program remains
  about **15--25%**.  The next smallest producer is the standard smooth product
  diffeomorphism, built locally from the existing regular-level structure and
  `busemannProdEquiv`.
- 2026-08-30: the standard smooth product diffeomorphism is now checked.
  `busemannProdDiffeo` equips the regular zero level with the canonical Morse
  manifold structure and upgrades `busemannProdEquiv` to a smooth equivalence
  with the ambient manifold.  Its focused check and explicit named refresh are
  warning-free GREEN.  The required weakest-assumption repair in
  `RegularSublevel` was restricted to the exact 17-declaration producer closure:
  its ambient manifold grade is now the project's smooth inner top rather than
  analytic outer top, with final focused and named-refresh verification GREEN.
  This is still dedicated machinery: the formal Cheeger--Gromoll metric
  splitting statement remains unstated (**0%**), splitting-dedicated machinery
  is about **94--96%**, whole-P1c machinery about **83--85%**, and the whole
  P0--P9 program remains about **15--25%**.  The next smallest canonical layer
  is the induced metric of a smooth immersion and the product Riemannian metric,
  followed by the horizontal, vertical, and mixed Busemann-flow identities and
  the non-tautological pullback-metric equality.
- 2026-08-30: the Soul-theorem denominator has been narrowed to the actual
  Morgan--Tian consumers.  P2 does not use Soul.  P3 uses only the
  positive-sectional-curvature specialization: a selectable point soul, the
  resulting three-dimensional Euclidean diffeomorphism, and the downstream
  separation/isotopy facts for neck central spheres.  It does not consume the
  full nonnegative-curvature normal-bundle hierarchy.  The current native tree
  has sectional-curvature-to-Ricci, Hopf--Rinow/minimizing-geodesic, Busemann,
  Morse-flow, induced-metric, point-normal-coordinate, and generic deformation-
  retract machinery, but it has no all-minimizing-segments total-convexity API,
  smooth normal bundle/tubular exponential for an embedded submanifold,
  Sharafutdinov retraction, soul existence, point-soul theorem, or Euclidean
  diffeomorphism endpoint.  More importantly, Morgan--Tian's first genuine
  soul-moving lemma is the angle-at-infinity estimate, whose proof invokes
  `lengthcompar`/Toponogov twice.  That is an exact P1d boundary and is outside
  this campaign.  Accordingly the project-used Soul endpoint remains unstated
  (**0%**) and its dedicated machinery is only about **0--5%**; generic geometry
  assets are not counted toward that percentage.  A standalone total-convexity
  predicate would be a legitimate future API brick but would not by itself move
  the endpoint, so P1c will not build a parallel Soul hierarchy around it.
- 2026-08-30: the supplied-line Cheeger--Gromoll metric splitting endpoint is
  now complete.  `localPull_smooth`, `immersionPullMetric`, and
  `immersionPull_inner` provide the canonical induced-metric layer;
  `prodMetric` and `prodMetric_inner` provide the product metric;
  `busemannProd_mfderiv`, `busemannLevelMetric`, `busemannProd_horiz`,
  `busemannProd_vert`, and `busemannProd_cross` identify the four metric
  blocks.  The public `busemannMetricSplit` internally chooses the
  `finrank(E)-1` Morse model and proves that the existing Busemann product
  diffeomorphism pulls the ambient metric back to the level metric times the
  flat real metric; callers supply no coordinate equivalence.  The final file
  is warning-free focused GREEN and explicitly named-refresh GREEN.  The
  expanded 148-declaration common axiom audit is warning-free GREEN, and every
  printed declaration, including `busemannMetricSplit`, depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.  Formal P1c endpoints are now
  three of four (**75%**): distributional Laplacian comparison, Busemann weak
  comparison, and supplied-line metric splitting are complete; Soul remains
  unstated (**0%**) at the exact P1d/Toponogov boundary.  Splitting-dedicated
  machinery is **100%**; under the corrected actual-consumer denominator,
  whole-P1c dedicated machinery is about **75--78%**, rather than counting
  generic geometry assets toward Soul.  The whole P0--P9 infrastructure
  estimate remains about **15--25%**, while the final Poincare theorem endpoint
  remains unstated (**0%**).
- 2026-08-30 aggregate accounting: across the actual project-used P1a--P1c
  denominator, ten of fourteen formal endpoints are checked (**71.4%**).
  P1a is seven of eight (**87.5%**) with about **98%** dedicated machinery;
  P1b is zero of two (**0%**) despite about **94%** dedicated machinery; P1c is
  three of four (**75%**) with about **75--78%** dedicated machinery under the
  corrected Soul denominator.  These figures remain separate on purpose:
  infrastructure is not theorem completion.  The unresolved endpoints are the
  local compact-closure Bishop producer, the two incomplete-ambient CGT
  consumers, and the positive-curvature Soul specialization.  The whole
  Poincare final theorem remains unstated (**0%**); the broad P0--P9
  infrastructure estimate remains **15--25%**.
- 2026-08-30 P1a compact-continuation closeout: `chart_vf_on_iff`,
  `geoLift_isIntegralOn`, `gvf_eqOn`, `geo_Ioo_extend_to`, and `exists_geo_one_cpt` are all
  warning-free focused GREEN.  The first three newly exported modules and the
  compact-geodesic module have fresh targeted artifacts, and the unified
  153-declaration `P1AxiomCheck.lean` focused audit is warning-free GREEN and
  every printed declaration depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.  The new compact theorem gives a base geodesic through time one
  under a compact closed-eball buffer and no ambient completeness.  It does not
  imply the current raw `expDomain`, because `IsGeodesicOnWithInitial` still
  records integral curves of the fixed-initial-chart vector field.  Three
  distinct routes are now exhausted: adding chart-source containment is true
  but misses the Morgan--Tian consumer; changing the existing support semantics
  to the global field is faithful but a foundational public API migration; and
  introducing a second base-geodesic domain creates a forbidden parallel
  hierarchy and a larger downstream migration.  The minimal canonical migration
  touches the support definition and proofs in `Geodesic/MaximalInterval.lean`,
  then the direct old-support constructions in `Geodesic/MaximalRescaling.lean`,
  `Exponential/Defs.lean`, `Exponential/ChartFlow/PreconnectedPropagation.lean`,
  `Exponential/ChartFlow/RescaledLift.lean`,
  `Exponential/ChartFlow/ChainedFlowContinuity.lean`,
  `Exponential/GaussLemmaPullback.lean`, and
  `Metric/LocalIsometryRigidity.lean`; unchanged-signature Jacobi, Bishop, and
  CGT consumers are regression checks.  No such public definition rewrite is
  authorized in the current campaign, so P1a closes at this exact design/API
  blocker with seven of eight endpoints (**87.5%**), P1b remains zero of two,
  aggregate P1 remains ten of fourteen (**71.4%**), and no endpoint percentage
  is credited for these completed helpers.
- 2026-08-30 P1a raw-domain follow-up: the authorized support migration has now
  passed `MaximalRescaling.lean` focused verification after only local
  elaboration repairs; its missing artifact was restored by one explicit
  exclusive-window named refresh (3754/3754).  The new canonical
  `Exponential/Smoothness/Domain.lean` is warning-free focused green and proves
  supported-point smoothness of raw `expMap`, openness of `expDomain`, and
  smoothness on that domain without ambient completeness.  The compact-ball
  minimizing assembly `minExp_of_cptBall` is source-written without placeholders
  but is not yet focused-verified or axiom-audited, so it remains 0% as a theorem
  endpoint.  P1a therefore remains seven of eight (**87.5%**) while dedicated
  machinery is about **98--99%**; aggregate P1 remains ten of fourteen
  (**71.4%**).  The next checks are `MinimizingGeodesic.lean` and
  `RadialSurjectivity.lean`, followed by the compact truncated raw segment-domain
  and localized area/Jacobi bridge.
- 2026-08-30 P1a raw local-polar assembly: the weakened
  `broken_minimizer_velocity_match` and the reusable noninjective manifold image
  theorem `riemVol_image_le` are warning-free focused green.  The latter exposes
  the coordinate-free `mapJacDensity` and needs only `C¹` regularity on an open
  neighborhood of a compact source, with no injectivity or completeness.
  Source-complete, placeholder-free downstream adapters now identify the raw
  exponential map density with the existing radial `curveDensity`, bound a
  compact raw exponential image, prove compactness and metric-ball coverage of
  the buffered raw minimizing locus, and assemble `rawBall_vol_le_int` without
  ambient completeness.  They remain unverified until their new upstream
  artifacts can be refreshed outside the current multi-task parallel window;
  the new rule allows only focused checks while tasks run concurrently.  Hence
  P1a remains seven of eight endpoints (**87.5%**), the compact-closure Bishop
  endpoint remains unstated (**0%**), dedicated machinery remains about
  **98--99%**, and aggregate P1 remains ten of fourteen (**71.4%**).  The next
  smallest independent producer is `curveDensity_le_on`; after it, the genuine
  raw frontier is pole normalization plus expDomain-local radial Jacobi data.
- 2026-08-30 P1a density-comparison producers: `curveDensity_le_on` is now a
  warning-free focused-green scalar theorem deriving the model-density bound
  from the localized mean comparison, ratio antitonicity, and pole limit.
  `radialDensity_pole` is also warning-free focused green in `RadialGram.lean`;
  it proves the Euclidean pole normalization directly for raw radial Jacobi
  fields and a generic finite orthonormal family, without intrinsic-geodesic,
  metric-completeness, or `hEnorm` assumptions.  The model counterpart
  `hypDensity_pole` is warning-free focused green.  The combined
  `radialRatio_pole` is source-complete and was independently checked by
  temporarily expanding that one model-limit call, but its final canonical
  source awaits the new `HyperbolicModel` artifact and is therefore not yet
  counted as verified.  P1a endpoint accounting stays seven of eight
  (**87.5%**) and the compact-closure theorem stays unstated (**0%**).  The next
  producer is the expDomain-local radial Jacobi regularity/Jacobi-equation
  package; after it, raw no-conjugacy/injectivity remains the genuine geometric
  frontier.
- 2026-08-30 P1a raw pole regularity: `radial_jacobi_d0` and
  `radial_jacobi_reg0` are warning-free focused GREEN without `CompleteSpace M`,
  `PseudoEMetricSpace`, `hEnorm`, Ricci, or small-radius assumptions.  They use
  the open raw exponential domain and a pole-local smooth joint variation to
  identify the prescribed initial derivative and supply exactly the two
  chart-regularity facts at zero.  The final sources have no placeholders but
  remain formally unverified because `Smoothness/Domain.olean` is absent and
  parallel-task policy forbids a named refresh.  Endpoint accounting therefore
  remains P1a seven of eight (**87.5%**), aggregate P1 ten of fourteen
  (**71.4%**), and the compact-closure Bishop theorem itself **0%**.  The next
  smallest producer is an endpoint-weakened Wronskian constancy lemma, followed
  by `raw_exp_inj_of_min`.
- 2026-08-30 P1a endpoint Wronskian bridge: `wronskian_zero_Ioo` is now
  warning-free focused GREEN.  It keeps the curve, field, and covariant-
  derivative regularity on the closed interval but needs the two Jacobi
  equations only on the open interval; the old `wronskian_zero_on` signature is
  preserved as a compatibility corollary.  This removes unnecessary endpoint
  Jacobi assumptions from the radial orthogonality step.  The raw index-form
  route still needs a separate endpoint-closure bridge for `IsJacobiSolOn`, so
  the compact-closure Bishop endpoint remains unstated (**0%**), P1a remains
  seven of eight (**87.5%**), and aggregate P1 remains ten of fourteen
  (**71.4%**).  The next concrete theorem remains `raw_exp_inj_of_min`;
  focused-only verification may resume after the shared window handback, but no
  named refresh/build is permitted while tasks remain parallel.
- 2026-08-30 P1a raw linear-independence adapter: `radialJacobi_li_of` is
  source-written in `Volume/RadialGram.lean`.  It consumes only a nonzero radial
  time, membership in the raw exponential domain, and injectivity of the raw
  exponential differential; scaling plus `radial_jacobi_dom` then transports an
  independent initial family to the corresponding radial Jacobi fields.  It
  removes the old normal-chart source and small-`expMapC2Radius` hypotheses from
  this bridge without adding completeness or a wrapper predicate.  Focused
  verification and unified axiom audit remain pending, so no endpoint credit is
  assigned; P1a stays **87.5%**, aggregate P1 stays **71.4%**, and the compact-
  closure Bishop theorem stays **0%**.
- 2026-08-30 P1a pointwise raw regularity: `radial_jacobi_reg` is now
  source-written under the single hypothesis `t • x ∈ expDomain g p`.  It
  returns exactly the two chart differentiability facts for the raw radial
  variation and its covariant derivative, without endpoint Jacobi,
  completeness, metric, curvature, or norm assumptions.  The earlier
  `radial_jacobi_reg0` signature is preserved as its zero specialization.  Both
  declarations await focused verification because their upstream artifact is
  still stale; no endpoint credit changes.
- 2026-08-30 P1a raw Gram focused attempt: `RadialGram.lean` stopped at the two
  expected stale-import identifiers, `radial_jacobi_dom` and
  `hypDensity_pole`; the former occurs at the new `radialJacobi_li_of` bridge,
  so its body was not elaborated.  No local proof diagnostic was produced.
  Dependency refresh remains prohibited during the parallel-task window, and
  the endpoint and machinery percentages are unchanged.
- 2026-09-01 P1a raw Gram recheck: `RadialGram.lean` is now warning-free
  focused GREEN as a whole.  The raw-domain linear-independence adapter
  `radialJacobi_li_of`, pole-normalized raw density `radialDensity_pole`, and
  hyperbolic-model ratio `radialRatio_pole` all elaborate; the earlier stale
  identifiers no longer block the file.  No refresh/build was run.  This closes
  producer verification only and does not change endpoint accounting.
- 2026-09-01 P1a raw segment-domain recheck: `SegmentDomain.lean` is
  warning-free focused GREEN.  The compact buffered equality locus
  `isCompact_rawSeg` and its raw exponential ball-coverage theorem
  `ball_sub_rawSeg` both elaborate without ambient completeness.  They remain
  producer machinery; the compact-closure Bishop inequality is still unstated
  and endpoint accounting is unchanged.
- 2026-09-01 P1a raw area adapter: `SegmentArea.lean` is warning-free focused
  GREEN through `riemVol_rawExp_le`.  The general raw exponential image measure
  is bounded by the time-one radial Gram density on every compact subset of
  `expDomain`; an unused positive-finrank section instance was removed from the
  theorem scope.  No refresh/build was run, and endpoint accounting is
  unchanged.
- 2026-08-30 P1a Jacobi-system endpoint closure: the native
  `IsJacobiSolOn.of_Ioo` producer is warning-free focused GREEN.  Under only a
  nondegenerate interval, closed-interval continuity of the field, velocity,
  and acceleration, and the two ordinary derivative equations on the open
  interval, it recovers both one-sided endpoint equations by Mathlib's
  derivative-limit API.  It adds no completeness, endpoint-value, or operator-
  wrapper hypothesis.  This closes the last generic ODE bridge needed by the
  raw index-form route; `raw_exp_inj_of_min` remains the next concrete theorem.
  Endpoint accounting is unchanged: P1a is **87.5%**, aggregate P1 is
  **71.4%**, and the compact-closure Bishop theorem remains unstated (**0%**).
- 2026-09-01 P1a Jacobi germ transport: `jacobiAt_congr` is warning-free
  focused GREEN.  It transports `IsJacobiAt` using only equality germs for the
  base curve and the underlying model-space values of the vector field; two
  applications of private covariant-derivative locality recover the required
  second derivative.  No derivative germ, completeness, or curvature
  hypothesis is added.  The theorem is now listed in the pending unified axiom
  audit.  Endpoint accounting is unchanged.
- 2026-08-30 P1a signed radial-geodesic bridge: the canonical geodesic-layer
  theorem `expMap_smul_max_ne` now handles every nonzero scalar by monotone or
  antitone inverse rescaling and is warning-free focused GREEN; the existing
  positive `expMap_smul_eq_max` interface is preserved as a direct corollary.
  The pointwise consequence `raw_radial_geo_at` is implemented in the new
  bridge module `Exponential/Smoothness/RadialGeodesic.lean`, above both raw-
  domain openness and maximal rescaling.  It covers the pole by the stationary
  identities and otherwise identifies the raw radial germ with the maximal
  geodesic, with no completeness assumption.  Its focused check is now
  warning-free GREEN; no refresh/build was run in the parallel-task window.
  No endpoint percentage changes.
- 2026-08-30 compact minimizing endpoint focused attempt: checking
  `RadialSurjectivity.lean` stopped at import preflight because the new
  `Exponential/BufferedExpDomain.olean` does not yet exist.  The checker never
  reached `minExp_of_cptBall`, so this records an artifact-freshness blocker,
  not a source or mathematical failure.  The required named refresh remains
  prohibited while tasks are parallel; theorem and phase percentages are
  unchanged.
- 2026-08-30 compact-domain producer recheck: the missing artifact's defining
  module `BufferedExpDomain.lean` is itself warning-free focused GREEN.  Thus
  the downstream preflight failure is isolated to artifact freshness; no
  source repair is pending in `mem_expDom_of_cpt`.  A named refresh still waits
  for an exclusive window.
- 2026-09-01 P1a completeness-free second variation: the canonical
  `indexForm_nonneg_var` producer and the refactored
  `indexForm_nonneg_of_minimising_geodesic` wrapper are warning-free focused
  GREEN.  The proof now reuses `exists_var_fix_ends`, whose compact-support
  global-flow construction realizes the field without ambient manifold
  completeness; the separate `IsMetricNorm` and base-curve smoothness
  assumptions were removed as redundant.  This is dedicated machinery only:
  P1a remains seven of eight endpoints (**87.5%**), aggregate P1 remains ten of
  fourteen (**71.4%**), and the compact-closure Bishop theorem itself remains
  unstated (**0%**).  Three downstream calls are being migrated statically;
  their focused checks wait for the single required upstream artifact refresh
  in an exclusive non-parallel window.
- 2026-09-01 P1a second-variation artifact handoff: the explicitly named
  `SecondVariationMinimiser` refresh completed successfully after all parallel
  P1 lanes were paused.  The target module remained warning-free; only existing
  linter messages from replayed dependencies appeared.  Parallel work now
  resumes with focused checks only on the three migrated consumers.  Endpoint
  percentages remain unchanged.
- 2026-09-01 P1a generic-interval artifact handoff: `radial_jacobi_on` now has
  an implicit arbitrary upper endpoint, with its domain hypothesis on
  `Icc 0 L` and all three regularity/Jacobi conclusions on `Ioo 0 L`; it is
  warning-free focused GREEN and explicitly refreshed.  The independent
  `RicciEndpoint` weak-signature refresh also passed for its one real consumer.
  Both refreshes ran only after the parallel lanes were paused.  Endpoint
  accounting remains unchanged pending the generic-horizon
  `raw_exp_inj_of_min` focused check and final Bishop assembly.
- 2026-09-01 P1a arbitrary-horizon nonsingularity: `raw_exp_inj_of_min` is now
  warning-free focused GREEN with an explicit positive horizon `L`, raw-domain
  coverage on `Icc 0 L`, the minimizing endpoint at `L • u`, and
  nonsingularity at every `c ∈ Ioo 0 L`.  The theorem has no ambient
  completeness or metric-norm witness and reuses the generic
  `radial_jacobi_on` plus the completeness-free second-variation producer.
  Its claim was normally released after targeted diff review.  This closes the
  tracked raw producer gate, not the theorem endpoint: P1a remains seven of
  eight endpoints (**87.5%**), the missing compact-closure Bishop theorem is
  still unstated (**0%**), aggregate P1 remains ten of fourteen (**71.4%**),
  and whole-Poincare endpoint completion remains **0%**.  The next smallest
  producer is the q=0 raw radial density comparison, followed by the absolute
  raw-polar ball-volume assembly; the two-radius equality/ratio bridge remains
  a separate later gate.
- 2026-09-01 P1a raw-density consumer re-audit: the compact-closure absolute
  endpoint belongs in `Volume/SegmentBallEuclideanUpper.lean` and needs no
  ambient completeness, global Ricci predicate, or extra integrability
  hypothesis.  The checked `rawBall_vol_le_int`, `riemVol_rawExp_le`, and
  `normalHaar_eq` chain will assemble it once a pointwise raw full-density
  bound is available.  The source-written `raw_ratio_anti` and
  `raw_density_le` target only the transverse density; `raw_exp_density`
  identifies the full radial Gram but does not factor it.  Therefore the next
  genuine producer after the scalar focused checks is a raw analogue of the
  full-to-transverse factorization behind
  `expJacDensity_eq_ncd0_mul_transverse`, followed by the pointwise endpoint
  `rawDens_le_zero`.  This is machinery only: P1a remains seven of eight
  endpoints (**87.5%**), aggregate P1 remains ten of fourteen (**71.4%**), and
  the compact-closure Bishop theorem itself remains unstated (**0%**).  The
  relative two-radius theorem is still a separate equality/common-polar-domain
  frontier and cannot be inferred from two one-sided absolute upper bounds.
- 2026-09-01 P1a compact-buffer endpoint closure: `BishopRawDensity.lean` is
  warning-free focused GREEN and exactly refreshed through `rawSpeed_sq`,
  `raw_ratio_anti`, `raw_density_le`, `rawDens_eq_trans`, and
  `rawDens_le_zero`.  The final `ball_vol_le_eucl` consumer in
  `SegmentBallEuclideanUpper.lean` is warning-free focused GREEN and its exact
  named refresh is GREEN (3998/3998).  It assumes compactness only for a
  strictly larger buffer ball and Ricci nonnegativity only on the compared
  ball; it does not add completeness, global Ricci, injectivity, no-conjugacy,
  or positive-radius hypotheses.  The 196-declaration unified P1 audit passed
  without warnings and every print lists only `propext`, `Classical.choice`,
  and `Quot.sound`.  P1a is therefore eight of eight endpoints (**100%**),
  aggregate P1 is eleven of fourteen (**78.6%**), and the whole-Poincare
  theorem endpoint remains unstated (**0%**).  The incomplete-ambient
  two-radius relative theorem remains a separate textbook extension and is not
  counted as a ninth project-used P1a endpoint.
- 2026-09-01 P1b post-migration re-audit: the 2026-08-28 fixed-chart/domain
  blocker is historical, not live.  Global `MaximalGeodesicWitness`, open raw
  `expDomain`, `mem_expDom_of_cpt`, and raw exponential smoothness now provide
  the domain layer.  Exact Morgan--Tian consumers still require incomplete-
  ambient E1 and E2, both formally unstated (**0%**).  The selected shortest
  route is a raw normal-map CGT specialization.  Its first bounded producer is
  `raw_gauss_pullback`; after raw lift fencing, the first major mathematical
  gate is local curvature upper control to raw exponential derivative
  injectivity/local diffeomorphism.  E1 then needs raw collision/fiber-count
  and full pull-volume assembly; E2 additionally needs compact-buffer local
  two-radius volume propagation.  This reclassification changes no endpoint
  count: P1 remains eleven of fourteen (**78.6%**), and the whole-Poincare
  theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b coordinates plumbing: the canonical
  `Coordinates.written_fderiv_inv` adapter is warning-free focused GREEN.  It
  converts invertibility of the manifold derivative to invertibility of the
  written ext-chart derivative under only the boundaryless source hypothesis,
  and feeds the existing set-level `infty` local-diffeomorphism theorem.  This
  closes plumbing only: curvature-to-raw-derivative injectivity and E1/E2 remain
  formally unstated (**0%**), so no endpoint percentage changes.
- 2026-09-01 P1b raw local-diffeomorphism plumbing: the explicitly named
  `Coordinates.LocalDiffeoIFT` refresh is GREEN (2357/2357), and the new
  `framedExp_mdiffAt` / `framedExp_locdiff` module is warning-free focused
  GREEN.  It uses only raw-domain membership, finite-dimensional derivative
  injectivity, and the canonical inverse-function theorem; it adds no
  curvature, radius, or completeness assumption.  This is dedicated machinery
  only.  E1 and E2 remain unstated (**0%**) and aggregate endpoint accounting is
  unchanged.
- 2026-09-01 P1b raw lift fence: map-generic `lift_norm_le` now assumes its
  radial Cauchy inequality only along the input path.  The checked
  `mfderiv_framedMap`, `rawFrame_radial_le`, and `rawLift_norm_le` chain
  specializes it to the raw framed exponential under only path-local radial
  domain support.  `LiftLength`, `RawFramedLocalDiffeo`, and
  `GaussLemmaPullback` received only explicitly named downstream-required
  refreshes; the final raw-lift file is warning-free focused GREEN.  This is
  dedicated machinery only: E1/E2 remain unstated (**0%**) and aggregate
  endpoint accounting remains eleven of fourteen (**78.6%**).
- 2026-09-01 P1b pole Jacobi bridge: the private raw clamped variation now
  proves its Jacobi conclusion on the closed interval by reusing
  `raw_radial_geo_at` at the clamp center.  The public `radial_jacobi_on`
  interface remains on `Ioo 0 L`, while `radial_jacobi_at0` exposes exactly
  the missing pole equation without completeness or a public positive-finrank
  premise.  Focused verification is warning-free GREEN; no artifact refresh
  was run because no source-written downstream consumer yet reads the new
  export.  Independent audits rule out duplicating the already-checked
  Ioo-to-Ico Gronwall bridge.  Their next exact API gap is a smooth-clamp and
  germ-transfer adapter giving an orthonormal parallel frame on a raw radial
  `Icc`.  E1/E2 remain unstated (**0%**), aggregate P1 remains eleven of
  fourteen (**78.6%**), and the whole-Poincare theorem endpoint remains
  unstated (**0%**).
- 2026-09-01 P1b raw interval frame: `exists_raw_ray_ext` globalizes a raw
  radial segment by compact thickening and a smooth time clamp; it is
  warning-free focused GREEN and exactly refreshed only because the new frame
  consumer reads its export.  `Volume/RawRadialFrame.lean` then transfers the
  existing global orthonormal parallel frame back by curve-germ congruence.
  Its public `exists_raw_frame` also handles zero model dimension without a
  `NeZero` assumption and is warning-free focused GREEN.  No raw-frame artifact
  refresh has run because the curvature consumer is not yet source-written.
  This closes the frame input to `covGronwall_ne_zero_at`; the next exact brick
  is the raw curvature/ODE package and resulting nonvanishing of radial Jacobi
  fields.  E1/E2 remain unstated (**0%**), aggregate P1 remains eleven of
  fourteen (**78.6%**), and the whole-Poincare theorem endpoint remains
  unstated (**0%**).
- 2026-09-01 P1b raw curvature/local-diffeomorphism gate:
  `RawRadialGronwall.lean` is warning-free focused GREEN through
  `rawJacobi_ne_of_rm` and `rawExp_mfderiv_inj`.  It reuses the native raw
  interval frame, pole Jacobi equation, `curv_sq_of_rm04_velocity_Ioo`, and
  `covGronwall_ne_zero_at`; no duplicate ODE or curvature wrapper was added.
  The exact upstream artifact refresh is GREEN (3874/3874).  The normal-frame
  specialization lives separately in `RawFramedGronwall.lean` to avoid a
  generic-norm/inner-product instance diamond; `framed_mfderiv_inj` and
  `framed_locdiff_rm` are warning-free focused GREEN.  This closes the major
  curvature-to-raw-local-diffeomorphism machinery gate, raising dedicated P1b
  machinery to about **96%**, but it does not state E1 or E2: both remain
  **0%**, aggregate P1 remains eleven of fourteen endpoints (**78.6%**), and
  the whole-Poincare theorem endpoint remains unstated (**0%**).  The next
  smallest frontier is the raw CGT collision/fiber-count specialization and
  its all-launch pull-volume input.
- 2026-09-01 P1b raw path-lift bridge: `CGTRawExpLift.lean` proves
  `CGT.exists_raw_lift` directly in the canonical `IsLiftOn` interface.  The
  compact fence is `rawLift_norm_le`, radial `expDomain` coverage is used only
  inside the local-diffeomorphism ball, and no `CompleteSpace`, sigma-compact,
  or duplicate `RawFrameLift` layer is introduced.  The exact
  `RawLiftLength` refresh is GREEN (3805/3805), and the new theorem is
  warning-free focused GREEN.  This closes one mechanical prerequisite but
  not the collision theorem: dedicated P1b machinery remains about **96%**,
  E1/E2 remain unstated (**0%**), aggregate P1 remains eleven of fourteen
  endpoints (**78.6%**), and the whole-Poincare theorem endpoint remains
  unstated (**0%**).  The next smallest producer is the all-launch
  injectivity-to-density bound `rawDens_le_of_inj`, in parallel with the raw
  multiplicity-area and propeller dependency kernels.
- 2026-09-01 P1b raw density/measure and radial-path split:
  `BishopRawDensity.lean` now proves `rawDens_le_of_inj` under only closed
  radial-domain coverage, positive-time raw differential injectivity, and
  radial Ricci nonnegativity; its focused check is warning-free GREEN.  The
  canonical lower measure layer now proves the completeness-free exact image
  formula `riemVol_image_eq`, also warning-free focused GREEN.  The true
  consumers `RawPullVolume.lean` and `RawMultiplicityArea.lean` are kept in
  separate comparison modules; the former is source-complete and its focused
  preflight stopped only because `rawDens_le_of_inj` has not yet been refreshed,
  while the latter is source work in progress and likewise waits for the exact
  image-equality artifact.  Independently, `CGTRawLiftOps.lean` is warning-free
  focused GREEN through the canonical raw radial `Path`, its flatness, and the
  exact length formulas `rawRadial_len` and `rawFlatPath_len`; the next source
  module forms the two-ray collision loop.  Parallel work remains focused-only,
  so no new targeted refresh/build has run.  These are dedicated producers,
  not E1/E2: both endpoints remain unstated (**0%**), aggregate P1 remains
  eleven of fourteen (**78.6%**), dedicated P1b machinery remains about
  **96%**, and the whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b raw measure/collision integration: the exact
  `BishopRawDensity` refresh is GREEN (3952/3952), after which
  `rawPullVol_le_eucl` became warning-free focused GREEN and shed its unused
  `SigmaCompactSpace M` premise.  The new canonical `riemVol_image_eq` artifact
  is exactly refreshed GREEN (2869/2869); its true consumer
  `raw_mul_le_area` is warning-free focused GREEN after only local import,
  alias-rewrite, and unused-instance repairs, and does not require completeness,
  connectedness, intrinsic APIs, or positive model dimension.  Independently,
  `CGTRawLiftOps` is exactly refreshed GREEN (3962/3962), and the downstream
  `rawCollisionPath`/`rawCollision_flat`/`rawCollision_len` module is
  warning-free focused GREEN.  `CGTRawExpLift` is exactly refreshed GREEN
  (3811/3811) for the next true consumer.  The next producer is now the
  completeness-free fiber embedding/cardinality comparison
  `rawFiber_encard_le`; a separate read-only audit is localizing the later raw
  pullback-metric/Jensen bridge.  Because neither P1b endpoint has yet been
  formally stated and proved, E1/E2 remain **0%**, aggregate P1 remains eleven
  of fourteen (**78.6%**), dedicated P1b machinery remains conservatively about
  **96%**, and the whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b raw geometric-boundary audit: the completeness-free fiber
  propagation source is now being implemented as `rawFiber_encard_le` in a
  dedicated focused-check-only module.  Independently, a source audit of
  `CGTPullbackMetric`, `CGTWhiteheadJensen`, and `CGTPropeller` shows that the
  first missing geometric producer is not the full Jensen package but the thin
  raw pullback adapter `rawPull_pathLen`.  It can reuse `hloc_restrict_open`,
  `localPullMetric`, and `localPull_pathLen` under a caller-provided raw local
  diffeomorphism, with no completeness, connectedness, curvature, core, or
  positive-dimension premise.  The next implementation lane therefore owns
  only `CGTRawPullback.lean`; strict convexity and center-of-mass machinery stay
  behind the later, separately audited frontier.  While these lanes run in
  parallel, verification remains focused-only and no targeted refresh/build is
  allowed.  E1/E2 are still unstated (**0%**), aggregate P1 is still eleven of
  fourteen (**78.6%**), dedicated P1b machinery remains conservatively about
  **96%**, and the whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b raw strict-Jensen dependency audit: actual pullback
  half-squared-distance strict Jensen cannot be started from branch energy
  alone.  All three audited routes converge on the same prerequisite order:
  `rawExtJoin_fenced`, raw core closure of that join, raw pullback/extension
  distance equality on the core, and only then the local branch-energy germ
  equality with the actual half-squared distance.  Direct minimization in the
  incomplete raw ball has no complete-space/minJoin input, while selected
  branch energy is not a replacement for the true metric function consumed by
  `CenterOfMass`.  The independent genuine producer
  `rawBranch_hess_pos`--strict Hessian positivity for branch energy under a
  caller-supplied extension-launch fence--has therefore been dispatched in
  parallel with the join/fence lane.  This records a dependency, not endpoint
  credit: strict Jensen remains unstated (**0%**), E1/E2 remain unstated
  (**0%**), aggregate P1 remains eleven of fourteen (**78.6%**), and the
  whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-02 P1b E2 raw interior measurability:
  `rawSegInt_ball_meas` in `Volume/RawBallPolarEq.lean` is warning-free
  focused GREEN (24.9s).  For a strict radius inside a compact closed buffer,
  it expresses `rawSegInt ∩ gBall` as a countable union of continuous rational-
  dilation preimages of a compact `rawSeg ∩ closedGBall` set.  This supplies
  actual `MeasurableSet`, rather than substituting the weaker endpoint
  `NullMeasurableSet`, and adds no ambient completeness or wrapper predicate.
  The next exact-COV brick is the direct `riemVol_image_eq` specialization on
  this set.  `rawBall_vol_rel` itself remains unstated (**0%**); E1/E2 remain
  unstated (**0%**), aggregate P1 remains eleven of fourteen (**78.6%**),
  dedicated P1b machinery remains conservatively about **97%**, and the
  whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b E2 local-propagation audit: no current theorem is a short
  incomplete-ambient adapter.  `injDecay_of_bg` and `segBall_vol_rel` use
  complete/global bounded geometry; `intrInj_ge_vol` likewise carries a
  complete ambient input.  The three audited alternatives isolate one
  smallest missing native producer: a compact-buffer, two-radius Bishop
  relative-volume lower bound (`rawBall_vol_rel`) under a local Ricci lower
  bound.  The checked `ball_vol_le_eucl` and `rawBall_vol_le_int` are one-sided
  upper bounds and cannot be reversed; a model-space complete extension would
  require a much larger ambient distance/curvature/volume transfer package;
  and the raw polar route still needs the common-domain/cut-locus volume
  equality that turns density-ratio monotonicity into a ball-volume ratio.
  The implementation lane is now attempting `rawBall_vol_rel` at the volume
  comparison layer rather than adding an E2 wrapper assumption.  Until that
  producer closes, E2 remains unstated (**0%**); aggregate P1 remains eleven
  of fourteen (**78.6%**), and the whole-Poincare theorem endpoint remains
  unstated (**0%**).
- 2026-09-01 P1b raw fiber propagation and norm-instance repair:
  `rawFiber` and `rawFiber_encard_le` are warning-free focused GREEN.  The
  proof uses only a raw radial pole loop, a short flat path, canonical
  `IsLiftOn` existence/uniqueness, endpoint norm fencing, and an injective
  fiber embedding; it has no ambient completeness, connectedness,
  sigma-compactness, or positive-dimension premise.  Its first focused pass
  exposed that `lift_norm_le`, `rawLift_norm_le`, and `exists_raw_lift` had
  baked the Tensor0S tangent norm into their declarations.  The existing three
  theorems now explicitly bind the two tangent norm structure families they
  already use; no proof body, geometry hypothesis, or duplicate theorem was
  added.  Each layer is warning-free focused GREEN, and the exact dependency
  refreshes are GREEN for `LiftLength` (3778/3778), `RawLiftLength`
  (3805/3805), and `CGTRawExpLift` (3811/3811).  The next two independent
  producers are the raw pullback curvature/quadratic-form API and the public
  multiplicity-to-`rawPullVol` composition bridge.  Parallel verification is
  focused-only.  E1/E2 remain unstated (**0%**), aggregate P1 remains eleven
  of fourteen (**78.6%**), dedicated P1b machinery remains conservatively
  about **96%**, and the whole-Poincare theorem endpoint remains unstated
  (**0%**).
- 2026-09-01 P1b raw pullback and multiplicity composition:
  `CGTRawPullback.lean` is warning-free focused GREEN through the exact
  pullback path-length, framed differential, pullback-inner-product,
  curvature, and quadratic-form adapters; its true downstream artifact was
  exactly refreshed GREEN (3828/3828).  `RawPullVolume.lean` was likewise
  exactly refreshed for its true consumer (3964/3964).  The public
  `raw_mul_le_pull` theorem then became warning-free focused GREEN: it composes
  `raw_mul_le_area` with the existing private normal-frame density conversion,
  adds no completeness, connectedness, intrinsic-exponential, or positive
  model-dimension assumption, and exposes no temporary conversion API.  The
  next independent producer is the generic raw-loop transport and exact
  pullback-length preservation; the read-only route audit separately selected
  a narrow raw complete-extension producer as the first input to the later
  core-staying minimizing join.  Parallel verification remains focused-only,
  so no further targeted refresh/build is permitted until those lanes reach a
  coordinated boundary.  E1/E2 remain unstated (**0%**), aggregate P1 remains
  eleven of fourteen (**78.6%**), dedicated P1b machinery remains
  conservatively about **96%**, and the whole-Poincare theorem endpoint remains
  unstated (**0%**).
- 2026-09-01 P1b generic raw transport: `CGTRawTransport.lean` is warning-free
  focused GREEN through the raw core, loop-radial path and exact length bound,
  canonical lift existence, endpoint transport, joint continuity, C1 transport
  of core curves, and exact pullback path-length preservation.  It imports the
  narrow canonical Mathlib lifting module directly for
  `IsLocalHomeomorph.continuous_lift` rather than routing through the heavier
  intrinsic CGT hierarchy.  The API is generic in the input flat loop and has
  no completeness, connectedness, ambient sigma-compactness, positive model
  dimension, curvature, minimizer, collision, or Jensen premise.  No artifact
  refresh has run: while the raw complete-extension and read-only endpoint
  audit lanes remain active, verification is focused-only.  Exact length alone
  does not prove nonexpansiveness; the next geometric input is a raw
  distance-realizing core join built through the complete-extension route.
  E1/E2 remain unstated (**0%**), aggregate P1 remains eleven of fourteen
  (**78.6%**), dedicated P1b machinery remains conservatively about **96%**,
  and the whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b raw complete extension: `CGTRawExtension.lean` is
  warning-free focused GREEN through the complete extended metric,
  closed-ball pointwise inner-product agreement, open-ball restriction
  equality, and `rawExt_complete`.  It directly reuses the native compact
  bump-extension and flat-model completeness APIs.  The final public interface
  needs no ambient completeness, connectedness, sigma-compactness,
  boundarylessness, tangent-bundle T2, curvature, raw-domain coverage, or
  positive model dimension.  No artifact refresh has run while the remaining
  static audits are active.  This removes the first prerequisite for the raw
  distance-realizing core join, but neither the join nor nonexpansiveness is
  yet proved.  E1/E2 remain unstated (**0%**), aggregate P1 remains eleven of
  fourteen (**78.6%**), dedicated P1b machinery remains conservatively about
  **96%**, and the whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b generic raw nonexpansion: the true downstream import justified
  an exact `CGTRawTransport` refresh, which is GREEN (4000/4000).
  `CGTRawNonexp.lean` then became warning-free focused GREEN through
  `rawTransport_nonexp`.  The theorem consumes only one caller-supplied C1
  core path whose pullback length realizes the source distance; it converts
  exact transported length to ordinary-distance nonexpansion through the native
  Hopf--Rinow metric realization.  It does not depend on a bundled min-join,
  join existence, curvature, completeness, positive model dimension, strict
  Jensen, or center-of-mass machinery.  The endpoint audit confirms that
  nonexpansion is routine once a core-staying distance-realizing join exists,
  but the later unique-center/fiber-count chain still genuinely needs strict
  Jensen for the real pullback distance.  In parallel, the independent
  `rawTransport_ne` producer and the extension-distance bridge are now the next
  focused/source lanes.  E1/E2 remain unstated (**0%**), aggregate P1 remains
  eleven of fourteen (**78.6%**), dedicated P1b machinery remains
  conservatively about **96%**, and the whole-Poincare theorem endpoint remains
  unstated (**0%**).
- 2026-09-01 P1b post-nonexp endpoint audit: exact transport length and
  nonexpansion do not remove the strict-Jensen gate.  E1's remaining dependency
  order is raw transport nonfixedness; raw zero-distance and core compactness;
  a core-staying distance-realizing join; strict Jensen for the actual
  pullback distance; unique center of mass; raw orbit/fiber count; quantitative
  flat-loop and collision bounds; then `framedInj_ge_cgt` and the final
  `framedInj_ge_vol`.  The center theorem genuinely consumes strict Jensen;
  selected branch energy cannot be substituted for the true half-squared
  distance.  `rawTransport_ne` is independent of the join/Jensen work and has
  therefore been dispatched as the next checked producer.  E2 is a separate
  frontier: propagating base noncollapse/injectivity across a bounded ball in
  an incomplete ambient still needs a local two-radius Bishop lower-volume
  theorem; the checked Euclidean upper bound cannot be reversed to supply it.
  This audit changes no endpoint count: E1/E2 remain unstated (**0%**),
  aggregate P1 remains eleven of fourteen (**78.6%**), and the whole-Poincare
  theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b raw transport nonfixedness: `CGTRawPropeller.lean` is
  warning-free focused GREEN through the single public theorem
  `rawTransport_ne`.  A caller-supplied nonclosed lift of the short based loop,
  together with raw lift uniqueness and the canonical radial return path,
  proves that raw loop transport fixes no point of the core.  The theorem adds
  no curvature, min-join, Jensen, center-of-mass, ambient completeness or
  connectedness, ambient sigma-compactness, or positive-dimension premise.
  It is the first post-nonexp producer in the E1 chain, not an endpoint.  No
  artifact refresh has run because no source-written downstream consumer yet
  imports it.  E1/E2 remain unstated (**0%**), aggregate P1 remains eleven of
  fourteen (**78.6%**), and the whole-Poincare theorem endpoint remains
  unstated (**0%**).
- 2026-09-01 P1b raw core basics: `CGTRawCore.lean` is warning-free focused
  GREEN through `rawCore_compact`, `rawZero`, `rawZero_mem`, and the exact
  origin-distance identity `rawPull_dist_zero`.  The distance proof combines
  the canonical raw radial upper path with the map-generic lift-length lower
  bound.  Its statement honestly keeps radial `expDomain` coverage for every
  raw-ball endpoint; local diffeomorphism alone is not treated as a domain
  theorem.  No ambient completeness or connectedness, ambient
  sigma-compactness, positive-dimension, curvature, minimizing-join, Jensen,
  or center-of-mass premise was added.  This closes the zero-distance/core-
  compactness prerequisite only.  Its first true downstream consumer now
  justifies an exact named refresh, GREEN (4001/4001).  E1/E2 remain unstated
  (**0%**), aggregate P1
  remains eleven of fourteen (**78.6%**), dedicated P1b machinery remains
  conservatively about **96%**, and the whole-Poincare theorem endpoint
  remains unstated (**0%**).
- 2026-09-01 P1b raw extension-distance bridge: the true downstream import
  justified an exact `CGTRawExtension` refresh, which is GREEN (3840/3840).
  `CGTRawExtDistance.lean` is then warning-free focused GREEN through
  `rawPull_geo_of_ext`, `rawExt_geo_of_pull`, `rawExt_pathLen`,
  `rawExt_radial_len`, and `rawExt_edist_le`.  The first three declarations
  are radial-domain free; the final two retain only the actual endpoint radial
  segments used by their proofs.  The live APIs do not derive those segment
  premises from `hloc`, so no false no-domain wrapper was introduced.  The
  module adds no ambient completeness/connectedness, positive dimension,
  curvature, join/fence, Jensen, or center-of-mass assumption.  The next
  join consumer justifies this module's exact named refresh, GREEN
  (3982/3982).  The next producer is the complete-extension minimizing join
  and its core fence;
  strict Jensen for the resulting true pullback distance remains a distinct
  later gate.  E1/E2 remain unstated (**0%**), aggregate P1 remains eleven of
  fourteen (**78.6%**), dedicated P1b machinery remains conservatively about
  **96%**, and the whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b complete-extension join and raw fence:
  `CGTRawExtJoin.lean` is warning-free focused GREEN through `rawExtJoin`, its
  endpoint identities, smoothness and geodesicity, and `rawExtJoin_fenced`.
  The construction treats the zero-dimensional model internally rather than
  adding a public positive-finrank assumption.  Its fence uses the honest
  whole-raw-ball radial `expDomain` hypothesis needed at the first-hit point,
  together with `rawPull_dist_zero`, `rawExt_edist_le`, and the pullback/
  extension path-length identities; it adds no ambient completeness,
  connectedness, or sigma-compactness assumption.  This closes the join/fence
  prerequisite, not either P1b theorem endpoint.  The first source-written
  downstream core-closure consumer justified an exact named refresh, GREEN
  (4012/4012); no broader build was run.  E1/E2 remain
  unstated (**0%**), aggregate P1 remains eleven of fourteen (**78.6%**),
  dedicated P1b machinery is now conservatively about **97%**, and the
  whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b branch-energy Hessian producer:
  `CGTRawBranchHess.lean` is warning-free focused GREEN through the public
  `rawBranch_hess_pos`.  For a fenced raw complete-extension launch, an
  arbitrary valid `ExpInvBranch`, and every nonzero endpoint tangent vector,
  it proves strict positivity of the branch-energy Hessian.  The proof uses
  the native branch Hessian/index-form identity, the radial/transverse Jacobi
  decomposition, the checked curvature-smallness estimate, and the exact
  radial diagonal/cross-term identities; it does not replace true distance by
  selected branch energy.  This closes an independent strict-Jensen input,
  while the actual-distance germ and core distance-equality bridge remain
  downstream.  No named refresh is justified yet because no checked consumer
  imports the new export, and parallel work stays focused-check-only.  E1/E2
  remain unstated (**0%**), aggregate P1 remains eleven of fourteen
  (**78.6%**), dedicated P1b machinery remains conservatively about **97%**,
  and the whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b pullback-instance boundary cleanup: the canonical curvature
  theorem `rm04_localPull` no longer exports an ambient target
  `SigmaCompactSpace`; it transports sigma compactness only onto the open
  pullback target where the theorem actually needs it.  The true downstream
  refresh of `PullbackNaturalityLocalCross` is GREEN (3667/3667).
  `CGTRawPullback.lean` now derives the base `T2Space` from the already-present
  tangent-bundle instance and is warning-free focused GREEN (18.3s), with its
  exact refresh GREEN (3856/3856).  `CGTRawBranchHess.lean` consequently drops
  the obsolete ambient sigma premise from the raw quadratic, no-conjugacy, and
  branch-Hessian chain; its final focused check is warning-free GREEN and its
  exact refresh is GREEN (3985/3985).  This is an API-boundary repair, not an
  endpoint: E1/E2 remain unstated (**0%**), aggregate P1 remains eleven of
  fourteen (**78.6%**), and the whole-Poincare theorem endpoint remains
  unstated (**0%**).
- 2026-09-01 P1b raw pinned injectivity: `CGTRawBigon.lean` is warning-free
  focused GREEN through `rawExt_pinned_inj` (61.6s), without ambient
  completeness, base sigma compactness, or a consumer wrapper.  Its exact
  downstream-required refresh is GREEN (4029/4029).  The next E1 producer is
  compact short-bigon exclusion on the raw core, reusing this local pinned
  injectivity rather than duplicating the derivative/IFT proof; actual-distance
  strict Jensen and center-of-mass assembly remain after it.  E1 itself is
  still unstated (**0%**).
- 2026-09-01 P1b raw-ball integration formula: `Volume/RawBallPolarEq.lean`
  is warning-free focused GREEN through `rawSegInt_ball_meas`,
  `rawSegInt_image_eq`, and `rawBall_integral_eq`; the last three checks took
  24.9s, 25.2s, and 25.9s respectively.  The proof removes the cut endpoint
  and metric-sphere boundaries by their native null-measure results and uses
  the checked injective raw-exponential image identity; it assumes neither
  ambient completeness nor a theorem-shaped volume hypothesis.  Its true
  downstream refresh is GREEN (3969/3969).  The actual E2 endpoint
  `rawBall_vol_rel` remains unstated (**0%**) and is now the active volume
  source lane.
- 2026-09-01 P1b post-pinned split: three mutually exclusive lanes are active
  under focused-check-only coordination: E1 `rawCore_short_inj`; E2 the
  canonical two-radius `rawBall_vol_rel` module; and the completed audit's
  implementation handoff to the actual-distance germ `rawCore_dist_germ`.  No named refresh or
  broader build is permitted while these lanes remain active.  Dedicated P1b
  machinery is conservatively about **98%**, but neither E1 nor E2 has a
  formally stated and proved endpoint, so both theorem percentages remain
  **0%**; aggregate P1 remains eleven of fourteen (**78.6%**) and the
  whole-Poincare theorem endpoint remains **0%**.
- 2026-09-02 P1b raw short-launch fence:
  `CGTRawBigon.lean` is warning-free focused GREEN through the public
  `rawExt_short_fenced` (86.7s).  A complete-extension launch whose initial
  point and metric length fit the `a + L < 3R/4` budget stays in the raw/extend
  agreement ball.  The proof uses the first boundary hit, the checked raw pull
  and extension path-length identities, and `rawPull_dist_zero`; it does not
  add ambient completeness, connectedness, sigma compactness, curvature, or a
  wrapper assumption.  The next source brick is the local pinned-root
  injectivity consequence `rawExt_pinned_inj`, before compact short-bigon
  exclusion.  No named refresh is permitted while the E1/E2 tasks are active
  in parallel.  E1/E2 remain unstated (**0%**), aggregate P1 remains eleven of
  fourteen (**78.6%**), dedicated P1b machinery remains conservatively about
  **97%**, and the whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-02 P1b E2 raw interior injectivity:
  `Volume/RawBallPolarEq.lean` is now warning-free focused GREEN through
  `rawSegInt_sub` and the public `rawExp_inj_seg`.  The latter proves global
  `Set.InjOn` of the raw exponential on the strict raw minimizing interior by
  extending both radial geodesics and applying the native broken-minimizer
  velocity-match theorem; it does not use ambient `CompleteSpace M`, a wrapper
  predicate, or an unproved assumption.  The explicit `hEnorm` input is already
  present in the intended local-volume consumer and is used only by the
  speed/distance bridge.  The native exact change-of-variables route is now
  blocked first by actual `MeasurableSet` of `rawSegInt ∩ gBall` (endpoint
  null-measurability alone is insufficient), after which the genuinely
  geometric remaining producer is the arbitrary-`q` raw radial density-ratio
  comparison.  `rawBall_vol_rel` itself remains unstated (**0%**); E1/E2 remain
  unstated (**0%**), aggregate P1 remains eleven of fourteen (**78.6%**),
  dedicated P1b machinery remains conservatively about **97%**, and the
  whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b raw core join and distance equality:
  after the exact `CGTRawExtJoin` refresh GREEN (4012/4012),
  `CGTRawCoreJoin.lean` is warning-free focused GREEN through
  `exists_raw_fenced`, the budgeted `rawPull_edist_eq`, and the all-core
  `rawCore_edist_eq`.  The nonzero-dimensional branch uses only private local
  instances; no public `NeZero`, ambient completeness/connectedness/
  sigma-compactness, curvature, Jensen, or center-of-mass hypothesis was
  added.  Whole-ball radial `expDomain` coverage is carried honestly through
  the fence and both distance inequalities.  This closes the core-staying
  distance-realizing join and raw/extension distance-equality prerequisites;
  it does not yet identify a local inverse-branch energy with actual squared
  distance and therefore does not prove strict Jensen.  No CoreJoin refresh
  is justified until that source-written consumer imports it.  E1/E2 remain
  unstated (**0%**), aggregate P1 remains eleven of fourteen (**78.6%**),
  dedicated P1b machinery remains conservatively about **97%**, and the
  whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b E2 raw-polar boundary/domain slice:
  `Volume/RawBallPolarEq.lean` is warning-free focused GREEN through
  `rawSeg`, `rawSegInt`, raywise endpoint subsingleton, compact-buffer
  `rawSegEnd_null`/`rawSegEnd_nullMeas`, `rawSeg_mem_dom`, and
  `rawSegInt_geo`.  The endpoint
  nullness is proved by compact radial contractions plus the native polar
  integration formula; the domain lemma rules out Mathlib's outside-domain
  exponential fallback for an honestly minimizing raw vector; the interior
  lemma then obtains a radially extended geodesic from the native
  `radialGeo_of_end`, retaining exactly its boundaryless and tangent-bundle
  T2 requirements.  The lower geodesic layer now also has warning-free
  focused-GREEN `smul_mem_expDomain`, proving the canonical star-domain
  scaling rule by maximal-geodesic reparametrization without completeness.
  No ambient
  completeness or global curvature premise was added.  These results remove
  the cut-boundary measure and domain gates, but they do not give global
  injectivity of raw exponential on `rawSegInt`; local diffeomorphism alone is
  insufficient for the image-equality change-of-variables theorem.  Hence
  `rawBall_vol_rel` remains unstated (**0%**).  No named refresh is justified
  yet because no source-written downstream module imports this export.
  E1/E2 remain unstated (**0%**), aggregate P1 remains eleven of fourteen
  (**78.6%**), dedicated P1b machinery remains conservatively about **97%**,
  and the whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b raw complete-extension no-conjugacy bridge:
  `CGTRawBranchHess.lean` is now warning-free focused GREEN through the public
  `rawExt_no_conj`.  For every fenced raw complete-extension launch below the
  curvature conjugacy scale it proves the native `IsConjVec` negation by a
  first-interior-maximum Jacobi/index-form argument.  The conclusion retains
  the positive-finrank instance already required by `IsConjVec` and
  `expMapIntrinsic`; this is not a new assumption for any actual CGT consumer,
  while the launch construction itself remains dimension-neutral.  The exact
  `CGTScale`, `CGTRawBranchHess`, and `CGTRawCoreJoin` refreshes are GREEN, and
  the lower canonical witness bridge `rawExtJoin_eq_min` is warning-free
  focused plus exactly refreshed GREEN (4012/4012).  Its true downstream
  `CGTRawProducer.rawCore_min_regular` is now warning-free focused GREEN
  (24.2s): the complete-extension minimizing vector is fenced, length-bounded,
  and nonconjugate.  This remains supporting machinery rather than either P1b
  endpoint because actual raw half-squared-distance strict Jensen is still
  unstated.  E1/E2
  remain unstated (**0%**), aggregate P1 remains eleven of fourteen
  (**78.6%**), dedicated P1b machinery remains conservatively about **97%**,
  and the whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b post-pinned quantitative bridges: the E1 short-bigon lane is
  warning-free focused GREEN through the raw-origin identity launch and public
  `rawOrigin_strict` (63.8s), and through the prefix half of the compact
  complete-extension scale estimate `rawExt_prefix` (67.6s).  The proof no
  longer needs a monolithic high-heartbeat Hessian elaboration: it gives the
  checked branch-Hessian theorem an explicit local target and derives strict
  positivity directly.  The E2 lane is warning-free focused GREEN through the
  arbitrary-curvature radial comparison `raw_ratio_anti_q`, the raw minimizing
  segment bridge `raw_min_seg`, the exact raywise specialization
  `raw_ratio_ray`, and the generic density continuity bridge `rawDn_cont`
  (19.4s for the final three helper layers).  The reusable
  `mapJac_contOn` was exposed at its existing measure-theory home under the
  same weakest signature, is warning-free focused GREEN (14.6s), and its true
  downstream refresh is GREEN (2868/2868).  Current next producers are the
  suffix/combined compact scale estimate leading to `rawCore_short_inj`, and
  the normal-frame polar equality leading to `rawBall_vol_rel`.  These are
  verified producer advances, not theorem endpoints: E1 and E2 remain
  unstated (**0%**), aggregate P1 remains eleven of fourteen (**78.6%**),
  dedicated P1b machinery is conservatively about **98%**, and the
  whole-Poincare theorem endpoint remains unstated (**0%**).
- 2026-09-01 P1b edge-core and raw polar assembly: the complete-extension
  prefix, suffix, and combined scale bounds are warning-free focused GREEN
  (74.4s for the final combined pass), and the public `rawExt_edge_core` is
  warning-free focused GREEN (76.0s).  This reusable theorem proves that every
  point of the selected short complete-extension geodesic remains in the raw
  norm core, using the already-checked strict origin convexity; it is the real
  common dependency of compact short-bigon exclusion and actual-distance
  Jensen.  In the E2 lane, `rawBall_normal` (19.5s) and `rawBall_polar` (20.3s)
  are warning-free focused GREEN, giving the exact normal-frame and radial
  integral formulas on a compact-buffer raw ball.  The source-written
  `rawCore_jensen` now consumes `rawExt_edge_core`, `rawCore_dist_germ`, and
  `rawBranch_hess_pos`, but remains unverified until the pending
  `rawCore_short_inj` export closes its honest dependency.  E2 continues with
  the raywise cross inequality and public `rawBall_vol_rel`.  Thus E1 and E2
  theorem endpoints remain **0%**, aggregate P1 remains eleven of fourteen
  (**78.6%**), dedicated P1b machinery is about **99%**, and the whole-Poincare
  theorem endpoint remains unstated (**0%**).
