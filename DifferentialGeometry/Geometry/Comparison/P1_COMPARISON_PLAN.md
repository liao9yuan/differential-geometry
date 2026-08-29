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

### Running status (2026-08-27, exact consumer audit frozen)

- Project-used theorem endpoints: **87.5%** (seven of eight separately counted
  endpoints are checked: global model-ratio comparison, its zero-Ricci power
  form, the absolute Euclidean upper bound, the packing consequence, and the
  small-radius Euclidean epsilon normalization and positive-radius continuity
  used by MT 9.66, plus the strict positive-sectional-curvature Euclidean
  volume inequality used by MT 9.56).
- Dedicated native machinery: **about 98%**.  The polar/Jacobian/normal-ball
  engine, complete/global segment-ball engine, and compact-tail endpoint
  continuation are checked.  The exact framed-density/Haar normalization is
  now also warning-free focused-check and named-refresh green under the intended
  smooth-manifold binder, and the Euclidean model-ball normalization adapter is
  warning-free focused-check and named-refresh green.  The curvature-operator
  and sectional-to-Ricci bridges are also checked and refreshed.
  Radius continuity and radial equality propagation are checked and axiom-clean.
  Local minimizing-geodesic coverage remains the sole genuine
  missing-groundwork frontier.  Strict sectional-volume assembly is
  warning-free focused-check and named-refresh green and is included in the
  common direct axiom audit.
- Direct P2/P3 usage has global curvature hypotheses (compact/global in P2;
  complete with global nonnegative Ricci curvature in P3).  The local
  compact-closure form is needed only to reproduce the Chapter 5 incomplete
  compactness chain in its stated generality; it is tracked separately and is
  not silently charged to the already checked global theorem.
- Current action: P1a is closed at a precisely documented blocker after seven
  checked endpoints.  Release its file claims and start the P1b consumer/native
  audit.  Do not reopen the one remaining local compact-closure endpoint unless
  new geodesic-lift or raw-exp polar infrastructure appears.

### Remaining-frontier route audit

- **Local compact-closure form.**  The nearest native target is a radius-local
  minimizing-exponential coverage theorem for `RadialSurjectivity.radialMinSet`,
  with explicit `v in expDomain`.  The compact-tail continuation lemmas remove
  ambient completeness for an already supplied bounded-speed geodesic, but they
  do not construct the minimizing radial ray.  Moreover, the present `SegDom`,
  `SegInt`, `expJacDensity`, and segment-polar integration layer are built from
  `expMapIntrinsic`/`intrinsicGeodesic`, hence still require `CompleteSpace M`.
  Thus the faithful incomplete-manifold theorem needs both local minimizing-ray
  coverage and a raw-`expMap` local segment-polar bridge; adding compactness to
  the existing complete theorem would not solve this consumer.  The smallest
  honest first statement is `minExp_of_cptBall` in `RadialSurjectivity`: compact
  closed ball plus a point in the corresponding open ball produces a minimizing
  `v in expDomain`.  Its proof first needs a base-geodesic-to-initial-data phase
  lift (the absent `IsGeodesicOn.toWithInitial`) and a finite-horizon maximal
  extension; even this lemma alone does not remove the separate local-polar gap.
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

### Running status (2026-08-28, exact consumer set frozen)

- Project-used theorem endpoints: **0%** (zero of two separately counted
  endpoints are yet proved in their exact local-on-balls P3 shape).
- Dedicated native machinery: **about 94%**.  The Whitehead/Jensen/propeller
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
  bounded ball.
- Exact endpoints: E1 has global nonnegative Ricci curvature, compact closure
  of a relevant larger ball, and full-curvature/volume control only there, and
  concludes a point injectivity lower bound; E2 propagates a uniform base
  injectivity/noncollapse bound to a uniform injectivity bound on each fixed
  bounded ball.  P2 has no direct P1b call.  Most P3 inputs are complete
  kappa-solutions, but the `volcomp` use at `temp2kappa:2668` explicitly allows
  an incomplete ambient and prevents completeness from being imposed globally.
- Current action: P1b is closed at the exact incomplete-ambient raw-domain
  blocker below.  Release its file claims and start P1c in phase order.  Do not
  state `frame_mem_expDom` under compact-eball assumptions: that proposed
  producer is false for the live fixed-chart representation of `expDomain`.

### Remaining-frontier route audit

1. **Source-contained fixed-chart route.**  A raw compatibility theorem can be
   proved if the entire geodesic is assumed to remain in
   `(chartAt H x).source`; a capped version of the compact-tail Zorn proof is
   also still needed.  Compact eball closure does not imply this chart-source
   condition, so the resulting theorem is valid but does not cover the audited
   Morgan--Tian consumers.
2. **Global witness/domain redesign.**  Generalize or replace
   `MaximalGeodesicWitness` and `expDomain` so the phase lift solves the global
   `geodesicVectorField`, with chart-local realization proved separately.  This
   is the smallest mathematically faithful route to the MT statement, but it is
   a substantial foundational API migration rather than a P1b-local lemma.
3. **Base-geodesic domain plus downstream migration.**  Define the raw domain
   directly from an open preconnected `IsGeodesicOn` base curve with initial
   data, prove compact-buffer coverage there, and migrate raw exponential,
   Jacobi, Bishop, and CGT consumers.  This avoids the fixed-chart phase field
   but creates a second domain notion and is larger than Route 2.

The decisive obstruction is representational: live `expDomain` uses a
`MaximalGeodesicWitness` for `geodesicVectorFieldChart g x`, which agrees with
the global geodesic vector field only inside the initial chart source and is
zero outside it.  Thus compact-eball-only `frame_mem_expDom`, and an
assumption-free equation-to-phase-lift bridge, are under-hypothesized.  P1b
therefore stops honestly at a foundational design choice after three distinct
routes; no endpoint is counted and no theorem-shaped placeholder was created.

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
- Dedicated native machinery: **about 60--65%** across the whole four-endpoint P1c
  denominator.  Separately: the Laplacian endpoint's dedicated machinery is
  **100%**, the weak Busemann endpoint **100%**, splitting **45--50%**, and soul
  **5%**.  The broader Busemann package needed by `narrows`, including the
  almost-everywhere unit-gradient/asymptotic-ray direction, is about **55%**.
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
  green.  The live frontier is the smooth-coefficient weak-solution to
  smooth-representative bridge; none of these declarations may be replaced by
  a stronger endpoint hypothesis.
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
- P1a theorem endpoints: **87.5%** (seven of eight); P1b: **0%** (zero of two);
  P1c: **50%** (two of four independently counted endpoints: Laplacian and the
  weak Busemann endpoint are complete; splitting and soul remain 0%).  Do not
  collapse these distinct denominators into a misleading single percentage.
- Whole P0--P9 program infrastructure: retain the global authority's current
  **15--25%** estimate; P1 audit or helper work must not inflate it.

## Dependency table

This table is filled from live source evidence during each phase.

| Phase | Morgan--Tian consumer | Exact assumptions/conclusion | Native producer | Classification | Verification/axioms |
|---|---|---|---|---|---|
| P1a | MT 1.34; 5.6; 8.10 | Complete/global metric; Ricci lower bound; compare two radii, then upper/lower volume bounds give packing | `segBall_vol_rel`, `segBall_vol_le`, `segBall_card` | checked producer | focused checks passed; direct axiom print has only standard logical axioms |
| P1a | MT 9.11, 9.59--9.63 | Complete; global `Ric >= 0`; power-law ratio and Euclidean absolute upper bound | `segBall_vol_pow`, `segBall_vol_le_euclidean` | checked producer plus thin zero-curvature adapter | focused/named-refresh checks passed; the common direct axiom audit reports only standard logical axioms |
| P1a | MT 5.9--5.11, 5.15 | Compact closure of the relevant ball and a Ricci bound only there; full-radius local ratio/packing | `localBall_ratio` covers only a small injectivity-radius interval under global completeness; `endpointCont_compact` and `geo_Ioo_extend_cpt` supply the compact-tail continuation brick | missing stronger producer | continuation bricks are focused/named-build green and axiom-clean; `radialMinSet` still lacks local minimizing coverage, and the segment-polar layer still depends on complete-only `expMapIntrinsic` |
| P1a | MT 9.66 | a sufficiently small radius has Euclidean-normalized volume within any prescribed relative error; no audited consumer needs a public abstract limit | `framedDens_zero`, `framedDens_haar`, `exists_ball_ratio`, `exists_euclid_ratio` | checked producer and endpoint | focused checks passed; both normalization theorems and the endpoint are axiom-clean |
| P1a | MT 9.66 | continuity in radius, used to choose a half-model-volume radius | `segBall_vol_cont` via polar integral, sphere-null, and dominated convergence | checked endpoint | focused/named-build verification passed; common axiom audit has only standard logical axioms |
| P1a | MT 9.56 | global strict positive sectional curvature makes every positive-radius intrinsic ball strictly smaller than its Euclidean comparison ball | checked bottom equality chain and radial propagation `transDens_eq_rigid`; checked general strict producers `expJac_lt_of_ricci` and `segBall_vol_lt`; checked smooth-manifold `normalHaar_eq`, `gBall_model_eucl`, `rm04_eq_inner_riem`, and sectional-to-Ricci bridges; exact wrapper `segBall_lt_of_sec` | checked endpoint | all dependencies and `SegmentBallEuclideanStrict` itself are warning-free focused/named-refresh green; common direct audit reports only `propext`, `Classical.choice`, and `Quot.sound` |
| P1b E1 | MT `volinj`; `basicconv`; `2ndmfdconv`; P3 `flowlimit` and the local `basicconv` use | Global `Ric >= 0` is available in every actual P3 use; a relevant larger ball has compact closure and a uniform local `|Rm|` bound; a smaller ball has `Vol >= epsilon*r^n`; conclude `inj(p) >= delta(n,epsilon)*r`. Ambient completeness cannot be required because of `temp2kappa:2668` | checked `intrInj_ge_cgt_on` and ambient-ball quantitative assembly `intrInj_ge_vol`; `flowInj_of_vol` realizes the stronger complete/global-bounded-geometry special case | missing exact local producer | all listed machinery is focused/named green and direct-axiom clean; the live fixed-chart `expDomain` cannot express compact-eball coverage without an extra chart-source hypothesis, so an exact raw producer requires a global witness/domain redesign before the raw Bishop/CGT bridge |
| P1b E2 | MT `mfdconv` proof, then P3 `flowlimit` | On each fixed bounded ball: compact closure and uniform curvature-derivative bounds; uniform positive base inj/noncollapse; conclude a uniform positive inj lower bound throughout that ball, allowing incomplete ambient manifolds | `injDecay_of_bg` gives an explicit exponential pointwise bound under complete global `SeqBoundedGeometry`; its proof actually reads only order-zero curvature, base injectivity, and the intrinsic complete-manifold normal-control package | conditional producer; exact local-on-balls adapter missing | source-complete global special case and all direct axiom prints are clean; exact E2 requires raw buffered normal/CGT control plus local Bishop coverage |
| P1c ray | MT `ends`, `prelim.tex:1093-1124` | complete connected noncompact manifold and chosen point; obtain a unit-speed minimizing ray with exact pairwise distance on nonnegative times | checked `properSpace_riemMetric`, `IsMinimizingRay`, and `exists_minRay` | checked producer | `MinimizingRay` is warning-free focused/named-refresh green and the common audit reports only the three standard logical axioms; no Toponogov dependency |
| P1c Laplacian | MT weak distance comparison, `prelim.tex:887-908,958-1000` | under `Ric >= 0`, distance from a pole satisfies the compactly supported distributional upper inequality needed for escaping-pole limits | `dist_lap_distrib`, assembled from the checked radial/Riccati chain, signed polar change of variables, compact-support Green identity, `radial_pairing_le`, and `dist_pairing_le` | checked endpoint | endpoint is warning-free focused and named-refresh green; the common direct audit reports only `propext`, `Classical.choice`, and `Quot.sound` |
| P1c Busemann | MT `prelim.tex:1128-1178`, especially `Blambda` | finite decreasing limit, one-Lipschitz continuity, value `-s` on the ray, and weak `Delta B <= 0`; `narrows` additionally needs a.e. unit-gradient/asymptotic-ray direction | checked metric core plus `busemann_lap`, obtained from escaping-pole `dist_lap_distrib` and compact-support dominated convergence | checked weak endpoint; stronger `narrows` extension missing | endpoint is warning-free focused/named-refresh green and the 58-declaration common audit reports only standard logical axioms; local Sobolev/unit-gradient/asymptotic-direction machinery remains for `narrows` |
| P1c splitting | MT `prelim.tex:1528-1606`, `line` and two-end `splitting` | supplied unit-speed minimizing line plus complete connected `Ric >= 0` gives an aligned global Riemannian product; two ends additionally give a compact factor | checked `IsMinimizingLine.pos_ray`/`neg_ray`, `buse_pair_nonneg`, `buse_pair_line`, `IsLapLEDistribOn.add`, `buse_pair_lap`, local Busemann-pair `W^{1,2}`, nonnegative `H₀¹` density, normalized metric coefficients, arbitrary-ball strong minimum, `chart_super_of_lap`, `buse_pair_eq_zero`, and `busemann_chart_sol`; Bochner pointwise identity exists downstream | prove smooth-coefficient weak solution to smooth representative, then eikonal/Hessian-zero, parallel-flow, and product assembly | the checked local analytic inputs add no splitting assumptions; the at-infinity line construction for `topsplit` remains P1d-dependent |
| P1c soul | MT `prelim.tex:1295-1321`, `soul`; P3 uses at `temp2kappa:2293,3581,3612,3714,3727` | complete connected noncompact `sec >= 0` gives compact totally convex/totally geodesic soul and diffeomorphism to its normal bundle; `sec > 0` gives point soul and `M` diffeomorphic to Euclidean space | no native soul, convex-exhaustion, smooth normal-bundle, normal exponential, or global normal-diffeomorphism chain found | missing producer; independent endpoint | MT's proof invokes `lengthcompar`, so that source route crosses the recorded P1d boundary; do not conflate soul with splitting |

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
