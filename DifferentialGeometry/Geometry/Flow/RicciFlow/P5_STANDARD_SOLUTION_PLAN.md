# P5 execution plan: the standard solution

Date: 2026-08-29

Authority: this is the phase-specific execution plan for P5 in
`POINCARE_PLAN.md`.  Morgan--Tian `stdsoln.tex` is the mathematical reference;
all implementation belongs in `DifferentialGeometry/` and uses native
RicciFlower APIs.

## 0. Start ruling and honest status

P5 may start now, but it cannot yet finish.

The initial metric, compact approximation, short-time limiting flow,
completeness, scoped noncompact parabolic analysis, rotational symmetry, and
specialized uniqueness lanes can be developed independently of the unfinished
P3/P4 endpoints.  The terminal statements `std_time_one` and `std_canon`
cannot close until the P3 kappa-solution canonical-neighborhood results and the
P4 singular-flow limit theorem are available.  The standard noncollapsing
argument also needs the complete bounded-curvature form of the P2 reduced-
volume theorem, not merely the checked compact `smooth_nlc` endpoint.

Current accounting:

- P5 main theorem: 0%; it is not stated or proved.
- P5-specific machinery: about 0--3%; no standard-solution module exists yet.
- Reusable compact-flow, Schauder, metric-completeness, and compactness
  infrastructure: substantial, but it is not counted as P5 theorem progress.
- Whole P0--P9 infrastructure: approximately 15--25%, with the denominator
  warning in `POINCARE_PLAN.md`.

## 1. Mathematical endpoint

Fix one standard initial metric on three-dimensional Euclidean space.  The P5
endpoint must produce its maximal Ricci flow and prove the Morgan--Tian package:

1. existence for positive time;
2. uniqueness among partial standard flows;
3. maximal time equal to one in the chosen normalization;
4. completeness and strictly positive curvature for positive time;
5. invariance under the standard rotation action;
6. smooth cylindrical asymptotics on every compact time subinterval;
7. kappa-noncollapsing below one fixed scale;
8. high-curvature canonical neighborhoods, including backward evolving necks;
9. the cap/neck corollaries consumed by surgery.

The main public endpoint should be a theorem such as `std_solution_main`, not a
structure whose fields assume these conclusions.  All public names must remain
at most twenty characters.

## 2. Scope boundaries

P5 will prove only the noncompact analysis needed by the standard solution.
It will not introduce a general noncompact Ricci-flow existence hierarchy, a
full Chen--Zhu uniqueness theorem, an RFWS or surgery-time object, or a generic
warped-product geometry hierarchy.

Use two ordinary data/proof pairs, not classes:

- `StdInit` for the chosen initial metric and geometric witnesses;
- `IsStdInit` for completeness, curvature, symmetry, tip, and exact cylindrical
  end properties;
- `StdFlow` for lifespan and metric-family data;
- `IsPartialStd` for the Ricci equation, initial condition, local-in-time
  curvature bounds, and standard-end behavior.

Maximality, uniqueness, canonical neighborhoods, and time-one existence are
theorems about this data.  They must not be stored as assumptions in `StdFlow`.

## 3. Native assets and audited gaps

Reusable native assets:

- closed-manifold DeTurck short-time existence;
- maximal compact Ricci flows and extension from bounded curvature;
- provider-native pointed Ricci-flow compactness under `RicciFlow/Compactness/`;
- local controlled-ball Shi estimates used by P2;
- metric completeness under uniform equivalence and compact perturbation;
- round sphere, product metric, pullback metric, orthogonal-action, and sphere
  diffeomorphism APIs;
- Ricci-flow tensor evolution, compact weak maximum principles, and the existing
  compact forward-uniqueness energy machinery;
- compact ordinary-flow reduced geometry through `smooth_nlc`.

Genuine missing producers:

- an explicit standard initial cap metric and its exact cylindrical end;
- compact doubles converging pointed-smoothly to that cap;
- the specialized noncompact linear parabolic existence used for rotational
  Killing fields and harmonic-map gauge;
- a localized noncompact tensor maximum principle and the strong kernel
  alternative shared with P3;
- specialized noncompact Ricci--DeTurck uniqueness with vanishing boundary
  error at cylindrical infinity;
- the complete bounded-curvature P2 noncollapsing bridge;
- P3 kappa-solution canonical neighborhoods and P4 singular-flow limits.

The current compact `forward_unique_of_gram` endpoint is not a noncompact
uniqueness theorem.  Its lower tensor identities and energy calculations may be
reused, but compact integration by parts cannot be silently applied on
Euclidean space.

## 4. Dependency graph

```text
P5-A standard initial metric
  -> P5-B compact doubles and common-time compact flows
  -> P5-C pointed limiting partial standard flow

P5-C + noncompact maximum principle
  -> P5-D completeness and positive curvature

P5-C + local Shi + P1c splitting/kernel alternative
  -> P5-E cylindrical asymptotics and T <= 1

P5-E + scoped noncompact linear parabolic theory
  -> P5-F rotational symmetry
  -> P5-G harmonic-map gauge and Ricci--DeTurck uniqueness
  -> P5-H unique maximal standard flow

P5-E + complete bounded-curvature P2 reduced geometry
  -> P5-I standard kappa-noncollapsing

P5-H + P5-I + P3 canonical neighborhoods + P4 singular limits
  -> P5-J high-curvature canonical neighborhoods
  -> P5-K T = 1 and surgery-facing cap/neck corollaries
```

Only P5-J and P5-K are hard-blocked by P3/P4.  P5-A through the independent
parts of P5-I may be developed now.

## 5. Module layout

Create modules only when their first theorem is ready; do not scaffold empty
wrappers.

```text
DifferentialGeometry/Geometry/Flow/RicciFlow/StandardSolution/
  Defs.lean
  InitialProfile.lean
  InitialMetric.lean
  InitialBounds.lean
  CompactDouble.lean
  CompactApprox.lean
  Existence.lean
  Completeness.lean
  Curvature.lean
  CylinderLimit.lean
  RotationField.lean
  Rotational.lean
  Noncollapse.lean
  HarmonicGauge.lean
  DeTurckUnique.lean
  Unique.lean
  Maximal.lean
  Canonical.lean
  Corollaries.lean
  AxiomCheck.lean
DifferentialGeometry/Geometry/Flow/RicciFlow/StandardSolution.lean
```

Analytic lemmas that are genuinely independent of the standard cap belong in
the lowest existing parabolic or Ricci-flow maximum-principle layer.  They must
not be hidden as private assumptions in `StandardSolution/`.

Every Lean module receives a same-name `.md` note.  The root
`StandardSolution.lean` remains an import-only umbrella.

## 6. Work package P5-A: standard initial geometry

### P5-A1. Freeze the interfaces

Target: `StandardSolution/Defs.lean`.

Define `StdInit`, `IsStdInit`, `StdFlow`, and `IsPartialStd`.  Use
`EuclideanSpace Real (Fin 3)` as the underlying standard space.  Express the
cylindrical end through a native diffeomorphism or partial diffeomorphism and a
pullback-metric equality, not prose or a supplied distance formula.

Acceptance gate:

- the predicates state exactly Morgan--Tian Definition 12.1 and partial standard
  flow, with no maximality or uniqueness fields;
- time intervals use the native interval API rather than assuming every future
  flow starts at zero internally;
- no new class, instance hierarchy, or RFWS object is introduced.

### P5-A2. Construct the radial profile

Target: `StandardSolution/InitialProfile.lean`.

Construct the smooth concave profile used in `stdinit`: spherical near the tip,
constant at large radius, positive away from the tip, and nonincreasing in
slope.  Reuse Mathlib smooth cutoffs and integration APIs.

The recommended route is Morgan--Tian's hypersurface-of-revolution profile.
It avoids creating a general warped-product framework and makes the two
sectional-curvature eigenvalues explicit.  First construct the graph manifold;
transport the resulting metric to Euclidean three-space only after proving the
required diffeomorphism.

Acceptance gate:

- a concrete profile exists without assuming its curvature conclusions;
- spherical and constant-end germs are exact, not asymptotic estimates;
- all public profile names are reusable and below the naming limit.

### P5-A3. Realize the metric and curvature

Targets: `InitialMetric.lean` and `InitialBounds.lean`.

Build the induced metric on the hypersurface of revolution, prove the metric is
round of sectional curvature `1/4` near the tip, and prove it is exactly the
round scalar-curvature-one cylinder outside a compact set.  Prove the radial
and tangential sectional-curvature formulas structurally, then deduce
nonnegative sectional curvature.  Transport the metric to Euclidean space and
use compact-perturbation completeness.

Acceptance gate:

- `exists_std_init` is focused-green and placeholder-free;
- scalar curvature has positive lower and finite upper bounds at time zero;
- compact-core volume and cylindrical-end witnesses are available to later
  noncollapsing arguments;
- the declaration's axiom audit contains only the standard three axioms.

## 7. Work package P5-B/C: existence by compact approximation

### P5-B1. Compact doubles

Targets: `CompactDouble.lean` and `CompactApprox.lean`.

Construct closed hypersurfaces by reflecting a long cylindrical profile and
capping its second end.  Work on one fixed smooth three-sphere model after
transport by diffeomorphisms, rather than creating a family of unrelated
manifold types.  Prove pointed smooth convergence on every fixed compact set to
the standard initial metric.

Acceptance gate:

- each approximant is a smooth metric on a compact connected boundaryless
  three-manifold;
- curvature and all initial jets are uniformly controlled on each fixed pointed
  ball;
- the pointed convergence package matches the actual hypotheses of the native
  compactness endpoint.

### P5-B2. Uniform positive existence time

Target: `Existence.lean`.

Run the checked compact short-time flow on every double.  Use the scalar/
curvature maximum principle and compact extension theorem to obtain one common
positive time and one common curvature bound.  Use local controlled-ball Shi
estimates for pointed compactness; do not consume the unresolved complete-flow
Shi theorem merely for convenience.

### P5-C. Pointed flow limit

Use the provider-native compactness stack under `RicciFlow/Compactness/` to
extract a Ricci flow on Euclidean three-space with the standard initial metric.
Prove the Ricci equation, initial convergence, local-in-time curvature bounds,
and positive lifespan.  The first phase endpoint is `exists_partial_std`.

Acceptance gate:

- `exists_partial_std` is a proved producer, not a theorem conditional on a
  supplied limiting flow;
- no complete noncompact short-time existence theorem is assumed;
- source compactness assumptions are discharged by the compact doubles.

## 8. Work package P5-D/E: geometric properties

### P5-D1. Completeness

Use bounded Ricci curvature on a compact time slab to prove uniform metric
equivalence with the complete initial metric.  Apply the native metric
completeness bridge.  This should be a short consumer once the bound is exposed.

### P5-D2. Nonnegative and positive curvature

Prove a localized weak tensor maximum principle on complete bounded-curvature
flows.  Then prove the strong kernel alternative: either curvature becomes
strictly positive or the null distribution is parallel and gives a splitting.
This producer is shared with P3 and belongs below `StandardSolution/`.

Use positivity near the initial tip and connectedness to eliminate the split
alternative for the standard flow.

### P5-E. Cylindrical asymptotics

For every sequence escaping to infinity, pull back the flow to longer cylinder
windows.  Apply local Shi and pointed flow compactness.  Use the P1c splitting
theorem plus the curvature-kernel result to identify every limit with the
shrinking round cylinder.  Upgrade sequential identification to the uniform
compact-time asymptotic statement `std_asymp_cyl`; deduce `std_time_le_one`.

P5-E can prepare all compactness and pullback producers now, but its final
identification gate waits for the exact P1c splitting consumer.

## 9. Work package P5-F/G: symmetry and uniqueness

### P5-F. Rotational symmetry

Implement only the scoped bounded solution of

```text
partial_t X = Delta X + Ric(X).
```

for the three initial rotational Killing fields.  Prove the evolution equation
for the symmetric part of `nabla X` using invariant tensor APIs, derive its
norm inequality, and apply the noncompact maximum principle using decay at the
cylindrical end.  Conclude that the fields remain stationary Killing fields and
prove `std_rot_symm`.

Do not build a generic Lie-group-action evolution theory.

### P5-G1. Harmonic-map gauge

Use rotational symmetry to reduce the harmonic-map heat flow to the scalar
radial equation in Morgan--Tian.  Build its short-time solution by exhaustion,
uniform estimates, and compactness.  The required endpoint includes decay
through three spatial derivatives, because Ricci--DeTurck uniqueness consumes
those bounds.

### P5-G2. Ricci--DeTurck uniqueness

Adapt the checked compact forward-energy identities, replacing compact
integration by parts with an exhaustion and boundary-error estimate.  State the
specialized endpoint for uniformly equivalent bounded Ricci--DeTurck solutions
with common initial metric, uniform `C2` bounds, and common sequential
asymptotics at infinity.  Prove boundary errors vanish; do not assume the
desired equality.

Combine harmonic gauges, Ricci--DeTurck uniqueness, and time-dependent ODE
uniqueness to prove `std_flow_unique` on overlap intervals.

## 10. Work package P5-H/I: maximal flow and noncollapsing

### P5-H. Canonical maximal flow

After overlap uniqueness is checked, glue compatible partial flows and define
the canonical maximal lifespan.  Prove the extension alternative: a finite
endpoint below the target time forces unbounded curvature.  This avoids storing
maximality as input data.

### P5-I. Kappa-noncollapsing

First prove early-time volume lower bounds from the compact core and exact
cylindrical end.  Prove the scalar upper ODE bound using the asymptotic maximum
argument.  For later times use the complete bounded-curvature P2 reduced-volume
producer.  The compact `smooth_nlc` theorem alone is not an admissible
substitute.

Endpoint: `std_nonc`, with one positive scale and one positive kappa valid on
the entire standard flow.

## 11. Work package P5-J/K: canonical neighborhoods and P6 interface

This package is intentionally gated.

P5-J consumes:

- P5 completeness, positive curvature, asymptotics, and noncollapsing;
- P3 kappa-solution compactness and canonical-neighborhood classification;
- P4 `smlmtflow`/`kaplimit` singular-flow convergence;
- stability of canonical neighborhoods under smooth pointed convergence.

It proves `std_canon`: every sufficiently high-curvature point has a strong
canonical neighborhood, and a strong neck extends backward for the required
rescaled time.

P5-K then proves:

- `std_time_one` by excluding a maximal time below one;
- `std_scal_lower`, the `c / (1 - t)` scalar lower bound;
- `std_nbhd`, the cap/initial-neck/backward-neck trichotomy;
- `std_cap`, the surgery-cap core corollary;
- `std_limit`, transfer of cap neighborhoods to convergent generalized flows.

The final `std_solution_main` packages the proved conclusions and is checked by
`StandardSolution/AxiomCheck.lean`.

## 12. Parallelization and ownership

The safe initial parallel lanes are:

| Lane | First owned file | Independent output |
| --- | --- | --- |
| A | `InitialProfile.lean` | concrete smooth cap profile |
| B | `Defs.lean` | minimal data/proof interfaces |
| C | a new low-layer maximum-principle module | localized weak scalar/tensor maximum principle |
| D | a design note under `StandardSolution/` | exact audit of native compactness hypotheses for the double sequence |
| E | a new low-layer parabolic module | bounded linear vector-field equation on the cylindrical-end background |

Do not parallelize two agents inside the same new module.  Every Lean file must
be claimed before editing.  Active build and file claims are never force-
released.

The recommended first implementation brick is P5-B `Defs.lean` followed
immediately by P5-A2 `InitialProfile.lean`.  This freezes the theorem-facing
objects and proves genuine geometry without waiting on P1c, P3, or P4.

## 13. Verification ladder

For every module:

1. focused check the owned file through `lake-locked.ps1`;
2. remove local warnings and placeholders;
3. refresh only when a direct downstream consumer needs the export;
4. check the nearest phase umbrella after each package gate;
5. run `#print axioms` only on package endpoints and the final theorem;
6. update the same-name note and this plan's status log.

Milestone audits:

- Gate A: `exists_std_init`;
- Gate C: `exists_partial_std`;
- Gate G: `std_flow_unique`;
- Gate I: `std_nonc`;
- Gate K: `std_solution_main`.

No package percentage becomes theorem completion until its named endpoint is
stated, proved, focused-green, and placeholder-free.

## 14. Stop conditions

Stop and redesign rather than adding assumptions if any of these occurs:

- the initial metric interface assumes its curvature, cylindrical, or
  completeness conclusions without a concrete producer;
- compact approximants are postulated rather than constructed;
- a compact maximum principle or integration-by-parts theorem is applied on
  Euclidean space without localization;
- rotational symmetry or uniqueness is assumed to prove the asymptotics that
  are later used to prove the same symmetry or uniqueness;
- `std_nonc` consumes compact `smooth_nlc` without a complete-flow bridge;
- `std_canon` is attempted before the P3/P4 limit inputs exist;
- an RFWS/event-seam object enters the ordinary standard-flow definitions.

## Status log

### 2026-08-30: canonical profile and punctured metric

- P5-A2 is focused-green: `stdRadius` is a concrete globally smooth concave
  profile, exactly round near the tip, exactly radius two on the outer end,
  positive away from zero, and with derivative in `[0, 1]`.
- The first P5-A3 realization is focused-green in `InitialProfile.lean`:
  `stdCylMetric` is the smooth positive-radius warped metric, `stdEndMetric` is
  the exact product round-cylinder metric, and `stdCyl_end` identifies them past
  `capEnd`.
- The analytic radial and tangential curvature coefficients are nonnegative and
  have the exact endpoint values: `(1/4, 1/4)` in the round-cap interior and
  `(0, 1/4)` in the cylindrical interior.
- `exists_std_init` remains unstated and 0%.  The remaining P5-A3 frontier is
  structural rather than elaborational: the tree has neither a warped-product
  curvature formula nor a hypersurface Gauss equation, and the sphere-polar API
  stops at ambient smoothness and set-level bijectivity rather than a local
  diffeomorphism with a pullback-metric identity.  A smooth polar-collapse
  extension across the origin is also still required before completeness can
  be proved on Euclidean three-space.
- P5-A dedicated machinery is approximately 25--35%; all dedicated P5
  machinery is approximately 4--7%.  The P5 main theorem remains 0%, and the
  whole Poincare-program infrastructure estimate remains approximately
  15--25%.

### 2026-08-30: A-D verification update

- A, B, C, and D pass focused verification in their own modules.
- `std_limit_of_bounds` is a checked conditional application of the native
  Hamilton compactness theorem.
- The missing upstream mathematics is unchanged: realize `capJoin` as a
  complete nonnegatively curved capped-cylinder metric, construct the actual
  compact doubles, and prove a common existence interval with uniform curvature
  and basepoint injectivity bounds.
- The main P5 standard-solution existence theorem is still unstated and 0%.
  Its dedicated checked machinery is approximately 3--6%; the whole Poincare
  program remains at the previously recorded approximately 15--25%
  infrastructure level, with the final theorem endpoint at 0%.

### 2026-08-30: A-D first implementation pass

- P5-A: `StdInit`, `IsStdCore`, `IsMetricInv`, and core projection lemmas are
  source-complete and focused-check green. This is an API/core result, not a
  constructed standard metric.
- P5-B: the globally smooth `capJoin` profile is focused-check green and is
  exactly round near the tip and exactly cylindrical outside radius two. The
  profile-to-metric realization and nonnegative-curvature proof remain missing.
- P5-C: `ClosedApprox` and `exists_closed_flow` are focused-check green. The
  actual Morgan--Tian compact-double sequence and uniform estimates remain 0%.
- P5-D: `std_limit_of_bounds` is source-written as a direct consumer of native
  `compactnessSol`, but focused verification is blocked by stale elaboration
  lock `4636159b-87de-4e97-8f01-e69580cbb67f`; no force-release was performed.
- P5 main theorem remains 0%. Dedicated P5 machinery is now approximately
  3--6%; the whole Poincare-program infrastructure estimate remains 15--25%.

- 2026-08-29: phase-level audit completed.  P5 is open for implementation at
  P5-A/B/C and the scoped analytic lanes.  The final canonical-neighborhood and
  time-one package is explicitly gated by complete-flow P2, P1c, P3, and P4.
  P5 theorem completion remains 0%; this plan does not count shared
  infrastructure as a proved standard solution.

## 2026-08-31: structural warped-product curvature formula

- Geometry/Curvature/WarpedProduct.lean is warning-free focused GREEN.
- The checked endpoint warpRm_coeffs gives the complete radial/tangential
  curvature-numerator decomposition for the standard warped connection with a
  unit-curvature fiber.
- warp_koszul certifies the connection term against the native Koszul API.
- The concrete metricRm04StdAt theorem for stdCylMetric remains unstated
  (0%). Its smallest next bridge is the identification of the difference
  between the warped and product Levi-Civita connections with warpConnDiff.
- Progress: P5-A profile/curvature stage about 35-45%; final P5 theorem 0% with
  about 6-10% of its dedicated machinery; whole Poincare infrastructure about
  15-25%.
