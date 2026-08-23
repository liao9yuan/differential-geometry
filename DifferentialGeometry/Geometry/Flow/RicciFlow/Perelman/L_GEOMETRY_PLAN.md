# B2 / P2 plan: Perelman's L-geometry

Written 2026-08-15.  This is the execution plan for the `P2` phase of
`../POINCARE_PLAN.md`, called **B2** in the current work allocation.  Its
mathematical references are Morgan--Tian `newcompar.tex`, `newcomp2.tex`, and
`noncoll.tex`.  Those files are references only; all implementation belongs
under `DifferentialGeometry/` and uses RicciFlower conventions.

## 0. Scope and final deliverables

The first implementation target is Perelman's L-geometry for an **ordinary
smooth Ricci flow on one fixed manifold**.  Surgery-space-time paths are a
later consumer-facing extension.  In particular, the first stages must not:

* introduce a global RFWS or an exotic space-time manifold;
* represent topology change by a single family `Real -> Metric M`;
* make generalized-flow data a field of the basic L-length definition;
* replace existence, cut-locus, or monotonicity arguments by supplied
  hypotheses with endpoint-looking names.

For a solution `S : SolutionOn D`, terminal forward time `T`, and a curve
`gamma : Real -> M` parameterized by backward time `tau`, use

```text
g_tau       = S.metric (T - tau)
X(tau)      = d gamma / d tau
L(gamma)    = integral sqrt(tau) * (R(T-tau,gamma(tau)) + |X(tau)|^2_g_tau)
l(q,tau)    = inf_gamma L(gamma) / (2 * sqrt(tau))
Vtilde(tau) = integral (4*pi*tau)^(-n/2) * exp(-l(q,tau)) dmu_g_tau(q)
```

The normalization of reduced volume is the standard `(4*pi*tau)^(-n/2)`
normalization.  Morgan--Tian sometimes suppresses the constant; theorem
statements must record which normalization they use.

The ordinary-flow capstones are:

1. `redVolume_anti`: reduced volume is antitone in backward time;
2. `smooth_nlc`: the resulting kappa-noncollapsing theorem for smooth flows;
3. scaling and pullback naturality sufficient to feed the existing
   `Perelman.NoLocalCollapsing` interface.

The later surgery capstone is an eventwise version of `smooth_nlc` whose
L-curves may cross metric seams and whose loss is controlled exactly as in
Morgan--Tian `noncoll.tex`.  It is not part of the initial fixed-manifold API.

Honest status at creation:

* `redVolume_anti`: unstated and unproved, **0%**;
* `smooth_nlc`: unstated and unproved, **0%**;
* dedicated L-geometry machinery: **0%**;
* reusable generic prerequisites already in the tree: roughly **35--45%**
  (curve derivatives, variational calculus, curvature, volume, exponential
  maps, and parabolic scaling).  This prerequisite number is not theorem
  completion.

## 1. Existing native assets

Reuse these APIs rather than building parallel versions.

| Need | Existing native layer |
|---|---|
| metric family and scalar curvature | `RicciFlow/Basic/Core.lean`: `SolutionOn`, `IsSolutionOn`, `SolutionOn.scalar` |
| time translation | `SolutionOn.timeShift` and its metric/scalar lemmas |
| parabolic scaling | `RicciFlow/ParabolicRescaling.lean` |
| velocity of a manifold curve | `mfderiv (I := source model) I gamma tau 1` and `MFDerivAlongCurve` |
| intrinsic derivative along a curve | `Connection/ParallelTransport/CovariantDerivativeAlong.lean`: `covDerivAlong` |
| smooth two-parameter variations | `Comparison/Variation/*`, especially `IsSmoothVariation` |
| first and second variation patterns | `Variation/FirstVariation.lean`, `SecondVariation.lean`, `RegularParameterFirstVariation.lean` |
| curvature commutation | `Variation/CovariantCommutationCurvature.lean` |
| Jacobi and exponential-map machinery | `Geometry/Exponential/*` |
| gradient, Hessian, Laplacian | `Geometry/Operator/Operators.lean`, `HessianTraceRealization.lean` |
| Riemannian volume | `Analysis/Integration/Measure/RiemannianMeasure.lean` and `Integration/Volume/*` |
| normal-coordinate Jacobians | `Comparison/Volume/NormalChartMeasure.lean`, `JacobianBounds.lean` |
| target NLC vocabulary | `Perelman/Noncollapsing.lean` |

The key missing reusable bridge is a clean calculus API for a curve evaluated
against the **moving metric** `S.metric (T - tau)`.  Build that bridge at the
lowest natural layer; do not copy the fixed-metric variation proofs into every
L-geometry theorem.

## 2. Module layout

Create the directory

```text
DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/LGeometry/
```

and use the following modules.  Keep the umbrella
`Perelman/LGeometry.lean` import-only once there is more than one module.

| Module | Responsibility |
|---|---|
| `Defs.lean` | velocity, speed squared, L-density, L-length |
| `Reparam.lean` | `s = sqrt(tau)` regularization and change of variables |
| `MovingMetric.lean` | time derivative of inner products and along-curve identities |
| `FirstVariation.lean` | first variation and Euler--Lagrange equation |
| `Geodesic.lean` | `IsLGeodesic`, regularized ODE, existence and uniqueness |
| `Exp.lean` | L-exponential map and its local smoothness |
| `Scaling.lean` | parabolic-scaling naturality of regularized curves and L-exp |
| `Naturality.lean` | fixed-diffeomorphism pullback naturality |
| `Jacobi.lean` | L-Jacobi equation and differential of L-exp |
| `SecondVariation.lean` | L-index form and second variation |
| `Minimizer.lean` | minimizing L-geodesics and L-cost |
| `CutDomain.lean` | minimizing domain, conjugate/cut alternatives, measurability |
| `ReducedLength.lean` | reduced length, gradient/time identities, weak inequalities |
| `Lipschitz.lean` | local Lipschitz and a.e. differentiability |
| `ReducedVolume.lean` | reduced-volume measure and tangent-space formula |
| `Monotonicity.lean` | Jacobian density and `redVolume_anti` |
| `CompleteFlow.lean` | complete bounded-curvature extension (`newcomp2.tex`) |
| `SmoothNLC.lean` | smooth-flow kappa-noncollapsing producer |

Tentative public names respect the 20-character limit:

```text
lVelocity       lSpeedSq       lDensity       lLength
IsLGeodesic     lExp           IsLJacobi      lCost
redLength       redDensity     redVolume      redVolume_anti
smooth_nlc
```

Names are tentative until their live signatures are tested.  Do not create a
data structure merely to make these names possible; raw curves plus separate
regularity hypotheses are preferred initially.

## 3. Mathematical dependency ladder

### L0. Definitions and time orientation

Implement the four scalar definitions in `Defs.lean` for raw curves
`gamma : Real -> M`.  Definitions are total because `SolutionOn`'s metric
family is total on `Real`; theorems that use the Ricci-flow equation must carry
the honest hypothesis that `T - tau` lies in `D.carrier`.

First checked facts should include:

* `lSpeedSq` is nonnegative;
* `lLength ... a a = 0`;
* additivity across adjacent intervals, with exactly the integrability
  hypotheses required by `intervalIntegral`;
* integrability/continuity of the density for a smooth curve on a compact
  positive backward-time interval;
* invariance under eventual equality of curves on the integration interval.

Do not claim L-density is nonnegative without a scalar-curvature hypothesis:
scalar curvature may be negative.

### L1. Square-root reparameterization

For `alpha(s) = gamma(s^2)`, prove the velocity relation

```text
A(s) = 2*s * X(s^2)
```

in tangent-space form, then prove

```text
L(gamma; tau1,tau2)
  = integral_[sqrt(tau1),sqrt(tau2)]
      (1/2 * |A(s)|^2 + 2*s^2*R(T-s^2,alpha(s))) ds.
```

This is the regular normal form at `tau = 0`; all ODE existence at the base
time should use `s`, not the singular `1/(2*tau)` equation directly.

Stop and add a general interval-integral substitution lemma only if Mathlib's
existing change-of-variables theorem cannot express the square map.  Such a
lemma belongs in `Analysis/Integration`, not in a Ricci-flow consumer.

### L2. Moving-metric calculus and first variation

For `g_tau = g(T-tau)`, first prove the reusable scalar identity

```text
d/dtau <Y,Z>_g_tau
  = <D_tau Y,Z> + <Y,D_tau Z> + 2*Ric(Y,Z).
```

Then adapt the existing fixed-metric variation engine to show the first
variation formula, including the endpoint term
`2*sqrt(tau)*<Y,X>`.  Deduce the Euler--Lagrange equation

```text
D_tau X - 1/2 grad R + (1/(2*tau))*X + 2*Ric(X,.)^sharp = 0.
```

Define `IsLGeodesic` by this intrinsic equation on positive backward times.
Do not define it as “is a critical point” until a sufficiently general
fundamental lemma of calculus of variations is available; instead prove the
critical-point equivalence afterward.

### L3. Regularized ODE and L-exponential

Rewrite the equation in `s = sqrt(tau)`.  Use chart ODE existence to prove a
unique L-geodesic with

```text
gamma(0) = x,
limit sqrt(tau)*X(tau) = Z.
```

Define `lExp S T x Z tau` by evaluating that solution.  Prove:

* initial value and initial tangent normalization;
* smooth dependence on `(Z,tau)` for `tau > 0` and the regularized extension
  at `tau = 0`;
* pullback and parabolic-scaling naturality.

Do not use the ordinary exponential map as the definition of `lExp`; it is
only the small-time comparison model.

### L4. L-Jacobi and second variation

Differentiate the L-geodesic equation using the existing curvature
commutation theorem.  Define `IsLJacobi` and identify solutions with the
differential of `lExp`.  Prove the regularized initial-value theorem at
`tau = 0`.

Then define the L-index form and prove the second-variation formula.  Reuse the
existing `Variation.SecondVariation` proof architecture, but keep the moving
metric and `nabla Ric`, `Hess R` correction terms explicit.  The main output is
positivity of the L-index form along a minimizing segment before the first
L-conjugate point.

### L5. Minimizers, L-cost, and the cut domain

Define `lCost` as the infimum of `lLength` over admissible curves with fixed
endpoints.  Prove existence of a minimizer first on compact manifolds.  The
complete bounded-curvature case is postponed to L8.

Build the analogue of the ordinary injectivity domain:

* unique minimizing L-geodesic before cut time;
* L-exp is a local diffeomorphism away from L-conjugate points;
* the minimizing tangent domain is open and star-shaped in backward time;
* its complement/cut image is measurable and has zero Riemannian measure in
  the form needed for change of variables.

This is the first major global-geometric frontier.  Do not assume a measurable
cut decomposition in `ReducedVolume.lean`; prove it here or leave the precise
frontier visible.

### L6. Reduced length and differential inequalities

Define

```text
redLength(q,tau) = lCost(x,q,tau) / (2*sqrt(tau)).
```

On the smooth minimizing domain prove the gradient and time-derivative
identities and the trace/Hessian inequalities from Morgan--Tian
`newcompar.tex` Sections “Second-order differential inequalities” and
“Reduced length”.  Then prove local Lipschitz estimates and extend the key
inequalities weakly or almost everywhere across the cut locus.

Do not encode the inequalities only on supplied smooth subsets; the later
measure theorem needs a statement covering almost every point of a time
slice.

### L7. Reduced volume and monotonicity

Define `redDensity` and `redVolume` using
`riemannianVolumeMeasure (S.metric (T-tau))`.  Prove the tangent-space
change-of-variables formula through `lExp` and its Jacobian.

For fixed initial tangent `Z`, prove antitonicity of

```text
tau^(-n/2) * exp(-redLength(lExp Z tau,tau)) * Jac(lExp_tau)(Z).
```

and its Euclidean small-time limit.  Integrate on the nested minimizing
domains to obtain `redVolume_anti`.  This is the ordinary-flow capstone of the
core L-geometry lane.

The Jacobian proof must use the L-Jacobi fields and second-variation trace
bound.  A theorem taking pointwise Jacobian monotonicity as an assumption is
not completion of this stage.

### L8. Complete bounded-curvature flows

Follow Morgan--Tian `newcomp2.tex`:

* existence of minimizing L-geodesics by coercivity and Hopf--Rinow;
* local Lipschitz estimates under bounded curvature;
* `min redLength <= n/2`;
* distributional reduced-length inequalities using compact cutoffs;
* reduced volume bounded by the Euclidean value, with rigidity.

Reuse the project's completeness, properness, Shi bounds, and cutoff/barrier
machinery.  Do not strengthen consumers to compactness when the book only
requires completeness plus bounded curvature.

### L9. Noncollapsing and surgery extension

First prove `smooth_nlc` for ordinary compact smooth Ricci flows and adapt it
to the existing `Perelman.NoLocalCollapsing` predicate.  Compare this output
with the entropy/W route; keep one canonical public predicate and two producer
theorems, not two noncollapsing hierarchies.

Only after the ordinary proof is complete, extend L-length across the event
presentation from `Perelman/Surgery/`.  A crossing path is piecewise a smooth
fixed-manifold path, with adjacent pieces matched by the surgery seam.  Prove
additivity of L-length and metric invariance on the kept region before
attempting Morgan--Tian `noncoll.tex`'s good/bad path decomposition.

The generalized-flow noncollapsing theorem is a P7 producer and must remain
separate from `smooth_nlc`.

## 4. First execution brick

The first implementation session should work only in
`E:/testdifferential-geometry` on branch `short-time-existence` and begin with:

1. reread `AGENTS.md`, `important_lesson.md`, `lessons.md`, `convention.md`,
   `dictionary.md`, this plan, and the live signatures named in Section 1;
2. confirm the working tree and file claims; do not touch stale claims or
   unrelated files;
3. create `Perelman/LGeometry/Defs.lean` and `Defs.md`;
4. implement `lVelocity`, `lSpeedSq`, `lDensity`, and `lLength` for an ordinary
   `SolutionOn` and raw curve;
5. prove the smallest stable L0 facts listed above, including at least one
   non-definitional integrability or congruence result;
6. focused-check the file through `scripts/lake-locked.ps1`; review the diff;
7. update this plan's status and next exact theorem, then continue into
   `Reparam.lean` if L0 is green.

The first session must not add `sorry`, an endpoint wrapper, a new foundational
class, or an RFWS object.  If a moving-fibre elaboration problem appears,
scalarize after applying the metric to the velocity; do not prove equality of
whole tangent-bundle or Hom objects.

## 5. Verification and stop conditions

For every Lean file, claim it before editing, use focused checks first, and
write the same-name Markdown note.  Refresh an `.olean` only when a downstream
module needs a newly exported declaration.  Never run raw `lake build`.

Stop and report rather than disguising the gap if any of the following occurs:

1. the basic definition appears to require an RFWS or a dependent space-time
   tangent bundle;
2. the square-root reparameterization needs a genuinely absent manifold chain
   rule or interval substitution theorem;
3. first variation requires a new consumer assumption instead of a reusable
   moving-metric identity;
4. L-geodesic existence cannot be expressed with the current chart ODE API;
5. cut-domain measurability would have to be assumed;
6. monotonicity is reduced to a new black-box Jacobian inequality;
7. surgery topology is being mixed into the ordinary-flow core.

At every handoff record separately:

* capstone theorem percentage (`redVolume_anti` remains 0% until stated and
  proved);
* dedicated L-geometry machinery percentage;
* generic reused infrastructure;
* exact smallest failed theorem/API and whether it is routine, missing API, or
  a genuine mathematical frontier.

## Status log

- 2026-08-15: plan created after a live source audit.  No native L-length,
  reduced-length, or reduced-volume declaration existed.  The fixed-manifold
  first route was selected; `Defs.lean` is the first execution target.
- 2026-08-15 (L0--L1 execution): `LGeometry/Defs.lean` and
  `LGeometry/Reparam.lean` are focused-green, warning-free, and contain no
  `sorry` or `admit`.  L0 now has the four total fixed-manifold definitions,
  speed-square nonnegativity, zero/additive interval laws, germ-level
  congruence, and moving-metric/scalar continuity plus integrability.  L1 now
  has `A(s) = 2s X(s^2)`, the regularized density, and the oriented
  square-root interval formula.  Mathlib's existing monotone substitution
  theorem was sufficient, so no generic integration wrapper was added.

  The next exact theorem is `lInner_deriv` in `MovingMetric.lean`.  At a
  backward time `tau0` with `T - tau0` regular, and for differentiable sections
  `V,W` along `gamma`, it should state the `HasDerivAt` identity

  ```text
  d/dtau <V,W>_{g(T-tau)} |_{tau0}
    = <D_tau V,W> + <V,D_tau W> + 2 Ric(V,W)
  ```

  using `covDerivAlong` for the two fixed-time connection terms and
  `IsSolutionOn.equation` for the backward-time metric term.  Prove the
  chart-regularity form matching the existing metric-compatibility theorem
  first, then add a smooth-curve wrapper.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **2--3%**; reusable generic prerequisites about **35--45%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%** because this first local brick does not materially move the
  multi-year denominator.

- 2026-08-15 (L2 moving-metric brick): `LGeometry/MovingMetric.lean` is
  focused-green, warning-free, and contains no `sorry` or `admit`.
  `lInner_deriv_chart` proves the weakest pinned-chart form of

  ```text
  d/dtau <V,W>_{g(T-tau)}
    = <D_tau V,W> + <V,D_tau W> + 2 Ric(V,W),
  ```

  and `lInner_deriv` supplies a pointwise-smooth wrapper.  The proof uses a
  jointly differentiable scalar chart-Gram pairing and its two coordinate
  slices; it does not infer the full derivative by merely adding two frozen
  formulas, and it introduces no new family class or moving-bundle equality.

  The next exact theorem is `lDensity_deriv` in
  `LGeometry/FirstVariation.lean`, the pointwise variation derivative of the
  L-density.  Reuse the native speed-square variation and mixed-covariant
  commutation plus fixed-time scalar-gradient duality.  Do not add an
  integrated variation theorem with a new domination hypothesis; first
  produce any missing joint compact-slab regularity at the reusable layer.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **4--5%**; reusable generic prerequisites about **35--45%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-15 (L2 first variation and equation):
  `LGeometry/FirstVariation.lean` and `LGeometry/Geodesic.lean` are
  focused-green, warning-free, and contain no `sorry` or `admit`.
  `lLength_first_var` proves the complete oriented Morgan--Tian first-variation
  identity, with compact domination and all interval integrability produced
  internally.  `lEulerPair` and `lLength_euler` give the fully applied scalar
  Euler-residual form.  `HasLEquationAt` prevents fake solutions at
  nondifferentiable points, `IsLGeodesic` is set-indexed for local positive
  regular-time segments, and `lFirst_var_zero` proves equation implies
  fixed-endpoint stationarity.

  Three independent routes have now been rejected.  Separate fixed-time scalar
  smoothness plus joint value continuity did not control spatial derivatives;
  pointwise difference quotients/FTC still lacked a common compact bound; and
  the existing exponential-map variation realization requires global
  completeness, connectedness, and continuous Riemannian-bundle assumptions
  absent from this lane.  The first two were resolved by the new generic
  producers `derivFst_contMDiffAt`, `scalarJointAt`, and `metricCLMSmoothAt`.
  The third is the current honest stop condition.

  The exact next producer is `exists_chartVar` in the generic
  comparison/variation layer: realize a compactly supported smooth field along
  a curve, supported inside one coordinate chart, by a smooth variation fixed
  wherever that field vanishes.  This should enable the fundamental-lemma
  converse from fixed-endpoint criticality to the pointwise L-geodesic equation
  without strengthening consumers.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **8--10%**; reusable generic prerequisites about **40--50%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-15 (L2 criticality equivalence): the third route boundary is now
  resolved without stronger consumer assumptions.  The generic
  `Comparison/Variation/ChartVariation.lean` module proves `exists_chartVar`:
  a compactly supported smooth model field whose supported curve image lies
  in one chart is realized as the transverse field of a global smooth
  variation, fixed wherever the field vanishes.  Its assumptions do not
  include completeness, connectedness, a metric, or a continuous
  Riemannian-bundle package.

  `LGeometry/FirstVariation.lean` now exposes the continuity producers
  `lGrad_contOn`, `lCross_contOn`, and `lEuler_contOn`, together with test-vector
  linearity `lEulerPair_smul`.  `LGeometry/Geodesic.lean` defines the canonical
  fixed-endpoint predicate `IsLCritical`; `IsLGeodesic.critical` proves the
  forward implication, and `IsLCritical.isLGeo` uses `exists_chartVar`, the
  scalar fundamental lemma, and continuity to prove the pointwise Euler
  equation on `Ioo a b`.  The generic producer and first-variation module have
  green targeted refreshes, while `Geodesic.lean` is focused-green and
  warning-free.  These files contain no `sorry` or `admit`.

  L2 is therefore complete at the planned intrinsic/criticality level.  The
  exact next theorem is `lEuler_sq` in `LGeometry/Geodesic.lean`: for
  `alpha(s) = gamma(s^2)` and `A = alpha'`, prove at `s > 0` the fully applied
  identity

  ```text
  4*s^2*lEulerPair
    = <Y,D_s A> - 2*s^2*<grad R,Y> + 4*s*Ric(Y,A).
  ```

  This is the nonsingular L3 normal form.  Do not start chart ODE existence
  from the singular `tau` equation, and do not define `lExp` before this
  identity is green.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **10--12%**; reusable generic prerequisites about **45--55%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-16 (first L3 regularized ODE brick): the square-root normal form and
  its first-order phase interface are focused-green and warning-free, with no
  `sorry` or `admit`.  The generic connection layer now has
  `covDerivAlong_comp`, and `lVelocity_sq_pos` supplies the positive-time germ
  identity even when manifold derivatives use their totalized zero value.
  `lEuler_sq` proves

  ```text
  4*s^2*lEulerPair
    = <Y,D_s A> - 2*s^2*<grad R,Y> + 4*s*Ric(Y,A).
  ```

  `lRegAccel` packages the direct vector right-hand side
  `2*s^2*grad R - 4*s*Ric-sharp(A)`, and
  `HasLEquationAt.accel_sq` upgrades the all-test-vector equation to
  `D_s A = lRegAccel`.  `lPhaseField` is the corresponding fixed-chart
  first-order system.  Its zero-time value is the ordinary phase field of
  `g(T)`, and the correct seed is `A(0) = 2*Z`, not `Z`.

  The exact next theorem is `lPhaseField_smoothAt` in `Geodesic.lean`: under
  `hS : IsSolutionOn S`, `T - s^2 in D.regular`, and a chart-interior phase
  point, prove joint `C-infinity` regularity of
  `Function.uncurry (lPhaseField S T x0)` at `(s,z)`.  Existing manifold
  integral-curve existence and uniqueness are sufficient after autonomizing
  on `Real x (E x E)`; no new Picard class or stronger manifold hypothesis is
  planned.

  `lPhaseField_smoothAt` is currently unstated and therefore **0%**.  The
  smallest missing reusable API is joint smoothness of the fixed-chart
  Christoffel contraction for a smooth metric family: a close proof exists
  only as a private DeTurck helper.  The scalar-gradient and Ricci-sharp terms
  can be produced componentwise from `scalarJointAt`, inverse-Gram
  smoothness, `derivFst_contMDiffAt`, and the metric evolution equation.  This
  is an API-placement gap rather than a mathematical obstruction, and its
  reusable prerequisites are counted separately.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **12--14%**; reusable generic prerequisites about **45--55%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-21 (`arxiv-preprint` migration and L3 existence): the checked L0--L3
  implementation has been migrated to the current native layout.  In
  particular, `Solution/Basic` replaces the older `Basic/Core` route,
  `Evolution/Scalar/JointRegularity.scalar_joint` supplies joint scalar
  regularity, and `Bundle/PartialMfderiv/Basic.timeDeriv_smoothAt` supplies the
  first-time-derivative producer.  The required generic bridges now live at
  their native layers: `metricCLMSmoothAt`, `covDerivAlong_comp`,
  `exists_chartVar`, the fixed-chart metric-sharp formula, and joint scalar and
  Ricci coordinate regularity.  No reference-tree import was introduced.

  `lPhaseField_smoothAt` is now proved and focused-green.  The autonomized ODE
  layer gives `exists_lPhaseSol`, arbitrary-base-time germ uniqueness
  `lPhaseSol_unique_at`, and its zero-time wrapper.  The chart/intrinsic bridges
  then give `exists_lRegCurve`, `lRegCurve_unique_at`, and the zero-time
  specialization, with the correct seed `A(0) = 2*Z`.

  `LGeometry/Exp.lean` completes the first maximal-domain brick:
  `IsLRegCurveOn`, `LRegCurveWitness`, the open `lRegDomain`, the totalized
  `lRegCurve`, `lExpDomain`, and `lExp`, including the zero-domain and zero-value
  laws.  It follows the native `maximalGeodesic` convention and returns the
  base point outside the witnessed domain.  Focused verification is green and
  warning-free, and the migrated files contain no `sorry` or `admit`.

  The exact next theorem is `lRegWitness_eq`: two `IsLRegCurveOn` witnesses on
  open preconnected sets containing zero, with the same `(x,Z)`, agree on the
  intersection of their domains.  It must propagate `lRegCurve_unique_at`
  from the common initial data at zero, after which `lRegCurve` can be shown
  locally equal to any witness and the existing local-flow machinery can
  export smooth dependence of `lExp`.  Pointwise germ uniqueness is complete;
  connected-domain propagation is not yet claimed.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **18--20%**; reusable generic prerequisites about **60--70%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-21 (L3 witness coherence and short-time smooth dependence):
  `LGeometry/Exp.lean` is focused-green and warning-free.  The maximal
  square-root-time domain is now preconnected; `lRegWitness_eq` propagates
  arbitrary-base-time germ uniqueness across overlapping witness intervals;
  and `lRegCurve_eqOn` identifies the totalized maximal curve with every local
  witness.

  The local ODE flow has also been promoted to actual parameter dependence.
  `exists_lPhaseFlow` gives a jointly smooth chart phase flow near a regular
  seed, `exists_lRegFamily` reconstructs a common smooth intrinsic family for
  nearby initial tangent vectors, and `lRegCurve_smoothAt` proves the
  regularized joint extension at `(Z,0)`.  Composing with `sqrt` away from zero,
  `exists_lExpFamily` proves joint smoothness of `lExp` on a uniform short
  positive-time interval.  No compactness/completeness consumer hypothesis,
  ordinary exponential-map definition, or new solution class was introduced.

  The exact next producer is `lRegFamily_extend`: continue this smooth family
  across a compact subinterval of a witnessed regularized solution, using the
  local phase flow and `lRegWitness_eq`.  This is needed before claiming joint
  smoothness at every positive point of the full maximal `lExpDomain`.
  Pullback/parabolic-scaling naturality also remains in L3, and L4 must not use
  the short-time theorem as an all-domain statement.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **22--24%**; reusable generic prerequisites about **65--75%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-21 (L3 full maximal-domain smoothness and naturality): L3 is now
  complete for the ordinary fixed-manifold `SolutionOn` model.  `Exp.lean`
  extends the local phase collar along every witnessed compact
  square-root-time segment.  The resulting declarations `lRegFamily_extend`,
  `lRegCurve_smooth`, `lRegCurve_smoothAt`, `lRegJointDom_open`,
  `lRegCurve_smoothOn`, `lExpPosDom_open`, and `lExp_smoothOn` give joint
  smoothness on the full positive maximal domain, while retaining the smooth
  regularized extension at `s = 0`.

  `Scaling.lean` proves both witness directions under parabolic rescaling and
  then identifies `lRegDomain`, the totalized `lRegCurve`, `lExpDomain`, and
  `lExp`; the terminal formula uses `Z -> R^(-1/2) Z` and `tau -> R*tau`.
  The generic metric input is the native `covDerivAlong_scale` theorem.
  `Naturality.lean` separately proves fixed-diffeomorphism naturality from the
  generic `chartRep_map_diff` and `covAlong_natMDiff` bridges.  Its
  single-witness theorem is directional, while the maximal-domain equality
  genuinely uses the inverse diffeomorphism.  `Perelman/LGeometry.lean` is now
  the import-only public entry point.

  All edited L3 modules are focused-green and warning-free; the two new
  terminal modules also pass targeted module verification.  The lane contains
  no `sorry`, `admit`, new axiom, reference-tree import, new foundational
  class, or strengthened compactness/completeness consumer assumption.

  The exact next declaration is `lRegJacobiPair` in a new `Jacobi.lean`: the
  fully paired scalar linearization of the regularized L-geodesic equation,
  with the current-time metric frozen in both along-curve covariant
  derivatives.  Then define `HasLRegJacobiAt` and `IsLRegJacobi`; the first
  substantive theorem is `lRegVar_jacobi` for a smooth family of regularized
  L-geodesics.  Connecting that theorem to the local `lExp` family will require
  a pointwise `cov_commute_at` adapter in the generic curvature-commutation
  layer, because the existing public wrapper assumes a globally smooth
  variation.  The fixed-chart pointwise identity already exists, so this is a
  routine local API placement task rather than a mathematical blocker and does
  not require consultation.

  Honest progress: `redVolume_anti` **0%**; dedicated L-geometry machinery
  about **30--32%**; reusable generic prerequisites about **75--80%**; P2 as a
  whole remains below **1%**.  The whole Poincare program estimate remains
  **3--5%**.

- 2026-08-22 (L4 Jacobi bridge, index form, and fixed-endpoint second
  variation): the regularized variation equation is now fully connected to the
  ordinary positive-backward-time equation.  `Jacobi.lean` proves
  `lRegVar_jacobiAt`, `lRegVar_jacobi`, the initial-tangent field
  `lRegJacobiField`, `lRegCurve_jacobi`, its normalization
  `lRegJacobi_d0`, and the differential identity `lExpJacobi_eq`.

  `SecondVariation.lean` defines the dynamic `lJacobiVel`, `lJacobiPair`,
  `HasLJacobiAt`, and `IsLJacobi`.  The fully paired square-root bridge
  `lJacobiPair_sq`, the moving-connection regularity theorem
  `lJacobiVel_sq_diff`, and `lJacobi_of_sq` yield `lExp_jacobi` without
  comparing whole moving bundle or Hom-valued objects.  The supporting
  Ricci-flow connection layer separates the scalar pairing identities
  `connBack_pair` and `connBack_along_sq` from `connBack_vec_sq`, which
  reconstructs chart differentiability of the resulting moving vector field.

  The L-index layer now contains `lIndexInt`, `lIndex`, pointwise and integral
  symmetry, the diagonal formula, the scalar balance identity
  `lIndex_balance`, zero interval, adjacent additivity with honest
  integrability hypotheses, Green's identity, the fixed-endpoint form, and the
  Jacobi boundary formula.  The scalar producers `lEuler_var_c1`,
  `lVarJacobiVel_diff`, and `lVarInner_c1` generate the compact-interval
  integrability needed by the concrete consumer.  Consequently
  `lLength_second_var` is proved with only its natural inputs: a smooth
  variation, a central L-geodesic, and fixed endpoints.  Its conclusion is the
  exact equality between the second derivative of L-length and twice
  `lIndex Y Y`; no nonnegativity is claimed without minimization or
  no-conjugate-point input.

  Focused verification is warning-free, the exported `SecondVariation` module
  refresh passes, and the import-only L-geometry umbrella checks against the
  refreshed artifact.  The edited lane contains no `sorry`, `admit`, new axiom,
  reference-tree import, foundational class, generalized RFWS object, or
  strengthened consumer assumption.

  The exact next theorem is `lRegJacobi_unique` in `Jacobi.lean`: on a connected
  regularized-time interval, two regularized L-Jacobi fields along the same
  curve with equal value and equal frozen-metric covariant derivative at one
  time agree throughout the interval.  It should be produced from the native
  regularized phase/ODE uniqueness layer, not added as a consumer hypothesis.
  This is the gate for defining L-conjugate points via the initial-tangent
  differential of `lExp`, and then proving the remaining L4 output, positivity
  of the index form before the first conjugate point.

  Honest progress: `redVolume_anti` **0%**; `lLength_second_var` **100%**;
  the broader L4 phase about **70--75%**; dedicated L-geometry machinery about
  **48--52%**; reusable generic prerequisites about **88--92%**; P2 as a whole
  remains below **1%**.  The whole Poincare program estimate remains **3--5%**.

- 2026-08-22 (L4 regularized Jacobi uniqueness and conjugacy):
  `LGeometry/JacobiUnique.lean` is focused-green and warning-free.
  `lRegJacobi_unique` proves initial-value uniqueness on a connected open
  regularized-time set by putting the field and its moving covariant velocity
  into a fixed-chart linear ODE and propagating equality by an open/relatively
  closed argument.  Its public hypotheses do not assume that the base curve is
  an L-geodesic or add an acceleration equation.

  The reusable coefficient input is now honest: `scalarHess_cont` and
  `nablaRicci_cont` supply the joint scalar-Hessian and covariant-Ricci tensor
  families, while `lRegJacCLM_cont` reconstructs the geometric velocity from
  its fixed-chart coordinate and proves operator-norm continuity without
  unfolding tensor or Hom representations.  The two generic regularity
  producers and the uniqueness module pass focused verification; the new
  exported modules have the targeted refreshes needed by their consumers.

  `LGeometry/Conjugate.lean` is also focused-green and warning-free.  `IsLConj`
  includes positive `lExp`-domain membership, so the totalized off-domain value
  cannot create artificial conjugate points.  `isLConj_iff` and
  `isLConj_iff_jac` give the kernel and regularized-Jacobi characterizations;
  `lExpDeriv_inj` and `lExpDeriv_surj` give the finite-dimensional
  nonconjugate differential consequences.

  The exact next theorem is `lRegIndex_balance` in a new `RegIndex.lean`.
  Define the square-root-time index density so that

  ```text
  d/ds <D_s Y,W> = 2 K_s(Y,W) + lRegJacobiPair(Y,W).
  ```

  This removes the positive-lower-endpoint restriction from the Green identity
  and permits a genuine endpoint at `s = 0`.  The subsequent bridge to the
  ordinary `lIndex` must prove the change of variables only almost everywhere:
  the pointwise density identity need not hold at `s = 0`.  Do not claim index
  positivity by adding a supplied semidefiniteness hypothesis; its remaining
  input is the native L-minimizer and field-realization layer.

  Honest progress: `redVolume_anti` **0%**; `lRegJacobi_unique` **100%**;
  the conjugacy definition/characterization brick **100%**; the broader L4
  phase about **78--82%**; dedicated L-geometry machinery about **52--56%**;
  reusable generic prerequisites about **90--93%**; P2 as a whole remains below
  **1%**.  The whole Poincare program estimate remains **3--5%**.

- 2026-08-22 (L4 endpoint-zero regularized index): `Jacobi.lean` now exposes
  `lRegJacobi_dyn_eq`, the residual-preserving moving-velocity identity; the
  original `lRegJacobi_dyn` is its Jacobi-zero corollary, so the connection
  calculus is not duplicated.  The refactored module is focused-green and its
  exported artifact is refreshed.

  The new `LGeometry/RegIndex.lean` is focused-green and warning-free.  It
  defines `lRegIndexInt` and `lRegIndex`, proves pointwise and integral
  symmetry, and establishes

  ```text
  d/ds <D_s Y,W> = 2 lRegIndexInt(Y,W) + lRegJacobiPair(Y,W).
  ```

  Consequently `lRegIndex_green` is valid on oriented intervals whose endpoint
  may be `s = 0`; `lRegIndex_zero_ends` and `lRegIndex_jacobi` give the
  fixed-endpoint and Jacobi boundary forms.  `lRegIndexInt_sq` identifies the
  positive-time density under `tau = s^2`, while `lIndex_sq` proves the
  interval identity by an almost-everywhere congruence that removes only the
  singleton `s = 0`.  No false pointwise equality at zero is stated.  The
  terminal L-geometry umbrella checks against the targeted `RegIndex` export.

  The exact next theorem is `lRegAction_second` in a new `RegAction.lean`.
  Define the direct regularized Lagrangian and action on a raw regularized
  curve, prove the first-variation formula, and then show that a smooth
  fixed-endpoint regularized variation about an `IsLRegCurveOn` central curve
  has second derivative `2 * lRegIndex Y Y`.  Produce compact domination and
  integrability internally; do not pass through an epsilon-to-zero limit and
  do not add a supplied semidefiniteness or minimizer assumption.

  Honest progress: `redVolume_anti` **0%**; the regularized index/Green/square
  bridge **100%**; the broader L4 phase about **82--85%**; dedicated L-geometry
  machinery about **55--59%**; reusable generic prerequisites about
  **90--93%**; P2 as a whole remains below **1%**.  The whole Poincare program
  estimate remains **3--5%**.

- 2026-08-22 (L4 endpoint-zero regularized action): the new
  `LGeometry/RegAction.lean` defines the direct square-root-time Lagrangian
  `lRegLag` and action `lRegAction`.  `lRegDensity_eq` and `lLength_reg`
  identify them with the earlier square-reparameterized density and ordinary
  L-length.  `lRegLag_deriv`, `lRegAction_deriv`, `lRegEuler_var_c1`, and
  `lRegAction_first` provide the pointwise, integral, regularity, and
  integration-by-parts first-variation layers with compact domination
  produced internally.

  The capstone `lRegAction_second` is focused-green and exported through the
  public L-geometry umbrella.  For a supplied smooth fixed-endpoint variation
  about an `IsLRegCurveOn` central curve it proves that the second derivative
  of regularized action is `2 * lRegIndex Y Y`.  The interval may have an
  endpoint at `s = 0`.  Jacobi integrability comes from the joint Euler
  regularity and `lRegEuler_deriv`; index-density integrability is proved
  internally from the independent metric/curve-time `C^2` theorem
  `lVarMetric_c2`, `inner_deriv_at`, and `lRegIndex_balance`.  No epsilon limit,
  supplied domination, minimizer wrapper, or semidefiniteness hypothesis was
  introduced.  Focused checks, the targeted `RegAction` export, and the
  import-only umbrella check all pass without warnings.

  The exact next theorem is `lRegIndex_nonneg_var` in a new
  `LGeometry/Minimizer.lean`: an actual smooth fixed-endpoint variation whose
  regularized action has a local minimum at the central parameter has
  nonnegative diagonal `lRegIndex`.  It should be a direct consequence of
  `lRegAction_deriv`, `lRegAction_second`, and the native real-calculus theorem
  `second_deriv_nonneg_of_isLocalMin`, not a supplied semidefinite wrapper.
  The following producer is the generic fixed-endpoint field-realization
  theorem needed to apply this result to an arbitrary smooth field; the
  existing complete-metric exponential producer is mathematically stronger
  than necessary, so the local ordinary-exponential route is being checked in
  the generic variation layer before adding L-specific assumptions.

  Honest progress: `redVolume_anti` **0%**; the regularized action/second-
  variation brick **100%**; the broader L4 phase about **86--89%**; dedicated
  L-geometry machinery about **58--62%**; reusable generic prerequisites about
  **90--93%**; P2 as a whole remains below **1%**.  The whole Poincare program
  estimate remains **3--5%**.

- 2026-08-22 (L4 variation-level index nonnegativity and field-realization
  blocker): the new `LGeometry/Minimizer.lean` proves the warning-free,
  exported theorem `lRegIndex_nonneg_var`.  Its hypothesis is an actual
  `IsLocalMin` statement for regularized action along a supplied smooth
  fixed-endpoint variation.  `lRegAction_deriv` supplies differentiability,
  the local-minimum derivative test gives the zero first derivative,
  `lRegAction_second` gives `2 * lRegIndex`, and
  `second_deriv_nonneg_of_isLocalMin` gives the sign.  No minimizer predicate,
  semidefinite wrapper, or desired-sign assumption was introduced.

  Extending this result to every smooth zero-endpoint field reached an honest
  missing-groundwork stop after three distinct native routes were checked.
  The ordinary `expMap` API is smooth only for a fixed base point; the local
  addition API currently needs compactness; and `exists_chartVar` handles only
  fields supported in one manifold chart.  The smallest reusable missing
  theorem is `total_exp_smooth_at` in the ordinary exponential smoothness
  layer: joint smoothness of

  ```text
  u : TangentBundle I M |-> expMap g u.proj u.snd
  ```

  at every zero vector, under local finite-dimensional manifold assumptions
  and without `CompleteSpace M`, `PseudoEMetricSpace M`, or an `IsMetricNorm`
  consumer hypothesis.  Its proof must add the varying-base
  chart-flow/`maximalGeodesic` identification missing beneath the existing
  `exists_chartExp_jointContDiffOn_nat`.  After it, the exact next producer is
  `exists_var_fix_ends` in the generic variation layer, followed by the
  arbitrary-field L-theorem `lRegIndex_nonneg`.

  Compact-manifold existence of an actual L-minimizer remains a separate
  global frontier: the current tree lacks manifold-valued weak `H^1`
  compactness, lower semicontinuity for the time-dependent kinetic action, and
  the Tonelli regularity upgrade.  This infrastructure is not hidden behind a
  supplied minimizer-existence theorem.

  Honest progress: `redVolume_anti` **0%**;
  `lRegIndex_nonneg_var` **100%**; arbitrary-field `lRegIndex_nonneg` **0%**;
  `total_exp_smooth_at` **0%**; the dedicated field-realization construction
  above that API is about **65--70%** understood but unproved; the broader L4
  phase is about **88--90%**; dedicated L-geometry machinery about
  **59--63%**; reusable generic prerequisites about **90--93%**; P2 remains
  below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-22 (L4 arbitrary-field index nonnegativity): the ordinary total
  exponential route was discarded because preferred charts do not give the
  required varying-base smoothness statement on an arbitrary charted
  manifold.  The replacement is fully local and checked.  The generic theorem
  `exists_var_fix_ends` cuts off the smooth geodesic vector field on the total
  tangent bundle near the compact image of the prescribed field, takes its
  complete compact-support flow, and projects that flow to the manifold.  It
  realizes every globally `C^8` field on `uIcc a b` and fixes both endpoints
  when the field vanishes there.  No `CompleteSpace M`, `PseudoEMetricSpace M`,
  `IsMetricNorm`, local-addition wrapper, or ordinary exponential smoothness
  hypothesis was added.

  The reusable `lRegIndex_congr` theorem transports both fields and their
  covariant derivatives on `uIoo a b`, then removes the remaining endpoint by
  an almost-everywhere interval-integral congruence.  This avoids the false
  inference that equality on a closed interval determines the two endpoint
  derivatives.  The new `lRegIndex_nonneg` combines this theorem with
  `exists_var_fix_ends` and `lRegIndex_nonneg_var`.  Its hypothesis is the
  honest statement that the central curve locally minimizes regularized action
  along every smooth fixed-endpoint variation; it does not assume the desired
  index sign.  Focused checks pass without warnings, and the generic
  field-realization export and `RegIndex` export are green.

  The exact next declaration is `sqrtReparam` in `LGeometry/Reparam.lean`,
  followed by `lLength_sqrt` in `LGeometry/RegAction.lean`.  The latter must use
  an almost-everywhere inverse square-root change of variables and discard the
  singleton backward-time endpoint; it must not require the raw curve to be
  differentiable at `tau = 0`.  Compact existence of an L-minimizer remains a
  separate direct-method frontier after this bridge.

  Honest progress: `redVolume_anti` **0%**; `lRegIndex_nonneg_var` **100%**;
  arbitrary-field `lRegIndex_nonneg` **100%**; generic fixed-endpoint field
  realization **100%**; the broader L4 phase **100%**; dedicated L-geometry
  machinery about **62--66%**; reusable generic prerequisites about
  **94--96%**.  `exists_lMinimizer` remains **0%**, with its dedicated
  direct-method machinery about **0--5%**.  P2 remains below **1%** and the
  whole Poincare program remains **3--5%**.

- 2026-08-22 (L5 inverse square-root action bridge): `sqrtReparam` now reads a
  regularized curve as a raw backward-time curve.  The positive-time identity
  `lDensity_sq_pos` uses the totalized manifold derivative and therefore holds
  for every raw curve, including the nondifferentiable branch.  The oriented
  integral theorem `lLength_sq_ae` removes the only possible exceptional point
  `s = 0` by an almost-everywhere congruence, so it requires no curve
  differentiability hypotheses.

  In the direct action layer, `lRegAction_congr` proves congruence from curve
  equality on `uIoo a b`; derivative equality is obtained only on genuine
  neighborhoods inside that open interval, and the endpoints are discarded by
  the interval measure.  `lLength_reg_ae` and the capstone `lLength_sqrt` then
  prove

  ```text
  lLength S T (sqrtReparam alpha) 0 tau
    = lRegAction S T alpha 0 (sqrt tau)
  ```

  for every `alpha` and `0 <= tau`.  In particular, the theorem does not demand
  differentiability of the singular raw curve at backward time zero.  Focused
  checks and the targeted `Reparam` and `RegAction` exports pass without
  warnings; an independent read-only audit confirmed both orientations and the
  degenerate interval `tau = 0`.

  This completes the executable inverse-reparameterization stage.  The next L5
  theorem endpoint is `exists_lMinimizer`, but it remains an honest direct-
  method blocker rather than a theorem to wrap with assumptions.  The current
  tree has no canonical manifold-valued absolutely-continuous/weak `H^1` path
  space, weak derivative subsequence extraction, lower semicontinuity theorem
  for the time-dependent metric action, or Tonelli regularity upgrade.  The
  admissible-path category must be chosen together with that API; no temporary
  `IsLAdmissible` or minimizer-existence wrapper is added here.

  Honest progress: `redVolume_anti` **0%**; inverse square-root action bridge
  **100%**; `lRegIndex_nonneg` **100%**; `exists_lMinimizer` **0%**, with its
  dedicated direct-method machinery about **0--5%**; dedicated L-geometry
  machinery about **64--68%**; reusable generic prerequisites about
  **94--96%**.  P2 remains below **1%** and the whole Poincare program remains
  **3--5%**.

- 2026-08-22 (L5 coercivity, C0 compactness, and first H1 realization): the
  direct-method preparation is now implemented through the full bounded-action
  C0 subsequence stage.  `metric_lower_icc` supplies one positive moving-metric
  coercivity constant on the compact spacetime slab.  `lScalar_lower`,
  `lAction_consts`, `lRefEnergy_bound`, and `lEdistOf_bound` turn one action
  bound into one family-wide fixed-reference energy budget and intrinsic
  square-root distance modulus, without assuming scalar curvature is
  nonnegative.  The reusable fixed-metric producers are `curveEnergy_mono` and
  `edistOf_le_budget`; `dist_lt_of_riedist` transfers the intrinsic modulus to
  any compatible compact-manifold pseudometric.

  `arzela_subseq_cpt` is the generic supplied-compact-target Arzela--Ascoli
  extraction theorem.  The L-specific capstone `lAction_subseq` applies it to
  every uniformly action-bounded sequence of regularized curves, and
  `lAction_subseq_fix` proves that two common endpoints survive in the C0
  limit.  All constants are chosen before the curve/sequence quantifier; no
  curvewise constants are silently reused as uniform data.

  The earlier claim that all AC/H1 and lower-semicontinuity infrastructure was
  absent was too broad.  The generic tree already had metric-valued absolute
  continuity and vector-valued `timeH1`.  This stage adds
  `timeH1.compact_subseq`, the genuine WeakSpace theorem
  `timeQuad_weak_lsc`, and the adapters `timeH1.ofContDiffOn`,
  `timeH1.toFun_ofContDiffOn`, and `timeH1.deriv_ofContDiffOn`.
  `chartCoord_contDiff`, `chartTimeH1`, `chartTimeH1_toFun`, and
  `chartTimeH1_deriv` then realize a C1 manifold curve whose image stays in one
  fixed chart as a coordinate-valued time-H1 path.  These generic and
  single-chart modules are focused-green without warnings or placeholders;
  required targeted exports and the L-geometry umbrella check are also green.

  The remaining stop is now precise.  There is no chart-independent
  manifold-valued weak H1 realization: finite chart localization and a weak
  chain rule on chart overlaps must identify the local weak derivatives before
  they can be compared with `lVelocity`.  The next reusable producer is an
  overlap theorem such as `chartH1_overlap`, followed by stability/lower
  semicontinuity for the curve-dependent moving-metric coefficient and
  continuity of the scalar potential integral.  A separate Tonelli/
  Euler--Lagrange regularity upgrade is then needed.  Stating
  `exists_lMinimizer` now would require choosing a new foundational path object
  or hiding these facts behind consumer assumptions, both forbidden in this
  lane.

  Honest progress: `redVolume_anti` **0%**; `exists_lMinimizer` **0%**;
  bounded-action C0 subsequence stage **100%**; fixed-chart C1-to-H1 producer
  **100%**; chart-independent manifold H1 realization about **10--15%**;
  dedicated direct-method machinery about **35--45%**; dedicated L-geometry
  machinery about **68--72%**; reusable generic prerequisites about
  **97--99%**.  P2 remains below **1%** and the whole Poincare program remains
  **3--5%**.
