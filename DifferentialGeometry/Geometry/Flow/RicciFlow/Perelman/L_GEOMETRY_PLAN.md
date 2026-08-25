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

- 2026-08-22 (L5 weak chart-overlap chain rule): the generic theorem
  `timeH1.chain_ae` now identifies weak derivatives whenever two existing
  time-H1 representatives agree through a map on the closed time interval and
  a relative Frechet derivative is supplied along the first representative.
  It deliberately does not claim to construct nonlinear compositions in
  `timeH1`; that stronger Nemytskii/FTC theorem is unnecessary for comparing
  separately extracted chart limits.

  `chartH1_overlap` applies this producer to two time-H1 coordinate
  representatives of the same manifold curve. Its conclusion uses
  `tangentCoordChange`, hence it works under only `IsManifold I 1 M` and does
  not require a boundaryless model, finite dimensionality, compactness, a
  metric, or C1 regularity of the underlying curve. The canonical C1
  realizations are covered by `chartH1_overlap_c1`. Both modules are
  focused-green without warnings or placeholders.

  Weak derivative compatibility on an overlap is therefore no longer the L5
  blocker. The next exact generic theorem is `timeOp_weak_lim`: stability of a
  bounded time-dependent continuous-linear coefficient acting on a weakly
  convergent `timeL2` sequence when the coefficients converge uniformly in
  operator norm. In parallel, the next geometric producer is finite
  time-chart localization for the compact C0 limit image; neither step should
  introduce a new manifold-H1 foundational object. Moving-metric quadratic
  lower semicontinuity, scalar-potential continuity, and the separate Tonelli/
  Euler--Lagrange regularity upgrade remain after those producers.

  Honest progress: `redVolume_anti` **0%**; `exists_lMinimizer` **0%**;
  bounded-action C0 subsequence stage **100%**; fixed-chart C1-to-H1 producer
  **100%**; weak chart-overlap identification **100%**; chart-independent
  manifold H1 realization about **25--35%**; dedicated direct-method machinery
  about **40--50%**; dedicated L-geometry machinery about **69--73%**;
  reusable generic prerequisites about **98--99%**. P2 remains below **1%**
  and the whole Poincare program remains **3--5%**.

- 2026-08-22 (L5 coefficient weak limits and finite chart split):
  `timeOp_weak_lim` proves that uniformly essentially bounded
  operator-valued coefficients converging uniformly in essential operator norm
  preserve weak convergence of time-L2 inputs. The theorem derives the needed
  uniform input norm bound from weak convergence by Banach--Steinhaus instead
  of adding it as a consumer hypothesis. Its proof combines the existing
  `timeOp` norm bound, a strongly vanishing coefficient-error term, and the
  adjoint test for the fixed limiting operator.

  The pure topological producer `exists_chart_split` gives every continuous
  compact-interval curve an eventually finite monotone subdivision whose
  closed pieces each lie in one preferred chart source. It requires only a
  `ChartedSpace`, interval nonemptiness, and `ContinuousOn`; the implementation
  does not import the existing heavy parallel-transport theorem with unrelated
  finite-dimensional smooth-manifold context. Both new modules are
  focused-green without warnings or placeholders.

  The next exact generic stage is the local interval API in
  `TimeH1Slice.lean`: construct a time-H1 slice on `[a,b]`, identify its
  continuous representative with `t |-> u.toFun (a+t)`, and identify its weak
  derivative with the translated original derivative almost everywhere. This
  will let `exists_chart_split` feed finitely many local H1 extractions and the
  already proved `chartH1_overlap`. After slicing, the next analytic theorem is
  moving-coefficient quadratic lower semicontinuity; scalar-potential
  continuity and the separate Tonelli/Euler--Lagrange regularity upgrade still
  remain.

  Honest progress: `redVolume_anti` **0%**; `exists_lMinimizer` **0%**;
  finite chart subdivision **100%**; weak coefficient-product stability
  **100%**; chart-independent manifold H1 realization about **35--45%**;
  dedicated direct-method machinery about **45--55%**; dedicated L-geometry
  machinery about **70--74%**; reusable generic prerequisites about **99%**.
  P2 remains below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (L5 finite-chart compactness and raw-action lower
  semicontinuity): the local and finite direct-method chain is now checked end
  to end. `TimeH1Slice.lean` supplies translated restrictions;
  `TimeOperatorWeak.lean` and `TimeQuadraticWeak.lean` pass weak convergence
  through uniformly convergent moving coefficients; and the finite-family
  theorem `timeH1.compact_subseq_fin` extracts one common subsequence. The
  generic finite chart producer `exists_cpt_split` also records compact chart
  buffers, not merely chart-source membership.

  `MetricFamilyGram.lean`, `MetricFamilyGramWeak.lean`,
  `ScalarCompact.lean`, and `KineticChart.lean` realize the moving kinetic and
  scalar terms with the correct forward time `T - s^2`. `ActionFinite.lean`
  turns the global C0 limit into finitely many canonical local `timeH1`
  representatives and extracts their weak derivatives simultaneously.
  `lRegAction_fin_lsc` then proves finite generalized chart-action lower
  semicontinuity. None of these theorems assumes scalar-curvature
  nonnegativity; the scalar term is controlled by compact continuity.

  The new generic bridge `curve_mdiff_local` proves that a curve represented
  by a fixed-chart `timeH1` path is manifold differentiable almost everywhere
  on the represented interval. It uses the chart inverse only within
  `range I`, so it does not add `I.Boundaryless`. Consequently
  `lRegAction_chart` identifies the finite generalized chart expression
  exactly with the raw manifold `lRegAction`. The terminal theorem
  `lAction_liminf` now gives a fixed-endpoint uniformly convergent subsequence
  and the honest inequality

  ```text
  lRegAction S T gamma a b
    <= liminf (fun n => lRegAction S T (alpha (chi n)) a b) atTop.
  ```

  Focused checks of the new producers, explicit targeted refreshes of exported
  modules, and the public `LGeometry.lean` umbrella check are green without
  warnings or placeholders. The endpoint is still not
  `exists_lMinimizer`: `exists_seq_tendsto_sInf` already handles the elementary
  minimizing-sequence bookkeeping, but the extracted local chart-H1 curve is
  not yet known to lie in the closure of the fixed-endpoint C1 competitor
  class with convergence of the action.

  The exact next generic/geometric producer is `lAction_c1_dense` in a new
  `ActionDensity.lean`. Its input should be the finite chart-H1 realization
  used by `lRegAction_chart`; its output should be fixed-endpoint C1 curves
  converging uniformly to `gamma`, strongly in the local H1 derivatives, and
  with `lRegAction` converging to `lRegAction S T gamma a b`. Three existing
  routes do not supply this statement: Mathlib manifold smooth approximation
  controls only C0 error, the current vector-valued `timeH1` API has no
  endpoint-preserving smooth-density/gluing theorem, and local L-ODE/
  `lExp` existence gives neither global endpoint shooting nor action
  minimality. Adding a new manifold-H1 foundational object or an admissibility
  wrapper would only hide this density theorem and remains forbidden. After
  density, a separate Tonelli/Euler--Lagrange regularity theorem must upgrade
  the relaxed minimizer to an `IsLRegCurveOn` curve.

  Honest progress: `redVolume_anti` **0%**; `exists_lMinimizer` **0%**;
  `lAction_liminf` and the finite-chart raw-action lower-semicontinuity stage
  **100%**; `lAction_c1_dense` **0%**; the Tonelli regularity producer **0%**;
  dedicated minimizer/direct-method machinery about **72--78%**; dedicated
  L-geometry machinery about **73--77%**. Reused generic compactness and weak
  L2 infrastructure for the completed stage is **100%**, while the new generic
  endpoint-preserving H1 density producer is **0%**. P2 remains below **1%**
  and the whole Poincare program remains **3--5%**.

- 2026-08-23 (L5 fixed-endpoint action recovery and first Tonelli bricks):
  the recovery side of the finite-chart direct method is now checked end to
  end. `TimeH1Flat.lean` proves `exists_flat_deriv`, strong approximation of a
  time-L2 derivative by a globally smooth function supported inside the open
  time interval. `TimeH1Density.lean` upgrades this to `exists_flat_dense`:
  global C1 curves with exact endpoint traces, constant germs at both
  endpoints, exact `timeH1` realization, strong H1 convergence, and strong
  derivative convergence. The proof corrects the derivative integral by a
  normalized interior bump; it does not infer endpoint flatness merely from
  pointwise support containment.

  `ActionDensityGeom.lean` supplies `exists_c1_of_flat`, including repeated
  nodes, zero-length pieces, and the empty subdivision. `ActionDensity.lean`
  constructs compact chart buffers internally, chooses one common tail over
  the finite chart family, and proves the terminal recovery theorem
  `lAction_c1_dense`. Its fixed-endpoint global C1 approximants converge
  strongly in each local chart-H1 space, uniformly as manifold curves, and in
  the complete regularized L-action. The public theorem exposes neither
  buffer choices nor stronger consumer assumptions. The focused checks,
  targeted exports, and public `LGeometry.lean` umbrella check are green
  without warnings or placeholders.

  The first genuine Tonelli bricks are also checked. `timeQuad_weak_euler`
  derives a weak Euler identity from an actual fixed-endpoint local minimizer;
  `mom_primitive` and `mom_rep_cont` turn that identity into an almost-
  everywhere momentum primitive with a continuous representative.
  `chartGramOp_unit` derives invertibility of the chart Gram operator from its
  existing metric coercivity, and `chartGramInv_cont` proves continuity of the
  inverse family on every regular chart-coordinate set. None of these results
  assumes a supplied inverse, momentum equation, or desired regularity.  The
  current momentum theorem uses an L2 force.  For the genuinely nonlinear
  chart action the position derivative contains a coefficient times
  `|u'|^2`, which is only L1 at the initial H1 regularity level; the L2 theorem
  is therefore a checked specialization, not yet the final Tonelli interface.

  The first nonlinear geometric and natural-exponent bridges are now checked.
  `ActionEuler.lean` defines `lChartLag` and `lChartAct` with the actual Gram
  and scalar coefficients evaluated along `u.toFun`, and `lRegAction_stat`
  derives stationarity of the full regularized action from an actual smooth
  fixed-endpoint local minimum.  It does not freeze the metric coefficient or
  assume the first variation.  `TimeQuadraticRegularL1.lean` proves
  `mom_primitive_l1` and `mom_rep_cont_l1`: a raw force merely integrable on
  the closed interval gives an almost-everywhere momentum primitive and a
  continuous representative.  `ActionVelocity.lean` proves `chartGram_time`,
  `chartVel_of_mom`, and `chartVel_rep_cont`; these derive the coefficient
  bound and inverse from the native metric family and turn that L1 momentum
  representative into a continuous coordinate-velocity representative.

  The full chart-H1 theorem `lChart_weak_euler` remains unstated and unproved.
  Its exact missing generic prerequisite is `timeH1_nl_deriv` in a nonlinear
  time-action module: for a curve-dependent quadratic coefficient and scalar
  potential with compact-buffer C1 bounds, differentiate the integral action
  on `timeH1`, prove that the position derivative is an actual `IntegrableOn`
  force, and derive the zero-endpoint weak Euler identity from an actual local
  minimum.  Three existing routes do not close this bridge: the fixed-
  coefficient `timeQuad_weak_euler` has the wrong nonlinear interface; the
  smooth geometric first variation now recorded by `lRegAction_stat` does not
  apply to an H1 base curve; and pointwise smoothness of `chartGramOp` does not
  by itself provide the needed Nemytskii/integral Frechet derivative into the
  H1 dual.  No L2 force, supplied Euler equation, or desired regularity may be
  added as a consumer hypothesis.  After this generic producer,
  `lChart_weak_euler` can feed the already checked L1 momentum and inverse
  chain; a later geometric identification gives `isLRegCurve_of_min`.

  Honest progress: `redVolume_anti` **0%**; `exists_lMinimizer` **0%**;
  `lAction_c1_dense` and its dedicated density machinery **100%**;
  `lAction_liminf` and raw-action lower semicontinuity **100%**; smooth
  nonlinear stationarity **100%**; the L1 momentum and momentum-to-velocity
  bridges **100%**.  The full nonlinear chart-H1 weak Euler theorem and the
  terminal Tonelli regularity theorem remain **0%**; their checked dedicated
  generic machinery is about **75--85%**, with the nonlinear H1 first-
  variation theorem still a substantial missing API rather than a local proof.
  Dedicated minimizer/direct-method machinery is about **84--89%** and
  dedicated L-geometry machinery about **78--82%**. Reused generic
  compactness, weak-L2, and endpoint-density infrastructure needed by the
  completed recovery stage is **100%**. P2 remains below **1%** and the whole
  Poincare program remains **3--5%**.

- 2026-08-23 (L5 relaxed attainment, Tonelli producers, and exact
  elaboration frontier): the fixed-endpoint direct method now attains its
  relaxed endpoint. `ActionAttain.lean` proves `exists_lRegMinC1`: a
  continuous finite-chart-H1 curve attains the infimum of the global C1
  actions and satisfies the genuine global C1 competitor inequality.
  `ActionSplice.lean` and `ActionLocalMin.lean` then prove
  `lChartAct_local`, transferring that inequality to an actual local minimum
  of every positive fixed-endpoint chart segment. These theorems do not assume
  stationarity or an Euler equation.

  The native Tonelli producer chain is checked through the point immediately
  after a weak Euler identity. `primitive_c1` and `mom_rep_c1` upgrade a
  continuous force to a C1 momentum representative. `chartGramInv_smooth`
  derives the jointly smooth Gram inverse from the native metric family.
  `chartVel_rep_c1` converts the momentum representative to a C1 velocity
  representative. `chartScalFun_smooth` and `chartScalCov_smooth` expose the
  whole chart scalar value and spatial covector without finite-coordinate
  reconstruction. `lChartForceRep_cont` and `lChartForceRep_ae` give the
  continuous representative of the actual L-force. Finally,
  `lChartVel_c1` is a verified C1-to-C2 bootstrap from the actual interval
  weak identity; it does not take a supplied force equation or inverse.

  The shared-node recovery infrastructure is also checked independently.
  `contDiffOn_Icc_join` glues adjacent closed-interval C1 pieces with matching
  one-sided derivatives. `timeH1.tent` supplies the exact `0,z,0` H1 node
  test, and `exists_tent_c1` approximates it by closed-interval C1 curves with
  exact outer endpoints and exact node value, strongly both in `timeH1` and
  in the derivative `timeL2` norm. `lNode_c1_dense` realizes two compatible
  chart-H1 pieces as one continuous shared-node curve and produces global C1
  competitors converging strongly in both pieces, uniformly on the manifold,
  and in the full regularized L-action. Repeated subdivision nodes are allowed.

  The remaining Tonelli theorem is blocked at an exact verification boundary,
  not hidden behind a new assumption. `ActionWeakEuler.lean` contains the
  source statements `lChartAct_line` and `lChart_weak_euler`, but a focused
  check deterministically exhausts 200000 heartbeats while reducing the
  minimal private producer

  ```text
  lWeakScal_cont :
    ContinuousOn
      (fun q => lWeakScal ... q.2
        (u.toFun q.2 + q.1 • v.toFun q.2))
      (Icc (-1) 1 ×ˢ Icc 0 L).
  ```

  This final route uses the checked public `chartScalFun_smooth` directly and
  passes joint lag continuity to the generic dominated-integral argument,
  which derives every parameter slice's interval integrability internally.
  Explicitly omitting the unused positive-finrank, boundaryless, and
  sigma-compact section instances from this declaration leaves the same
  deterministic timeout.
  Earlier genuinely different routes through coordinatewise scalar
  covectors, a whole scalar covector followed by a separate shifted
  integrability producer, and an isolated translated `lScalar_int` theorem
  reached the same deterministic `whnf` performance boundary. The whole-Hom
  topology issue is no longer present: the Gram derivative is fully evaluated
  on two velocities and bounded on a compact product of unit balls.

  `ActionRegular.lean` contains the source-only theorem `lChart_min_c1`, with
  the actual local-minimum input and no supplied Euler or regularity
  hypothesis, but it was intentionally not checked because its
  `ActionWeakEuler` import is not green. Neither red source module is imported
  by the public `LGeometry.lean` umbrella. All verified attainment, force,
  velocity, bootstrap, local-minimum, and shared-node recovery modules are
  imported there; the focused umbrella check is green after the one genuinely
  required targeted refresh of `ActionNodeSplice`.

  The exact next verification target remains `lWeakScal_cont` in
  `ActionWeakEuler.lean`. Once its elaboration performance is resolved, the
  concrete checked sequence is `lChart_weak_euler`, `lChart_min_c1`, and then
  the Weierstrass--Erdmann node equation `lNode_mom_match`; the last theorem
  must use the checked shared-node C1 recovery and must not assume momentum
  matching or introduce a cotangent-transition wrapper.

  Honest progress: `redVolume_anti` **0%**; terminal regular
  `exists_lMinimizer` **0%**; relaxed `exists_lRegMinC1` **100%**;
  fixed-endpoint local chart-minimum transfer **100%**; raw direct method and
  fixed-endpoint C1 recovery **100%**; generic C1 momentum/velocity,
  continuous-force, C1-to-C2, and shared-node test/recovery producers for their
  stated interfaces **100%**. `lChart_weak_euler`, `lChart_min_c1`, and
  `lNode_mom_match` are each **0% verified**; their dedicated source and
  supporting machinery is about **92--95%**, **90--93%**, and **90%**
  respectively. Dedicated minimizer/direct-method machinery is about
  **94--96%**, while dedicated L-geometry machinery is about **85--87%**.
  Reused generic infrastructure for the completed bricks is **100%**. P2
  remains below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (weak Euler green, fixed-chart C1/momentum green, node corner
  execution): the previous elaboration frontier is closed.  The scalar
  space-time term is now packaged through the existing subtype-continuity API,
  so `lChartAct_line` and `lChart_weak_euler` both pass focused verification
  without warnings.  `ActionRegular.lean` then proves the actual
  local-minimizer endpoint `lChart_min_c1`, and `ActionMomentum.lean` strengthens
  it to `lChart_mom_c1`: a closed-interval C1 momentum representative equal
  pointwise to twice the chart Gram operator applied to the continuous
  velocity, with derivative equal to twice the continuous chart force.
  Neither theorem takes a supplied Euler equation, inverse Gram operator, or
  desired regularity.

  The exact node-variation support is also green.  `TimeQuadraticBoundary.lean`
  evaluates the upward and downward affine ramp integrals as the terminal and
  negative initial momentum pairings.  `TimeH1Ramp.lean` realizes those ramps
  in `timeH1`; `TimeH1Buffer.lean` supplies a nonzero common scale whose whole
  affine unit tube stays in an open chart target.  `ChartTimeC1.lean` lifts a
  C1 fixed-chart representative back to a C1 manifold curve.
  `lNode_c1_dense` now exposes the constructed curve's chart containment and
  representation facts, and the verified theorem `lNodeAct_min` uses them to
  transfer the global fixed-endpoint C1 comparison to an exact two-piece chart
  action inequality.  This comparison assumes neither stationarity nor the
  corner equation.

  The current exact theorem is `lNode_mom_match`.  Its same-chart analytic core
  is being executed directly from `lNodeAct_min`, `lChartAct_line`,
  `lChart_mom_c1`, and the two ramp boundary identities.  The cross-chart
  assembly must then localize the right-hand head in the left node chart and
  cancel the unchanged tail; affine tents in the two original charts are not
  exact shared-node variations because the chart transition is nonlinear.
  No nonlinear endpoint-amplitude wrapper or cotangent-transition object will
  be introduced.

  Honest progress: `redVolume_anti` **0%**; terminal
  `exists_lMinimizer` **0%**; relaxed `exists_lRegMinC1` **100%**;
  `lChartAct_line`, `lChart_weak_euler`, `lChart_min_c1`, and
  `lChart_mom_c1` **100%**; shared-node density and two-piece action comparison
  **100%**; `lNode_mom_match` **0% until its public theorem is proved**.
  Dedicated node-match machinery is about **94--96%**; dedicated
  minimizer/direct-method machinery about **96--97%**; dedicated L-geometry
  machinery about **87--89%**.  Reused generic compactness, weak-L2, C1,
  ramp, and endpoint-density infrastructure needed here is **100%**.  P2
  remains below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (cross-chart node momentum match green): the public theorem
  `lNode_mom_match` is now focused-checked and its module refresh is green,
  without warnings or placeholders.  Starting only from the global
  fixed-endpoint C1 competitor inequality, it obtains exact two-piece action
  comparison, proves the right piece C1, rewrites a positive right-hand head
  in the left node chart, applies the checked same-chart corner theorem, and
  transports the resulting scalar Gram pairing back with
  `chartDeriv_head` and `chartGramOp_change`.  It assumes neither momentum
  matching nor curve regularity at the node.

  The next exact theorem is `lNode_vel_match`: cancel the positive-definite
  chart Gram operator from `lNode_mom_match` and prove that the two endpoint
  coordinate velocities are related by `tangentCoordChange`.  The proof must
  use the existing Gram-unit and coordinate-change composition APIs and must
  not introduce a cotangent-transition wrapper.  In parallel, the generic
  two-piece manifold C1 gluing producer is being checked at the TimeSobolev
  layer for the subsequent finite-node assembly.

  Honest progress: `redVolume_anti` **0%**; terminal
  `exists_lMinimizer` **0%**; `lNode_mom_match` **100%**;
  `lNode_vel_match` **0% until its public theorem is proved**.  Dedicated
  node-corner machinery is about **98--99%**; dedicated
  minimizer/direct-method machinery remains about **96--97%**; dedicated
  L-geometry machinery is about **89--91%**.  Reused generic infrastructure
  needed by the checked corner theorem is **100%**.  P2 remains below **1%**
  and the whole Poincare program remains **3--5%**.

- 2026-08-23 (node velocity match and generic C1 join green):
  `lNode_vel_match` is now focused-checked and refreshed without warnings or
  placeholders.  Under exactly the assumptions of `lNode_mom_match`, it uses
  coordinate-change composition, `chartGramOp_change`, and
  `chartGramOp_unit` to cancel the positive-definite Gram operator and prove
  that the right initial coordinate velocity is the tangent-coordinate
  transport of the left terminal coordinate velocity.

  The lower generic layer now also exports the checked theorem
  `curve_c1_join`.  Two positive adjacent pieces of the same manifold curve,
  C1 on their respective closed intervals and with matching one-sided
  derivatives in the node-centered chart, glue to a C1 curve on the whole
  interval.  It needs no finite-dimensionality, completeness, separation,
  compactness, or Ricci-flow assumptions and does not require one chart to
  contain both full pieces.

  The next exact theorem is `lNode_c1`: derive the C1 regularity of both
  positive L-action pieces from their local minimality, transport
  `lNode_vel_match` into the node-centered chart, and apply
  `curve_c1_join`.  Repeated or zero-length subdivision nodes remain a later
  compression step and are not silently included in this positive two-piece
  statement.

  Honest progress: `redVolume_anti` **0%**; terminal
  `exists_lMinimizer` **0%**; `lNode_mom_match` and `lNode_vel_match`
  **100%**; `lNode_c1` **0% until its public theorem is proved**.  Dedicated
  positive-node corner machinery is **100%**; dedicated
  minimizer/direct-method machinery remains about **96--97%**; dedicated
  L-geometry machinery is about **90--92%**.  The generic two-piece C1 join
  and other reused infrastructure needed here are **100%**.  P2 remains below
  **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (positive two-piece C1 regularity green): `lNode_c1` is now
  focused-checked and refreshed without warnings or placeholders.  From the
  same global fixed-endpoint C1 competitor inequality as the corner equation,
  it derives exact two-piece comparison, local minimality and chart C1 for
  each piece, translates the endpoint derivatives to global time, transports
  both into the node-centered chart, and applies `curve_c1_join` after
  `lNode_vel_match`.  Thus the positive two-piece minimizer is genuinely C1
  across its chart node; node regularity is a conclusion, not a hypothesis.

  The generic strict finite iteration `curve_c1_fin` is also checked and
  refreshed.  It strongly inducts over a bounded Nat-indexed subdivision,
  gluing the final segment after locally identifying the accumulated-left
  derivative with the previous-piece derivative.  This theorem deliberately
  excludes repeated nodes.

  The next exact L-geometry producer is arbitrary-window localization:
  transfer the global relaxed fixed-endpoint minimum to any adjacent positive
  two-piece window without assuming the baseline curve is already globally
  C1.  That producer will let `lNode_c1` run at every internal strict node;
  repeated/zero-length node compression remains the following separate step.

  Honest progress: `redVolume_anti` **0%**; terminal
  `exists_lMinimizer` **0%**; `lNode_mom_match`, `lNode_vel_match`, and
  positive two-piece `lNode_c1` **100%**.  Arbitrary-window localization is
  **0% until a public theorem is proved**.  Positive-node corner machinery
  and strict finite generic C1 gluing are **100%**; dedicated
  minimizer/direct-method machinery remains about **96--97%**; dedicated
  L-geometry machinery is about **91--93%**.  Reused generic infrastructure
  needed by the completed stages is **100%**.  P2 remains below **1%** and
  the whole Poincare program remains **3--5%**.

- 2026-08-23 (arbitrary positive-window comparison green):
  `lNodeWin_cmp` is focused-checked and refreshed without warnings or
  placeholders.  For any finite chart-H1 realization with at least two
  pieces, any selected adjacent positive pair, and any compatible pair of
  target-contained replacements, it embeds the replacements into the full
  dependent family, realizes the resulting continuous finite-H1 curve by
  global fixed-endpoint C1 curves, applies the genuine global minimum, and
  cancels every unchanged prefix and suffix action term.  The theorem is not
  tied to the original chart family, so it also applies after a short-head
  refinement of the right segment.

  The next exact producer is that caller-side refinement: insert a positive
  split point in one finite segment while preserving nodes, charts,
  dependent `timeH1` pieces, representations, and all unchanged complement
  data.  This will supply the common-chart left/head comparison needed by the
  already checked same-chart corner theorem at every internal node.  In
  parallel, subdivision compression is selecting all original positive
  segments while retaining their indices and exact endpoints.

  Honest progress: `redVolume_anti` **0%**; terminal
  `exists_lMinimizer` **0%**; `lNodeWin_cmp` **100%**; caller-side dependent
  refinement **0% until a public producer is proved**.  Arbitrary positive-
  window comparison machinery is about **98--99%**, with only the refinement
  consumer assembly remaining; dedicated L-geometry machinery is about
  **92--94%**.  Reused generic infrastructure remains **100%**.  P2 remains
  below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (witness-preserving subdivision compression green): the generic
  theorem `exists_strict_subdiv` is focused-checked and refreshed without
  warnings or placeholders.  From a monotone `Fin (m+1)` node family it
  filters the original positive segments, enumerates them in strict index
  order, and returns a strict compressed node family together with the
  original segment map.  Each compressed segment has exactly the endpoints
  of its recorded original segment, so dependent `lSegLen`, chart, and
  `timeH1` witnesses can be transported; the all-zero case correctly returns
  no segments.  Value-only list deduplication was rejected because it would
  lose those witnesses.

  The generic compression theorem is **100%**.  The next L-specific work is
  to transport the finite realization along its returned segment map and to
  combine that strict realization with `lNodeWin_cmp` and the short-head
  refinement adapter.  `redVolume_anti` and terminal `exists_lMinimizer`
  remain **0%**; dedicated L-geometry machinery remains about **92--94%**
  because this generic producer is not itself an L endpoint.  P2 remains
  below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (strict L-realization transport green): `exists_lStrict` is
  focused-checked and refreshed without warnings or placeholders.  It consumes
  `exists_strict_subdiv`, preserves the strictly increasing original positive-
  segment map, and transports the chart centers, dependent `timeH1` pieces,
  chart-source containment, and exact coordinate representatives to the
  compressed strict subdivision.  The public result needs no Ricci-flow,
  compactness, or smoothness assumptions.

  Generic subdivision compression and its L-specific realization transport are
  **100%**.  The next exact producer remains `lNodeRef_cmp`: split the selected
  right segment at a positive interior time and use `lNodeWin_cmp` to obtain the
  common-chart left/head comparison while preserving every untouched finite
  piece.  `redVolume_anti` and terminal `exists_lMinimizer` remain **0%**;
  dedicated L-geometry machinery is about **92--94%**; reused generic
  infrastructure is **100%**.  P2 remains below **1%** and the whole Poincare
  program remains **3--5%**.

- 2026-08-23 (finite right-head refinement green): `lNodeRef_cmp` is
  focused-checked and refreshed without warnings or placeholders.  At an
  arbitrary selected internal node it inserts a positive split point into the
  right segment, realizes the short head in the left chart, uses `timeH1.slice`
  for the old-chart tail, transports every dependent length witness, and
  preserves all unchanged pieces.  Applying `lNodeWin_cmp` to the refined
  realization gives the exact common-chart left/head action comparison.

  The caller-side finite refinement adapter is **100%**.  The next exact theorem
  is `lFinNode_vel`: combine this comparison with right-piece C1 regularity,
  `lNode_mom_same`, chart-head derivative transport, and Gram injectivity to
  prove velocity matching at any positive finite internal node.  Dedicated
  L-geometry machinery is about **93--95%**; reused generic infrastructure is
  **100%**.  `exists_lMinimizer` and `redVolume_anti` remain **0%**; P2 remains
  below **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (strict finite piece regularity green): `lStrict_piece_c1` is
  focused-checked and refreshed without warnings or placeholders.  For each
  segment of a strict finite realization it derives the actual fixed-endpoint
  local minimum from the global competitor inequality and concludes closed-
  interval C1 regularity through `lChart_min_c1`.  Strictness supplies exactly
  the positive length needed by the analytic theorem.

  Strict finite piecewise C1 regularity is **100%**.  The next exact theorem
  remains `lFinNode_vel`, followed by finite C1 gluing.  Dedicated L-geometry
  machinery is about **93--95%**; reused generic infrastructure is **100%**.
  `exists_lMinimizer` and `redVolume_anti` remain **0%**; P2 remains below
  **1%** and the whole Poincare program remains **3--5%**.

- 2026-08-23 (arbitrary finite-node velocity match green): `lFinNode_vel` is
  focused-checked and refreshed without warnings or placeholders.  Under only
  positivity of each realized piece, it proves C1 regularity for the selected
  right segment, extracts a short head in the left chart, applies
  `lNodeRef_cmp` and `lNode_mom_same`, transports the endpoint derivative
  through the chart transition, and cancels the native positive-definite Gram
  operator.  No strict-subdivision package or desired corner equation is an
  input.

  Arbitrary finite-node velocity matching is **100%**.  The next exact theorem
  is `lFinCurve_c1`: translate these coordinate endpoint equalities into the
  node-centered chart and combine them with strict piecewise regularity via
  `curve_c1_fin`.  Dedicated L-geometry machinery is about **94--96%**; reused
  generic infrastructure is **100%**.  `exists_lMinimizer` and
  `redVolume_anti` remain **0%**; P2 remains below **1%** and the whole
  Poincare program remains **3--5%**.

- 2026-08-23 (strict finite global C1 green): `lFinCurve_c1` is
  focused-checked and refreshed without warnings or placeholders.  Its
  canonical interface accepts any positive number of strict realized pieces.
  The single-piece case uses local chart regularity directly; the multiple-
  piece case converts `lFinNode_vel` at every internal node into equality in
  the node-centered chart and applies `curve_c1_fin`.

  Strict finite global C1 regularity is **100%**.  The next exact theorem is
  `lMinCurve_c1`: compress an arbitrary monotone realization with
  `exists_lStrict`, rule out the zero-piece case from `a < b`, and apply
  `lFinCurve_c1`.  Dedicated L-geometry machinery is about **94--96%**; reused
  generic infrastructure is **100%**.  `exists_lMinimizer` and
  `redVolume_anti` remain **0%**; P2 remains below **1%** and the whole
  Poincare program remains **3--5%**.

- 2026-08-23 (strict finite piece C2 green): `lStrict_piece_c2` is
  focused-checked and refreshed without warnings or placeholders.  On every
  positive strict piece it derives the genuine local minimum, obtains the
  continuous weak velocity and native weak Euler identity, applies
  `lChartVel_c1`, and uses the pointwise within-derivative identity to conclude
  `ContDiffOn Real 2` for the coordinate representative.  It assumes neither
  Euler nor C2 regularity.

  Strict finite piecewise C2 regularity is **100%**.  In parallel with the
  repeated-node/global-C1 consumer `lMinCurve_c1`, the next analytic audit is
  the genuine classical bridge from this chart Euler data to
  `covDerivAlong = lRegAccel`; no assumption-wrapped substitute will be added.
  Dedicated L-geometry machinery is about **95--96%**; reused generic
  infrastructure is **100%**.  `exists_lMinimizer` and `redVolume_anti` remain
  **0%**; P2 remains below **1%** and the whole Poincare program remains
  **3--5%**.

- 2026-08-23 (monotone finite minimizer C1 green): `lMinCurve_c1` is
  focused-checked and refreshed without warnings or placeholders.  It applies
  `exists_lStrict` to an arbitrary monotone finite realization, rules out the
  zero-piece compressed family from the strict global endpoint inequality
  `a < b`, and invokes `lFinCurve_c1`.  Repeated and zero-length chart pieces
  are therefore fully discharged before the global C1 conclusion.

  The repeated-node/global-C1 assembly is **100%**.  The next exact direct-
  method consumer is `exists_lRegMinC1On`, which hides the finite realization
  returned by `exists_lRegMinC1` and exposes the attained C1-on minimizer,
  endpoint values, exact cost equality, and genuine competitor inequality.
  Dedicated L-geometry machinery is about **95--97%**; reused generic
  infrastructure is **100%**.  `exists_lMinimizer` and `redVolume_anti` remain
  **0%**; P2 remains below **1%** and the whole Poincare program remains
  **3--5%**.

- 2026-08-23 (C1 relaxed minimizer attainment green):
  `exists_lRegMinC1On` is focused-checked and refreshed without warnings or
  placeholders.  It consumes `exists_lRegMinC1` and `lMinCurve_c1`, hides all
  finite chart-H1 and approximation witnesses, and returns a closed-interval
  C1 curve with prescribed endpoints, exact `lRegCostC1` equality, and the
  genuine global fixed-endpoint C1 competitor inequality.  It does not assert
  `IsLRegCurveOn`.  Its present signature inherits the positive-finrank
  instance from the node-regularity chain; the raw direct-method producer does
  not need that instance.

  C1 relaxed attainment is **100%**.  The exact analytic frontier is now the
  native `lChartEuler_iff` calculation converting the checked pointwise chart
  momentum equation into `covDerivAlong = lRegAccel`; after that, the minimizer
  can be identified with the regularized L-ODE on each positive piece.
  Dedicated L-geometry machinery is about **96--97%**; reused generic
  infrastructure is **100%**.  The terminal `exists_lMinimizer` and
  `redVolume_anti` remain **0%**; P2 remains below **1%** and the whole
  Poincare program remains **3--5%**.

- 2026-08-23 (classical fixed-chart Euler bridge green):
  `lChartEuler_iff` is focused-checked and refreshed without warnings or
  placeholders.  At a local chart parameter `r`, it uses the global
  square-root time `a + r` and proves the genuine equivalence between the
  differentiated chart momentum equation and the second component of
  `lPhaseField`.  The proof stays scalar after fully applying the Gram
  operator: `lRegInner_deriv` gives the moving-metric derivative,
  `chartGram_spatial` gives the spatial Gram--Christoffel identity,
  `lRegAccel_inner` gives the intrinsic acceleration pairing, and Gram
  invertibility recovers the model-space vector equation.  No Euler,
  acceleration, or smooth-solution conclusion is supplied as an assumption.

  The generic `chartGram_spatial` producer and the L-specific
  `lChartEuler_iff` bridge are **100%**.  The next exact theorem is
  `lChart_min_accel`: consume the momentum and C1 velocity representatives of
  an actual positive fixed-chart minimum, invoke `lChartEuler_iff` pointwise,
  and apply `lPhase_accel` to the shifted global phase
  `z(s) = (u.toFun (s - a), q (s - a))`.  The terminal
  `exists_lMinimizer` and `redVolume_anti` remain **0%**; dedicated L-geometry
  machinery remains about **96--97%**, reused generic infrastructure is
  **100%**, P2 remains below **1%**, and the whole Poincare program remains
  **3--5%**.

- 2026-08-23 (fixed-chart minimizer acceleration green):
  `lChart_min_accel` is focused-checked and refreshed without warnings or
  placeholders.  It derives C1 momentum and velocity representatives from a
  genuine positive fixed-chart local minimum, cancels the momentum factor,
  invokes `lChartEuler_iff`, and applies `lPhase_accel` to the correctly
  shifted phase.  It then identifies the phase velocity with the actual
  `lVelocity` on a neighborhood, so the public conclusion is the intrinsic
  `covDerivAlong = lRegAccel` equation at every interior parameter time.  No
  compactness, pseudometric, Euler equation, or acceleration equation is an
  input.

  The fixed-chart classical consumer is **100%**.  The next exact assembly is
  `lStrict_piece_accel`: derive the local minimum on every positive strict
  finite piece, apply `lChart_min_accel`, and transport the shifted inverse-
  chart curve back to the attained manifold curve.  In parallel the endpoint
  audit must determine the weakest native route extending the equation across
  subdivision nodes before claiming `IsLRegCurveOn`.  The terminal
  `exists_lMinimizer` and `redVolume_anti` remain **0%**; dedicated L-geometry
  machinery is about **97--98%**, reused generic infrastructure is **100%**,
  P2 remains below **1%**, and the whole Poincare program remains **3--5%**.

- 2026-08-23 (arbitrary-base phase existence green):
  `exists_lPhaseSol_at` is focused-checked and refreshed without warnings or
  placeholders.  At any regular square-root time `s0` and chart-interior phase
  state `z0`, it constructs the autonomized integral curve directly through
  `(s0,z0)` at parameter time `s0`; a generalized clock lemma then identifies
  the first component with actual time on a two-sided neighborhood.  No time
  translation is used, so the nonautonomous field retains the correct
  `T - s^2` dependence.

  Arbitrary-base phase existence is **100%**.  The next exact producer is
  `exists_lRegCurve_at`, reconstructing a genuine intrinsic local curve with
  prescribed position and velocity at `s0` and the full regularized solution
  triple.  That producer will support the endpoint patch after the internal-
  node regularity assembly.  The terminal `exists_lMinimizer` and
  `redVolume_anti` remain **0%**; dedicated L-geometry machinery is about
  **97--98%**, reused generic infrastructure is **100%**, P2 remains below
  **1%**, and the whole Poincare program remains **3--5%**.

- 2026-08-23 (strict finite open-piece acceleration green):
  `lStrict_piece_accel` is focused-checked and refreshed without warnings or
  placeholders.  It applies the fixed-chart minimizer theorem on every
  positive strict piece, identifies the shifted inverse-chart curve with the
  attained manifold curve as a germ through the exact representation witness,
  transports `lVelocity` by the native `mfderiv` germ congruence, and transports
  the covariant derivative with `covDerivAlong_congr_curve`.  Thus the actual
  attained curve satisfies `covDerivAlong = lRegAccel` at every point in every
  open piece; no equation or regularity conclusion is an input.

  Strict finite open-piece acceleration is **100%**.  The next exact frontier
  is the node/endpoint extension needed before asserting `IsLRegCurveOn` for
  the attained curve.  It must combine strict piecewise C2, global C1 node
  matching, and a native continuity or phase-ODE argument; it must not simply
  omit the finite nodes from a theorem whose set includes them.  The terminal
  `exists_lMinimizer` and `redVolume_anti` remain **0%**; dedicated L-geometry
  machinery is about **97--98%**, reused generic infrastructure is **100%**,
  P2 remains below **1%**, and the whole Poincare program remains **3--5%**.

- 2026-08-23 (arbitrary-base intrinsic regularized curve green):
  `exists_lRegCurve_at` is focused-checked and refreshed without warnings or
  placeholders.  From any regular square-root time `s0`, prescribed point
  `x`, and prescribed actual tangent velocity `A0`, it reconstructs the local
  phase solution as a manifold curve with `alpha s0 = x` and
  `lVelocity alpha s0 = A0`.  On a two-sided neighborhood it supplies the full
  local regularized triple: manifold differentiability, differentiability of
  the actual-velocity chart representative, and the intrinsic acceleration
  equation.  No regularized solution or Euler equation is an input.

  Arbitrary-base intrinsic regularized curve existence is **100%**.  The next
  exact theorem is `lFinNode_reg`: combine global finite C1 gluing with the two
  adjacent strict C2/acceleration pieces and a deleted-neighborhood derivative
  extension to obtain the full regularity triple at every internal node.  The
  endpoint patch will then use `exists_lRegCurve_at` on both sides of the
  closed minimizing interval.  The terminal `exists_lMinimizer` and
  `redVolume_anti` remain **0%**; dedicated L-geometry machinery is about
  **98%**, reused generic infrastructure is **100%**, P2 remains below **1%**,
  and the whole Poincare program remains **3--5%**.

- 2026-08-23 (internal-node and full-interior regularity green):
  `hasDerivAt_of_punct`, `lStrict_piece_c2_at`, `lFinNode_reg`,
  `lStrict_curve_reg`, and `lMinCurve_reg` are focused-checked and their
  downstream exports are refreshed without warnings or placeholders.  The
  generic deleted-neighborhood theorem extends a continuous derivative field
  through one puncture.  At every strict internal node, global C1 gluing makes
  the actual chart phase continuous while the adjacent C2/acceleration pieces
  solve the phase equation off the node; phase reconstruction then supplies
  manifold differentiability, actual-velocity chart differentiability, and
  the intrinsic acceleration equation at the node itself.  Finite segment
  coverage assembles pieces and nodes on the full open interval, and
  `exists_lStrict` transports the conclusion back across repeated and
  zero-length pieces of an arbitrary monotone realization.

  Internal-node regularity and the full open-interval regularity package are
  **100%**.  The exact remaining direct-method regularity producer is
  `exists_lRegExt`: keep the attained curve on `Icc a b`, attach the
  arbitrary-base local regularized curves outside its two endpoints, and use
  the same punctured phase argument to make total `lVelocity` and acceleration
  honest at both endpoints.  Only after that theorem is green may the closed-
  interval `IsLRegCurveOn` minimizer be packaged.  The terminal
  `exists_lMinimizer` and `redVolume_anti` remain **0%**; dedicated L-geometry
  machinery is about **98--99%**, reused generic infrastructure is **100%**,
  P2 remains below **1%**, and the whole Poincare program remains **3--5%**.

- 2026-08-23 (closed-interval endpoint extension green):
  `exists_lRegExt` is focused-checked and refreshed without warnings or
  placeholders.  It starts from a curve that is C1 on `Icc a b` and satisfies
  the full regularized equation on `Ioo a b`.  The one-sided chart derivatives
  determine honest endpoint tangent data; `exists_lRegCurve_at` supplies local
  regularized curves through those data, and the returned total curve uses
  them outside the closed interval while remaining equal to the original
  curve on `Icc a b`.  A punctured phase argument at each endpoint proves the
  total manifold derivative, actual-velocity chart differentiability, and
  intrinsic acceleration equation there.  In particular, no total endpoint
  derivative of the original closed-interval curve is assumed.

  Closed-interval endpoint extension is **100%**.  The next exact theorem is
  `exists_lRegMinOn`: consume the finite witnesses of `exists_lRegMinC1`, use
  `lMinCurve_reg` for the open interval, apply `exists_lRegExt`, normalize
  `Z = (1/2) * lVelocity alpha 0`, and package the attained curve as
  `IsLRegCurveOn` on `Icc 0 b` while retaining exact cost and competitor data.
  The terminal `exists_lMinimizer` and `redVolume_anti` remain **0%**;
  dedicated L-geometry machinery is about **99%**, reused generic
  infrastructure is **100%**, P2 remains below **1%**, and the whole Poincare
  program remains **3--5%**.

- 2026-08-23 (endpoint-honest regularized minimizer green):
  `exists_lRegMinOn` is focused-checked and refreshed without warnings or
  placeholders.  It deliberately consumes `exists_lRegMinC1` before hiding
  the finite realization, obtains closed-interval C1 and open-interval full
  regularity from `lMinCurve_c1` and `lMinCurve_reg`, and applies
  `exists_lRegExt`.  The returned curve is an actual `IsLRegCurveOn` on
  `Icc 0 b`, has the prescribed terminal point, realizes `lRegCostC1`, and is
  no more expensive than every global fixed-endpoint C1 competitor.  Its
  normalized initial tangent is defined from the repaired curve's actual total
  velocity, not from the original one-sided direct-method witness.

  The endpoint-honest regularized minimizer theorem is **100%**.  The next
  exact capstone is `exists_lMinimizer`: expose the same result in raw backward
  time using `sqrtReparam` and `lLength_sqrt`, with an explicit cost/competitor
  statement that does not introduce a temporary admissible-path class or
  enlarge the competitor category beyond what the direct method proved.  The
  terminal theorem itself remains **0%** until stated and proved;
  `redVolume_anti` remains **0%**.  Dedicated L-geometry machinery is about
  **99%**, reused generic infrastructure is **100%**, P2 remains below **1%**,
  and the whole Poincare program remains **3--5%**.

- 2026-08-23 (compact raw L-minimizer capstone green):
  `lCost`, `lCost_eq_reg`, and `exists_lMinimizer` are focused-checked and the
  capstone export is refreshed without warnings or placeholders.  `lCost` is
  the infimum of raw `lLength` over `sqrtReparam` of global regularized C1
  fixed-endpoint competitors; this selects the exact category proved by the
  direct method without adding a temporary admissible-path predicate.
  `lCost_eq_reg` applies `lLength_sqrt` competitor by competitor.  On a compact
  manifold and positive backward time, `exists_lMinimizer` then applies the
  endpoint-honest regularized minimizer at `sqrt tau` and returns an actual
  `IsLRegCurveOn` whose raw L-length equals `lCost` and is no greater than that
  of every competitor in the stated class.

  The compact global-regularized-C1 `exists_lMinimizer` endpoint is **100%**;
  its dedicated direct-method and regularity machinery is **100%**.  This does
  not claim an AC or piecewise-C1 category, nor the complete noncompact L8
  extension.  The next L5 frontier is the unique-minimizing/cut domain, its
  local-diffeomorphism and star-shaped structure, and the measure-zero cut
  image needed for reduced length.  `redVolume_anti` remains **0%**; P2 remains
  below **1%**, and the whole Poincare program remains **3--5%**.

- 2026-08-23 (minimizing-prefix and downward cut fibers green):
  `exists_chartH1_join` is focused-checked and refreshed without warnings or
  placeholders.  It combines two closed-interval C1 curves meeting at a node
  into one finite chart-H1 realization, with the common node duplicated across
  a zero-length middle segment.  `lReg_prefix_min` then uses this realization,
  global fixed-endpoint C1 density, action convergence, and honest interval
  additivity to show that a global regularized minimizer minimizes every closed
  C1 prefix.  The companion `lRegCostC1_eq_on` identifies such a closed-prefix
  minimizer with `lRegCostC1` without adding a global-C1 hypothesis.

  The maximal-flow API now exports `lRegDomain_seg`, `lRegDomain_reg`,
  `lRegCurve_c1On`, `lExpPosDom_down`, and `lExpPosDom_reg`.  `lMinDomain_down`
  consumes these statements and the prefix theorem to prove that minimizing
  membership survives every decrease to a positive backward time;
  `lMinFiber_ord` packages each fixed-initial-tangent fiber as an
  order-connected set.  All of these modules are focused-checked and their
  exported symbols are refreshed.

  The backward-time star-shaped/order-connected minimizing-fiber theorem is
  **100%**; compact global minimizer attainment is **100%**; and the
  nonconjugate local-diffeomorphism producer is **100%**.  The strict pre-cut
  uniqueness / cut-alternative theorem is unstated and unproved (**0%**), and
  the cut-image measure-zero theorem is unstated and unproved (**0%**).
  `IsLMinVec` includes equality at a possible cut time, so the inclusive
  `lMinDomain` is not generally expected to be open; an `interior` wrapper
  would not replace the missing cut mathematics.  The next exact stage is the
  strict pre-cut uniqueness/cut alternative, followed by the separate open
  injectivity domain and its measure-zero cut image.

  `redVolume_anti` remains **0%**.  Dedicated L-geometry machinery for the
  compact ordinary-flow route is about **90%**; generic finite-chart and C1
  density infrastructure used here is **100%**.  P2 remains below **1%**, and
  the whole Poincare program remains approximately **3--5%**.

- 2026-08-23 (strict pre-cut uniqueness green):
  `CutStrict.lMinVec_unique_lt` is focused-checked, axiom-audited, and refreshed
  without warnings or placeholders.  If the `Z` ray minimizes through `tau`,
  `0 < sigma < tau`, and a minimizing `W` ray reaches the same point at
  `sigma`, then `W = Z`.  The strict inequality is essential because
  `IsLMinVec` deliberately includes equality at a possible cut time.

  The proof is the native broken-path argument.  It splices the `W` prefix to
  the `Z` tail, converts both minimizing raw lengths to regularized actions,
  and uses additivity to show that the splice is still globally minimizing.
  `exists_chartH1_join` and `lMinCurve_c1` force C1 matching at the node;
  one-sided `mfderivWithin` uniqueness identifies the two node velocities.
  Finally `lRegSol_eqOn` propagates the matched phase state back to zero, where
  the normalization `A(0) = 2 Z` recovers equality of initial tangents.  The
  public theorem's axiom audit reports only `propext`, classical choice, and
  quotient soundness.

  Strict pre-cut uniqueness is **100%**.  The next exact theorem is
  `lMinVec_nconj_lt`: a ray that remains minimizing to a later time is not
  L-conjugate at a strictly earlier time.  That theorem is currently unstated
  and unproved (**0%**).  Its smallest missing mathematical producer is an
  L-specific `lIndex_neg_conj`: from an interior vanishing nonzero L-Jacobi
  field, construct a globally smooth zero-endpoint field with strictly
  negative `lRegIndex`.  Existing `isLConj_iff_jac`, `lRegIndex_green`,
  `lRegIndex_jacobi`, and `lRegIndex_nonneg` reach both sides of this bridge,
  but no native declaration currently connects them.

  The later `lCut_alt` boundary theorem is also unstated and unproved (**0%**).
  Beyond nonconjugacy it needs the Morgan--Tian min--max bound and a native
  compactness/stability theorem for minimizing initial tangents, so that a
  bounded sequence has a convergent subsequence whose limit remains
  minimizing.  Therefore openness of the genuine injectivity domain and the
  cut-image measure-zero theorem remain **0%**.  Do not replace them by
  `interior (lMinDomain ...)`.

  `redVolume_anti` remains **0%**.  Dedicated L-geometry machinery for the
  compact ordinary-flow route is about **90--91%**; the generic splice,
  finite-chart, C1-density, and ODE-uniqueness infrastructure used here is
  **100%**.  P2 remains below **1%**, and the whole Poincare program remains
  approximately **3--5%**.
