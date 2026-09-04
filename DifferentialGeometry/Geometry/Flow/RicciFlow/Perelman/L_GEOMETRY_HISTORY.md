# Perelman L-geometry execution history

This file archives the earliest execution entries from
[`L_GEOMETRY_PLAN.md`](L_GEOMETRY_PLAN.md).  These entries are historical
snapshots, not the current status authority; resume work from the live status
and next-theorem pointers in `L_GEOMETRY_PLAN.md`.

## Archived status log

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

<!-- End of the verbatim archived block. -->
