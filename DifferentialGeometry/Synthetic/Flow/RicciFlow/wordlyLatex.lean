import DifferentialGeometry.Synthetic.Flow.RicciFlow.HamiltonThreeManifold

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Word-by-word LaTeX theorem spine for `RicciFlow/main.tex`

This experimental file follows the root LaTeX blueprint theorem by theorem.
The point is not to introduce new assumptions, but to restate the LaTeX steps
in the most concrete synthetic setting currently available and prove each step
by citing existing Lean infrastructure where it already exists.

Large analytic inputs such as DeTurck short-time existence, maximal interval
construction, extension criteria, Hamilton compactness, and Perelman
noncollapsing remain explicit interfaces.

## Status Legend

Each entry below separates two facts:

* `Lean status`: whether the declaration in this file is proved by Lean.
* `Math status`: whether the underlying mathematical theorem is already proved
  in the repository, or is still represented by an explicit interface.

All declarations in this file are Lean-proved wrappers: there is no `sorry`
here. A row marked `conditional` means the wrapper is proved, but only after
the named analytic/geometric interface is supplied by a realization.

| LaTeX target | Lean status | Math status in this repo |
| --- | --- | --- |
| Short-time existence | proved wrapper | conditional on `SmoothInitialMetricShortTimeExistence` |
| Maximal interval | proved wrapper | conditional on maximal gluing and terminal-time interfaces |
| Maximal-flow uniqueness | proved wrapper | conditional on DeTurck-style uniqueness interface |
| Finite maximal time is singular | proved wrapper | conditional on terminal singularity criterion |
| Christoffel/connection evolution | proved wrapper | underlying tensor-calculus proof is in `connection_evolution` |
| Scalar weak maximum principles | proved wrappers | conditional on scalar WMP interface |
| Hamilton tensor maximum principle | proved wrapper | conditional on tensor WMP interface |
| Contracted second Bianchi | proved wrapper | underlying proof route is `HamiltonP1NamedCalculusInputs` |
| Ricci nonnegativity preservation | proved consumer | subsolution/null-vector verification not proved here |
| Ricci pinching preservation | proved consumer | shifted-tensor subsolution not proved here |
| Positive scalar gives finite time | proved wrapper | conditional on finite-time theorem and Ricci-to-scalar bridge |
| Finite-time curvature blow-up | proved wrapper | conditional on terminal-time witness and blow-up alternative |
| Point selection/rescaling | proved wrapper | conditional on scalar promotion and point-selection interface |
| CGH compactness | proved wrapper | conditional on Hamilton compactness interface |
| CGH curvature-ratio convergence | proved wrapper | conditional on ratio-convergence interface |
| Limit scalar positivity | proved consumer | conditional on scalar strong maximum principle |
| 3D curvature identities | proved wrapper | P2 has trace/eigenframe and real-trace producers |
| Q factorization | proved algebraic wrapper | underlying algebra proved in this repo |
| Q lower bound | proved algebraic wrapper | underlying ordered-eigenvalue inequality proved in this repo |
| Improved pinching estimate | proved wrapper | P4 producer proof is in `ImprovedPinching.lean`; WMP/decay remain interfaces |
| Section 12 claims | proved assembly | conditional on analytic/P1/P2/P3/builder inputs |
| Main Hamilton theorem | proved assembly | conditional on typed input, analytic bundle, P1/P2/P3, builder |
-/

open SyntheticTensor

section WordlyLatexTensorCalculusEvolution

variable {k R V Time A : Type*}
variable [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- LaTeX `lem:evol-christoffel`, in the synthetic coordinate-free form.

Status: genuinely Lean-proved tensor calculus, not just a black-box wrapper.
The theorem cited here is `connection_evolution` from
`Evolution/Connection.lean`. It proves the connection variation paired against
the fixed metric at time `t`:

`d/ds|_t g(t)(nabla^s_X Y, Z)
  = -(nabla_X Ric)(Y,Z) - (nabla_Y Ric)(X,Z) + (nabla_Z Ric)(X,Y)`.

In a local frame, raising the last slot gives the usual Christoffel-symbol
formula
`partial_t Gamma^k_ij = -g^{kl}(nabla_i Ric_jl + nabla_j Ric_il - nabla_l Ric_ij)`.
The remaining coordinate-coefficient presentation lives in the realization
layer; this theorem is the proved invariant tensor-calculus core. -/
theorem wordly_latex_lem_evol_christoffel_symbols
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (atr : AbstractTrace R V)
    (g_fam : Time -> MetricDuality R V)
    (h_met : forall vs αs, td.isSmoothFam (fun τ => (g_fam τ).g_tensor vs αs))
    (h_emb_met : forall (W U U' : V),
      td.isSmoothFam (fun s => (emb.embed W) ((g_fam s).g U U')))
    (conn_fam : Time -> V -> V -> V)
    (ha_fam : forall s, forall X Y Z,
      conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : forall s, forall X Y Z,
      conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : forall s, forall (f : R) X Z,
      conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : forall s, forall X (f : R) Y,
      conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_rf : IsRicciFlow emb td atr g_fam h_met conn_fam
      ha_fam hal_fam hsl_fam hl_fam)
    (h_lc : forall s, IsLeviCivita emb (conn_fam s) (g_fam s))
    (t : Time)
    (h_decomp : forall (F : Time -> V) (W : V),
      td.dt_apply (fun s => (g_fam s).g (F s) W) t =
      metric_var_form td g_fam h_met t ![F t, W] ![] +
      td.dt_apply (fun s => (g_fam t).g (F s) W) t)
    (X Y Z : V)
    (h_conn_smooth : td.isSmoothFam (fun s => (g_fam s).g (conn_fam s X Y) Z)) :
    td.dt_apply (fun s => (g_fam t).g (conn_fam s X Y) Z) t =
    - ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t)
        (hsl_fam t) (hl_fam t) atr X Y Z
    - ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t)
        (hsl_fam t) (hl_fam t) atr Y X Z
    + ricci_cov_deriv emb (conn_fam t) (ha_fam t) (hal_fam t)
        (hsl_fam t) (hl_fam t) atr Z X Y :=
  connection_evolution emb td h_st atr g_fam h_met h_emb_met conn_fam
    ha_fam hal_fam hsl_fam hl_fam h_rf h_lc t h_decomp X Y Z h_conn_smooth

end WordlyLatexTensorCalculusEvolution

section WordlyLatexShortTimeAndMaximalInterval

variable {Flow Time Manifold Metric : Type*}

/-- LaTeX `thm:rf-short-time-existence`.

Status: Lean-proved wrapper. The analytic DeTurck/strictly-parabolic theorem is
not proved here; it is the explicit interface
`SmoothInitialMetricShortTimeExistence`. -/
theorem wordly_latex_thm_rf_short_time_existence
    [H : SmoothInitialMetricShortTimeExistence Flow Manifold Metric]
    (g0 : SmoothInitialMetricData Manifold Metric)
    (hsmooth : H.IsSmoothInitialMetric g0) :
    Nonempty { sol : ExperimentalRicciFlowSolution Flow //
      H.StartsFrom g0 sol.flow } :=
  H.exists_short_time g0 hsmooth

/-- LaTeX `bb:maximal-rf-interval`.

Status: Lean-proved wrapper. The gluing/maximal-interval construction and the
terminal-time dichotomy are explicit interfaces, not proved here. -/
theorem wordly_latex_bb_maximal_rf_interval
    [H : SmoothInitialMetricMaximalIntervalConstruction Flow Manifold Metric]
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    (g0 : SmoothInitialMetricData Manifold Metric)
    (hsmooth : H.IsSmoothInitialMetric g0) :
    Nonempty (SmoothInitialMetricMaximalFlow Flow Time Manifold Metric g0) :=
  maximal_flow_from_smooth_initial_metric Flow Time Manifold Metric g0 hsmooth

/-- LaTeX Section 14.6 uniqueness statement.

Status: Lean-proved wrapper. The underlying DeTurck-style uniqueness theorem is
represented by `SmoothInitialMetricUniqueness`. -/
theorem wordly_latex_maximal_flow_unique
    [H : SmoothInitialMetricUniqueness Flow Manifold Metric]
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    (g0 : SmoothInitialMetricData Manifold Metric)
    (hmild : H.MildUniquenessHypothesis g0)
    (M1 M2 : SmoothInitialMetricMaximalFlow Flow Time Manifold Metric g0) :
    H.EquivalentFlows M1.maximal.flow M2.maximal.flow :=
  maximal_flow_unique_from_smooth_initial_metric Flow Time Manifold Metric
    g0 hmild M1 M2

/-- Endpoint uniqueness version of the same LaTeX uniqueness step.

Status: Lean-proved wrapper. The extra mathematical input is that equivalent
maximal flows have the same terminal time. -/
theorem wordly_latex_maximal_terminal_time_unique
    [H : SmoothInitialMetricUniqueness Flow Manifold Metric]
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    [E : ExperimentalTerminalTimeRespectsEquivalence Flow Time H.EquivalentFlows]
    (g0 : SmoothInitialMetricData Manifold Metric)
    (hmild : H.MildUniquenessHypothesis g0)
    (M1 M2 : SmoothInitialMetricMaximalFlow Flow Time Manifold Metric g0) :
    M1.terminalTime = M2.terminalTime :=
  maximal_terminal_time_unique_from_smooth_initial_metric Flow Time Manifold Metric
    g0 hmild M1 M2

/-- LaTeX `lem:sing time iff max time`, finite-endpoint direction.

Status: Lean-proved wrapper. The realization must still supply the terminal
singularity criterion connecting nonextendability to singularity. -/
theorem wordly_latex_lem_finite_maximal_time_is_singular
    [H : SmoothInitialMetricMaximalIntervalConstruction Flow Manifold Metric]
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    [S : ExperimentalTerminalSingularityCriterion Flow Time T.CanExtendPast]
    {g0 : SmoothInitialMetricData Manifold Metric}
    (M : SmoothInitialMetricMaximalFlow Flow Time Manifold Metric g0)
    (hfinite : T.IsFiniteTerminalTime M.maximal) :
    S.IsSingularAt M.maximal.flow M.terminalTime :=
  finite_maximal_time_is_singular_from_smooth_initial_metric
    Flow Time Manifold Metric M hfinite

end WordlyLatexShortTimeAndMaximalInterval

section WordlyLatexParabolicMaximumPrinciples

/-- LaTeX `thm:scalar-wmp-super`.

Status: Lean-proved wrapper around the scalar weak maximum-principle interface;
the PDE maximum principle itself is not proved here. -/
theorem wordly_latex_thm_scalar_wmp_super
    {R Time : Type*} [Preorder R] [Zero R]
    [ScalarWeakMaximumPrinciple R Time]
    (P : ScalarParabolicProblem R Time) (u : Time -> R)
    (hsub : IsScalarSubsolution P u)
    (hinit : IsInitiallyNonpositive P u)
    (t : Time) (ht : P.domain t) :
    u t <= 0 :=
  scalar_wmp_preserve_nonpositive P u hsub hinit t ht

/-- LaTeX `thm:scalar-wmp-sub`.

Status: Lean-proved wrapper using the reusable upper-bound form of scalar WMP;
the PDE maximum principle itself remains an interface. -/
theorem wordly_latex_thm_scalar_wmp_sub_upper_bound
    {R Time : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]
    [ScalarWeakMaximumPrinciple R Time]
    (P : ScalarParabolicProblem R Time) (u : Time -> R) (C : R)
    (hsub : IsScalarSubsolution P (fun t => u t - C))
    (hinit : IsInitiallyNonpositive P (fun t => u t - C))
    (t : Time) (ht : P.domain t) :
    u t <= C :=
  scalar_wmp_preserve_upper_bound P u C hsub hinit t ht

/-- LaTeX `thm:hamilton-tensor-wmp`.

Status: Lean-proved wrapper around the tensor cone-invariance interface; the
tensor maximum-principle analysis is not proved here. -/
theorem wordly_latex_thm_hamilton_tensor_wmp
    {T Time : Type*} [TensorWeakMaximumPrinciple T Time]
    (P : TensorParabolicProblem T Time) (u : Time -> T)
    (hsub : IsTensorSubsolution P u)
    (hinit : IsInitiallyInCone P u)
    (t : Time) (ht : P.domain t) :
    P.cone.mem (u t) :=
  tensor_wmp_preserve_cone P u hsub hinit t ht

end WordlyLatexParabolicMaximumPrinciples

section WordlyLatexSyntheticHamiltonSpine

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- LaTeX `lem:preserve-ricci-nonnegative`.

Status: Lean-proved consumer of Hamilton's tensor WMP. The Ricci evolution
subsolution/null-vector verification is a hypothesis here, not proved in this
wrapper. -/
theorem wordly_latex_lem_preserve_ricci_nonnegative
    [TensorWeakMaximumPrinciple (TensorData R V 0 2) Time]
    (D : RicciFlowData k R V Time A)
    (domain initial : Time -> Prop)
    (heatInequality : (Time -> TensorData R V 0 2) -> Prop)
    (hsub : IsTensorSubsolution
      (ricciNonnegativeParabolicProblem R V Time domain initial heatInequality)
      (fun t => ricciFlowRicciTensorAt k R V Time A D t))
    (hinit : forall t, initial t ->
      NonnegativeRicci D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
        (D.hsl_fam t) (D.hl_fam t) D.atr)
    (t : Time) (ht : domain t) :
    NonnegativeRicci D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
      (D.hsl_fam t) (D.hl_fam t) D.atr :=
  ricci_nonnegative_preserved_by_tensor_wmp k R V Time A
    D domain initial heatInequality hsub hinit t ht

/-- LaTeX `lem:preserve-ricci-pinching`.

Status: Lean-proved consumer of the shifted-Ricci tensor WMP. The shifted
tensor subsolution and the order bridge are explicit hypotheses. -/
theorem wordly_latex_lem_preserve_ricci_pinching
    [TensorWeakMaximumPrinciple (TensorData R V 0 2) Time]
    (D : RicciFlowData k R V Time A) (delta : R)
    (domain initial : Time -> Prop)
    (heatInequality : (Time -> TensorData R V 0 2) -> Prop)
    (hsub : IsTensorSubsolution
      (ricciPinchingParabolicProblem R V Time domain initial heatInequality)
      (fun t => ricciPinchingTensorAt k R V Time A D delta t))
    (hinit : forall t, initial t ->
      RicciPinched D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
        (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) delta)
    (h_order : SubNonnegIffLe R)
    (t : Time) (ht : domain t) :
    RicciPinched D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
      (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) delta :=
  ricci_pinched_preserved_by_tensor_wmp_of_sub_nonneg_iff k R V Time A
    D delta domain initial heatInequality hsub hinit h_order t ht

/-- LaTeX `cor:positive-scalar-finite-time`.

Status: Lean-proved wrapper in the typed positive-Ricci setting. The finite-time
ODE/maximum-principle theorem and the positive-Ricci-to-positive-scalar bridge
are explicit interfaces. -/
theorem wordly_latex_cor_positive_scalar_finite_time
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext
      k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [P : PositiveInitialScalarFromRicciPositive
      k R V Time A H.PositiveInitialScalar] :
    H.HasFiniteMaximalTime input.data :=
  finite_time_from_typed_positive_ricci k R V Time A ctx input

/-- LaTeX `lem:finite-time-curvature-blow-up`.

Status: Lean-proved wrapper. The mathematical blow-up alternative and terminal
time witness are still black-box interfaces. -/
theorem wordly_latex_lem_finite_time_curvature_blow_up
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext
      k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [P : PositiveInitialScalarFromRicciPositive
      k R V Time A H.PositiveInitialScalar]
    [W : MaximalTimeWitness k R V Time A H.HasFiniteMaximalTime]
    [B : CurvatureBlowUpAlternative k R V Time A] :
    UnboundedAboveOn (B.curvatureQuantity input.data)
      (B.domain input.data (W.terminalTime input.data)) :=
  curvature_blow_up_from_typed_finite_time k R V Time A ctx input

/-- Scalar-unboundedness step used before LaTeX `lem:point-selection-rescaling`.

Status: Lean-proved wrapper. The bridge from curvature blow-up to scalar
unboundedness is an explicit interface. -/
theorem wordly_latex_scalar_unbounded_from_finite_time
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext
      k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [P : PositiveInitialScalarFromRicciPositive
      k R V Time A H.PositiveInitialScalar]
    [W : MaximalTimeWitness k R V Time A H.HasFiniteMaximalTime]
    [B : CurvatureBlowUpAlternative k R V Time A]
    [S : ScalarBlowUpFromCurvatureBlowUp k R V Time A] :
    UnboundedAboveOn (S.scalarQuantity input.data) (S.domain input.data) :=
  scalar_unbounded_from_typed_finite_time k R V Time A ctx input

/-- LaTeX `lem:point-selection-rescaling`.

Status: Lean-proved wrapper producing the concrete Section 12 rescaling
certificate. Scalar-to-spacetime promotion and point selection remain explicit
interfaces. -/
theorem wordly_latex_lem_point_selection_rescaling
    {Point Index Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext
      k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [F : PositiveInitialScalarFromRicciPositive
      k R V Time A H.PositiveInitialScalar]
    [W : MaximalTimeWitness k R V Time A H.HasFiniteMaximalTime]
    [B : CurvatureBlowUpAlternative k R V Time A]
    [S : ScalarBlowUpFromCurvatureBlowUp k R V Time A]
    [P : PointSelectionAndRescalingTheorem k R V Time A Point Index]
    [SP : ScalarSpatialPromotionFromTime k R V Time A Point
      S.scalarQuantity P.scalarQuantity S.domain P.domain] :
    Nonempty { data : ParabolicRescalingData k R V Time A Point Index //
      data.original = input.data /\ data.scalarQuantity = P.scalarQuantity /\
        data.pinchingRatio = P.pinchingRatio /\
        data.pinchingDecayQuantity = P.pinchingDecayQuantity /\
        data.pinchingDecayFactor = P.pinchingDecayFactor } :=
  rescaling_certificate_from_typed_input k R V Time A ctx input
    (Point := Point) (Index := Index)

/-- LaTeX `bb:cgh-compactness`.

Status: Lean-proved wrapper that directly exposes the Hamilton-CGH compactness
interface. The compactness theorem itself is not proved here. -/
theorem wordly_latex_bb_cgh_compactness
    {Index : Type*}
    [K : HamiltonCompactnessTheorem k R V Time A Index]
    (sequence : PointedRicciFlowSequence k R V Time A Index) :
    Nonempty { data : SmoothCGHConvergenceData k R V Time A Index //
      data.sequence = sequence } :=
  K.extract_limit sequence

/-- LaTeX `cor:cgh-curvature-ratio-convergence`.

Status: Lean-proved wrapper. Smooth CGH curvature convergence and the
ratio-convergence conclusion are supplied by the interface. -/
theorem wordly_latex_cor_cgh_curvature_ratio_convergence
    {Index : Type*}
    [CR : CurvatureRatioConvergenceUnderSmoothCGH k R V Time A Index]
    (data : SmoothCGHConvergenceData k R V Time A Index)
    (hpos : EventuallyPositiveWitness Index R CR.profile.eventually) :
    Nonempty { conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index //
      conclusion.curvature.sequence = data.sequence /\
        conclusion.curvature.limit = data.limit /\
        conclusion.curvature.profile = CR.profile } :=
  cgh_curvature_ratio_convergence_from_interface k R V Time A data hpos

/-- LaTeX `lem:limit-scalar-positive`.

Status: Lean-proved consumer of scalar strong maximum principle in the
limit-spacetime problem. The strong maximum principle is an analytic interface. -/
theorem wordly_latex_lem_limit_scalar_positive
    {Point SpaceTime : Type*} [ScalarStrongMaximumPrinciple R SpaceTime]
    (problem : LimitScalarPositivityProblem R V Point SpaceTime)
    (hone : (0 : R) < 1) :
    forall z, problem.P.domain z -> 0 < problem.scalar z :=
  limit_scalar_positive_everywhere_from_strong_mp R V problem hone

/-- LaTeX `lem:contracted-second-bianchi`.

Status: Lean-proved wrapper around the Hamilton P1 theorem. The underlying
proof route is the named trace/Fubini/commutation calculus packaged by
`HamiltonP1NamedCalculusInputs`; this presentation theorem does not reopen that
calculation. -/
theorem wordly_latex_lem_contracted_second_bianchi
    [P1 : HamiltonP1ContractedSecondBianchiTheorem k R V Time A]
    (D : RicciFlowData k R V Time A) (t : Time) (half : R)
    (h_half : IsHalfCoefficient half) :
    ContractedSecondBianchiIdentity D.emb (D.conn_fam t) (D.ha_fam t)
      (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) half :=
  P1.contracted_second_bianchi D t half h_half

/-- LaTeX `lem:3d-curvature-identities`.

Status: Lean-proved wrapper around the stable P2 Riemann-from-Ricci theorem.
The preferred producer is the trace/eigenframe package route, with the
real-trace constructor available for finite-dimensional real realizations; this
presentation file does not reprove that algebra. -/
theorem wordly_latex_lem_3d_curvature_identities
    [P2 : HamiltonP2RiemannFromRicci3DTheorem k R V Time A]
    (D : RicciFlowData k R V Time A) (t : Time) (half : R)
    (h_dim : IsDimensionThree D.atr)
    (h_half : IsHalfCoefficient half) :
    RiemannFromRicci3DFormula D.emb (D.conn_fam t) (D.ha_fam t)
      (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) half :=
  P2.riemann_from_ricci_3d D t half h_dim h_half

/-- LaTeX `lem:Q-factorization`.

Status: Lean-proved algebraic wrapper. The underlying eigenvalue polynomial
identity is already proved in the repository. -/
theorem wordly_latex_lem_Q_factorization
    {R0 : Type*} [CommRing R0] (l1 l2 l3 : R0) :
    hamiltonCubicQ3 l1 l2 l3 = hamiltonCubicQFactorized3 l1 l2 l3 :=
  hamiltonCubicQ3_factorized l1 l2 l3

/-- LaTeX `lem:Q-lower-bound`.

Status: Lean-proved algebraic wrapper. The ordered nonnegative eigenvalue
inequality is already proved in the repository under the displayed hypotheses. -/
theorem wordly_latex_lem_Q_lower_bound
    {R0 : Type*} [Field R0] [LinearOrder R0] [IsStrictOrderedRing R0]
    (l1 l2 l3 delta : R0)
    (h12 : l2 <= l1) (h23 : l3 <= l2)
    (h1 : 0 <= l1) (h2 : 0 <= l2) (h3 : 0 <= l3)
    (hdelta : 0 <= delta)
    (hpinch : delta * ricciEigenScalar3 l1 l2 l3 <= l3) :
    2 * delta ^ 2 * ricciEigenNormSq3 l1 l2 l3 *
        tracefreeRicciEigenNormSq3 l1 l2 l3 <=
      hamiltonCubicQ3 l1 l2 l3 :=
  hamiltonCubicQ3_lower_bound_ordered_nonnegative_eigenvalues
    l1 l2 l3 delta h12 h23 h1 h2 h3 hdelta hpinch

/-- LaTeX `cor:improved-ricci-pinching`.

Status: Lean-proved wrapper around the P4 producer and scalar weak maximum
principle consumer. The quotient-evolution producer is in
`DimensionThree/ImprovedPinching.lean`; the scalar WMP and decay data remain
explicit interfaces. -/
theorem wordly_latex_cor_improved_ricci_pinching
    {R0 Time0 : Type*}
    [CommRing R0] [LinearOrder R0] [IsStrictOrderedRing R0]
    [ScalarWeakMaximumPrinciple R0 Time0]
    (D : HamiltonImprovedPinchingProducerData (R := R0) (Time := Time0))
    (t : Time0) (ht : D.problem.domain t) :
    D.ratio t <= D.C * D.decay t :=
  improved_ricci_pinching_ratio_bound_from_hamilton_producer D t ht

/-- Section 12 P4 consumer: improved pinching plus decay forces the CGH limit
sample to have vanishing trace-free Ricci norm squared.

Status: Lean-proved wrapper. The P4 producer is synthetic; the convergence
squeeze, eventuality, scalar WMP, and decay upper bound remain interfaces. -/
theorem wordly_latex_cor_limit_tracefree_norm_zero_from_p4
    {k0 R0 V0 Time0 A0 Index : Type*}
    [Field k0] [CommRing R0] [Algebra k0 R0] [Invertible (2 : R0)]
    [LinearOrder R0] [IsStrictOrderedRing R0]
    [AddCommGroup V0] [Module R0 V0] [Module k0 V0]
    [IsScalarTower k0 R0 V0]
    [CommRing A0] [Algebra R0 A0]
    [ScalarWeakMaximumPrinciple R0 Index]
    (conclusion : CurvatureRatioConvergenceConclusion k0 R0 V0 Time0 A0 Index)
    [Hsq : ScalarConvergenceSqueezeToZero Index R0
      conclusion.curvature.profile.scalarConvergesTo
      conclusion.curvature.profile.eventually]
    [Hev : EventuallyImp Index conclusion.curvature.profile.eventually]
    (D : HamiltonImprovedPinchingProducerData (R := R0) (Time := Index))
    (hratio_seq : conclusion.tracefree_ratio.seq = D.ratio)
    (hdomain : conclusion.curvature.profile.eventually (fun i => D.problem.domain i))
    (hupper :
      conclusion.curvature.profile.scalarConvergesTo
        (fun i => D.C * D.decay i) 0)
    (hnonneg : conclusion.curvature.profile.eventually
      (fun i => 0 <= conclusion.tracefree_ratio.seq i)) :
    ricciFlowTracefreeRicciNormSqAt k0 R0 V0 Time0 A0 conclusion.curvature.limit.flow
      conclusion.curvature.nInv conclusion.curvature.limitTime = 0 :=
  limit_tracefree_norm_zero_from_hamilton_improved_pinching_producer
    k0 R0 V0 Time0 A0 conclusion D hratio_seq hdomain hupper hnonneg

/-- LaTeX completion Section: build the Section 12 claims.

Status: Lean-proved assembly theorem. It depends on the analytic/global
interfaces, the P1/P2/P3 synthetic theorem interfaces, and the concrete builder
data for the limit-geometry claims. -/
theorem wordly_latex_section12_claims_from_typed_input
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    [ScalarStrongMaximumPrinciple R SpaceTime]
    (ctx : HamiltonThreeManifoldGeometricContext
      k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [F : PositiveInitialScalarFromRicciPositive
      k R V Time A H.PositiveInitialScalar]
    [W : MaximalTimeWitness k R V Time A H.HasFiniteMaximalTime]
    [B : CurvatureBlowUpAlternative k R V Time A]
    [S : ScalarBlowUpFromCurvatureBlowUp k R V Time A]
    [P : PointSelectionAndRescalingTheorem k R V Time A Point Index]
    [SP : ScalarSpatialPromotionFromTime k R V Time A Point
      S.scalarQuantity P.scalarQuantity S.domain P.domain]
    [K : HamiltonCompactnessTheorem k R V Time A Index]
    [CR : CurvatureRatioConvergenceUnderSmoothCGH k R V Time A Index]
    [G1 : HamiltonP1ContractedSecondBianchiTheorem k R V Time A]
    [G2 : HamiltonP2RiemannFromRicci3DTheorem k R V Time A]
    [G3 : HamiltonP3CubicReactionGeometryTheorem k R V Time A]
    (hpos : EventuallyPositiveWitness Index R CR.profile.eventually)
    (builder :
      HamiltonSection12ClaimBuilderInput k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) :
    Nonempty (HamiltonSection12Claims k R V Time A ctx input
      (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) :=
  section12_claims_from_typed_input k R V Time A ctx input
    (Point := Point) (Index := Index) (SpaceTime := SpaceTime) hpos builder

/-- LaTeX `thm:main-hamilton-3d`.

Status: Lean-proved final assembly theorem in the current typed synthetic
setting. It is not yet the unconditional manifold theorem from the LaTeX text:
it remains conditional on typed Ricci-flow input, analytic black boxes, P1/P2/P3
interfaces, and the Section 12 builder. -/
theorem wordly_latex_thm_main_hamilton_3d
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    [ScalarStrongMaximumPrinciple R SpaceTime]
    (ctx : HamiltonThreeManifoldGeometricContext
      k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [AI : HamiltonSyntheticAnalyticInputs k R V Time A Point Index]
    [G1 : HamiltonP1ContractedSecondBianchiTheorem k R V Time A]
    [G2 : HamiltonP2RiemannFromRicci3DTheorem k R V Time A]
    [G3 : HamiltonP3CubicReactionGeometryTheorem k R V Time A]
    (hpos : EventuallyPositiveWitness Index R
      AI.curvature_ratio_convergence.profile.eventually)
    (builder :
      HamiltonSection12ClaimBuilderInput k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) :
    exists g : Metric,
      ctx.metricOn input.initialManifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.initialManifold g :=
  hamilton_three_manifold_from_typed_input k R V Time A ctx input hpos builder

end WordlyLatexSyntheticHamiltonSpine
