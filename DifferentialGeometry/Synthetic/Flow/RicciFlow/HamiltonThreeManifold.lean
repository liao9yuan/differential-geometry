import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.ImprovedPinching
import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.RicciReaction
import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.RiemannFromRicci3D
import DifferentialGeometry.Synthetic.Flow.RicciFlow.blackbox
import DifferentialGeometry.Synthetic.Analysis.Parabolic.ScalarMaximumPrinciple
import DifferentialGeometry.Synthetic.Analysis.Parabolic.TensorMaximumPrinciple

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Hamilton's Three-Manifold Theorem: Assembly Target

This module records the final theorem interface for `RicciFlow/main.tex`. The
analytic and global inputs are supplied by the maximum-principle, blow-up, and
compactness interfaces.
-/

open SyntheticTensor

section HamiltonThreeManifold

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Minimal geometric realization data needed to state the final Section 12
conclusion without committing yet to a concrete manifold API. -/
structure HamiltonThreeManifoldGeometricContext
    (Manifold Metric Diffeomorphism : Type*) where
  manifoldOfFlow : RicciFlowData k R V Time A -> Manifold
  metricOn : Manifold -> Metric -> Prop
  isCompact : Manifold -> Prop
  isConnected : Manifold -> Prop
  isDiffeomorphism : Diffeomorphism -> Manifold -> Manifold -> Prop
  hasConstantPositiveSectionalCurvature : Manifold -> Metric -> Prop
  pullback_constant_positive :
    forall {M N : Manifold} {h : Metric} {φ : Diffeomorphism},
      isDiffeomorphism φ M N ->
      metricOn N h ->
      hasConstantPositiveSectionalCurvature N h ->
      exists g : Metric, metricOn M g /\ hasConstantPositiveSectionalCurvature M g

/-- Typed input for Hamilton's theorem. Positivity is attached to the Ricci
tensor of the initial slice instead of being a name-only proposition. -/
structure HamiltonThreeManifoldTypedInput
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    where
  data : RicciFlowData k R V Time A
  initialTime : Time
  initialManifold : Manifold
  initial_manifold_eq : initialManifold = ctx.manifoldOfFlow data
  dimensionThree : IsDimensionThree data.atr
  compactInitialManifold : ctx.isCompact initialManifold
  connectedInitialManifold : ctx.isConnected initialManifold
  positiveRicciInitial :
    RicciPositive data.emb (data.conn_fam initialTime) (data.ha_fam initialTime)
      (data.hal_fam initialTime) (data.hsl_fam initialTime) (data.hl_fam initialTime)
      data.atr

/-- Typed final conclusion: the original manifold carries a metric of constant
positive sectional curvature. -/
structure HamiltonThreeManifoldTypedConclusion
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx) where
  metric : Metric
  metric_on_initial : ctx.metricOn input.initialManifold metric
  constant_positive_sectional_curvature :
    ctx.hasConstantPositiveSectionalCurvature input.initialManifold metric

/-- Final transport step: if the compact CGH limit has a constant-positive
curvature metric and the original manifold is diffeomorphic to it, pull that
metric back to the original manifold. -/
noncomputable def typed_conclusion_of_diffeomorphic_constant_positive_limit
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    {limitManifold : Manifold} {limitMetric : Metric} {φ : Diffeomorphism}
    (hφ : ctx.isDiffeomorphism φ input.initialManifold limitManifold)
    (hmetric : ctx.metricOn limitManifold limitMetric)
    (hconst : ctx.hasConstantPositiveSectionalCurvature limitManifold limitMetric) :
    HamiltonThreeManifoldTypedConclusion k R V Time A ctx input :=
  let h := ctx.pullback_constant_positive hφ hmetric hconst
  ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

/-- Geometric context for the manifold-aware Section 12 wrapper. Unlike the
legacy context above, this does not include `manifoldOfFlow`: the manifold is
stored directly in `GeometricRicciFlowData`. -/
structure HamiltonThreeManifoldFlowContext
    (Manifold Metric Diffeomorphism : Type*) where
  metricOn : Manifold -> Metric -> Prop
  isCompact : Manifold -> Prop
  isConnected : Manifold -> Prop
  isDiffeomorphism : Diffeomorphism -> Manifold -> Manifold -> Prop
  hasConstantPositiveSectionalCurvature : Manifold -> Metric -> Prop
  pullback_constant_positive :
    forall {M N : Manifold} {h : Metric} {φ : Diffeomorphism},
      isDiffeomorphism φ M N ->
      metricOn N h ->
      hasConstantPositiveSectionalCurvature N h ->
      exists g : Metric, metricOn M g /\ hasConstantPositiveSectionalCurvature M g

/-- Manifold-aware typed input for Hamilton's theorem. The geometric flow
contains the initial manifold, point set, time domain, metric realization, and
the synthetic core used by the local tensor identities. -/
structure HamiltonThreeManifoldGeometricFlowInput
    {Manifold Point Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    where
  flow : GeometricRicciFlowData k R V Time A Manifold Point Metric
  dimensionThree : IsDimensionThree flow.core.atr
  compactInitialManifold : ctx.isCompact flow.manifold
  connectedInitialManifold : ctx.isConnected flow.manifold
  positiveRicciInitial :
    RicciPositive flow.core.emb (flow.core.conn_fam flow.initialTime)
      (flow.core.ha_fam flow.initialTime) (flow.core.hal_fam flow.initialTime)
      (flow.core.hsl_fam flow.initialTime) (flow.core.hl_fam flow.initialTime)
      flow.core.atr

/-- Final conclusion for the manifold-aware wrapper. -/
structure HamiltonThreeManifoldGeometricFlowConclusion
    {Manifold Point Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldGeometricFlowInput
        (Point := Point) k R V Time A ctx) where
  metric : Metric
  metric_on_initial : ctx.metricOn input.flow.manifold metric
  constant_positive_sectional_curvature :
    ctx.hasConstantPositiveSectionalCurvature input.flow.manifold metric

/-- Final transport step for the manifold-aware wrapper: if the CGH limit
manifold has a constant-positive-sectional-curvature metric and the initial
manifold is diffeomorphic to it, pull the metric back. -/
noncomputable def geometric_flow_conclusion_of_diffeomorphic_constant_positive_limit
    {Manifold Point Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldGeometricFlowInput
        (Point := Point) k R V Time A ctx)
    {limitManifold : Manifold} {limitMetric : Metric} {φ : Diffeomorphism}
    (hφ : ctx.isDiffeomorphism φ input.flow.manifold limitManifold)
    (hmetric : ctx.metricOn limitManifold limitMetric)
    (hconst : ctx.hasConstantPositiveSectionalCurvature limitManifold limitMetric) :
    HamiltonThreeManifoldGeometricFlowConclusion
      (Point := Point) k R V Time A ctx input :=
  let h := ctx.pullback_constant_positive hφ hmetric hconst
  ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

/-- Manifold-aware final theorem target: the initial manifold of the geometric
flow admits a metric with constant positive sectional curvature. This is the
new wrapper boundary for concrete Section 12 realizations. -/
theorem hamilton_three_manifold_exists_constant_positive_metric_geometric_flow
    {Manifold Point Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldGeometricFlowInput
        (Point := Point) k R V Time A ctx)
    {limitManifold : Manifold} {limitMetric : Metric} {φ : Diffeomorphism}
    (hφ : ctx.isDiffeomorphism φ input.flow.manifold limitManifold)
    (hmetric : ctx.metricOn limitManifold limitMetric)
    (hconst : ctx.hasConstantPositiveSectionalCurvature limitManifold limitMetric) :
    exists g : Metric,
      ctx.metricOn input.flow.manifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.flow.manifold g := by
  let conclusion :=
    geometric_flow_conclusion_of_diffeomorphic_constant_positive_limit
      k R V Time A ctx input hφ hmetric hconst
  exact ⟨conclusion.metric, conclusion.metric_on_initial,
    conclusion.constant_positive_sectional_curvature⟩

/-- Smoke theorem for the manifold-aware final wrapper. -/
theorem hamilton_three_manifold_geometric_flow_smoke
    {Manifold Point Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldGeometricFlowInput
        (Point := Point) k R V Time A ctx)
    {limitManifold : Manifold} {limitMetric : Metric} {φ : Diffeomorphism}
    (hφ : ctx.isDiffeomorphism φ input.flow.manifold limitManifold)
    (hmetric : ctx.metricOn limitManifold limitMetric)
    (hconst : ctx.hasConstantPositiveSectionalCurvature limitManifold limitMetric) :
    exists g : Metric,
      ctx.metricOn input.flow.manifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.flow.manifold g :=
  hamilton_three_manifold_exists_constant_positive_metric_geometric_flow
    k R V Time A ctx input hφ hmetric hconst

/-- Cone of nonnegative `(0,2)` tensors, written only as the quadratic-form
condition needed for Ricci nonnegativity. -/
def ricciNonnegativeCone : TensorCone (TensorData R V 0 2) where
  mem T := forall X, 0 <= T ![X, X] ![]

/-- Tensor maximum-principle problem whose cone is Ricci nonnegativity. The
heat inequality predicate is supplied by the later Ricci-evolution realization. -/
def ricciNonnegativeParabolicProblem
    (domain initial : Time -> Prop)
    (heatInequality : (Time -> TensorData R V 0 2) -> Prop) :
    TensorParabolicProblem (TensorData R V 0 2) Time where
  domain := domain
  initial := initial
  cone := ricciNonnegativeCone R V
  heatInequality := heatInequality

/-- Section 12 consumer for Hamilton's tensor weak maximum principle:
nonnegative Ricci curvature is preserved once the Ricci tensor is known to be a
subsolution for the corresponding cone problem. -/
theorem ricci_nonnegative_preserved_by_tensor_wmp
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
      (D.hsl_fam t) (D.hl_fam t) D.atr := by
  let P := ricciNonnegativeParabolicProblem R V Time domain initial heatInequality
  let u : Time -> TensorData R V 0 2 := fun s => ricciFlowRicciTensorAt k R V Time A D s
  have hcone : P.cone.mem (u t) :=
    tensor_wmp_preserve_cone_of_initial P u hsub (fun s hs X => hinit s hs X) t ht
  intro X
  exact hcone X

/-- Shifted tensor for the strict Ricci pinching cone:
`Ric - delta * R * g`. Nonnegativity of this tensor is the quadratic-form
statement `Ric >= delta R g`. -/
noncomputable def ricciPinchingTensorAt
    (D : RicciFlowData k R V Time A) (delta : R) (t : Time) :
    TensorData R V 0 2 :=
  ricciFlowRicciTensorAt k R V Time A D t -
    (delta * ricciFlowScalarCurvatureAt k R V Time A D t) • (D.g_fam t).g_tensor

theorem ricciPinchingTensorAt_eval
    (D : RicciFlowData k R V Time A) (delta : R) (t : Time) (X Y : V) :
    ricciPinchingTensorAt k R V Time A D delta t ![X, Y] ![] =
      ricciFlowRicciTensorAt k R V Time A D t ![X, Y] ![] -
        (delta * ricciFlowScalarCurvatureAt k R V Time A D t) * (D.g_fam t).g X Y := by
  unfold ricciPinchingTensorAt
  simp [MetricDuality.g]

/-- Tensor maximum-principle problem for the shifted pinching tensor. -/
def ricciPinchingParabolicProblem
    (domain initial : Time -> Prop)
    (heatInequality : (Time -> TensorData R V 0 2) -> Prop) :
    TensorParabolicProblem (TensorData R V 0 2) Time :=
  ricciNonnegativeParabolicProblem R V Time domain initial heatInequality

/-- Maximum-principle consumer for the shifted pinching tensor. The geometric
work still lies in proving the shifted tensor is a subsolution for this cone
problem. -/
theorem ricci_pinching_tensor_nonnegative_preserved_by_tensor_wmp
    [TensorWeakMaximumPrinciple (TensorData R V 0 2) Time]
    (D : RicciFlowData k R V Time A) (delta : R)
    (domain initial : Time -> Prop)
    (heatInequality : (Time -> TensorData R V 0 2) -> Prop)
    (hsub : IsTensorSubsolution
      (ricciPinchingParabolicProblem R V Time domain initial heatInequality)
      (fun t => ricciPinchingTensorAt k R V Time A D delta t))
    (hinit : forall t, initial t ->
      forall X, 0 <= ricciPinchingTensorAt k R V Time A D delta t ![X, X] ![])
    (t : Time) (ht : domain t) :
    forall X, 0 <= ricciPinchingTensorAt k R V Time A D delta t ![X, X] ![] := by
  let P := ricciPinchingParabolicProblem R V Time domain initial heatInequality
  let u : Time -> TensorData R V 0 2 :=
    fun s => ricciPinchingTensorAt k R V Time A D delta s
  have hcone : P.cone.mem (u t) :=
    tensor_wmp_preserve_cone_of_initial P u hsub (fun s hs X => hinit s hs X) t ht
  intro X
  exact hcone X

/-- Convert nonnegativity of `Ric - delta R g` into the named pinching
predicate. The subtraction/order bridge is explicit to keep this theorem valid
over the file's abstract ordered coefficient rings. -/
theorem ricciPinched_of_pinching_tensor_nonnegative
    (D : RicciFlowData k R V Time A) (delta : R) (t : Time)
    (h_nonneg :
      forall X, 0 <= ricciPinchingTensorAt k R V Time A D delta t ![X, X] ![])
    (h_le_of_sub_nonneg : forall a b : R, 0 <= a - b -> b <= a) :
    RicciPinched D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
      (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) delta := by
  intro X
  have hx := h_nonneg X
  rw [ricciPinchingTensorAt_eval] at hx
  change delta *
        ScalarCurvature D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
          (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) *
        (D.g_fam t).g X X <=
      ricciForm_tensor D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
        (D.hsl_fam t) (D.hl_fam t) D.atr ![X, X] ![]
  exact h_le_of_sub_nonneg _ _ hx

/-- P5 consumer: preservation of the quadratic-form pinching condition
`Ric >= delta R g`, assuming the shifted tensor satisfies the tensor
maximum-principle subsolution hypothesis. -/
theorem ricci_pinched_preserved_by_tensor_wmp
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
    (h_sub_nonneg_of_le : forall a b : R, b <= a -> 0 <= a - b)
    (h_le_of_sub_nonneg : forall a b : R, 0 <= a - b -> b <= a)
    (t : Time) (ht : domain t) :
    RicciPinched D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
      (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) delta := by
  have hinit_nonneg :
      forall s, initial s ->
        forall X, 0 <= ricciPinchingTensorAt k R V Time A D delta s ![X, X] ![] := by
    intro s hs X
    rw [ricciPinchingTensorAt_eval]
    exact h_sub_nonneg_of_le _ _ (hinit s hs X)
  exact ricciPinched_of_pinching_tensor_nonnegative k R V Time A D delta t
    (ricci_pinching_tensor_nonnegative_preserved_by_tensor_wmp k R V Time A
      D delta domain initial heatInequality hsub hinit_nonneg t ht)
    h_le_of_sub_nonneg

/-- Order bridge used by the shifted Ricci pinching tensor:
`0 <= a - b` is equivalent to `b <= a`. It is kept explicit because this file
works over an abstract ordered coefficient ring. -/
def SubNonnegIffLe : Prop :=
  forall a b : R, (0 <= a - b) <-> b <= a

/-- P5 consumer with the subtraction/order bridge packaged as one hypothesis. -/
theorem ricci_pinched_preserved_by_tensor_wmp_of_sub_nonneg_iff
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
  ricci_pinched_preserved_by_tensor_wmp k R V Time A D delta domain initial
    heatInequality hsub hinit
    (fun a b h => (h_order a b).2 h)
    (fun a b h => (h_order a b).1 h)
    t ht

/-- Section 12 bridge from the typed initial hypothesis `Ric > 0` to the
positive-scalar hypothesis expected by the finite-time theorem. This is a
realization/eigenvalue-trace bridge: it should eventually be instantiated from
the concrete finite-dimensional trace model. -/
class PositiveInitialScalarFromRicciPositive
    (PositiveInitialScalar : RicciFlowData k R V Time A -> Prop) : Prop where
  of_ricci_positive :
    forall (D : RicciFlowData k R V Time A) (t : Time),
      RicciPositive D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
        (D.hsl_fam t) (D.hl_fam t) D.atr ->
        PositiveInitialScalar D

theorem positive_initial_scalar_from_typed_positive_ricci
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [B : PositiveInitialScalarFromRicciPositive k R V Time A H.PositiveInitialScalar] :
    H.PositiveInitialScalar input.data :=
  B.of_ricci_positive input.data input.initialTime input.positiveRicciInitial

/-- Section 12 finite-time branch produced from the typed positive-Ricci input. -/
theorem finite_time_from_typed_positive_ricci
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [B : PositiveInitialScalarFromRicciPositive k R V Time A H.PositiveInitialScalar] :
    H.HasFiniteMaximalTime input.data :=
  finite_time_singularity_from_positive_scalar k R V Time A input.data
    (positive_initial_scalar_from_typed_positive_ricci k R V Time A ctx input)

/-- Bound version of the same finite-time branch.

This is currently recorded for downstream compactness/time-window arguments;
the Section 12 rescaling producer below does not yet consume the bound. -/
theorem finite_time_bound_from_typed_positive_ricci
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [B : PositiveInitialScalarFromRicciPositive k R V Time A H.PositiveInitialScalar] :
    exists bound, H.UpperBoundForMaximalTime input.data bound :=
  finite_time_singularity_bound_from_positive_scalar k R V Time A input.data
    (positive_initial_scalar_from_typed_positive_ricci k R V Time A ctx input)

/-- Section 12 curvature-blow-up branch from a supplied terminal maximal time.
The finite-time theorem identifies that such a terminal time should exist; the
current global interface still asks the realization layer to provide the
specific `T` and the nonextendability proof at `T`. -/
theorem curvature_blow_up_from_typed_maximal_time
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [B : CurvatureBlowUpAlternative k R V Time A]
    (T : Time)
    (hmax : forall ext : RicciFlowExtensionCriterion k R V Time A,
      ¬ ext.CanExtendPast input.data T) :
    UnboundedAboveOn (B.curvatureQuantity input.data) (B.domain input.data T) :=
  finite_time_curvature_blow_up_from_maximality k R V Time A input.data T hmax

/-- Section 12 scalar blow-up branch: curvature blow-up at a terminal maximal
time plus the 3D curvature-control bridge gives scalar unboundedness, the input
used by Hamilton's point-selection lemma. -/
theorem scalar_unbounded_from_typed_maximal_time
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [B : CurvatureBlowUpAlternative k R V Time A]
    [S : ScalarBlowUpFromCurvatureBlowUp k R V Time A]
    (T : Time)
    (hmax : forall ext : RicciFlowExtensionCriterion k R V Time A,
      ¬ ext.CanExtendPast input.data T) :
    UnboundedAboveOn (S.scalarQuantity input.data) (S.domain input.data) :=
  scalar_unbounded_from_curvature_blowup k R V Time A input.data T
    (curvature_blow_up_from_typed_maximal_time k R V Time A ctx input T hmax)

/-- Section 12 point-selection/rescaling branch. The hypothesis `hpoint`
is the explicit realization bridge from the time-only scalar blow-up statement
to the point-spacetime hypothesis expected by the point-selection theorem. -/
theorem point_selection_rescaling_from_typed_maximal_time
    {Point Index Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [B : CurvatureBlowUpAlternative k R V Time A]
    [S : ScalarBlowUpFromCurvatureBlowUp k R V Time A]
    [P : PointSelectionAndRescalingTheorem k R V Time A Point Index]
    (T : Time)
    (hmax : forall ext : RicciFlowExtensionCriterion k R V Time A,
      ¬ ext.CanExtendPast input.data T)
    (hpoint :
      UnboundedAboveOn (S.scalarQuantity input.data) (S.domain input.data) ->
        PointSelectionHypothesis k R V Time A Point P.scalarQuantity P.domain input.data) :
    Nonempty { data : ParabolicRescalingData k R V Time A Point Index //
      data.original = input.data /\ data.scalarQuantity = P.scalarQuantity /\
        data.pinchingRatio = P.pinchingRatio /\
        data.pinchingDecayQuantity = P.pinchingDecayQuantity /\
        data.pinchingDecayFactor = P.pinchingDecayFactor } :=
  point_selection_rescaling_from_interface k R V Time A input.data
    (hpoint
      (scalar_unbounded_from_typed_maximal_time k R V Time A ctx input T hmax))

/-- Curvature blow-up from typed positive Ricci without manually supplying the
terminal time. The missing link is isolated in `MaximalTimeWitness`, which
turns the abstract finite-time predicate into a terminal time and
nonextendability proof. -/
theorem curvature_blow_up_from_typed_finite_time
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [P : PositiveInitialScalarFromRicciPositive k R V Time A H.PositiveInitialScalar]
    [W : MaximalTimeWitness k R V Time A H.HasFiniteMaximalTime]
    [B : CurvatureBlowUpAlternative k R V Time A] :
    UnboundedAboveOn (B.curvatureQuantity input.data)
      (B.domain input.data (W.terminalTime input.data)) :=
  finite_time_curvature_blow_up_from_finite_time k R V Time A input.data
    (finite_time_from_typed_positive_ricci k R V Time A ctx input)

/-- Scalar unboundedness from typed positive Ricci, with the terminal maximal
time supplied by `MaximalTimeWitness`. -/
theorem scalar_unbounded_from_typed_finite_time
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [P : PositiveInitialScalarFromRicciPositive k R V Time A H.PositiveInitialScalar]
    [W : MaximalTimeWitness k R V Time A H.HasFiniteMaximalTime]
    [B : CurvatureBlowUpAlternative k R V Time A]
    [S : ScalarBlowUpFromCurvatureBlowUp k R V Time A] :
    UnboundedAboveOn (S.scalarQuantity input.data) (S.domain input.data) :=
  scalar_unbounded_from_curvature_blowup k R V Time A input.data
    (W.terminalTime input.data)
    (curvature_blow_up_from_typed_finite_time k R V Time A ctx input)

/-- Section 12 rescaling certificate from the typed input. This packages the
previous finite-time, terminal-time, blow-up, scalar-blow-up, spatial-promotion,
and point-selection steps into the exact `ParabolicRescalingData` subtype shape
used by the final assembly certificate. -/
theorem rescaling_certificate_from_typed_input
    {Point Index Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [F : PositiveInitialScalarFromRicciPositive k R V Time A H.PositiveInitialScalar]
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
  point_selection_rescaling_from_interface k R V Time A input.data
    (SP.promote input.data
      (scalar_unbounded_from_typed_finite_time k R V Time A ctx input))

/-- Prefix of the Section 12 assembly produced by the finite-time, blow-up,
point-selection, Hamilton compactness, and curvature-ratio convergence
interfaces. The curvature conclusion used downstream is `ratio.curvature`, so
the ratio and curvature pieces share the same CGH topology/profile by
construction. -/
structure HamiltonSection12RescalingConvergenceData
    {Point Index Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx) where
  rescaling : ParabolicRescalingData k R V Time A Point Index
  rescaling_original : rescaling.original = input.data
  cgh : SmoothCGHConvergenceData k R V Time A Index
  cgh_sequence_eq : cgh.sequence.flow = rescaling.rescaled
  ratio : CurvatureRatioConvergenceConclusion k R V Time A Index
  ratio_sequence_eq : ratio.curvature.sequence = cgh.sequence
  ratio_limit_eq : ratio.curvature.limit = cgh.limit

/-- Section 12 producer from typed initial data through rescaling and curvature
ratio convergence. The caller supplies only the eventual scalar-positivity
witness required by the ratio-convergence interface. -/
theorem rescaling_convergence_data_from_typed_input
    {Point Index Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [F : PositiveInitialScalarFromRicciPositive k R V Time A H.PositiveInitialScalar]
    [W : MaximalTimeWitness k R V Time A H.HasFiniteMaximalTime]
    [B : CurvatureBlowUpAlternative k R V Time A]
    [S : ScalarBlowUpFromCurvatureBlowUp k R V Time A]
    [P : PointSelectionAndRescalingTheorem k R V Time A Point Index]
    [SP : ScalarSpatialPromotionFromTime k R V Time A Point
      S.scalarQuantity P.scalarQuantity S.domain P.domain]
    [K : HamiltonCompactnessTheorem k R V Time A Index]
    [CR : CurvatureRatioConvergenceUnderSmoothCGH k R V Time A Index]
    (hpos : EventuallyPositiveWitness Index R CR.profile.eventually) :
    Nonempty
      (HamiltonSection12RescalingConvergenceData k R V Time A ctx input
        (Point := Point) (Index := Index)) := by
  obtain ⟨rescaling, hrescaling⟩ :=
    rescaling_certificate_from_typed_input k R V Time A ctx input
      (Point := Point) (Index := Index)
  let sequence : PointedRicciFlowSequence k R V Time A Index :=
    { flow := rescaling.rescaled }
  obtain ⟨cgh, hcgh⟩ := K.extract_limit sequence
  obtain ⟨ratio, hratio⟩ :=
    cgh_curvature_ratio_convergence_from_interface k R V Time A cgh hpos
  refine Nonempty.intro ?_
  refine
    { rescaling := rescaling
      rescaling_original := hrescaling.1
      cgh := cgh
      cgh_sequence_eq := ?_
      ratio := ratio
      ratio_sequence_eq := hratio.1
      ratio_limit_eq := hratio.2.1 }
  rw [hcgh]

/-- Abstract spacetime scalar-positivity problem for the CGH limit in Section
12.

`Point` is the point type of the eventual limit model, and `limitRicci` is the
pointwise Ricci tensor on that model. This keeps the "Ricci nonnegative on the
limit" assumption as a concrete quadratic-form predicate instead of an opaque
`Prop`, while still deferring the actual manifold/spacetime realization. -/
structure LimitScalarPositivityProblem (Point SpaceTime : Type*) where
  P : ScalarParabolicProblem R SpaceTime
  scalar : SpaceTime -> R
  pointOf : SpaceTime -> Point
  limitRicci : Point -> TensorData R V 0 2
  ricciNonnegativeOnLimit :
    forall x X, 0 <= limitRicci x ![X, X] ![]
  scalar_nonnegative_of_ricci :
    (forall x X, 0 <= limitRicci x ![X, X] ![]) ->
      forall z, P.domain z -> 0 <= scalar z
  base : SpaceTime
  base_mem : P.domain base
  scalar_base_eq_one : scalar base = 1

/-- If the compactness limit has nonnegative Ricci curvature and normalized
scalar curvature `R(base)=1`, the scalar strong maximum principle makes scalar
curvature strictly positive throughout the chosen spacetime region. -/
theorem limit_scalar_positive_everywhere_from_strong_mp
    {Point SpaceTime : Type*} [ScalarStrongMaximumPrinciple R SpaceTime]
    (input : LimitScalarPositivityProblem R V Point SpaceTime)
    (hone : (0 : R) < 1) :
    forall z, input.P.domain z -> 0 < input.scalar z :=
  ScalarStrongMaximumPrinciple.strict_of_nontrivial input.P input.scalar
    (input.scalar_nonnegative_of_ricci input.ricciNonnegativeOnLimit)
    ⟨input.base, input.base_mem, by rw [input.scalar_base_eq_one]; exact hone⟩

section IntervalSection12

variable (FlowTime AmbientTime : Type*)

/-- Interval-aware typed input for Hamilton's theorem. The flow core is only
defined on regular `FlowTime`; terminal times and infinity live in
`AmbientTime` in the global interfaces. -/
structure HamiltonThreeManifoldIntervalInput
    {Manifold Point Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    where
  flow :
    GeometricRicciFlowOnInterval k R V FlowTime AmbientTime A Manifold Point Metric
  dimensionThree : IsDimensionThree flow.core.atr
  compactInitialManifold : ctx.isCompact flow.manifold
  connectedInitialManifold : ctx.isConnected flow.manifold
  positiveRicciInitial :
    RicciPositive flow.core.emb (flow.core.conn_fam flow.initialTime)
      (flow.core.ha_fam flow.initialTime) (flow.core.hal_fam flow.initialTime)
      (flow.core.hsl_fam flow.initialTime) (flow.core.hl_fam flow.initialTime)
      flow.core.atr

/-- Interval-aware final conclusion. -/
structure HamiltonThreeManifoldIntervalConclusion
    {Manifold Point Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldIntervalInput
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point) ctx) where
  metric : Metric
  metric_on_initial : ctx.metricOn input.flow.manifold metric
  constant_positive_sectional_curvature :
    ctx.hasConstantPositiveSectionalCurvature input.flow.manifold metric

/-- Final transport step for the interval-aware wrapper. -/
noncomputable def interval_conclusion_of_diffeomorphic_constant_positive_limit
    {Manifold Point Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldIntervalInput
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point) ctx)
    {limitManifold : Manifold} {limitMetric : Metric} {φ : Diffeomorphism}
    (hφ : ctx.isDiffeomorphism φ input.flow.manifold limitManifold)
    (hmetric : ctx.metricOn limitManifold limitMetric)
    (hconst : ctx.hasConstantPositiveSectionalCurvature limitManifold limitMetric) :
    HamiltonThreeManifoldIntervalConclusion
      (k := k) (R := R) (V := V) (FlowTime := FlowTime)
      (AmbientTime := AmbientTime) (A := A) (Point := Point) ctx input :=
  let h := ctx.pullback_constant_positive hφ hmetric hconst
  ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

/-- Interval-aware Section 12 assembly certificate. It is the terminal wrapper
shape for the concrete global proof: rescaling, CGH compactness, limit
geometry, and diffeomorphism data all live in the interval-aware geometric
layer. -/
structure HamiltonSection12IntervalAssemblyData
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldIntervalInput
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point) ctx) where
  rescaling :
    IntervalGeometricParabolicRescalingData
      k R V FlowTime AmbientTime A Manifold Point Metric Index
  rescaling_original : rescaling.original = input.flow
  cgh :
    IntervalGeometricSmoothCGHConvergenceData
      k R V FlowTime AmbientTime A Manifold Point Metric Index
  cgh_sequence_eq : cgh.sequence.flow = rescaling.rescaled
  limitScalarProblem : LimitScalarPositivityProblem R V Point SpaceTime
  limit_scalar_positive :
    forall z, limitScalarProblem.P.domain z -> 0 < limitScalarProblem.scalar z
  limitEinsteinTime : FlowTime
  nInv : R
  limit_scalar_normalized :
    GeometricRicciFlowOnInterval.syntheticScalarCurvatureAt
      cgh.limit.flow limitEinsteinTime = 1
  limit_tracefree_norm_zero :
    GeometricRicciFlowOnInterval.syntheticTracefreeRicciNormSqAt
      cgh.limit.flow nInv limitEinsteinTime = 0
  limitMetric : Metric
  limit_metric_on : ctx.metricOn cgh.limit.flow.manifold limitMetric
  limit_constant_positive :
    ctx.hasConstantPositiveSectionalCurvature cgh.limit.flow.manifold limitMetric
  limit_compact : ctx.isCompact cgh.limit.flow.manifold
  compact_limit_diffeomorphism :
    IntervalGeometricCompactLimitDiffeomorphismConclusion
      k R V FlowTime AmbientTime A Manifold Point Metric Index Diffeomorphism
  compact_limit_diffeomorphism_matches :
    compact_limit_diffeomorphism.sequence = cgh.sequence /\
      compact_limit_diffeomorphism.limit = cgh.limit /\
      compact_limit_diffeomorphism.isDiffeomorphism = ctx.isDiffeomorphism
  original_limit_diffeomorphism : Diffeomorphism
  original_diffeomorphic_to_limit :
    ctx.isDiffeomorphism original_limit_diffeomorphism input.flow.manifold
      cgh.limit.flow.manifold

/-- Interval-aware typed claim bundle. The collaborator supplies these claims
from the analytic/global realization; this file owns only the final
composition. -/
structure HamiltonSection12IntervalClaims
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldIntervalInput
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point) ctx) where
  rescaling :
    IntervalGeometricParabolicRescalingData
      k R V FlowTime AmbientTime A Manifold Point Metric Index
  rescaling_original : rescaling.original = input.flow
  cgh :
    IntervalGeometricSmoothCGHConvergenceData
      k R V FlowTime AmbientTime A Manifold Point Metric Index
  cgh_sequence_eq : cgh.sequence.flow = rescaling.rescaled
  limitScalarProblem : LimitScalarPositivityProblem R V Point SpaceTime
  limit_scalar_positive :
    forall z, limitScalarProblem.P.domain z -> 0 < limitScalarProblem.scalar z
  limitEinsteinTime : FlowTime
  nInv : R
  limit_scalar_normalized :
    GeometricRicciFlowOnInterval.syntheticScalarCurvatureAt
      cgh.limit.flow limitEinsteinTime = 1
  limit_tracefree_norm_zero :
    GeometricRicciFlowOnInterval.syntheticTracefreeRicciNormSqAt
      cgh.limit.flow nInv limitEinsteinTime = 0
  limitMetric : Metric
  limit_metric_on : ctx.metricOn cgh.limit.flow.manifold limitMetric
  limit_constant_positive :
    ctx.hasConstantPositiveSectionalCurvature cgh.limit.flow.manifold limitMetric
  limit_compact : ctx.isCompact cgh.limit.flow.manifold
  compact_limit_diffeomorphism :
    IntervalGeometricCompactLimitDiffeomorphismConclusion
      k R V FlowTime AmbientTime A Manifold Point Metric Index Diffeomorphism
  compact_limit_diffeomorphism_matches :
    compact_limit_diffeomorphism.sequence = cgh.sequence /\
      compact_limit_diffeomorphism.limit = cgh.limit /\
      compact_limit_diffeomorphism.isDiffeomorphism = ctx.isDiffeomorphism
  original_limit_diffeomorphism : Diffeomorphism
  original_diffeomorphic_to_limit :
    ctx.isDiffeomorphism original_limit_diffeomorphism input.flow.manifold
      cgh.limit.flow.manifold

/-- Build the interval-aware Section 12 assembly certificate from the smaller
claim bundle. -/
theorem hamilton_section12_interval_assembly_from_claims
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldIntervalInput
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point) ctx)
    (claims :
      HamiltonSection12IntervalClaims
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point)
        (Index := Index) (SpaceTime := SpaceTime) ctx input) :
    Nonempty
      (HamiltonSection12IntervalAssemblyData
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point)
        (Index := Index) (SpaceTime := SpaceTime) ctx input) := by
  refine Nonempty.intro ?_
  exact
    { rescaling := claims.rescaling
      rescaling_original := claims.rescaling_original
      cgh := claims.cgh
      cgh_sequence_eq := claims.cgh_sequence_eq
      limitScalarProblem := claims.limitScalarProblem
      limit_scalar_positive := claims.limit_scalar_positive
      limitEinsteinTime := claims.limitEinsteinTime
      nInv := claims.nInv
      limit_scalar_normalized := claims.limit_scalar_normalized
      limit_tracefree_norm_zero := claims.limit_tracefree_norm_zero
      limitMetric := claims.limitMetric
      limit_metric_on := claims.limit_metric_on
      limit_constant_positive := claims.limit_constant_positive
      limit_compact := claims.limit_compact
      compact_limit_diffeomorphism := claims.compact_limit_diffeomorphism
      compact_limit_diffeomorphism_matches := claims.compact_limit_diffeomorphism_matches
      original_limit_diffeomorphism := claims.original_limit_diffeomorphism
      original_diffeomorphic_to_limit := claims.original_diffeomorphic_to_limit }

/-- Hamilton's positive-Ricci theorem in the interval-aware final wrapper:
the initial manifold of the geometric flow admits a metric of constant positive
sectional curvature. -/
theorem hamilton_three_manifold_exists_constant_positive_metric_interval
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldIntervalInput
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point) ctx)
    (assembly :
      Nonempty
        (HamiltonSection12IntervalAssemblyData
          (k := k) (R := R) (V := V) (FlowTime := FlowTime)
          (AmbientTime := AmbientTime) (A := A) (Point := Point)
          (Index := Index) (SpaceTime := SpaceTime) ctx input)) :
    exists g : Metric,
      ctx.metricOn input.flow.manifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.flow.manifold g := by
  let data := Classical.choice assembly
  exact ctx.pullback_constant_positive data.original_diffeomorphic_to_limit
    data.limit_metric_on data.limit_constant_positive

/-- Final convenience theorem from interval-aware Section 12 claims. -/
theorem hamilton_three_manifold_from_interval_section12_claims
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldIntervalInput
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point) ctx)
    (claims :
      HamiltonSection12IntervalClaims
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point)
        (Index := Index) (SpaceTime := SpaceTime) ctx input) :
    exists g : Metric,
      ctx.metricOn input.flow.manifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.flow.manifold g :=
  hamilton_three_manifold_exists_constant_positive_metric_interval
    (k := k) (R := R) (V := V) (FlowTime := FlowTime)
    (AmbientTime := AmbientTime) (A := A) ctx input
    (hamilton_section12_interval_assembly_from_claims
      (k := k) (R := R) (V := V) (FlowTime := FlowTime)
      (AmbientTime := AmbientTime) (A := A) ctx input claims)

/-- Smoke theorem for the interval-aware terminal Section 12 wrapper. -/
theorem hamilton_section12_interval_claims_smoke
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldFlowContext Manifold Metric Diffeomorphism)
    (input :
      HamiltonThreeManifoldIntervalInput
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point) ctx)
    (claims :
      HamiltonSection12IntervalClaims
        (k := k) (R := R) (V := V) (FlowTime := FlowTime)
        (AmbientTime := AmbientTime) (A := A) (Point := Point)
        (Index := Index) (SpaceTime := SpaceTime) ctx input) :
    exists g : Metric,
      ctx.metricOn input.flow.manifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.flow.manifold g :=
  hamilton_three_manifold_from_interval_section12_claims
    (k := k) (R := R) (V := V) (FlowTime := FlowTime)
    (AmbientTime := AmbientTime) (A := A) ctx input claims

end IntervalSection12

/-- Interface for the closedness of the nonnegative Ricci cone under the
curvature convergence profile chosen for a CGH limit. This is the typed
Section 12 bridge from `Ric(g_i) >= 0` to `Ric(g_infty) >= 0`. -/
class RicciNonnegativeClosedUnderCGHCurvatureConvergence (Index : Type*) where
  limit_ricci_nonnegative :
    forall conclusion : CurvatureConvergenceConclusion k R V Time A Index,
      (forall i,
        NonnegativeRicci (conclusion.sequence.flow i).emb
          ((conclusion.sequence.flow i).conn_fam (conclusion.time i))
          ((conclusion.sequence.flow i).ha_fam (conclusion.time i))
          ((conclusion.sequence.flow i).hal_fam (conclusion.time i))
          ((conclusion.sequence.flow i).hsl_fam (conclusion.time i))
          ((conclusion.sequence.flow i).hl_fam (conclusion.time i))
          (conclusion.sequence.flow i).atr) ->
      NonnegativeRicci conclusion.limit.flow.emb
        (conclusion.limit.flow.conn_fam conclusion.limitTime)
        (conclusion.limit.flow.ha_fam conclusion.limitTime)
        (conclusion.limit.flow.hal_fam conclusion.limitTime)
        (conclusion.limit.flow.hsl_fam conclusion.limitTime)
        (conclusion.limit.flow.hl_fam conclusion.limitTime)
        conclusion.limit.flow.atr

theorem limit_ricci_nonnegative_from_cgh_curvature_convergence
    {Index : Type*} [H : RicciNonnegativeClosedUnderCGHCurvatureConvergence k R V Time A Index]
    (conclusion : CurvatureConvergenceConclusion k R V Time A Index)
    (hseq : forall i,
      NonnegativeRicci (conclusion.sequence.flow i).emb
        ((conclusion.sequence.flow i).conn_fam (conclusion.time i))
        ((conclusion.sequence.flow i).ha_fam (conclusion.time i))
        ((conclusion.sequence.flow i).hal_fam (conclusion.time i))
        ((conclusion.sequence.flow i).hsl_fam (conclusion.time i))
        ((conclusion.sequence.flow i).hl_fam (conclusion.time i))
        (conclusion.sequence.flow i).atr) :
    NonnegativeRicci conclusion.limit.flow.emb
      (conclusion.limit.flow.conn_fam conclusion.limitTime)
      (conclusion.limit.flow.ha_fam conclusion.limitTime)
      (conclusion.limit.flow.hal_fam conclusion.limitTime)
      (conclusion.limit.flow.hsl_fam conclusion.limitTime)
      (conclusion.limit.flow.hl_fam conclusion.limitTime)
      conclusion.limit.flow.atr :=
  H.limit_ricci_nonnegative conclusion hseq

/-- Extract the original-to-limit diffeomorphism used at the end of Section
12 from a compact-limit diffeomorphism conclusion at one sufficiently large
index. The caller supplies `hi`, the concrete instance of the conclusion's
eventual diffeomorphism predicate at that index, and `hsource`, the realization
fact that the rescaled flow at that index has the same underlying manifold as
the initial flow. -/
theorem original_limit_diffeomorphism_from_compact_limit_at_index
    {Index Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    (cgh : SmoothCGHConvergenceData k R V Time A Index)
    (conclusion :
      CompactLimitDiffeomorphismConclusion k R V Time A Index Manifold Diffeomorphism)
    (i : Index)
    (hseq : conclusion.sequence = cgh.sequence)
    (hlimit : conclusion.limit = cgh.limit)
    (hmanifold : conclusion.manifoldOfFlow = ctx.manifoldOfFlow)
    (hdiffeomorphism : conclusion.isDiffeomorphism = ctx.isDiffeomorphism)
    (hsource : ctx.manifoldOfFlow (cgh.sequence.flow i) = input.initialManifold)
    (hi :
      conclusion.isDiffeomorphism (conclusion.diffeomorphism i)
        (conclusion.manifoldOfFlow (conclusion.sequence.flow i))
        (conclusion.manifoldOfFlow conclusion.limit.flow)) :
    Nonempty { phi : Diffeomorphism //
      ctx.isDiffeomorphism phi input.initialManifold
        (ctx.manifoldOfFlow cgh.limit.flow) } := by
  refine Nonempty.intro (Subtype.mk (conclusion.diffeomorphism i) ?_)
  have h := hi
  rw [hdiffeomorphism, hmanifold, hseq, hlimit] at h
  rwa [hsource] at h

/-- P7 wrapper for the limit-Einstein to constant-positive step. The bridge
hypothesis is where the realization layer combines norm definiteness, the
proved Einstein conversion, contracted Bianchi, and the 3D Riemann formula. -/
theorem limit_constant_positive_from_einstein
    {Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (D : RicciFlowData k R V Time A) (t : Time) (nInv : R)
    (limitMetric : Metric)
    (hmetric : ctx.metricOn (ctx.manifoldOfFlow D) limitMetric)
    (hscalar :
      ricciFlowScalarCurvatureAt k R V Time A D t = 1)
    (htracefree :
      ricciFlowTracefreeRicciNormSqAt k R V Time A D nInv t = 0)
    (hbridge :
      ctx.metricOn (ctx.manifoldOfFlow D) limitMetric ->
        ricciFlowScalarCurvatureAt k R V Time A D t = 1 ->
        ricciFlowTracefreeRicciNormSqAt k R V Time A D nInv t = 0 ->
          ctx.hasConstantPositiveSectionalCurvature (ctx.manifoldOfFlow D) limitMetric) :
    ctx.hasConstantPositiveSectionalCurvature (ctx.manifoldOfFlow D) limitMetric :=
  hbridge hmetric hscalar htracefree

/-- P8 wrapper in Hamilton's geometric context: constant positive sectional
curvature gives a positive Ricci lower bound, then Myers gives compactness. -/
theorem limit_compact_from_constant_positive
    {Manifold Metric Diffeomorphism : Type*}
    [H : MyersPositiveRicciCompactness R Manifold]
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (M : Manifold) (g : Metric) (lower : R)
    (hmetric : ctx.metricOn M g)
    (hconst : ctx.hasConstantPositiveSectionalCurvature M g)
    (hlower : 0 < lower)
    (hRic :
      ctx.metricOn M g ->
        ctx.hasConstantPositiveSectionalCurvature M g ->
          H.HasPositiveRicciLowerBound M lower)
    (hcompact_eq : H.IsCompact = ctx.isCompact) :
    ctx.isCompact M := by
  have hcompact :
      H.IsCompact M :=
    limit_compact_from_constant_positive_consumer R
      ctx.metricOn ctx.hasConstantPositiveSectionalCurvature M g lower
      hmetric hconst hlower hRic
  simpa [hcompact_eq] using hcompact

/-- P9 wrapper in the Hamilton assembly language: the normalized scalar at the
rescaling basepoint passes to the CGH limit through curvature convergence. -/
theorem hamilton_limit_scalar_normalized_from_cgh_convergence
    {Point Index Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    (sectionData :
      HamiltonSection12RescalingConvergenceData k R V Time A ctx input
        (Point := Point) (Index := Index))
    (htime : sectionData.ratio.curvature.time = sectionData.rescaling.time)
    (hscalar_sample : forall i,
      ricciFlowScalarCurvatureAt k R V Time A
          (sectionData.rescaling.rescaled i) (sectionData.rescaling.time i) =
        sectionData.rescaling.scalarQuantity
          (sectionData.rescaling.rescaled i) (sectionData.rescaling.point i)
          (sectionData.rescaling.time i))
    (hconst :
      sectionData.ratio.curvature.profile.scalarConvergesTo (fun _ => (1 : R)) 1)
    (hunique :
      forall (seq : Index -> R) (a b : R),
        sectionData.ratio.curvature.profile.scalarConvergesTo seq a ->
        sectionData.ratio.curvature.profile.scalarConvergesTo seq b -> a = b) :
    ricciFlowScalarCurvatureAt k R V Time A
      sectionData.cgh.limit.flow sectionData.ratio.curvature.limitTime = 1 := by
  have hsequence :
      sectionData.ratio.curvature.sequence.flow = sectionData.rescaling.rescaled := by
    rw [sectionData.ratio_sequence_eq, sectionData.cgh_sequence_eq]
  have hnormalized :
      ricciFlowScalarCurvatureAt k R V Time A
        sectionData.ratio.curvature.limit.flow sectionData.ratio.curvature.limitTime = 1 :=
    limit_scalar_normalized_from_cgh_convergence k R V Time A
      sectionData.rescaling sectionData.ratio.curvature hsequence htime hscalar_sample hconst hunique
  rwa [sectionData.ratio_limit_eq] at hnormalized

/-- Section 12 assembly certificate. Each field is a typed checkpoint in the
completion proof: rescaling, compactness, curvature convergence, limit scalar
positivity, improved-pinching limit, Einstein/constant-curvature conversion,
Myers compactness, and the compact-limit diffeomorphism back to the original
manifold. -/
structure HamiltonSection12AssemblyData
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx) where
  rescaling : ParabolicRescalingData k R V Time A Point Index
  rescaling_original : rescaling.original = input.data
  cgh : SmoothCGHConvergenceData k R V Time A Index
  cgh_sequence_eq : cgh.sequence.flow = rescaling.rescaled
  curvature : CurvatureConvergenceConclusion k R V Time A Index
  curvature_matches_cgh :
    curvature.sequence = cgh.sequence /\ curvature.limit = cgh.limit
  ratio : CurvatureRatioConvergenceConclusion k R V Time A Index
  ratio_matches_curvature : ratio.curvature = curvature
  limitScalarProblem : LimitScalarPositivityProblem R V Point SpaceTime
  limit_scalar_positive :
    forall z, limitScalarProblem.P.domain z -> 0 < limitScalarProblem.scalar z
  limitEinsteinTime : Time
  limit_scalar_normalized :
    ricciFlowScalarCurvatureAt k R V Time A cgh.limit.flow limitEinsteinTime = 1
  limit_tracefree_norm_zero :
    ricciFlowTracefreeRicciNormSqAt k R V Time A cgh.limit.flow curvature.nInv
      limitEinsteinTime = 0
  limitMetric : Metric
  limit_metric_on :
    ctx.metricOn (ctx.manifoldOfFlow cgh.limit.flow) limitMetric
  limit_constant_positive :
    ctx.hasConstantPositiveSectionalCurvature (ctx.manifoldOfFlow cgh.limit.flow) limitMetric
  limit_compact : ctx.isCompact (ctx.manifoldOfFlow cgh.limit.flow)
  compact_limit_diffeomorphism :
    CompactLimitDiffeomorphismConclusion k R V Time A Index Manifold Diffeomorphism
  compact_limit_diffeomorphism_matches :
    compact_limit_diffeomorphism.sequence = cgh.sequence /\
      compact_limit_diffeomorphism.limit = cgh.limit /\
      compact_limit_diffeomorphism.manifoldOfFlow = ctx.manifoldOfFlow /\
      compact_limit_diffeomorphism.isDiffeomorphism = ctx.isDiffeomorphism
  original_limit_diffeomorphism : Diffeomorphism
  original_diffeomorphic_to_limit :
    ctx.isDiffeomorphism original_limit_diffeomorphism input.initialManifold
      (ctx.manifoldOfFlow cgh.limit.flow)

/-- Typed claim bundle for the synthetic final wrapper.

The analytic/manifold realization is intentionally not proved here.  The
collaborator can supply these claims from the concrete analysis route, while
this file owns the Lean composition from the claims to the final theorem.  The
prefix is the already-composed rescaling/CGH/ratio data; the remaining fields
are exactly the Section 12 limit-geometry claims needed to build the final
assembly certificate. -/
structure HamiltonSection12Claims
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx) where
  rescalingConvergence :
    HamiltonSection12RescalingConvergenceData k R V Time A ctx input
      (Point := Point) (Index := Index)
  limitScalarProblem : LimitScalarPositivityProblem R V Point SpaceTime
  limit_scalar_positive :
    forall z, limitScalarProblem.P.domain z -> 0 < limitScalarProblem.scalar z
  limitEinsteinTime : Time
  limit_scalar_normalized :
    ricciFlowScalarCurvatureAt k R V Time A
      rescalingConvergence.cgh.limit.flow limitEinsteinTime = 1
  limit_tracefree_norm_zero :
    ricciFlowTracefreeRicciNormSqAt k R V Time A
      rescalingConvergence.cgh.limit.flow
      rescalingConvergence.ratio.curvature.nInv limitEinsteinTime = 0
  limitMetric : Metric
  limit_metric_on :
    ctx.metricOn (ctx.manifoldOfFlow rescalingConvergence.cgh.limit.flow) limitMetric
  limit_constant_positive :
    ctx.hasConstantPositiveSectionalCurvature
      (ctx.manifoldOfFlow rescalingConvergence.cgh.limit.flow) limitMetric
  limit_compact : ctx.isCompact (ctx.manifoldOfFlow rescalingConvergence.cgh.limit.flow)
  compact_limit_diffeomorphism :
    CompactLimitDiffeomorphismConclusion k R V Time A Index Manifold Diffeomorphism
  compact_limit_diffeomorphism_matches :
    compact_limit_diffeomorphism.sequence = rescalingConvergence.cgh.sequence /\
      compact_limit_diffeomorphism.limit = rescalingConvergence.cgh.limit /\
      compact_limit_diffeomorphism.manifoldOfFlow = ctx.manifoldOfFlow /\
      compact_limit_diffeomorphism.isDiffeomorphism = ctx.isDiffeomorphism
  original_limit_diffeomorphism : Diffeomorphism
  original_diffeomorphic_to_limit :
    ctx.isDiffeomorphism original_limit_diffeomorphism input.initialManifold
      (ctx.manifoldOfFlow rescalingConvergence.cgh.limit.flow)

/-- Hamilton-level P1 witness: the contracted second Bianchi identity is
available on every time slice of a synthetic Ricci-flow datum.

The preferred producer is `HamiltonP1NamedCalculusInputs`, which supplies the
named trace/Fubini/commutation calculus and derives this theorem mechanically.
This class remains as the Section 12-facing interface, not as an invitation to
restart the contracted-Bianchi proof stack. -/
class HamiltonP1ContractedSecondBianchiTheorem where
  contracted_second_bianchi :
    forall (D : RicciFlowData k R V Time A) (t : Time) (half : R),
      IsHalfCoefficient half ->
        ContractedSecondBianchiIdentity D.emb (D.conn_fam t) (D.ha_fam t)
          (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) half

/-- Build the Hamilton-level P1 witness from the named-pattern contracted
second-Bianchi calculus on each time slice.

This is the P1 analogue of
`hamiltonP2RiemannFromRicci3DTheorem_of_dim3_calculus`: the realization layer
supplies the reusable double-metric-trace Fubini bridge, the named-pattern
calculus, and trace-commutation for every slice; the Ricci-flow datum supplies
metric compatibility and torsion-freeness through its Levi-Civita hypothesis. -/
@[reducible] def hamiltonP1ContractedSecondBianchiTheorem_of_named_calculus
    (h_fubini :
      forall (D : RicciFlowData k R V Time A) (t : Time),
        HasDoubleMetricTrace05PatternFubini
          DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
          DoubleMetricTrace05Pattern.contractedBianchiDivPattern
          (D.g_fam t) D.atr)
    (h_calc :
      forall (D : RicciFlowData k R V Time A) (t : Time),
        HasContractedSecondBianchiNamedPatternCalculus D.emb (D.conn_fam t)
          (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t)
          D.atr (D.g_fam t))
    (h_ntr :
      forall (D : RicciFlowData k R V Time A) (t : Time),
        NablaTrComm D.emb D.atr (D.conn_fam t) (D.ha_fam t) (D.hl_fam t)) :
    HamiltonP1ContractedSecondBianchiTheorem k R V Time A where
  contracted_second_bianchi := by
    intro D t half h_half
    haveI :
        HasDoubleMetricTrace05PatternFubini
          DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
          DoubleMetricTrace05Pattern.contractedBianchiDivPattern
          (D.g_fam t) D.atr :=
      h_fubini D t
    haveI :
        HasContractedSecondBianchiNamedPatternCalculus D.emb (D.conn_fam t)
          (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t)
          D.atr (D.g_fam t) :=
      h_calc D t
    exact contractedSecondBianchiIdentity_from_second_bianchi_named_patterns
      D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
      (D.hl_fam t) D.atr (D.g_fam t) half h_half
      (D.levi_civita t).1 (D.levi_civita t).2 (h_ntr D t)

/-- Bundled P1 inputs in the form produced by the named-pattern contraction
work.

This is the final-proof-facing package for P1: concrete realizations provide
the metric double-trace Fubini bridge, the named-pattern calculus, and
trace-commutation for each Ricci-flow slice. The Hamilton P1 theorem is then
derived mechanically by `hamiltonP1ContractedSecondBianchiTheorem_of_named_calculus`. -/
class HamiltonP1NamedCalculusInputs where
  metric_trace_fubini :
    forall (D : RicciFlowData k R V Time A) (t : Time),
      HasDoubleMetricTrace05PatternFubini
        DoubleMetricTrace05Pattern.contractedBianchiDivFubiniPattern
        DoubleMetricTrace05Pattern.contractedBianchiDivPattern
        (D.g_fam t) D.atr
  named_pattern_calculus :
    forall (D : RicciFlowData k R V Time A) (t : Time),
      HasContractedSecondBianchiNamedPatternCalculus D.emb (D.conn_fam t)
        (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t)
        D.atr (D.g_fam t)
  trace_comm :
    forall (D : RicciFlowData k R V Time A) (t : Time),
      NablaTrComm D.emb D.atr (D.conn_fam t) (D.ha_fam t) (D.hl_fam t)

/-- Low-priority bridge from the named-pattern P1 inputs to the Hamilton-level
P1 theorem consumed by Section 12. -/
instance (priority := 100) hamiltonP1ContractedSecondBianchiTheorem_of_named_calculus_inputs
    [P1 : HamiltonP1NamedCalculusInputs k R V Time A] :
    HamiltonP1ContractedSecondBianchiTheorem k R V Time A :=
  hamiltonP1ContractedSecondBianchiTheorem_of_named_calculus k R V Time A
    P1.metric_trace_fubini P1.named_pattern_calculus P1.trace_comm

/-- Hamilton-level P2 witness: the three-dimensional Riemann-from-Ricci formula
is available from `IsDimensionThree`.

The preferred producer is the trace/eigenframe route
`hamiltonP2RiemannFromRicci3DTheorem_of_trace_eigenframe_packages`; finite-frame
and real-trace constructors are supported bridges for concrete realizations. -/
class HamiltonP2RiemannFromRicci3DTheorem where
  riemann_from_ricci_3d :
    forall (D : RicciFlowData k R V Time A) (t : Time) (half : R),
      IsDimensionThree D.atr ->
        IsHalfCoefficient half ->
          RiemannFromRicci3DFormula D.emb (D.conn_fam t) (D.ha_fam t)
            (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) half

/-- Build the Hamilton-level P2 witness from the slice-level
Riemann-from-Ricci calculus package.

This keeps `HamiltonP2RiemannFromRicci3DTheorem` as the Section 12-facing
interface while giving realization layers a theorem-shaped path for supplying
that witness on each Ricci-flow time slice. -/
@[reducible] def hamiltonP2RiemannFromRicci3DTheorem_of_dim3_calculus
    (h_calc :
      forall (D : RicciFlowData k R V Time A) (t : Time),
        HasRiemannFromRicci3DCalculus D.emb (D.conn_fam t) (D.ha_fam t)
          (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t)) :
    HamiltonP2RiemannFromRicci3DTheorem k R V Time A where
  riemann_from_ricci_3d := by
    intro D t half h_dim h_half
    haveI :
        HasRiemannFromRicci3DCalculus D.emb (D.conn_fam t) (D.ha_fam t)
          (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) :=
      h_calc D t
    exact riemannFromRicci3DFormula_from_dim3_calculus D.emb (D.conn_fam t)
      (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t) D.atr
      (D.g_fam t) h_dim half h_half

/-- Build the Hamilton-level P2 witness from the finite-frame six-component
package on each time slice.

This is the realization-facing P2 bridge when a coordinate proof supplies a
`Fin 3` frame and the six independent residual component identities, rather
than a prepackaged `HasRiemannFromRicci3DCalculus` instance. -/
@[reducible] def hamiltonP2RiemannFromRicci3DTheorem_of_fin_three_component_packages
    (h_pkg :
      forall (D : RicciFlowData k R V Time A) (t : Time),
        RiemannFromRicci3DFinThreeComponentPackage
          D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
          (D.hl_fam t) D.atr (D.g_fam t)) :
    HamiltonP2RiemannFromRicci3DTheorem k R V Time A where
  riemann_from_ricci_3d := by
    intro D t half h_dim h_half
    exact riemannFromRicci3DFormula_from_fin_three_component_package
      D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
      (D.hl_fam t) D.atr (D.g_fam t) h_dim half h_half (h_pkg D t)

/-- Build the Hamilton-level P2 witness from a trace/eigenframe package on each
time slice.

This is the preferred synthetic P2 packaging after the Ricci convention fix:
the realization layer supplies a Ricci eigenframe, the orthonormal trace
formula, and the off-diagonal Ricci trace equations, while the finite-frame
six residual components are derived internally. -/
@[reducible] def hamiltonP2RiemannFromRicci3DTheorem_of_trace_eigenframe_packages
    (h_pkg :
      forall (D : RicciFlowData k R V Time A) (t : Time),
        RiemannFromRicci3DTraceEigenframePackage
          D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
          (D.hl_fam t) D.atr (D.g_fam t)) :
    HamiltonP2RiemannFromRicci3DTheorem k R V Time A where
  riemann_from_ricci_3d := by
    intro D t half h_dim h_half
    exact riemannFromRicci3DFormula_from_trace_eigenframe_package
      D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
      (D.hl_fam t) D.atr (D.g_fam t) h_dim half h_half (h_pkg D t)

/-- Build the Hamilton-level P2 witness from real finite-dimensional standard
trace data on each time slice.

This is the compact pointwise-real model for P2. The caller only supplies the
two realization identifications `atr.tr = LinearMap.trace` and `g = inner`,
plus metric compatibility and torsion-freeness for each slice. The canonical
coefficient `(2 : ℝ)⁻¹` is stored inside the trace/eigenframe package; the
public P2 theorem still accepts any `half` satisfying `IsHalfCoefficient half`
and converts coefficients internally. -/
@[reducible] noncomputable def
    hamiltonP2RiemannFromRicci3DTheorem_of_real_trace_inner_product
    {E Time₀ A₀ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CommRing A₀] [Algebra ℝ A₀]
    (htr :
      forall (D : RicciFlowData ℝ ℝ E Time₀ A₀) (_t : Time₀)
        (L : E →ₗ[ℝ] E),
          D.atr.tr L = LinearMap.trace ℝ E L)
    (hfin : Module.finrank ℝ E = 3)
    (h_met_inner :
      forall (D : RicciFlowData ℝ ℝ E Time₀ A₀) (t : Time₀) (X Y : E),
        (D.g_fam t).g X Y = inner ℝ X Y)
    (h_mc :
      forall (D : RicciFlowData ℝ ℝ E Time₀ A₀) (t : Time₀),
        IsMetricCompatible D.emb (D.conn_fam t) (D.g_fam t))
    (h_tf :
      forall (D : RicciFlowData ℝ ℝ E Time₀ A₀) (t : Time₀),
        IsTorsionFree D.emb (D.conn_fam t)) :
    HamiltonP2RiemannFromRicci3DTheorem ℝ ℝ E Time₀ A₀ :=
  hamiltonP2RiemannFromRicci3DTheorem_of_trace_eigenframe_packages
    ℝ ℝ E Time₀ A₀
    (fun D t =>
      riemannFromRicci3DTraceEigenframePackage_of_real_trace_inner_product
        D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
        (D.hl_fam t) D.atr (D.g_fam t) (htr D t) hfin
        (h_met_inner D t) (h_mc D t) (h_tf D t)
        (fun a h => by
          exact (mul_eq_zero.mp h).resolve_left (by norm_num))
        ((2 : ℝ)⁻¹) (isHalfCoefficient_inv_two (by norm_num)))

/-- P3.3 named typeclass witness: the geometric contraction of the 3D
Riemann-from-Ricci formula into Hamilton's cubic relation.

The argument named `reaction` is the existing API name for the
Riemann-Ricci-Ricci contraction scalar `R_{ikjl} Ric^{kl} Ric^{ij}` in the
project's fixed curvature slot convention. `IsGeometricReactionData D reaction
cubicQ` is intentionally a field of the typeclass: the realization layer can
choose the concrete contraction predicate once the Ricci/Riemann contraction API
has stabilized. -/
class HamiltonP3CubicReactionGeometryTheorem where
  IsGeometricReactionData :
    RicciFlowData k R V Time A -> (Time -> R) -> (Time -> R) -> Prop
  cubic_reaction_relation :
    forall (D : RicciFlowData k R V Time A) (reaction cubicQ : Time -> R),
      IsDimensionThree D.atr ->
        IsGeometricReactionData D reaction cubicQ ->
          forall t,
            2 * ricciFlowScalarCurvatureAt k R V Time A D t * reaction t =
              2 * ricciFlowRicciNormSqAt k R V Time A D t ^ 2 - cubicQ t

/-- Build the Hamilton-level P3 witness from the slice-level
Riemann-Ricci-Ricci contraction calculus.

The resulting geometric data predicate says exactly two things:

* `cubicQ` is Hamilton's synthetic cubic `Q` on every slice;
* `reaction t`, the Riemann-Ricci-Ricci contraction scalar, satisfies the
  realization's geometricity predicate on every slice.

The Ricci-flow datum supplies metric compatibility and torsion-freeness through
its Levi-Civita hypothesis. -/
@[reducible] def hamiltonP3CubicReactionGeometryTheorem_of_reaction_calculus
    (h_calc :
      forall (D : RicciFlowData k R V Time A) (t : Time),
        HasRicciReactionContractionCalculus D.emb (D.conn_fam t)
          (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t)
          D.atr (D.g_fam t)) :
    HamiltonP3CubicReactionGeometryTheorem k R V Time A where
  IsGeometricReactionData D reaction cubicQ :=
    (forall t,
      cubicQ t =
        hamiltonCubicQ D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
          (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t)) /\
    (forall t,
      HasRicciReactionContractionCalculus.IsGeometricReactionScalar
        (emb := D.emb) (conn := D.conn_fam t) (ha := D.ha_fam t)
        (hal := D.hal_fam t) (hsl := D.hsl_fam t) (hl := D.hl_fam t)
        (atr := D.atr) (met := D.g_fam t) (reaction t))
  cubic_reaction_relation := by
    intro D reaction cubicQ h_dim h_data t
    rcases h_data with ⟨h_cubicQ, h_reaction⟩
    have h_relation :=
      ricciReactionContractionIdentity_from_dim3_calculus
        (emb := D.emb) (conn := D.conn_fam t) (ha := D.ha_fam t)
        (hal := D.hal_fam t) (hsl := D.hsl_fam t) (hl := D.hl_fam t)
        (atr := D.atr) (met := D.g_fam t) (reaction := reaction t)
        (h_geom := h_reaction t) (h_dim := h_dim)
        (h_mc := (D.levi_civita t).1) (h_tf := (D.levi_civita t).2)
    rw [h_cubicQ t]
    simpa [ricciFlowScalarCurvatureAt, ricciFlowRicciNormSqAt] using h_relation

/-- Final-wrapper-facing P3 input package. Realizations can provide one
Riemann-Ricci-Ricci contraction calculus instance per Ricci-flow slice; the
Hamilton-level P3 theorem is then derived mechanically. -/
class HamiltonP3ReactionCalculusInputs where
  reaction_calculus :
    forall (D : RicciFlowData k R V Time A) (t : Time),
      HasRicciReactionContractionCalculus D.emb (D.conn_fam t)
        (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t)
        D.atr (D.g_fam t)

/-- Low-priority bridge from slice-level P3 reaction calculus to the
Hamilton-level P3 theorem consumed by Section 12. -/
instance (priority := 100) hamiltonP3CubicReactionGeometryTheorem_of_reaction_calculus_inputs
    [P3 : HamiltonP3ReactionCalculusInputs k R V Time A] :
    HamiltonP3CubicReactionGeometryTheorem k R V Time A :=
  hamiltonP3CubicReactionGeometryTheorem_of_reaction_calculus k R V Time A
    P3.reaction_calculus

/-- Slice-level P3 input package obtained from Ricci eigenvalue packages.

This is the current checked route for the cubic correction term: the
Hamilton-level geometricity predicate becomes the assertion that each time-slice
Riemann-Ricci-Ricci contraction scalar admits a `RicciReactionEigenvaluePackage`.
The remaining realization work is to construct those packages for the actual
`Rm * Ric * Ric` contraction scalar. -/
@[reducible]
noncomputable def hamiltonP3ReactionCalculusInputs_of_eigenvalue_packages :
    HamiltonP3ReactionCalculusInputs k R V Time A where
  reaction_calculus := by
    intro D t
    exact hasRicciReactionContractionCalculus_of_eigenvalue_packages
      D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
      (D.hl_fam t) D.atr (D.g_fam t)

/-- Hamilton-level P3.3 witness through Ricci eigenvalue packages.

This discharges the Section 12 P3 typeclass while keeping the geometric
payload explicit: callers must still prove the chosen Riemann-Ricci-Ricci
contraction scalar satisfies the eigenvalue-package predicate inside
`IsGeometricReactionData`. -/
@[reducible]
noncomputable def hamiltonP3CubicReactionGeometryTheorem_of_eigenvalue_packages :
    HamiltonP3CubicReactionGeometryTheorem k R V Time A :=
  hamiltonP3CubicReactionGeometryTheorem_of_reaction_calculus k R V Time A
    (hamiltonP3ReactionCalculusInputs_of_eigenvalue_packages k R V Time A).reaction_calculus

/-- Slice-level P3 input package obtained from the P2 trace/eigenframe
packages.

This is the tighter route after the eigenframe contraction proof in
`RicciReaction.lean`: the chosen Riemann-Ricci-Ricci contraction scalar is
required to equal the finite contraction
`sum_i sum_j Rm(e_i,e_j,e_i,e_j) lambda_i lambda_j` for the Ricci eigenframe
carried by the P2 trace package. -/
@[reducible]
noncomputable def hamiltonP3ReactionCalculusInputs_of_trace_eigenframe_packages
    (h_pkg :
      forall (D : RicciFlowData k R V Time A) (t : Time),
        RiemannFromRicci3DTraceEigenframePackage
          D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
          (D.hl_fam t) D.atr (D.g_fam t)) :
    HamiltonP3ReactionCalculusInputs k R V Time A where
  reaction_calculus := by
    intro D t
    exact hasRicciReactionContractionCalculus_of_trace_eigenframe_package
      D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
      (D.hl_fam t) D.atr (D.g_fam t) (h_pkg D t)

/-- Hamilton-level P3.3 witness through P2 trace/eigenframe packages.

This consumes the same package shape as
`hamiltonP2RiemannFromRicci3DTheorem_of_trace_eigenframe_packages`, so a
realization that proves the trace/eigenframe package for P2 also gets the P3
cubic contraction geometry theorem for the corresponding finite eigenframe
Riemann-Ricci-Ricci contraction scalar. -/
@[reducible]
noncomputable def hamiltonP3CubicReactionGeometryTheorem_of_trace_eigenframe_packages
    (h_pkg :
      forall (D : RicciFlowData k R V Time A) (t : Time),
        RiemannFromRicci3DTraceEigenframePackage
          D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
          (D.hl_fam t) D.atr (D.g_fam t)) :
    HamiltonP3CubicReactionGeometryTheorem k R V Time A :=
  hamiltonP3CubicReactionGeometryTheorem_of_reaction_calculus k R V Time A
    (hamiltonP3ReactionCalculusInputs_of_trace_eigenframe_packages
      k R V Time A h_pkg).reaction_calculus

/-- Low-priority default P3.3 instance for Section 12.

The instance is theorem-shaped and conditional through
`IsGeometricReactionData`: when a caller uses it, the geometricity predicate
for the Riemann-Ricci-Ricci contraction scalar is the Ricci-eigenvalue package
predicate from `RicciReaction.lean`. Custom realization-specific P3 instances
can override this because this instance has low priority. -/
noncomputable instance (priority := 50) hamiltonP3CubicReactionGeometryTheorem_of_eigenvalue_packages_instance :
    HamiltonP3CubicReactionGeometryTheorem k R V Time A :=
  hamiltonP3CubicReactionGeometryTheorem_of_eigenvalue_packages k R V Time A

/-- Remaining typed witnesses needed to turn the produced rescaling/CGH data
into the Section 12 claim bundle.

This record is not a fourth mathematical black box: it collects the concrete
choices that the global realization must still make, such as scalar
normalization samples, the improved-pinching decay comparison, the limit metric,
and the final compact-limit diffeomorphism witness. The local theorem packages
P1, P2, and P3 are consumed by `limit_tracefree_norm_zero_from_p3` and
`constant_positive_from_p1_p2`; P1 and P2 already have concrete preferred
producer routes in this file.
Gap typeclass arguments inside builder field types are resolved from the
surrounding instance scope when the builder is consumed. -/
structure HamiltonSection12ClaimBuilderInput
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx) where
  one_pos : (0 : R) < 1
  limitScalarProblem :
    HamiltonSection12RescalingConvergenceData k R V Time A ctx input
      (Point := Point) (Index := Index) ->
      LimitScalarPositivityProblem R V Point SpaceTime
  scalar_time_eq :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      sectionData.ratio.curvature.time = sectionData.rescaling.time
  scalar_sample_eq :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      forall i,
        ricciFlowScalarCurvatureAt k R V Time A
            (sectionData.rescaling.rescaled i) (sectionData.rescaling.time i) =
          sectionData.rescaling.scalarQuantity
            (sectionData.rescaling.rescaled i) (sectionData.rescaling.point i)
            (sectionData.rescaling.time i)
  scalar_constant_converges :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      sectionData.ratio.curvature.profile.scalarConvergesTo (fun _ => (1 : R)) 1
  scalar_convergence_unique :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      forall (seq : Index -> R) (a b : R),
        sectionData.ratio.curvature.profile.scalarConvergesTo seq a ->
        sectionData.ratio.curvature.profile.scalarConvergesTo seq b -> a = b
  limit_dimensionThree_from_input :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      IsDimensionThree input.data.atr ->
        IsDimensionThree sectionData.cgh.limit.flow.atr
  limit_tracefree_norm_zero_from_p3 :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      IsDimensionThree sectionData.cgh.limit.flow.atr ->
        [HamiltonP3CubicReactionGeometryTheorem k R V Time A] ->
        ricciFlowTracefreeRicciNormSqAt k R V Time A sectionData.cgh.limit.flow
          sectionData.ratio.curvature.nInv sectionData.ratio.curvature.limitTime = 0
  limitMetric :
    HamiltonSection12RescalingConvergenceData k R V Time A ctx input
      (Point := Point) (Index := Index) -> Metric
  limit_metric_on :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      ctx.metricOn (ctx.manifoldOfFlow sectionData.cgh.limit.flow)
        (limitMetric sectionData)
  constant_positive_from_p1_p2 :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      IsDimensionThree sectionData.cgh.limit.flow.atr ->
        [HamiltonP1ContractedSecondBianchiTheorem k R V Time A] ->
        [HamiltonP2RiemannFromRicci3DTheorem k R V Time A] ->
          ctx.metricOn (ctx.manifoldOfFlow sectionData.cgh.limit.flow)
              (limitMetric sectionData) ->
            ricciFlowScalarCurvatureAt k R V Time A sectionData.cgh.limit.flow
                sectionData.ratio.curvature.limitTime = 1 ->
              ricciFlowTracefreeRicciNormSqAt k R V Time A
                  sectionData.cgh.limit.flow sectionData.ratio.curvature.nInv
                  sectionData.ratio.curvature.limitTime = 0 ->
                ctx.hasConstantPositiveSectionalCurvature
                  (ctx.manifoldOfFlow sectionData.cgh.limit.flow)
                  (limitMetric sectionData)
  limit_compact_from_constant_positive :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      ctx.metricOn (ctx.manifoldOfFlow sectionData.cgh.limit.flow)
          (limitMetric sectionData) ->
        ctx.hasConstantPositiveSectionalCurvature
            (ctx.manifoldOfFlow sectionData.cgh.limit.flow)
            (limitMetric sectionData) ->
          ctx.isCompact (ctx.manifoldOfFlow sectionData.cgh.limit.flow)
  compact_limit_diffeomorphism :
    forall _sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      CompactLimitDiffeomorphismConclusion k R V Time A Index Manifold Diffeomorphism
  compact_limit_diffeomorphism_matches :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      (compact_limit_diffeomorphism sectionData).sequence = sectionData.cgh.sequence /\
        (compact_limit_diffeomorphism sectionData).limit = sectionData.cgh.limit /\
        (compact_limit_diffeomorphism sectionData).manifoldOfFlow = ctx.manifoldOfFlow /\
        (compact_limit_diffeomorphism sectionData).isDiffeomorphism = ctx.isDiffeomorphism
  original_limit_diffeomorphism :
    HamiltonSection12RescalingConvergenceData k R V Time A ctx input
      (Point := Point) (Index := Index) -> Diffeomorphism
  original_diffeomorphic_to_limit :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      ctx.isDiffeomorphism (original_limit_diffeomorphism sectionData)
        input.initialManifold (ctx.manifoldOfFlow sectionData.cgh.limit.flow)

/-- P10 producer: build the typed Section 12 claim bundle from positive-Ricci
input, the existing analytic/global interfaces, and the local P1/P2/P3 theorem
packages.

The theorem deliberately returns `Nonempty` because the rescaling/CGH prefix is
obtained through abstract extraction interfaces. -/
theorem section12_claims_from_typed_input
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    [ScalarStrongMaximumPrinciple R SpaceTime]
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [F : PositiveInitialScalarFromRicciPositive k R V Time A H.PositiveInitialScalar]
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
      (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) := by
  obtain ⟨sectionData⟩ :=
    rescaling_convergence_data_from_typed_input k R V Time A ctx input
      (Point := Point) (Index := Index) hpos
  have hlimit_dim :
      IsDimensionThree sectionData.cgh.limit.flow.atr :=
    builder.limit_dimensionThree_from_input sectionData input.dimensionThree
  have hlimit_scalar_positive :
      forall z, (builder.limitScalarProblem sectionData).P.domain z ->
        0 < (builder.limitScalarProblem sectionData).scalar z :=
    limit_scalar_positive_everywhere_from_strong_mp R V
      (builder.limitScalarProblem sectionData) builder.one_pos
  have hlimit_scalar_normalized :
      ricciFlowScalarCurvatureAt k R V Time A
        sectionData.cgh.limit.flow sectionData.ratio.curvature.limitTime = 1 :=
    hamilton_limit_scalar_normalized_from_cgh_convergence k R V Time A ctx input
      sectionData (builder.scalar_time_eq sectionData)
      (builder.scalar_sample_eq sectionData)
      (builder.scalar_constant_converges sectionData)
      (builder.scalar_convergence_unique sectionData)
  have hlimit_tracefree_zero :
      ricciFlowTracefreeRicciNormSqAt k R V Time A
        sectionData.cgh.limit.flow sectionData.ratio.curvature.nInv
        sectionData.ratio.curvature.limitTime = 0 :=
    builder.limit_tracefree_norm_zero_from_p3 sectionData hlimit_dim
  have hlimit_constant_positive :
      ctx.hasConstantPositiveSectionalCurvature
        (ctx.manifoldOfFlow sectionData.cgh.limit.flow)
        (builder.limitMetric sectionData) :=
    limit_constant_positive_from_einstein k R V Time A ctx
      sectionData.cgh.limit.flow sectionData.ratio.curvature.limitTime
      sectionData.ratio.curvature.nInv (builder.limitMetric sectionData)
      (builder.limit_metric_on sectionData) hlimit_scalar_normalized
      hlimit_tracefree_zero
      (builder.constant_positive_from_p1_p2 sectionData hlimit_dim)
  have hlimit_compact :
      ctx.isCompact (ctx.manifoldOfFlow sectionData.cgh.limit.flow) :=
    builder.limit_compact_from_constant_positive sectionData
      (builder.limit_metric_on sectionData) hlimit_constant_positive
  refine Nonempty.intro ?_
  exact
    { rescalingConvergence := sectionData
      limitScalarProblem := builder.limitScalarProblem sectionData
      limit_scalar_positive := hlimit_scalar_positive
      limitEinsteinTime := sectionData.ratio.curvature.limitTime
      limit_scalar_normalized := hlimit_scalar_normalized
      limit_tracefree_norm_zero := hlimit_tracefree_zero
      limitMetric := builder.limitMetric sectionData
      limit_metric_on := builder.limit_metric_on sectionData
      limit_constant_positive := hlimit_constant_positive
      limit_compact := hlimit_compact
      compact_limit_diffeomorphism := builder.compact_limit_diffeomorphism sectionData
      compact_limit_diffeomorphism_matches :=
        builder.compact_limit_diffeomorphism_matches sectionData
      original_limit_diffeomorphism := builder.original_limit_diffeomorphism sectionData
      original_diffeomorphic_to_limit :=
        builder.original_diffeomorphic_to_limit sectionData }

/-- Final P10 wrapper with the analytic/global interfaces listed explicitly.
Prefer `hamilton_three_manifold_from_typed_input` for downstream use; this
version is kept as the transparent debugging form. -/
theorem hamilton_three_manifold_from_typed_input_explicit_interfaces
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    [ScalarStrongMaximumPrinciple R SpaceTime]
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [F : PositiveInitialScalarFromRicciPositive k R V Time A H.PositiveInitialScalar]
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
    exists g : Metric,
      ctx.metricOn input.initialManifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.initialManifold g := by
  obtain ⟨claims⟩ :=
    section12_claims_from_typed_input k R V Time A ctx input
      (Point := Point) (Index := Index) (SpaceTime := SpaceTime) hpos builder
  let conclusion :=
    typed_conclusion_of_diffeomorphic_constant_positive_limit k R V Time A ctx input
      claims.original_diffeomorphic_to_limit claims.limit_metric_on
      claims.limit_constant_positive
  exact ⟨conclusion.metric, conclusion.metric_on_initial,
    conclusion.constant_positive_sectional_curvature⟩

/-- Bundled inputs for the Section 12 synthetic assembly.

The hard global analytic stack is inherited from
`HamiltonGlobalAnalyticBlackBoxes` in `blackbox.lean`. The two remaining fields
are the local bridges that should stay visible here because they are realistic
synthetic proof obligations. -/
class HamiltonSyntheticAnalyticInputs (Point Index : Type*) extends
    HamiltonGlobalAnalyticBlackBoxes k R V Time A Point Index where
  positive_scalar_from_ricci :
    PositiveInitialScalarFromRicciPositive k R V Time A finite_time.PositiveInitialScalar
  scalar_spatial_promotion :
    ScalarSpatialPromotionFromTime k R V Time A Point
      scalar_blowup.scalarQuantity point_selection.scalarQuantity
      scalar_blowup.domain point_selection.domain

/-- Low-priority constructor for the analytic/global input bundle from the
individual interface instances. This keeps downstream realization code usable
while still allowing a custom bundled instance to override it. -/
instance (priority := 100) hamiltonSyntheticAnalyticInputs_of_components
    {Point Index : Type*}
    [GB : HamiltonGlobalAnalyticBlackBoxes k R V Time A Point Index]
    [F : PositiveInitialScalarFromRicciPositive k R V Time A
      GB.finite_time.PositiveInitialScalar]
    [SP : ScalarSpatialPromotionFromTime k R V Time A Point
      GB.scalar_blowup.scalarQuantity GB.point_selection.scalarQuantity
      GB.scalar_blowup.domain GB.point_selection.domain] :
    HamiltonSyntheticAnalyticInputs k R V Time A Point Index where
  toHamiltonGlobalAnalyticBlackBoxes := GB
  positive_scalar_from_ricci := F
  scalar_spatial_promotion := SP

/-- HAMILTON POSITIVE RICCI THEOREM (synthetic, conditional).

Canonical export for the synthetic Section 12 layer: typed positive Ricci input
gives a constant-positive-sectional-curvature metric on the initial manifold,
conditional on the bundled analytic/global interfaces, the concrete builder
witnesses, the P1/P2 theorem-package instances, and the P3
Riemann-Ricci-Ricci contraction data predicate supplied by the selected
`HamiltonP3CubicReactionGeometryTheorem` instance. -/
theorem hamilton_three_manifold_from_typed_input
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    [ScalarStrongMaximumPrinciple R SpaceTime]
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [AI : HamiltonSyntheticAnalyticInputs k R V Time A Point Index]
    [G1 : HamiltonP1ContractedSecondBianchiTheorem k R V Time A]
    [G2 : HamiltonP2RiemannFromRicci3DTheorem k R V Time A]
    [G3 : HamiltonP3CubicReactionGeometryTheorem k R V Time A]
    (hpos : EventuallyPositiveWitness Index R AI.curvature_ratio_convergence.profile.eventually)
    (builder :
      HamiltonSection12ClaimBuilderInput k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) :
    exists g : Metric,
      ctx.metricOn input.initialManifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.initialManifold g :=
  hamilton_three_manifold_from_typed_input_explicit_interfaces k R V Time A ctx input
    (Point := Point) (Index := Index) (SpaceTime := SpaceTime)
    (H := AI.finite_time)
    (F := AI.positive_scalar_from_ricci)
    (W := AI.maximal_time)
    (B := AI.curvature_blowup)
    (S := AI.scalar_blowup)
    (P := AI.point_selection)
    (SP := AI.scalar_spatial_promotion)
    (K := AI.compactness)
    (CR := AI.curvature_ratio_convergence)
    hpos builder

/-- Final Section 12 theorem with P3 fed in through the Ricci eigenvalue-package
route for the cubic Riemann-Ricci-Ricci contraction correction.

Compared with `hamilton_three_manifold_from_typed_input`, this wrapper no
longer asks callers for `[HamiltonP3CubicReactionGeometryTheorem]` directly:
it derives P3 from `hamiltonP3CubicReactionGeometryTheorem_of_eigenvalue_packages`.
P1 and P2 remain explicit theorem-package inputs; prefer the P1 named-calculus
and P2 trace/eigenframe producers when supplying them. -/
theorem hamilton_three_manifold_from_typed_input_with_p3_eigenvalue_packages
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    [ScalarStrongMaximumPrinciple R SpaceTime]
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [AI : HamiltonSyntheticAnalyticInputs k R V Time A Point Index]
    [G1 : HamiltonP1ContractedSecondBianchiTheorem k R V Time A]
    [G2 : HamiltonP2RiemannFromRicci3DTheorem k R V Time A]
    (hpos : EventuallyPositiveWitness Index R AI.curvature_ratio_convergence.profile.eventually)
    (builder :
      HamiltonSection12ClaimBuilderInput k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) :
    exists g : Metric,
      ctx.metricOn input.initialManifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.initialManifold g := by
  letI : HamiltonP3CubicReactionGeometryTheorem k R V Time A :=
    hamiltonP3CubicReactionGeometryTheorem_of_eigenvalue_packages k R V Time A
  exact hamilton_three_manifold_from_typed_input k R V Time A ctx input hpos builder

/-- Final Section 12 theorem with P1 fed in through the named-pattern
contracted-Bianchi package.

Compared with `hamilton_three_manifold_from_typed_input`, this wrapper no
longer asks callers for `[HamiltonP1ContractedSecondBianchiTheorem]` directly:
it derives P1 from `HamiltonP1NamedCalculusInputs`. P2 and P3 remain explicit
theorem-package inputs, with P2 normally supplied by the trace/eigenframe or
real-trace constructors above. -/
theorem hamilton_three_manifold_from_typed_input_with_p1_named_calculus
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    [ScalarStrongMaximumPrinciple R SpaceTime]
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    [AI : HamiltonSyntheticAnalyticInputs k R V Time A Point Index]
    [P1 : HamiltonP1NamedCalculusInputs k R V Time A]
    [G2 : HamiltonP2RiemannFromRicci3DTheorem k R V Time A]
    [G3 : HamiltonP3CubicReactionGeometryTheorem k R V Time A]
    (hpos : EventuallyPositiveWitness Index R AI.curvature_ratio_convergence.profile.eventually)
    (builder :
      HamiltonSection12ClaimBuilderInput k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) :
    exists g : Metric,
      ctx.metricOn input.initialManifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.initialManifold g := by
  letI : HamiltonP1ContractedSecondBianchiTheorem k R V Time A :=
    hamiltonP1ContractedSecondBianchiTheorem_of_named_calculus k R V Time A
      P1.metric_trace_fubini P1.named_pattern_calculus P1.trace_comm
  exact hamilton_three_manifold_from_typed_input k R V Time A ctx input hpos builder

/-- Build the full Section 12 assembly certificate from the smaller typed claim
bundle. This is the synthetic wrapper boundary: no analytic theorem is proved
here, but all fields are wired into the final certificate with shared
rescaling/CGH/curvature-ratio data. -/
theorem hamilton_section12_assembly_from_claims
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    (claims :
      HamiltonSection12Claims k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) :
    Nonempty (HamiltonSection12AssemblyData k R V Time A ctx input
      (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) := by
  refine Nonempty.intro ?_
  exact
    { rescaling := claims.rescalingConvergence.rescaling
      rescaling_original := claims.rescalingConvergence.rescaling_original
      cgh := claims.rescalingConvergence.cgh
      cgh_sequence_eq := claims.rescalingConvergence.cgh_sequence_eq
      curvature := claims.rescalingConvergence.ratio.curvature
      curvature_matches_cgh :=
        And.intro claims.rescalingConvergence.ratio_sequence_eq
          claims.rescalingConvergence.ratio_limit_eq
      ratio := claims.rescalingConvergence.ratio
      ratio_matches_curvature := rfl
      limitScalarProblem := claims.limitScalarProblem
      limit_scalar_positive := claims.limit_scalar_positive
      limitEinsteinTime := claims.limitEinsteinTime
      limit_scalar_normalized := claims.limit_scalar_normalized
      limit_tracefree_norm_zero := claims.limit_tracefree_norm_zero
      limitMetric := claims.limitMetric
      limit_metric_on := claims.limit_metric_on
      limit_constant_positive := claims.limit_constant_positive
      limit_compact := claims.limit_compact
      compact_limit_diffeomorphism := claims.compact_limit_diffeomorphism
      compact_limit_diffeomorphism_matches := claims.compact_limit_diffeomorphism_matches
      original_limit_diffeomorphism := claims.original_limit_diffeomorphism
      original_diffeomorphic_to_limit := claims.original_diffeomorphic_to_limit }

/-- Granular Section 12 final assembly. The proof is now a real composition of
the typed assembly certificate, rather than a single theorem-shaped black box. -/
noncomputable def hamilton_three_manifold_from_section12_assembly
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    (assembly :
      HamiltonSection12AssemblyData k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) :
    HamiltonThreeManifoldTypedConclusion k R V Time A ctx input :=
  typed_conclusion_of_diffeomorphic_constant_positive_limit k R V Time A ctx input
    assembly.original_diffeomorphic_to_limit assembly.limit_metric_on
    assembly.limit_constant_positive

/-- Data-valued wrapper for Hamilton's theorem from the Section 12 certificate.

This is the canonical synthetic final theorem shape before concrete
realization: once the Section 12 checkpoint data is supplied, the typed initial
manifold carries a metric of constant positive sectional curvature. -/
noncomputable def hamilton_three_manifold_typed_conclusion_of_section12_claims
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    (assembly :
      Nonempty (HamiltonSection12AssemblyData k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime))) :
    HamiltonThreeManifoldTypedConclusion k R V Time A ctx input :=
  hamilton_three_manifold_from_section12_assembly k R V Time A ctx input
    (Classical.choice assembly)

/-- Hamilton's positive Ricci theorem in the exact geometric form used in
`RicciFlow/main.tex`: the initial manifold admits a metric of constant positive
sectional curvature. Equivalently, after the concrete topological realization,
it is a spherical space form.

All analytic and realization work is isolated in the supplied
`HamiltonSection12AssemblyData`; this theorem only performs the final transport
from the compact constant-curvature blow-up limit back to the original
manifold. -/
theorem hamilton_three_manifold_exists_constant_positive_metric
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    (assembly :
      Nonempty (HamiltonSection12AssemblyData k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime))) :
    exists g : Metric,
      ctx.metricOn input.initialManifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.initialManifold g := by
  let conclusion :=
    hamilton_three_manifold_typed_conclusion_of_section12_claims
      k R V Time A ctx input assembly
  exact ⟨conclusion.metric, conclusion.metric_on_initial,
    conclusion.constant_positive_sectional_curvature⟩

/-- Final synthetic wrapper from the Section 12 claim bundle. This is the
preferred theorem for this branch: collaborators supply the typed claims, and
the synthetic layer returns the exact Hamilton conclusion. -/
theorem hamilton_three_manifold_from_section12_claims
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    (claims :
      HamiltonSection12Claims k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) :
    exists g : Metric,
      ctx.metricOn input.initialManifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.initialManifold g :=
  hamilton_three_manifold_exists_constant_positive_metric k R V Time A ctx input
    (hamilton_section12_assembly_from_claims k R V Time A ctx input claims)

/-- Smoke theorem: the new claims bundle directly exposes the final
constant-positive-sectional-curvature metric statement. -/
theorem hamilton_section12_claims_smoke
    {Point Index SpaceTime Manifold Metric Diffeomorphism : Type*}
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    (claims :
      HamiltonSection12Claims k R V Time A ctx input
        (Point := Point) (Index := Index) (SpaceTime := SpaceTime)) :
    exists g : Metric,
      ctx.metricOn input.initialManifold g /\
        ctx.hasConstantPositiveSectionalCurvature input.initialManifold g :=
  hamilton_three_manifold_from_section12_claims k R V Time A ctx input claims

/-- Legacy name-only data for the old black-box wrapper. Prefer
`HamiltonThreeManifoldTypedInput` and
`hamilton_three_manifold_exists_constant_positive_metric` for new code. -/
structure HamiltonThreeManifoldInput where
  data : RicciFlowData k R V Time A
  dimensionThree : IsDimensionThree data.atr
  compactInitialManifold : Prop
  positiveRicciInitial : Prop

/-- Legacy name-only target conclusion. Prefer the typed existential theorem
above, which states the actual constant-positive-sectional-curvature metric. -/
structure HamiltonThreeManifoldConclusion where
  sphericalSpaceForm : Prop

/-- Legacy black-box bundle for compatibility with early code. The current
canonical wrapper is `hamilton_three_manifold_exists_constant_positive_metric`,
whose conclusion is the exact geometric statement from `main.tex`. -/
class HamiltonThreeManifoldBlackBoxes where
  conclusion : HamiltonThreeManifoldInput k R V Time A -> HamiltonThreeManifoldConclusion
  proves_spherical_space_form :
    forall input : HamiltonThreeManifoldInput k R V Time A,
      (conclusion input).sphericalSpaceForm

theorem hamilton_three_manifold_from_black_boxes
    [H : HamiltonThreeManifoldBlackBoxes k R V Time A]
    (input : HamiltonThreeManifoldInput k R V Time A) :
    (H.conclusion input).sphericalSpaceForm :=
  H.proves_spherical_space_form input

end HamiltonThreeManifold

section HamiltonSection12P4Bridge

variable {k R V Time A : Type*}
variable [Field k] [CommRing R] [Algebra k R] [Invertible (2 : R)]
variable [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Section 12 handoff from the P4 improved-pinching producer.

This is the local bridge from the synthetic P4 producer to the exact
trace-free-Ricci vanishing claim used by the Section 12 assembly. The only
remaining inputs are the convergence and eventuality witnesses needed by the
global compactness consumer. -/
theorem section12_limit_tracefree_norm_zero_from_p4
    {Point Index Manifold Metric Diffeomorphism : Type*}
    [ScalarWeakMaximumPrinciple R Index]
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    (sectionData :
      HamiltonSection12RescalingConvergenceData k R V Time A ctx input
        (Point := Point) (Index := Index))
    [Hsq : ScalarConvergenceSqueezeToZero Index R
      sectionData.ratio.curvature.profile.scalarConvergesTo
      sectionData.ratio.curvature.profile.eventually]
    [Hev : EventuallyImp Index sectionData.ratio.curvature.profile.eventually]
    (D : HamiltonImprovedPinchingProducerData (R := R) (Time := Index))
    (hratio_seq : sectionData.ratio.tracefree_ratio.seq = D.ratio)
    (hdomain :
      sectionData.ratio.curvature.profile.eventually
        (fun i => D.problem.domain i))
    (hupper :
      sectionData.ratio.curvature.profile.scalarConvergesTo
        (fun i => D.C * D.decay i) 0)
    (hnonneg :
      sectionData.ratio.curvature.profile.eventually
        (fun i => 0 <= sectionData.ratio.tracefree_ratio.seq i)) :
    ricciFlowTracefreeRicciNormSqAt k R V Time A sectionData.cgh.limit.flow
      sectionData.ratio.curvature.nInv sectionData.ratio.curvature.limitTime = 0 := by
  have hzero :
      ricciFlowTracefreeRicciNormSqAt k R V Time A
        sectionData.ratio.curvature.limit.flow
        sectionData.ratio.curvature.nInv sectionData.ratio.curvature.limitTime = 0 :=
    limit_tracefree_norm_zero_from_hamilton_improved_pinching_producer
      k R V Time A sectionData.ratio D hratio_seq hdomain hupper hnonneg
  simpa [sectionData.ratio_limit_eq] using hzero

/-- Compatibility adapter: fill the legacy Section 12 builder field
`limit_tracefree_norm_zero_from_p3` using the P4 improved-pinching producer.

The legacy field still accepts dimension-three and P3 arguments because older
realization code may fill it directly from P3. This adapter ignores those
arguments and routes through P4 instead. -/
theorem section12_limit_tracefree_norm_zero_from_p4_builder_field
    {Point Index Manifold Metric Diffeomorphism : Type*}
    [ScalarWeakMaximumPrinciple R Index]
    (ctx : HamiltonThreeManifoldGeometricContext k R V Time A Manifold Metric Diffeomorphism)
    (input : HamiltonThreeManifoldTypedInput k R V Time A ctx)
    (producer :
      forall _sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
        HamiltonImprovedPinchingProducerData (R := R) (Time := Index))
    (hratio_seq :
      forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
        sectionData.ratio.tracefree_ratio.seq = (producer sectionData).ratio)
    (hdomain :
      forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
        sectionData.ratio.curvature.profile.eventually
          (fun i => (producer sectionData).problem.domain i))
    (hupper :
      forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
        sectionData.ratio.curvature.profile.scalarConvergesTo
          (fun i => (producer sectionData).C * (producer sectionData).decay i) 0)
    (hnonneg :
      forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
        sectionData.ratio.curvature.profile.eventually
          (fun i => 0 <= sectionData.ratio.tracefree_ratio.seq i))
    (hsqueeze :
      forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
        ScalarConvergenceSqueezeToZero Index R
          sectionData.ratio.curvature.profile.scalarConvergesTo
          sectionData.ratio.curvature.profile.eventually)
    (heventually :
      forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
        EventuallyImp Index sectionData.ratio.curvature.profile.eventually) :
    forall sectionData :
        HamiltonSection12RescalingConvergenceData k R V Time A ctx input
          (Point := Point) (Index := Index),
      IsDimensionThree sectionData.cgh.limit.flow.atr ->
        [HamiltonP3CubicReactionGeometryTheorem k R V Time A] ->
        ricciFlowTracefreeRicciNormSqAt k R V Time A sectionData.cgh.limit.flow
          sectionData.ratio.curvature.nInv sectionData.ratio.curvature.limitTime = 0 := by
  intro sectionData _h_dim _G3
  letI : ScalarConvergenceSqueezeToZero Index R
      sectionData.ratio.curvature.profile.scalarConvergesTo
      sectionData.ratio.curvature.profile.eventually :=
    hsqueeze sectionData
  letI : EventuallyImp Index sectionData.ratio.curvature.profile.eventually :=
    heventually sectionData
  exact
    section12_limit_tracefree_norm_zero_from_p4
      (k := k) (R := R) (V := V) (Time := Time) (A := A)
      (Point := Point) (Index := Index) ctx input sectionData
      (producer sectionData) (hratio_seq sectionData) (hdomain sectionData)
      (hupper sectionData) (hnonneg sectionData)

end HamiltonSection12P4Bridge
