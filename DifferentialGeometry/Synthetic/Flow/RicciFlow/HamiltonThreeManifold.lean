import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.ImprovedPinching
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Global.Compactness
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
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
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
  have hinitCone : IsInitiallyInCone P u := by
    intro s hs X
    exact hinit s hs X
  have hcone : P.cone.mem (u t) :=
    tensor_wmp_preserve_cone P u hsub hinitCone t ht
  intro X
  exact hcone X

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
