import DifferentialGeometry.Synthetic.Flow.RicciFlow.Global.BlowUp
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.RicciNorm
import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.ImprovedPinching

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Compactness and Noncollapsing Interfaces

This file names the global black boxes used in the blow-up-limit part of
Hamilton's theorem.
-/

open SyntheticTensor

/-- A concrete convergence witness: a sequence, a proposed limit, and the
shared relation saying that this sequence converges to that limit. The
relation is a parameter rather than a field so a conclusion can force several
witnesses to use the same topology/filter. -/
structure ConvergenceWitness (Index Value : Type*)
    (ConvergesTo : (Index -> Value) -> Value -> Prop) where
  seq : Index -> Value
  limit : Value
  converges : ConvergesTo seq limit

/-- A concrete eventual-positivity witness for scalar quantities along a
sequence. The `eventually` relation is a parameter so multiple eventual
statements can share the same filter. -/
structure EventuallyPositiveWitness (Index R : Type*) [Zero R] [Preorder R]
    (eventually : (Index -> Prop) -> Prop) where
  scalar : Index -> R
  positive_eventually : eventually (fun i => 0 < scalar i)

/-- Compatibility between an abstract scalar convergence relation and an
eventuality/filter relation: a nonnegative sequence squeezed eventually below
a sequence converging to zero also converges to the zero limit.

This is the Section 12 topological/order bridge behind the step
`|Ric^0|^2 / R^2 <= C * decay_i` and `decay_i -> 0`, hence the limit ratio is
zero. Concrete realizations should instantiate this with `Filter.Tendsto` and
the usual order topology. -/
class ScalarConvergenceSqueezeToZero (Index R : Type*) [Zero R] [Preorder R]
    (ConvergesTo : (Index -> R) -> R -> Prop)
    (eventually : (Index -> Prop) -> Prop) : Prop where
  squeeze_to_zero :
    forall {u b : Index -> R} {limit : R},
      ConvergesTo u limit ->
      ConvergesTo b 0 ->
      eventually (fun i => 0 <= u i) ->
      eventually (fun i => u i <= b i) ->
        limit = 0

/-- Monotonicity for an abstract eventuality/filter relation. This is the
minimum structure needed to turn a pointwise implication on a domain into an
eventual bound. Concrete realizations should instantiate it from filter
monotonicity. -/
class EventuallyImp (Index : Type*) (eventually : (Index -> Prop) -> Prop) : Prop where
  mono :
    forall {P Q : Index -> Prop},
      eventually P -> (forall i, P i -> Q i) -> eventually Q

section CompactnessInterfaces

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- A sequence of pointed Ricci flows, abstracting the parabolic rescaling setup. -/
structure PointedRicciFlowSequence (Index : Type*) where
  flow : Index -> RicciFlowData k R V Time A

/-- Riemann tensor of a bundled Ricci flow at a time. -/
noncomputable def ricciFlowRiemannTensorAt
    (D : RicciFlowData k R V Time A) (t : Time) : TensorData R V 1 3 :=
  Rm_tensor D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t) (D.hl_fam t)

/-- Ricci tensor of a bundled Ricci flow at a time. -/
noncomputable def ricciFlowRicciTensorAt
    (D : RicciFlowData k R V Time A) (t : Time) : TensorData R V 0 2 :=
  ricciForm_tensor D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
    (D.hl_fam t) D.atr

/-- Scalar curvature of a bundled Ricci flow at a time. -/
noncomputable def ricciFlowScalarCurvatureAt
    (D : RicciFlowData k R V Time A) (t : Time) : R :=
  ScalarCurvature D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
    (D.hl_fam t) D.atr (D.g_fam t)

/-- Squared Ricci norm of a bundled Ricci flow at a time. -/
noncomputable def ricciFlowRicciNormSqAt
    (D : RicciFlowData k R V Time A) (t : Time) : R :=
  ricci_norm_sq D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t) (D.hsl_fam t)
    (D.hl_fam t) D.atr (D.g_fam t)

/-- Squared trace-free Ricci norm of a bundled Ricci flow at a time. -/
noncomputable def ricciFlowTracefreeRicciNormSqAt
    (D : RicciFlowData k R V Time A) (nInv : R) (t : Time) : R :=
  tracefree_ricci_norm_sq D.emb (D.conn_fam t) (D.ha_fam t) (D.hal_fam t)
    (D.hsl_fam t) (D.hl_fam t) D.atr (D.g_fam t) nInv

/-- Concrete point-selection hypothesis: the scalar quantity is unbounded above
on the supplied spacetime domain. -/
def PointSelectionHypothesis (Point : Type*)
    (scalarQuantity : RicciFlowData k R V Time A -> Point -> Time -> R)
    (domain : RicciFlowData k R V Time A -> Point -> Time -> Prop)
    (D : RicciFlowData k R V Time A) : Prop :=
  forall C, exists p t, domain D p t /\ C <= scalarQuantity D p t

/-- Bridge from a time-only scalar unboundedness statement to the spacetime
point-selection hypothesis. In concrete geometry this is where compactness and
continuity provide spatial points realizing large scalar curvature. -/
class ScalarSpatialPromotionFromTime (Point : Type*)
    (timeScalarQuantity : RicciFlowData k R V Time A -> Time -> R)
    (spaceScalarQuantity : RicciFlowData k R V Time A -> Point -> Time -> R)
    (timeDomain : RicciFlowData k R V Time A -> Time -> Prop)
    (spaceDomain : RicciFlowData k R V Time A -> Point -> Time -> Prop) where
  promote :
    forall D : RicciFlowData k R V Time A,
      UnboundedAboveOn (timeScalarQuantity D) (timeDomain D) ->
        PointSelectionHypothesis k R V Time A Point spaceScalarQuantity spaceDomain D

theorem point_selection_hypothesis_from_time_unbounded
    {Point : Type*}
    {timeScalarQuantity : RicciFlowData k R V Time A -> Time -> R}
    {spaceScalarQuantity : RicciFlowData k R V Time A -> Point -> Time -> R}
    {timeDomain : RicciFlowData k R V Time A -> Time -> Prop}
    {spaceDomain : RicciFlowData k R V Time A -> Point -> Time -> Prop}
    [H : ScalarSpatialPromotionFromTime k R V Time A Point
      timeScalarQuantity spaceScalarQuantity timeDomain spaceDomain]
    (D : RicciFlowData k R V Time A)
    (h : UnboundedAboveOn (timeScalarQuantity D) (timeDomain D)) :
    PointSelectionHypothesis k R V Time A Point spaceScalarQuantity spaceDomain D :=
  H.promote D h

/-- Parabolic rescaling data selected near a singular time, as in Lemma 11.4.

The predicates are tied to concrete scalar and pinching-ratio quantities. The
realization layer still chooses the point set and spacetime domain, but these
fields are no longer name-only `Prop` placeholders. -/
structure ParabolicRescalingData (Point Index : Type*) where
  original : RicciFlowData k R V Time A
  point : Index -> Point
  time : Index -> Time
  scale : Index -> R
  rescaled : Index -> RicciFlowData k R V Time A
  scalarQuantity : RicciFlowData k R V Time A -> Point -> Time -> R
  pinchingRatio : RicciFlowData k R V Time A -> Point -> Time -> R
  pinchingDecayQuantity : RicciFlowData k R V Time A -> Point -> Time -> R
  pinchingDecayFactor : Index -> R
  backwardRegion : Index -> Point -> Time -> Prop
  scale_tends_to_infinity : UnboundedAboveOn scale (fun _ => True)
  normalized_scalar_at_base :
    forall i, scalarQuantity (rescaled i) (point i) (time i) = 1
  scalar_max_on_backward_interval :
    forall i p t, backwardRegion i p t -> scalarQuantity original p t <= scale i
  scale_invariant_pinching_ratio_preserved :
    forall i, pinchingRatio (rescaled i) (point i) (time i) =
      pinchingRatio original (point i) (time i)
  /-- Quantitative rescaling rule used in Section 12 after the improved
  pinching estimate: the scale-invariant ratio on the normalized flow is
  bounded by a scale-decay factor times the improved pinching quantity on the
  original flow. In concrete coordinates this factor is the `R_i^{-epsilon}`
  term. -/
  pinching_ratio_decay_rule_at_base :
    forall i, pinchingRatio (rescaled i) (point i) (time i) =
      pinchingDecayFactor i * pinchingDecayQuantity original (point i) (time i)
  /-- Region-wise version used by later limit arguments when the full
  backward parabolic neighborhood, not only the selected base point, is needed. -/
  scale_invariant_pinching_ratio_preserved_on_backward_region :
    forall i p t, backwardRegion i p t ->
      pinchingRatio (rescaled i) p t = pinchingRatio original p t

/-- Black-box form of Lemma 11.4: point selection and scalar normalization. -/
class PointSelectionAndRescalingTheorem (Point Index : Type*) where
  scalarQuantity : RicciFlowData k R V Time A -> Point -> Time -> R
  domain : RicciFlowData k R V Time A -> Point -> Time -> Prop
  pinchingRatio : RicciFlowData k R V Time A -> Point -> Time -> R
  pinchingDecayQuantity : RicciFlowData k R V Time A -> Point -> Time -> R
  pinchingDecayFactor : Index -> R
  selection :
    forall D : RicciFlowData k R V Time A,
      PointSelectionHypothesis k R V Time A Point scalarQuantity domain D ->
        Nonempty { data : ParabolicRescalingData k R V Time A Point Index //
          data.original = D /\ data.scalarQuantity = scalarQuantity /\
            data.pinchingRatio = pinchingRatio /\
            data.pinchingDecayQuantity = pinchingDecayQuantity /\
            data.pinchingDecayFactor = pinchingDecayFactor }

theorem point_selection_rescaling_from_interface
    {Point Index : Type*} [H : PointSelectionAndRescalingTheorem k R V Time A Point Index]
    (D : RicciFlowData k R V Time A)
    (hD : PointSelectionHypothesis k R V Time A Point H.scalarQuantity H.domain D) :
    Nonempty { data : ParabolicRescalingData k R V Time A Point Index //
      data.original = D /\ data.scalarQuantity = H.scalarQuantity /\
        data.pinchingRatio = H.pinchingRatio /\
        data.pinchingDecayQuantity = H.pinchingDecayQuantity /\
        data.pinchingDecayFactor = H.pinchingDecayFactor } :=
  H.selection D hD

/-- Candidate compactness limit. -/
structure RicciFlowLimitCandidate where
  flow : RicciFlowData k R V Time A

/-- Smooth pointed Cheeger-Gromov-Hamilton convergence data. -/
structure SmoothCGHConvergenceData (Index : Type*) where
  sequence : PointedRicciFlowSequence k R V Time A Index
  limit : RicciFlowLimitCandidate k R V Time A
  smoothConvergesTo :
    (Index -> RicciFlowData k R V Time A) -> RicciFlowData k R V Time A -> Prop
  smoothConvergence :
    ConvergenceWitness Index (RicciFlowData k R V Time A) smoothConvergesTo
  smooth_seq_eq : smoothConvergence.seq = sequence.flow
  smooth_limit_eq : smoothConvergence.limit = limit.flow

/-- Shared convergence profile for curvature quantities extracted from smooth
CGH convergence. A concrete realization should eventually replace these
relations by `Filter.Tendsto` statements for the chosen topology/filter. -/
structure CurvatureConvergenceProfile (Index : Type*) where
  riemannConvergesTo :
    (Index -> TensorData R V 1 3) -> TensorData R V 1 3 -> Prop
  ricciConvergesTo :
    (Index -> TensorData R V 0 2) -> TensorData R V 0 2 -> Prop
  scalarConvergesTo : (Index -> R) -> R -> Prop
  eventually : (Index -> Prop) -> Prop

/-- Squeeze a scalar convergence witness to zero using the convergence profile's
shared scalar topology and eventuality relation. -/
theorem scalar_convergence_witness_limit_eq_zero_of_squeeze
    {Index : Type*}
    (profile : CurvatureConvergenceProfile R V Index)
    [H : ScalarConvergenceSqueezeToZero Index R profile.scalarConvergesTo profile.eventually]
    (w : ConvergenceWitness Index R profile.scalarConvergesTo)
    (upper : Index -> R)
    (hupper : profile.scalarConvergesTo upper 0)
    (hnonneg : profile.eventually (fun i => 0 <= w.seq i))
    (hle : profile.eventually (fun i => w.seq i <= upper i)) :
    w.limit = 0 :=
  H.squeeze_to_zero w.converges hupper hnonneg hle

/-- Curvature convergence conclusions from smooth CGH convergence, Lemma 11.5. -/
structure CurvatureConvergenceConclusion (Index : Type*) where
  sequence : PointedRicciFlowSequence k R V Time A Index
  limit : RicciFlowLimitCandidate k R V Time A
  time : Index -> Time
  limitTime : Time
  nInv : R
  profile : CurvatureConvergenceProfile R V Index
  riemann : ConvergenceWitness Index (TensorData R V 1 3) profile.riemannConvergesTo
  riemann_seq_eq :
    riemann.seq = fun i => ricciFlowRiemannTensorAt k R V Time A (sequence.flow i) (time i)
  riemann_limit_eq :
    riemann.limit = ricciFlowRiemannTensorAt k R V Time A limit.flow limitTime
  ricci : ConvergenceWitness Index (TensorData R V 0 2) profile.ricciConvergesTo
  ricci_seq_eq :
    ricci.seq = fun i => ricciFlowRicciTensorAt k R V Time A (sequence.flow i) (time i)
  ricci_limit_eq :
    ricci.limit = ricciFlowRicciTensorAt k R V Time A limit.flow limitTime
  scalar : ConvergenceWitness Index R profile.scalarConvergesTo
  scalar_seq_eq :
    scalar.seq = fun i => ricciFlowScalarCurvatureAt k R V Time A (sequence.flow i) (time i)
  scalar_limit_eq :
    scalar.limit = ricciFlowScalarCurvatureAt k R V Time A limit.flow limitTime
  riemann_norm_sq : ConvergenceWitness Index R profile.scalarConvergesTo
  /-- Temporary hook for `|Rm|^2` convergence. This should become a canonical
  synthetic Riemann norm accessor once that tensor norm is available. -/
  riemann_norm_sq_quantity : RicciFlowData k R V Time A -> Time -> R
  riemann_norm_sq_seq_eq :
    riemann_norm_sq.seq = fun i => riemann_norm_sq_quantity (sequence.flow i) (time i)
  riemann_norm_sq_limit_eq :
    riemann_norm_sq.limit = riemann_norm_sq_quantity limit.flow limitTime
  ricci_norm_sq : ConvergenceWitness Index R profile.scalarConvergesTo
  ricci_norm_sq_seq_eq :
    ricci_norm_sq.seq = fun i => ricciFlowRicciNormSqAt k R V Time A (sequence.flow i) (time i)
  ricci_norm_sq_limit_eq :
    ricci_norm_sq.limit = ricciFlowRicciNormSqAt k R V Time A limit.flow limitTime
  tracefree_ricci_norm_sq : ConvergenceWitness Index R profile.scalarConvergesTo
  tracefree_ricci_norm_sq_seq_eq :
    tracefree_ricci_norm_sq.seq =
      fun i => ricciFlowTracefreeRicciNormSqAt k R V Time A (sequence.flow i) nInv (time i)
  tracefree_ricci_norm_sq_limit_eq :
    tracefree_ricci_norm_sq.limit =
      ricciFlowTracefreeRicciNormSqAt k R V Time A limit.flow nInv limitTime

/-- If the scalar samples in a curvature-convergence conclusion are the
constant sequence `c`, and the chosen scalar convergence relation has unique
limits for that sequence, then the limit scalar sample is `c`. This is the
abstract version of `R(g_i)(x_i,0)=1` passing to
`R(g_infty)(x_infty,0)=1`. -/
theorem scalar_limit_eq_of_constant_samples
    {Index : Type*}
    (conclusion : CurvatureConvergenceConclusion k R V Time A Index)
    (c : R)
    (hseq : conclusion.scalar.seq = fun _ => c)
    (hconst : conclusion.profile.scalarConvergesTo (fun _ => c) c)
    (hunique :
      forall (seq : Index -> R) (a b : R),
        conclusion.profile.scalarConvergesTo seq a ->
        conclusion.profile.scalarConvergesTo seq b -> a = b) :
    conclusion.scalar.limit = c := by
  have hconv :
      conclusion.profile.scalarConvergesTo (fun _ => c) conclusion.scalar.limit := by
    simpa [hseq] using conclusion.scalar.converges
  exact hunique (fun _ => c) conclusion.scalar.limit c hconv hconst

/-- Section 12 scalar-normalization transfer. If the scalar samples in the
curvature-convergence conclusion are the normalized basepoint scalars from a
parabolic rescaling, then the limit scalar sample is `1`. The hypothesis
`hscalar_sample` is the realization bridge identifying the pointwise scalar
quantity used in point selection with the synthetic scalar sample in the
curvature-convergence profile. -/
theorem scalar_limit_eq_one_from_rescaling_curvature_convergence
    {Point Index : Type*}
    (rescaling : ParabolicRescalingData k R V Time A Point Index)
    (conclusion : CurvatureConvergenceConclusion k R V Time A Index)
    (hsequence : conclusion.sequence.flow = rescaling.rescaled)
    (htime : conclusion.time = rescaling.time)
    (hscalar_sample : forall i,
      ricciFlowScalarCurvatureAt k R V Time A (rescaling.rescaled i) (rescaling.time i) =
        rescaling.scalarQuantity (rescaling.rescaled i) (rescaling.point i) (rescaling.time i))
    (hconst : conclusion.profile.scalarConvergesTo (fun _ => (1 : R)) 1)
    (hunique :
      forall (seq : Index -> R) (a b : R),
        conclusion.profile.scalarConvergesTo seq a ->
        conclusion.profile.scalarConvergesTo seq b -> a = b) :
    ricciFlowScalarCurvatureAt k R V Time A conclusion.limit.flow conclusion.limitTime = 1 := by
  have hseq : conclusion.scalar.seq = fun _ => (1 : R) := by
    rw [conclusion.scalar_seq_eq]
    funext i
    rw [hsequence, htime, hscalar_sample i, rescaling.normalized_scalar_at_base i]
  have hlim := scalar_limit_eq_of_constant_samples k R V Time A conclusion 1 hseq hconst hunique
  rwa [conclusion.scalar_limit_eq] at hlim

/-- P9-facing name for the Section 12 scalar-normalization transfer from CGH
curvature convergence. -/
theorem limit_scalar_normalized_from_cgh_convergence
    {Point Index : Type*}
    (rescaling : ParabolicRescalingData k R V Time A Point Index)
    (conclusion : CurvatureConvergenceConclusion k R V Time A Index)
    (hsequence : conclusion.sequence.flow = rescaling.rescaled)
    (htime : conclusion.time = rescaling.time)
    (hscalar_sample : forall i,
      ricciFlowScalarCurvatureAt k R V Time A (rescaling.rescaled i) (rescaling.time i) =
        rescaling.scalarQuantity (rescaling.rescaled i) (rescaling.point i) (rescaling.time i))
    (hconst : conclusion.profile.scalarConvergesTo (fun _ => (1 : R)) 1)
    (hunique :
      forall (seq : Index -> R) (a b : R),
        conclusion.profile.scalarConvergesTo seq a ->
        conclusion.profile.scalarConvergesTo seq b -> a = b) :
    ricciFlowScalarCurvatureAt k R V Time A conclusion.limit.flow conclusion.limitTime = 1 :=
  scalar_limit_eq_one_from_rescaling_curvature_convergence k R V Time A
    rescaling conclusion hsequence htime hscalar_sample hconst hunique

/-- Black-box form of Lemma 11.5: smooth CGH convergence implies smooth
convergence of curvature and its contractions/norms. -/
class CurvatureConvergenceUnderSmoothCGH (Index : Type*) where
  profile : CurvatureConvergenceProfile R V Index
  curvature_convergence :
    forall data : SmoothCGHConvergenceData k R V Time A Index,
      Nonempty { conclusion : CurvatureConvergenceConclusion k R V Time A Index //
        conclusion.sequence = data.sequence /\ conclusion.limit = data.limit /\
          conclusion.profile = profile }

@[reducible] def cgh_curvature_convergence_from_interface
    {Index : Type*} [H : CurvatureConvergenceUnderSmoothCGH k R V Time A Index]
    (data : SmoothCGHConvergenceData k R V Time A Index) :
    Nonempty { conclusion : CurvatureConvergenceConclusion k R V Time A Index //
      conclusion.sequence = data.sequence /\ conclusion.limit = data.limit /\
        conclusion.profile = H.profile } :=
  H.curvature_convergence data

/-- Curvature-ratio convergence conclusion following Lemma 11.5. -/
structure CurvatureRatioConvergenceConclusion (Index : Type*) where
  curvature : CurvatureConvergenceConclusion k R V Time A Index
  scalar_positive_eventually :
    EventuallyPositiveWitness Index R curvature.profile.eventually
  scalar_positive_seq_eq :
    scalar_positive_eventually.scalar = curvature.scalar.seq
  tracefree_ratio : ConvergenceWitness Index R curvature.profile.scalarConvergesTo
  ratioQuantity : RicciFlowData k R V Time A -> Time -> R
  ratio_seq_eq :
    tracefree_ratio.seq =
      fun i => ratioQuantity (curvature.sequence.flow i) (curvature.time i)
  ratio_limit_eq :
    tracefree_ratio.limit = ratioQuantity curvature.limit.flow curvature.limitTime
  ratio_relation :
    forall D t,
      ricciFlowScalarCurvatureAt k R V Time A D t *
          ricciFlowScalarCurvatureAt k R V Time A D t *
          ratioQuantity D t =
        ricciFlowTracefreeRicciNormSqAt k R V Time A D curvature.nInv t

/-- Section 12 squeeze step for the trace-free Ricci ratio. Once the ratio
sequence from CGH convergence is eventually nonnegative and eventually bounded
above by a zero-convergent upper-bound sequence, its CGH limit is zero. -/
theorem tracefree_ratio_limit_eq_zero_of_squeeze
    {Index : Type*}
    (conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index)
    [H : ScalarConvergenceSqueezeToZero Index R
      conclusion.curvature.profile.scalarConvergesTo
      conclusion.curvature.profile.eventually]
    (upper : Index -> R)
    (hupper : conclusion.curvature.profile.scalarConvergesTo upper 0)
    (hnonneg : conclusion.curvature.profile.eventually
      (fun i => 0 <= conclusion.tracefree_ratio.seq i))
    (hle : conclusion.curvature.profile.eventually
      (fun i => conclusion.tracefree_ratio.seq i <= upper i)) :
    conclusion.tracefree_ratio.limit = 0 :=
  scalar_convergence_witness_limit_eq_zero_of_squeeze (R := R) (V := V)
    conclusion.curvature.profile conclusion.tracefree_ratio upper hupper hnonneg hle

/-- Same squeeze step, rewritten through the canonical ratio quantity on the
CGH limit flow. -/
theorem tracefree_ratio_quantity_limit_eq_zero_of_squeeze
    {Index : Type*}
    (conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index)
    [H : ScalarConvergenceSqueezeToZero Index R
      conclusion.curvature.profile.scalarConvergesTo
      conclusion.curvature.profile.eventually]
    (upper : Index -> R)
    (hupper : conclusion.curvature.profile.scalarConvergesTo upper 0)
    (hnonneg : conclusion.curvature.profile.eventually
      (fun i => 0 <= conclusion.tracefree_ratio.seq i))
    (hle : conclusion.curvature.profile.eventually
      (fun i => conclusion.tracefree_ratio.seq i <= upper i)) :
    conclusion.ratioQuantity conclusion.curvature.limit.flow conclusion.curvature.limitTime = 0 := by
  have h := tracefree_ratio_limit_eq_zero_of_squeeze k R V Time A conclusion
    upper hupper hnonneg hle
  rwa [conclusion.ratio_limit_eq] at h

/-- If the scale-invariant trace-free Ricci ratio vanishes on the CGH limit,
then the synthetic trace-free Ricci norm squared vanishes there. This uses the
ratio relation
`R^2 * ratio = |Ric^0|^2`; no division or scalar-positivity hypothesis is
needed in this direction. -/
theorem limit_tracefree_ricci_norm_sq_eq_zero_of_ratio_limit_zero
    {Index : Type*}
    (conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index)
    (hratio :
      conclusion.ratioQuantity conclusion.curvature.limit.flow conclusion.curvature.limitTime = 0) :
    ricciFlowTracefreeRicciNormSqAt k R V Time A conclusion.curvature.limit.flow
      conclusion.curvature.nInv conclusion.curvature.limitTime = 0 := by
  have hrel := conclusion.ratio_relation conclusion.curvature.limit.flow
    conclusion.curvature.limitTime
  rw [hratio, mul_zero] at hrel
  exact hrel.symm

/-- Combined Section 12 consequence of the improved-pinching squeeze:
eventual nonnegativity, an eventual zero-convergent upper bound, and ratio
convergence force `|Ric^0|^2 = 0` on the CGH limit sample. -/
theorem limit_tracefree_ricci_norm_sq_eq_zero_of_squeezed_ratio
    {Index : Type*}
    (conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index)
    [H : ScalarConvergenceSqueezeToZero Index R
      conclusion.curvature.profile.scalarConvergesTo
      conclusion.curvature.profile.eventually]
    (upper : Index -> R)
    (hupper : conclusion.curvature.profile.scalarConvergesTo upper 0)
    (hnonneg : conclusion.curvature.profile.eventually
      (fun i => 0 <= conclusion.tracefree_ratio.seq i))
    (hle : conclusion.curvature.profile.eventually
      (fun i => conclusion.tracefree_ratio.seq i <= upper i)) :
    ricciFlowTracefreeRicciNormSqAt k R V Time A conclusion.curvature.limit.flow
      conclusion.curvature.nInv conclusion.curvature.limitTime = 0 :=
  limit_tracefree_ricci_norm_sq_eq_zero_of_ratio_limit_zero k R V Time A conclusion
    (tracefree_ratio_quantity_limit_eq_zero_of_squeeze k R V Time A conclusion
      upper hupper hnonneg hle)

end CompactnessInterfaces

section GeometricCompactnessInterfaces

variable (k R V Time A Manifold Point Metric : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- A sequence of pointed geometric Ricci flows. -/
structure GeometricPointedRicciFlowSequence (Index : Type*) where
  flow : Index -> GeometricFlow k R V Time A Manifold Point Metric

/-- Geometric point-selection hypothesis: a pointwise scalar quantity is
unbounded above on a spacetime domain. -/
def GeometricPointSelectionHypothesis
    (scalarQuantity :
      GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> R)
    (domain :
      GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> Prop)
    (G : GeometricFlow k R V Time A Manifold Point Metric) : Prop :=
  UnboundedAboveOnSpacetime (scalarQuantity G) (domain G)

/-- Parabolic rescaling data selected near a singular time in the geometric
layer. The original and rescaled flows carry their own manifolds and metrics. -/
structure GeometricParabolicRescalingData (Index : Type*) where
  original : GeometricFlow k R V Time A Manifold Point Metric
  point : Index -> Point
  time : Index -> Time
  scale : Index -> R
  rescaled : Index -> GeometricFlow k R V Time A Manifold Point Metric
  scalarQuantity :
    GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> R
  pinchingRatio :
    GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> R
  pinchingDecayQuantity :
    GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> R
  pinchingDecayFactor : Index -> R
  backwardRegion : Index -> Point -> Time -> Prop
  scale_tends_to_infinity : UnboundedAboveOn scale (fun _ => True)
  normalized_scalar_at_base :
    forall i, scalarQuantity (rescaled i) (point i) (time i) = 1
  scalar_max_on_backward_interval :
    forall i p t, backwardRegion i p t -> scalarQuantity original p t <= scale i
  scale_invariant_pinching_ratio_preserved :
    forall i, pinchingRatio (rescaled i) (point i) (time i) =
      pinchingRatio original (point i) (time i)
  pinching_ratio_decay_rule_at_base :
    forall i, pinchingRatio (rescaled i) (point i) (time i) =
      pinchingDecayFactor i * pinchingDecayQuantity original (point i) (time i)
  scale_invariant_pinching_ratio_preserved_on_backward_region :
    forall i p t, backwardRegion i p t ->
      pinchingRatio (rescaled i) p t = pinchingRatio original p t

/-- Geometric form of point selection and parabolic rescaling. -/
class GeometricPointSelectionAndRescalingTheorem (Index : Type*) where
  scalarQuantity :
    GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> R
  domain :
    GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> Prop
  pinchingRatio :
    GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> R
  pinchingDecayQuantity :
    GeometricFlow k R V Time A Manifold Point Metric -> Point -> Time -> R
  pinchingDecayFactor : Index -> R
  selection :
    forall G : GeometricFlow k R V Time A Manifold Point Metric,
      GeometricPointSelectionHypothesis k R V Time A Manifold Point Metric
        scalarQuantity domain G ->
        Nonempty { data :
            GeometricParabolicRescalingData k R V Time A Manifold Point Metric Index //
          data.original = G /\ data.scalarQuantity = scalarQuantity /\
            data.pinchingRatio = pinchingRatio /\
            data.pinchingDecayQuantity = pinchingDecayQuantity /\
            data.pinchingDecayFactor = pinchingDecayFactor }

theorem geometric_point_selection_rescaling_from_interface
    {Index : Type*}
    [H : GeometricPointSelectionAndRescalingTheorem
      k R V Time A Manifold Point Metric Index]
    (G : GeometricFlow k R V Time A Manifold Point Metric)
    (hG :
      GeometricPointSelectionHypothesis k R V Time A Manifold Point Metric
        H.scalarQuantity H.domain G) :
    Nonempty { data :
        GeometricParabolicRescalingData k R V Time A Manifold Point Metric Index //
      data.original = G /\ data.scalarQuantity = H.scalarQuantity /\
        data.pinchingRatio = H.pinchingRatio /\
        data.pinchingDecayQuantity = H.pinchingDecayQuantity /\
        data.pinchingDecayFactor = H.pinchingDecayFactor } :=
  H.selection G hG

/-- Candidate compactness limit for geometric Ricci flows. -/
structure GeometricRicciFlowLimitCandidate where
  flow : GeometricFlow k R V Time A Manifold Point Metric

/-- Smooth pointed Cheeger-Gromov-Hamilton convergence data in the geometric
layer. The limit and sequence flows already contain their manifolds. -/
structure GeometricSmoothCGHConvergenceData (Index : Type*) where
  sequence : GeometricPointedRicciFlowSequence k R V Time A Manifold Point Metric Index
  limit : GeometricRicciFlowLimitCandidate k R V Time A Manifold Point Metric
  smoothConvergesTo :
    (Index -> GeometricFlow k R V Time A Manifold Point Metric) ->
      GeometricFlow k R V Time A Manifold Point Metric -> Prop
  smoothConvergence :
    ConvergenceWitness Index
      (GeometricFlow k R V Time A Manifold Point Metric) smoothConvergesTo
  smooth_seq_eq : smoothConvergence.seq = sequence.flow
  smooth_limit_eq : smoothConvergence.limit = limit.flow

/-- Hamilton-Cheeger-Gromov compactness in the geometric layer. -/
class GeometricHamiltonCompactnessTheorem (Index : Type*) where
  extract_limit :
    forall sequence :
        GeometricPointedRicciFlowSequence k R V Time A Manifold Point Metric Index,
      Nonempty { data :
          GeometricSmoothCGHConvergenceData k R V Time A Manifold Point Metric Index //
        data.sequence = sequence }

/-- Compact-limit diffeomorphism conclusion for geometric CGH convergence.
There is no `manifoldOfFlow` field: each geometric flow carries its manifold. -/
structure GeometricCompactLimitDiffeomorphismConclusion
    (Index Diffeomorphism : Type*) where
  sequence : GeometricPointedRicciFlowSequence k R V Time A Manifold Point Metric Index
  limit : GeometricRicciFlowLimitCandidate k R V Time A Manifold Point Metric
  eventually : (Index -> Prop) -> Prop
  diffeomorphism : Index -> Diffeomorphism
  isDiffeomorphism : Diffeomorphism -> Manifold -> Manifold -> Prop
  eventually_diffeomorphic :
    eventually (fun i =>
      isDiffeomorphism (diffeomorphism i)
        (sequence.flow i).manifold limit.flow.manifold)

/-- Compact-limit diffeomorphism interface in the geometric layer. -/
class GeometricCompactLimitDiffeomorphismUnderSmoothCGH
    (Index Diffeomorphism : Type*) where
  IsCompact : Manifold -> Prop
  eventually : (Index -> Prop) -> Prop
  IsDiffeomorphism : Diffeomorphism -> Manifold -> Manifold -> Prop
  diffeomorphic_for_large_i :
    forall data :
        GeometricSmoothCGHConvergenceData k R V Time A Manifold Point Metric Index,
      IsCompact data.limit.flow.manifold ->
        Nonempty { conclusion :
            GeometricCompactLimitDiffeomorphismConclusion
              k R V Time A Manifold Point Metric Index Diffeomorphism //
          conclusion.sequence = data.sequence /\ conclusion.limit = data.limit /\
            conclusion.eventually = eventually /\
            conclusion.isDiffeomorphism = IsDiffeomorphism }

theorem geometric_compact_limit_diffeomorphism_from_interface
    {Index Diffeomorphism : Type*}
    [H : GeometricCompactLimitDiffeomorphismUnderSmoothCGH
      k R V Time A Manifold Point Metric Index Diffeomorphism]
    (data : GeometricSmoothCGHConvergenceData k R V Time A Manifold Point Metric Index)
    (hcompact : H.IsCompact data.limit.flow.manifold) :
    Nonempty { conclusion :
        GeometricCompactLimitDiffeomorphismConclusion
          k R V Time A Manifold Point Metric Index Diffeomorphism //
      conclusion.sequence = data.sequence /\ conclusion.limit = data.limit /\
        conclusion.eventually = H.eventually /\
        conclusion.isDiffeomorphism = H.IsDiffeomorphism } :=
  H.diffeomorphic_for_large_i data hcompact

end GeometricCompactnessInterfaces

section IntervalGeometricCompactnessInterfaces

variable (k R V FlowTime AmbientTime A Manifold Point Metric : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- A sequence of pointed interval-aware geometric Ricci flows. -/
structure IntervalGeometricPointedRicciFlowSequence (Index : Type*) where
  flow :
    Index ->
      IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric

/-- Interval-aware point-selection hypothesis: a pointwise scalar quantity is
unbounded above on a regular spacetime domain. -/
def IntervalGeometricPointSelectionHypothesis
    (scalarQuantity :
      IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
        Point -> FlowTime -> R)
    (domain :
      IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
        Point -> FlowTime -> Prop)
    (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric) :
    Prop :=
  UnboundedAboveOnSpacetime (scalarQuantity G) (domain G)

/-- Parabolic rescaling data selected near an ambient singular time. The
selected times and backward regions use only regular `FlowTime`s. -/
structure IntervalGeometricParabolicRescalingData (Index : Type*) where
  original :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric
  point : Index -> Point
  time : Index -> FlowTime
  scale : Index -> R
  rescaled :
    Index ->
      IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric
  scalarQuantity :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> R
  pinchingRatio :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> R
  pinchingDecayQuantity :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> R
  pinchingDecayFactor : Index -> R
  backwardRegion : Index -> Point -> FlowTime -> Prop
  scale_tends_to_infinity : UnboundedAboveOn scale (fun _ => True)
  normalized_scalar_at_base :
    forall i, scalarQuantity (rescaled i) (point i) (time i) = 1
  scalar_max_on_backward_interval :
    forall i p t, backwardRegion i p t -> scalarQuantity original p t <= scale i
  scale_invariant_pinching_ratio_preserved :
    forall i, pinchingRatio (rescaled i) (point i) (time i) =
      pinchingRatio original (point i) (time i)
  pinching_ratio_decay_rule_at_base :
    forall i, pinchingRatio (rescaled i) (point i) (time i) =
      pinchingDecayFactor i * pinchingDecayQuantity original (point i) (time i)
  scale_invariant_pinching_ratio_preserved_on_backward_region :
    forall i p t, backwardRegion i p t ->
      pinchingRatio (rescaled i) p t = pinchingRatio original p t

/-- Interval-aware form of point selection and parabolic rescaling. -/
class IntervalGeometricPointSelectionAndRescalingTheorem (Index : Type*) where
  scalarQuantity :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> R
  domain :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> Prop
  pinchingRatio :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> R
  pinchingDecayQuantity :
    IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric ->
      Point -> FlowTime -> R
  pinchingDecayFactor : Index -> R
  selection :
    forall G :
        IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric,
      IntervalGeometricPointSelectionHypothesis
        k R V FlowTime AmbientTime A Manifold Point Metric scalarQuantity domain G ->
        Nonempty { data :
            IntervalGeometricParabolicRescalingData
              k R V FlowTime AmbientTime A Manifold Point Metric Index //
          data.original = G /\ data.scalarQuantity = scalarQuantity /\
            data.pinchingRatio = pinchingRatio /\
            data.pinchingDecayQuantity = pinchingDecayQuantity /\
            data.pinchingDecayFactor = pinchingDecayFactor }

theorem interval_geometric_point_selection_rescaling_from_interface
    {Index : Type*}
    [H : IntervalGeometricPointSelectionAndRescalingTheorem
      k R V FlowTime AmbientTime A Manifold Point Metric Index]
    (G : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
    (hG :
      IntervalGeometricPointSelectionHypothesis
        k R V FlowTime AmbientTime A Manifold Point Metric
        H.scalarQuantity H.domain G) :
    Nonempty { data :
        IntervalGeometricParabolicRescalingData
          k R V FlowTime AmbientTime A Manifold Point Metric Index //
      data.original = G /\ data.scalarQuantity = H.scalarQuantity /\
        data.pinchingRatio = H.pinchingRatio /\
        data.pinchingDecayQuantity = H.pinchingDecayQuantity /\
        data.pinchingDecayFactor = H.pinchingDecayFactor } :=
  H.selection G hG

/-- Candidate compactness limit for interval-aware geometric Ricci flows. -/
structure IntervalGeometricRicciFlowLimitCandidate where
  flow : IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric

/-- Smooth pointed Cheeger-Gromov-Hamilton convergence data in the
interval-aware geometric layer. The sequence and limit flows carry their own
manifolds and ambient interval data. -/
structure IntervalGeometricSmoothCGHConvergenceData (Index : Type*) where
  sequence :
    IntervalGeometricPointedRicciFlowSequence
      k R V FlowTime AmbientTime A Manifold Point Metric Index
  limit :
    IntervalGeometricRicciFlowLimitCandidate
      k R V FlowTime AmbientTime A Manifold Point Metric
  smoothConvergesTo :
    (Index ->
      IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric) ->
      IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric -> Prop
  smoothConvergence :
    ConvergenceWitness Index
      (IntervalGeometricFlow k R V FlowTime AmbientTime A Manifold Point Metric)
      smoothConvergesTo
  smooth_seq_eq : smoothConvergence.seq = sequence.flow
  smooth_limit_eq : smoothConvergence.limit = limit.flow

/-- Hamilton-Cheeger-Gromov compactness in the interval-aware geometric layer. -/
class IntervalGeometricHamiltonCompactnessTheorem (Index : Type*) where
  extract_limit :
    forall sequence :
        IntervalGeometricPointedRicciFlowSequence
          k R V FlowTime AmbientTime A Manifold Point Metric Index,
      Nonempty { data :
          IntervalGeometricSmoothCGHConvergenceData
            k R V FlowTime AmbientTime A Manifold Point Metric Index //
        data.sequence = sequence }

/-- Compact-limit diffeomorphism conclusion for interval-aware CGH convergence.
There is no `manifoldOfFlow` field: each flow stores its manifold. -/
structure IntervalGeometricCompactLimitDiffeomorphismConclusion
    (Index Diffeomorphism : Type*) where
  sequence :
    IntervalGeometricPointedRicciFlowSequence
      k R V FlowTime AmbientTime A Manifold Point Metric Index
  limit :
    IntervalGeometricRicciFlowLimitCandidate
      k R V FlowTime AmbientTime A Manifold Point Metric
  eventually : (Index -> Prop) -> Prop
  diffeomorphism : Index -> Diffeomorphism
  isDiffeomorphism : Diffeomorphism -> Manifold -> Manifold -> Prop
  eventually_diffeomorphic :
    eventually (fun i =>
      isDiffeomorphism (diffeomorphism i)
        (sequence.flow i).manifold limit.flow.manifold)

/-- Compact-limit diffeomorphism interface in the interval-aware geometric
layer. -/
class IntervalGeometricCompactLimitDiffeomorphismUnderSmoothCGH
    (Index Diffeomorphism : Type*) where
  IsCompact : Manifold -> Prop
  eventually : (Index -> Prop) -> Prop
  IsDiffeomorphism : Diffeomorphism -> Manifold -> Manifold -> Prop
  diffeomorphic_for_large_i :
    forall data :
        IntervalGeometricSmoothCGHConvergenceData
          k R V FlowTime AmbientTime A Manifold Point Metric Index,
      IsCompact data.limit.flow.manifold ->
        Nonempty { conclusion :
            IntervalGeometricCompactLimitDiffeomorphismConclusion
              k R V FlowTime AmbientTime A Manifold Point Metric Index Diffeomorphism //
          conclusion.sequence = data.sequence /\ conclusion.limit = data.limit /\
            conclusion.eventually = eventually /\
            conclusion.isDiffeomorphism = IsDiffeomorphism }

theorem interval_geometric_compact_limit_diffeomorphism_from_interface
    {Index Diffeomorphism : Type*}
    [H : IntervalGeometricCompactLimitDiffeomorphismUnderSmoothCGH
      k R V FlowTime AmbientTime A Manifold Point Metric Index Diffeomorphism]
    (data :
      IntervalGeometricSmoothCGHConvergenceData
        k R V FlowTime AmbientTime A Manifold Point Metric Index)
    (hcompact : H.IsCompact data.limit.flow.manifold) :
    Nonempty { conclusion :
        IntervalGeometricCompactLimitDiffeomorphismConclusion
          k R V FlowTime AmbientTime A Manifold Point Metric Index Diffeomorphism //
      conclusion.sequence = data.sequence /\ conclusion.limit = data.limit /\
        conclusion.eventually = H.eventually /\
        conclusion.isDiffeomorphism = H.IsDiffeomorphism } :=
  H.diffeomorphic_for_large_i data hcompact

end IntervalGeometricCompactnessInterfaces

section ImprovedPinchingCompactnessBridge

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Sample-level Section 12 bridge from the improved pinching estimate to
vanishing of `|Ric^0|^2` on the CGH limit sample.

Here the improved pinching estimate is indexed by the same `Index` as the CGH
sequence. The hypotheses `hratio_seq`, `hdomain`, and `hupper` are the
realization/decay links: the CGH ratio sequence is the improved-pinching ratio,
the selected samples eventually lie in the pinching domain, and the decay upper
sequence `C * decay_i` converges to zero. -/
theorem limit_tracefree_ricci_norm_sq_eq_zero_of_improved_pinching_decay
    {Index : Type*}
    (conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index)
    [Hsq : ScalarConvergenceSqueezeToZero Index R
      conclusion.curvature.profile.scalarConvergesTo
      conclusion.curvature.profile.eventually]
    [Hev : EventuallyImp Index conclusion.curvature.profile.eventually]
    (E : ImprovedRicciPinchingEstimateAlongFlow (R := R) (Time := Index))
    (hratio_seq : conclusion.tracefree_ratio.seq = E.ratio)
    (hdomain : conclusion.curvature.profile.eventually (fun i => E.problem.domain i))
    (hpinching_bound : forall i, E.problem.domain i -> E.ratio i <= E.C * E.decay i)
    (hupper :
      conclusion.curvature.profile.scalarConvergesTo
        (fun i => E.C * E.decay i) 0)
    (hnonneg : conclusion.curvature.profile.eventually
      (fun i => 0 <= conclusion.tracefree_ratio.seq i)) :
    ricciFlowTracefreeRicciNormSqAt k R V Time A conclusion.curvature.limit.flow
      conclusion.curvature.nInv conclusion.curvature.limitTime = 0 := by
  refine limit_tracefree_ricci_norm_sq_eq_zero_of_squeezed_ratio k R V Time A
    conclusion (fun i => E.C * E.decay i) hupper hnonneg ?_
  exact Hev.mono hdomain (fun i hi => by
    rw [hratio_seq]
    exact hpinching_bound i hi)

/-- Sample-level Section 12 bridge with the weak maximum principle supplying
the improved-pinching ratio bound. This is the direct consumer form for the
chain
`improved pinching + decay -> |Ric^0|^2 / R^2 -> 0 -> |Ric^0|^2_limit = 0`. -/
theorem limit_tracefree_ricci_norm_sq_eq_zero_of_improved_pinching_wmp_decay
    {Index : Type*}
    [ScalarWeakMaximumPrinciple R Index]
    (conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index)
    [Hsq : ScalarConvergenceSqueezeToZero Index R
      conclusion.curvature.profile.scalarConvergesTo
      conclusion.curvature.profile.eventually]
    [Hev : EventuallyImp Index conclusion.curvature.profile.eventually]
    (E : ImprovedRicciPinchingEstimateAlongFlow (R := R) (Time := Index))
    (hratio_seq : conclusion.tracefree_ratio.seq = E.ratio)
    (hdomain : conclusion.curvature.profile.eventually (fun i => E.problem.domain i))
    (hupper :
      conclusion.curvature.profile.scalarConvergesTo
        (fun i => E.C * E.decay i) 0)
    (hnonneg : conclusion.curvature.profile.eventually
      (fun i => 0 <= conclusion.tracefree_ratio.seq i)) :
    ricciFlowTracefreeRicciNormSqAt k R V Time A conclusion.curvature.limit.flow
      conclusion.curvature.nInv conclusion.curvature.limitTime = 0 :=
  limit_tracefree_ricci_norm_sq_eq_zero_of_improved_pinching_decay k R V Time A
    conclusion E hratio_seq hdomain
    (fun i hi => improved_ricci_pinching_ratio_bound_from_wmp E i hi)
    hupper hnonneg

/-- P6-facing name for the improved-pinching consumer chain:
weak maximum principle plus a zero-convergent decay upper bound forces the CGH
limit sample to have vanishing trace-free Ricci norm squared. -/
theorem limit_tracefree_norm_zero_from_improved_pinching
    {Index : Type*}
    [ScalarWeakMaximumPrinciple R Index]
    (conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index)
    [Hsq : ScalarConvergenceSqueezeToZero Index R
      conclusion.curvature.profile.scalarConvergesTo
      conclusion.curvature.profile.eventually]
    [Hev : EventuallyImp Index conclusion.curvature.profile.eventually]
    (E : ImprovedRicciPinchingEstimateAlongFlow (R := R) (Time := Index))
    (hratio_seq : conclusion.tracefree_ratio.seq = E.ratio)
    (hdomain : conclusion.curvature.profile.eventually (fun i => E.problem.domain i))
    (hupper :
      conclusion.curvature.profile.scalarConvergesTo
        (fun i => E.C * E.decay i) 0)
    (hnonneg : conclusion.curvature.profile.eventually
      (fun i => 0 <= conclusion.tracefree_ratio.seq i)) :
    ricciFlowTracefreeRicciNormSqAt k R V Time A conclusion.curvature.limit.flow
      conclusion.curvature.nInv conclusion.curvature.limitTime = 0 :=
  limit_tracefree_ricci_norm_sq_eq_zero_of_improved_pinching_wmp_decay
    k R V Time A conclusion E hratio_seq hdomain hupper hnonneg

/-- P6-facing bridge using the Hamilton P4 producer directly. This is the
Section 12 consumer shape after the quotient-evolution calculation has been
packaged as `HamiltonImprovedPinchingProducerData`. -/
theorem limit_tracefree_norm_zero_from_hamilton_improved_pinching_producer
    {Index : Type*}
    [ScalarWeakMaximumPrinciple R Index]
    (conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index)
    [Hsq : ScalarConvergenceSqueezeToZero Index R
      conclusion.curvature.profile.scalarConvergesTo
      conclusion.curvature.profile.eventually]
    [Hev : EventuallyImp Index conclusion.curvature.profile.eventually]
    (D : HamiltonImprovedPinchingProducerData (R := R) (Time := Index))
    (hratio_seq : conclusion.tracefree_ratio.seq = D.ratio)
    (hdomain : conclusion.curvature.profile.eventually (fun i => D.problem.domain i))
    (hupper :
      conclusion.curvature.profile.scalarConvergesTo
        (fun i => D.C * D.decay i) 0)
    (hnonneg : conclusion.curvature.profile.eventually
      (fun i => 0 <= conclusion.tracefree_ratio.seq i)) :
    ricciFlowTracefreeRicciNormSqAt k R V Time A conclusion.curvature.limit.flow
      conclusion.curvature.nInv conclusion.curvature.limitTime = 0 :=
  limit_tracefree_norm_zero_from_improved_pinching k R V Time A conclusion
    (improved_ricci_pinching_estimate_along_flow_of_hamilton_producer D)
    hratio_seq hdomain hupper hnonneg

end ImprovedPinchingCompactnessBridge

section CompactnessInterfaces

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Region-level Section 12 decay data. A compact-region realization should
provide one upper sequence `upper` for the whole region, prove that it converges
to zero in each scalar convergence profile, and prove that every ratio sample
in the region is eventually nonnegative and eventually bounded by `upper`.

This is deliberately still abstract about what a `RegionPoint` is; concrete CGH
realizations can use spacetime points, compact subsets with local charts, or
any equivalent indexing of the region. -/
structure UniformTracefreeRatioDecayOnRegion (Index RegionPoint : Type*) where
  region : RegionPoint -> Prop
  ratioAt : RegionPoint -> CurvatureRatioConvergenceConclusion k R V Time A Index
  upper : Index -> R
  squeeze_to_zero :
    forall z, region z ->
      ScalarConvergenceSqueezeToZero Index R
        (ratioAt z).curvature.profile.scalarConvergesTo
        (ratioAt z).curvature.profile.eventually
  upper_converges_zero :
    forall z, region z ->
      (ratioAt z).curvature.profile.scalarConvergesTo upper 0
  ratio_nonnegative_eventually :
    forall z, region z ->
      (ratioAt z).curvature.profile.eventually
        (fun i => 0 <= (ratioAt z).tracefree_ratio.seq i)
  ratio_bound_eventually :
    forall z, region z ->
      (ratioAt z).curvature.profile.eventually
        (fun i => (ratioAt z).tracefree_ratio.seq i <= upper i)

/-- Region-level consequence: a uniform zero-convergent upper bound for the
trace-free Ricci ratio forces `|Ric^0|^2 = 0` at every CGH limit sample in the
region. This is the compact-region version of the sample squeeze step; the
realization layer supplies the region and the uniform upper sequence. -/
theorem limit_tracefree_ricci_norm_sq_eq_zero_on_region_of_uniform_decay
    {Index RegionPoint : Type*}
    (data : UniformTracefreeRatioDecayOnRegion k R V Time A Index RegionPoint)
    (z : RegionPoint) (hz : data.region z) :
    ricciFlowTracefreeRicciNormSqAt k R V Time A
      (data.ratioAt z).curvature.limit.flow
      (data.ratioAt z).curvature.nInv
      (data.ratioAt z).curvature.limitTime = 0 := by
  have hratio :
      (data.ratioAt z).ratioQuantity (data.ratioAt z).curvature.limit.flow
        (data.ratioAt z).curvature.limitTime = 0 := by
    have hlim :
        (data.ratioAt z).tracefree_ratio.limit = 0 :=
      (data.squeeze_to_zero z hz).squeeze_to_zero
        (data.ratioAt z).tracefree_ratio.converges
        (data.upper_converges_zero z hz)
        (data.ratio_nonnegative_eventually z hz)
        (data.ratio_bound_eventually z hz)
    rwa [(data.ratioAt z).ratio_limit_eq] at hlim
  exact limit_tracefree_ricci_norm_sq_eq_zero_of_ratio_limit_zero k R V Time A
    (data.ratioAt z) hratio

/-- Interface for the curvature-ratio convergence corollary under a concrete
eventual-positivity witness for the limit scalar curvature. It extends the
curvature convergence interface and returns a ratio conclusion containing the
curvature conclusion whose scalar topology/filter it uses. -/
class CurvatureRatioConvergenceUnderSmoothCGH (Index : Type*) extends
    CurvatureConvergenceUnderSmoothCGH k R V Time A Index where
  ratio_convergence :
    forall data : SmoothCGHConvergenceData k R V Time A Index,
      EventuallyPositiveWitness Index R profile.eventually ->
        Nonempty { conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index //
          conclusion.curvature.sequence = data.sequence /\
            conclusion.curvature.limit = data.limit /\
            conclusion.curvature.profile = profile }

@[reducible] def cgh_curvature_ratio_convergence_from_interface
    {Index : Type*} [H : CurvatureRatioConvergenceUnderSmoothCGH k R V Time A Index]
    (data : SmoothCGHConvergenceData k R V Time A Index)
    (hpos : EventuallyPositiveWitness Index R H.profile.eventually) :
    Nonempty { conclusion : CurvatureRatioConvergenceConclusion k R V Time A Index //
      conclusion.curvature.sequence = data.sequence /\
        conclusion.curvature.limit = data.limit /\
        conclusion.curvature.profile = H.profile } :=
  H.ratio_convergence data hpos

/-- Hamilton-Cheeger-Gromov compactness as a black-box extraction interface. -/
class HamiltonCompactnessTheorem (Index : Type*) where
  extract_limit :
    forall sequence : PointedRicciFlowSequence k R V Time A Index,
      Nonempty { data : SmoothCGHConvergenceData k R V Time A Index //
        data.sequence = sequence }

/-- Diffeomorphism conclusion obtained from compact smooth CGH convergence:
for large `i`, the sequence manifold is diffeomorphic to the compact limit
manifold. The concrete realization supplies the manifold model and the actual
diffeomorphism predicate. -/
structure CompactLimitDiffeomorphismConclusion
    (Index Manifold Diffeomorphism : Type*) where
  sequence : PointedRicciFlowSequence k R V Time A Index
  limit : RicciFlowLimitCandidate k R V Time A
  manifoldOfFlow : RicciFlowData k R V Time A -> Manifold
  eventually : (Index -> Prop) -> Prop
  diffeomorphism : Index -> Diffeomorphism
  isDiffeomorphism : Diffeomorphism -> Manifold -> Manifold -> Prop
  eventually_diffeomorphic :
    eventually (fun i =>
      isDiffeomorphism (diffeomorphism i)
        (manifoldOfFlow (sequence.flow i)) (manifoldOfFlow limit.flow))

/-- Section 12 compact-limit input: compactness of the CGH limit promotes
smooth convergence to eventual diffeomorphism with the original manifolds. -/
class CompactLimitDiffeomorphismUnderSmoothCGH
    (Index Manifold Diffeomorphism : Type*) where
  manifoldOfFlow : RicciFlowData k R V Time A -> Manifold
  IsCompact : Manifold -> Prop
  eventually : (Index -> Prop) -> Prop
  IsDiffeomorphism : Diffeomorphism -> Manifold -> Manifold -> Prop
  diffeomorphic_for_large_i :
    forall data : SmoothCGHConvergenceData k R V Time A Index,
      IsCompact (manifoldOfFlow data.limit.flow) ->
        Nonempty { conclusion :
            CompactLimitDiffeomorphismConclusion k R V Time A Index Manifold Diffeomorphism //
          conclusion.sequence = data.sequence /\ conclusion.limit = data.limit /\
            conclusion.manifoldOfFlow = manifoldOfFlow /\
            conclusion.eventually = eventually /\
            conclusion.isDiffeomorphism = IsDiffeomorphism }

theorem compact_limit_diffeomorphism_from_interface
    {Index Manifold Diffeomorphism : Type*}
    [H : CompactLimitDiffeomorphismUnderSmoothCGH k R V Time A Index Manifold Diffeomorphism]
    (data : SmoothCGHConvergenceData k R V Time A Index)
    (hcompact : H.IsCompact (H.manifoldOfFlow data.limit.flow)) :
    Nonempty { conclusion :
        CompactLimitDiffeomorphismConclusion k R V Time A Index Manifold Diffeomorphism //
      conclusion.sequence = data.sequence /\ conclusion.limit = data.limit /\
        conclusion.manifoldOfFlow = H.manifoldOfFlow /\
        conclusion.eventually = H.eventually /\
        conclusion.isDiffeomorphism = H.IsDiffeomorphism } :=
  H.diffeomorphic_for_large_i data hcompact

/-- Concrete lower-volume conclusion for Perelman's noncollapsing theorem at a
single spacetime point and scale. Radii and volumes are represented in the
ambient scalar type `R`; the realization layer supplies the actual ball-volume
function. -/
structure KappaNoncollapsedAtScale (Point : Type*) where
  flow : RicciFlowData k R V Time A
  point : Point
  time : Time
  radius : R
  ballVolume : RicciFlowData k R V Time A -> Point -> Time -> R -> R
  kappa : R
  radius_positive : 0 < radius
  kappa_positive : 0 < kappa
  lower_volume_bound : kappa * radius * radius * radius <= ballVolume flow point time radius

/-- Typed Perelman noncollapsing interface used by Section 12: curvature
control on a parabolic ball yields a concrete lower volume bound at the base
scale. -/
class PerelmanNoncollapsingAtScale (Point : Type*) where
  ballVolume : RicciFlowData k R V Time A -> Point -> Time -> R -> R
  CurvatureControlledOnParabolicBall :
    RicciFlowData k R V Time A -> Point -> Time -> R -> Prop
  noncollapsed_of_curvature_control :
    forall (D : RicciFlowData k R V Time A) (p : Point) (t : Time) (radius : R),
      0 < radius ->
      CurvatureControlledOnParabolicBall D p t radius ->
        Nonempty { conclusion : KappaNoncollapsedAtScale k R V Time A Point //
          conclusion.flow = D /\ conclusion.point = p /\ conclusion.time = t /\
            conclusion.radius = radius /\ conclusion.ballVolume = ballVolume }

theorem perelman_noncollapsed_at_scale_from_interface
    {Point : Type*} [H : PerelmanNoncollapsingAtScale k R V Time A Point]
    (D : RicciFlowData k R V Time A) (p : Point) (t : Time) (radius : R)
    (hradius : 0 < radius)
    (hcurv : H.CurvatureControlledOnParabolicBall D p t radius) :
    Nonempty { conclusion : KappaNoncollapsedAtScale k R V Time A Point //
      conclusion.flow = D /\ conclusion.point = p /\ conclusion.time = t /\
        conclusion.radius = radius /\ conclusion.ballVolume = H.ballVolume } :=
  H.noncollapsed_of_curvature_control D p t radius hradius hcurv

/-- Perelman's noncollapsing theorem as an interface. -/
class PerelmanNoncollapsing where
  IsKappaNoncollapsed : RicciFlowData k R V Time A -> Prop
  noncollapsed : forall D : RicciFlowData k R V Time A, IsKappaNoncollapsed D

/-- Myers-type compactness conclusion with a positive Ricci lower bound. -/
structure MyersCompactnessConclusion (Manifold : Type*) where
  manifold : Manifold
  IsCompact : Manifold -> Prop
  compact : IsCompact manifold
  diameterBound : R

/-- Typed Myers interface used in Section 12. The concrete realization should
define `HasPositiveRicciLowerBound` in terms of the limit metric. -/
class MyersPositiveRicciCompactness (Manifold : Type*) where
  IsCompact : Manifold -> Prop
  HasPositiveRicciLowerBound : Manifold -> R -> Prop
  compact_of_positive_ricci :
    forall (M : Manifold) (lower : R),
      0 < lower -> HasPositiveRicciLowerBound M lower ->
        Nonempty { conclusion : MyersCompactnessConclusion R Manifold //
          conclusion.manifold = M /\ conclusion.IsCompact = IsCompact }

theorem myers_compactness_from_positive_ricci_interface
    {Manifold : Type*} [H : MyersPositiveRicciCompactness R Manifold]
    (M : Manifold) (lower : R)
    (hlower : 0 < lower) (hRic : H.HasPositiveRicciLowerBound M lower) :
    Nonempty { conclusion : MyersCompactnessConclusion R Manifold //
      conclusion.manifold = M /\ conclusion.IsCompact = H.IsCompact } :=
  H.compact_of_positive_ricci M lower hlower hRic

/-- P8-facing compactness consumer. A geometric bridge from constant positive
sectional curvature to a positive Ricci lower bound, followed by the Myers
interface, gives compactness of the limit manifold. -/
theorem limit_compact_from_constant_positive_consumer
    {Manifold Metric : Type*} [H : MyersPositiveRicciCompactness R Manifold]
    (MetricOn ConstantPositiveSectionalCurvature : Manifold -> Metric -> Prop)
    (M : Manifold) (g : Metric) (lower : R)
    (hmetric : MetricOn M g)
    (hconst : ConstantPositiveSectionalCurvature M g)
    (hlower : 0 < lower)
    (hRic :
      MetricOn M g ->
        ConstantPositiveSectionalCurvature M g ->
          H.HasPositiveRicciLowerBound M lower) :
    H.IsCompact M := by
  obtain ⟨conclusion, hconclusion⟩ :=
    myers_compactness_from_positive_ricci_interface R M lower hlower
      (hRic hmetric hconst)
  have hcompact := conclusion.compact
  rw [hconclusion.1, hconclusion.2] at hcompact
  exact hcompact

/-- Myers-type compactness conclusion needed for the final contradiction. -/
class MyersTheoremInterface (Input Output : Type*) where
  conclusion : Input -> Output -> Prop
  exists_output : forall input, Nonempty { output : Output // conclusion input output }

end CompactnessInterfaces

