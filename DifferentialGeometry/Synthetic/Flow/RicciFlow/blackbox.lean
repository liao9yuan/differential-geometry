import DifferentialGeometry.Synthetic.Flow.RicciFlow.Global.Compactness

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci Flow Analytic Black Boxes

This module is the named boundary for global analytic Ricci-flow inputs that
the synthetic Hamilton-three-manifold assembly should consume as black boxes:
short-time/maximal-time existence, finite-time singularity, blow-up and
point-selection, Hamilton-Cheeger-Gromov compactness, curvature convergence, and
Perelman noncollapsing.

Elementary algebraic, tensor-calculus, and finite-dimensional reductions should
remain in their proof modules rather than being moved here.

Black-box policy: theorem-shaped declarations with `sorry` are allowed in this
file only when the statement is a concrete analytic/global input such as
short-time existence, maximal gluing, extension criteria, Hamilton compactness,
Perelman noncollapsing, or realization-level scalar-power/positivity APIs. Each
such theorem must state the mathematical hypothesis it abstracts and explain in
its docstring why the proof belongs outside the synthetic layer. Do not move
P1/P2/P3/P4 tensor algebra or quotient evolution here.
-/

open SyntheticTensor

section HamiltonAnalyticBlackBoxes

variable (k R V Time A : Type*)
variable [Field k] [CommRing R] [Algebra k R] [Preorder R] [Invertible (2 : R)]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Bundled global analytic inputs for Hamilton's Section 12 assembly.

This contains only the hard global/analytic stack. Local synthetic gaps and
finite-dimensional algebraic bridges stay outside this bundle so they can be
proved in the ordinary proof files. -/
class HamiltonGlobalAnalyticBlackBoxes (Point Index : Type*) where
  finite_time : PositiveScalarFiniteTimeTheorem k R V Time A
  maximal_time : MaximalTimeWitness k R V Time A finite_time.HasFiniteMaximalTime
  curvature_blowup : CurvatureBlowUpAlternative k R V Time A
  scalar_blowup : ScalarBlowUpFromCurvatureBlowUp k R V Time A
  point_selection : PointSelectionAndRescalingTheorem k R V Time A Point Index
  compactness : HamiltonCompactnessTheorem k R V Time A Index
  curvature_ratio_convergence :
    CurvatureRatioConvergenceUnderSmoothCGH k R V Time A Index

/-- Low-priority constructor for the global analytic black-box bundle from the
individual global theorem interfaces. -/
instance (priority := 100) hamiltonGlobalAnalyticBlackBoxes_of_components
    {Point Index : Type*}
    [H : PositiveScalarFiniteTimeTheorem k R V Time A]
    [W : MaximalTimeWitness k R V Time A H.HasFiniteMaximalTime]
    [B : CurvatureBlowUpAlternative k R V Time A]
    [S : ScalarBlowUpFromCurvatureBlowUp k R V Time A]
    [P : PointSelectionAndRescalingTheorem k R V Time A Point Index]
    [K : HamiltonCompactnessTheorem k R V Time A Index]
    [CR : CurvatureRatioConvergenceUnderSmoothCGH k R V Time A Index] :
    HamiltonGlobalAnalyticBlackBoxes k R V Time A Point Index where
  finite_time := H
  maximal_time := W
  curvature_blowup := B
  scalar_blowup := S
  point_selection := P
  compactness := K
  curvature_ratio_convergence := CR

end HamiltonAnalyticBlackBoxes

section ExperimentalSmoothInitialMetricMaximalTime

variable (Flow Time Manifold Metric : Type*)

/-- Experimental carrier for a smooth initial metric. The realization layer
decides what `Manifold`, `Metric`, and smoothness mean. -/
structure SmoothInitialMetricData where
  manifold : Manifold
  metric : Metric

/-- Abstract Ricci-flow solution used only by the experimental 14.5/14.6
skeleton. This intentionally avoids the older global `RicciFlowData` token API:
the missing work is interval restriction, gluing, and concrete realization
data, not another synthetic tensor bundle. -/
structure ExperimentalRicciFlowSolution where
  flow : Flow

/-- Abstract maximal Ricci flow produced by gluing all compatible short-time
solutions. The `isMaximal` field records the Zorn/union construction result
until the interval category is available. -/
structure ExperimentalMaximalRicciFlow where
  flow : Flow
  isMaximal : Prop

/-- Short-time Ricci-flow existence from a smooth initial metric.

Mathematically this is Hamilton/DeTurck short-time existence: after choosing a
background metric, solve the strictly parabolic Ricci-DeTurck system, then pull
back by the DeTurck diffeomorphisms. -/
class SmoothInitialMetricShortTimeExistence where
  IsSmoothInitialMetric : SmoothInitialMetricData Manifold Metric -> Prop
  StartsFrom : SmoothInitialMetricData Manifold Metric -> Flow -> Prop
  exists_short_time :
    forall g0 : SmoothInitialMetricData Manifold Metric,
      IsSmoothInitialMetric g0 ->
        Nonempty { sol : ExperimentalRicciFlowSolution Flow //
          StartsFrom g0 sol.flow }

/-- Maximal-interval construction by gluing compatible short-time solutions.

This is the Section 14.5 step. The black-box assumption is not that a singular
time is finite. It only says a smooth initial metric has a maximal solution,
and that the glued maximal solution still extends the original short-time
solution and keeps the same initial metric. -/
class SmoothInitialMetricMaximalIntervalConstruction extends
    SmoothInitialMetricShortTimeExistence Flow Manifold Metric where
  Extends : Flow -> Flow -> Prop
  extend_to_maximal :
    forall sol : ExperimentalRicciFlowSolution Flow,
      Nonempty { max : ExperimentalMaximalRicciFlow Flow //
        Extends sol.flow max.flow }
  starts_from_of_extends :
    forall {g0 : SmoothInitialMetricData Manifold Metric} {F G : Flow},
      StartsFrom g0 F -> Extends F G -> StartsFrom g0 G

/-- Mild uniqueness package for Ricci flow from a smooth initial metric.

For closed manifolds this is the usual uniqueness theorem proved through the
Ricci-DeTurck gauge. For complete noncompact flows, the realization should make
the mild hypothesis include the standard bounded-curvature and completeness
assumptions needed for uniqueness. -/
class SmoothInitialMetricUniqueness extends
    SmoothInitialMetricMaximalIntervalConstruction Flow Manifold Metric where
  MildUniquenessHypothesis : SmoothInitialMetricData Manifold Metric -> Prop
  EquivalentFlows : Flow -> Flow -> Prop
  unique_from_initial :
    forall (g0 : SmoothInitialMetricData Manifold Metric) (F G : Flow),
      MildUniquenessHypothesis g0 ->
        StartsFrom g0 F -> StartsFrom g0 G -> EquivalentFlows F G

/-- Endpoint data for a maximal Ricci flow.

The terminal value may be a genuine finite endpoint or an infinity-like marker,
depending on the realization. We only require nonextendability in the finite
case. -/
class ExperimentalTerminalTimeAndExtension where
  terminalTime : ExperimentalMaximalRicciFlow Flow -> Time
  IsFiniteTerminalTime : ExperimentalMaximalRicciFlow Flow -> Prop
  IsInfiniteTerminalTime : ExperimentalMaximalRicciFlow Flow -> Prop
  finite_or_infinite :
    forall M : ExperimentalMaximalRicciFlow Flow,
      IsFiniteTerminalTime M \/ IsInfiniteTerminalTime M
  CanExtendPast : Flow -> Time -> Prop
  nonextendable_at_finite_terminal :
    forall M : ExperimentalMaximalRicciFlow Flow,
      IsFiniteTerminalTime M ->
        Not (CanExtendPast M.flow (terminalTime M))

/-- Optional realization-level interpretation of finite nonextendability as a
singular endpoint. This is the Section 14.6 extension-criterion conclusion:
if a smooth limit existed with bounded curvature, short-time existence from
that terminal metric would extend the flow past the endpoint. -/
class ExperimentalTerminalSingularityCriterion
    (CanExtendPast : Flow -> Time -> Prop) where
  IsSingularAt : Flow -> Time -> Prop
  singular_of_nonextendable :
    forall {F : Flow} {T : Time},
      Not (CanExtendPast F T) -> IsSingularAt F T

/-- A local version of unboundedness for the experimental flow carrier. -/
def ExperimentalUnboundedAboveOn {R Time : Type*} [Preorder R]
    (q : Time -> R) (domain : Time -> Prop) : Prop :=
  forall C, exists t, domain t /\ C <= q t

/-- Optional curvature blow-up criterion for a concrete realization.

This is deliberately conditional on the same extension relation as the
terminal-time package. It should be instantiated from the standard extension
criterion: bounded full curvature up to the finite endpoint gives a smooth
extension, hence nonextendability forces curvature blow-up. -/
class ExperimentalCurvatureBlowUpCriterion (R : Type*) [Preorder R]
    (CanExtendPast : Flow -> Time -> Prop) where
  curvatureQuantity : Flow -> Time -> R
  domain : Flow -> Time -> Time -> Prop
  curvature_unbounded_of_nonextendable :
    forall {F : Flow} {T : Time},
      Not (CanExtendPast F T) ->
        ExperimentalUnboundedAboveOn (curvatureQuantity F) (domain F T)

/-- Compatibility between the realization's flow-equivalence relation and
terminal times. This is the extra endpoint-level statement needed to turn
DeTurck uniqueness of maximal flows into uniqueness of the maximal time. -/
class ExperimentalTerminalTimeRespectsEquivalence
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    (EquivalentFlows : Flow -> Flow -> Prop) where
  terminalTime_eq_of_equivalent :
    forall M N : ExperimentalMaximalRicciFlow Flow,
      EquivalentFlows M.flow N.flow -> T.terminalTime M = T.terminalTime N

/-- Output of the experimental Section 14.5/14.6 maximal-interval construction.

The structure records the clean mathematical split:
1. short-time existence from a smooth initial metric;
2. maximal extension by gluing compatible solutions;
3. a terminal time that may be finite or infinite;
4. finite terminal time implies nonextendability. -/
structure SmoothInitialMetricMaximalFlow
    [H : SmoothInitialMetricMaximalIntervalConstruction Flow Manifold Metric]
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    (g0 : SmoothInitialMetricData Manifold Metric) where
  shortTime : ExperimentalRicciFlowSolution Flow
  short_starts_from : H.StartsFrom g0 shortTime.flow
  maximal : ExperimentalMaximalRicciFlow Flow
  maximal_extends_short : H.Extends shortTime.flow maximal.flow
  maximal_starts_from : H.StartsFrom g0 maximal.flow
  terminalTime : Time
  terminalTime_eq : terminalTime = T.terminalTime maximal
  finite_or_infinite :
    T.IsFiniteTerminalTime maximal \/ T.IsInfiniteTerminalTime maximal
  nonextendable_if_finite :
    T.IsFiniteTerminalTime maximal ->
      Not (T.CanExtendPast maximal.flow terminalTime)

/-- Experimental skeleton: from a smooth initial metric, construct a maximal
Ricci flow and its maximal endpoint.

This theorem does not assert finite-time singularity. It gives the maximal
flow dichotomy: the maximal endpoint is either infinite/long-time or, if
finite, nonextendable. -/
theorem maximal_flow_from_smooth_initial_metric
    [H : SmoothInitialMetricMaximalIntervalConstruction Flow Manifold Metric]
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    (g0 : SmoothInitialMetricData Manifold Metric)
    (hsmooth : H.IsSmoothInitialMetric g0) :
    Nonempty (SmoothInitialMetricMaximalFlow Flow Time Manifold Metric g0) := by
  obtain ⟨short, hshort⟩ := H.exists_short_time g0 hsmooth
  obtain ⟨maximal, hextends⟩ := H.extend_to_maximal short
  refine Nonempty.intro ?_
  refine
    { shortTime := short
      short_starts_from := hshort
      maximal := maximal
      maximal_extends_short := hextends
      maximal_starts_from := H.starts_from_of_extends hshort hextends
      terminalTime := T.terminalTime maximal
      terminalTime_eq := rfl
      finite_or_infinite := T.finite_or_infinite maximal
      nonextendable_if_finite := ?_ }
  intro hfinite
  exact T.nonextendable_at_finite_terminal maximal hfinite

/-- Under the mild uniqueness hypothesis, any two maximal flows produced from
the same initial metric are equivalent. This is the Section 14.6 uniqueness
input, stated through the realization-supplied equivalence relation on flows. -/
theorem maximal_flow_unique_from_smooth_initial_metric
    [H : SmoothInitialMetricUniqueness Flow Manifold Metric]
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    (g0 : SmoothInitialMetricData Manifold Metric)
    (hmild : H.MildUniquenessHypothesis g0)
    (M1 M2 : SmoothInitialMetricMaximalFlow Flow Time Manifold Metric g0) :
    H.EquivalentFlows M1.maximal.flow M2.maximal.flow :=
  H.unique_from_initial g0 M1.maximal.flow M2.maximal.flow hmild
    M1.maximal_starts_from M2.maximal_starts_from

/-- Under the mild uniqueness hypothesis, the maximal endpoint itself is
unique once the realization proves that equivalent maximal flows have the same
terminal time. -/
theorem maximal_terminal_time_unique_from_smooth_initial_metric
    [H : SmoothInitialMetricUniqueness Flow Manifold Metric]
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    [E : ExperimentalTerminalTimeRespectsEquivalence Flow Time H.EquivalentFlows]
    (g0 : SmoothInitialMetricData Manifold Metric)
    (hmild : H.MildUniquenessHypothesis g0)
    (M1 M2 : SmoothInitialMetricMaximalFlow Flow Time Manifold Metric g0) :
    M1.terminalTime = M2.terminalTime := by
  have heq :
      H.EquivalentFlows M1.maximal.flow M2.maximal.flow :=
    maximal_flow_unique_from_smooth_initial_metric Flow Time Manifold Metric
      g0 hmild M1 M2
  calc
    M1.terminalTime = T.terminalTime M1.maximal := M1.terminalTime_eq
    _ = T.terminalTime M2.maximal :=
      E.terminalTime_eq_of_equivalent M1.maximal M2.maximal heq
    _ = M2.terminalTime := M2.terminalTime_eq.symm

/-- A finite maximal endpoint is singular in the realization's extension
criterion sense. -/
theorem finite_maximal_time_is_singular_from_smooth_initial_metric
    [H : SmoothInitialMetricMaximalIntervalConstruction Flow Manifold Metric]
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    [S : ExperimentalTerminalSingularityCriterion Flow Time T.CanExtendPast]
    {g0 : SmoothInitialMetricData Manifold Metric}
    (M : SmoothInitialMetricMaximalFlow Flow Time Manifold Metric g0)
    (hfinite : T.IsFiniteTerminalTime M.maximal) :
    S.IsSingularAt M.maximal.flow M.terminalTime :=
  S.singular_of_nonextendable (M.nonextendable_if_finite hfinite)

/-- If the realization supplies the standard curvature extension criterion,
then a finite maximal endpoint has unbounded curvature on its terminal domain. -/
theorem curvature_blowup_at_finite_maximal_time_from_smooth_initial_metric
    {R : Type*} [Preorder R]
    [H : SmoothInitialMetricMaximalIntervalConstruction Flow Manifold Metric]
    [T : ExperimentalTerminalTimeAndExtension Flow Time]
    [B : ExperimentalCurvatureBlowUpCriterion Flow Time R T.CanExtendPast]
    {g0 : SmoothInitialMetricData Manifold Metric}
    (M : SmoothInitialMetricMaximalFlow Flow Time Manifold Metric g0)
    (hfinite : T.IsFiniteTerminalTime M.maximal) :
    ExperimentalUnboundedAboveOn (B.curvatureQuantity M.maximal.flow)
      (B.domain M.maximal.flow M.terminalTime) :=
  B.curvature_unbounded_of_nonextendable (M.nonextendable_if_finite hfinite)

end ExperimentalSmoothInitialMetricMaximalTime
