import RicciFlower.GlobalGeometry.Lecture07.SprayChartPush
import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# GSM245 Lecture 7.3: normal-coordinate front end

This file is the coordinate-defined front end for eventual normal coordinates.
It deliberately starts with relation-valued endpoint data instead of defining
an exponential map as a function.  A functional exponential map requires the
next analytic layer: uniqueness and smooth dependence of the local geodesic
flow on initial velocity.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Lecture07

open Bundle
open scoped Manifold ContDiff Topology
open RicciFlower.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

/-! ## Coordinate geodesic segments -/

/-- A curve satisfies the coordinate-defined geodesic equation on `s`, in the
fixed `extChartAt x0` coordinates.

This is intentionally coordinate-level.  It uses the canonical
`HasCoordCovAccelAt` predicate introduced in `CoordinateEquation.lean`, not the
older global-representative acceleration relation. -/
def IsCoordGeodesicOn
    (g : SmoothRiemannianMetric I M) (x0 : M)
    (gamma : Curve M) (s : Set Real) : Prop :=
  (∀ t : Real, t ∈ s -> gamma t ∈ coordinateFrameSet (I := I) x0) ∧
    ∀ t : Real, t ∈ s ->
      HasCoordCovAccelAt (I := I) x0
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        gamma t 0

/-- A coordinate geodesic segment with prescribed initial tangent vector. -/
def IsCoordGeodesicSegment
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x)
    (gamma : Curve M) (s : Set Real) : Prop :=
  gamma 0 = x ∧
    curveVelocityBundle I gamma 0 = (⟨x, v⟩ : TangentBundle I M) ∧
      IsCoordGeodesicOn (I := I) g x gamma s

/-- Relation-valued coordinate exponential endpoint at time `tau`.

The relation says that some coordinate-defined geodesic segment with initial
data `(x, v)` reaches `y` at time `tau`.  The set `s` is explicit so later
theorems can use intervals, balls, or compact subintervals without changing
the public endpoint relation. -/
def CoordExpRelAtTime
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (tau : Real) (y : M) : Prop :=
  ∃ s : Set Real,
    0 ∈ s ∧ tau ∈ s ∧
      ∃ gamma : Curve M,
        IsCoordGeodesicSegment (I := I) g x v gamma s ∧
          gamma tau = y

/-- Relation-valued coordinate exponential endpoint at time `1`. -/
def CoordExpRel
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (y : M) : Prop :=
  CoordExpRelAtTime (I := I) g x v 1 y

/-! ## Short endpoint API -/

/-- Short public name for the time-one relation-valued coordinate exponential.

This is still a relation, not a function: uniqueness and smooth dependence of
the chart-fixed geodesic flow are the next analytic layer. -/
def expAt
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (y : M) : Prop :=
  CoordExpRel (I := I) g x v y

@[simp] theorem expAt_iff
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) (y : M) :
    expAt (I := I) g x v y ↔ CoordExpRel (I := I) g x v y :=
  Iff.rfl

/-- Package a coordinate geodesic segment whose time domain contains `0` and
`1` as a time-one endpoint relation. -/
theorem expAt_of_segment
    {g : SmoothRiemannianMetric I M}
    {x : M} {v : TangentSpace I x}
    {gamma : Curve M} {s : Set Real}
    (h0 : 0 ∈ s) (h1 : 1 ∈ s)
    (hseg : IsCoordGeodesicSegment (I := I) g x v gamma s) :
    expAt (I := I) g x v (gamma 1) := by
  exact ⟨s, h0, h1, gamma, hseg, rfl⟩

/-- Constant curves have zero coordinate-defined covariant acceleration in any
valid `extChartAt` coordinate package.

This reuses the representative-based compatibility layer only as a producer:
the ambient zero field realizes the velocity of a constant curve, and the
already-proved `toCoord` theorem converts that intrinsic pullback acceleration
to the coordinate-defined predicate. -/
private theorem coordAccel_const
    [I.Boundaryless]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (x0 x : M) (t : Real)
    (hx : x ∈ coordinateFrameSet (I := I) x0) :
    HasCoordCovAccelAt (I := I) x0 cov (fun _ : Real => x) t 0 := by
  let gamma : Curve M := fun _ : Real => x
  let X : GlobalVectorField I M := fun _p : M => 0
  have hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma t := by
    simpa [gamma] using
      (mdifferentiableAt_const
        (I := 𝓘(Real, Real)) (I' := I) (c := x) (x := t))
  have hX : MDiffSectionAt (I := I) (F := E)
      (V := TangentSpace I) X (gamma t) := by
    simpa [MDiffSectionAt, X, gamma, zeroSection] using
      (Bundle.mdifferentiableAt_zeroSection
        (𝕜 := Real) (F := E) (E := TangentSpace I) (x := x))
  have hvel : RealizesVelocity (I := I) gamma X := by
    intro s
    simp [gamma, X, velocityAlong]
  have hpb :
      HasPullbackCovariantAccelerationAt (I := I) cov gamma t
        ((cov X (gamma t)) (curveVelocity I gamma t)) :=
    hasPullbackCovariantAccelerationAt_of_global_velocity
      (I := I) (cov := cov) (gamma := gamma) (X := X) (t := t)
      hgamma hX hvel
  have hcoord :
      HasCoordCovAccelAt (I := I) x0 cov gamma t
        ((cov X (gamma t)) (curveVelocity I gamma t)) :=
    hpb.toCoord (I := I) x0 (by simpa [gamma] using hx)
  simpa [gamma, X] using hcoord

/-- Time-one zero-velocity endpoint.

Mathematically this is realized by the constant coordinate geodesic.  The
proof now goes through the coordinate-defined acceleration layer, not through a
functional exponential map. -/
theorem expAt_zero
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    expAt (I := I) g x (0 : TangentSpace I x) x := by
  let gamma : Curve M := fun _ : Real => x
  refine expAt_of_segment (I := I) (g := g) (x := x)
    (v := (0 : TangentSpace I x)) (gamma := gamma)
    (s := Set.univ) (by simp) (by simp) ?_
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · simp [gamma, zeroInitialVelocity]
  · constructor
    · intro t _ht
      simpa [gamma] using coordinateFrameAt_mem (I := I) x
    · intro t _ht
      simpa [gamma] using
        coordAccel_const (I := I)
          (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
          x x t (coordinateFrameAt_mem (I := I) x)

/-! ## Fixed-chart time-one frontier -/

/-- The zero phase point `0_x ∈ TM` used to chart the time-one local flow. -/
private def phaseZero (x : M) : TangentBundle I M :=
  (⟨x, (0 : E)⟩ : TangentBundle I M)

/-- Interpret model coordinates in the tangent-bundle chart centered at
`0_x`. -/
private def phaseOfModel (x : M) (z : E × E) : TangentBundle I M :=
  (extChartAt I.tangent (phaseZero (I := I) x)).symm z

/-- Fixed-chart model vector field for the geodesic spray near `0_x`.

This is the object that should feed the uniform time-one Picard-Lindelof
argument: solve `z' = modelSpray g x z` on `[0, 1]`, then map the solution
back to `TM` with `phaseOfModel`. -/
private def modelSpray
    (g : SmoothRiemannianMetric I M) (x : M) (z : E × E) : E × E :=
  let q : TangentBundle I M := phaseOfModel (I := I) x z
  tangentCoordChange I.tangent q (phaseZero (I := I) x) q
    (leviCivitaGeodesicSprayChart (I := I) g x q)

/-- Uniform time-one local existence of the relation-valued coordinate
exponential near zero velocity.

This is the first genuinely analytic normal-coordinate frontier.  The checked
spray package gives small-time existence for each fixed initial velocity; this
statement asks for a single velocity ball on which the solution exists through
time `1`.  It should be proved from a fixed-chart Picard-Lindelof flow with
continuous dependence on initial data. -/
theorem exists_exp_one
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    ∃ r > 0, ∀ v ∈ Metric.ball (0 : TangentSpace I x) r,
      ∃ y : M, expAt (I := I) g x v y := by
  sorry

/-- Strict derivative at zero for a functional local endpoint map.

This is intentionally stated only after choosing a genuine local endpoint
function realizing `expAt` on a ball.  An arbitrary `Classical.choose` from the
relation-valued endpoint would not be smooth; the missing proof is smooth
dependence and uniqueness of the chart-fixed geodesic flow, followed by the
standard zero-velocity linearization. -/
theorem expAt_strict
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    ∃ r > 0, ∃ exp : TangentSpace I x -> M,
      exp 0 = x ∧
        (∀ v ∈ Metric.ball (0 : TangentSpace I x) r,
          expAt (I := I) g x v (exp v)) ∧
        HasStrictFDerivAt
          (fun v : TangentSpace I x => extChartAt I x (exp v))
          (ContinuousLinearMap.id Real (TangentSpace I x)) 0 := by
  sorry

/-! ## What the current spray package proves -/

/-- The Picard-Lindelof spray producer gives a coordinate-defined geodesic
equation at the initial time. -/
theorem exists_coordGeoAt
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ gamma : Curve M,
      gamma 0 = x ∧
        curveVelocityBundle I gamma 0 =
          (⟨x, v⟩ : TangentBundle I M) ∧
        IsCoordGeodesicOn (I := I) g x gamma ({0} : Set Real) := by
  obtain ⟨gamma, hgamma0, hvel, _hspray, _hode, hacc⟩ :=
    exists_local_geodesic_coordZero (I := I) g x v
  refine ⟨gamma, hgamma0, hvel, ?_⟩
  constructor
  · intro t ht
    have ht0 : t = 0 := by simpa using ht
    subst t
    simpa [hgamma0] using coordinateFrameAt_mem (I := I) x
  · intro t ht
    have ht0 : t = 0 := by simpa using ht
    subst t
    simpa using hacc

/-- The relation-valued endpoint exists at time `0`, by the local spray
producer and the checked initial-time coordinate acceleration theorem. -/
theorem coordExp_zero
    [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    CoordExpRelAtTime (I := I) g x v 0 x := by
  obtain ⟨gamma, hgamma0, hvel, hgeo⟩ :=
    exists_coordGeoAt (I := I) g x v
  refine ⟨({0} : Set Real), ?_, ?_, gamma, ?_, ?_⟩
  · simp
  · simp
  · exact ⟨hgamma0, hvel, hgeo⟩
  · simp [hgamma0]

/-- Local coordinate-geodesic existence on a genuine time ball.

The proof uses the chart-fixed spray IVP, shrinks the time ball so the base
projection remains in the original `extChartAt x` chart, and then applies the
fixed-chart scalar ODE bridge from `SprayChartPush.lean` at each time. -/
theorem exists_coordGeoOn
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ epsilon > 0, ∃ gamma : Curve M,
      gamma 0 = x ∧
        curveVelocityBundle I gamma 0 =
          (⟨x, v⟩ : TangentBundle I M) ∧
        IsCoordGeodesicOn (I := I) g x gamma
          (Metric.ball (0 : Real) epsilon) := by
  classical
  obtain ⟨G, -⟩ := exists_localGeodesicIVPAt_leviCivita (I := I) g x v
  let gamma : Curve M := projectCurve (I := I) G.lift
  have hballG : Metric.ball (0 : Real) G.epsilon ∈ 𝓝 (0 : Real) :=
    Metric.ball_mem_nhds _ G.epsilon_pos
  have hf0 : IsMIntegralCurveAt G.lift
      (leviCivitaGeodesicSprayChart (I := I) g x) 0 :=
    G.spray_integral.isMIntegralCurveAt hballG
  have hproj_cont :
      ContinuousAt (fun t : Real => (G.lift t).proj) 0 := by
    exact (FiberBundle.continuous_proj E
      (TangentSpace I : M -> Type _)).continuousAt.comp hf0.continuousAt
  have hsrc_nhds :
      (extChartAtCoordinateData (I := I) x).domain ∈
        𝓝 ((G.lift 0).proj) := by
    simpa [G.lift_initial, extChartAtCoordinateData, coordinateFrameSet,
      coordinateTrivializationAt, extChartAt_source] using
      extChartAt_source_mem_nhds (I := I) x
  have hsrc_event :
      ∀ᶠ t in 𝓝 (0 : Real),
        (G.lift t).proj ∈
          (extChartAtCoordinateData (I := I) x).domain :=
    hproj_cont.preimage_mem_nhds hsrc_nhds
  have hgood :
      Metric.ball (0 : Real) G.epsilon ∩
          {t : Real | (G.lift t).proj ∈
            (extChartAtCoordinateData (I := I) x).domain} ∈
        𝓝 (0 : Real) :=
    Filter.inter_mem hballG hsrc_event
  rw [Metric.mem_nhds_iff] at hgood
  obtain ⟨epsilon, hepsilon, hepsilon_sub⟩ := hgood
  have hsubsetG :
      Metric.ball (0 : Real) epsilon ⊆
        Metric.ball (0 : Real) G.epsilon := by
    intro t ht
    exact (hepsilon_sub ht).1
  have hf_small : IsMIntegralCurveOn G.lift
      (leviCivitaGeodesicSprayChart (I := I) g x)
      (Metric.ball (0 : Real) epsilon) :=
    G.spray_integral.mono hsubsetG
  have hsrc_small :
      ∀ t ∈ Metric.ball (0 : Real) epsilon,
        projectCurve (I := I) G.lift t ∈
          (extChartAtCoordinateData (I := I) x).domain := by
    intro t ht
    simpa [projectCurve] using (hepsilon_sub ht).2
  refine ⟨epsilon, hepsilon, gamma, ?_, ?_, ?_⟩
  · simpa [gamma] using
      projectCurve_zero_of_lift (I := I)
        (u := (⟨x, v⟩ : TangentBundle I M)) G.lift_initial
  · simpa [gamma] using
      projectCurve_initialVelocity_of_geodesicSprayIntegral
        (I := I) (g := g) (u := (⟨x, v⟩ : TangentBundle I M))
        (f := G.lift) G.lift_initial hf0
  · constructor
    · exact hsrc_small
    · intro t ht
      have hode :=
        coordSprayODEOn (I := I) (g := g) (x := x) (v := v)
          (lift := G.lift) (epsilon := epsilon) (t := t)
          G.lift_initial hf_small ht hsrc_small
      exact hode.zeroAccel

/-- Local relation-valued endpoint existence for small times, produced by the
checked local coordinate-geodesic segment theorem. -/
theorem exists_coordExpTime
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    ∃ epsilon > 0, ∀ tau ∈ Metric.ball (0 : Real) epsilon,
      ∃ y : M, CoordExpRelAtTime (I := I) g x v tau y := by
  obtain ⟨epsilon, hepsilon, gamma, hgamma0, hvel, hgeo⟩ :=
    exists_coordGeoOn (I := I) g x v
  refine ⟨epsilon, hepsilon, ?_⟩
  intro tau htau
  refine ⟨gamma tau, Metric.ball (0 : Real) epsilon, ?_, htau,
    gamma, ?_, rfl⟩
  · exact Metric.mem_ball_self hepsilon
  · exact ⟨hgamma0, hvel, hgeo⟩

/-! ## Future normal-coordinate package -/

/-- Data that would make the relation-valued endpoint into a normal-coordinate
chart around `x`.

This is a package of future facts, not an existence theorem.  The field
`exp_realizes` keeps the map tied to the relation-valued endpoint above, while
`source_inj` and `target_open` record the local chart facts that should follow
from smooth dependence of the geodesic flow and the inverse function theorem. -/
structure NormalCoordinateData
    (g : SmoothRiemannianMetric I M) (x : M) where
  radius : Real
  radius_pos : 0 < radius
  exp : TangentSpace I x -> M
  exp_zero : exp 0 = x
  exp_realizes :
    ∀ v : TangentSpace I x,
      v ∈ Metric.ball (0 : TangentSpace I x) radius ->
        CoordExpRel (I := I) g x v (exp v)
  source_inj :
    Set.InjOn exp (Metric.ball (0 : TangentSpace I x) radius)
  target_open :
    IsOpen (exp '' Metric.ball (0 : TangentSpace I x) radius)

end Lecture07
end GlobalGeometry
end RicciFlower
