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
    Set.uIcc 0 tau ⊆ s ∧
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
    (hs : Set.uIcc 0 1 ⊆ s)
    (hseg : IsCoordGeodesicSegment (I := I) g x v gamma s) :
    expAt (I := I) g x v (gamma 1) := by
  exact ⟨s, hs, gamma, hseg, rfl⟩

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
    (s := Set.univ) (by intro t ht; simp) ?_
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

/-- Initial phase coordinate in the tangent-bundle chart centered at `0_x`. -/
private def initPhase (x : M) (v : TangentSpace I x) : E × E :=
  extChartAt I.tangent (phaseZero (I := I) x)
    (⟨x, v⟩ : TangentBundle I M)

/-- Interpret model coordinates in the tangent-bundle chart centered at
`0_x`. -/
private def phaseOfModel (x : M) (z : E × E) : TangentBundle I M :=
  (extChartAt I.tangent (phaseZero (I := I) x)).symm z

@[simp] private theorem initPhase_zero (x : M) :
    initPhase (I := I) x (0 : TangentSpace I x) =
      extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x) := by
  rfl

/-- The initial-phase chart coordinate depends continuously on the initial
velocity at the zero vector. -/
private theorem initPhase_continuousAt_zero (x : M) :
    ContinuousAt
      (initPhase (I := I) x)
      (0 : TangentSpace I x) := by
  have hmk :
      ContinuousAt
        (fun v : TangentSpace I x =>
          (⟨x, v⟩ : TangentBundle I M))
        (0 : TangentSpace I x) := by
    simpa using
      (FiberBundle.continuous_totalSpaceMk E
        (TangentSpace I : M -> Type _) x).continuousAt
  have hchart :
      ContinuousAt
        (fun q : TangentBundle I M =>
          extChartAt I.tangent (phaseZero (I := I) x) q)
        (phaseZero (I := I) x) :=
    continuousAt_extChartAt (I := I.tangent)
      (phaseZero (I := I) x)
  have hzero :
      (⟨x, (0 : TangentSpace I x)⟩ : TangentBundle I M) =
        phaseZero (I := I) x := by
    rfl
  simpa [initPhase] using hchart.comp_of_eq hmk hzero

/-- Small initial velocities have model coordinates close to the zero phase
coordinate. -/
private theorem initPhase_small
    (x : M) {r : NNReal} (hr : 0 < r) :
    ∃ ρ > 0, ∀ v ∈ Metric.ball (0 : TangentSpace I x) ρ,
      initPhase (I := I) x v ∈
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) r := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hrR : (0 : Real) < (r : Real) := by
    exact_mod_cast hr
  have hclosed : Metric.closedBall z0 (r : Real) ∈ 𝓝 z0 :=
    Metric.closedBall_mem_nhds z0 hrR
  have hpre :
      {v : TangentSpace I x |
        initPhase (I := I) x v ∈
          Metric.closedBall z0 (r : Real)} ∈
        𝓝 (0 : TangentSpace I x) := by
    simpa [z0] using
      (initPhase_continuousAt_zero (I := I) x).preimage_mem_nhds
        hclosed
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨ρ, hρ, ?_⟩
  intro v hv
  simpa [z0] using hρsub hv

/-- Fixed-chart model vector field for the geodesic spray near `0_x`.

This is the object that should feed the uniform time-one Picard-Lindelof
argument: solve `z' = modelSpray g x z` on `[0, 1]`, then map the solution
back to `TM` with `phaseOfModel`. -/
private def modelSpray
    (g : SmoothRiemannianMetric I M) (x : M) (z : E × E) : E × E :=
  let q : TangentBundle I M := phaseOfModel (I := I) x z
  tangentCoordChange I.tangent q (phaseZero (I := I) x) q
    (leviCivitaGeodesicSprayChart (I := I) g x q)

/-- Homogeneity of the quadratic Christoffel velocity term. -/
private theorem sprayQuad_smul
    (g : SmoothRiemannianMetric I M) (x : M)
    (y v : E) (a : Real) (k : CoordinateIdx (𝕜 := Real) E) :
    leviCivitaGeodesicSprayQuadratic (I := I) g x y (a • v) k =
      (a * a) *
        leviCivitaGeodesicSprayQuadratic (I := I) g x y v k := by
  classical
  simp [leviCivitaGeodesicSprayQuadratic, modelCoord, map_smul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Homogeneity of the model-space spray acceleration. -/
private theorem sprayAccel_smul
    (g : SmoothRiemannianMetric I M) (x : M)
    (y v : E) (a : Real) :
    leviCivitaGeodesicSprayAcceleration (I := I) g x y (a • v) =
      (a * a) •
        leviCivitaGeodesicSprayAcceleration (I := I) g x y v := by
  classical
  apply (Module.finBasis Real E).ext_elem
  intro k
  change modelCoord k
      (leviCivitaGeodesicSprayAcceleration (I := I) g x y (a • v)) =
    modelCoord k
      ((a * a) • leviCivitaGeodesicSprayAcceleration (I := I) g x y v)
  rw [modelCoord_leviCivitaGeodesicSprayAcceleration]
  have hrhs :
      modelCoord k
          ((a * a) •
            leviCivitaGeodesicSprayAcceleration (I := I) g x y v) =
        (a * a) * modelCoord k
          (leviCivitaGeodesicSprayAcceleration (I := I) g x y v) := by
    simp [modelCoord, map_smul]
  rw [hrhs, modelCoord_leviCivitaGeodesicSprayAcceleration,
    sprayQuad_smul]
  ring

/-- The tangent-bundle chart inverse centered at `0_x` is smooth at the chart
coordinate of `0_x`. -/
private theorem phaseOfModel_cdAt
    [I.Boundaryless] (x : M) :
    ContMDiffAt 𝓘(Real, E × E) I.tangent 1
      (phaseOfModel (I := I) x)
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  have hwithin :
      ContMDiffWithinAt 𝓘(Real, E × E) I.tangent 1
        (extChartAt I.tangent (phaseZero (I := I) x)).symm
        (Set.range I.tangent)
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) :=
    contMDiffWithinAt_extChartAt_symm_range_self
      (I := I.tangent) (x := phaseZero (I := I) x) (n := (1 : WithTop ℕ∞))
  have hrange :
      Set.range I.tangent ∈
        𝓝 (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I.tangent)]
    exact Filter.univ_mem
  simpa [phaseOfModel] using hwithin.contMDiffAt hrange

/-- In the fixed tangent-bundle chart, the model vector field is locally the
chart-fiber RHS used to define the spray. -/
private theorem modelSpray_eq_fiber
    (g : SmoothRiemannianMetric I M) (x : M) {z : E × E}
    (hsrc : (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source) :
    modelSpray (I := I) g x z =
      leviCivitaGeodesicSprayChartFiber (I := I) g x
        (phaseOfModel (I := I) x z) := by
  classical
  let q : TangentBundle I M := phaseOfModel (I := I) x z
  let lift : Real -> TangentBundle I M :=
    fun t : Real => if t = 0 then phaseZero (I := I) x else q
  have hlift0 :
      lift 0 = (⟨x, (0 : E)⟩ : TangentBundle I M) := by
    simp [lift, phaseZero]
  have hsrc1 : (lift 1).proj ∈ (extChartAt I x).source := by
    simpa [lift, q] using hsrc
  have h :=
    chartVF_eq_fiber (I := I) (g := g) (x := x)
      (v0 := (0 : TangentSpace I x)) (lift := lift)
      (t0 := 0) (t := 1) hlift0 hsrc1
  have hone : (1 : Real) ≠ 0 := one_ne_zero
  have hlift1 : lift 1 = q := by
    simp [lift, hone]
  change
    tangentCoordChange I.tangent (lift 1) (lift 0) (lift 1)
        (leviCivitaGeodesicSprayChart (I := I) g x (lift 1)) =
      leviCivitaGeodesicSprayChartFiber (I := I) g x (lift 1) at h
  rw [hlift1, hlift0] at h
  simpa [modelSpray, q, phaseZero] using h

/-- The first component of the tangent-bundle chart centered over `x` is the
base `extChartAt x` coordinate. -/
private theorem chartPushLift_fst_eq_extChartAt_proj
    {x : M} {v0 : TangentSpace I x}
    {lift : Real -> TangentBundle I M} {t0 : Real}
    (hlift0 : lift t0 = (⟨x, v0⟩ : TangentBundle I M))
    {t : Real} (_hsrc : (lift t).proj ∈ (extChartAt I x).source) :
    (chartPushLift (I := I) lift t0 t).1 =
      extChartAt I x (lift t).proj := by
  rcases hq : lift t with ⟨y, w⟩
  simp [chartPushLift, hlift0, hq, TangentBundle.chartAt, extChartAt]

/-- On the fixed tangent-bundle chart target, the model spray is the explicit
first-order system `(x', v') = (v, -Γ(v,v))`. -/
private theorem modelSpray_eq_pair
    (g : SmoothRiemannianMetric I M) (x : M) {z : E × E}
    (hztarget : z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target)
    (hsrc : (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source) :
    modelSpray (I := I) g x z =
      (z.2, leviCivitaGeodesicSprayAcceleration (I := I) g x z.1 z.2) := by
  classical
  let q : TangentBundle I M := phaseOfModel (I := I) x z
  let lift : Real -> TangentBundle I M :=
    fun t : Real => if t = 0 then phaseZero (I := I) x else q
  have hlift0 :
      lift 0 = (⟨x, (0 : E)⟩ : TangentBundle I M) := by
    simp [lift, phaseZero]
  have hqz :
      extChartAt I.tangent (phaseZero (I := I) x) q = z := by
    exact PartialEquiv.right_inv _ hztarget
  have hone : (1 : Real) ≠ 0 := one_ne_zero
  have hlift1 : lift 1 = q := by
    simp [lift, hone]
  have hsrc1 : (lift 1).proj ∈ (extChartAt I x).source := by
    simpa [hlift1, q] using hsrc
  have hchart :
      chartPushLift (I := I) lift 0 1 = z := by
    simpa [chartPushLift, hlift0, hlift1, q, phaseZero] using hqz
  have hfst :
      z.1 = extChartAt I x q.proj := by
    have h :=
      chartPushLift_fst_eq_extChartAt_proj
        (I := I) (lift := lift) (t0 := 0) (t := 1)
        hlift0 hsrc1
    have hz := congrArg Prod.fst hchart
    rw [h] at hz
    simpa [hlift1, q] using hz.symm
  have hsnd :
      z.2 = chartFiberCoordAt (I := I) x q := by
    have h :=
      chartPushLift_snd_eq_chartFiberCoordAt
        (I := I) (lift := lift) (t0 := 0) (t := 1)
        hlift0 hsrc1
    have hz := congrArg Prod.snd hchart
    rw [h] at hz
    simpa [hlift1, q] using hz.symm
  rw [modelSpray_eq_fiber (I := I) g x hsrc]
  simp [leviCivitaGeodesicSprayChartFiber, q, hfst, hsnd]

/-- The tangent-bundle chart target centered at `0_x` is fiberwise full, so
scaling the second model coordinate preserves target membership. -/
private theorem phaseTarget_smul
    [I.Boundaryless] (x : M) {z : E × E} {a : Real}
    (hz : z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target) :
    (z.1, a • z.2) ∈
      (extChartAt I.tangent (phaseZero (I := I) x)).target := by
  rw [FiberBundle.extChartAt_target] at hz ⊢
  exact ⟨hz.1, trivial⟩

/-- Scaling the fiber model coordinate keeps the reconstructed point over the
same fixed base chart source. -/
private theorem phaseSrc_smul
    [I.Boundaryless] (x : M) {z : E × E} {a : Real}
    (hz : z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target) :
    (phaseOfModel (I := I) x (z.1, a • z.2)).proj ∈
      (extChartAt I x).source := by
  have hz' := phaseTarget_smul (I := I) x (z := z) (a := a) hz
  have hqsrc :
      phaseOfModel (I := I) x (z.1, a • z.2) ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).source := by
    exact (extChartAt I.tangent (phaseZero (I := I) x)).map_target hz'
  simpa [phaseOfModel, phaseZero, extChartAt_source,
    TangentBundle.mem_chart_source_iff] using hqsrc.1

/-- Rescale a model-space spray solution so that a short-time solution becomes
a time-one candidate. -/
private def modelRescale (α : Real -> E × E) (τ : Real) : Real -> E × E :=
  fun s => ((α (τ * s)).1, τ • (α (τ * s)).2)

@[simp] private theorem modelRescale_zero
    (α : Real -> E × E) (τ : Real) :
    modelRescale α τ 0 = ((α 0).1, τ • (α 0).2) := by
  simp [modelRescale]

private theorem deriv_fst
    {F : Real -> E × E} {F' : E × E} {t : Real}
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun s : Real => (F s).1) F'.1 t := by
  have hfst : HasFDerivAt (ContinuousLinearMap.fst Real E E)
      (ContinuousLinearMap.fst Real E E) (F t) :=
    (ContinuousLinearMap.fst Real E E).hasFDerivAt
  simpa [Function.comp_def] using hfst.comp_hasDerivAt t hF

private theorem deriv_snd
    {F : Real -> E × E} {F' : E × E} {t : Real}
    (hF : HasDerivAt F F' t) :
    HasDerivAt (fun s : Real => (F s).2) F'.2 t := by
  have hsnd : HasFDerivAt (ContinuousLinearMap.snd Real E E)
      (ContinuousLinearMap.snd Real E E) (F t) :=
    (ContinuousLinearMap.snd Real E E).hasFDerivAt
  simpa [Function.comp_def] using hsnd.comp_hasDerivAt t hF

/-- Homogeneous reparametrization for the fixed-chart model spray. -/
private theorem modelRescale_deriv
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε τ s : Real} {α : Real -> E × E}
    (hαderiv : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt α (modelSpray (I := I) g x (α t)) t)
    (hsrc : ∀ t ∈ Set.Icc (-ε) ε,
      α t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (α t)).proj ∈
          (extChartAt I x).source)
    (ht : τ * s ∈ Set.Ioo (-ε) ε) :
    HasDerivAt (modelRescale α τ)
      (modelSpray (I := I) g x (modelRescale α τ s)) s := by
  let t : Real := τ * s
  have htIcc : t ∈ Set.Icc (-ε) ε := Set.Ioo_subset_Icc_self ht
  have hscale : HasDerivAt (fun r : Real => τ * r) τ s := by
    simpa using (hasDerivAt_const_mul τ (x := s))
  have hcomp :
      HasDerivAt (fun r : Real => α (τ * r))
        (τ • modelSpray (I := I) g x (α t)) s := by
    simpa [t, Function.comp_def] using
      (hαderiv t ht).hasFDerivAt.comp_hasDerivAt s hscale
  have hfst :
      HasDerivAt (fun r : Real => (α (τ * r)).1)
        (τ • (modelSpray (I := I) g x (α t)).1) s := by
    simpa using deriv_fst hcomp
  have hsnd0 :
      HasDerivAt (fun r : Real => (α (τ * r)).2)
        (τ • (modelSpray (I := I) g x (α t)).2) s := by
    simpa using deriv_snd hcomp
  have hsnd :
      HasDerivAt (fun r : Real => τ • (α (τ * r)).2)
        (τ • (τ • (modelSpray (I := I) g x (α t)).2)) s := by
    simpa using hsnd0.const_smul τ
  have hprod :
      HasDerivAt (modelRescale α τ)
        (τ • (modelSpray (I := I) g x (α t)).1,
          τ • (τ • (modelSpray (I := I) g x (α t)).2)) s := by
    simpa [modelRescale, t] using hfst.prodMk hsnd
  have hαtarget :
      α t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target :=
    (hsrc t htIcc).1
  have hαsrc :
      (phaseOfModel (I := I) x (α t)).proj ∈ (extChartAt I x).source :=
    (hsrc t htIcc).2
  have hβtarget :
      modelRescale α τ s ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target := by
    simpa [modelRescale, t] using
      phaseTarget_smul (I := I) x (z := α t) (a := τ) hαtarget
  have hβsrc :
      (phaseOfModel (I := I) x (modelRescale α τ s)).proj ∈
        (extChartAt I x).source := by
    simpa [modelRescale, t] using
      phaseSrc_smul (I := I) x (z := α t) (a := τ) hαtarget
  have hαpair :=
    modelSpray_eq_pair (I := I) g x hαtarget hαsrc
  have hβpair :=
    modelSpray_eq_pair (I := I) g x hβtarget hβsrc
  rw [hβpair]
  simpa [modelRescale, t, hαpair, sprayAccel_smul,
    smul_smul, mul_assoc, mul_comm, mul_left_comm] using hprod

/-- A fixed-chart model solution maps back to an integral curve of the
chart-fixed spray. -/
private theorem modelSol_integralOn
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε : Real} {β : Real -> E × E}
    (hβderiv : ∀ t ∈ Metric.ball (0 : Real) ε,
      HasDerivAt β (modelSpray (I := I) g x (β t)) t)
    (hβsrc : ∀ t ∈ Metric.ball (0 : Real) ε,
      β t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (β t)).proj ∈
          (extChartAt I x).source) :
    IsMIntegralCurveOn
      (fun t : Real => phaseOfModel (I := I) x (β t))
      (leviCivitaGeodesicSprayChart (I := I) g x)
      (Metric.ball (0 : Real) ε) := by
  intro t ht
  let q0 : TangentBundle I M := phaseZero (I := I) x
  let q : TangentBundle I M := phaseOfModel (I := I) x (β t)
  have hβt_target :
      β t ∈ (extChartAt I.tangent q0).target := by
    simpa [q0] using (hβsrc t ht).1
  have hq_src0 : q ∈ (extChartAt I.tangent q0).source := by
    simpa [q, q0, phaseOfModel] using
      (extChartAt I.tangent q0).map_target hβt_target
  have hq_src_self : q ∈ (extChartAt I.tangent q).source :=
    mem_extChartAt_source (I := I.tangent) q
  have hβderiv_t : HasDerivAt β
      (tangentCoordChange I.tangent q q0 q
        (leviCivitaGeodesicSprayChart (I := I) g x q)) t := by
    simpa [modelSpray, q, q0] using hβderiv t ht
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨?_, HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  · exact (continuousAt_extChartAt_symm'' hβt_target).comp hβderiv_t.continuousAt
  · simp only [mfld_simps, hasDerivWithinAt_univ]
    change HasDerivAt
      ((extChartAt I.tangent q ∘ (extChartAt I.tangent q0).symm) ∘ β)
      (leviCivitaGeodesicSprayChart (I := I) g x q) t
    rw [← tangentCoordChange_self (I := I.tangent) (x := q) (z := q)
        (v := leviCivitaGeodesicSprayChart (I := I) g x q) hq_src_self,
      ← tangentCoordChange_comp (I := I.tangent) (x := q0)
        ⟨⟨hq_src_self, hq_src0⟩, hq_src_self⟩]
    apply HasFDerivAt.comp_hasDerivAt _ _ hβderiv_t
    apply HasFDerivWithinAt.hasFDerivAt (s := Set.range I.tangent) _ <|
      mem_nhds_iff.mpr ⟨(extChartAt I.tangent q0).target,
        extChartAt_target_subset_range q0,
        isOpen_extChartAt_target (I := I.tangent) q0, hβt_target⟩
    rw [← (extChartAt I.tangent q0).right_inv hβt_target]
    exact hasFDerivWithinAt_tangentCoordChange
      (I := I.tangent) ⟨hq_src0, hq_src_self⟩

/-- Same-base initial tangent vectors have the expected model coordinates in
the tangent-bundle chart centered at `0_x`. -/
private theorem initPhase_eq_pair (x : M) (v : TangentSpace I x) :
    initPhase (I := I) x v = (extChartAt I x x, v) := by
  let q : TangentBundle I M := ⟨x, v⟩
  let lift : Real -> TangentBundle I M :=
    fun t : Real => if t = 0 then phaseZero (I := I) x else q
  have hlift0 :
      lift 0 = (⟨x, (0 : E)⟩ : TangentBundle I M) := by
    simp [lift, phaseZero]
  have hone : (1 : Real) ≠ 0 := one_ne_zero
  have hlift1 : lift 1 = q := by
    simp [lift, hone]
  have hsrc1 : (lift 1).proj ∈ (extChartAt I x).source := by
    simp [hlift1, q]
  have hchart :
      chartPushLift (I := I) lift 0 1 = initPhase (I := I) x v := by
    simp [chartPushLift, initPhase, hlift0, hlift1, q, phaseZero]
  apply Prod.ext
  · have hfst :=
      chartPushLift_fst_eq_extChartAt_proj
        (I := I) (lift := lift) (t0 := 0) (t := 1)
        hlift0 hsrc1
    have hz := congrArg Prod.fst hchart
    rw [hfst] at hz
    simpa [hlift1, q] using hz
  · have hsnd :=
      chartPushLift_snd_eq_chartFiberCoordAt
        (I := I) (lift := lift) (t0 := 0) (t := 1)
        hlift0 hsrc1
    have hz := congrArg Prod.snd hchart
    rw [hsnd] at hz
    have hfiber : chartFiberCoordAt (I := I) x q = v := by
      simpa [q] using chartFiberCoordAt_self (I := I) (u := q)
    rw [hlift1, hfiber] at hz
    exact hz.symm

/-- Scaling the fiber coordinate of an initial phase is the initial phase of
the scaled tangent vector. -/
private theorem initPhase_smul
    (x : M) (a : Real) (v : TangentSpace I x) :
    ((initPhase (I := I) x v).1, a • (initPhase (I := I) x v).2) =
      initPhase (I := I) x (a • v) := by
  rw [initPhase_eq_pair, initPhase_eq_pair]
  rfl

private theorem half_mul_mem_Ioo
    {ε s : Real} (hε : 0 < ε)
    (hs : s ∈ Metric.ball (0 : Real) 2) :
    (ε / 2) * s ∈ Set.Ioo (-ε) ε := by
  have hτ : 0 < ε / 2 := half_pos hε
  have hsabs : |s| < 2 := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hs
  rcases abs_lt.mp hsabs with ⟨hslo, hshi⟩
  have hlo : (ε / 2) * (-2) < (ε / 2) * s :=
    mul_lt_mul_of_pos_left hslo hτ
  have hhi : (ε / 2) * s < (ε / 2) * 2 :=
    mul_lt_mul_of_pos_left hshi hτ
  constructor <;> nlinarith

private theorem uIcc01_mem_ball_two {t : Real}
    (ht : t ∈ Set.uIcc 0 1) :
    t ∈ Metric.ball (0 : Real) 2 := by
  rw [Metric.mem_ball]
  have hdist : dist (0 : Real) t ≤ dist (0 : Real) 1 :=
    Real.dist_left_le_of_mem_uIcc ht
  norm_num at hdist ⊢
  linarith

/-- The chart-fiber RHS, pulled back to the fixed model chart, is smooth at
`0_x`. -/
private theorem sprayFiber_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1
      (fun z : E × E =>
        leviCivitaGeodesicSprayChartFiber (I := I) g x
          (phaseOfModel (I := I) x z))
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  have hfiber :
      ContMDiffAt I.tangent 𝓘(Real, E × E) 1
        (leviCivitaGeodesicSprayChartFiber (I := I) g x)
        (phaseZero (I := I) x) := by
    have htop :=
      leviCivitaGeodesicSprayChartFiber_contMDiffAt_self
        (I := I) g x (0 : TangentSpace I x)
    simpa [phaseZero] using
      htop.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hphase := phaseOfModel_cdAt (I := I) x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hphase_self :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hfiber' :
      ContMDiffAt I.tangent 𝓘(Real, E × E) 1
        (leviCivitaGeodesicSprayChartFiber (I := I) g x)
        (phaseOfModel (I := I) x z0) := by
    simpa [hphase_self] using hfiber
  have hcomp :
      ContMDiffAt 𝓘(Real, E × E) 𝓘(Real, E × E) 1
        ((leviCivitaGeodesicSprayChartFiber (I := I) g x) ∘
          phaseOfModel (I := I) x)
        z0 :=
    hfiber'.comp
      (x := z0)
      hphase
  simpa [Function.comp_def, z0] using hcomp.contDiffAt

/-- The fixed-chart model spray is `C^1` at the zero phase point. -/
private theorem modelSpray_cdAt
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ContDiffAt Real 1 (modelSpray (I := I) g x)
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hfiber := sprayFiber_cdAt (I := I) g x
  have hsrc_nhds :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseZero (I := I) x) := by
    have hproj :
        ContinuousAt
          (fun q : TangentBundle I M => q.proj)
          (phaseZero (I := I) x) :=
      (FiberBundle.continuous_proj E
        (TangentSpace I : M -> Type _)).continuousAt
    have hxsrc :
        (phaseZero (I := I) x).proj ∈ (extChartAt I x).source := by
      simp [phaseZero]
    exact hproj.preimage_mem_nhds
      (by
        simpa [extChartAt_source] using
          extChartAt_source_mem_nhds (I := I) x)
  have hphase_self :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hsrc_nhds' :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseOfModel (I := I) x z0) := by
    simpa [hphase_self] using hsrc_nhds
  have hsrc_event :
      ∀ᶠ z in 𝓝 z0,
        (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source := by
    have hphase_cont := (phaseOfModel_cdAt (I := I) x).continuousAt
    simpa [z0] using hphase_cont.preimage_mem_nhds hsrc_nhds'
  refine hfiber.congr_of_eventuallyEq ?_
  filter_upwards [hsrc_event] with z hz
  exact modelSpray_eq_fiber (I := I) g x hz

/-- The zero phase point is an equilibrium of the fixed-chart model spray. -/
private theorem modelSpray_zero
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) :
    modelSpray (I := I) g x
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) = 0 := by
  have hq :
      phaseOfModel (I := I) x
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) =
        phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hsrc :
      (phaseOfModel (I := I) x
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x))).proj ∈
        (extChartAt I x).source := by
    rw [hq]
    simp [phaseZero]
  rw [modelSpray_eq_fiber (I := I) g x hsrc, hq]
  have hv :
      chartFiberCoordAt (I := I) x (phaseZero (I := I) x) = 0 := by
    simp [phaseZero]
    simpa [phaseZero] using
      chartFiberCoordAt_self (I := I)
        (u := (phaseZero (I := I) x))
  change
    (chartFiberCoordAt (I := I) x (phaseZero (I := I) x),
      leviCivitaGeodesicSprayAcceleration (I := I) g x
        (extChartAt I x (phaseZero (I := I) x).proj)
        (chartFiberCoordAt (I := I) x (phaseZero (I := I) x))) = (0, 0)
  rw [hv]
  simp [leviCivitaGeodesicSprayAcceleration,
    leviCivitaGeodesicSprayQuadratic, modelCoord]

/-- Local Picard-Lindelof data for the fixed-chart model spray near the zero
phase point.

This is uniform for initial phase points in a small closed model ball, but only
on a short time interval.  Extending this checked local flow to time `1` is the
remaining continuation argument for `exists_exp_one`. -/
private theorem modelSpray_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal), ∃ (_hr : 0 < r),
        ∀ t0 : Real,
          IsPicardLindelof
            (fun _ : Real => modelSpray (I := I) g x)
            (tmin := t0 - ε) (tmax := t0 + ε)
            ⟨t0, by simp [le_of_lt hε]⟩
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x))
            a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one
      (modelSpray_cdAt (I := I) g x)
  exact ⟨ε, hε, a, r, L, K, hr, hpl⟩

/-- Picard-Lindelof local solutions stay in the controlling closed ball.

Mathlib's public existence theorem returns the derivative equation but hides
this bound.  The normal-coordinate endpoint proof needs the bound to keep the
model solution inside the fixed tangent-bundle chart source. -/
private theorem plSol_bounded
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 x : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K)
    (hx : x ∈ Metric.closedBall x0 r) :
    ∃ α : Real -> F, α t0 = x ∧
      (∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt α (f t (α t)) (Set.Icc tmin tmax) t) ∧
      ∀ t : Real, α t ∈ Metric.closedBall x0 a := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_, ?_⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le)
      x ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro t
    exact α.compProj_mem_closedBall hf.mul_max_le

/-- Functional Picard-Lindelof flow with both Lipschitz dependence on the
initial condition and the closed-ball bound for the same chosen flow. -/
private theorem plFlow_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {f : Real -> F -> F} {tmin tmax : Real}
    {t0 : Set.Icc tmin tmax} {x0 : F} {a r L K : NNReal}
    (hf : IsPicardLindelof f t0 x0 a r L K) :
    ∃ α : F -> Real -> F,
      (∀ x ∈ Metric.closedBall x0 r, α x t0 = x ∧
        ∀ t ∈ Set.Icc tmin tmax,
          HasDerivWithinAt (α x) (f t (α x t)) (Set.Icc tmin tmax) t) ∧
      (∀ x ∈ Metric.closedBall x0 r, ∀ t : Real,
        α x t ∈ Metric.closedBall x0 a) ∧
      ∃ L' : NNReal, ∀ t ∈ Set.Icc tmin tmax,
        LipschitzOnWith L' (fun x => α x t) (Metric.closedBall x0 r) := by
  classical
  have hfixed (x : F) (hx : x ∈ Metric.closedBall x0 r) :=
    ODE.FunSpace.exists_isFixedPt_next hf hx
  choose β hβ using hfixed
  let α : F -> Real -> F := fun x =>
    if hx : x ∈ Metric.closedBall x0 r then (β x hx).compProj else 0
  refine ⟨α, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · change (if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t0 = x
      rw [dif_pos hx, ODE.FunSpace.compProj_val, ← hβ x hx,
        ODE.FunSpace.next_apply₀]
    · intro t ht
      change HasDerivWithinAt
        (if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0)
        (f t ((if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t))
        (Set.Icc tmin tmax) t
      rw [dif_pos hx]
      apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
        (β x hx).continuous_compProj.continuousOn
        (fun _ _ => (β x hx).compProj_mem_closedBall hf.mul_max_le)
        x ht).congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hβ x hx]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
  · intro x hx t
    change (if hx' : x ∈ Metric.closedBall x0 r then
        (β x hx').compProj else 0) t ∈ Metric.closedBall x0 a
    rw [dif_pos hx]
    exact (β x hx).compProj_mem_closedBall hf.mul_max_le
  · obtain ⟨L', hL'⟩ :=
      ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨L', fun t ht => LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    have : Nonempty (Set.Icc tmin tmax) := ⟨t0⟩
    have hdist :=
      hL' x y hx hy (β x hx) (β y hy) (hβ x hx) (hβ y hy)
    have hpoint :=
      (ContinuousMap.dist_le_iff_of_nonempty.mp hdist)
        (⟨t, ht⟩ : Set.Icc tmin tmax)
    change dist
        ((if hx' : x ∈ Metric.closedBall x0 r then
          (β x hx').compProj else 0) t)
        ((if hy' : y ∈ Metric.closedBall x0 r then
          (β y hy').compProj else 0) t) ≤
      ↑L' * dist x y
    rw [dif_pos hx, dif_pos hy]
    rw [ODE.FunSpace.compProj_of_mem ht, ODE.FunSpace.compProj_of_mem ht]
    simpa [ODE.FunSpace.toContinuousMap_apply_eq_apply] using hpoint

/-- A Picard-Lindelof solution whose controlling ball lies in the fixed chart
source gives an ordinary model ODE solution on the open time interval, with
source control for `phaseOfModel`. -/
private theorem modelFlow_src_of_pl
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε : Real} (hε : 0 < ε) {a r L K : NNReal}
    (hpl : IsPicardLindelof
      (fun _ : Real => modelSpray (I := I) g x)
      (tmin := 0 - ε) (tmax := 0 + ε)
      ⟨0, by simp [le_of_lt hε]⟩
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x))
      a r L K)
    (hsrc : Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) a ⊆
        {z : E × E |
          z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source})
    {z : E × E}
    (hz : z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r) :
    ∃ α : Real -> E × E,
      α 0 = z ∧
        (∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt α (modelSpray (I := I) g x (α t)) t) ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          α t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
            (phaseOfModel (I := I) x (α t)).proj ∈
              (extChartAt I x).source := by
  obtain ⟨α, hα0, hαderiv, hαbound⟩ :=
    plSol_bounded (F := E × E) (f := fun _ : Real =>
      modelSpray (I := I) g x) hpl hz
  refine ⟨α, by simpa using hα0, ?_, ?_⟩
  · intro t ht
    have htIcc : t ∈ Set.Icc (-ε) ε := Set.Ioo_subset_Icc_self ht
    have hwithin := hαderiv t (by simpa using htIcc)
    have hIcc_mem : Set.Icc (0 - ε) (0 + ε) ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  · intro t ht
    exact hsrc (hαbound t)

/-- The fixed tangent-bundle model chart is a valid source neighborhood for
points whose model coordinates are close to the zero phase. -/
private theorem modelSrc_nhds
    [I.Boundaryless] (x : M) :
    {z : E × E |
      z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x z).proj ∈ (extChartAt I x).source} ∈
      𝓝 (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) := by
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  have hsrc_nhds :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseZero (I := I) x) := by
    have hproj :
        ContinuousAt
          (fun q : TangentBundle I M => q.proj)
          (phaseZero (I := I) x) :=
      (FiberBundle.continuous_proj E
        (TangentSpace I : M -> Type _)).continuousAt
    exact hproj.preimage_mem_nhds
      (by
        simpa [extChartAt_source] using
          extChartAt_source_mem_nhds (I := I) x)
  have hphase_self :
      phaseOfModel (I := I) x z0 = phaseZero (I := I) x := by
    exact PartialEquiv.left_inv _ (mem_extChartAt_source (I := I.tangent)
      (phaseZero (I := I) x))
  have hsrc_nhds' :
      {q : TangentBundle I M | q.proj ∈ (extChartAt I x).source} ∈
        𝓝 (phaseOfModel (I := I) x z0) := by
    simpa [hphase_self] using hsrc_nhds
  have hphase_cont := (phaseOfModel_cdAt (I := I) x).continuousAt
  have htarget :
      (extChartAt I.tangent (phaseZero (I := I) x)).target ∈ 𝓝 z0 :=
    (isOpen_extChartAt_target (I := I.tangent)
      (phaseZero (I := I) x)).mem_nhds
      ((extChartAt I.tangent (phaseZero (I := I) x)).map_source
        (mem_extChartAt_source (I := I.tangent) (phaseZero (I := I) x)))
  exact Filter.inter_mem htarget
    (by
      simpa [z0, Set.preimage, Function.comp_def] using
        hphase_cont.preimage_mem_nhds hsrc_nhds')

/-- Picard-Lindelof data at time `0`, shrunk so the whole controlling model
ball stays in the fixed tangent-bundle chart source. -/
private theorem modelSpray_pl0_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (hε : 0 < ε), ∃ (a r L K : NNReal),
      0 < r ∧
        Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) a ⊆
          {z : E × E |
            z ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x z).proj ∈
                (extChartAt I x).source} ∧
        IsPicardLindelof
          (fun _ : Real => modelSpray (I := I) g x)
          (tmin := 0 - ε) (tmax := 0 + ε)
          ⟨0, by simp [le_of_lt hε]⟩
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x))
          a r L K := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ :=
    modelSpray_pl (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
    (modelSrc_nhds (I := I) x)
  have hpl0 := hpl 0
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hnonneg :
      (0 : Real) ≤
        (L : Real) * max ((0 + ε) - 0) (0 - (0 - ε)) := by
    exact mul_nonneg (NNReal.coe_nonneg L)
      (le_max_of_le_left (by linarith))
  have hra : (r : Real) ≤ (a : Real) := by
    have hmul := hpl0.mul_max_le
    nlinarith [hmul, hnonneg]
  have ha : 0 < a := by
    exact_mod_cast (lt_of_lt_of_le hrR hra)
  let δnn : NNReal := ⟨δ / 2, le_of_lt (half_pos hδ)⟩
  let a' : NNReal := min a δnn
  have hδnn : 0 < δnn := by
    change (0 : Real) < δ / 2
    exact half_pos hδ
  have ha' : 0 < a' := by
    exact lt_min ha hδnn
  let r' : NNReal := a' / 2
  have hr' : 0 < r' := by
    simp [r', ha']
  have hrlt : r' < a' := by
    simpa [r'] using half_lt_self ha'
  obtain ⟨ε', hε', hpl'⟩ :=
    IsPicardLindelof.exists_shrink_radius
      (f := fun _ : Real => modelSpray (I := I) g x)
      (t₀ := (0 : Real)) (ε := ε) hε hpl0
      (a' := a') (r' := r') (by exact min_le_left _ _) hrlt
  refine ⟨ε', hε', a', r', L, K, hr', ?_, hpl'⟩
  intro z hz
  apply hδsub
  rw [Metric.mem_ball]
  have hdist : dist z z0 ≤ (a' : Real) := by
    simpa [z0] using Metric.mem_closedBall.mp hz
  have haδ : (a' : Real) ≤ δ / 2 := by
    have : a' ≤ δnn := min_le_right _ _
    exact_mod_cast this
  calc
    dist z z0 ≤ (a' : Real) := hdist
    _ ≤ δ / 2 := haδ
    _ < δ := half_lt_self hδ

/-- Uniform short-time model flow with source control in the fixed
tangent-bundle chart around `0_x`. -/
private theorem modelFlow_src
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) r,
        ∃ α : Real -> E × E,
          α 0 = z ∧
            (∀ t ∈ Set.Ioo (-ε) ε,
              HasDerivAt α (modelSpray (I := I) g x (α t)) t) ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              α t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
                (phaseOfModel (I := I) x (α t)).proj ∈
                  (extChartAt I x).source := by
  obtain ⟨ε, hε, a, r, L, K, hr, hsrc, hpl⟩ :=
    modelSpray_pl0_src (I := I) g x
  refine ⟨ε, hε, r, hr, ?_⟩
  intro z hz
  exact modelFlow_src_of_pl (I := I) g x hε hpl hsrc hz

/-- Uniform short-time model flow with Lipschitz dependence on the initial
phase point.

This is the first analytic upgrade beyond relation-valued endpoint existence:
the Picard-Lindelof package supplies a single local flow `α z t` and a
Lipschitz estimate in the initial model phase `z`.  It does not yet assert
source control or strict differentiability of the endpoint map. -/
private theorem modelFlow_lipschitz
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ α : E × E -> Real -> E × E,
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          α z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (α z)
                (modelSpray (I := I) g x (α z t))
                (Set.Icc (-ε) ε) t) ∧
          ∃ L' : NNReal,
            ∀ t ∈ Set.Icc (-ε) ε,
              LipschitzOnWith L'
                (fun z => α z t)
                (Metric.closedBall
                  (extChartAt I.tangent (phaseZero (I := I) x)
                    (phaseZero (I := I) x)) r) := by
  obtain ⟨ε, hε, _a, r, _L, _K, hr, hpl⟩ :=
    modelSpray_pl (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨α, hα, L', hLip⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  refine ⟨ε, hε, r, hr, α, ?_, L', ?_⟩
  · intro z hz
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    refine ⟨(hα z hz').1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hα z hz').2 t ht'
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa [z0] using hLip t ht'

/-- Uniform short-time model flow with source control and Lipschitz dependence
for the same chosen functional flow. -/
private theorem modelFlow_srcLip
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∃ α : E × E -> Real -> E × E,
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          α z 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt (α z)
                (modelSpray (I := I) g x (α z t))
                (Set.Icc (-ε) ε) t) ∧
        (∀ z ∈ Metric.closedBall
            (extChartAt I.tangent (phaseZero (I := I) x)
              (phaseZero (I := I) x)) r,
          ∀ t ∈ Set.Icc (-ε) ε,
            α z t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
              (phaseOfModel (I := I) x (α z t)).proj ∈
                (extChartAt I x).source) ∧
        ∃ L' : NNReal,
          ∀ t ∈ Set.Icc (-ε) ε,
            LipschitzOnWith L'
              (fun z => α z t)
              (Metric.closedBall
                (extChartAt I.tangent (phaseZero (I := I) x)
                  (phaseZero (I := I) x)) r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hsrc, hpl⟩ :=
    modelSpray_pl0_src (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  obtain ⟨α, hα, hbound, L', hLip⟩ :=
    plFlow_bound (F := E × E) (f := fun _ : Real =>
      modelSpray (I := I) g x) hpl
  refine ⟨ε, hε, r, hr, α, ?_, ?_, L', ?_⟩
  · intro z hz
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    refine ⟨(hα z hz').1, ?_⟩
    intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa using (hα z hz').2 t ht'
  · intro z hz t ht
    have hz' : z ∈ Metric.closedBall z0 r := by
      simpa [z0] using hz
    exact hsrc (hbound z hz' t)
  · intro t ht
    have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
      simpa using ht
    simpa [z0] using hLip t ht'

/-- Short-time model flow produced by the local Picard-Lindelof package.

This is still a short-time statement.  It is the checked analytic producer
that should feed either a continuation argument or the homogeneous rescaling
argument for `exists_exp_one`. -/
private theorem modelFlow_short
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (ε : Real), ∃ (_hε : 0 < ε), ∃ (r : NNReal), ∃ (_hr : 0 < r),
      ∀ z ∈ Metric.closedBall
          (extChartAt I.tangent (phaseZero (I := I) x)
            (phaseZero (I := I) x)) r,
        ∃ α : Real -> E × E,
          α 0 = z ∧
            ∀ t ∈ Set.Icc (-ε) ε,
              HasDerivWithinAt α
                (modelSpray (I := I) g x (α t))
                (Set.Icc (-ε) ε) t := by
  obtain ⟨ε, hε, _a, r, _L, _K, hr, hpl⟩ :=
    modelSpray_pl (I := I) g x
  let z0 : E × E :=
    extChartAt I.tangent (phaseZero (I := I) x)
      (phaseZero (I := I) x)
  refine ⟨ε, hε, r, hr, ?_⟩
  intro z hz
  obtain ⟨α, hα0, hαderiv⟩ :=
    (hpl 0).exists_eq_forall_mem_Icc_hasDerivWithinAt
      (x := z) (by simpa [z0] using hz)
  refine ⟨α, hα0, ?_⟩
  intro t ht
  have ht' : t ∈ Set.Icc (0 - ε) (0 + ε) := by
    simpa using ht
  simpa using hαderiv t ht'

/-- Chart coordinate of the time-one endpoint produced from a fixed functional
model flow and the homogeneous time rescaling. -/
private def chartEnd
    (α : E × E -> Real -> E × E) (τ : Real) (x : M)
    (v : TangentSpace I x) : E :=
  (α (initPhase (I := I) x (τ⁻¹ • v)) τ).1

/-- Manifold endpoint produced from a fixed functional model flow and the
homogeneous time rescaling. -/
private def manifoldEnd
    (α : E × E -> Real -> E × E) (τ : Real) (x : M)
    (v : TangentSpace I x) : M :=
  (phaseOfModel (I := I) x
    (chartEnd (I := I) α τ x v,
      τ • (α (initPhase (I := I) x (τ⁻¹ • v)) τ).2)).proj

/-- The functional model endpoint realizes the relation-valued exponential
wherever the rescaled initial phase lies in the Picard-Lindelof ball. -/
private theorem end_expAt
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M)
    {ε : Real} (hε : 0 < ε) {r : NNReal}
    {α : E × E -> Real -> E × E}
    (hflow : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      α z 0 = z ∧
        ∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt (α z)
            (modelSpray (I := I) g x (α z t))
            (Set.Icc (-ε) ε) t)
    (hsrc : ∀ z ∈ Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r,
      ∀ t ∈ Set.Icc (-ε) ε,
        α z t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
          (phaseOfModel (I := I) x (α z t)).proj ∈
            (extChartAt I x).source)
    {v : TangentSpace I x}
    (hv : initPhase (I := I) x ((ε / 2)⁻¹ • v) ∈
      Metric.closedBall
        (extChartAt I.tangent (phaseZero (I := I) x)
          (phaseZero (I := I) x)) r) :
    expAt (I := I) g x v (manifoldEnd (I := I) α (ε / 2) x v) := by
  classical
  let τ : Real := ε / 2
  let u : TangentSpace I x := τ⁻¹ • v
  let z : E × E := initPhase (I := I) x u
  have hz : z ∈ Metric.closedBall
      (extChartAt I.tangent (phaseZero (I := I) x)
        (phaseZero (I := I) x)) r := by
    simpa [z, u, τ] using hv
  have hτ : 0 < τ := by
    exact half_pos hε
  have hα0 : α z 0 = z := (hflow z hz).1
  have hαderiv : ∀ t ∈ Set.Ioo (-ε) ε,
      HasDerivAt (α z) (modelSpray (I := I) g x (α z t)) t := by
    intro t ht
    have hwithin := (hflow z hz).2 t (Set.Ioo_subset_Icc_self ht)
    have hIcc_mem : Set.Icc (-ε) ε ∈ 𝓝 t := by
      simpa using Icc_mem_nhds ht.1 ht.2
    exact hwithin.hasDerivAt hIcc_mem
  have hαsrc : ∀ t ∈ Set.Icc (-ε) ε,
      α z t ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (α z t)).proj ∈
          (extChartAt I x).source := hsrc z hz
  let β : Real -> E × E := modelRescale (α z) τ
  let lift : Real -> TangentBundle I M :=
    fun s : Real => phaseOfModel (I := I) x (β s)
  let gamma : Curve M := projectCurve (I := I) lift
  have hτu : τ • u = v := by
    change τ • (τ⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  have hβ0 : β 0 = initPhase (I := I) x v := by
    calc
      β 0 = ((α z 0).1, τ • (α z 0).2) := by
        simp [β]
      _ = ((initPhase (I := I) x u).1,
            τ • (initPhase (I := I) x u).2) := by
        rw [hα0]
      _ = initPhase (I := I) x (τ • u) :=
        initPhase_smul (I := I) x τ u
      _ = initPhase (I := I) x v := by
        rw [hτu]
  have hqsrc :
      (⟨x, v⟩ : TangentBundle I M) ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).source := by
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
    simp [phaseZero]
  have hlift0 : lift 0 = (⟨x, v⟩ : TangentBundle I M) := by
    change phaseOfModel (I := I) x (β 0) =
      (⟨x, v⟩ : TangentBundle I M)
    rw [hβ0]
    simpa [initPhase] using
      PartialEquiv.left_inv
        (extChartAt I.tangent (phaseZero (I := I) x)) hqsrc
  have hβderiv : ∀ s ∈ Metric.ball (0 : Real) 2,
      HasDerivAt β (modelSpray (I := I) g x (β s)) s := by
    intro s hs
    exact modelRescale_deriv (I := I) g x hαderiv hαsrc
      (by simpa [τ] using half_mul_mem_Ioo hε hs)
  have hβsrc : ∀ s ∈ Metric.ball (0 : Real) 2,
      β s ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (β s)).proj ∈
          (extChartAt I x).source := by
    intro s hs
    have htIoo : τ * s ∈ Set.Ioo (-ε) ε := by
      simpa [τ] using half_mul_mem_Ioo hε hs
    have htIcc : τ * s ∈ Set.Icc (-ε) ε :=
      Set.Ioo_subset_Icc_self htIoo
    have hαtarget :
        α z (τ * s) ∈
          (extChartAt I.tangent (phaseZero (I := I) x)).target :=
      (hαsrc (τ * s) htIcc).1
    constructor
    · simpa [β, modelRescale] using
        phaseTarget_smul (I := I) x (z := α z (τ * s)) (a := τ)
          hαtarget
    · simpa [β, modelRescale] using
        phaseSrc_smul (I := I) x (z := α z (τ * s)) (a := τ)
          hαtarget
  have hspray : IsMIntegralCurveOn lift
      (leviCivitaGeodesicSprayChart (I := I) g x)
      (Metric.ball (0 : Real) 2) := by
    simpa [lift, β] using
      modelSol_integralOn (I := I) g x hβderiv hβsrc
  have hspray0 : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x) 0 :=
    hspray.isMIntegralCurveAt
      (Metric.ball_mem_nhds (0 : Real) (by norm_num : (0 : Real) < 2))
  have hsrcBall : ∀ s ∈ Metric.ball (0 : Real) 2,
      projectCurve (I := I) lift s ∈
        (extChartAtCoordinateData (I := I) x).domain := by
    intro s hs
    simpa [projectCurve, lift, extChartAtCoordinateData, coordinateFrameSet,
      coordinateTrivializationAt, extChartAt_source] using (hβsrc s hs).2
  have hy : gamma 1 = manifoldEnd (I := I) α τ x v := by
    simp [gamma, lift, β, manifoldEnd, chartEnd, modelRescale, z, u, τ]
  rw [← hy]
  refine expAt_of_segment (I := I) (g := g)
    (x := x) (v := v) (gamma := gamma) (s := Set.uIcc 0 1)
    (by intro t ht; exact ht) ?_
  refine ⟨?_, ?_, ?_⟩
  · simpa [gamma] using
      projectCurve_zero_of_lift (I := I)
        (u := (⟨x, v⟩ : TangentBundle I M)) hlift0
  · simpa [gamma] using
      projectCurve_initialVelocity_of_geodesicSprayIntegral
        (I := I) (g := g) (u := (⟨x, v⟩ : TangentBundle I M))
        (f := lift) hlift0 hspray0
  · constructor
    · intro t ht
      exact hsrcBall t (uIcc01_mem_ball_two ht)
    · intro t ht
      have htball : t ∈ Metric.ball (0 : Real) 2 :=
        uIcc01_mem_ball_two ht
      have hode := coordSprayODEOn
        (I := I) (g := g) (x := x) (v := v)
        (lift := lift) (epsilon := (2 : Real)) (t := t)
        hlift0 hspray htball hsrcBall
      exact hode.zeroAccel

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
  classical
  obtain ⟨ε, hε, rModel, hrModel, hflow⟩ :=
    modelFlow_src (I := I) g x
  obtain ⟨ρ, hρ, hsmall⟩ := initPhase_small (I := I) x hrModel
  let τ : Real := ε / 2
  have hτ : 0 < τ := by
    exact half_pos hε
  let R : Real := τ * ρ
  have hR : 0 < R := mul_pos hτ hρ
  refine ⟨R, hR, ?_⟩
  intro v hv
  let u : TangentSpace I x := τ⁻¹ • v
  have hu : u ∈ Metric.ball (0 : TangentSpace I x) ρ := by
    rw [Metric.mem_ball] at hv ⊢
    have hvnorm : ‖v‖ < τ * ρ := by
      simpa [R, dist_zero_right] using hv
    have hscale :=
      mul_lt_mul_of_pos_left hvnorm (inv_pos.mpr hτ)
    have hnormu : ‖τ⁻¹ • v‖ < ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
      rw [← mul_assoc, inv_mul_cancel₀ hτ.ne', one_mul] at hscale
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscale
    simpa [u, dist_zero_right] using hnormu
  obtain ⟨α, hα0, hαderiv, hαsrc⟩ :=
    hflow (initPhase (I := I) x u) (hsmall u hu)
  let β : Real -> E × E := modelRescale α τ
  let lift : Real -> TangentBundle I M :=
    fun s : Real => phaseOfModel (I := I) x (β s)
  let gamma : Curve M := projectCurve (I := I) lift
  have hτu : τ • u = v := by
    change τ • (τ⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  have hβ0 : β 0 = initPhase (I := I) x v := by
    calc
      β 0 = ((α 0).1, τ • (α 0).2) := by
        simp [β]
      _ = ((initPhase (I := I) x u).1,
            τ • (initPhase (I := I) x u).2) := by
        rw [hα0]
      _ = initPhase (I := I) x (τ • u) :=
        initPhase_smul (I := I) x τ u
      _ = initPhase (I := I) x v := by
        rw [hτu]
  have hqsrc :
      (⟨x, v⟩ : TangentBundle I M) ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).source := by
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
    simp [phaseZero]
  have hlift0 : lift 0 = (⟨x, v⟩ : TangentBundle I M) := by
    change phaseOfModel (I := I) x (β 0) =
      (⟨x, v⟩ : TangentBundle I M)
    rw [hβ0]
    simpa [initPhase] using
      PartialEquiv.left_inv
        (extChartAt I.tangent (phaseZero (I := I) x)) hqsrc
  have hβderiv : ∀ s ∈ Metric.ball (0 : Real) 2,
      HasDerivAt β (modelSpray (I := I) g x (β s)) s := by
    intro s hs
    exact modelRescale_deriv (I := I) g x hαderiv hαsrc
      (half_mul_mem_Ioo hε hs)
  have hβsrc : ∀ s ∈ Metric.ball (0 : Real) 2,
      β s ∈ (extChartAt I.tangent (phaseZero (I := I) x)).target ∧
        (phaseOfModel (I := I) x (β s)).proj ∈
          (extChartAt I x).source := by
    intro s hs
    have htIoo := half_mul_mem_Ioo hε hs
    have htIcc : τ * s ∈ Set.Icc (-ε) ε :=
      Set.Ioo_subset_Icc_self htIoo
    have hαtarget : α (τ * s) ∈
        (extChartAt I.tangent (phaseZero (I := I) x)).target :=
      (hαsrc (τ * s) htIcc).1
    constructor
    · simpa [β, modelRescale] using
        phaseTarget_smul (I := I) x (z := α (τ * s)) (a := τ)
          hαtarget
    · simpa [β, modelRescale] using
        phaseSrc_smul (I := I) x (z := α (τ * s)) (a := τ)
          hαtarget
  have hspray : IsMIntegralCurveOn lift
      (leviCivitaGeodesicSprayChart (I := I) g x)
      (Metric.ball (0 : Real) 2) := by
    simpa [lift, β] using
      modelSol_integralOn (I := I) g x hβderiv hβsrc
  have hspray0 : IsMIntegralCurveAt lift
      (leviCivitaGeodesicSprayChart (I := I) g x) 0 :=
    hspray.isMIntegralCurveAt
      (Metric.ball_mem_nhds (0 : Real) (by norm_num : (0 : Real) < 2))
  have hsrcBall : ∀ s ∈ Metric.ball (0 : Real) 2,
      projectCurve (I := I) lift s ∈
        (extChartAtCoordinateData (I := I) x).domain := by
    intro s hs
    simpa [projectCurve, lift, extChartAtCoordinateData, coordinateFrameSet,
      coordinateTrivializationAt, extChartAt_source] using (hβsrc s hs).2
  refine ⟨gamma 1, expAt_of_segment (I := I) (g := g)
    (x := x) (v := v) (gamma := gamma) (s := Set.uIcc 0 1)
    (by intro t ht; exact ht) ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [gamma] using
      projectCurve_zero_of_lift (I := I)
        (u := (⟨x, v⟩ : TangentBundle I M)) hlift0
  · simpa [gamma] using
      projectCurve_initialVelocity_of_geodesicSprayIntegral
        (I := I) (g := g) (u := (⟨x, v⟩ : TangentBundle I M))
        (f := lift) hlift0 hspray0
  · constructor
    · intro t ht
      exact hsrcBall t (uIcc01_mem_ball_two ht)
    · intro t ht
      have htball : t ∈ Metric.ball (0 : Real) 2 :=
        uIcc01_mem_ball_two ht
      have hode :=
        coordSprayODEOn (I := I) (g := g) (x := x) (v := v)
          (lift := lift) (epsilon := (2 : Real)) (t := t)
          hlift0 hspray htball hsrcBall
      exact hode.zeroAccel

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
  refine ⟨({0} : Set Real), ?_, gamma, ?_, ?_⟩
  · intro t ht
    simpa using ht
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
  refine ⟨gamma tau, Metric.ball (0 : Real) epsilon, ?_,
    gamma, ?_, rfl⟩
  · intro s hs
    rw [Metric.mem_ball]
    have hdist : dist (0 : Real) s ≤ dist (0 : Real) tau :=
      Real.dist_left_le_of_mem_uIcc hs
    have htau' : dist (0 : Real) tau < epsilon := by
      simpa [Metric.mem_ball, dist_comm] using htau
    have hdist' : dist s (0 : Real) ≤ dist (0 : Real) tau := by
      simpa [dist_comm] using hdist
    exact hdist'.trans_lt htau'
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
