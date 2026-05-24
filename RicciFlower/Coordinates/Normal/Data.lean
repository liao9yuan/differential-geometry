import RicciFlower.Coordinates.Normal.Existence

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate normal coordinates

This file contains the reusable coordinate-defined normal-coordinate front end.
It deliberately starts with relation-valued endpoint data instead of defining
an exponential map as a function.  A functional exponential map requires the
next analytic layer: uniqueness and smooth dependence of the local geodesic
flow on initial velocity.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle
open scoped Manifold ContDiff Topology
open RicciFlower.GlobalGeometry.Lecture07

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [SigmaCompactSpace M] [T2Space M]

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

/-- Topological normal-coordinate data obtained from the strict inverse
function theorem.

This stores the actual local homeomorphism for
`v ↦ extChartAt I x (exp v)`.  It intentionally does not claim that the
corresponding chart is smooth or belongs to the maximal atlas. -/
structure NormalTopChartData
    (g : SmoothRiemannianMetric I M) (x : M) where
  domain : Set (TangentSpace I x)
  domain_open : IsOpen domain
  zero_mem_domain : (0 : TangentSpace I x) ∈ domain
  exp : TangentSpace I x -> M
  exp_zero : exp 0 = x
  chartExp : OpenPartialHomeomorph (TangentSpace I x) (TangentSpace I x)
  domain_subset_source : domain ⊆ chartExp.source
  exp_realizes :
    ∀ v : TangentSpace I x, v ∈ domain -> expAt (I := I) g x v (exp v)
  exp_mem_source :
    ∀ v : TangentSpace I x, v ∈ domain -> exp v ∈ (extChartAt I x).source
  chartExp_eq :
    ∀ v : TangentSpace I x, v ∈ domain -> chartExp v = extChartAt I x (exp v)

namespace NormalTopChartData

/-- Forget the stored topological local homeomorphism to the older endpoint
package by shrinking the open tangent-domain to a metric ball. -/
def toNormalCoordinateData
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : NormalTopChartData (I := I) g x) :
    NormalCoordinateData (I := I) g x := by
  have hnhds : N.domain ∈ 𝓝 (0 : TangentSpace I x) :=
    N.domain_open.mem_nhds N.zero_mem_domain
  rw [Metric.mem_nhds_iff] at hnhds
  let r : Real := Classical.choose hnhds
  have hr : 0 < r := (Classical.choose_spec hnhds).1
  have hrsub :
      Metric.ball (0 : TangentSpace I x) r ⊆ N.domain :=
    (Classical.choose_spec hnhds).2
  let B : Set (TangentSpace I x) := Metric.ball (0 : TangentSpace I x) r
  have hBsub_source : B ⊆ N.chartExp.source := fun v hv =>
    N.domain_subset_source (hrsub hv)
  have hsrc_exp : ∀ v ∈ B, N.exp v ∈ (extChartAt I x).source := by
    intro v hv
    exact N.exp_mem_source v (hrsub hv)
  have hchartOpen : IsOpen (N.chartExp '' B) :=
    N.chartExp.isOpen_image_of_subset_source Metric.isOpen_ball hBsub_source
  have htargetOpen : IsOpen (N.exp '' B) := by
    have hpreOpen :
        IsOpen ((extChartAt I x).source ∩
          (extChartAt I x) ⁻¹' (N.chartExp '' B)) := by
      rw [extChartAt]
      exact (chartAt H x).isOpen_extend_preimage' (I := I) hchartOpen
    have himage :
        N.exp '' B =
          (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' (N.chartExp '' B) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨hsrc_exp v hv, v, hv, N.chartExp_eq v (hrsub hv)⟩
      · rintro ⟨hy_src, v, hv, h_eq⟩
        refine ⟨v, hv, ?_⟩
        apply (extChartAt I x).injOn (hsrc_exp v hv) hy_src
        simpa [N.chartExp_eq v (hrsub hv)] using h_eq
    simpa [B, himage] using hpreOpen
  refine {
    radius := r
    radius_pos := hr
    exp := N.exp
    exp_zero := N.exp_zero
    exp_realizes := ?_
    source_inj := ?_
    target_open := ?_
  }
  · intro v hv
    exact (expAt_iff (I := I) g x v (N.exp v)).1 (N.exp_realizes v (hrsub hv))
  · intro v hv w hw h_eq
    have hvN : v ∈ N.domain := hrsub hv
    have hwN : w ∈ N.domain := hrsub hw
    apply N.chartExp.injOn (N.domain_subset_source hvN) (N.domain_subset_source hwN)
    rw [N.chartExp_eq v hvN, N.chartExp_eq w hwN]
    exact congrArg (fun y : M => extChartAt I x y) h_eq
  · simpa [B] using htargetOpen

end NormalTopChartData

/-- Smooth local-diffeomorphism data for the exponential endpoint map.

This is the geometric/ODE frontier behind smooth normal coordinates: the
selected endpoint map must be a genuine smooth local diffeomorphism near
`0 : T_xM`, and it must realize the relation-valued endpoint API on its source.
The normal chart is the local inverse of `expLD`, not the construction chart
`extChartAt I x`. -/
structure NormalExpLocalDiffeomorphData
    (g : SmoothRiemannianMetric I M) (x : M) where
  expLD :
    PartialDiffeomorph
      (modelWithCornersSelf Real (TangentSpace I x)) I
      (TangentSpace I x) M (∞ : WithTop ℕ∞)
  zero_mem_source : (0 : TangentSpace I x) ∈ expLD.source
  map_zero : expLD 0 = x
  expAt_realizes :
    ∀ v : TangentSpace I x, v ∈ expLD.source -> expAt (I := I) g x v (expLD v)

namespace NormalExpLocalDiffeomorphData

/-- The smooth normal partial diffeomorphism `normalCoord ∘ Exp_x^{-1}`.

This is the smooth object underlying the normal chart.  Its inverse is the
exponential local diffeomorphism followed by `normalHCoord⁻¹`. -/
def normalPartialDiffeomorph [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    PartialDiffeomorph I I M H (∞ : WithTop ℕ∞) :=
  PartialDiffeomorph.transDiffeomorph (I := I) D.expLD.symm
    (normalHCoordDiffeomorph (I := I) x)

/-- The normal coordinate chart induced by a smooth local exponential
diffeomorphism.  Its inverse is `D.expLD`; its forward map sends a nearby point
to the normal coordinate of the unique tangent vector that exponentiates to it.
-/
def normalChart [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    OpenPartialHomeomorph M H :=
  (D.normalPartialDiffeomorph (I := I)).toOpenPartialHomeomorph

@[simp]
theorem normalPartialDiffeomorph_toOpenPartialHomeomorph [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    (D.normalPartialDiffeomorph (I := I)).toOpenPartialHomeomorph =
      D.expLD.symm.toOpenPartialHomeomorph.transHomeomorph
        (normalHCoordHomeomorph (I := I) x) := by
  simp [normalPartialDiffeomorph]

@[simp]
theorem normalChart_eq [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    D.normalChart (I := I) =
      D.expLD.symm.toOpenPartialHomeomorph.transHomeomorph
        (normalHCoordHomeomorph (I := I) x) := by
  simp [normalChart]

/-- Forget smooth local-diffeomorphism exponential data to the older
relation-valued endpoint package by shrinking the source to a metric ball. -/
def toNormalCoordinateData
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    NormalCoordinateData (I := I) g x := by
  have hnhds : D.expLD.source ∈ 𝓝 (0 : TangentSpace I x) :=
    D.expLD.open_source.mem_nhds D.zero_mem_source
  rw [Metric.mem_nhds_iff] at hnhds
  let r : Real := Classical.choose hnhds
  have hr : 0 < r := (Classical.choose_spec hnhds).1
  have hrsub :
      Metric.ball (0 : TangentSpace I x) r ⊆ D.expLD.source :=
    (Classical.choose_spec hnhds).2
  let expHomeomorph := D.expLD.toOpenPartialHomeomorph
  refine {
    radius := r
    radius_pos := hr
    exp := D.expLD
    exp_zero := D.map_zero
    exp_realizes := ?_
    source_inj := ?_
    target_open := ?_
  }
  · intro v hv
    exact (expAt_iff (I := I) g x v (D.expLD v)).1 (D.expAt_realizes v (hrsub hv))
  · intro v hv w hw h_eq
    exact expHomeomorph.injOn (hrsub hv) (hrsub hw) h_eq
  · exact expHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hrsub

end NormalExpLocalDiffeomorphData

/-- The strict inverse-function theorem applied to the endpoint map, retaining
the resulting topological local homeomorphism in tangent coordinates. -/
theorem expAt_topChart
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalTopChartData (I := I) g x) := by
  classical
  obtain ⟨r0, hr0, exp, hexp0, hreal, hstrict⟩ :=
    expAt_strict (I := I) g x
  let chartExp : TangentSpace I x -> TangentSpace I x :=
    fun v => extChartAt I x (exp v)
  let eIso : TangentSpace I x ≃L[Real] TangentSpace I x :=
    ContinuousLinearEquiv.refl Real (TangentSpace I x)
  have hstrictIso :
      HasStrictFDerivAt chartExp (eIso : TangentSpace I x →L[Real] TangentSpace I x)
        (0 : TangentSpace I x) := by
    simpa [chartExp, eIso] using hstrict
  let eIFT := hstrictIso.toOpenPartialHomeomorph chartExp
  have hIFTsrc : (0 : TangentSpace I x) ∈ eIFT.source := by
    simpa [eIFT] using hstrictIso.mem_toOpenPartialHomeomorph_source
  refine ⟨{
    domain := Metric.ball (0 : TangentSpace I x) r0 ∩ eIFT.source
    domain_open := Metric.isOpen_ball.inter eIFT.open_source
    zero_mem_domain := ?_
    exp := exp
    exp_zero := hexp0
    chartExp := eIFT
    domain_subset_source := ?_
    exp_realizes := ?_
    exp_mem_source := ?_
    chartExp_eq := ?_
  }⟩
  · exact ⟨Metric.mem_ball_self hr0, hIFTsrc⟩
  · intro v hv
    exact hv.2
  · intro v hv
    exact hreal v hv.1
  · intro v hv
    have hcoord : exp v ∈ coordinateFrameSet (I := I) x :=
      expAt_mem_source (I := I) (hreal v hv.1)
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hcoord
  · intro v hv
    simp [eIFT, chartExp]

/-- The topological local inverse-function skeleton supplied by
`expAt_strict`.

This deliberately stops at the older endpoint package: strict differentiability
at the center gives local injectivity and open image, but not smooth maximal
atlas membership for the normal chart. -/
theorem expAt_topData
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalCoordinateData (I := I) g x) := by
  obtain ⟨N⟩ := expAt_topChart (I := I) g x
  exact ⟨N.toNormalCoordinateData (I := I)⟩

/-- Smooth normal-coordinate chart data before registering the tangent-bundle
trivialization.

This is the correct smooth local-diffeomorphism layer: it records a genuine
normal chart in the maximal atlas and the endpoint/inverse formulas, but does
not yet claim that the chart has been converted to a `LocalChartAt`. -/
structure NormalChartCoreData
    (g : SmoothRiemannianMetric I M) (x : M) where
  domain : Set (TangentSpace I x)
  domain_open : IsOpen domain
  zero_mem_domain : (0 : TangentSpace I x) ∈ domain
  exp : TangentSpace I x -> M
  exp_zero : exp 0 = x
  chart : OpenPartialHomeomorph M H
  mem_source : x ∈ chart.source
  mem_max : chart ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M
  exp_realizes :
    ∀ v : TangentSpace I x, v ∈ domain -> expAt (I := I) g x v (exp v)
  source_eq : exp '' domain = chart.source
  exp_open_image :
    ∀ s : Set (TangentSpace I x), IsOpen s -> s ⊆ domain -> IsOpen (exp '' s)
  ext_exp_eq :
    ∀ v : TangentSpace I x, v ∈ domain -> chart.extend I (exp v) = normalCoord (I := I) x v
  symm_normalCoord_eq :
    ∀ v : TangentSpace I x, v ∈ domain -> chart.symm (normalHCoord (I := I) x v) = exp v

namespace NormalChartCoreData

/-- Forget smooth normal-chart core data to the older relation-valued endpoint
package by shrinking the open tangent-domain to a metric ball. -/
def toNormalCoordinateData
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : NormalChartCoreData (I := I) g x) :
    NormalCoordinateData (I := I) g x := by
  have hnhds : N.domain ∈ 𝓝 (0 : TangentSpace I x) :=
    N.domain_open.mem_nhds N.zero_mem_domain
  rw [Metric.mem_nhds_iff] at hnhds
  let r : Real := Classical.choose hnhds
  have hr : 0 < r := (Classical.choose_spec hnhds).1
  have hrsub :
      Metric.ball (0 : TangentSpace I x) r ⊆ N.domain :=
    (Classical.choose_spec hnhds).2
  refine {
    radius := r
    radius_pos := hr
    exp := N.exp
    exp_zero := N.exp_zero
    exp_realizes := ?_
    source_inj := ?_
    target_open := ?_
  }
  · intro v hv
    exact (expAt_iff (I := I) g x v (N.exp v)).1 (N.exp_realizes v (hrsub hv))
  · intro v hv w hw h_eq
    apply normalCoord_injective (I := I) x
    calc
      normalCoord (I := I) x v = N.chart.extend I (N.exp v) := (N.ext_exp_eq v (hrsub hv)).symm
      _ = N.chart.extend I (N.exp w) := congrArg (fun y : M => N.chart.extend I y) h_eq
      _ = normalCoord (I := I) x w := N.ext_exp_eq w (hrsub hw)
  · exact N.exp_open_image (Metric.ball (0 : TangentSpace I x) r)
      Metric.isOpen_ball hrsub

end NormalChartCoreData

namespace NormalExpLocalDiffeomorphData

/-- A smooth local exponential diffeomorphism gives the smooth chart-core
package: the normal chart is the inverse exponential map followed by the
linear normal-coordinate homeomorphism. -/
def toNormalChartCoreData [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (D : NormalExpLocalDiffeomorphData (I := I) g x) :
    NormalChartCoreData (I := I) g x := by
  classical
  let e : OpenPartialHomeomorph (TangentSpace I x) M :=
    D.expLD.toOpenPartialHomeomorph
  refine {
    domain := D.expLD.source
    domain_open := D.expLD.open_source
    zero_mem_domain := D.zero_mem_source
    exp := D.expLD
    exp_zero := D.map_zero
    chart := D.normalChart (I := I)
    mem_source := ?_
    mem_max := ?_
    exp_realizes := ?_
    source_eq := ?_
    exp_open_image := ?_
    ext_exp_eq := ?_
    symm_normalCoord_eq := ?_
  }
  · have hx_target : x ∈ D.expLD.target := by
      have h0 : D.expLD 0 ∈ D.expLD.target := by
        simpa [e] using
          (e.map_source (x := (0 : TangentSpace I x)) D.zero_mem_source)
      simpa [D.map_zero] using h0
    simpa [normalChart, e] using hx_target
  · exact PartialDiffeomorph.toOpenPartialHomeomorph_mem_maximalAtlas
      (I := I) (D.normalPartialDiffeomorph (I := I))
  · intro v hv
    exact (expAt_iff (I := I) g x v (D.expLD v)).1 (D.expAt_realizes v hv)
  · simpa [normalChart, e] using e.image_source_eq_target
  · intro s hs hsub
    exact e.isOpen_image_of_subset_source hs hsub
  · intro v hv
    have hv_target : D.expLD v ∈ D.expLD.target := by
      exact e.map_source hv
    have hsymm : D.expLD.symm (D.expLD v) = v := by
      simpa [e] using e.left_inv hv
    have hchart :
        D.normalChart (I := I) (D.expLD v) = normalHCoord (I := I) x v := by
      change normalHCoord (I := I) x (D.expLD.symm (D.expLD v)) =
        normalHCoord (I := I) x v
      rw [hsymm]
    calc
      (D.normalChart (I := I)).extend I (D.expLD v)
          = I (D.normalChart (I := I) (D.expLD v)) := rfl
      _ = I (normalHCoord (I := I) x v) := congrArg I hchart
      _ = normalCoord (I := I) x v := model_normalHCoord (I := I) x v
  · intro v hv
    have hv_target : D.expLD v ∈ D.expLD.target := by
      exact e.map_source hv
    have hnormal_target :
        normalHCoord (I := I) x v ∈ (D.normalChart (I := I)).target := by
      have hpre :
          (normalHCoordHomeomorph (I := I) x).symm
              (normalHCoord (I := I) x v) = v := by
        rw [← normalHCoordHomeomorph_apply (I := I) x v]
        exact (normalHCoordHomeomorph (I := I) x).left_inv v
      simpa [normalChart, e, hpre] using hv
    have hright :
        (D.normalChart (I := I)) ((D.normalChart (I := I)).symm
            (normalHCoord (I := I) x v)) =
          normalHCoord (I := I) x v := by
      exact (D.normalChart (I := I)).right_inv hnormal_target
    have hchart :
        D.normalChart (I := I) (D.expLD v) = normalHCoord (I := I) x v := by
      have hsymm : D.expLD.symm (D.expLD v) = v := by
        simpa [e] using e.left_inv hv
      change normalHCoord (I := I) x (D.expLD.symm (D.expLD v)) =
        normalHCoord (I := I) x v
      rw [hsymm]
    exact (D.normalChart (I := I)).injOn
      ((D.normalChart (I := I)).map_target hnormal_target)
      (by simpa [normalChart, e] using hv_target)
      (hright.trans hchart.symm)

end NormalExpLocalDiffeomorphData

/-- The real smooth exponential-map frontier.

This should be proved from smooth dependence of the chart-fixed geodesic flow
on the initial velocity, followed by the smooth inverse-function/local
diffeomorphism theorem. -/
theorem expAt_localDiffeomorph
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalExpLocalDiffeomorphData (I := I) g x) := by
  sorry

/-- Smooth normal-chart core data follows from the smooth local exponential
diffeomorphism frontier. -/
theorem expAt_smoothChartCore
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalChartCoreData (I := I) g x) := by
  obtain ⟨D⟩ := expAt_localDiffeomorph (I := I) g x
  exact ⟨D.toNormalChartCoreData (I := I)⟩

/-- Normal coordinates as an actual selected local chart.

The chart is part of the data, not reconstructed from the default `extChartAt`.
This is the package downstream normal-coordinate frames should consume.  The
older `NormalCoordinateData` is only the relation-valued compatibility view
obtained by forgetting this chart structure. -/
structure NormalChartData
    (g : SmoothRiemannianMetric I M) (x : M) where
  radius : Real
  radius_pos : 0 < radius
  exp : TangentSpace I x -> M
  exp_zero : exp 0 = x
  localChart : LocalChartAt (I := I) x
  exp_realizes :
    ∀ v : TangentSpace I x,
      v ∈ Metric.ball (0 : TangentSpace I x) radius ->
        expAt (I := I) g x v (exp v)
  source_eq :
    exp '' Metric.ball (0 : TangentSpace I x) radius = localChart.source
  ext_exp_eq :
    ∀ v : TangentSpace I x,
      v ∈ Metric.ball (0 : TangentSpace I x) radius ->
        localChart.ext (exp v) = normalCoord (I := I) x v
  symm_normalCoord_eq :
    ∀ v : TangentSpace I x,
      v ∈ Metric.ball (0 : TangentSpace I x) radius ->
        localChart.chart.symm (normalHCoord (I := I) x v) = exp v

namespace NormalChartData

/-- Forget a genuine normal local chart to the older relation-valued endpoint
package. -/
def toNormalCoordinateData [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : NormalChartData (I := I) g x) :
    NormalCoordinateData (I := I) g x where
  radius := N.radius
  radius_pos := N.radius_pos
  exp := N.exp
  exp_zero := N.exp_zero
  exp_realizes := by
    intro v hv
    exact (expAt_iff (I := I) g x v (N.exp v)).1 (N.exp_realizes v hv)
  source_inj := by
    intro v hv w hw h_eq
    apply normalCoord_injective (I := I) x
    calc
      normalCoord (I := I) x v = N.localChart.ext (N.exp v) := (N.ext_exp_eq v hv).symm
      _ = N.localChart.ext (N.exp w) := congrArg N.localChart.ext h_eq
      _ = normalCoord (I := I) x w := N.ext_exp_eq w hw
  target_open := by
    simpa [N.source_eq] using N.localChart.source_open

end NormalChartData

/-- Compatibility existence for the older relation-valued package. -/
theorem exists_normalData
    [I.Boundaryless] [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (NormalCoordinateData (I := I) g x) := by
  obtain ⟨D⟩ := expAt_localDiffeomorph (I := I) g x
  exact ⟨D.toNormalCoordinateData (I := I)⟩


end Coordinates
end RicciFlower
