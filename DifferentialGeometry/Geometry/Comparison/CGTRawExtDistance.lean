import DifferentialGeometry.Geometry.Comparison.CGTRawExtension
import DifferentialGeometry.Geometry.Comparison.CGTRawLiftOps
import DifferentialGeometry.Geometry.Geodesic.OpenSubtype

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential Geodesic NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (rawPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (rawPullBall (E := E) R).isOpen)

noncomputable local instance {R : Real} :
    SigmaCompactSpace (rawAgree (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (rawAgree (E := E) R).isOpen)

section Geodesic

private theorem rawGeo_iff
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (γ : Real → rawPullBall (E := E) R) (s : Set Real)
    (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hstay : ∀ t ∈ s,
      ‖((γ t : rawPullBall (E := E) R) : E)‖ < 3 * R / 4) :
    IsGeodesicOn (I := 𝓘(Real, E))
        (rawExtMetric (I := I) g p hR hloc)
        (fun t => ((γ t : rawPullBall (E := E) R) : E)) s ↔
      IsGeodesicOn (I := 𝓘(Real, E))
        (rawPullMetric (I := I) g p hloc) γ s := by
  classical
  let U := rawPullBall (E := E) R
  let V := rawAgree (E := E) R
  let gExt := rawExtMetric (I := I) g p hR hloc
  let gPull := rawPullMetric (I := I) g p hloc
  let z₀ : V :=
    ⟨⟨0, Metric.mem_ball_self hR⟩, by
      change (0 : E) ∈ Metric.ball (0 : E) (3 * R / 4)
      exact Metric.mem_ball_self (by linarith)⟩
  let γV : Real → V := fun t =>
    if ht : γ t ∈ V then ⟨γ t, ht⟩ else z₀
  have hmem : ∀ t ∈ s, γ t ∈ V := by
    intro t ht
    change ((γ t : rawPullBall (E := E) R) : E) ∈
      Metric.ball (0 : E) (3 * R / 4)
    simpa only [Metric.mem_ball, dist_zero_right] using hstay t ht
  have heq : ∀ t ∈ s,
      (fun r => ((γV r : V) : U)) =ᶠ[𝓝 t] γ := by
    intro t ht
    have hpre : γ ⁻¹' (V : Set U) ∈ 𝓝 t :=
      hγ.continuous.continuousAt
        (V.isOpen.mem_nhds (hmem t ht))
    filter_upwards [hpre] with r hr
    change γ r ∈ V at hr
    simp only [γV, dif_pos hr]
  constructor
  · intro hgeo
    have hgeoU :
        IsGeodesicOn (I := 𝓘(Real, E))
          (gExt.restrictOpen (I := 𝓘(Real, E)) U) γ s :=
      (Geodesic.geodesicOn_open_iff
        (I := 𝓘(Real, E)) gExt U γ s).2 hgeo
    have hgeoUV :
        IsGeodesicOn (I := 𝓘(Real, E))
          (gExt.restrictOpen (I := 𝓘(Real, E)) U)
          (fun t => ((γV t : V) : U)) s := by
      intro t ht
      exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
        (heq t ht).eq_of_nhds (heq t ht) (hgeoU t ht)
    have hgeoV :
        IsGeodesicOn (I := 𝓘(Real, E))
          ((gExt.restrictOpen (I := 𝓘(Real, E)) U).restrictOpen
            (I := 𝓘(Real, E)) V) γV s :=
      (Geodesic.geodesicOn_open_iff
        (I := 𝓘(Real, E))
        (gExt.restrictOpen (I := 𝓘(Real, E)) U) V γV s).2 hgeoUV
    have hgeoV' := hgeoV
    rw [show
      ((gExt.restrictOpen (I := 𝓘(Real, E)) U).restrictOpen
          (I := 𝓘(Real, E)) V) =
        gPull.restrictOpen (I := 𝓘(Real, E)) V by
          simpa only [U, V, gExt, gPull] using
            rawExt_restrict (I := I) g p hR hloc] at hgeoV'
    have hgeoPullV :
        IsGeodesicOn (I := 𝓘(Real, E)) gPull
          (fun t => ((γV t : V) : U)) s :=
      (Geodesic.geodesicOn_open_iff
        (I := 𝓘(Real, E)) gPull V γV s).1 hgeoV'
    intro t ht
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (heq t ht).eq_of_nhds.symm (heq t ht).symm (hgeoPullV t ht)
  · intro hgeo
    have hgeoPullV :
        IsGeodesicOn (I := 𝓘(Real, E)) gPull
          (fun t => ((γV t : V) : U)) s := by
      intro t ht
      exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
        (heq t ht).eq_of_nhds (heq t ht) (hgeo t ht)
    have hgeoV :
        IsGeodesicOn (I := 𝓘(Real, E))
          (gPull.restrictOpen (I := 𝓘(Real, E)) V) γV s :=
      (Geodesic.geodesicOn_open_iff
        (I := 𝓘(Real, E)) gPull V γV s).2 hgeoPullV
    have hgeoV' := hgeoV
    rw [show
      gPull.restrictOpen (I := 𝓘(Real, E)) V =
        (gExt.restrictOpen (I := 𝓘(Real, E)) U).restrictOpen
          (I := 𝓘(Real, E)) V by
        simpa only [U, V, gExt, gPull] using
          (rawExt_restrict (I := I) g p hR hloc).symm] at hgeoV'
    have hgeoExtU :
        IsGeodesicOn (I := 𝓘(Real, E))
          (gExt.restrictOpen (I := 𝓘(Real, E)) U)
          (fun t => ((γV t : V) : U)) s :=
      (Geodesic.geodesicOn_open_iff
        (I := 𝓘(Real, E))
        (gExt.restrictOpen (I := 𝓘(Real, E)) U) V γV s).1 hgeoV'
    have hgeoExt :
        IsGeodesicOn (I := 𝓘(Real, E)) gExt
          (fun t => (((γV t : V) : U) : E)) s :=
      (Geodesic.geodesicOn_open_iff
        (I := 𝓘(Real, E)) gExt U
        (fun t => ((γV t : V) : U)) s).1 hgeoExtU
    intro t ht
    have heqE :
        (fun r => (((γV r : V) : U) : E)) =ᶠ[𝓝 t]
          (fun r => ((γ r : U) : E)) :=
      (heq t ht).fun_comp (fun z : U => (z : E))
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      heqE.eq_of_nhds.symm heqE.symm (hgeoExt t ht)

/-- A geodesic for the complete extension that stays in the agreement ball is
a geodesic for the raw pullback metric. -/
theorem rawPull_geo_of_ext
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (γ : Real → rawPullBall (E := E) R) (s : Set Real)
    (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hstay : ∀ t ∈ s,
      ‖((γ t : rawPullBall (E := E) R) : E)‖ < 3 * R / 4)
    (hgeo : IsGeodesicOn (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc)
      (fun t => ((γ t : rawPullBall (E := E) R) : E)) s) :
    IsGeodesicOn (I := 𝓘(Real, E))
      (rawPullMetric (I := I) g p hloc) γ s :=
  (rawGeo_iff (I := I) g p hR hloc γ s hγ hstay).mp hgeo

/-- A raw-pullback geodesic that stays in the agreement ball is a geodesic for
the complete extension after inclusion into the model space. -/
theorem rawExt_geo_of_pull
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (γ : Real → rawPullBall (E := E) R) (s : Set Real)
    (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hstay : ∀ t ∈ s,
      ‖((γ t : rawPullBall (E := E) R) : E)‖ < 3 * R / 4)
    (hgeo : IsGeodesicOn (I := 𝓘(Real, E))
      (rawPullMetric (I := I) g p hloc) γ s) :
    IsGeodesicOn (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc)
      (fun t => ((γ t : rawPullBall (E := E) R) : E)) s :=
  (rawGeo_iff (I := I) g p hR hloc γ s hγ hstay).mpr hgeo

end Geodesic

section Length

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- A path contained in the closed agreement ball has the same length for the
complete extension as its raw framed-exponential image. -/
theorem rawExt_pathLen
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {γ : Real → E} {a b : Real}
    (hγ : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc a b))
    (hstay : ∀ t ∈ Set.Icc a b,
      γ t ∈ Metric.closedBall (0 : E) (3 * R / 4)) :
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E => TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E) γ a b =
      Manifold.pathELength I
        ((framedExpMap (I := I) g p) ∘ γ) a b := by
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  change Manifold.pathELength 𝓘(Real, E) γ a b =
    Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ γ) a b
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have htIcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hball : γ t ∈ Metric.ball (0 : E) R :=
    Metric.closedBall_subset_ball (by linarith) (hstay t htIcc)
  have hγt : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t htIcc).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  have hFt : MDifferentiableAt 𝓘(Real, E) I
      (framedExpMap (I := I) g p) (γ t) :=
    (hloc ⟨γ t, hball⟩).mdifferentiableAt (by decide)
  have hcomp :
      mfderiv 𝓘(Real, Real) I
          ((framedExpMap (I := I) g p) ∘ γ) t =
        (mfderiv 𝓘(Real, E) I
          (framedExpMap (I := I) g p) (γ t)).comp
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t) :=
    mfderiv_comp t hFt hγt
  change
    ‖mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1‖ₑ =
      ‖mfderiv 𝓘(Real, Real) I
        ((framedExpMap (I := I) g p) ∘ γ) t 1‖ₑ
  rw [hcomp]
  change
    ‖mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1‖ₑ =
      ‖mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) (γ t)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1)‖ₑ
  let v : TangentSpace 𝓘(Real, E) (γ t) :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1
  let zU : rawPullBall (E := E) R := ⟨γ t, hball⟩
  have hExtNorm :
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner (γ t) v v)) := by
    simpa only using
      (tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt (γ t) v)
  have hBaseNorm :
      ‖mfderiv 𝓘(Real, E) I
          (framedExpMap (I := I) g p) (γ t) v‖ₑ =
        ENNReal.ofReal (Real.sqrt
          (g.inner (framedExpMap (I := I) g p (γ t))
            (mfderiv 𝓘(Real, E) I
              (framedExpMap (I := I) g p) (γ t) v)
            (mfderiv 𝓘(Real, E) I
              (framedExpMap (I := I) g p) (γ t) v))) :=
    hEnorm _ _
  change ‖v‖ₑ = ‖mfderiv 𝓘(Real, E) I
    (framedExpMap (I := I) g p) (γ t) v‖ₑ
  rw [hExtNorm, hBaseNorm]
  congr 2
  calc
    gExt.inner (γ t) v v =
        (rawPullMetric (I := I) g p hloc).inner zU v v := by
      simpa only [gExt, zU] using
        rawExt_inner (I := I) g p hR hloc (hstay t htIcc) v v
    _ = g.inner (framedExpMap (I := I) g p (γ t))
        (mfderiv 𝓘(Real, E) I
          (framedExpMap (I := I) g p) (γ t) v)
        (mfderiv 𝓘(Real, E) I
          (framedExpMap (I := I) g p) (γ t) v) := by
      simpa only [zU] using
        rawPullMetric_inner (I := I) g p hloc zU v v

section Radial

variable [I.Boundaryless] [T2Space (TangentBundle I M)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- A centered radial path in the complete extension has length equal to the
norm of its endpoint, assuming only that radial segment lies in the raw
exponential domain. -/
theorem rawExt_radial_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ ≤ 3 * R / 4)
    (hdom : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p) :
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun y : E => TangentSpace 𝓘(Real, E) y) :=
      ⟨gExt.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E)
        (fun t : Real => Real.smoothTransition t • z) 0 1 =
      ENNReal.ofReal ‖z‖ := by
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun y : E => TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.toRiemannianMetric⟩
  let γ : Real → E := fun t => Real.smoothTransition t • z
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    intro t
    rw [contMDiffAt_iff_contDiffAt]
    exact Real.smoothTransition.contDiff.contDiffAt.smul contDiffAt_const
  have hγone : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ
      (Set.Icc (0 : Real) 1) :=
    (hγinf.of_le (by norm_num)).contMDiffOn
  have hstay : ∀ t ∈ Set.Icc (0 : Real) 1,
      γ t ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    intro t _
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖Real.smoothTransition t • z‖ ≤ 3 * R / 4
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact
      (mul_le_of_le_one_left (norm_nonneg z)
        (Real.smoothTransition.le_one t)).trans hz
  have hext :
      Manifold.pathELength 𝓘(Real, E) γ 0 1 =
        Manifold.pathELength I
          ((framedExpMap (I := I) g p) ∘ γ) 0 1 := by
    simpa only [gExt] using
      rawExt_pathLen (I := I) g hEnorm p hR hloc hγone hstay
  let ρ : Real → Real := Real.smoothTransition
  let β : Real → M :=
    (framedExpMap (I := I) g p) ∘ fun t : Real => t • z
  have hβC1 : ContMDiffOn 𝓘(Real, Real) I 1 β (Set.Icc 0 1) := by
    intro t ht
    have hline : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞
        (fun s : Real => s • z) t :=
      (contMDiff_id.smul contMDiff_const).contMDiffAt
    exact (((framedExp_mdiffAt (I := I) g p
      (by simpa only [map_smul] using hdom t ht)).comp t hline).of_le
        (by decide : (1 : WithTop ℕ∞) ≤
          (↑(⊤ : ℕ∞) : WithTop ℕ∞))).contMDiffWithinAt
  have hbase : Manifold.pathELength I β 0 1 = ENNReal.ofReal ‖z‖ := by
    simpa only [β] using rawRadial_len (I := I) g hEnorm p z hdom
  calc
    Manifold.pathELength 𝓘(Real, E) γ 0 1 =
        Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ γ) 0 1 := hext
    _ = Manifold.pathELength I (β ∘ ρ) 0 1 := by rfl
    _ = Manifold.pathELength I β 0 1 := by
      rw [Manifold.pathELength_comp_of_monotoneOn
        (I := I) (γ := β) (f := ρ) (a := 0) (b := 1)
        zero_le_one (Real.smoothTransition.monotone.monotoneOn (Set.Icc 0 1))
        ((Real.smoothTransition.contDiff (n := 1)).differentiable
          one_ne_zero).differentiableOn
        (by
          simpa only [ρ, Real.smoothTransition.zero_of_nonpos le_rfl,
            Real.smoothTransition.one_of_one_le le_rfl] using
              hβC1.mdifferentiableOn one_ne_zero)]
      simp only [ρ, Real.smoothTransition.zero_of_nonpos le_rfl,
        Real.smoothTransition.one_of_one_le le_rfl]
    _ = ENNReal.ofReal ‖z‖ := hbase

/-- Two points in the centered core are at extension distance at most twice
their common norm bound, using only their two radial domain segments. -/
theorem rawExt_edist_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (ha : a ≤ 3 * R / 4)
    (hdomx : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p x) ∈ expDomain (I := I) g p)
    (hdomy : ∀ s ∈ Set.Icc (0 : Real) 1,
      (show TangentSpace I p from
        s • normalFrame (I := I) g p y) ∈ expDomain (I := I) g p) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (rawExtMetric (I := I) g p hR hloc) x y ≤
      ENNReal.ofReal (2 * a) := by
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  change Manifold.riemannianEDist 𝓘(Real, E) x y ≤ ENNReal.ofReal (2 * a)
  have hdist_zero :
      ∀ (z : E), ‖z‖ ≤ 3 * R / 4 →
        (∀ s ∈ Set.Icc (0 : Real) 1,
          (show TangentSpace I p from
            s • normalFrame (I := I) g p z) ∈ expDomain (I := I) g p) →
        Manifold.riemannianEDist 𝓘(Real, E) 0 z ≤ ENNReal.ofReal ‖z‖ := by
    intro z hz hdomz
    let γz : Real → E := fun t => Real.smoothTransition t • z
    have hγzinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γz := by
      intro t
      rw [contMDiffAt_iff_contDiffAt]
      exact Real.smoothTransition.contDiff.contDiffAt.smul contDiffAt_const
    have hγz : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γz
        (Set.Icc (0 : Real) 1) :=
      (hγzinf.of_le (by norm_num)).contMDiffOn
    have hdist :=
      Manifold.riemannianEDist_le_pathELength
        (I := 𝓘(Real, E)) (x := (0 : E)) (y := z)
        hγz (by
          simp only [γz, Real.smoothTransition.zero_of_nonpos le_rfl,
            zero_smul])
        (by
          simp only [γz, Real.smoothTransition.one_of_one_le le_rfl,
            one_smul])
        zero_le_one
    rw [rawExt_radial_len (I := I) g hEnorm p hR hloc hz hdomz] at hdist
    exact hdist
  have hx_inner : ‖x‖ ≤ 3 * R / 4 := hx.trans ha
  have hy_inner : ‖y‖ ≤ 3 * R / 4 := hy.trans ha
  calc
    Manifold.riemannianEDist 𝓘(Real, E) x y ≤
        Manifold.riemannianEDist 𝓘(Real, E) x 0 +
          Manifold.riemannianEDist 𝓘(Real, E) 0 y :=
      Manifold.riemannianEDist_triangle
    _ = Manifold.riemannianEDist 𝓘(Real, E) 0 x +
          Manifold.riemannianEDist 𝓘(Real, E) 0 y := by
      rw [Manifold.riemannianEDist_comm]
    _ ≤ ENNReal.ofReal ‖x‖ + ENNReal.ofReal ‖y‖ :=
      add_le_add (hdist_zero x hx_inner hdomx)
        (hdist_zero y hy_inner hdomy)
    _ = ENNReal.ofReal (‖x‖ + ‖y‖) :=
      (ENNReal.ofReal_add (norm_nonneg x) (norm_nonneg y)).symm
    _ ≤ ENNReal.ofReal (2 * a) := by
      exact ENNReal.ofReal_le_ofReal (by linarith)

end Radial
end Length

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
