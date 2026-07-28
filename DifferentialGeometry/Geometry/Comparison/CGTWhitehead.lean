import DifferentialGeometry.Analysis.ODE.TubeStability
import DifferentialGeometry.Geometry.Comparison.CGTConvexity
import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth
import DifferentialGeometry.Geometry.Geodesic.OpenSubtype
import DifferentialGeometry.Geometry.Metric.CompactPerturbationComplete

set_option autoImplicit false

/-!
# Complete extensions for the CGT Whitehead argument

The intrinsic exponential pullback metric lives on an open model ball and is
not complete.  This file extends it to a complete metric on the whole model
space while preserving it on a buffered inner ball.  The selected minimizing
geodesic for the complete extension will then be confined to that agreement
region by a first-hit argument.

Connectedness is not added to the ambient HCG input.  The model pullback ball
is connected on its own, and any later legacy ambient theorem is to be applied
only after restricting to the connected component containing the basepoint.
-/

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential Geodesic NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable local instance {R : Real} :
    SigmaCompactSpace (intrPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrPullBall (E := E) R).isOpen)

/-- The CGT cutoff is one through radius `3R/4` and supported through radius
`7R/8`.  Both radii lie strictly inside the pullback ball. -/
noncomputable def intrCut (R : Real) (hR : 0 < R) :
    ContDiffBump (0 : E) :=
  ⟨3 * R / 4, 7 * R / 8, by linarith, by linarith⟩

omit [NeZero (Module.finrank Real E)] in
/-- The CGT cutoff is smooth. -/
theorem intrCut_smooth (R : Real) (hR : 0 < R) :
    ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞
      (intrCut (E := E) R hR : E → Real) :=
  (intrCut (E := E) R hR).contDiff.contMDiff

omit [NeZero (Module.finrank Real E)] in
/-- The CGT cutoff takes values in the unit interval. -/
theorem intrCut_range (R : Real) (hR : 0 < R) (z : E) :
    intrCut (E := E) R hR z ∈ Set.Icc (0 : Real) 1 :=
  ⟨(intrCut (E := E) R hR).nonneg,
    (intrCut (E := E) R hR).le_one⟩

omit [NeZero (Module.finrank Real E)] in
/-- The topological support of the CGT cutoff lies in the pullback ball. -/
theorem intrCut_support (R : Real) (hR : 0 < R) :
    tsupport (intrCut (E := E) R hR : E → Real) ⊆
      (intrPullBall (E := E) R : Set E) := by
  rw [(intrCut (E := E) R hR).tsupport_eq]
  change Metric.closedBall (0 : E) (7 * R / 8) ⊆
    Metric.ball (0 : E) R
  exact Metric.closedBall_subset_ball (by linarith)

omit [NeZero (Module.finrank Real E)] in
/-- The CGT cutoff has compact support. -/
theorem intrCut_compact (R : Real) (hR : 0 < R) :
    IsCompact (tsupport (intrCut (E := E) R hR : E → Real)) := by
  letI : ProperSpace E := FiniteDimensional.proper Real E
  rw [(intrCut (E := E) R hR).tsupport_eq]
  exact isCompact_closedBall (0 : E) (7 * R / 8)

omit [NeZero (Module.finrank Real E)] in
/-- The CGT cutoff is one on the buffered agreement ball. -/
theorem intrCut_one (R : Real) (hR : 0 < R) {z : E}
    (hz : z ∈ Metric.ball (0 : E) (3 * R / 4)) :
    intrCut (E := E) R hR z = 1 :=
  (intrCut (E := E) R hR).one_of_mem_closedBall
    (Metric.ball_subset_closedBall hz)

omit [NeZero (Module.finrank Real E)] in
/-- The CGT cutoff is one on the closed buffered agreement ball. -/
theorem intrCut_one_closed (R : Real) (hR : 0 < R) {z : E}
    (hz : z ∈ Metric.closedBall (0 : E) (3 * R / 4)) :
    intrCut (E := E) R hR z = 1 :=
  (intrCut (E := E) R hR).one_of_mem_closedBall hz

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
/-- The buffered agreement ball lies in the pullback ball. -/
theorem intrInner_subset (R : Real) (hR : 0 < R) :
    Metric.ball (0 : E) (3 * R / 4) ⊆
      (intrPullBall (E := E) R : Set E) :=
  Metric.ball_subset_ball (by linarith)

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
/-- The closed buffered agreement ball lies in the pullback ball. -/
theorem intrClosed_subset (R : Real) (hR : 0 < R) :
    Metric.closedBall (0 : E) (3 * R / 4) ⊆
      (intrPullBall (E := E) R : Set E) :=
  Metric.closedBall_subset_ball (by linarith)

/-- The open agreement region inside the intrinsic pullback ball. -/
def intrAgree (R : Real) : Opens (intrPullBall (E := E) R) :=
  ⟨Subtype.val ⁻¹' Metric.ball (0 : E) (3 * R / 4),
    Metric.isOpen_ball.preimage continuous_subtype_val⟩

noncomputable local instance {R : Real} :
    SigmaCompactSpace (intrAgree (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrAgree (E := E) R).isOpen)

/-- The total CGT metric obtained by blending the pullback metric into the
canonical flat metric. -/
noncomputable def intrExtMetric
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    SmoothRiemannianMetric 𝓘(Real, E) E :=
  (flatModelMetric E).bumpExtendOpen
    (intrPullBall (E := E) R)
    (intrPullMetric (I := I) g hEnorm p hloc)
    (intrCut (E := E) R hR : E → Real)
    (intrCut_smooth (E := E) R hR)
    (intrCut_range (E := E) R hR)
    (intrCut_support (E := E) R hR)

/-- On the buffered inner ball, the complete extension is exactly the CGT
pullback metric. -/
theorem intrExt_inner
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : z ∈ Metric.closedBall (0 : E) (3 * R / 4))
    (v w : E) :
    (intrExtMetric (I := I) g hEnorm p hR hloc).inner z v w =
      (intrPullMetric (I := I) g hEnorm p hloc).inner
        ⟨z, intrClosed_subset (E := E) R hR hz⟩ v w := by
  simpa only [intrExtMetric] using
    bumpExtendOpen_eq_gU_on (I := 𝓘(Real, E))
      (flatModelMetric E) (intrPullBall (E := E) R)
      (intrPullMetric (I := I) g hEnorm p hloc)
      (intrCut (E := E) R hR : E → Real)
      (intrCut_smooth (E := E) R hR)
      (intrCut_range (E := E) R hR)
      (intrCut_support (E := E) R hR)
      (Metric.closedBall (0 : E) (3 * R / 4))
      (fun z hz => intrCut_one_closed (E := E) R hR hz)
      (intrClosed_subset (E := E) R hR) z hz v w

/-- On the open agreement region, the restricted complete extension is exactly
the restricted intrinsic pullback metric. -/
theorem intrExt_restrict
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    ((intrExtMetric (I := I) g hEnorm p hR hloc).restrictOpen
        (I := 𝓘(Real, E)) (intrPullBall (E := E) R)).restrictOpen
          (I := 𝓘(Real, E)) (intrAgree (E := E) R) =
      (intrPullMetric (I := I) g hEnorm p hloc).restrictOpen
        (I := 𝓘(Real, E)) (intrAgree (E := E) R) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  simp only [SmoothRiemannianMetric.restrictOpen_inner]
  have hz :
      ((z : intrPullBall (E := E) R) : E) ∈
        Metric.closedBall (0 : E) (3 * R / 4) :=
    Metric.ball_subset_closedBall z.2
  simpa only using
    intrExt_inner (I := I) g hEnorm p hR hloc hz v w

/-- A smooth curve in the pullback ball which stays in the agreement region
is a pullback geodesic whenever its ambient-value curve is a geodesic for the
complete extension. -/
theorem intrPull_geo_of_ext
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (γ : Real → intrPullBall (E := E) R) (s : Set Real)
    (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hstay : ∀ t ∈ s, ‖((γ t : intrPullBall (E := E) R) : E)‖ <
      3 * R / 4)
    (hgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc)
        (fun t => ((γ t : intrPullBall (E := E) R) : E)) s) :
    IsGeodesicOn (I := 𝓘(Real, E))
      (intrPullMetric (I := I) g hEnorm p hloc) γ s := by
  classical
  let U := intrPullBall (E := E) R
  let V := intrAgree (E := E) R
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  let z₀ : V :=
    ⟨intrZero (E := E) hR, by
      change (0 : E) ∈ Metric.ball (0 : E) (3 * R / 4)
      simpa only [Metric.mem_ball, dist_self] using
        (show 0 < 3 * R / 4 by positivity)⟩
  let γV : Real → V := fun t =>
    if ht : γ t ∈ V then ⟨γ t, ht⟩ else z₀
  have hmem : ∀ t ∈ s, γ t ∈ V := by
    intro t ht
    change ((γ t : intrPullBall (E := E) R) : E) ∈
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
  have hgeoU :
      IsGeodesicOn (I := 𝓘(Real, E))
        (gExt.restrictOpen (I := 𝓘(Real, E)) U) γ s := by
    exact (Geodesic.geodesicOn_open_iff
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
          intrExt_restrict (I := I) g hEnorm p hR hloc] at hgeoV'
  have hgeoPullV :
      IsGeodesicOn (I := 𝓘(Real, E)) gPull
        (fun t => ((γV t : V) : U)) s :=
    (Geodesic.geodesicOn_open_iff
      (I := 𝓘(Real, E)) gPull V γV s).1 hgeoV'
  intro t ht
  exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
    (heq t ht).eq_of_nhds.symm (heq t ht).symm (hgeoPullV t ht)

/-- A path contained in the agreement core has the same length for the total
extension as its intrinsic framed exponential image. -/
theorem intrExt_pathLen
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {γ : Real → E} {a b : Real}
    (hγ : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ
      (Set.Icc a b))
    (hstay : ∀ t ∈ Set.Icc a b,
      γ t ∈ Metric.closedBall (0 : E) (3 * R / 4)) :
    let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E) γ a b =
      Manifold.pathELength I
        ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) a b := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  change Manifold.pathELength 𝓘(Real, E) γ a b =
    Manifold.pathELength I
      ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) a b
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hγt : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t
      ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
        (Icc_mem_nhds ht.1 ht.2)
  have hFt : MDifferentiableAt 𝓘(Real, E) I
      (intrinsicFramedExp (I := I) g hEnorm p) (γ t) :=
    (intrFrame_smooth (I := I) g hEnorm p).mdifferentiableAt
      (by decide)
  have hcomp :
      mfderiv 𝓘(Real, Real) I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) t =
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (γ t)).comp
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t) :=
    mfderiv_comp t hFt hγt
  change
    ‖mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1‖ₑ =
      ‖mfderiv 𝓘(Real, Real) I
        ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) t 1‖ₑ
  rw [hcomp]
  change
    ‖mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1‖ₑ =
      ‖mfderiv 𝓘(Real, E) I
        (intrinsicFramedExp (I := I) g hEnorm p) (γ t)
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1)‖ₑ
  let v : TangentSpace 𝓘(Real, E) (γ t) :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t 1
  have hExtNorm :
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner (γ t) v v)) := by
    simpa only using
      (tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt (γ t) v)
  have hBaseNorm :
      ‖mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v‖ₑ =
        ENNReal.ofReal (Real.sqrt
          (g.inner (intrinsicFramedExp (I := I) g hEnorm p (γ t))
            (mfderiv 𝓘(Real, E) I
              (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v)
            (mfderiv 𝓘(Real, E) I
              (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v))) :=
    hEnorm _ _
  change ‖v‖ₑ = ‖mfderiv 𝓘(Real, E) I
    (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v‖ₑ
  rw [hExtNorm, hBaseNorm]
  congr 2
  calc
    gExt.inner (γ t) v v =
        (intrPullMetric (I := I) g hEnorm p hloc).inner
          ⟨γ t, intrClosed_subset (E := E) R hR
            (hstay t ⟨ht.1.le, ht.2.le⟩)⟩ v v :=
      intrExt_inner (I := I) g hEnorm p hR hloc
        (hstay t ⟨ht.1.le, ht.2.le⟩) v v
    _ = intrFrameMetric (I := I) g hEnorm p (γ t) v v :=
      intrPullMetric_inner (I := I) g hEnorm p hloc _ v v
    _ = g.inner
        (intrinsicFramedExp (I := I) g hEnorm p (γ t))
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v)
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (γ t) v) := by
      rw [intrFrameMetric_apply]

/-- A radial path contained in the agreement core has exactly its model
radius as length for the complete extension. -/
theorem intrExt_radial_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {z : E} (hz : ‖z‖ ≤ 3 * R / 4) :
    let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
    letI : RiemannianBundle
        (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
      ⟨gExt.toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E)
        (fun t : Real => Real.smoothTransition t • z) 0 1 =
      ENNReal.ofReal ‖z‖ := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
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
    rw [norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact
      (mul_le_of_le_one_left (norm_nonneg z)
        (Real.smoothTransition.le_one t)).trans hz
  have hext :
      Manifold.pathELength 𝓘(Real, E) γ 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) 0 1 := by
    simpa only [gExt] using
      (intrExt_pathLen (I := I) g hEnorm p hR hloc hγone hstay)
  let zU : intrPullBall (E := E) R :=
    ⟨z, intrClosed_subset (E := E) R hR (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz)⟩
  letI : RiemannianBundle
      (fun y : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) y) :=
    ⟨(intrPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
  have hradC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1
        (intrRadial (E := E) zU) (Set.Icc (0 : Real) 1) :=
    ((intrRadial_smooth (E := E) zU).of_le (by norm_num)).contMDiffOn
  have hpull :=
    intrPull_pathLen (I := I) g hEnorm p hloc hradC1
  have hrad :=
    intrRadial_len (I := I) g hEnorm p hloc zU
  calc
    Manifold.pathELength 𝓘(Real, E) γ 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ γ) 0 1 := hext
    _ = Manifold.pathELength 𝓘(Real, E)
        (intrRadial (E := E) zU) 0 1 := by
      simpa only [γ, zU, intrRadial, intrExpOn, Function.comp_apply] using hpull
    _ = ENNReal.ofReal ‖z‖ := by
      simpa only [zU] using hrad

/-- Two points in a radius-`a` core have complete-extension distance at most
`2a`, witnessed by the two radial segments through the model origin. -/
theorem intrExt_edist_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (ha : a ≤ 3 * R / 4) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) x y ≤
      ENNReal.ofReal (2 * a) := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E :=
    ⟨fun _ _ => rfl⟩
  change Manifold.riemannianEDist 𝓘(Real, E) x y ≤
    ENNReal.ofReal (2 * a)
  have hdist_zero :
      ∀ z : E, ‖z‖ ≤ 3 * R / 4 →
        Manifold.riemannianEDist 𝓘(Real, E) 0 z ≤
          ENNReal.ofReal ‖z‖ := by
    intro z hz
    let γz : Real → E := fun t => Real.smoothTransition t • z
    have hγzinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γz := by
      intro t
      rw [contMDiffAt_iff_contDiffAt]
      exact Real.smoothTransition.contDiff.contDiffAt.smul contDiffAt_const
    have hγz :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γz
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
    rw [intrExt_radial_len (I := I) g hEnorm p hR hloc hz] at hdist
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
      add_le_add (hdist_zero x hx_inner) (hdist_zero y hy_inner)
    _ = ENNReal.ofReal (‖x‖ + ‖y‖) :=
      (ENNReal.ofReal_add (norm_nonneg x) (norm_nonneg y)).symm
    _ ≤ ENNReal.ofReal (2 * a) := by
      exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The total CGT extension is a complete Riemannian metric. -/
theorem intrExt_complete
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    RiemannianMetricComplete (I := 𝓘(Real, E))
      (intrExtMetric (I := I) g hEnorm p hR hloc) := by
  simpa only [intrExtMetric] using
    RiemannianMetricComplete.bumpExtend_complete
      (I := 𝓘(Real, E)) (flatModelMetric E)
      (RiemannianMetricComplete.flatModel_complete (E := E))
      (intrPullBall (E := E) R)
      (intrPullMetric (I := I) g hEnorm p hloc)
      (intrCut (E := E) R hR : E → Real)
      (intrCut_smooth (E := E) R hR)
      (intrCut_range (E := E) R hR)
      (intrCut_support (E := E) R hR)
      (intrCut_compact (E := E) R hR)

/-- The canonical selected minimizing join for the complete CGT extension. -/
noncomputable def intrExtJoin
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) : Real → E := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  exact minJoin (I := 𝓘(Real, E)) gExt hExt x y

/-- The complete-extension join starts at its first endpoint. -/
@[simp] theorem intrExtJoin_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) :
    intrExtJoin (I := I) g hEnorm p hR hloc x y 0 = x := by
  simp only [intrExtJoin, minJoin_zero]

/-- The complete-extension join ends at its second endpoint. -/
@[simp] theorem intrExtJoin_one
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) :
    intrExtJoin (I := I) g hEnorm p hR hloc x y 1 = y := by
  simp only [intrExtJoin, minJoin_one]

/-- The selected complete-extension join is smooth. -/
theorem intrExtJoin_smooth
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) :
    ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞
      (intrExtJoin (I := I) g hEnorm p hR hloc x y) := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  simpa only [intrExtJoin, gExt] using
    intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)

/-- The selected complete-extension join is a geodesic. -/
theorem intrExtJoin_geo
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (x y : E) :
    IsGeodesic (I := 𝓘(Real, E))
      (intrExtMetric (I := I) g hEnorm p hR hloc)
      (intrExtJoin (I := I) g hEnorm p hR hloc x y) := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  simpa only [intrExtJoin, gExt, minJoin] using
    intrinsicGeodesic_isGeodesic
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)

/-- If both endpoints lie in a radius-`a` core with `4a < R`, the selected
complete-extension minimizing join stays strictly inside the metric-agreement
ball of radius `3R/4`. -/
theorem intrExtJoin_fenced
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖intrExtJoin (I := I) g hEnorm p hR hloc x y t‖ <
        3 * R / 4 := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  let γ : Real → E :=
    minJoin (I := 𝓘(Real, E)) gExt hExt x y
  have hγinf :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    exact intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)
  have hγcont : Continuous γ := hγinf.continuous
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have haB : a < 3 * R / 4 := by linarith
  have haInner : a ≤ 3 * R / 4 := haB.le
  have hdist :
      Manifold.riemannianEDist 𝓘(Real, E) x y ≤
        ENNReal.ofReal (2 * a) := by
    simpa only [gExt, riemannianEDistOf] using
      (intrExt_edist_le (I := I) g hEnorm p hR hloc hx hy haInner)
  have hdist_top :
      Manifold.riemannianEDist 𝓘(Real, E) x y ≠
        (⊤ : ENNReal) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdist
  have hfull :
      Manifold.pathELength 𝓘(Real, E) γ 0 1 =
        ENNReal.ofReal
          ((Manifold.riemannianEDist 𝓘(Real, E) x y).toReal) := by
    simpa only [γ] using
      (minJoin_pathLen (I := 𝓘(Real, E)) gExt hExt x y)
  intro t ht
  by_contra hnot
  have hcross :
      3 * R / 4 ≤ ‖γ t‖ := by
    simpa only [γ, intrExtJoin] using (not_lt.mp hnot)
  have hstart : ‖γ 0‖ < 3 * R / 4 := by
    simpa only [γ, minJoin_zero] using hx.trans_lt haB
  obtain ⟨τ, hτ, hτeq, hbefore⟩ :=
    DifferentialGeometry.Analysis.ODE.exists_first_hit_Icc
      zero_le_one hγcont.norm.continuousOn hstart ⟨t, ht, hcross⟩
  have hτ0 : 0 ≤ τ := hτ.1
  let f : Real → Real := fun s => τ * Real.smoothTransition s
  have hfIcc : ∀ s : Real, f s ∈ Set.Icc (0 : Real) τ := by
    intro s
    dsimp only [f]
    constructor
    · exact mul_nonneg hτ0 (Real.smoothTransition.nonneg s)
    · nlinarith [Real.smoothTransition.nonneg s,
        Real.smoothTransition.le_one s]
  let η : Real → E := γ ∘ f
  have hηinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ η := by
    apply hγinf.comp
    rw [contMDiff_iff_contDiff]
    dsimp only [f]
    fun_prop
  have hηstay :
      ∀ s : Real, η s ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    intro s
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbefore (f s) (hfIcc s)
  have hηmem : ∀ s : Real, η s ∈ intrPullBall (E := E) R := by
    intro s
    exact intrClosed_subset (E := E) R hR (hηstay s)
  let ηU : Real → intrPullBall (E := E) R :=
    fun s => ⟨η s, hηmem s⟩
  have hηUinf :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ ηU := by
    intro s
    exact codRestr_contMDiffAt (V := intrPullBall (E := E) R)
      hηmem (hηinf s)
  have hηC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
        (Set.Icc (0 : Real) 1) :=
    (hηinf.of_le (by decide)).contMDiffOn
  have hηUC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 ηU
        (Set.Icc (0 : Real) 1) :=
    (hηUinf.of_le (by decide)).contMDiffOn
  let xU : intrPullBall (E := E) R :=
    ⟨x, intrClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.trans haInner)⟩
  let zU : intrPullBall (E := E) R :=
    ⟨γ τ, intrClosed_subset (E := E) R hR (by
      rw [Metric.mem_closedBall, dist_zero_right, hτeq])⟩
  have hη0 : η 0 = x := by
    simp only [η, f, Function.comp_apply,
      Real.smoothTransition.zero_of_nonpos le_rfl, mul_zero, γ,
      minJoin_zero]
  have hη1 : η 1 = γ τ := by
    simp only [η, f, Function.comp_apply,
      Real.smoothTransition.one_of_one_le le_rfl, mul_one]
  have hηU0 : ηU 0 = xU := by
    apply Subtype.ext
    exact hη0
  have hηU1 : ηU 1 = zU := by
    apply Subtype.ext
    exact hη1
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  letI : RiemannianBundle
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  have hpullLen :
      Manifold.pathELength 𝓘(Real, E) ηU 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) 0 1 := by
    simpa only [ηU, intrExpOn, Function.comp_apply] using
      (intrPull_pathLen (I := I) g hEnorm p hloc hηUC1).symm
  have hextLen :
      Manifold.pathELength 𝓘(Real, E) η 0 1 =
        Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) 0 1 := by
    simpa only [gExt] using
      (intrExt_pathLen (I := I) g hEnorm p hR hloc hηC1
        (fun s _ => hηstay s))
  have hmonoF : MonotoneOn f (Set.Icc (0 : Real) 1) := by
    intro s _ u _ hsu
    dsimp only [f]
    exact mul_le_mul_of_nonneg_left
      (Real.smoothTransition.monotone hsu) hτ0
  have hfDiff : DifferentiableOn Real f (Set.Icc (0 : Real) 1) := by
    dsimp only [f]
    exact
      ((contDiff_const.mul (Real.smoothTransition.contDiff (n := 1))).differentiable
        one_ne_zero).differentiableOn
  have hηPrefix :
      Manifold.pathELength 𝓘(Real, E) η 0 1 =
        Manifold.pathELength 𝓘(Real, E) γ 0 τ := by
    convert Manifold.pathELength_comp_of_monotoneOn
      (I := 𝓘(Real, E)) (γ := γ) (f := f)
      (a := 0) (b := 1) zero_le_one hmonoF hfDiff
      (hγinf.mdifferentiable (by simp)).mdifferentiableOn using 1
    all_goals
      simp only [f, Real.smoothTransition.zero_of_nonpos le_rfl,
        Real.smoothTransition.one_of_one_le le_rfl, mul_zero, mul_one]
  have hprefix :
      Manifold.pathELength 𝓘(Real, E) γ 0 τ ≤
        ENNReal.ofReal (2 * a) := by
    calc
      Manifold.pathELength 𝓘(Real, E) γ 0 τ ≤
          Manifold.pathELength 𝓘(Real, E) γ 0 1 :=
        Manifold.pathELength_mono le_rfl hτ.2
      _ = ENNReal.ofReal
          ((Manifold.riemannianEDist 𝓘(Real, E) x y).toReal) := hfull
      _ = Manifold.riemannianEDist 𝓘(Real, E) x y :=
        ENNReal.ofReal_toReal hdist_top
      _ ≤ ENNReal.ofReal (2 * a) := hdist
  have hdist_xz :
      Manifold.riemannianEDist 𝓘(Real, E) xU zU ≤
        ENNReal.ofReal (2 * a) := by
    have hpath :=
      Manifold.riemannianEDist_le_pathELength
        (I := 𝓘(Real, E)) (x := xU) (y := zU)
        hηUC1 hηU0 hηU1 zero_le_one
    calc
      Manifold.riemannianEDist 𝓘(Real, E) xU zU ≤
          Manifold.pathELength 𝓘(Real, E) ηU 0 1 := hpath
      _ = Manifold.pathELength I
          ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) 0 1 := hpullLen
      _ = Manifold.pathELength 𝓘(Real, E) η 0 1 := hextLen.symm
      _ = Manifold.pathELength 𝓘(Real, E) γ 0 τ := hηPrefix
      _ ≤ ENNReal.ofReal (2 * a) := hprefix
  have hx0 :=
    intrPull_dist_zero (I := I) g hEnorm p hR hloc xU
  have hz0 :=
    intrPull_dist_zero (I := I) g hEnorm p hR hloc zU
  have hx0' :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrZero (E := E) hR) xU =
        ENNReal.ofReal ‖(xU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc)
          (intrZero (E := E) hR) xU =
      ENNReal.ofReal ‖(xU : E)‖
    exact hx0
  have hz0' :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrZero (E := E) hR) zU =
        ENNReal.ofReal ‖(zU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc)
          (intrZero (E := E) hR) zU =
      ENNReal.ofReal ‖(zU : E)‖
    exact hz0
  have htri :
      Manifold.riemannianEDist 𝓘(Real, E)
          (intrZero (E := E) hR) zU ≤
        Manifold.riemannianEDist 𝓘(Real, E)
            (intrZero (E := E) hR) xU +
          Manifold.riemannianEDist 𝓘(Real, E) xU zU :=
    Manifold.riemannianEDist_triangle
  have hB3a :
      ENNReal.ofReal (3 * R / 4) ≤ ENNReal.ofReal (3 * a) := by
    calc
      ENNReal.ofReal (3 * R / 4) =
          Manifold.riemannianEDist 𝓘(Real, E)
            (intrZero (E := E) hR) zU := by
        rw [hz0']
        simp only [zU, hτeq]
      _ ≤ Manifold.riemannianEDist 𝓘(Real, E)
            (intrZero (E := E) hR) xU +
          Manifold.riemannianEDist 𝓘(Real, E) xU zU := htri
      _ = ENNReal.ofReal ‖x‖ +
          Manifold.riemannianEDist 𝓘(Real, E) xU zU := by
        rw [hx0']
      _ ≤ ENNReal.ofReal a + ENNReal.ofReal (2 * a) :=
        add_le_add (ENNReal.ofReal_le_ofReal hx) hdist_xz
      _ = ENNReal.ofReal (3 * a) := by
        rw [← ENNReal.ofReal_add ha (mul_nonneg (by norm_num) ha)]
        congr 2
        ring
  have hreal : 3 * R / 4 ≤ 3 * a :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hB3a
  linarith

/-- For a fixed pair of core points, the complete-extension minimizing
geodesic admits a globally smooth codrestriction to the pullback ball.  The
codrestricted curve agrees with the ambient minimizing geodesic on a
neighborhood of `[0, 1]`, and is therefore a pullback geodesic on that
interval. -/
theorem exists_fenced_curve
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : intrPullBall (E := E) R}
    (hx : x ∈ intrCore (E := E) R a)
    (hy : y ∈ intrCore (E := E) R a) :
    ∃ γU : Real → intrPullBall (E := E) R,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γU ∧
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc)
        γU (Set.Icc (0 : Real) 1) ∧
      γU 0 = x ∧ γU 1 = y ∧
      (∀ t ∈ Set.Icc (0 : Real) 1,
        ‖((γU t : intrPullBall (E := E) R) : E)‖ < 3 * R / 4) ∧
      Set.EqOn
        (fun t => ((γU t : intrPullBall (E := E) R) : E))
        (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
        (Set.Icc (0 : Real) 1) := by
  classical
  let γ : Real → E :=
    intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E)
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    simpa only [γ] using
      intrExtJoin_smooth (I := I) g hEnorm p hR hloc (x : E) (y : E)
  have hγgeo :
      IsGeodesic (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) γ := by
    simpa only [γ] using
      intrExtJoin_geo (I := I) g hEnorm p hR hloc (x : E) (y : E)
  have hγfence : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖γ t‖ < 3 * R / 4 := by
    simpa only [γ] using
      intrExtJoin_fenced (I := I) g hEnorm p hR h4aR hloc hx hy
  have hγ0_ball : γ 0 ∈ Metric.ball (0 : E) R := by
    simpa only [γ, intrExtJoin_zero] using x.property
  have hγ1_ball : γ 1 ∈ Metric.ball (0 : E) R := by
    simpa only [γ, intrExtJoin_one] using y.property
  have hpre0 : γ ⁻¹' Metric.ball (0 : E) R ∈ 𝓝 (0 : Real) :=
    hγinf.continuous.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hγ0_ball)
  have hpre1 : γ ⁻¹' Metric.ball (0 : E) R ∈ 𝓝 (1 : Real) :=
    hγinf.continuous.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hγ1_ball)
  obtain ⟨ε0, hε0, hε0sub⟩ := Metric.mem_nhds_iff.mp hpre0
  obtain ⟨ε1, hε1, hε1sub⟩ := Metric.mem_nhds_iff.mp hpre1
  let ε : Real := min ε0 ε1
  have hε : 0 < ε := by
    simpa only [ε] using lt_min hε0 hε1
  have hε_le0 : ε ≤ ε0 := by
    exact min_le_left ε0 ε1
  have hε_le1 : ε ≤ ε1 := by
    exact min_le_right ε0 ε1
  have hstayExt : ∀ t ∈ Set.Icc (-ε / 2) (1 + ε / 2),
      γ t ∈ Metric.ball (0 : E) R := by
    intro t ht
    by_cases ht0 : t < 0
    · apply hε0sub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg ht0]
      have hhalf : ε / 2 < ε0 := by
        linarith [hε, hε_le0]
      linarith [ht.1, hhalf]
    · have ht0' : 0 ≤ t := le_of_not_gt ht0
      by_cases ht1 : t ≤ 1
      · rw [Metric.mem_ball, dist_zero_right]
        exact (hγfence t ⟨ht0', ht1⟩).trans (by linarith)
      · have ht1' : 1 < t := lt_of_not_ge ht1
        apply hε1sub
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht1')]
        have hhalf : ε / 2 < ε1 := by
          linarith [hε, hε_le1]
        linarith [ht.2, hhalf]
  let c : Real := 1 / 2
  let lam : Real := 1 / 2 + ε / 2
  let clipLeft : Real := -1 / 2 - ε / 4
  let clipRight : Real := 1 / 2 + ε / 4
  have hlam : 0 < lam := by
    dsimp only [lam]
    linarith
  have hclipLeft : -lam < clipLeft := by
    dsimp only [lam, clipLeft]
    linarith
  have hclipRight : clipRight < lam := by
    dsimp only [lam, clipRight]
    linarith
  obtain ⟨σ, hσinf, hσid, hσrange⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_time_window_clip
      hlam hclipLeft hclipRight
  let τ : Real → Real := fun t => c + σ (t - c)
  have hτinf : ContDiff Real (∞ : WithTop ℕ∞) τ := by
    dsimp only [τ]
    exact contDiff_const.add
      (hσinf.comp (contDiff_id.sub contDiff_const))
  have hτrange : ∀ t, τ t ∈ Set.Icc (-ε / 2) (1 + ε / 2) := by
    intro t
    have hσbounds := (abs_le.mp (hσrange (t - c)))
    dsimp only [τ, c, lam] at hσbounds ⊢
    constructor <;> linarith
  have hτid :
      Set.EqOn τ id (Set.Icc (-ε / 4) (1 + ε / 4)) := by
    intro t ht
    have htClip : t - c ∈ Set.Icc clipLeft clipRight := by
      dsimp only [c, clipLeft, clipRight]
      constructor <;> linarith [ht.1, ht.2]
    have hσ := hσid htClip
    change σ (t - c) = t - c at hσ
    dsimp only [τ]
    rw [hσ]
    dsimp only [c, id]
    ring
  let γU : Real → intrPullBall (E := E) R := fun t =>
    ⟨γ (τ t), hstayExt (τ t) (hτrange t)⟩
  have hγUinf :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γU := by
    have hcomp :
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ (fun t => γ (τ t)) := by
      apply hγinf.comp
      rw [contMDiff_iff_contDiff]
      exact hτinf
    intro t
    exact codRestr_contMDiffAt
      (V := intrPullBall (E := E) R)
      (fun s => hstayExt (τ s) (hτrange s)) (hcomp t)
  have hEqLarge :
      Set.EqOn
        (fun t => ((γU t : intrPullBall (E := E) R) : E)) γ
        (Set.Icc (-ε / 4) (1 + ε / 4)) := by
    intro t ht
    change γ (τ t) = γ t
    rw [hτid ht]
    rfl
  have hEq :
      Set.EqOn
        (fun t => ((γU t : intrPullBall (E := E) R) : E)) γ
        (Set.Icc (0 : Real) 1) := by
    intro t ht
    exact hEqLarge ⟨by linarith [ht.1, hε], by linarith [ht.2, hε]⟩
  have hγUgeoExt :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc)
        (fun t => ((γU t : intrPullBall (E := E) R) : E))
        (Set.Icc (0 : Real) 1) := by
    intro t ht
    have hlarge_nhds :
        Set.Icc (-ε / 4) (1 + ε / 4) ∈ 𝓝 t :=
      Icc_mem_nhds (by linarith [ht.1, hε])
        (by linarith [ht.2, hε])
    have heq :
        (fun s => ((γU s : intrPullBall (E := E) R) : E)) =ᶠ[𝓝 t] γ :=
      hEqLarge.eventuallyEq_of_mem hlarge_nhds
    exact Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at
      heq.eq_of_nhds heq (hγgeo t)
  have hγUfence : ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖((γU t : intrPullBall (E := E) R) : E)‖ < 3 * R / 4 := by
    intro t ht
    calc
      ‖((γU t : intrPullBall (E := E) R) : E)‖ = ‖γ t‖ :=
        congrArg norm (hEq ht)
      _ < 3 * R / 4 := hγfence t ht
  have hγUgeo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc)
        γU (Set.Icc (0 : Real) 1) :=
    intrPull_geo_of_ext (I := I) g hEnorm p hR hloc γU
      (Set.Icc (0 : Real) 1) hγUinf hγUfence hγUgeoExt
  refine ⟨γU, hγUinf, hγUgeo, ?_, ?_, hγUfence, ?_⟩
  · apply Subtype.ext
    simpa only [γ, intrExtJoin_zero] using
      hEq (x := (0 : Real)) (by norm_num)
  · apply Subtype.ext
    simpa only [γ, intrExtJoin_one] using
      hEq (x := (1 : Real)) (by norm_num)
  · simpa only [γ] using hEq

/-- On the radius-`a` core, the pullback distance agrees with the distance of
the complete extension.  The forward comparison uses the fenced minimizing
extension join.  Conversely, any pullback curve shorter than that join is
forced by the exact radial distance estimate to remain in the agreement ball,
where its two path lengths coincide. -/
theorem intrCore_edist_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : intrPullBall (E := E) R}
    (hx : x ∈ intrCore (E := E) R a)
    (hy : y ∈ intrCore (E := E) R a) :
    riemannianEDistOf (I := 𝓘(Real, E))
        (intrPullMetric (I := I) g hEnorm p hloc) x y =
      riemannianEDistOf (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) (x : E) (y : E) := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  letI : RiemannianBundle
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  letI (z : intrPullBall (E := E) R) :
      NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : intrPullBall (E := E) R) :
      NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : intrPullBall (E := E) R,
      ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : intrPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace (intrPullBall (E := E) R) :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E)
      (intrPullBall (E := E) R)
  letI : IsRiemannianManifold 𝓘(Real, E)
      (intrPullBall (E := E) R) :=
    ⟨fun _ _ => rfl⟩
  change
    Manifold.riemannianEDist 𝓘(Real, E) x y =
      Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E)
  have ha : 0 ≤ a := (norm_nonneg (x : E)).trans hx
  have haInner : a ≤ 3 * R / 4 := by
    linarith
  have hExtBound :
      Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) ≤
        ENNReal.ofReal (2 * a) := by
    simpa only [gExt, riemannianEDistOf] using
      (intrExt_edist_le (I := I) g hEnorm p hR hloc hx hy haInner)
  have hExtTop :
      Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) ≠
        (⊤ : ENNReal) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hExtBound
  have hlen_of_stay :
      ∀ {γ : Real → intrPullBall (E := E) R} {s t : Real},
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc s t) →
        (∀ u ∈ Set.Icc s t,
          ‖((γ u : intrPullBall (E := E) R) : E)‖ ≤ 3 * R / 4) →
        Manifold.pathELength 𝓘(Real, E) γ s t =
          Manifold.pathELength 𝓘(Real, E)
            (fun u => ((γ u : intrPullBall (E := E) R) : E)) s t := by
    intro γ s t hγ hstay
    let η : Real → E :=
      fun u => ((γ u : intrPullBall (E := E) R) : E)
    have hη :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η (Set.Icc s t) := by
      exact
        ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
          (I := 𝓘(Real, E))
          (U := intrPullBall (E := E) R)).of_le
            (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
          ).comp_contMDiffOn hγ
    have hpull :
        Manifold.pathELength 𝓘(Real, E) γ s t =
          Manifold.pathELength I
            ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) s t := by
      simpa only [η, intrExpOn, Function.comp_apply] using
        (intrPull_pathLen (I := I) g hEnorm p hloc hγ).symm
    have hext :
        Manifold.pathELength 𝓘(Real, E) η s t =
          Manifold.pathELength I
            ((intrinsicFramedExp (I := I) g hEnorm p) ∘ η) s t := by
      simpa only [gExt] using
        (intrExt_pathLen (I := I) g hEnorm p hR hloc hη
          (fun u hu => by
            rw [Metric.mem_closedBall, dist_zero_right]
            exact hstay u hu))
    exact hpull.trans hext.symm
  apply le_antisymm
  · obtain ⟨γ, hγinf, _, hγ0, hγ1, hγstay, hγeq⟩ :=
      exists_fenced_curve (I := I) g hEnorm p hR h4aR hloc hx hy
    have hγC1 :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ
          (Set.Icc (0 : Real) 1) :=
      (hγinf.of_le (by decide)).contMDiffOn
    have hpath :=
      Manifold.riemannianEDist_le_pathELength
        (I := 𝓘(Real, E)) (x := x) (y := y)
        hγC1 hγ0 hγ1 zero_le_one
    have hlen :
        Manifold.pathELength 𝓘(Real, E) γ 0 1 =
          Manifold.pathELength 𝓘(Real, E)
            (fun t => ((γ t : intrPullBall (E := E) R) : E)) 0 1 :=
      hlen_of_stay hγC1 (fun t ht => (hγstay t ht).le)
    have hjoin :
        Manifold.pathELength 𝓘(Real, E)
            (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
            0 1 =
          Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) := by
      calc
        Manifold.pathELength 𝓘(Real, E)
              (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
              0 1 =
            ENNReal.ofReal
              ((Manifold.riemannianEDist 𝓘(Real, E)
                (x : E) (y : E)).toReal) := by
          simpa only [intrExtJoin, gExt] using
            (minJoin_pathLen (I := 𝓘(Real, E)) gExt hExt (x : E) (y : E))
        _ = Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) :=
          ENNReal.ofReal_toReal hExtTop
    calc
      Manifold.riemannianEDist 𝓘(Real, E) x y ≤
          Manifold.pathELength 𝓘(Real, E) γ 0 1 := hpath
      _ = Manifold.pathELength 𝓘(Real, E)
          (fun t => ((γ t : intrPullBall (E := E) R) : E)) 0 1 := hlen
      _ = Manifold.pathELength 𝓘(Real, E)
          (intrExtJoin (I := I) g hEnorm p hR hloc (x : E) (y : E))
          0 1 :=
        Manifold.pathELength_congr hγeq
      _ = Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) := hjoin
  · by_contra hnot
    have hlt :
        Manifold.riemannianEDist 𝓘(Real, E) x y <
          Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) :=
      lt_of_not_ge hnot
    obtain ⟨γ, hγ0, hγ1, hγC1, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hlt
    have htwoPos : 0 < ENNReal.ofReal (2 * a) :=
      lt_of_le_of_lt bot_le (hγlen.trans_le hExtBound)
    have haPos : 0 < a := by
      have : 0 < 2 * a := ENNReal.ofReal_pos.mp htwoPos
      linarith
    have hstay :
        ∀ t ∈ Set.Icc (0 : Real) 1,
          ‖((γ t : intrPullBall (E := E) R) : E)‖ ≤ 3 * R / 4 := by
      intro t ht
      have hγC1pre :
          ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc 0 t) :=
        hγC1.mono (Set.Icc_subset_Icc le_rfl ht.2)
      have hdist_pre :
          Manifold.riemannianEDist 𝓘(Real, E) x (γ t) ≤
            Manifold.pathELength 𝓘(Real, E) γ 0 t :=
        Manifold.riemannianEDist_le_pathELength
          (I := 𝓘(Real, E)) (x := x) (y := γ t)
          hγC1pre hγ0 rfl ht.1
      have hdist_lt :
          Manifold.riemannianEDist 𝓘(Real, E) x (γ t) <
            ENNReal.ofReal (2 * a) := by
        calc
          Manifold.riemannianEDist 𝓘(Real, E) x (γ t) ≤
              Manifold.pathELength 𝓘(Real, E) γ 0 t := hdist_pre
          _ ≤ Manifold.pathELength 𝓘(Real, E) γ 0 1 :=
            Manifold.pathELength_mono le_rfl ht.2
          _ < Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) :=
            hγlen
          _ ≤ ENNReal.ofReal (2 * a) := hExtBound
      have hx0 := intrPull_dist_zero (I := I) g hEnorm p hR hloc x
      have hz0 := intrPull_dist_zero (I := I) g hEnorm p hR hloc (γ t)
      have hnormE :
          ENNReal.ofReal ‖((γ t : intrPullBall (E := E) R) : E)‖ <
            ENNReal.ofReal (3 * a) := by
        calc
          ENNReal.ofReal ‖((γ t : intrPullBall (E := E) R) : E)‖ =
              Manifold.riemannianEDist 𝓘(Real, E)
                (intrZero (E := E) hR) (γ t) := by
            change
              ENNReal.ofReal ‖((γ t : intrPullBall (E := E) R) : E)‖ =
                riemannianEDistOf (I := 𝓘(Real, E)) gPull
                  (intrZero (E := E) hR) (γ t)
            exact hz0.symm
          _ ≤ Manifold.riemannianEDist 𝓘(Real, E)
                (intrZero (E := E) hR) x +
              Manifold.riemannianEDist 𝓘(Real, E) x (γ t) :=
            Manifold.riemannianEDist_triangle
          _ < ENNReal.ofReal a + ENNReal.ofReal (2 * a) := by
            have hx0' :
                Manifold.riemannianEDist 𝓘(Real, E)
                    (intrZero (E := E) hR) x =
                  ENNReal.ofReal ‖(x : E)‖ := by
              change
                riemannianEDistOf (I := 𝓘(Real, E)) gPull
                    (intrZero (E := E) hR) x =
                  ENNReal.ofReal ‖(x : E)‖
              exact hx0
            rw [hx0']
            exact ENNReal.add_lt_add_of_le_of_lt
              ENNReal.ofReal_ne_top (ENNReal.ofReal_le_ofReal hx) hdist_lt
          _ = ENNReal.ofReal (3 * a) := by
            rw [← ENNReal.ofReal_add ha (mul_nonneg (by norm_num) ha)]
            congr 2
            ring
      have hnorm :
          ‖((γ t : intrPullBall (E := E) R) : E)‖ < 3 * a :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hnormE
      exact hnorm.le.trans (by linarith)
    let η : Real → E :=
      fun t => ((γ t : intrPullBall (E := E) R) : E)
    have hηC1 :
        ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
          (Set.Icc (0 : Real) 1) := by
      exact
        ((contMDiff_subtype_val (n := (⊤ : WithTop ℕ∞))
          (I := 𝓘(Real, E))
          (U := intrPullBall (E := E) R)).of_le
            (show (1 : WithTop ℕ∞) ≤ (⊤ : WithTop ℕ∞) from le_top)
          ).comp_contMDiffOn hγC1
    have hη0 : η 0 = (x : E) := by
      simp only [η, hγ0]
    have hη1 : η 1 = (y : E) := by
      simp only [η, hγ1]
    have hExtPath :
        Manifold.riemannianEDist 𝓘(Real, E) (x : E) (y : E) ≤
          Manifold.pathELength 𝓘(Real, E) η 0 1 :=
      Manifold.riemannianEDist_le_pathELength
        (I := 𝓘(Real, E)) (x := (x : E)) (y := (y : E))
        hηC1 hη0 hη1 zero_le_one
    have hlen :
        Manifold.pathELength 𝓘(Real, E) γ 0 1 =
          Manifold.pathELength 𝓘(Real, E) η 0 1 := by
      simpa only [η] using hlen_of_stay hγC1 hstay
    exact (not_lt_of_ge (hExtPath.trans_eq hlen.symm)) hγlen

/-- Two points in the radius-`a` core admit a smooth minimizing geodesic for
the complete extension which stays in the strict metric-agreement ball.

The curve is kept in the ambient model space.  This avoids a non-geodesic
global reparametrization merely to totalize it as a curve in the open pullback
subtype; downstream local pullback arguments may codrestrict it on
`[0, 1]` using the strict fence. -/
theorem exists_fenced_ext
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ∃ γ : Real → E,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ ∧
      IsGeodesic (I := 𝓘(Real, E))
        (intrExtMetric (I := I) g hEnorm p hR hloc) γ ∧
      γ 0 = x ∧ γ 1 = y ∧
      (∀ t ∈ Set.Icc (0 : Real) 1, ‖γ t‖ < 3 * R / 4) ∧
      Variation.arcLength (I := 𝓘(Real, E))
          (intrExtMetric (I := I) g hEnorm p hR hloc) γ 0 1 =
        (riemannianEDistOf (I := 𝓘(Real, E))
          (intrExtMetric (I := I) g hEnorm p hR hloc) x y).toReal := by
  let gExt := intrExtMetric (I := I) g hEnorm p hR hloc
  letI : RiemannianBundle
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (intrExt_complete (I := I) g hEnorm p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  let γ : Real → E :=
    minJoin (I := 𝓘(Real, E)) gExt hExt x y
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)
  · simpa only [γ, minJoin] using
      intrinsicGeodesic_isGeodesic
        (I := 𝓘(Real, E)) gExt hExt x
          (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)
  · exact minJoin_zero (I := 𝓘(Real, E)) gExt hExt x y
  · exact minJoin_one (I := 𝓘(Real, E)) gExt hExt x y
  · simpa only [γ, gExt, intrExtJoin] using
      intrExtJoin_fenced (I := I) g hEnorm p hR h4aR hloc hx hy
  · simpa only [γ, gExt, riemannianEDistOf] using
      minJoin_arcLength (I := 𝓘(Real, E)) gExt hExt x y

/-- A single globally defined join on the pullback ball whose restriction to
each pair of points in the radius-`a` core is a smooth pullback geodesic,
strictly fenced inside the agreement region.  Outside the core the join is
filled arbitrarily; no geodesic claim is made there. -/
theorem exists_fenced_min
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    ∃ join :
        intrPullBall (E := E) R →
        intrPullBall (E := E) R →
        Real → intrPullBall (E := E) R,
      ∀ x ∈ intrCore (E := E) R a,
      ∀ y ∈ intrCore (E := E) R a,
        ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ (join x y) ∧
        IsGeodesicOn (I := 𝓘(Real, E))
          (intrPullMetric (I := I) g hEnorm p hloc)
          (join x y) (Set.Icc (0 : Real) 1) ∧
        join x y 0 = x ∧ join x y 1 = y ∧
        (∀ t ∈ Set.Icc (0 : Real) 1,
          ‖((join x y t : intrPullBall (E := E) R) : E)‖ <
            3 * R / 4) ∧
        Set.EqOn
          (fun t => ((join x y t : intrPullBall (E := E) R) : E))
          (intrExtJoin (I := I) g hEnorm p hR hloc
            (x : E) (y : E))
          (Set.Icc (0 : Real) 1) := by
  classical
  let join :
      intrPullBall (E := E) R →
      intrPullBall (E := E) R →
      Real → intrPullBall (E := E) R :=
    fun x y =>
      if hx : x ∈ intrCore (E := E) R a then
        if hy : y ∈ intrCore (E := E) R a then
          Classical.choose
            (exists_fenced_curve (I := I) g hEnorm p hR h4aR hloc
              (x := x) (y := y) hx hy)
        else fun _ => x
      else fun _ => x
  refine ⟨join, ?_⟩
  intro x hx y hy
  have hspec :=
    Classical.choose_spec
      (exists_fenced_curve (I := I) g hEnorm p hR h4aR hloc
        (x := x) (y := y) hx hy)
  simpa only [join, dif_pos hx, dif_pos hy] using hspec

end CGT
end Riemannian
end Geometry
end DifferentialGeometry

end
