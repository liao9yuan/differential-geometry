import DifferentialGeometry.Geometry.Comparison.CGTRawBranchHess
import DifferentialGeometry.Geometry.Comparison.CGTRawExtJoin
import DifferentialGeometry.Geometry.Comparison.HessianAlongGeodesic
import DifferentialGeometry.Analysis.Calculus.BumpClamp
import DifferentialGeometry.Geometry.Coordinates.PartialDiffeomorphOpens
import DifferentialGeometry.Geometry.Geodesic.PullbackCross
import DifferentialGeometry.Analysis.Calculus.MovingImplicit

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Metric Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential Geodesic NormalCoordinates
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

section Fence

variable [I.Boundaryless] [T2Space (TangentBundle I M)]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
variable [NeZero (Module.finrank Real E)]

omit [I.Boundaryless] [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem rawExtLaunch_len_le
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {x : E} (v : TangentSpace 𝓘(Real, E) x) {s t : Real} :
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E => TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E => TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
    letI : PseudoEMetricSpace E :=
      PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E :=
      (rawExt_complete (I := I) g p hR hloc).complete
    Manifold.pathELength 𝓘(Real, E)
        (rawExtLaunch (I := I) g p hR hloc x v) s t ≤
      ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * (t - s)) := by
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  let speed : Real := Real.sqrt (gExt.inner x v v)
  have hspeed : 0 ≤ speed := Real.sqrt_nonneg _
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hγC1 : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ
      (Set.Icc s t) :=
    (intrinsicGeodesic_contMDiffOn (I := 𝓘(Real, E)) gExt hExt x v).mono
      (Set.subset_univ _)
  have hlen : Manifold.pathELength 𝓘(Real, E) γ s t ≤
      ENNReal.ofReal (speed * (t - s)) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have hle :
        ∫⁻ u in Set.Icc s t,
            (fun u => ‖mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ u (1 : Real)‖ₑ) u ≤
          ∫⁻ _ in Set.Icc s t, ENNReal.ofReal speed := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun u _ => ?_)
      simpa only [γ, speed] using
        intrinsicGeodesic_velocity_enorm_le
          (I := 𝓘(Real, E)) gExt hExt x v u
    have hconst :
        (∫⁻ _ in Set.Icc s t, ENNReal.ofReal speed) =
          ENNReal.ofReal speed * MeasureTheory.volume (Set.Icc s t) :=
      MeasureTheory.setLIntegral_const (Set.Icc s t) (ENNReal.ofReal speed)
    have hvol : MeasureTheory.volume (Set.Icc s t) =
        ENNReal.ofReal (t - s) := Real.volume_Icc
    calc
      ∫⁻ u in Set.Icc s t,
          ‖mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ u (1 : Real)‖ₑ ≤
          ∫⁻ _ in Set.Icc s t, ENNReal.ofReal speed := hle
      _ = ENNReal.ofReal speed * MeasureTheory.volume (Set.Icc s t) := hconst
      _ = ENNReal.ofReal speed * ENNReal.ofReal (t - s) := by rw [hvol]
      _ = ENNReal.ofReal (speed * (t - s)) :=
        (ENNReal.ofReal_mul hspeed).symm
  simpa only [γ, speed, gExt, hExt, rawExtLaunch] using hlen

/-- A raw complete-extension launch of length at most `L` from the `a`-core
stays in the agreement ball whenever `a + L` is below its radius budget. -/
theorem rawExt_short_fenced
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a L : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {x : E} (hx : ‖x‖ ≤ a)
    (v : TangentSpace 𝓘(Real, E) x)
    (hv : Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x v v) ≤ L)
    (hbudget : a + L < 3 * R / 4) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖rawExtLaunch (I := I) g p hR hloc x v t‖ < 3 * R / 4 := by
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    exact intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt x v
  have hγcont : Continuous γ := hγinf.continuous
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have hspeed : 0 ≤ Real.sqrt (gExt.inner x v v) := Real.sqrt_nonneg _
  have hL : 0 ≤ L := hspeed.trans (by simpa only [gExt] using hv)
  have haB : a < 3 * R / 4 := by linarith
  have haInner : a ≤ 3 * R / 4 := haB.le
  have hcore : 3 * R / 4 < R := by linarith
  intro t ht
  by_contra hnot
  have hcross : 3 * R / 4 ≤ ‖γ t‖ := by
    simpa only [γ, gExt, hExt, rawExtLaunch] using not_lt.mp hnot
  have hstart : ‖γ 0‖ < 3 * R / 4 := by
    simpa only [γ, intrinsicGeodesic_zero] using hx.trans_lt haB
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
  have hηstay : ∀ s : Real,
      η s ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    intro s
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbefore (f s) (hfIcc s)
  have hηmem : ∀ s : Real, η s ∈ rawPullBall (E := E) R := by
    intro s
    exact Metric.closedBall_subset_ball hcore (hηstay s)
  let ηU : Real → rawPullBall (E := E) R :=
    fun s => ⟨η s, hηmem s⟩
  have hηUinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ ηU := by
    intro s
    exact codRestr_contMDiffAt (V := rawPullBall (E := E) R)
      hηmem (hηinf s)
  have hηC1 : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
      (Set.Icc (0 : Real) 1) :=
    (hηinf.of_le (by decide)).contMDiffOn
  have hηUC1 : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 ηU
      (Set.Icc (0 : Real) 1) :=
    (hηUinf.of_le (by decide)).contMDiffOn
  let xU : rawPullBall (E := E) R :=
    ⟨x, Metric.closedBall_subset_ball hcore (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx.trans haInner)⟩
  let zU : rawPullBall (E := E) R :=
    ⟨γ τ, Metric.closedBall_subset_ball hcore (by
      rw [Metric.mem_closedBall, dist_zero_right, hτeq])⟩
  have hη0 : η 0 = x := by
    simp only [η, f, Function.comp_apply,
      Real.smoothTransition.zero_of_nonpos le_rfl, mul_zero, γ,
      intrinsicGeodesic_zero]
  have hη1 : η 1 = γ τ := by
    simp only [η, f, Function.comp_apply,
      Real.smoothTransition.one_of_one_le le_rfl, mul_one]
  have hηU0 : ηU 0 = xU := by
    apply Subtype.ext
    exact hη0
  have hηU1 : ηU 1 = zU := by
    apply Subtype.ext
    exact hη1
  letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
  let gPull := rawPullMetric (I := I) g p hloc
  letI : RiemannianBundle
      (fun z : rawPullBall (E := E) R =>
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  have hpullLen : Manifold.pathELength 𝓘(Real, E) ηU 0 1 =
      Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ η) 0 1 := by
    simpa only [ηU, rawExpOn, Function.comp_apply] using
      (rawPull_pathLen (I := I) g hEnorm p hloc hηUC1).symm
  have hextLen : Manifold.pathELength 𝓘(Real, E) η 0 1 =
      Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ η) 0 1 := by
    simpa only [gExt] using
      (rawExt_pathLen (I := I) g hEnorm p hR hloc hηC1
        (fun s _ => hηstay s))
  have hmonoF : MonotoneOn f (Set.Icc (0 : Real) 1) := by
    intro s _ u _ hsu
    dsimp only [f]
    exact mul_le_mul_of_nonneg_left
      (Real.smoothTransition.monotone hsu) hτ0
  have hfDiff : DifferentiableOn Real f (Set.Icc (0 : Real) 1) := by
    dsimp only [f]
    exact ((contDiff_const.mul (Real.smoothTransition.contDiff (n := 1))).differentiable
      one_ne_zero).differentiableOn
  have hηPrefix : Manifold.pathELength 𝓘(Real, E) η 0 1 =
      Manifold.pathELength 𝓘(Real, E) γ 0 τ := by
    convert Manifold.pathELength_comp_of_monotoneOn
      (I := 𝓘(Real, E)) (γ := γ) (f := f)
      (a := 0) (b := 1) zero_le_one hmonoF hfDiff
      (hγinf.mdifferentiable (by simp)).mdifferentiableOn using 1
    all_goals
      simp only [f, Real.smoothTransition.zero_of_nonpos le_rfl,
        Real.smoothTransition.one_of_one_le le_rfl, mul_zero, mul_one]
  have hmul : Real.sqrt (gExt.inner x v v) * τ ≤ L := by
    have hspeedτ : 0 ≤ Real.sqrt (gExt.inner x v v) * (1 - τ) :=
      mul_nonneg hspeed (sub_nonneg.mpr hτ.2)
    nlinarith
  have hprefix : Manifold.pathELength 𝓘(Real, E) γ 0 τ ≤
      ENNReal.ofReal L := by
    calc
      Manifold.pathELength 𝓘(Real, E) γ 0 τ ≤
          ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * (τ - 0)) := by
        simpa only [γ, gExt, hExt, rawExtLaunch] using
          rawExtLaunch_len_le (I := I) g p hR hloc v
      _ = ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * τ) := by ring_nf
      _ ≤ ENNReal.ofReal L := ENNReal.ofReal_le_ofReal hmul
  have hdist_xz : Manifold.riemannianEDist 𝓘(Real, E) xU zU ≤
      ENNReal.ofReal L := by
    have hpath := Manifold.riemannianEDist_le_pathELength
      (I := 𝓘(Real, E)) (x := xU) (y := zU)
      hηUC1 hηU0 hηU1 zero_le_one
    calc
      Manifold.riemannianEDist 𝓘(Real, E) xU zU ≤
          Manifold.pathELength 𝓘(Real, E) ηU 0 1 := hpath
      _ = Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ η) 0 1 :=
        hpullLen
      _ = Manifold.pathELength 𝓘(Real, E) η 0 1 := hextLen.symm
      _ = Manifold.pathELength 𝓘(Real, E) γ 0 τ := hηPrefix
      _ ≤ ENNReal.ofReal L := hprefix
  have hx0 := rawPull_dist_zero (I := I) g hEnorm p hR hloc hdom xU
  have hz0 := rawPull_dist_zero (I := I) g hEnorm p hR hloc hdom zU
  have hx0' : Manifold.riemannianEDist 𝓘(Real, E)
      (rawZero (E := E) hR) xU = ENNReal.ofReal ‖(xU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E))
      (rawPullMetric (I := I) g p hloc) (rawZero (E := E) hR) xU =
        ENNReal.ofReal ‖(xU : E)‖
    exact hx0
  have hz0' : Manifold.riemannianEDist 𝓘(Real, E)
      (rawZero (E := E) hR) zU = ENNReal.ofReal ‖(zU : E)‖ := by
    change riemannianEDistOf (I := 𝓘(Real, E))
      (rawPullMetric (I := I) g p hloc) (rawZero (E := E) hR) zU =
        ENNReal.ofReal ‖(zU : E)‖
    exact hz0
  have htri : Manifold.riemannianEDist 𝓘(Real, E)
      (rawZero (E := E) hR) zU ≤
        Manifold.riemannianEDist 𝓘(Real, E) (rawZero (E := E) hR) xU +
          Manifold.riemannianEDist 𝓘(Real, E) xU zU :=
    Manifold.riemannianEDist_triangle
  have hB : ENNReal.ofReal (3 * R / 4) ≤ ENNReal.ofReal (a + L) := by
    calc
      ENNReal.ofReal (3 * R / 4) =
          Manifold.riemannianEDist 𝓘(Real, E) (rawZero (E := E) hR) zU := by
        rw [hz0']
        simp only [zU, hτeq]
      _ ≤ Manifold.riemannianEDist 𝓘(Real, E) (rawZero (E := E) hR) xU +
          Manifold.riemannianEDist 𝓘(Real, E) xU zU := htri
      _ = ENNReal.ofReal ‖x‖ + Manifold.riemannianEDist 𝓘(Real, E) xU zU := by
        rw [hx0']
      _ ≤ ENNReal.ofReal a + ENNReal.ofReal L :=
        add_le_add (ENNReal.ofReal_le_ofReal hx) hdist_xz
      _ = ENNReal.ofReal (a + L) := by
        rw [← ENNReal.ofReal_add ha hL]
  have hreal : 3 * R / 4 ≤ a + L :=
    (ENNReal.ofReal_le_ofReal_iff (add_nonneg ha hL)).mp hB
  exact (not_le_of_gt hbudget) hreal

private theorem rawExt_prefix
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {x : E} (v : TangentSpace 𝓘(Real, E) x)
    (hfence : ∀ s ∈ Set.Icc (0 : Real) 1,
      ‖rawExtLaunch (I := I) g p hR hloc x v s‖ < 3 * R / 4)
    {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    ‖rawExtLaunch (I := I) g p hR hloc x v t‖ ≤ ‖x‖ +
      Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x v v) * t := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ :=
    intrinsicGeodesic_contMDiff (I := 𝓘(Real, E)) gExt hExt x v
  have hcore : 3 * R / 4 < R := by linarith
  let f : Real → Real := fun s => t * Real.smoothTransition s
  have hfIcc : ∀ s : Real, f s ∈ Set.Icc (0 : Real) t := by
    intro s
    dsimp only [f]
    constructor
    · exact mul_nonneg ht.1 (Real.smoothTransition.nonneg s)
    · calc
        t * Real.smoothTransition s ≤ t * 1 :=
          mul_le_mul_of_nonneg_left
            (Real.smoothTransition.le_one s) ht.1
        _ = t := mul_one t
  let η : Real → E := γ ∘ f
  have hηinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ η := by
    apply hγinf.comp
    rw [contMDiff_iff_contDiff]
    dsimp only [f]
    fun_prop
  have hηstay : ∀ s : Real,
      η s ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    intro s
    rw [Metric.mem_closedBall, dist_zero_right]
    have hs : ‖γ (f s)‖ < 3 * R / 4 := by
      simpa only [γ, gExt, hExt, rawExtLaunch] using
        (hfence (f s) ⟨(hfIcc s).1, (hfIcc s).2.trans ht.2⟩)
    simpa only [η, Function.comp_apply] using hs.le
  have hηmem : ∀ s : Real, η s ∈ rawPullBall (E := E) R := by
    intro s
    exact Metric.closedBall_subset_ball hcore (hηstay s)
  let ηU : Real → rawPullBall (E := E) R :=
    fun s => ⟨η s, hηmem s⟩
  have hηUinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ ηU := by
    intro s
    exact codRestr_contMDiffAt (V := rawPullBall (E := E) R)
      hηmem (hηinf s)
  have hηC1 : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
      (Set.Icc (0 : Real) 1) :=
    (hηinf.of_le (by decide)).contMDiffOn
  have hηUC1 : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 ηU
      (Set.Icc (0 : Real) 1) :=
    (hηUinf.of_le (by decide)).contMDiffOn
  have hγzero : γ 0 = x := by
    simp only [γ, intrinsicGeodesic_zero]
  let xU : rawPullBall (E := E) R :=
    ⟨x, Metric.closedBall_subset_ball hcore (by
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [← hγzero]
      simpa only [γ, gExt, hExt, rawExtLaunch] using
        (hfence 0 ⟨le_rfl, zero_le_one⟩).le)⟩
  let zU : rawPullBall (E := E) R :=
    ⟨γ t, Metric.closedBall_subset_ball hcore (by
      rw [Metric.mem_closedBall, dist_zero_right]
      simpa only [γ, gExt, hExt, rawExtLaunch] using (hfence t ht).le)⟩
  have hη0 : η 0 = x := by
    simp only [η, f, Function.comp_apply,
      Real.smoothTransition.zero_of_nonpos le_rfl, mul_zero, γ,
      intrinsicGeodesic_zero]
  have hη1 : η 1 = γ t := by
    simp only [η, f, Function.comp_apply,
      Real.smoothTransition.one_of_one_le le_rfl, mul_one]
  have hηU0 : ηU 0 = xU := Subtype.ext hη0
  have hηU1 : ηU 1 = zU := Subtype.ext hη1
  letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
  let gPull := rawPullMetric (I := I) g p hloc
  letI : RiemannianBundle
      (fun z : rawPullBall (E := E) R =>
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  have hpullLen : Manifold.pathELength 𝓘(Real, E) ηU 0 1 =
      Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ η) 0 1 := by
    simpa only [ηU, rawExpOn, Function.comp_apply] using
      (rawPull_pathLen (I := I) g hEnorm p hloc hηUC1).symm
  have hextLen : Manifold.pathELength 𝓘(Real, E) η 0 1 =
      Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ η) 0 1 := by
    simpa only [gExt] using
      (rawExt_pathLen (I := I) g hEnorm p hR hloc hηC1
        (fun s _ => hηstay s))
  have hmonoF : MonotoneOn f (Set.Icc (0 : Real) 1) := by
    intro s _ u _ hsu
    dsimp only [f]
    exact mul_le_mul_of_nonneg_left
      (Real.smoothTransition.monotone hsu) ht.1
  have hfDiff : DifferentiableOn Real f (Set.Icc (0 : Real) 1) := by
    dsimp only [f]
    exact ((contDiff_const.mul
      (Real.smoothTransition.contDiff (n := 1))).differentiable
        one_ne_zero).differentiableOn
  have hηPrefix : Manifold.pathELength 𝓘(Real, E) η 0 1 =
      Manifold.pathELength 𝓘(Real, E) γ 0 t := by
    convert Manifold.pathELength_comp_of_monotoneOn
      (I := 𝓘(Real, E)) (γ := γ) (f := f)
      (a := 0) (b := 1) zero_le_one hmonoF hfDiff
      (hγinf.mdifferentiable (by simp)).mdifferentiableOn using 1
    all_goals
      simp only [f, Real.smoothTransition.zero_of_nonpos le_rfl,
        Real.smoothTransition.one_of_one_le le_rfl, mul_zero, mul_one]
  have hprefix : Manifold.pathELength 𝓘(Real, E) γ 0 t ≤
      ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * t) := by
    calc
      Manifold.pathELength 𝓘(Real, E) γ 0 t ≤
          ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * (t - 0)) := by
        simpa only [γ, gExt, hExt, rawExtLaunch] using
          (rawExtLaunch_len_le (I := I) g p hR hloc v (s := 0) (t := t))
      _ = ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * t) := by ring_nf
  have hdist_xz : Manifold.riemannianEDist 𝓘(Real, E) xU zU ≤
      ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * t) := by
    have hpath := Manifold.riemannianEDist_le_pathELength
      (I := 𝓘(Real, E)) (x := xU) (y := zU)
      hηUC1 hηU0 hηU1 zero_le_one
    calc
      Manifold.riemannianEDist 𝓘(Real, E) xU zU ≤
          Manifold.pathELength 𝓘(Real, E) ηU 0 1 := hpath
      _ = Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ η) 0 1 :=
        hpullLen
      _ = Manifold.pathELength 𝓘(Real, E) η 0 1 := hextLen.symm
      _ = Manifold.pathELength 𝓘(Real, E) γ 0 t := hηPrefix
      _ ≤ ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * t) := hprefix
  have hx0 := rawPull_dist_zero (I := I) g hEnorm p hR hloc hdom xU
  have hz0 := rawPull_dist_zero (I := I) g hEnorm p hR hloc hdom zU
  have hsum : 0 ≤ ‖x‖ + Real.sqrt (gExt.inner x v v) * t := by
    exact add_nonneg (norm_nonneg x)
      (mul_nonneg (Real.sqrt_nonneg _) ht.1)
  have hnormE : ENNReal.ofReal ‖γ t‖ ≤
      ENNReal.ofReal (‖x‖ + Real.sqrt (gExt.inner x v v) * t) := by
    calc
      ENNReal.ofReal ‖γ t‖ =
          Manifold.riemannianEDist 𝓘(Real, E) (rawZero (E := E) hR) zU := by
        change ENNReal.ofReal ‖γ t‖ =
          riemannianEDistOf (I := 𝓘(Real, E)) gPull
            (rawZero (E := E) hR) zU
        exact hz0.symm
      _ ≤ Manifold.riemannianEDist 𝓘(Real, E) (rawZero (E := E) hR) xU +
          Manifold.riemannianEDist 𝓘(Real, E) xU zU :=
        Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal ‖x‖ +
          ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * t) := by
        rw [show Manifold.riemannianEDist 𝓘(Real, E)
          (rawZero (E := E) hR) xU = ENNReal.ofReal ‖x‖ by
          change riemannianEDistOf (I := 𝓘(Real, E)) gPull
            (rawZero (E := E) hR) xU = ENNReal.ofReal ‖x‖
          exact hx0]
        exact add_le_add le_rfl hdist_xz
      _ = ENNReal.ofReal (‖x‖ +
          Real.sqrt (gExt.inner x v v) * t) := by
        rw [← ENNReal.ofReal_add (norm_nonneg x)
          (mul_nonneg (Real.sqrt_nonneg _) ht.1)]
  have hnorm : ‖γ t‖ ≤ ‖x‖ + Real.sqrt (gExt.inner x v v) * t :=
    (ENNReal.ofReal_le_ofReal_iff hsum).mp hnormE
  simpa only [γ, gExt, hExt, rawExtLaunch] using hnorm

private theorem rawExt_suffix
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {x y : E} (v : TangentSpace 𝓘(Real, E) x)
    (hfence : ∀ s ∈ Set.Icc (0 : Real) 1,
      ‖rawExtLaunch (I := I) g p hR hloc x v s‖ < 3 * R / 4)
    (hend : rawExtLaunch (I := I) g p hR hloc x v 1 = y)
    {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    ‖rawExtLaunch (I := I) g p hR hloc x v t‖ ≤ ‖y‖ +
      Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x v v) * (1 - t) := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ :=
    intrinsicGeodesic_contMDiff (I := 𝓘(Real, E)) gExt hExt x v
  have hγone : γ 1 = y := by
    simpa only [γ, gExt, hExt, rawExtLaunch] using hend
  have hcore : 3 * R / 4 < R := by linarith
  let f : Real → Real := fun s => 1 - (1 - t) * Real.smoothTransition s
  have hfIcc : ∀ s : Real, f s ∈ Set.Icc t (1 : Real) := by
    intro s
    dsimp only [f]
    constructor
    · calc
        t = 1 - (1 - t) * 1 := by ring
        _ ≤ 1 - (1 - t) * Real.smoothTransition s :=
          sub_le_sub_left
            (mul_le_mul_of_nonneg_left
              (Real.smoothTransition.le_one s) (sub_nonneg.mpr ht.2)) 1
    · exact sub_le_self 1
        (mul_nonneg (sub_nonneg.mpr ht.2)
          (Real.smoothTransition.nonneg s))
  let η : Real → E := γ ∘ f
  have hηinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ η := by
    apply hγinf.comp
    rw [contMDiff_iff_contDiff]
    dsimp only [f]
    fun_prop
  have hηstay : ∀ s : Real,
      η s ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    intro s
    rw [Metric.mem_closedBall, dist_zero_right]
    have hs : ‖γ (f s)‖ < 3 * R / 4 := by
      simpa only [γ, gExt, hExt, rawExtLaunch] using
        (hfence (f s) ⟨ht.1.trans (hfIcc s).1, (hfIcc s).2⟩)
    simpa only [η, Function.comp_apply] using hs.le
  have hηmem : ∀ s : Real, η s ∈ rawPullBall (E := E) R := by
    intro s
    exact Metric.closedBall_subset_ball hcore (hηstay s)
  let ηU : Real → rawPullBall (E := E) R :=
    fun s => ⟨η s, hηmem s⟩
  have hηUinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ ηU := by
    intro s
    exact codRestr_contMDiffAt (V := rawPullBall (E := E) R)
      hηmem (hηinf s)
  have hηC1 : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η
      (Set.Icc (0 : Real) 1) :=
    (hηinf.of_le (by decide)).contMDiffOn
  have hηUC1 : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 ηU
      (Set.Icc (0 : Real) 1) :=
    (hηUinf.of_le (by decide)).contMDiffOn
  let yU : rawPullBall (E := E) R :=
    ⟨y, Metric.closedBall_subset_ball hcore (by
      rw [Metric.mem_closedBall, dist_zero_right, ← hγone]
      simpa only [γ, gExt, hExt, rawExtLaunch] using
        (hfence 1 ⟨zero_le_one, le_rfl⟩).le)⟩
  let zU : rawPullBall (E := E) R :=
    ⟨γ t, Metric.closedBall_subset_ball hcore (by
      rw [Metric.mem_closedBall, dist_zero_right]
      simpa only [γ, gExt, hExt, rawExtLaunch] using (hfence t ht).le)⟩
  have hη0 : η 0 = y := by
    rw [show η 0 = γ 1 by
      simp only [η, f, Function.comp_apply,
        Real.smoothTransition.zero_of_nonpos le_rfl, mul_zero, sub_zero]]
    exact hγone
  have hη1 : η 1 = γ t := by
    simp only [η, f, Function.comp_apply,
      Real.smoothTransition.one_of_one_le le_rfl, mul_one, sub_sub_cancel]
  have hηU0 : ηU 0 = yU := Subtype.ext hη0
  have hηU1 : ηU 1 = zU := Subtype.ext hη1
  letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
  let gPull := rawPullMetric (I := I) g p hloc
  letI : RiemannianBundle
      (fun z : rawPullBall (E := E) R =>
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  have hpullLen : Manifold.pathELength 𝓘(Real, E) ηU 0 1 =
      Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ η) 0 1 := by
    simpa only [ηU, rawExpOn, Function.comp_apply] using
      (rawPull_pathLen (I := I) g hEnorm p hloc hηUC1).symm
  have hextLen : Manifold.pathELength 𝓘(Real, E) η 0 1 =
      Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ η) 0 1 := by
    simpa only [gExt] using
      (rawExt_pathLen (I := I) g hEnorm p hR hloc hηC1
        (fun s _ => hηstay s))
  have hantiF : AntitoneOn f (Set.Icc (0 : Real) 1) := by
    intro s _ u _ hsu
    dsimp only [f]
    exact sub_le_sub_left
      (mul_le_mul_of_nonneg_left
        (Real.smoothTransition.monotone hsu) (sub_nonneg.mpr ht.2)) 1
  have hfDiff : DifferentiableOn Real f (Set.Icc (0 : Real) 1) := by
    have hfcont : ContDiff Real ∞ f := by
      dsimp only [f]
      fun_prop
    exact (hfcont.differentiable (by simp)).differentiableOn
  have hηSuffix : Manifold.pathELength 𝓘(Real, E) η 0 1 =
      Manifold.pathELength 𝓘(Real, E) γ t 1 := by
    convert Manifold.pathELength_comp_of_antitoneOn
      (I := 𝓘(Real, E)) (γ := γ) (f := f)
      (a := 0) (b := 1) zero_le_one hantiF hfDiff
      (hγinf.mdifferentiable (by simp)).mdifferentiableOn using 1
    all_goals
      simp only [f, Real.smoothTransition.zero_of_nonpos le_rfl,
        Real.smoothTransition.one_of_one_le le_rfl, mul_zero, mul_one,
        sub_zero, sub_sub_cancel]
  have hsuffix : Manifold.pathELength 𝓘(Real, E) γ t 1 ≤
      ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * (1 - t)) := by
    simpa only [γ, gExt, hExt, rawExtLaunch] using
      (rawExtLaunch_len_le (I := I) g p hR hloc v (s := t) (t := 1))
  have hdist_yz : Manifold.riemannianEDist 𝓘(Real, E) yU zU ≤
      ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * (1 - t)) := by
    have hpath := Manifold.riemannianEDist_le_pathELength
      (I := 𝓘(Real, E)) (x := yU) (y := zU)
      hηUC1 hηU0 hηU1 zero_le_one
    calc
      Manifold.riemannianEDist 𝓘(Real, E) yU zU ≤
          Manifold.pathELength 𝓘(Real, E) ηU 0 1 := hpath
      _ = Manifold.pathELength I ((framedExpMap (I := I) g p) ∘ η) 0 1 :=
        hpullLen
      _ = Manifold.pathELength 𝓘(Real, E) η 0 1 := hextLen.symm
      _ = Manifold.pathELength 𝓘(Real, E) γ t 1 := hηSuffix
      _ ≤ ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * (1 - t)) := hsuffix
  have hy0 := rawPull_dist_zero (I := I) g hEnorm p hR hloc hdom yU
  have hz0 := rawPull_dist_zero (I := I) g hEnorm p hR hloc hdom zU
  have hsum : 0 ≤ ‖y‖ + Real.sqrt (gExt.inner x v v) * (1 - t) := by
    exact add_nonneg (norm_nonneg y)
      (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr ht.2))
  have hnormE : ENNReal.ofReal ‖γ t‖ ≤
      ENNReal.ofReal (‖y‖ + Real.sqrt (gExt.inner x v v) * (1 - t)) := by
    calc
      ENNReal.ofReal ‖γ t‖ =
          Manifold.riemannianEDist 𝓘(Real, E) (rawZero (E := E) hR) zU := by
        change ENNReal.ofReal ‖γ t‖ =
          riemannianEDistOf (I := 𝓘(Real, E)) gPull
            (rawZero (E := E) hR) zU
        exact hz0.symm
      _ ≤ Manifold.riemannianEDist 𝓘(Real, E) (rawZero (E := E) hR) yU +
          Manifold.riemannianEDist 𝓘(Real, E) yU zU :=
        Manifold.riemannianEDist_triangle
      _ ≤ ENNReal.ofReal ‖y‖ +
          ENNReal.ofReal (Real.sqrt (gExt.inner x v v) * (1 - t)) := by
        rw [show Manifold.riemannianEDist 𝓘(Real, E)
          (rawZero (E := E) hR) yU = ENNReal.ofReal ‖y‖ by
          change riemannianEDistOf (I := 𝓘(Real, E)) gPull
            (rawZero (E := E) hR) yU = ENNReal.ofReal ‖y‖
          exact hy0]
        exact add_le_add le_rfl hdist_yz
      _ = ENNReal.ofReal (‖y‖ +
          Real.sqrt (gExt.inner x v v) * (1 - t)) := by
        rw [← ENNReal.ofReal_add (norm_nonneg y)
          (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr ht.2))]
  have hnorm : ‖γ t‖ ≤ ‖y‖ + Real.sqrt (gExt.inner x v v) * (1 - t) :=
    (ENNReal.ofReal_le_ofReal_iff hsum).mp hnormE
  simpa only [γ, gExt, hExt, rawExtLaunch] using hnorm

private theorem rawExt_scale
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a L : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (v : TangentSpace 𝓘(Real, E) x)
    (hv : Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x v v) ≤ L)
    (hbudget : a + L < 3 * R / 4)
    (hend : rawExtLaunch (I := I) g p hR hloc x v 1 = y) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖rawExtLaunch (I := I) g p hR hloc x v t‖ ≤ a + L / 2 := by
  have hell : 0 ≤ Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x v v) :=
    Real.sqrt_nonneg _
  have hfence :=
    rawExt_short_fenced (I := I) g hEnorm p hR hloc hdom hx v hv hbudget
  intro t ht
  have hpre := rawExt_prefix (I := I) g hEnorm p hR hloc hdom v hfence ht
  have hsuf := rawExt_suffix (I := I) g hEnorm p hR hloc hdom v hfence hend ht
  have hpre' : ‖rawExtLaunch (I := I) g p hR hloc x v t‖ ≤
      a + Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x v v) * t :=
    by nlinarith [hpre, hx]
  have hsuf' : ‖rawExtLaunch (I := I) g p hR hloc x v t‖ ≤
      a + Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x v v) * (1 - t) :=
    by nlinarith [hsuf, hy]
  nlinarith

omit [NeZero (Module.finrank Real E)] in
private theorem rawPinned_inj_nhds
    (F : E × E → E) (hF : ContDiff Real ∞ F)
    {x u : E} (hinj : Function.Injective (Analysis.partialFDeriv₂ F x u)) :
    ∃ U : Set (E × E), U ∈ 𝓝 (x, u) ∧
      Set.InjOn (fun z : E × E => (F z, z.1)) U := by
  classical
  have hsurj : Function.Surjective (Analysis.partialFDeriv₂ F x u) :=
    LinearMap.surjective_of_injective hinj
  let e : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective (Analysis.partialFDeriv₂ F x u)
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  have hpartial : (Analysis.partialFDeriv₂ F x u).IsInvertible := by
    refine ⟨e, ?_⟩
    rfl
  let H : E × E → E × E := Analysis.pinnedRootMap F
  have hH : ContDiff Real ∞ H := by
    simpa only [H, Analysis.pinnedRootMap] using hF.prodMk contDiff_fst
  have hHinv : (fderiv Real H (x, u)).IsInvertible := by
    simpa only [H] using
      Analysis.pinnedFDeriv_inv
        ((hF.differentiable (by simp)).differentiableAt) hpartial
  rcases hHinv with ⟨B, hB⟩
  have hHD : HasFDerivAt H (B : (E × E) →L[Real] (E × E)) (x, u) := by
    rw [hB]
    exact ((hH.differentiable (by simp)).differentiableAt).hasFDerivAt
  let homeomorph := hH.contDiffAt.toOpenPartialHomeomorph H hHD (by simp)
  have hmem : (x, u) ∈ homeomorph.source :=
    hH.contDiffAt.mem_toOpenPartialHomeomorph_source hHD (by simp)
  refine ⟨homeomorph.source, homeomorph.open_source.mem_nhds hmem, ?_⟩
  simpa only [homeomorph, H, Analysis.pinnedRootMap] using homeomorph.injOn

/-- A raw complete-extension exponential is locally injective in its velocity
variable when its short launch lies below the raw conjugacy scale. -/
theorem rawExt_pinned_inj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K L : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K)
    (hRm : ∀ z : E, ‖z‖ < 3 * R / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p z) 4
        (Geometry.Curvature.metricRm04At (I := I) (M := M) g
          (framedExpMap (I := I) g p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    {x : E} (hx : ‖x‖ ≤ a) (u : E)
    (huL : Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x u u) ≤ L)
    (hbudget : a + L < 3 * R / 4) :
    ∃ U : Set (E × E), U ∈ 𝓝 (x, u) ∧
      Set.InjOn
        (fun z : E × E =>
          (rawExtLaunch (I := I) g p hR hloc z.1 z.2 1, z.1)) U := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) := inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  have hfence :=
    rawExt_short_fenced (I := I) g hEnorm p hR hloc hdom hx u huL hbudget
  have hnot := rawExt_no_conj (I := I) g p hR hloc u hfence huL hK hRm hsmall
  change ¬ IsConjVec (I := 𝓘(Real, E)) gExt hExt x u at hnot
  have hlift :
      ContMDiff (𝓘(Real, E).prod 𝓘(Real, E)) 𝓘(Real, E).tangent ∞
        (fun z : E × E => (⟨z.1, z.2⟩ : TangentBundle 𝓘(Real, E) E)) := by
    have h := contMDiff_tangentBundleModelSpaceHomeomorph_symm
      (I := 𝓘(Real, E)) (n := (∞ : WithTop ℕ∞))
    unfold ModelProd at h
    rw [← chartedSpaceSelf_prod] at h
    simpa only [tangentBundleModelSpaceHomeomorph_coe_symm,
      TotalSpace.toProd, Equiv.coe_fn_symm_mk] using h
  have hFmd :
      ContMDiff (𝓘(Real, E).prod 𝓘(Real, E)) 𝓘(Real, E) ∞ F := by
    simpa only [F, Function.comp_apply] using
      (intrinsicExp_smooth (I := 𝓘(Real, E)) gExt hExt).comp hlift
  have hFcd : ContDiff Real ∞ F := by
    rw [← contMDiff_iff_contDiff, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hFmd
  let f : E → E := fun w =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt x w
  have hfM :
      HasMFDerivAt 𝓘(Real, E) 𝓘(Real, E) f u
        (mfderiv 𝓘(Real, E) 𝓘(Real, E) f u) :=
    ((intrinsicFiber_smooth (I := 𝓘(Real, E)) gExt hExt x).contMDiffAt
      |>.mdifferentiableAt (by simp)).hasMFDerivAt
  have hf : HasFDerivAt f
      (mfderiv 𝓘(Real, E) 𝓘(Real, E) f u) u :=
    hasMFDerivAt_iff_hasFDerivAt.mp hfM
  have hpartial : Analysis.partialFDeriv₂ F x u =
      mfderiv 𝓘(Real, E) 𝓘(Real, E) f u := by
    apply Analysis.partialFDeriv₂_eq
      ((hFcd.differentiable (by simp)).differentiableAt)
    simpa only [F, f] using hf
  have hinj : Function.Injective (Analysis.partialFDeriv₂ F x u) := by
    rw [hpartial]
    simpa only [IsConjVec, f, not_not] using hnot
  simpa only [F, rawExtLaunch] using rawPinned_inj_nhds F hFcd hinj

omit [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [NeZero (Module.finrank Real E)] in
private theorem rawPull_geo_at
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real}
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    {γ : Real → rawPullBall (E := E) R} {t : Real}
    (hγ : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞ γ t)
    (hgeo : HasGeodesicEquationAt (I := I) g
      (fun s => rawExpOn (I := I) g p R (γ s)) t) :
    HasGeodesicEquationAt (I := 𝓘(Real, E))
      (rawPullMetric (I := I) g p hloc) γ t := by
  classical
  letI : SigmaCompactSpace (rawPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (rawPullBall (E := E) R).isOpen)
  letI : T2Space M := gauss_t2Space_base I
  obtain ⟨Φ, htΦ, hfΦ⟩ :=
    (rawExpOn_local (I := I) g p hloc) (γ t)
  let U : Opens (rawPullBall (E := E) R) :=
    ⟨Φ.source, Φ.open_source⟩
  have hUΦ : (U : Set (rawPullBall (E := E) R)) ⊆ Φ.source :=
    fun _ hx => hx
  let V : Opens M :=
    ⟨(Φ : rawPullBall (E := E) R → M) '' (U : Set (rawPullBall (E := E) R)),
      image_opens_isOpen Φ hUΦ⟩
  let Ψ : Diffeomorph 𝓘(Real, E) I U V ∞ :=
    PartialDiffeomorph.toOpensDiffeoCross Φ hUΦ
  letI : SigmaCompactSpace U :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen 𝓘(Real, E) U.isOpen)
  letI : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_iff_isSigmaCompact_univ.mpr (by
        simpa using
          (isSigmaCompact_univ.image Ψ.toHomeomorph.continuous)))
  let γtU : U := ⟨γ t, htΦ⟩
  let γU : Real → U := fun s =>
    if hs : γ s ∈ (U : Set (rawPullBall (E := E) R)) then ⟨γ s, hs⟩ else γtU
  have hmem : ∀ᶠ s in 𝓝 t, γ s ∈ (U : Set (rawPullBall (E := E) R)) :=
    hγ.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds htΦ)
  have hγU_val : (fun s => ((γU s : U) : rawPullBall (E := E) R)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hmem] with s hs
    simp only [γU, dif_pos hs]
  have hγU_smooth : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞ γU t := by
    have hamb : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞
        (fun s => ((γU s : U) : rawPullBall (E := E) R)) t :=
      hγ.congr_of_eventuallyEq hγU_val
    have hcod := codRestr_contMDiffAt
      (I := 𝓘(Real, Real)) (J := 𝓘(Real, E)) (V := U)
      (f := fun s => ((γU s : U) : rawPullBall (E := E) R))
      (fun s => (γU s).property) hamb
    simpa only [Subtype.coe_eta] using hcod
  have hΦmfd :
      ∀ (x : U),
        mfderiv 𝓘(Real, E) I (Φ : rawPullBall (E := E) R → M)
          (x : rawPullBall (E := E) R) =
          mfderiv 𝓘(Real, E) I (rawExpOn (I := I) g p R)
            (x : rawPullBall (E := E) R) := by
    intro x
    have heq : rawExpOn (I := I) g p R =ᶠ[𝓝 (x : rawPullBall (E := E) R)]
        (Φ : rawPullBall (E := E) R → M) :=
      Filter.eventuallyEq_of_mem
        (Φ.open_source.mem_nhds x.property) hfΦ
    exact heq.mfderiv_eq.symm
  have hmetric :
      (rawPullMetric (I := I) g p hloc).restrictOpen (I := 𝓘(Real, E)) U =
        Diffeomorph.pullbackMetricCross (g.restrictOpen (I := I) V) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    dsimp only [Ψ]
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      Diffeomorph.pullbackMetricCross_inner,
      SmoothRiemannianMetric.restrictOpen_inner,
      PartialDiffeomorph.opensDiffeo_mfd,
      PartialDiffeomorph.opensDiffeo_mfd,
      hΦmfd x]
    change
      (rawPullMetric (I := I) g p hloc).inner (x : rawPullBall (E := E) R) v w =
        g.inner ((Ψ x : V) : M)
          (mfderiv 𝓘(Real, E) I (rawExpOn (I := I) g p R)
            (x : rawPullBall (E := E) R) v)
          (mfderiv 𝓘(Real, E) I (rawExpOn (I := I) g p R)
            (x : rawPullBall (E := E) R) w)
    rw [rawPullMetric, localPullMetric_inner]
    have hval : ((Ψ x : V) : M) =
        rawExpOn (I := I) g p R (x : rawPullBall (E := E) R) := by
      change (Φ : rawPullBall (E := E) R → M)
        (x : rawPullBall (E := E) R) = _
      exact (hfΦ x.property).symm
    rw [hval]
  have hmap_eq :
      (fun s => rawExpOn (I := I) g p R (γ s)) =ᶠ[𝓝 t]
        (fun s => ((Ψ (γU s) : V) : M)) := by
    filter_upwards [hmem] with s hs
    dsimp only [Ψ]
    have hγUs : ((γU s : U) : rawPullBall (E := E) R) = γ s := by
      simp only [γU, dif_pos hs]
    change rawExpOn (I := I) g p R (γ s) =
      (Φ : rawPullBall (E := E) R → M)
        ((γU s : U) : rawPullBall (E := E) R)
    rw [hγUs]
    exact hfΦ hs
  have hgeo_target :
      HasGeodesicEquationAt (I := I) g
        (fun s => ((Ψ (γU s) : V) : M)) t :=
    HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (I := I) (g := g) hmap_eq.eq_of_nhds.symm hmap_eq.symm hgeo
  have hgeo_V :
      HasGeodesicEquationAt (I := I) (g.restrictOpen (I := I) V)
        (fun s => Ψ (γU s)) t := by
    have hOn : IsGeodesicOn (I := I) g
        (fun s => ((Ψ (γU s) : V) : M)) ({t} : Set Real) := by
      intro s hs
      simpa only [Set.mem_singleton_iff] using hs ▸ hgeo_target
    have hOnV :=
      (geodesicOn_open_iff (I := I) g V
        (fun s => Ψ (γU s)) ({t} : Set Real)).mpr hOn
    exact hOnV t (Set.mem_singleton t)
  have hgeo_pull :
      HasGeodesicEquationAt (I := 𝓘(Real, E))
        (Diffeomorph.pullbackMetricCross (g.restrictOpen (I := I) V) Ψ)
        γU t :=
    geoEq_of_mapCrossAt (I := 𝓘(Real, E)) (J := I)
      (g.restrictOpen (I := I) V) Ψ γU t hγU_smooth hgeo_V
  have hgeo_U :
      HasGeodesicEquationAt (I := 𝓘(Real, E))
        ((rawPullMetric (I := I) g p hloc).restrictOpen
          (I := 𝓘(Real, E)) U) γU t := by
    rw [hmetric]
    exact hgeo_pull
  have hgeo_amb :
      HasGeodesicEquationAt (I := 𝓘(Real, E))
        (rawPullMetric (I := I) g p hloc)
        (fun s => ((γU s : U) : rawPullBall (E := E) R)) t := by
    have hOnU : IsGeodesicOn (I := 𝓘(Real, E))
        ((rawPullMetric (I := I) g p hloc).restrictOpen
          (I := 𝓘(Real, E)) U) γU ({t} : Set Real) := by
      intro s hs
      simpa only [Set.mem_singleton_iff] using hs ▸ hgeo_U
    have hOn :=
      (geodesicOn_open_iff (I := 𝓘(Real, E))
        (rawPullMetric (I := I) g p hloc) U γU ({t} : Set Real)).mp hOnU
    exact hOn t (Set.mem_singleton t)
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
    (I := 𝓘(Real, E)) (g := rawPullMetric (I := I) g p hloc)
      hγU_val.eq_of_nhds.symm hγU_val.symm hgeo_amb

omit [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [NeZero (Module.finrank Real E)] in
private theorem rawOrigin_geo
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {z : E} (hz : ‖z‖ < 3 * R / 4) :
    ∃ c : Real, 1 < c ∧
      IsGeodesicOn (I := 𝓘(Real, E))
        (rawExtMetric (I := I) g p hR hloc)
        (fun t : Real => t • z) (Set.Ioo (-c) c) := by
  classical
  let B : Real := 3 * R / 4
  let n : Real := ‖z‖
  let gap : Real := B - n
  let ε : Real := gap / (4 * (n + 1))
  let c : Real := 1 + ε
  let d : Real := 1 + 2 * ε
  have hn : 0 ≤ n := by
    exact norm_nonneg z
  have hgap : 0 < gap := by
    simpa only [gap, B, n] using sub_pos.mpr hz
  have hden : 0 < 4 * (n + 1) := by positivity
  have hε : 0 < ε := div_pos hgap hden
  have hc : 1 < c := by
    dsimp only [c]
    linarith
  have hcd : c < d := by
    dsimp only [c, d]
    linarith
  have hd_mul : d * n < B := by
    have hsmall : 2 * ε * n < gap := by
      rw [show 2 * ε * n = (2 * gap * n) / (4 * (n + 1)) by
        dsimp only [ε]
        ring]
      rw [div_lt_iff₀ hden]
      nlinarith
    dsimp only [d]
    dsimp only [gap] at hsmall
    linarith
  have hBR : B < R := by
    dsimp only [B]
    nlinarith
  let b : ContDiffBump (0 : Real) :=
    { rIn := c
      rOut := d
      rIn_pos := lt_trans zero_lt_one hc
      rIn_lt_rOut := hcd }
  let φ : Real → Real := b.radial
  have hφ_smooth : ContDiff Real (∞ : WithTop ℕ∞) φ := by
    simpa only [φ] using b.radial_contDiff
  have hφ_bound : ∀ t : Real, ‖φ t • z‖ < B := by
    intro t
    have ht := b.radial_mapsTo (Set.mem_univ t)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hn0 : n = 0
    · have hz0 : ‖z‖ = 0 := by simpa only [n] using hn0
      rw [hz0, mul_zero]
      simpa only [hn0, mul_zero] using hd_mul
    · calc
        |φ t| * ‖z‖ = |φ t| * n := by rfl
        _ < d * n :=
          mul_lt_mul_of_pos_right ht (lt_of_le_of_ne hn (Ne.symm hn0))
        _ < B := hd_mul
  have hφ_eq : ∀ {t : Real}, t ∈ Set.Ioo (-c) c → φ t = t := by
    intro t ht
    apply b.radial_eq_self
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact (abs_lt.mpr ht).le
  let γ : Real → rawPullBall (E := E) R := fun t =>
    ⟨φ t • z, by
      change φ t • z ∈ Metric.ball (0 : E) R
      rw [Metric.mem_ball, dist_zero_right]
      exact (hφ_bound t).trans hBR⟩
  have hγ_smooth :
      ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    intro t
    exact codRestr_contMDiffAt
      (I := 𝓘(Real, Real)) (J := 𝓘(Real, E))
      (V := rawPullBall (E := E) R)
      (f := fun s : Real => φ s • z)
      (fun s => (γ s).property)
      ((hφ_smooth.smul contDiff_const).contMDiff.contMDiffAt)
  let gPull := rawPullMetric (I := I) g p hloc
  letI : RiemannianBundle
      (fun x : rawPullBall (E := E) R ↦ TangentSpace 𝓘(Real, E) x) :=
    ⟨gPull.toRiemannianMetric⟩
  have hmap_geo :
      IsGeodesicOn (I := I) g
        (fun t => rawExpOn (I := I) g p R (γ t))
        (Set.Ioo (-c) c) := by
    intro t ht
    have heq :
        (fun s => rawExpOn (I := I) g p R (γ s)) =ᶠ[𝓝 t]
          (fun s => expMap (I := I) g p
            (s • normalFrame (I := I) g p z)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      change framedExpMap (I := I) g p (γ s : E) =
        expMap (I := I) g p (s • normalFrame (I := I) g p z)
      rw [show (γ s : E) = s • z by
        change φ s • z = s • z
        rw [hφ_eq hs]]
      simp only [framedExpMap_apply, map_smul]
    have htBall : t • z ∈ rawPullBall (E := E) R := by
      change t • z ∈ Metric.ball (0 : E) R
      rw [Metric.mem_ball, dist_zero_right, ← hφ_eq ht]
      exact (hφ_bound t).trans hBR
    have htDom := hdom ⟨t • z, htBall⟩ 1 ⟨zero_le_one, le_rfl⟩
    have hrad :
        HasGeodesicEquationAt (I := I) g
          (fun s : Real => expMap (I := I) g p
            (s • normalFrame (I := I) g p z)) t := by
      apply raw_radial_geo_at (I := I) g p
        (normalFrame (I := I) g p z)
      simpa only [one_smul, map_smul] using htDom
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
      heq.eq_of_nhds heq hrad
  have hpull_geo :
      IsGeodesicOn (I := 𝓘(Real, E)) gPull γ
        (Set.Ioo (-c) c) := by
    intro t ht
    simpa only [gPull] using
      rawPull_geo_at (I := I) g p hloc (hγ_smooth t) (hmap_geo t ht)
  have hext_geo :
      IsGeodesicOn (I := 𝓘(Real, E))
        (rawExtMetric (I := I) g p hR hloc)
        (fun t => ((γ t : rawPullBall (E := E) R) : E))
        (Set.Ioo (-c) c) := by
    exact rawExt_geo_of_pull (I := I) g p hR hloc γ
      (Set.Ioo (-c) c) hγ_smooth
      (fun t _ht => by
        change ‖φ t • z‖ < 3 * R / 4
        simpa only [B] using hφ_bound t)
      (by simpa only [gPull] using hpull_geo)
  refine ⟨c, hc, ?_⟩
  intro t ht
  have heq :
      (fun s => ((γ s : rawPullBall (E := E) R) : E)) =ᶠ[𝓝 t]
        (fun s : Real => s • z) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    change φ s • z = s • z
    rw [hφ_eq hs]
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
    (I := 𝓘(Real, E))
    (g := rawExtMetric (I := I) g p hR hloc)
    heq.eq_of_nhds.symm heq.symm (hext_geo t ht)

omit [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem rawOrigin_launch
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {z : E} (hz : ‖z‖ < 3 * R / 4)
    {t : Real} (ht : t ∈ Set.Icc (0 : Real) 1) :
    rawExtLaunch (I := I) g p hR hloc (0 : E) z t = t • z := by
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun x : E ↦ TangentSpace 𝓘(Real, E) x) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (x : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) x) :=
    inferInstance
  letI (x : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) x) :=
    inferInstance
  letI : ∀ x : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) x) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun x : E ↦ TangentSpace 𝓘(Real, E) x) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro x v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (x : E) (v : TangentSpace 𝓘(Real, E) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner x v v)) :=
    fun x v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt x v
  obtain ⟨c, hc, hline⟩ :=
    rawOrigin_geo (I := I) g p hR hloc hdom hz
  let O : Set Real := Set.Ioo (-c) c
  let Γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt (0 : E) z
  have hΓ :
      IsGeodesicOn (I := 𝓘(Real, E)) gExt Γ O := by
    intro s _hs
    exact intrinsicGeodesic_isGeodesic
      (I := 𝓘(Real, E)) gExt hExt (0 : E) z s
  have hline' :
      IsGeodesicOn (I := 𝓘(Real, E)) gExt
        (fun s : Real => s • z) O := by
    simpa only [O] using hline
  have hΓcont : ContinuousOn Γ O :=
    (intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt (0 : E) z).continuous.continuousOn
  have hlineCont : ContinuousOn (fun s : Real => s • z) O :=
    (continuous_id.smul continuous_const).continuousOn
  have hvel :
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) Γ 0 (1 : Real) : E) =
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (fun s : Real => s • z) 0 (1 : Real) : E) := by
    have hleft :
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) Γ 0 (1 : Real) : E) = z := by
      simpa only [Γ] using
        intrinsicGeodesic_mfderiv_zero
          (I := 𝓘(Real, E)) gExt hExt (0 : E) z
    have hright :
        mfderiv 𝓘(Real, Real) 𝓘(Real, E)
          (fun s : Real => s • z) 0 (1 : Real) = z := by
      rw [mfderiv_eq_fderiv]
      have hfd :
          HasFDerivAt (fun s : Real => s • z)
            (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real) z) 0 := by
        simpa using (hasFDerivAt_id (0 : Real)).smul_const z
      rw [hfd.fderiv]
      change (ContinuousLinearMap.smulRight
        (1 : Real →L[Real] Real) z) (1 : Real) = z
      change (1 : Real) • z = z
      exact one_smul Real z
    rw [hleft, hright]
  have h0O : (0 : Real) ∈ O := by
    dsimp only [O]
    constructor <;> linarith
  have heq :=
    geo_eqOn_of_init (I := 𝓘(Real, E)) gExt
      (O := O) isOpen_Ioo isPreconnected_Ioo h0O hΓ hline'
      hΓcont hlineCont
      (by simp only [Γ, intrinsicGeodesic_zero, zero_smul])
      hvel
  have htO : t ∈ O := by
    dsimp only [O]
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  have hΓt : Γ t = t • z := heq htO
  simpa only [Γ, gExt, hExt, rawExtLaunch] using hΓt

private noncomputable def rawOriginHom {R : Real} :
    PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ where
  toPartialEquiv :=
    PartialEquiv.ofSet (Metric.ball (0 : E) (3 * R / 4))
  open_source := Metric.isOpen_ball
  open_target := Metric.isOpen_ball
  contMDiffOn_toFun := contMDiff_id.contMDiffOn
  contMDiffOn_invFun := contMDiff_id.contMDiffOn

omit [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [NeZero (Module.finrank Real E)] in
private theorem rawOrigin_inner
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (v w : E) :
    (rawExtMetric (I := I) g p hR hloc).inner (0 : E) v w =
      Inner.inner Real v w := by
  have hzero :
      (0 : E) ∈ Metric.closedBall (0 : E) (3 * R / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
    linarith
  rw [rawExt_inner (I := I) g p hR hloc hzero,
    rawPullMetric_inner]
  have h0 : normalFrame (I := I) g p (0 : E) ∈
      expDomain (I := I) g p := by
    simpa using zero_mem_expDomain (I := I) g p
  have hF0 : framedExpMap (I := I) g p (0 : E) = p := by
    rw [framedExpMap_apply, map_zero]
    exact expMap_zero (I := I) g p
  have hD0 :
      mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) (0 : E) =
        (normalFrame (I := I) g p).toContinuousLinearMap := by
    rw [mfderiv_framedMap (I := I) g p h0, map_zero]
    have hraw := mfderiv_expMap_at_zero (I := I) g p
    have hcomp := congrArg
      (fun D : E →L[Real] E =>
        D.comp (normalFrame (I := I) g p).toContinuousLinearMap) hraw
    simpa only [ContinuousLinearMap.id_comp] using hcomp
  rw [hF0, hD0]
  exact normalFrame_inner (I := I) g p v w

omit [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [NeZero (Module.finrank Real E)] in
private theorem rawOrigin_energy
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (z : E) :
    (1 / 2 : Real) *
        (rawExtMetric (I := I) g p hR hloc).inner (0 : E) z z =
      (1 / 2 : Real) * ‖z‖ ^ 2 := by
  rw [rawOrigin_inner (I := I) g p hR hloc,
    real_inner_self_eq_norm_sq]

omit [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- Squared raw normal coordinates are strictly convex on fenced extension geodesics. -/
theorem rawOrigin_strict
    (g : SmoothRiemannianMetric I M) (p : M) {R K L : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (framedExpMap (I := I) g p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (framedExpMap (I := I) g p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    {γ : Real → E} (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    {D : Set Real}
    (hgeo : IsGeodesicOn (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc) γ (interior D))
    (hD : Convex Real D)
    (hfence : ∀ t ∈ interior D, ‖γ t‖ < 3 * R / 4)
    (hbound : ∀ t ∈ interior D, ‖γ t‖ ≤ L)
    (hvel : ∀ t ∈ interior D,
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) ≠ 0) :
    StrictConvexOn Real D
      ((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ) := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (y : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) y) :=
    inferInstance
  letI (y : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) y) :=
    inferInstance
  letI : ∀ y : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) y) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun y : E ↦ TangentSpace 𝓘(Real, E) y) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro y v w; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  letI : T2Space M := gauss_t2Space_base I
  let hExt : ∀ (y : E) (v : TangentSpace 𝓘(Real, E) y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner y v v)) :=
    fun y v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt y v
  let hom : PartialDiffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ :=
    rawOriginHom (E := E) (R := R)
  let B : ExpInvBranch (I := 𝓘(Real, E)) gExt hExt (0 : E) :=
    { hom := hom
      hom_eq := by
        intro y hy
        have hy' : ‖y‖ < 3 * R / 4 := by
          simpa only [hom, rawOriginHom, PartialEquiv.ofSet_source,
            Metric.mem_ball, dist_zero_right] using hy
        simpa only [expMapIntrinsic_def, gExt, hExt, rawExtLaunch,
          one_smul] using
          rawOrigin_launch (I := I) g p hR hloc hdom hy'
            (t := (1 : Real)) ⟨zero_le_one, le_rfl⟩ }
  let f : E → Real := fun y => (1 / 2 : Real) * ‖y‖ ^ 2
  have henergy :
      branchEnergy (I := 𝓘(Real, E)) gExt B = f := by
    funext y
    change (1 / 2 : Real) * gExt.inner (0 : E) y y =
      (1 / 2 : Real) * ‖y‖ ^ 2
    simpa only [gExt] using rawOrigin_energy (I := I) g p hR hloc y
  have hf : ContMDiff 𝓘(Real, E) 𝓘(Real, Real) ∞ f :=
    (contDiff_const.mul (contDiff_norm_sq Real)).contMDiff
  have hcont : ContinuousOn (f ∘ γ) D :=
    (hf.continuous.comp hγ.continuous).continuousOn
  refine strictConvex_geo_on (I := 𝓘(Real, E)) gExt
    (U := Set.univ) isOpen_univ hf.contMDiffOn hγ hgeo hD hcont
    (fun _ _ => Set.mem_univ _) ?_
  intro t ht
  have hBsrc : (γ t : E) ∈ B.hom.source := by
    simpa only [B, hom, rawOriginHom, PartialEquiv.ofSet_source,
      Metric.mem_ball, dist_zero_right] using hfence t ht
  have hradfence :
      ∀ s ∈ Set.Icc (0 : Real) 1,
        ‖rawExtLaunch (I := I) g p hR hloc (0 : E) (γ t) s‖ <
          3 * R / 4 := by
    intro s hs
    have hsAbs : |s| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    calc
      ‖rawExtLaunch (I := I) g p hR hloc (0 : E) (γ t) s‖ =
          ‖s • γ t‖ := congrArg norm
            (rawOrigin_launch (I := I) g p hR hloc hdom (hfence t ht) hs)
      _ = |s| * ‖γ t‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖γ t‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hsAbs (norm_nonneg (γ t))
      _ < 3 * R / 4 := hfence t ht
  have hspeed : Real.sqrt (gExt.inner (0 : E) (γ t) (γ t)) ≤ L := by
    rw [show gExt.inner (0 : E) (γ t) (γ t) =
        Inner.inner Real (γ t) (γ t) by
      simpa only [gExt] using
        rawOrigin_inner (I := I) g p hR hloc (γ t) (γ t),
      real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg (γ t))]
    exact hbound t ht
  have hlaunch :
      expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (0 : E) (γ t) = γ t := by
    simpa only [expMapIntrinsic_def, gExt, hExt, rawExtLaunch,
      one_smul] using
      rawOrigin_launch (I := I) g p hR hloc hdom (hfence t ht)
        (t := (1 : Real)) ⟨zero_le_one, le_rfl⟩
  have hpos :
      0 < hessFun (I := 𝓘(Real, E)) gExt
        (branchEnergy (I := 𝓘(Real, E)) gExt B)
        (expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt (0 : E) (γ t))
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) := by
    exact rawBranch_hess_pos (I := I) g p hR hloc hK hRm hsmall (γ t)
      hradfence hspeed B hBsrc (hvel t ht)
  rw [henergy, hlaunch] at hpos
  exact hpos

/-- A short raw complete-extension launch with core endpoints remains in the
raw core. -/
theorem rawExt_edge_core
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K L : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K)
    (hRm : ∀ z : E, ‖z‖ < 3 * R / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p z) 4
        (Geometry.Curvature.metricRm04At (I := I) (M := M) g
          (framedExpMap (I := I) g p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (h2aL : 2 * a < L) (hbudget : a + L < 3 * R / 4)
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a)
    (v : TangentSpace 𝓘(Real, E) x)
    (hv : Real.sqrt ((rawExtMetric (I := I) g p hR hloc).inner x v v) ≤ L)
    (hend : rawExtLaunch (I := I) g p hR hloc x v 1 = y) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖rawExtLaunch (I := I) g p hR hloc x v t‖ ≤ a := by
  classical
  let gExt := rawExtMetric (I := I) g p hR hloc
  letI : RiemannianBundle
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.toRiemannianMetric⟩
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI (z : E) : NormedSpace Real (TangentSpace 𝓘(Real, E) z) :=
    inferInstance
  letI : ∀ z : E, ENormSMulClass Real (TangentSpace 𝓘(Real, E) z) :=
    fun _ => inferInstance
  letI : IsContinuousRiemannianBundle E
      (fun z : E => TangentSpace 𝓘(Real, E) z) :=
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w u; rfl⟩
  letI : PseudoEMetricSpace E :=
    PseudoEMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x v
  have hγ0 : γ 0 = x :=
    intrinsicGeodesic_zero (I := 𝓘(Real, E)) gExt hExt x v
  have hγ1 : γ 1 = y := by
    simpa only [γ, gExt, hExt, rawExtLaunch] using hend
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  intro t ht
  by_cases hv0 : v = 0
  · have hdist :=
      intrinsicGeodesic_riemannianEDist_le
        (I := 𝓘(Real, E)) gExt hExt x v (s := 0) (t := t) ht.1
    have hspeed0 : Real.sqrt (gExt.inner x v v) = 0 := by
      rw [hv0]
      simp
    rw [hspeed0, zero_mul, ENNReal.ofReal_zero] at hdist
    have heq : γ 0 = γ t :=
      riemannianEDist_eq_zero_imp_eq
        (I := 𝓘(Real, E)) (γ 0) (γ t)
        (le_antisymm (by simpa only [γ, sub_zero] using hdist) bot_le)
    rw [hγ0] at heq
    simpa only [γ, gExt, hExt, rawExtLaunch, ← heq] using hx
  · have hfence :
        ∀ s ∈ Set.Icc (0 : Real) 1, ‖γ s‖ < 3 * R / 4 := by
      simpa only [γ, gExt, hExt, rawExtLaunch] using
        rawExt_short_fenced (I := I) g hEnorm p hR hloc hdom hx v hv hbudget
    have hscale :
        ∀ s ∈ Set.Icc (0 : Real) 1, ‖γ s‖ ≤ a + L / 2 := by
      simpa only [γ, gExt, hExt, rawExtLaunch] using
        rawExt_scale (I := I) g hEnorm p hR hloc hdom hx hy v hv hbudget hend
    have hstrict :
        StrictConvexOn Real (Set.Icc (0 : Real) 1)
          ((fun z : E => (1 / 2 : Real) * ‖z‖ ^ 2) ∘ γ) :=
      rawOrigin_strict (I := I) g p hR hloc hdom hK hRm hsmall
        (intrinsicGeodesic_contMDiff
          (I := 𝓘(Real, E)) gExt hExt x v)
        (D := Set.Icc (0 : Real) 1)
        (by
          simpa only [interior_Icc] using
            (intrinsicGeodesic_isGeodesic
              (I := 𝓘(Real, E)) gExt hExt x v).isGeodesicOn
                (Set.Ioo (0 : Real) 1))
        (convex_Icc (0 : Real) 1)
        (fun s hs => by
          have hs' : s ∈ Set.Ioo (0 : Real) 1 := by
            simpa only [interior_Icc] using hs
          exact hfence s ⟨hs'.1.le, hs'.2.le⟩)
        (fun s hs => by
          have hs' : s ∈ Set.Ioo (0 : Real) 1 := by
            simpa only [interior_Icc] using hs
          have hsBound := hscale s ⟨hs'.1.le, hs'.2.le⟩
          linarith)
        (fun s _ =>
          intrGeo_vel_ne
            (I := 𝓘(Real, E)) gExt hExt x v hv0 s)
    have hjensen :=
      hstrict.convexOn.2
        (Set.left_mem_Icc.mpr zero_le_one)
        (Set.right_mem_Icc.mpr zero_le_one)
        (sub_nonneg.mpr ht.2) ht.1 (by ring : (1 - t) + t = 1)
    have henergy :
        (1 / 2 : Real) * ‖γ t‖ ^ 2 ≤
          (1 - t) * ((1 / 2 : Real) * ‖γ 0‖ ^ 2) +
            t * ((1 / 2 : Real) * ‖γ 1‖ ^ 2) := by
      simpa only [Function.comp_apply, smul_eq_mul, mul_zero, zero_add,
        mul_one] using hjensen
    rw [hγ0, hγ1] at henergy
    have hxSq : ‖x‖ ^ 2 ≤ a ^ 2 :=
      (sq_le_sq₀ (norm_nonneg x) ha).2 hx
    have hySq : ‖y‖ ^ 2 ≤ a ^ 2 :=
      (sq_le_sq₀ (norm_nonneg y) ha).2 hy
    have hxt :
        (1 - t) * ‖x‖ ^ 2 ≤ (1 - t) * a ^ 2 :=
      mul_le_mul_of_nonneg_left hxSq (sub_nonneg.mpr ht.2)
    have hyt : t * ‖y‖ ^ 2 ≤ t * a ^ 2 :=
      mul_le_mul_of_nonneg_left hySq ht.1
    have hγSq : ‖γ t‖ ^ 2 ≤ a ^ 2 := by
      nlinarith
    have hnorm : ‖γ t‖ ≤ a :=
      (sq_le_sq₀ (norm_nonneg (γ t)) ha).1 hγSq
    simpa only [γ, gExt, hExt, rawExtLaunch] using hnorm

omit [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- A nonconstant raw extension geodesic cannot return to its midpoint while
remaining in the strict-convexity core. -/
theorem rawOrigin_no_return
    (g : SmoothRiemannianMetric I M)
    (p : M) {R K L T : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K)
    (hRm : ∀ z : E, ‖z‖ < 3 * R / 4 →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (framedExpMap (I := I) g p z) 4
        (Geometry.Curvature.metricRm04At (I := I) (M := M) g
          (framedExpMap (I := I) g p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (hT : 0 < T)
    {γ : Real → E} (hγ : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ)
    (hgeo : IsGeodesicOn (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc) γ
      (Set.Ioo (0 : Real) (2 * T)))
    (hfence : ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γ t‖ < 3 * R / 4)
    (hbound : ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γ t‖ ≤ L)
    (hvel : ∀ t ∈ Set.Ioo (0 : Real) (2 * T),
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ t (1 : Real) : E) ≠ 0)
    (h0T : γ 0 = γ T) (hT2 : γ T = γ (2 * T)) :
    False := by
  have hstrict :=
    rawOrigin_strict (I := I) g p hR hloc hdom hK hRm hsmall
      hγ (D := Set.Icc (0 : Real) (2 * T))
      (by simpa only [interior_Icc] using hgeo)
      (convex_Icc (0 : Real) (2 * T))
      (by simpa only [interior_Icc] using hfence)
      (by simpa only [interior_Icc] using hbound)
      (by simpa only [interior_Icc] using hvel)
  have h2T : 0 < 2 * T := mul_pos (by norm_num) hT
  have hlt :
      (((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ)
          ((1 / 2 : Real) • (0 : Real) +
            (1 / 2 : Real) • (2 * T))) <
        (1 / 2 : Real) •
          (((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ) 0) +
          (1 / 2 : Real) •
            (((fun y : E => (1 / 2 : Real) * ‖y‖ ^ 2) ∘ γ) (2 * T)) := by
    exact hstrict.2
      ⟨le_rfl, h2T.le⟩ ⟨h2T.le, le_rfl⟩
      (ne_of_lt h2T) (by norm_num) (by norm_num) (by norm_num)
  have hmid :
      (1 / 2 : Real) • (0 : Real) +
          (1 / 2 : Real) • (2 * T) = T := by
    simp only [smul_eq_mul]
    ring
  rw [hmid] at hlt
  simp only [Function.comp_apply, smul_eq_mul] at hlt
  rw [h0T, ← hT2] at hlt
  linarith

private def rawShortBigons
    (F : E × E → E) (ell : E × E → Real) (a L : Real) :
    Set (E × E × E) :=
  {z |
    ‖z.1‖ ≤ a ∧
    ‖F (z.1, z.2.1)‖ ≤ a ∧
    F (z.1, z.2.1) = F (z.1, z.2.2) ∧
    ell (z.1, z.2.1) ≤ L ∧
    ell (z.1, z.2.2) ≤ L ∧
    z.2.1 ≠ z.2.2}

omit [NeZero (Module.finrank Real E)] in
private theorem rawShort_compact
    (F : E × E → E) (ell : E × E → Real) (a L B : Real)
    (hF : Continuous F) (hell : Continuous ell)
    (hdiag :
      ∀ x u : E, ‖x‖ ≤ a → ell (x, u) ≤ L →
        ∃ U ∈ 𝓝 (x, u),
          Set.InjOn (fun z : E × E => (F z, z.1)) U)
    (hbound :
      ∀ z ∈ rawShortBigons F ell a L,
        ‖z.2.1‖ ≤ B ∧ ‖z.2.2‖ ≤ B) :
    IsCompact (rawShortBigons F ell a L) := by
  let pu : E × E × E → E × E := fun z => (z.1, z.2.1)
  let pv : E × E × E → E × E := fun z => (z.1, z.2.2)
  let Raw : Set (E × E × E) :=
    {z |
      ‖z.1‖ ≤ a ∧
      ‖F (pu z)‖ ≤ a ∧
      F (pu z) = F (pv z) ∧
      ell (pu z) ≤ L ∧
      ell (pv z) ≤ L}
  have hpu : Continuous pu :=
    continuous_fst.prodMk continuous_snd.fst
  have hpv : Continuous pv :=
    continuous_fst.prodMk continuous_snd.snd
  have hRawClosed : IsClosed Raw := by
    have hxClosed : IsClosed {z : E × E × E | ‖z.1‖ ≤ a} :=
      isClosed_le (continuous_norm.comp continuous_fst) continuous_const
    have hyClosed : IsClosed {z : E × E × E | ‖F (pu z)‖ ≤ a} :=
      isClosed_le (continuous_norm.comp (hF.comp hpu)) continuous_const
    have heqClosed : IsClosed {z : E × E × E | F (pu z) = F (pv z)} :=
      isClosed_eq (hF.comp hpu) (hF.comp hpv)
    have huClosed : IsClosed {z : E × E × E | ell (pu z) ≤ L} :=
      isClosed_le (hell.comp hpu) continuous_const
    have hvClosed : IsClosed {z : E × E × E | ell (pv z) ≤ L} :=
      isClosed_le (hell.comp hpv) continuous_const
    simpa only [Raw, Set.mem_setOf_eq] using
      hxClosed.inter
        (hyClosed.inter
          (heqClosed.inter (huClosed.inter hvClosed)))
  have hBadRaw :
      rawShortBigons F ell a L =
        Raw ∩ {z : E × E × E | z.2.1 ≠ z.2.2} := by
    ext z
    simp only [rawShortBigons, Raw, pu, pv, Set.mem_setOf_eq,
      Set.mem_inter_iff]
    tauto
  have hBadClosed : IsClosed (rawShortBigons F ell a L) := by
    rw [hBadRaw, ← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    change z ∉ Raw ∩ {w : E × E × E | w.2.1 ≠ w.2.2} at hz
    by_cases hzRaw : z ∈ Raw
    · have huv : z.2.1 = z.2.2 := by
        by_contra hne
        exact hz ⟨hzRaw, hne⟩
      obtain ⟨U, hU, hUinj⟩ :=
        hdiag z.1 z.2.1 hzRaw.1 hzRaw.2.2.2.1
      have hUu : U ∈ 𝓝 (pu z) := by
        simpa only [pu] using hU
      have hUv : U ∈ 𝓝 (pv z) := by
        simpa only [pu, pv, huv] using hU
      have hV :
          {w : E × E × E | pu w ∈ U ∧ pv w ∈ U} ∈ 𝓝 z :=
        Filter.inter_mem (hpu.continuousAt hUu) (hpv.continuousAt hUv)
      refine Filter.mem_of_superset hV ?_
      intro w hw
      change w ∉ Raw ∩ {r : E × E × E | r.2.1 ≠ r.2.2}
      intro hwBad
      have hpairs : pu w = pv w := by
        apply hUinj hw.1 hw.2
        apply Prod.ext
        · exact hwBad.1.2.2.1
        · rfl
      exact hwBad.2 (congrArg Prod.snd hpairs)
    · have hRawCompl : Rawᶜ ∈ 𝓝 z :=
        hRawClosed.isOpen_compl.mem_nhds hzRaw
      refine Filter.mem_of_superset hRawCompl ?_
      intro w hw
      change w ∉ Raw ∩ {r : E × E × E | r.2.1 ≠ r.2.2}
      exact fun h => hw h.1
  let Box : Set (E × E × E) :=
    Metric.closedBall (0 : E) a ×ˢ
      (Metric.closedBall (0 : E) B ×ˢ Metric.closedBall (0 : E) B)
  have hBox : IsCompact Box :=
    (isCompact_closedBall (0 : E) a).prod
      ((isCompact_closedBall (0 : E) B).prod
        (isCompact_closedBall (0 : E) B))
  apply hBox.of_isClosed_subset hBadClosed
  intro z hz
  have hb := hbound z hz
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hb.1
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hb.2

omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] in
private theorem rawPeriodic_core
    {γu γv : Real → E} {a c d T : Real}
    (hTdef : T = 1 + d) (hcPos : 0 < c) (hcd : c * d = 1)
    (hjoin : ∀ s : Real, γu (s + 1) = γv (1 - c * s))
    (hperiod : ∀ s : Real, γu (s + T) = γu s)
    (hcoreU : ∀ t ∈ Set.Icc (0 : Real) 1, ‖γu t‖ ≤ a)
    (hcoreV : ∀ t ∈ Set.Icc (0 : Real) 1, ‖γv t‖ ≤ a) :
    ∀ t ∈ Set.Ioo (0 : Real) (2 * T), ‖γu t‖ ≤ a := by
  have honeCore :
      ∀ t ∈ Set.Icc (0 : Real) T, ‖γu t‖ ≤ a := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · exact hcoreU t ⟨ht.1, ht1⟩
    · have hs0 : 0 ≤ t - 1 := sub_nonneg.mpr (le_of_not_ge ht1)
      have hsd : t - 1 ≤ d := by
        have ht' : t ≤ 1 + d := by
          simpa only [hTdef] using ht.2
        exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using ht')
      have hcs : 0 ≤ c * (t - 1) :=
        mul_nonneg hcPos.le hs0
      have hcs1 : c * (t - 1) ≤ 1 := by
        calc
          c * (t - 1) ≤ c * d :=
            mul_le_mul_of_nonneg_left hsd hcPos.le
          _ = 1 := hcd
      have hj := hjoin (t - 1)
      have htime : (t - 1) + 1 = t := by ring
      rw [htime] at hj
      rw [hj]
      exact hcoreV (1 - c * (t - 1))
        ⟨sub_nonneg.mpr hcs1, sub_le_self 1 hcs⟩
  intro t ht
  by_cases htT : t ≤ T
  · exact honeCore t ⟨ht.1.le, htT⟩
  · have hred : t - T ∈ Set.Icc (0 : Real) T := by
      constructor
      · exact sub_nonneg.mpr (le_of_not_ge htT)
      · apply sub_le_iff_le_add.mpr
        simpa only [two_mul] using ht.2.le
    have hp := hperiod (t - T)
    have heq : (t - T) + T = t := by ring
    rw [heq] at hp
    rw [hp]
    exact honeCore (t - T) hred

private theorem rawMidpoint_loop
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K L : Real} (hR : 0 < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (framedExpMap (I := I) g p)
        (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (framedExpMap (I := I) g p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (framedExpMap (I := I) g p z))) ≤ K)
    (hsmall : K * L ^ 2 < (Real.pi / 2) ^ 2)
    (h2aL : 2 * a < L) (hbudget : a + L < 3 * R / 4) :
    let gExt := rawExtMetric (I := I) g p hR hloc
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
      ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
    letI : EMetricSpace E :=
      EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
    letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
    letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
    letI : CompleteSpace E :=
      (rawExt_complete (I := I) g p hR hloc).complete
    let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
      fun z w =>
        tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := 𝓘(Real, E)) gExt z w
    let F : E × E → E := fun z =>
      expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
    let ell : E × E → Real := fun z =>
      Real.sqrt (gExt.inner z.1 z.2 z.2)
    let total : E × E × E → Real := fun z =>
      ell (z.1, z.2.1) + ell (z.1, z.2.2)
    ∀ (z₀ : E × E × E),
      IsMinOn total (rawShortBigons F ell a L) z₀ →
      total z₀ < 2 * L →
      ∀ (x₀ q₀ : E), ‖x₀‖ ≤ a →
        ell (x₀, q₀) ≤ L → q₀ ≠ 0 →
        F (x₀, q₀) = x₀ → total z₀ = ell (x₀, q₀) →
        ∃ z₁ : E × E × E,
          z₁ ∈ rawShortBigons F ell a L ∧
          IsMinOn total (rawShortBigons F ell a L) z₁ ∧
          z₁.2.1 ≠ 0 ∧ z₁.2.2 ≠ 0 ∧
          ell (z₁.1, z₁.2.1) < L ∧
          ell (z₁.1, z₁.2.2) < L := by
  dsimp only
  let gExt := rawExtMetric (I := I) g p hR hloc
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
    ⟨gExt.inner, gExt.contMDiff.continuous, by intro z w r; rfl⟩
  letI : EMetricSpace E :=
    EMetricSpace.ofRiemannianMetric 𝓘(Real, E) E
  letI : IsRiemannianManifold 𝓘(Real, E) E := ⟨fun _ _ => rfl⟩
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (w : TangentSpace 𝓘(Real, E) z),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z w w)) :=
    fun z w =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z w
  let F : E × E → E := fun z =>
    expMapIntrinsic (I := 𝓘(Real, E)) gExt hExt z.1 z.2
  let ell : E × E → Real := fun z =>
    Real.sqrt (gExt.inner z.1 z.2 z.2)
  let total : E × E × E → Real := fun z =>
    ell (z.1, z.2.1) + ell (z.1, z.2.2)
  intro z₀ hmin htotalLt x₀ q₀ hx₀ hqL hqne hloop htot
  let γ : Real → E :=
    intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt x₀ q₀
  let m : E := γ (1 / 2)
  let w : E :=
    mfderiv 𝓘(Real, Real) 𝓘(Real, E) γ (1 / 2) (1 : Real)
  have hγ0 : γ 0 = x₀ :=
    intrinsicGeodesic_zero
      (I := 𝓘(Real, E)) gExt hExt x₀ q₀
  have hγ1 : γ 1 = x₀ := by
    simpa only [γ, F, expMapIntrinsic_def] using hloop
  have hm : ‖m‖ ≤ a := by
    apply rawExt_edge_core
      (I := I) g hEnorm p hR hloc hdom hK hRm hsmall h2aL hbudget
      hx₀ hx₀ q₀
    · simpa only [ell, gExt] using hqL
    · simpa only [γ, m, gExt, hExt, rawExtLaunch] using hγ1
    · norm_num
  have hcont :
      (fun s : Real => γ (s + 1 / 2)) =
        intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt m w := by
    simpa only [γ, m, w] using
      intrinsicGeodesic_continuation
        (I := 𝓘(Real, E)) gExt hExt x₀ q₀ (1 / 2)
  have hplus : F (m, (1 / 2 : Real) • w) = x₀ := by
    change
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
        m ((1 / 2 : Real) • w) 1 = x₀
    have hscale :
        intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
            m ((1 / 2 : Real) • w) 1 =
          intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt m w (1 / 2) :=
      intrinsicGeodesic_smul
        (I := 𝓘(Real, E)) gExt hExt m w (1 / 2)
    rw [hscale]
    rw [← congrFun hcont (1 / 2)]
    norm_num
    exact hγ1
  have hminus : F (m, (-1 / 2 : Real) • w) = x₀ := by
    change
      intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
        m ((-1 / 2 : Real) • w) 1 = x₀
    have hscale :
        intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt
            m ((-1 / 2 : Real) • w) 1 =
          intrinsicGeodesic (I := 𝓘(Real, E)) gExt hExt m w (-1 / 2) :=
      intrinsicGeodesic_smul
        (I := 𝓘(Real, E)) gExt hExt m w (-1 / 2)
    rw [hscale]
    rw [← congrFun hcont (-1 / 2)]
    norm_num
    exact hγ0
  have hspeed :
      gExt.inner m w w = gExt.inner x₀ q₀ q₀ := by
    simpa only [γ, m, w] using
      intrinsicGeodesic_speedSq_eq
        (I := 𝓘(Real, E)) gExt hExt x₀ q₀ (1 / 2)
  have hellPlus :
      ell (m, (1 / 2 : Real) • w) =
        (1 / 2 : Real) * ell (x₀, q₀) := by
    simp only [ell]
    have hscale :
        Real.sqrt
            (gExt.inner m ((1 / 2 : Real) • w)
              ((1 / 2 : Real) • w)) =
          (1 / 2 : Real) * Real.sqrt (gExt.inner m w w) :=
      sqrt_gInner_smul_self
        (I := 𝓘(Real, E)) gExt m (by norm_num) w
    rw [hscale, hspeed]
  have hellMinus :
      ell (m, (-1 / 2 : Real) • w) =
        (1 / 2 : Real) * ell (x₀, q₀) := by
    simp only [ell]
    rw [show (-1 / 2 : Real) • w =
        (1 / 2 : Real) • (-w) by module]
    have hscale :
        Real.sqrt
            (gExt.inner m ((1 / 2 : Real) • (-w))
              ((1 / 2 : Real) • (-w))) =
          (1 / 2 : Real) * Real.sqrt (gExt.inner m (-w) (-w)) :=
      sqrt_gInner_smul_self
        (I := 𝓘(Real, E)) gExt m (by norm_num) (-w)
    have hneg : gExt.inner m (-w) (-w) = gExt.inner m w w := by
      have h :=
        gInner_smul_self
          (I := 𝓘(Real, E)) gExt m (-1 : Real) w
      simpa only [neg_one_smul, neg_sq, one_pow, one_mul] using h
    rw [hscale, hneg, hspeed]
  have hwne : w ≠ 0 := by
    simpa only [γ, w] using
      intrGeo_vel_ne
        (I := 𝓘(Real, E)) gExt hExt x₀ q₀ hqne (1 / 2)
  have hplusNe : (1 / 2 : Real) • w ≠ 0 :=
    smul_ne_zero (by norm_num) hwne
  have hminusNe : (-1 / 2 : Real) • w ≠ 0 :=
    smul_ne_zero (by norm_num) hwne
  let z₁ : E × E × E :=
    (m, ((1 / 2 : Real) • w, (-1 / 2 : Real) • w))
  have hz₁ : z₁ ∈ rawShortBigons F ell a L := by
    change
      ‖m‖ ≤ a ∧
      ‖F (m, (1 / 2 : Real) • w)‖ ≤ a ∧
      F (m, (1 / 2 : Real) • w) = F (m, (-1 / 2 : Real) • w) ∧
      ell (m, (1 / 2 : Real) • w) ≤ L ∧
      ell (m, (-1 / 2 : Real) • w) ≤ L ∧
      (1 / 2 : Real) • w ≠ (-1 / 2 : Real) • w
    refine ⟨hm, ?_, hplus.trans hminus.symm, ?_, ?_, ?_⟩
    · rw [hplus]
      exact hx₀
    · rw [hellPlus]
      have hqnonneg : 0 ≤ ell (x₀, q₀) := Real.sqrt_nonneg _
      exact (mul_le_of_le_one_left hqnonneg (by norm_num)).trans hqL
    · rw [hellMinus]
      have hqnonneg : 0 ≤ ell (x₀, q₀) := Real.sqrt_nonneg _
      exact (mul_le_of_le_one_left hqnonneg (by norm_num)).trans hqL
    · intro heq
      let q : E := (1 / 2 : Real) • w
      have hqneg : q = -q := by
        calc
          q = (-1 / 2 : Real) • w := heq
          _ = -q := by simp only [q]; module
      have htwo : (2 : Real) • q = 0 := by
        rw [two_smul]
        nth_rewrite 1 [hqneg]
        exact neg_add_cancel q
      have hq0 : q = 0 :=
        (smul_eq_zero.mp htwo).resolve_left (by norm_num)
      exact hplusNe (by simpa only [q] using hq0)
  have htotal₁ : total z₁ = total z₀ := by
    calc
      total z₁ =
          ell (m, (1 / 2 : Real) • w) +
            ell (m, (-1 / 2 : Real) • w) := by
              rfl
      _ = ell (x₀, q₀) := by
        rw [hellPlus, hellMinus]
        ring
      _ = total z₀ := htot.symm
  have hmin₁ : IsMinOn total (rawShortBigons F ell a L) z₁ := by
    apply isMinOn_iff.mpr
    intro z hz
    rw [htotal₁]
    exact (isMinOn_iff.mp hmin) z hz
  have hqLt : ell (x₀, q₀) < 2 * L := by
    have hqLtRaw := htotalLt
    rw [htot] at hqLtRaw
    simpa only [ell, gExt] using hqLtRaw
  have hplusLt : ell (m, (1 / 2 : Real) • w) < L := by
    rw [hellPlus]
    calc
      (1 / 2 : Real) * ell (x₀, q₀) < (1 / 2 : Real) * (2 * L) :=
        mul_lt_mul_of_pos_left hqLt (by norm_num)
      _ = L := by ring
  have hminusLt : ell (m, (-1 / 2 : Real) • w) < L := by
    rw [hellMinus]
    calc
      (1 / 2 : Real) * ell (x₀, q₀) < (1 / 2 : Real) * (2 * L) :=
        mul_lt_mul_of_pos_left hqLt (by norm_num)
      _ = L := by ring
  exact
    ⟨z₁, hz₁, hmin₁,
      by simpa only [z₁] using hplusNe,
      by simpa only [z₁] using hminusNe,
      by simpa only [z₁] using hplusLt,
      by simpa only [z₁] using hminusLt⟩

end Fence

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
