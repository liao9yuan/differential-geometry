import DifferentialGeometry.Geometry.Comparison.CGTRawExtDistance
import DifferentialGeometry.Geometry.Comparison.CGTRawCore
import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Analysis.ODE.TubeStability

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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

/-- A minimizing join for the complete raw pullback extension. In model
dimension zero it is the unique constant curve. -/
noncomputable def rawExtJoin
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (x y : E) : Real → E := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · exact fun _ => x
  · letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
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
    exact minJoin (I := 𝓘(Real, E)) gExt hExt x y

/-- In positive model dimension, `rawExtJoin` is the canonical minimizing
geodesic for the complete raw extension. -/
theorem rawExtJoin_eq_min
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdim : Module.finrank Real E ≠ 0) (x y : E) :
    rawExtJoin (I := I) g p hR hloc x y =
      letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
      let gExt := rawExtMetric (I := I) g p hR hloc
      letI : RiemannianBundle
          (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
        ⟨gExt.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E
          (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
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
      minJoin (I := 𝓘(Real, E)) gExt hExt x y := by
  classical
  letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
  simp only [rawExtJoin, dif_neg hdim]

/-- The complete-extension minimizing join starts at its first endpoint. -/
@[simp] theorem rawExtJoin_zero
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (x y : E) :
    rawExtJoin (I := I) g p hR hloc x y 0 = x := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · simp only [rawExtJoin, dif_pos hdim]
  · letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
    simp only [rawExtJoin, dif_neg hdim, minJoin_zero]

/-- The complete-extension minimizing join ends at its second endpoint. -/
@[simp] theorem rawExtJoin_one
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (x y : E) :
    rawExtJoin (I := I) g p hR hloc x y 1 = y := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · letI : Subsingleton E := Module.finrank_zero_iff.mp hdim
    simp only [rawExtJoin, dif_pos hdim]
    exact Subsingleton.elim x y
  · letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
    simp only [rawExtJoin, dif_neg hdim, minJoin_one]

/-- The complete-extension minimizing join is smooth. -/
theorem rawExtJoin_smooth
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (x y : E) :
    ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞
      (rawExtJoin (I := I) g p hR hloc x y) := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · have hjoin :
        rawExtJoin (I := I) g p hR hloc x y = fun _ : Real => x := by
      simp only [rawExtJoin, dif_pos hdim]
    rw [hjoin]
    exact contMDiff_const
  · letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
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
    simpa only [rawExtJoin, dif_neg hdim, gExt] using
      intrinsicGeodesic_contMDiff
        (I := 𝓘(Real, E)) gExt hExt x
          (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)

/-- The complete-extension minimizing join is a geodesic of the extended
metric. -/
theorem rawExtJoin_geo
    (g : SmoothRiemannianMetric I M) (p : M) {R : Real} (hR : 0 < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (x y : E) :
    IsGeodesic (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc)
      (rawExtJoin (I := I) g p hR hloc x y) := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · have hjoin :
        rawExtJoin (I := I) g p hR hloc x y = fun _ : Real => x := by
      simp only [rawExtJoin, dif_pos hdim]
    rw [hjoin]
    exact isGeodesic_const (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc) x
  · letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
    let gExt := rawExtMetric (I := I) g p hR hloc
    letI : RiemannianBundle
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
      ⟨gExt.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : E ↦ TangentSpace 𝓘(Real, E) z) :=
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
    simpa only [rawExtJoin, dif_neg hdim, gExt, minJoin] using
      intrinsicGeodesic_isGeodesic
        (I := 𝓘(Real, E)) gExt hExt x
          (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)

section Fence

variable [I.Boundaryless] [T2Space (TangentBundle I M)]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem rawExtJoin_budget_of_ne
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a L : Real} (hR : 0 < R)
    (hdim : ¬ Module.finrank Real E = 0)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {x y : E} (hx : ‖x‖ ≤ a) (hL : 0 ≤ L)
    (hdist : riemannianEDistOf (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc) x y ≤ ENNReal.ofReal L)
    (hbudget : a + L < 3 * R / 4) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖rawExtJoin (I := I) g p hR hloc x y t‖ < 3 * R / 4 := by
  classical
  letI : NeZero (Module.finrank Real E) := ⟨hdim⟩
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
  letI : UniformSpace E := PseudoEMetricSpace.toUniformSpace
  letI : CompleteSpace E :=
    (rawExt_complete (I := I) g p hR hloc).complete
  let hExt : ∀ (z : E) (v : TangentSpace 𝓘(Real, E) z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gExt.inner z v v)) :=
    fun z v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := 𝓘(Real, E)) gExt z v
  let γ : Real → E := minJoin (I := 𝓘(Real, E)) gExt hExt x y
  have hγinf : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞ γ := by
    exact intrinsicGeodesic_contMDiff
      (I := 𝓘(Real, E)) gExt hExt x
        (minimizingVec (I := 𝓘(Real, E)) gExt hExt x y)
  have hγcont : Continuous γ := hγinf.continuous
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have haB : a < 3 * R / 4 := by linarith
  have haInner : a ≤ 3 * R / 4 := haB.le
  have hcore : 3 * R / 4 < R := by linarith
  have hdist' : Manifold.riemannianEDist 𝓘(Real, E) x y ≤
      ENNReal.ofReal L := by
    simpa only [gExt, riemannianEDistOf] using hdist
  have hdist_top : Manifold.riemannianEDist 𝓘(Real, E) x y ≠
      (⊤ : ENNReal) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdist'
  have hfull : Manifold.pathELength 𝓘(Real, E) γ 0 1 =
      ENNReal.ofReal ((Manifold.riemannianEDist 𝓘(Real, E) x y).toReal) := by
    simpa only [γ] using
      (minJoin_pathLen (I := 𝓘(Real, E)) gExt hExt x y)
  intro t ht
  by_contra hnot
  have hcross : 3 * R / 4 ≤ ‖γ t‖ := by
    simpa only [γ, rawExtJoin, dif_neg hdim] using (not_lt.mp hnot)
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
  have hprefix : Manifold.pathELength 𝓘(Real, E) γ 0 τ ≤
      ENNReal.ofReal L := by
    calc
      Manifold.pathELength 𝓘(Real, E) γ 0 τ ≤
          Manifold.pathELength 𝓘(Real, E) γ 0 1 :=
        Manifold.pathELength_mono le_rfl hτ.2
      _ = ENNReal.ofReal
          ((Manifold.riemannianEDist 𝓘(Real, E) x y).toReal) := hfull
      _ = Manifold.riemannianEDist 𝓘(Real, E) x y :=
        ENNReal.ofReal_toReal hdist_top
      _ ≤ ENNReal.ofReal L := hdist'
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

private theorem rawExtJoin_budget
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
    {x y : E} (hx : ‖x‖ ≤ a) (hL : 0 ≤ L)
    (hdist : riemannianEDistOf (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc) x y ≤ ENNReal.ofReal L)
    (hbudget : a + L < 3 * R / 4) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖rawExtJoin (I := I) g p hR hloc x y t‖ < 3 * R / 4 := by
  classical
  by_cases hdim : Module.finrank Real E = 0
  · intro t ht
    have haB : a < 3 * R / 4 := by linarith
    simpa only [rawExtJoin, dif_pos hdim] using hx.trans_lt haB
  · exact rawExtJoin_budget_of_ne (I := I) g hEnorm p hR hdim hloc hdom
      hx hL hdist hbudget

/-- A complete-extension minimizing join stays in the raw agreement core when
the raw exponential domain covers every radial segment of the pullback ball. -/
theorem rawExtJoin_fenced
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) (Metric.ball (0 : E) R))
    (hdom : ∀ w : rawPullBall (E := E) R,
      ∀ s ∈ Set.Icc (0 : Real) 1,
        (show TangentSpace I p from
          s • normalFrame (I := I) g p (w : E)) ∈ expDomain (I := I) g p)
    {x y : E} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ∀ t ∈ Set.Icc (0 : Real) 1,
      ‖rawExtJoin (I := I) g p hR hloc x y t‖ < 3 * R / 4 := by
  have ha : 0 ≤ a := (norm_nonneg x).trans hx
  have haInner : a ≤ 3 * R / 4 := by linarith
  have hxBall : x ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hyBall : y ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hdist : riemannianEDistOf (I := 𝓘(Real, E))
      (rawExtMetric (I := I) g p hR hloc) x y ≤ ENNReal.ofReal (2 * a) :=
    rawExt_edist_le (I := I) g hEnorm p hR hloc hx hy haInner
      (hdom ⟨x, hxBall⟩) (hdom ⟨y, hyBall⟩)
  exact rawExtJoin_budget (I := I) g hEnorm p hR hloc hdom hx
    (mul_nonneg (by norm_num) ha) hdist (by linarith)

end Fence

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
