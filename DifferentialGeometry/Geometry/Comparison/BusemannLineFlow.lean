import DifferentialGeometry.Analysis.ODE.CompleteFlow
import DifferentialGeometry.Geometry.Comparison.HalfSqDistGrad
import DifferentialGeometry.Geometry.Comparison.BusemannLineParallel
import DifferentialGeometry.Geometry.Exponential.ParallelField
import DifferentialGeometry.Geometry.Metric.ParallelFlow

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold Topology

namespace DifferentialGeometry

open Analysis.ODE
open Geometry.Connection
open Geometry.Operator
open Geometry.Riemannian
open Geometry.Riemannian.BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

private def buseGrad
    (g : SmoothRiemannianMetric I M) {b : M → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b) :
    ContMDiffSection I E ((⊤ : ℕ∞) : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
  ⟨fun x : M ↦ gradFun (I := I) g b x,
    gradFun_contMDiff_total_section (I := I) g hb⟩

private theorem buseGrad_complete
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    ∀ x : M, ∃ c : ℝ → M, c 0 = x ∧
      IsMIntegralCurve c
        (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y) := by
  classical
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let b : M → ℝ := busemann (I := I) γ
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    simpa only [b] using busemann_smooth (I := I) g hEnorm hγ hd hRic
  let X : ContMDiffSection I E ((⊤ : ℕ∞) : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := buseGrad (I := I) g hb
  have hX : ∀ y : M,
      (LeviCivita (I := I) g).toFun (fun z : M ↦ X z) y = 0 := by
    intro y
    simpa only [X, buseGrad, ContMDiffSection.coeFn_mk, b] using
      busemann_grad_par (I := I) g hEnorm hγ hd hRic y
  intro x
  refine ⟨Geometry.Riemannian.Exponential.intrinsicGeodesic
      (I := I) g hEnorm x (X x), ?_, ?_⟩
  · exact Geometry.Riemannian.Exponential.intrinsicGeodesic_zero
      (I := I) g hEnorm x (X x)
  · simpa only [X, buseGrad, ContMDiffSection.coeFn_mk, b] using
      Geometry.Riemannian.Exponential.intrinsic_intCurve
        (I := I) g hEnorm X hX x

omit [I.Boundaryless] [ConnectedSpace M] in
private theorem minLine_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ) : Continuous γ := by
  have hIso : Isometry γ := by
    intro s t
    rw [IsRiemannianManifold.out (I := I) (γ s) (γ t), edist_dist,
      Real.dist_eq]
    rcases le_total s t with hst | hts
    · rw [show |s - t| = t - s by
        rw [abs_of_nonpos (sub_nonpos.mpr hst)]; ring]
      exact hγ.edist_eq hst
    · rw [riemannianEDist_comm,
        abs_of_nonneg (sub_nonneg.mpr hts)]
      exact hγ.edist_eq hts
  have hmetric :
      @Continuous ℝ M _
        PseudoEMetricSpace.toUniformSpace.toTopologicalSpace γ :=
    hIso.continuous
  rw [continuous_iff_continuousAt]
  intro s
  have hsMetric : Filter.Tendsto γ (@nhds ℝ _ s)
      (@nhds M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace (γ s)) :=
    @Continuous.tendsto ℝ M _
      PseudoEMetricSpace.toUniformSpace.toTopologicalSpace γ hmetric s
  exact Geometry.Riemannian.HopfRinow.tendsto_nhds_of_tendsto_metric_nhds
    (I := I) hsMetric

private theorem minLine_speed_sq
    [NeZero (Module.finrank ℝ E)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ) (t : ℝ) :
    g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1 := by
  classical
  let p : M := γ 0
  let v : TangentSpace I p := mfderiv 𝓘(ℝ, ℝ) I γ 0 1
  let σ : ℝ → M :=
    Geometry.Riemannian.Exponential.intrinsicGeodesic
      (I := I) g hEnorm p v
  have hγ_cont : Continuous γ := minLine_continuous (I := I) hγ
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ := by
    apply contMDiffOn_univ.mp
    exact Geometry.Riemannian.Geodesic.isGeodesicOn_contMDiffOn_infty
      (I := I) g isOpen_univ (hγ.isGeodesic.isGeodesicOn Set.univ)
        hγ_cont.continuousOn
  have hσ_geo : Geometry.Riemannian.Geodesic.IsGeodesic (I := I) g σ := by
    simpa only [σ] using
      Geometry.Riemannian.Exponential.intrinsicGeodesic_isGeodesic
        (I := I) g hEnorm p v
  have hσ_cont : Continuous σ := by
    simpa only [σ] using
      Geometry.Riemannian.Exponential.intrinsicGeodesic_continuous
        (I := I) g hEnorm p v
  have hfoot : γ 0 = σ 0 := by
    simpa only [p, σ] using
      (Geometry.Riemannian.Exponential.intrinsicGeodesic_zero
        (I := I) g hEnorm p v).symm
  have hvel :
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 1 : E) =
        (mfderiv 𝓘(ℝ, ℝ) I σ 0 1 : E) := by
    change (v : E) = _
    simpa only [σ] using
      (Geometry.Riemannian.Exponential.intrinsicGeodesic_mfderiv_zero
        (I := I) g hEnorm p v).symm
  have hγσ : γ = σ :=
    Geometry.Riemannian.Exponential.isGeodesic_eq_of_initial
      (I := I) g hγ.isGeodesic hσ_geo hγ_cont hσ_cont hfoot hvel
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  letI : RegularSpace M := inferInstance
  letI : T3Space M := inferInstance
  letI : MetricSpace M :=
    Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I) (M := M)
  obtain ⟨ρ, hρ, hdist⟩ :=
    Geometry.Riemannian.exists_dist_eq_sqrt (I := I) g hEnorm p
  let c : ℝ := Real.sqrt (g.inner p v v)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  let δ : ℝ := ρ / (c + 1)
  have hc1 : 0 < c + 1 := by linarith
  have hδ : 0 < δ := div_pos hρ hc1
  have hδc : δ * c < ρ := by
    have hfrac : c / (c + 1) < 1 := (div_lt_one hc1).2 (by linarith)
    calc
      δ * c = ρ * (c / (c + 1)) := by
        dsimp only [δ]
        ring
      _ < ρ * 1 := mul_lt_mul_of_pos_left hfrac hρ
      _ = ρ := mul_one ρ
  have hscaled :
      Real.sqrt (g.inner p ((δ • v : TangentSpace I p) : E)
        ((δ • v : TangentSpace I p) : E)) = δ * c := by
    simpa only [c] using
      Geometry.Riemannian.Exponential.sqrt_gInner_smul_self
        (I := I) g p hδ.le v
  have hsmall₀ :
      Real.sqrt (g.inner p ((δ • v : TangentSpace I p) : E)
        ((δ • v : TangentSpace I p) : E)) < ρ := by
    rw [hscaled]
    exact hδc
  have hγδ : γ δ =
      Geometry.Riemannian.Exponential.expMapIntrinsic
        (I := I) g hEnorm p (δ • v) := by
    rw [hγσ]
    change Geometry.Riemannian.Exponential.intrinsicGeodesic
        (I := I) g hEnorm p v δ =
      Geometry.Riemannian.Exponential.intrinsicGeodesic
        (I := I) g hEnorm p (δ • v) 1
    exact (Geometry.Riemannian.Exponential.intrinsicGeodesic_smul
      (I := I) g hEnorm p v δ).symm
  have hdist_param : dist p (γ δ) = δ := by
    rw [Geometry.Riemannian.HopfRinow.riemMetric_dist_eq]
    have h := congrArg ENNReal.toReal
      (hγ.edist_eq (s := 0) (t := δ) hδ.le)
    simpa only [p, sub_zero, ENNReal.toReal_ofReal hδ.le] using h
  have hδeq : δ = δ * c := by
    calc
      δ = dist p (γ δ) := hdist_param.symm
      _ = dist p
          (Geometry.Riemannian.Exponential.expMapIntrinsic
            (I := I) g hEnorm p (δ • v)) := by rw [hγδ]
      _ = Real.sqrt (g.inner p ((δ • v : TangentSpace I p) : E)
          ((δ • v : TangentSpace I p) : E)) := hdist hsmall₀
      _ = δ * c := hscaled
  have hc_eq : c = 1 := by nlinarith
  have hv_nonneg : 0 ≤ g.inner p v v :=
    Geometry.Riemannian.Exponential.gInner_self_nonneg (I := I) g p v
  have hspeed0 : g.inner p v v = 1 := by
    calc
      g.inner p v v = (Real.sqrt (g.inner p v v)) ^ 2 :=
        (Real.sq_sqrt hv_nonneg).symm
      _ = c ^ 2 := by rfl
      _ = 1 := by rw [hc_eq]; norm_num
  have hconst :=
    Geometry.Riemannian.HopfRinow.isGeodesicOn_speedSq_const
      (I := I) g (t₀ := t) (t₁ := 0) isOpen_univ
        (hγ.isGeodesic.isGeodesicOn Set.univ)
        (hγ_smooth.contMDiffOn.of_le (by simp)) (Set.subset_univ _)
  rw [hconst]
  simpa only [p, v] using hspeed0

/-- The complete flow of the gradient of the forward Busemann function of a
supplied minimizing line. -/
noncomputable def busemannFlow
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (t : ℝ) (x : M) : M :=
  curveAt
    (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y)
    (buseGrad_complete (I := I) g hEnorm hγ hd hRic) x t

/-- The Busemann-gradient flow is the identity at time zero. -/
@[simp] theorem busemannFlow_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (x : M) :
    busemannFlow (I := I) g hEnorm hγ hd hRic 0 x = x := by
  simpa only [busemannFlow] using
    curveAt_zero
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y)
      (buseGrad_complete (I := I) g hEnorm hγ hd hRic) x

/-- Every time orbit of the Busemann-gradient flow is an integral curve of the
Busemann gradient. -/
theorem busemannFlow_curve
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (x : M) :
    IsMIntegralCurve
      (fun t : ℝ ↦ busemannFlow (I := I) g hEnorm hγ hd hRic t x)
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y) := by
  simpa only [busemannFlow] using
    curveAt_integralCurve
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y)
      (buseGrad_complete (I := I) g hEnorm hγ hd hRic) x

/-- The Busemann-gradient flow obeys the additive flow law. -/
theorem busemannFlow_add
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    (x : M) (s t : ℝ) :
    busemannFlow (I := I) g hEnorm hγ hd hRic (s + t) x =
      busemannFlow (I := I) g hEnorm hγ hd hRic t
        (busemannFlow (I := I) g hEnorm hγ hd hRic s x) := by
  have hb := busemann_smooth (I := I) g hEnorm hγ hd hRic
  have hv : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
      (fun y : M ↦
        (⟨y, gradFun (I := I) g (busemann (I := I) γ) y⟩ :
          TangentBundle I M)) :=
    (gradFun_contMDiff_total_section (I := I) g hb).of_le (by simp)
  simpa only [busemannFlow] using
    curveAt_add
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y)
      hv (buseGrad_complete (I := I) g hEnorm hγ hd hRic) x s t

/-- The Busemann-gradient flow depends smoothly on time and its initial point. -/
theorem busemannFlow_smooth
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M ↦
        busemannFlow (I := I) g hEnorm hγ hd hRic p.1 p.2) := by
  have hb := busemann_smooth (I := I) g hEnorm hγ hd hRic
  have hv : ContMDiff I (I.prod 𝓘(ℝ, E))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M ↦
        (⟨y, gradFun (I := I) g (busemann (I := I) γ) y⟩ :
          TangentBundle I M)) :=
    gradFun_contMDiff_total_section (I := I) g hb
  simpa only [busemannFlow] using
    curveAt_contMDiff
      (fun y : M ↦ gradFun (I := I) g (busemann (I := I) γ) y)
      hv (buseGrad_complete (I := I) g hEnorm hγ hd hRic)

/-- The spatial differential of the Busemann-gradient flow preserves the
Riemannian inner product. -/
theorem busemannFlow_inner
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    (x : M) (v w : TangentSpace I x) (t : ℝ) :
    g.inner (busemannFlow (I := I) g hEnorm hγ hd hRic t x)
        (mfderiv I I
          (fun y ↦ busemannFlow (I := I) g hEnorm hγ hd hRic t y) x v)
        (mfderiv I I
          (fun y ↦ busemannFlow (I := I) g hEnorm hγ hd hRic t y) x w) =
      g.inner x v w := by
  classical
  let b : M → ℝ := busemann (I := I) γ
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    simpa only [b] using busemann_smooth (I := I) g hEnorm hγ hd hRic
  let X : ContMDiffSection I E ((⊤ : ℕ∞) : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := buseGrad (I := I) g hb
  have hcomplete : ∀ y : M, ∃ c : ℝ → M, c 0 = y ∧
      IsMIntegralCurve c (fun z : M ↦ X z) := by
    simpa only [X, buseGrad, ContMDiffSection.coeFn_mk, b] using
      buseGrad_complete (I := I) g hEnorm hγ hd hRic
  have hpar : ∀ y : M,
      (LeviCivita (I := I) g).toFun (fun z : M ↦ X z) y = 0 := by
    intro y
    simpa only [X, buseGrad, ContMDiffSection.coeFn_mk, b] using
      busemann_grad_par (I := I) g hEnorm hγ hd hRic y
  simpa only [busemannFlow, X, buseGrad, ContMDiffSection.coeFn_mk, b] using
    curveAt_inner_eq (I := I) g X hcomplete hpar x v w t

/-- Flowing for time `t` translates the forward Busemann value by `t`. -/
theorem busemannFlow_value
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (t : ℝ) (x : M) :
    busemann (I := I) γ
        (busemannFlow (I := I) g hEnorm hγ hd hRic t x) =
      busemann (I := I) γ x + t := by
  classical
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let b : M → ℝ := busemann (I := I) γ
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    simpa only [b] using busemann_smooth (I := I) g hEnorm hγ hd hRic
  have hunit (y : M) :
      g.inner y (gradFun (I := I) g b y) (gradFun (I := I) g b y) = 1 := by
    simpa only [b, gradient_eq_gradFun] using
      busemann_grad_sq (I := I) g hEnorm hγ.pos_ray y
        (hb.contMDiffAt.mdifferentiableAt (by simp))
  have hdf : ∀ y : M,
      (NormedSpace.fromTangentSpace ((-b) y))
        ((mfderiv I 𝓘(ℝ, ℝ) (-b) y) (gradFun (I := I) g b y)) = -1 := by
    intro y
    rw [mfderiv_neg]
    change -((mfderiv I 𝓘(ℝ, ℝ) b y)
      (gradFun (I := I) g b y)) = -1
    rw [← inner_gradFun (I := I) g b y]
    exact congrArg (fun z : ℝ ↦ -z) (hunit y)
  have hcurve : IsMIntegralCurve
      (fun s : ℝ ↦ busemannFlow (I := I) g hEnorm hγ hd hRic s x)
      (fun y : M ↦ gradFun (I := I) g b y) := by
    simpa only [b] using
      busemannFlow_curve (I := I) g hEnorm hγ hd hRic x
  have htranslate := f_eq_sub_of_integralCurve (I := I)
    (-b) hb.neg (fun y : M ↦ gradFun (I := I) g b y) hdf hcurve t
  rw [busemannFlow_zero (I := I) g hEnorm hγ hd hRic x] at htranslate
  change -b (busemannFlow (I := I) g hEnorm hγ hd hRic t x) =
    -b x - t at htranslate
  change b (busemannFlow (I := I) g hEnorm hγ hd hRic t x) = b x + t
  linarith

/-- Flow time `-t` from the line origin is the supplied minimizing line at
parameter `t`. -/
theorem busemannFlow_line
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) (t : ℝ) :
    busemannFlow (I := I) g hEnorm hγ hd hRic (-t) (γ 0) = γ t := by
  classical
  letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let b : M → ℝ := busemann (I := I) γ
  let X : (y : M) → TangentSpace I y := fun y ↦
    gradFun (I := I) g b y
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    simpa only [b] using busemann_smooth (I := I) g hEnorm hγ hd hRic
  have hγ_cont : Continuous γ := minLine_continuous (I := I) hγ
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ := by
    apply contMDiffOn_univ.mp
    exact Geometry.Riemannian.Geodesic.isGeodesicOn_contMDiffOn_infty
      (I := I) g isOpen_univ (hγ.isGeodesic.isGeodesicOn Set.univ)
        hγ_cont.continuousOn
  have hbline (s : ℝ) : b (γ s) = -s := by
    by_cases hs : 0 ≤ s
    · simpa only [b] using busemann_ray (I := I) hγ.pos_ray hs
    · have hs' : s ≤ 0 := le_of_not_ge hs
      have hneg :
          busemann (I := I) (fun r : ℝ ↦ γ (-r)) (γ s) = s := by
        simpa only [neg_neg] using
          busemann_ray (I := I) hγ.neg_ray (s := -s) (neg_nonneg.mpr hs')
      have hpair := buse_pair_line (I := I) hγ s
      change b (γ s) +
        busemann (I := I) (fun r : ℝ ↦ γ (-r)) (γ s) = 0 at hpair
      rw [hneg] at hpair
      linarith
  have hgrad_unit (s : ℝ) :
      g.inner (γ s) (X (γ s)) (X (γ s)) = 1 := by
    simpa only [X, b, gradient_eq_gradFun] using
      busemann_grad_sq (I := I) g hEnorm hγ.pos_ray (γ s)
        (hb.contMDiffAt.mdifferentiableAt (by simp))
  have hline_vel (s : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) I γ s 1 = -X (γ s) := by
    let q : ℝ :=
      NormedSpace.fromTangentSpace (b (γ s))
        (mfderiv I 𝓘(ℝ, ℝ) b (γ s)
          (mfderiv 𝓘(ℝ, ℝ) I γ s 1))
    have hcomp : HasDerivAt (fun r : ℝ ↦ b (γ r)) q s := by
      simpa only [q] using
        Analysis.Calculus.hasDerivAt_comp_mfderiv_along
          I b γ s (hb.contMDiffAt.mdifferentiableAt (by simp))
            (hγ_smooth.contMDiffAt.mdifferentiableAt (by simp))
    have hlinear : HasDerivAt (fun r : ℝ ↦ -r) (-1) s := by
      simpa only using (hasDerivAt_id (x := s)).neg
    have hfun : (fun r : ℝ ↦ b (γ r)) = fun r : ℝ ↦ -r :=
      funext hbline
    rw [hfun] at hcomp
    have hq : q = -1 := hcomp.unique hlinear
    have hq_inner : q =
        g.inner (γ s) (X (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) := by
      dsimp only [q]
      change mfderiv I 𝓘(ℝ, ℝ) b (γ s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s 1) = _
      exact (Geometry.Connection.gradFun_metricDual (I := I) g b (γ s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s 1)).symm
    have hgrad_vel :
        g.inner (γ s) (X (γ s)) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) = -1 := by
      rw [← hq_inner]
      exact hq
    have hvel_grad :
        g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (X (γ s)) = -1 :=
      (g.symm (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (X (γ s))).trans
        hgrad_vel
    have hvel_unit :
        g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ s 1) = 1 :=
      minLine_speed_sq (I := I) g hEnorm hγ s
    have hsum_inner :
        g.inner (γ s)
            (mfderiv 𝓘(ℝ, ℝ) I γ s 1 + X (γ s))
            (mfderiv 𝓘(ℝ, ℝ) I γ s 1 + X (γ s)) = 0 := by
      rw [(g.inner (γ s)).map_add, ContinuousLinearMap.add_apply,
        (g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1)).map_add,
        (g.inner (γ s) (X (γ s))).map_add,
        hvel_unit, hvel_grad, hgrad_vel, hgrad_unit]
      norm_num
    have hsum : mfderiv 𝓘(ℝ, ℝ) I γ s 1 + X (γ s) = 0 := by
      by_contra hne
      have hpos := g.pos (γ s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s 1 + X (γ s)) hne
      rw [hsum_inner] at hpos
      exact (lt_irrefl 0 hpos)
    exact eq_neg_of_add_eq_zero_left hsum
  have hγ_curve : IsMIntegralCurve γ (fun y : M ↦ -X y) := by
    intro s
    have hγ_at : HasMFDerivAt 𝓘(ℝ, ℝ) I γ s
        (mfderiv 𝓘(ℝ, ℝ) I γ s) :=
      (hγ_smooth.mdifferentiableAt (by simp)).hasMFDerivAt
    have hmfderiv : mfderiv 𝓘(ℝ, ℝ) I γ s =
        (1 : ℝ →L[ℝ] ℝ).smulRight (-X (γ s)) := by
      apply ContinuousLinearMap.ext
      intro (r : ℝ)
      calc
        mfderiv 𝓘(ℝ, ℝ) I γ s r =
            r • mfderiv 𝓘(ℝ, ℝ) I γ s 1 := by
          calc
            mfderiv 𝓘(ℝ, ℝ) I γ s r =
                mfderiv 𝓘(ℝ, ℝ) I γ s (r • (1 : ℝ)) := by congr 1; simp
            _ = r • mfderiv 𝓘(ℝ, ℝ) I γ s 1 :=
              ContinuousLinearMap.map_smul
                (mfderiv 𝓘(ℝ, ℝ) I γ s) r (1 : ℝ)
        _ = r • (-X (γ s)) := by rw [hline_vel s]
        _ = ((1 : ℝ →L[ℝ] ℝ).smulRight (-X (γ s))) r := by simp
    exact hγ_at.congr_mfderiv hmfderiv
  have hrev : IsMIntegralCurve (fun s : ℝ ↦ γ (-s)) X := by
    have hc := IsMIntegralCurve.comp_mul hγ_curve (-1)
    have hcurve : (γ ∘ fun s : ℝ ↦ s * (-1)) = fun s : ℝ ↦ γ (-s) := by
      funext s
      simp
    have hfield : ((-1 : ℝ) • fun y : M ↦ -X y) = X := by
      funext y
      simp
    rw [hcurve, hfield] at hc
    exact hc
  have hflow : IsMIntegralCurve
      (fun s : ℝ ↦ busemannFlow (I := I) g hEnorm hγ hd hRic s (γ 0)) X := by
    simpa only [X, b] using
      busemannFlow_curve (I := I) g hEnorm hγ hd hRic (γ 0)
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) (1 : WithTop ℕ∞)
      (fun y : M ↦ (⟨y, X y⟩ : TangentBundle I M)) := by
    simpa only [X] using
      (gradFun_contMDiff_total_section (I := I) g hb).of_le (by simp)
  have heq := integralCurve_eq_of_agree_zero X hX hflow hrev (by
    rw [busemannFlow_zero (I := I) g hEnorm hγ hd hRic]
    simp)
  have ht := congrFun heq (-t)
  simpa only [neg_neg] using ht

end

end DifferentialGeometry
