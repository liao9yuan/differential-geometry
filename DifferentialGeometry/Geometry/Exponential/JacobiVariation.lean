import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond
import DifferentialGeometry.Analysis.Calculus.SmoothClamp
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiField
import DifferentialGeometry.Geometry.Exponential.GaussLemmaPullback
import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity
import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Geometry.Geodesic.MaximalRescaling
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace E]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem chartRep_congr_curve
    {γ γ' : ℝ → M}
    (V : ∀ s : ℝ, TangentSpace I (γ s)) (V' : ∀ s : ℝ, TangentSpace I (γ' s))
    {t : ℝ}
    (hγ : γ =ᶠ[𝓝 t] γ')
    (hV : ∀ᶠ s in 𝓝 t, (V s : E) = (V' s : E)) :
    chartRepAt (I := I) γ V t =ᶠ[𝓝 t] chartRepAt (I := I) γ' V' t := by
  have hfoot : γ t = γ' t := hγ.eq_of_nhds
  have hkey : ∀ (x y : M), x = y → ∀ (v : TangentSpace I x) (v' : TangentSpace I y),
      (v : E) = (v' : E) →
      (trivializationAt E (TangentSpace I) (γ' t)).continuousLinearMapAt ℝ x v
        = (trivializationAt E (TangentSpace I) (γ' t)).continuousLinearMapAt ℝ y v' := by
    intro x y hxy
    subst hxy
    intro v v' hvv'
    have hvv : v = v' := hvv'
    rw [hvv]
  filter_upwards [hγ, hV] with s hsγ hsV
  rw [chartRepAt_apply, chartRepAt_apply, hfoot]
  exact hkey _ _ hsγ _ _ hsV

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem covDerivAlong_congr_curve
    (g : SmoothRiemannianMetric I M) {γ γ' : ℝ → M}
    (V : ∀ s : ℝ, TangentSpace I (γ s)) (V' : ∀ s : ℝ, TangentSpace I (γ' s)) {t : ℝ}
    (hγ : γ =ᶠ[𝓝 t] γ')
    (hV : ∀ᶠ s in 𝓝 t, (V s : E) = (V' s : E)) :
    (covDerivAlong (I := I) g γ V t : E) = (covDerivAlong (I := I) g γ' V' t : E) := by
  have hfoot : γ t = γ' t := hγ.eq_of_nhds
  have hcurve : chartCurve (I := I) (γ' t) γ =ᶠ[𝓝 t] chartCurve (I := I) (γ' t) γ' := by
    filter_upwards [hγ] with s hs
    simp only [chartCurve_def]
    rw [hs]
  have hrep : chartRepAt (I := I) γ V t =ᶠ[𝓝 t] chartRepAt (I := I) γ' V' t :=
    chartRep_congr_curve (I := I) V V' hγ hV
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [show (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
        = (trivializationAt E (TangentSpace I) (γ' t)).symmL ℝ (γ' t) from by rw [hfoot]]
  rw [show (γ t) = (γ' t) from hfoot]
  congr 1
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [hrep.deriv_eq, hrep.eq_of_nhds, hcurve.deriv_eq, hcurve.eq_of_nhds]

omit [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma riemannOp_congr_point (g : SmoothRiemannianMetric I M)
    {x y : M} (h : x = y) (A B C : E) :
    ((DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) x) A B C : E)
    = ((DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) y) A B C : E) := by
  subst h
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem covDerivAlong_const (g : SmoothRiemannianMetric I M) (p : M)
    (V : ℝ → TangentSpace I p) (t : ℝ)
    (hV : DifferentiableAt ℝ (fun s => (V s : E)) t) :
    (covDerivAlong (I := I) g (fun _ : ℝ => p) V t : E)
      = deriv (fun s => (V s : E)) t := by
  classical
  set L : TangentSpace I p →L[ℝ] E :=
    (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p with hL
  have hrep : chartRepAt (I := I) (fun _ : ℝ => p) V t = fun s : ℝ => L (V s) := by
    funext s; rw [chartRepAt_apply]
  have hcurve_deriv : deriv (chartCurve (I := I) p (fun _ : ℝ => p)) t = 0 := by
    have hc : chartCurve (I := I) p (fun _ : ℝ => p) = fun _ : ℝ => extChartAt I p p := by
      funext s; rw [chartCurve_def]
    rw [hc]; exact deriv_const t _
  have hsecderiv : HasDerivAt (fun s : ℝ => L (V s)) (L (deriv (fun s => (V s : E)) t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t hV.hasDerivAt
  have hmem : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) p
  rw [covDerivAlong_def, chartCovDerivAlong_def, hrep, hcurve_deriv,
    chartChristoffelContraction_zero_left, add_zero, hsecderiv.deriv]
  exact (trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt
    (R := ℝ) hmem (deriv (fun s => (V s : E)) t)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
theorem intrinsic_jacobi
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (x w : E) :
    IsJacobiAlong (I := I) g
      (fun t : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from x) t)
      (fun t : ℝ => show TangentSpace I
          (intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x) t) from
        mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x + s • w) t) 0 (1 : ℝ)) := by
  classical
  let F : ℝ → ℝ → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from x + s • w) t
  have hFsmooth : IsSmoothVariation (I := I) F := by
    change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ)
      (fun q : ℝ × ℝ => F q.1 q.2)
    exact (intrinsicVar_smooth (I := I) g hEnorm p x w).of_le ENat.LEInfty.out
  intro t₀
  have houterL_field : ∀ s : ℝ,
      covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) v (1 : ℝ)) t₀ = 0 := by
    intro s
    have hslice : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun v : ℝ => F s v) := by
      have hincl : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
          (fun v : ℝ => (s, v)) := contMDiff_const.prodMk contMDiff_id
      exact (hFsmooth : ContMDiff _ _ _ _).comp hincl
    have hsliceC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun v : ℝ => F s v) t₀ :=
      hslice.contMDiffAt.of_le (by norm_num)
    have hgeo : HasGeodesicEquationAt (I := I) g (fun v : ℝ => F s v) t₀ := by
      simpa only [F] using
        (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from x + s • w) t₀)
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
      (I := I) g _ t₀ hsliceC2 hgeo
  have houterL : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => F s t₀)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0) 0 := by
    have hzero : (chartRepAt (I := I) (fun s : ℝ => F s t₀)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0)
        =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => (0 : E)) := by
      filter_upwards with s
      rw [chartRepAt_apply, houterL_field s]
      exact map_zero _
    exact (hzero.differentiableAt_iff).mpr (differentiableAt_const _)
  have hsymm : ∀ v : ℝ,
      covDerivAlong (I := I) g (fun u : ℝ => F u v)
        (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u' : ℝ => F u u') v (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v :=
    fun v => commute_ds_dt_intrinsic (I := I) g F hFsmooth v
  have hfields : (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F u v)
      (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u' : ℝ => F u u') v (1 : ℝ)) 0)
      = (fun v : ℝ => covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v) :=
    funext hsymm
  have houterR : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => F 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F u v)
          (fun u : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u' : ℝ => F u u') v (1 : ℝ)) 0) t₀) t₀ := by
    rw [hfields]
    exact variationField_covDeriv_chartRep_differentiableAt (I := I) g F hFsmooth t₀
  have hcomm := commute_ds_dt_curvature (I := I) g F hFsmooth t₀ houterL houterR
  have hT1 : covDerivAlong (I := I) g (fun s : ℝ => F s t₀)
      (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0 = 0 := by
    have hfun : (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) v (1 : ℝ)) t₀)
        = (fun s : ℝ => (0 : TangentSpace I ((fun s' : ℝ => F s' t₀) s))) :=
      funext houterL_field
    rw [hfun]
    exact covDerivAlong_zero (I := I) g (fun s' : ℝ => F s' t₀) 0
  rw [hT1, hfields, zero_sub, neg_eq_iff_eq_neg] at hcomm
  have hjac : IsJacobiAt (I := I) g (fun v : ℝ => F 0 v)
      (fun v : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F u v) 0 (1 : ℝ)) t₀ := by
    change covDerivAlong (I := I) g (fun v : ℝ => F 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
          (fun v' : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v) t₀
      + (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (F 0 t₀))
          (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F u t₀) 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F 0 u) t₀ (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F 0 u) t₀ (1 : ℝ)) = 0
    linear_combination (norm := module) hcomm
  have hF0 : (fun v : ℝ => F 0 v) =
      (fun v : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from x) v) := by
    funext v
    simp only [F, zero_smul, add_zero]
  rw [hF0] at hjac
  exact hjac

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem intrinsic_jacobi_one
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (x w : E) :
    mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from x + s • w) 1) 0 (1 : ℝ)
      = mfderiv 𝓘(ℝ, E) I
          (fun b : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from b)) x w := by
  let line : ℝ → E := fun s => x + s • w
  let exp : E → M := fun b => expMapIntrinsic (I := I) g hEnorm p
    (show TangentSpace I p from b)
  have hfoot : line 0 = x := by simp only [line, zero_smul, add_zero]
  have hcurve : (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from x + s • w) 1) = exp ∘ line := by
    funext s
    rfl
  have hexp_md : MDifferentiableAt 𝓘(ℝ, E) I exp x :=
    (intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt.mdifferentiableAt (by decide)
  have hexp_md' : MDifferentiableAt 𝓘(ℝ, E) I exp (line 0) := by
    rw [hfoot]
    exact hexp_md
  have hline_md : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) line 0 := by
    have hMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ line :=
      contMDiff_const.add (contMDiff_id.smul contMDiff_const)
    exact hMD.contMDiffAt.mdifferentiableAt (by decide)
  have hline : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) line 0 (1 : ℝ) = w := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt line
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w) 0 := by
      simpa only [line] using ((hasFDerivAt_id (0 : ℝ)).smul_const w).const_add x
    rw [h.fderiv]
    change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w) (1 : ℝ) = w
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  have hfootCLM : (mfderiv 𝓘(ℝ, E) I exp (line 0) : E →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, E) I exp x : E →L[ℝ] E) := by
    rw [hfoot]
  rw [hcurve]
  have hstep := mfderiv_comp_apply (f := line) (x := (0 : ℝ))
    hexp_md' hline_md (1 : ℝ)
  have hgoal : (mfderiv 𝓘(ℝ, E) I exp (line 0))
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) line 0) (1 : ℝ)) =
      (mfderiv 𝓘(ℝ, E) I exp x) w := by
    rw [hline]
    exact congrArg (fun L : E →L[ℝ] E => L w) hfootCLM
  exact hstep.trans hgoal

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem intrinsic_jacobi_at
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (x w : E) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from x + s • w) t) 0 (1 : ℝ)
      =
        mfderiv 𝓘(ℝ, E) I
          (fun b : E => expMapIntrinsic (I := I) g hEnorm p
            (show TangentSpace I p from b))
          (t • x) (t • w) := by
  have hfun :
      (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from x + s • w) t) =
        fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from t • x + s • (t • w)) 1 := by
    funext s
    have hvec : t • (x + s • w) = t • x + s • (t • w) := by
      module
    rw [← hvec]
    exact
      (intrinsicGeodesic_smul (I := I) g hEnorm p
        (show TangentSpace I p from x + s • w) t).symm
  rw [hfun]
  exact intrinsic_jacobi_one (I := I) g hEnorm p (t • x) (t • w)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] [CompleteSpace E] in
theorem intrinsic_jacobi_d0
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (x w : E) :
    (covDerivAlong (I := I) g
      (fun t : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from x) t)
      (fun t : ℝ => show TangentSpace I
          (intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x) t) from
        mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from x + s • w) t) 0 (1 : ℝ))
      0 : E) = w := by
  classical
  let F : ℝ → ℝ → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from x + s • w) t
  have hFsmooth : IsSmoothVariation (I := I) F := by
    change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I (8 : ℕ)
      (fun q : ℝ × ℝ => F q.1 q.2)
    exact (intrinsicVar_smooth (I := I) g hEnorm p x w).of_le ENat.LEInfty.out
  have hF0 : ∀ s : ℝ, F s 0 = p := by
    intro s
    exact intrinsicGeodesic_zero (I := I) g hEnorm p _
  have hlaunch : ∀ s : ℝ,
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) 0 (1 : ℝ) : E) = x + s • w := by
    intro s
    exact intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p
      (show TangentSpace I p from x + s • w)
  have hF0_ev : (fun s : ℝ => F s 0) =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => p) :=
    Filter.Eventually.of_forall hF0
  have hlaunch_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) 0 (1 : ℝ) : E)
        = ((show TangentSpace I p from x + s • w : E)) :=
    Filter.Eventually.of_forall hlaunch
  have hHDA : HasDerivAt (fun s : ℝ => x + s • w) w 0 := by
    have h : HasDerivAt (fun s : ℝ => x + s • w) ((1 : ℝ) • w) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    simpa using h
  have hLHS := covDerivAlong_congr_curve (I := I) g
    (fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) 0 (1 : ℝ))
    (fun s : ℝ => (show TangentSpace I p from x + s • w)) hF0_ev hlaunch_ev
  have hdiff : DifferentiableAt ℝ
      (fun s : ℝ => ((show TangentSpace I p from x + s • w) : E)) 0 :=
    hHDA.differentiableAt
  have hconst := covDerivAlong_const (I := I) g p
    (fun s : ℝ => (show TangentSpace I p from x + s • w)) 0 hdiff
  have hderiv :
      deriv (fun s : ℝ => ((show TangentSpace I p from x + s • w) : E)) 0 = w :=
    hHDA.deriv
  have hcomm := commute_ds_dt_intrinsic (I := I) g F hFsmooth 0
  have hcomm_E :
      (covDerivAlong (I := I) g (fun s : ℝ => F s 0)
          (fun s : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => F s u) 0 (1 : ℝ)) 0 : E)
        = (covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
          (fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F s t) 0 (1 : ℝ)) 0 : E) := by
    rw [hcomm]
  have hfinal :
      (covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
          (fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F s t) 0 (1 : ℝ)) 0 : E)
        = w :=
    hcomm_E.symm.trans (hLHS.trans (hconst.trans hderiv))
  have hcentral_ev : (fun t : ℝ => F 0 t) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from x) t) := by
    filter_upwards with t
    simp only [F, zero_smul, add_zero]
  have hfield_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F s t) 0 (1 : ℝ) : E)
        = ((show TangentSpace I
            (intrinsicGeodesic (I := I) g hEnorm p
              (show TangentSpace I p from x) t) from
          mfderiv 𝓘(ℝ, ℝ) I
            (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
              (show TangentSpace I p from x + s • w) t) 0 (1 : ℝ)) : E) := by
    filter_upwards with t
    rfl
  have hRHS := covDerivAlong_congr_curve (I := I) g
    (fun t : ℝ => mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => F s t) 0 (1 : ℝ))
    (fun t : ℝ => show TangentSpace I
        (intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from x) t) from
      mfderiv 𝓘(ℝ, ℝ) I
        (fun s : ℝ => intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from x + s • w) t) 0 (1 : ℝ))
    hcentral_ev hfield_ev
  exact hRHS.symm.trans hfinal

omit [T2Space M] [SigmaCompactSpace M] in
private lemma clamped_slice_covDeriv_velocity_zero
    (g : SmoothRiemannianMetric I M) (p : M) (a : E)
    (ha : ‖a‖ < expMapC2Radius (I := I) g p)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψid : ∀ u ∈ Set.Icc (-1 : ℝ) 2, ψ u = u)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    covDerivAlong (I := I) g
      (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (ψ v • a)) : M))
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
        (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (ψ u • a)) : M)) v (1 : ℝ))
      t₀ = 0 := by
  classical
  haveI : T2Space M := gauss_t2Space_base (I := I)
  have ht₀win : t₀ ∈ Set.Icc (-1 : ℝ) 2 := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  have hψt₀ : ψ t₀ = t₀ := hψid t₀ ht₀win
  have hnorm_t₀ : ‖ψ t₀ • a‖ < expMapC2Radius (I := I) g p := by
    rw [hψt₀, norm_smul, Real.norm_eq_abs, abs_of_pos ht₀.1]
    calc t₀ * ‖a‖ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right ht₀.2.le (norm_nonneg a)
      _ = ‖a‖ := one_mul _
      _ < _ := ha
  have hψMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
    rw [contMDiff_iff_contDiff]; exact hψ
  have hsmul : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun v : ℝ => ψ v • a) :=
    hψMD.smul contMDiff_const
  have hexpC2 : ContMDiffAt 𝓘(ℝ, E) I 2
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
      ((fun v : ℝ => ψ v • a) t₀) :=
    expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p hnorm_t₀
  have hγC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2
      (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (ψ v • a)) : M)) t₀ :=
    hexpC2.comp t₀ (hsmul.contMDiffAt.of_le ENat.LEInfty.out)
  have hgeo_max : HasGeodesicEquationAt (I := I) g
      (fun s : ℝ => maximalGeodesic (I := I) g p a s) t₀ :=
    radial_hasGeodesicEquationAt_of_norm_lt_radius (I := I) g p ha t₀
      ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  have hEv1 : (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M))
      =ᶠ[𝓝 t₀] (fun s : ℝ => maximalGeodesic (I := I) g p a s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht₀] with u hu
    rw [expMap]
    exact maximalGeodesic_rescale_of_norm_lt_radius (I := I) g p ha u ⟨hu.1.le, hu.2.le⟩
  have hgeo_unclamped : HasGeodesicEquationAt (I := I) g
      (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) t₀ :=
    HasGeodesicEquationAt.congr_of_eventuallyEq_at hEv1.eq_of_nhds hEv1 hgeo_max
  have hEv2 : (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (ψ v • a)) : M))
      =ᶠ[𝓝 t₀] (fun u : ℝ => (expMap (I := I) g p (show TangentSpace I p from (u • a)) : M)) := by
    have hwin : Set.Ioo (-1 : ℝ) 2 ∈ 𝓝 t₀ :=
      isOpen_Ioo.mem_nhds ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
    filter_upwards [hwin] with u hu
    rw [hψid u ⟨hu.1.le, hu.2.le⟩]
  have hgeo : HasGeodesicEquationAt (I := I) g
      (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (ψ v • a)) : M)) t₀ :=
    HasGeodesicEquationAt.congr_of_eventuallyEq_at hEv2.eq_of_nhds hEv2 hgeo_unclamped
  exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g _ t₀ hγC2 hgeo

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
private lemma clamped_slice_covDeriv_velocity_zero_at_zero
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (a : E)
    (ψ : ℝ → ℝ) (hψid : ∀ u ∈ Set.Icc (-1 : ℝ) 2, ψ u = u) :
    covDerivAlong (I := I) g
      (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (ψ v • a)) : M))
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (ψ u • a)) : M)) v (1 : ℝ))
      0 = 0 := by
  classical
  have hcurve : (fun v : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from (ψ v • a)) : M))
      =ᶠ[𝓝 (0 : ℝ)]
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • a)) : M)) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 2 by norm_num)] with v hv
    rw [hψid v ⟨hv.1.le, hv.2.le⟩]
  have hvel : ∀ᶠ v in 𝓝 (0 : ℝ),
      ((mfderiv (𝓘(ℝ, ℝ)) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (ψ u • a)) : M)) v (1 : ℝ)) : E)
      =
      ((mfderiv (𝓘(ℝ, ℝ)) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (u • a)) : M)) v (1 : ℝ)) : E) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 2 by norm_num)] with v hv
    have hgerm : (fun u : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from (ψ u • a)) : M))
        =ᶠ[𝓝 v]
          (fun u : ℝ => (expMap (I := I) g p
            (show TangentSpace I p from (u • a)) : M)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hv] with u hu
      rw [hψid u ⟨hu.1.le, hu.2.le⟩]
    have hmf : mfderiv (𝓘(ℝ, ℝ)) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (ψ u • a)) : M)) v
        =
        mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (u • a)) : M)) v :=
      hgerm.mfderiv_eq
    rw [hmf]
    rfl
  have hcongr := covDerivAlong_congr_curve (I := I) g
    (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
      (fun u : ℝ => (expMap (I := I) g p
        (show TangentSpace I p from (ψ u • a)) : M)) v (1 : ℝ))
    (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
      (fun u : ℝ => (expMap (I := I) g p
        (show TangentSpace I p from (u • a)) : M)) v (1 : ℝ))
    hcurve hvel
  have hzero := Exponential.exp_radial_d2_zero
    (I := I) g hEnorm p (show TangentSpace I p from a)
  change ((covDerivAlong (I := I) g
      (fun v : ℝ => (expMap (I := I) g p
        (show TangentSpace I p from (ψ v • a)) : M))
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
        (fun u : ℝ => (expMap (I := I) g p
          (show TangentSpace I p from (ψ u • a)) : M)) v (1 : ℝ))
      0 : TangentSpace I _) : E) = (0 : E)
  exact hcongr.trans (by simpa using hzero)

open DifferentialGeometry.Geometry.Riemannian.Exponential in
def jacobiVarRadius (g : SmoothRiemannianMetric I M) (p : M) : ℝ :=
  expMapC2Radius (I := I) g p / 26

omit [T2Space M] [SigmaCompactSpace M] in
lemma jacobiVarRadius_pos (g : SmoothRiemannianMetric I M) (p : M) :
    0 < jacobiVarRadius (I := I) g p := by
  exact div_pos (expMapC2Radius_pos (I := I) g p) (by norm_num)

omit [SigmaCompactSpace M] in
theorem radial_jacobi_of_lt (g : SmoothRiemannianMetric I M) (p : M)
    {x w : E} (hx : ‖x‖ < jacobiVarRadius (I := I) g p)
    (hw : ‖w‖ < jacobiVarRadius (I := I) g p) :
    ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      IsJacobiAt (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (fun v : ℝ => show TangentSpace I
            ((expMap (I := I) g p (show TangentSpace I p from (v • x)) : M)) from
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 (1 : ℝ))
        t₀ := by
  classical
  haveI : T2Space M := gauss_t2Space_base (I := I)
  obtain ⟨ψ, hψS, hψid, hψbd⟩ := exists_smooth_clamp (-1) 2 (by norm_num) (by norm_num)
  obtain ⟨φ, hφS, hφid, hφbd⟩ := exists_smooth_clamp (-1) 1 (by norm_num) (by norm_num)
  have hψbd5 : ∀ u : ℝ, |ψ u| ≤ 5 := fun u => (hψbd u).trans (by norm_num)
  have hφbd4 : ∀ u : ℝ, |φ u| ≤ 4 := fun u => (hφbd u).trans (by norm_num)
  set δ : ℝ := expMapC2Radius (I := I) g p with hδdef
  have hδpos : 0 < δ := by simpa [δ] using expMapC2Radius_pos (I := I) g p
  change ‖x‖ < δ / 26 at hx
  change ‖w‖ < δ / 26 at hw
  intro t₀ ht₀
  have ht₀win : t₀ ∈ Set.Icc (-1 : ℝ) 2 := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  have hslice_norm : ∀ s : ℝ, ‖x + φ s • w‖ < δ / 5 := by
    intro s
    have h1 : ‖x + φ s • w‖ ≤ ‖x‖ + |φ s| * ‖w‖ := by
      calc ‖x + φ s • w‖ ≤ ‖x‖ + ‖φ s • w‖ := norm_add_le _ _
        _ = ‖x‖ + |φ s| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h2 : |φ s| * ‖w‖ ≤ 4 * ‖w‖ :=
      mul_le_mul_of_nonneg_right (hφbd4 s) (norm_nonneg w)
    have hδ26 : ‖x‖ + 4 * ‖w‖ < 5 * (δ / 26) := by linarith [hx, hw, norm_nonneg w]
    have : (5 : ℝ) * (δ / 26) ≤ δ / 5 := by linarith [hδpos]
    linarith
  have hlaunch_norm : ∀ s t : ℝ, ‖ψ t • (x + φ s • w)‖ < δ := by
    intro s t
    have h0 : (0 : ℝ) ≤ ‖x + φ s • w‖ := norm_nonneg _
    calc ‖ψ t • (x + φ s • w)‖ = |ψ t| * ‖x + φ s • w‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 5 * ‖x + φ s • w‖ := mul_le_mul_of_nonneg_right (hψbd5 t) h0
      _ < 5 * (δ / 5) := by
          have := hslice_norm s
          nlinarith
      _ = δ := by ring
  have hslice_radius : ∀ s : ℝ, ‖x + φ s • w‖ < expMapC2Radius (I := I) g p := by
    intro s
    calc ‖x + φ s • w‖ < δ / 5 := hslice_norm s
      _ ≤ δ := by linarith [hδpos]
      _ = _ := hδdef
  set F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p (show TangentSpace I p from (ψ t • (x + φ s • w))) : M) with hFdef
  have hFsmooth : IsSmoothVariation (I := I) F := by
    have hψMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
      rw [contMDiff_iff_contDiff]; exact hψS
    have hφMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ φ := by
      rw [contMDiff_iff_contDiff]; exact hφS
    have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) :=
      (hψMD.comp contMDiff_snd).smul
        (contMDiff_const.add ((hφMD.comp contMDiff_fst).smul contMDiff_const))
    intro q
    have hexp : ContMDiffAt 𝓘(ℝ, E) I (8 : ℕ)
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ((fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) q) := by
      exact (expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) g p
        (hlaunch_norm q.1 q.2)).of_le ENat.LEInfty.out
    have hl8 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (8 : ℕ)
        (fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) q :=
      hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out
    exact hexp.comp q hl8
  have houterL_field : ∀ s : ℝ,
      covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) v (1 : ℝ)) t₀ = 0 := by
    intro s
    exact clamped_slice_covDeriv_velocity_zero (I := I) g p (x + φ s • w)
      (hslice_radius s) ψ hψS hψid t₀ ht₀
  have houterL : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => F s t₀)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0) 0 := by
    have hzero : (chartRepAt (I := I) (fun s : ℝ => F s t₀)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0)
        =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => (0 : E)) := by
      filter_upwards with s
      rw [chartRepAt_apply, houterL_field s]
      exact map_zero _
    exact (hzero.differentiableAt_iff).mpr (differentiableAt_const _)
  have hsymm : ∀ v : ℝ,
      covDerivAlong (I := I) g (fun u : ℝ => F u v)
        (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u' : ℝ => F u u') v (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v :=
    fun v => commute_ds_dt_intrinsic (I := I) g F hFsmooth v
  have hfields : (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F u v)
      (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u' : ℝ => F u u') v (1 : ℝ)) 0)
      = (fun v : ℝ => covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v) :=
    funext hsymm
  have houterR : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => F 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u' : ℝ => F u u') v (1 : ℝ)) 0) t₀) t₀ := by
    rw [hfields]
    exact variationField_covDeriv_chartRep_differentiableAt (I := I) g F hFsmooth t₀
  have hcomm := commute_ds_dt_curvature (I := I) g F hFsmooth t₀ houterL houterR
  have hT1 : covDerivAlong (I := I) g (fun s : ℝ => F s t₀)
      (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0 = 0 := by
    have hfun : (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) v (1 : ℝ)) t₀)
        = (fun s : ℝ => (0 : TangentSpace I ((fun s' : ℝ => F s' t₀) s))) :=
      funext houterL_field
    rw [hfun]
    exact covDerivAlong_zero (I := I) g (fun s' : ℝ => F s' t₀) 0
  rw [hT1, hfields, zero_sub, neg_eq_iff_eq_neg] at hcomm
  set γ : ℝ → M :=
    fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M) with hγdef
  set J : ∀ v : ℝ, TangentSpace I (γ v) := fun v : ℝ =>
    show TangentSpace I (γ v) from
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 (1 : ℝ)
    with hJdef
  have hwin_nhds : ∀ v : ℝ, v ∈ Set.Ioo (-1 : ℝ) 2 → Set.Ioo (-1 : ℝ) 2 ∈ 𝓝 v :=
    fun v hv => isOpen_Ioo.mem_nhds hv
  have ht₀win' : t₀ ∈ Set.Ioo (-1 : ℝ) 2 := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  have hφ0 : φ 0 = 0 := hφid 0 ⟨by norm_num, by norm_num⟩
  have hcentral_eq : ∀ v ∈ Set.Ioo (-1 : ℝ) 2, F 0 v = γ v := by
    intro v hv
    change (expMap (I := I) g p (show TangentSpace I p from (ψ v • (x + φ 0 • w))) : M) = γ v
    rw [hψid v ⟨hv.1.le, hv.2.le⟩, hφ0, zero_smul, add_zero]
  have hcentral_ev : ∀ v ∈ Set.Ioo (-1 : ℝ) 2,
      (fun v' : ℝ => F 0 v') =ᶠ[𝓝 v] γ := by
    intro v hv
    filter_upwards [hwin_nhds v hv] with u hu
    exact hcentral_eq u hu
  have hJ_eq : ∀ v ∈ Set.Ioo (-1 : ℝ) 2,
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0 (1 : ℝ) : E) = (J v : E) := by
    intro v hv
    have hgerm : (fun u : ℝ => F u v) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ =>
          (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)]
        with u hu
      change (expMap (I := I) g p (show TangentSpace I p from (ψ v • (x + φ u • w))) : M) = _
      rw [hψid v ⟨hv.1.le, hv.2.le⟩, hφid u ⟨hu.1.le, hu.2.le⟩]
    have hmf : mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0
        = mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 :=
      hgerm.mfderiv_eq
    rw [hmf]
    rfl
  have hJ_ev : ∀ v ∈ Set.Ioo (-1 : ℝ) 2,
      ∀ᶠ u in 𝓝 v, ((mfderiv (𝓘(ℝ, ℝ)) I (fun u' : ℝ => F u' u) 0 (1 : ℝ) : E)) = (J u : E) := by
    intro v hv
    filter_upwards [hwin_nhds v hv] with u hu
    exact hJ_eq u hu
  have hDJ_ev : ∀ᶠ v in 𝓝 t₀,
      ((covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v : E))
      = ((covDerivAlong (I := I) g γ J v : E)) := by
    filter_upwards [hwin_nhds t₀ ht₀win'] with v hv
    exact covDerivAlong_congr_curve (I := I) g _ _ (hcentral_ev v hv) (hJ_ev v hv)
  have houter_eq : ((covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
      (fun v : ℝ => covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v) t₀ : E))
      = ((covDerivAlong (I := I) g γ
        (fun v : ℝ => covDerivAlong (I := I) g γ J v) t₀ : E)) :=
    covDerivAlong_congr_curve (I := I) g _ _ (hcentral_ev t₀ ht₀win') hDJ_ev
  have hfoot0 : F 0 t₀ = γ t₀ := hcentral_eq t₀ ht₀win'
  have hS_eq : (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u t₀) 0 (1 : ℝ) : E) = (J t₀ : E) :=
    hJ_eq t₀ ht₀win'
  have hT_eq : (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F 0 u) t₀ (1 : ℝ) : E)
      = (curveVelocity (I := I) γ t₀ : E) := by
    have hmf : mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F 0 u) t₀ = mfderiv (𝓘(ℝ, ℝ)) I γ t₀ :=
      (hcentral_ev t₀ ht₀win').mfderiv_eq
    rw [show curveVelocity (I := I) γ t₀ = mfderiv (𝓘(ℝ, ℝ)) I γ t₀ (1 : ℝ) from rfl]
    rw [hmf]
    rfl
  change covDerivAlong (I := I) g γ (fun v : ℝ => covDerivAlong (I := I) g γ J v) t₀
      + (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t₀))
          (J t₀) (curveVelocity (I := I) γ t₀) (curveVelocity (I := I) γ t₀) = 0
  have hfinal : (covDerivAlong (I := I) g γ
      (fun v : ℝ => covDerivAlong (I := I) g γ J v) t₀ : E)
      = - ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t₀))
          (J t₀) (curveVelocity (I := I) γ t₀) (curveVelocity (I := I) γ t₀) : E) := by
    rw [← houter_eq, hcomm]
    rw [hS_eq, hT_eq]
    rw [riemannOp_congr_point (I := I) g hfoot0]
    rfl
  linear_combination (norm := module) hfinal

omit [SigmaCompactSpace M] in
theorem exists_radial_jacobi_radius (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ t₀ ∈ Set.Ioo (0 : ℝ) 1,
      IsJacobiAt (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (fun v : ℝ => show TangentSpace I
            ((expMap (I := I) g p (show TangentSpace I p from (v • x)) : M)) from
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 (1 : ℝ))
        t₀ := by
  refine ⟨jacobiVarRadius (I := I) g p, jacobiVarRadius_pos (I := I) g p, ?_⟩
  intro x w hx hw
  exact radial_jacobi_of_lt (I := I) g p hx hw

open DifferentialGeometry.Geometry.Riemannian.Exponential in
omit [T2Space M] [SigmaCompactSpace M] in
theorem jacobi_diff_of_lt (g : SmoothRiemannianMetric I M) (p : M)
    {x w : E} (hx : ‖x‖ < jacobiVarRadius (I := I) g p)
    (hw : ‖w‖ < jacobiVarRadius (I := I) g p) :
    ∀ {b : ℝ}, b ≤ 1 →
      (∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I)
            (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
            (fun v : ℝ => show TangentSpace I
              ((expMap (I := I) g p (show TangentSpace I p from (v • x)) : M)) from
                mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
                  (expMap (I := I) g p
                    (show TangentSpace I p from (v • (x + s • w))) : M)) 0 (1 : ℝ)) t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I)
            (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
            (fun v : ℝ =>
              covDerivAlong (I := I) g
                (fun u : ℝ => (expMap (I := I) g p
                  (show TangentSpace I p from (u • x)) : M))
                (fun u : ℝ => show TangentSpace I
                  ((expMap (I := I) g p (show TangentSpace I p from (u • x)) : M)) from
                    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
                      (expMap (I := I) g p
                        (show TangentSpace I p from (u • (x + s • w))) : M)) 0 (1 : ℝ)) v) t)
                          t) := by
  classical
  haveI : T2Space M := gauss_t2Space_base (I := I)
  obtain ⟨ψ, hψS, hψid, hψbd⟩ := exists_smooth_clamp (-1) 2 (by norm_num) (by norm_num)
  obtain ⟨φ, hφS, hφid, hφbd⟩ := exists_smooth_clamp (-1) 1 (by norm_num) (by norm_num)
  have hψbd5 : ∀ u : ℝ, |ψ u| ≤ 5 := fun u => (hψbd u).trans (by norm_num)
  have hφbd4 : ∀ u : ℝ, |φ u| ≤ 4 := fun u => (hφbd u).trans (by norm_num)
  set δ : ℝ := expMapC2Radius (I := I) g p
  have hδpos : 0 < δ := by simpa [δ] using expMapC2Radius_pos (I := I) g p
  change ‖x‖ < δ / 26 at hx
  change ‖w‖ < δ / 26 at hw
  intro b hb
  have hslice_norm : ∀ s : ℝ, ‖x + φ s • w‖ < δ / 5 := by
    intro s
    have h1 : ‖x + φ s • w‖ ≤ ‖x‖ + |φ s| * ‖w‖ := by
      calc ‖x + φ s • w‖ ≤ ‖x‖ + ‖φ s • w‖ := norm_add_le _ _
        _ = ‖x‖ + |φ s| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h2 : |φ s| * ‖w‖ ≤ 4 * ‖w‖ :=
      mul_le_mul_of_nonneg_right (hφbd4 s) (norm_nonneg w)
    have hδ26 : ‖x‖ + 4 * ‖w‖ < 5 * (δ / 26) := by linarith [hx, hw, norm_nonneg w]
    have : (5 : ℝ) * (δ / 26) ≤ δ / 5 := by linarith [hδpos]
    linarith
  have hlaunch_norm : ∀ s t : ℝ, ‖ψ t • (x + φ s • w)‖ < δ := by
    intro s t
    have h0 : (0 : ℝ) ≤ ‖x + φ s • w‖ := norm_nonneg _
    calc ‖ψ t • (x + φ s • w)‖ = |ψ t| * ‖x + φ s • w‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 5 * ‖x + φ s • w‖ := mul_le_mul_of_nonneg_right (hψbd5 t) h0
      _ < 5 * (δ / 5) := by
          have := hslice_norm s
          nlinarith
      _ = δ := by ring
  set F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p (show TangentSpace I p from (ψ t • (x + φ s • w))) : M) with hFdef
  have hFsmooth : IsSmoothVariation (I := I) F := by
    have hψMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
      rw [contMDiff_iff_contDiff]; exact hψS
    have hφMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ φ := by
      rw [contMDiff_iff_contDiff]; exact hφS
    have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) :=
      (hψMD.comp contMDiff_snd).smul
        (contMDiff_const.add ((hφMD.comp contMDiff_fst).smul contMDiff_const))
    intro q
    have hexp : ContMDiffAt 𝓘(ℝ, E) I (8 : ℕ)
        (fun a : E => (expMap (I := I) g p (show TangentSpace I p from a) : M))
        ((fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) q) := by
      exact (expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) g p
        (hlaunch_norm q.1 q.2)).of_le ENat.LEInfty.out
    have hl8 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (8 : ℕ)
        (fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) q :=
      hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out
    exact hexp.comp q hl8
  set γ : ℝ → M :=
    fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M) with hγdef
  set J : ∀ v : ℝ, TangentSpace I (γ v) := fun v : ℝ =>
    show TangentSpace I (γ v) from
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 (1 : ℝ)
    with hJdef
  set Vc : ∀ v : ℝ, TangentSpace I ((fun v' : ℝ => F 0 v') v) := fun v : ℝ =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0 (1 : ℝ) with hVcdef
  have hwin_nhds : ∀ v : ℝ, v ∈ Set.Ioo (-1 : ℝ) 2 → Set.Ioo (-1 : ℝ) 2 ∈ 𝓝 v :=
    fun v hv => isOpen_Ioo.mem_nhds hv
  have hφ0 : φ 0 = 0 := hφid 0 ⟨by norm_num, by norm_num⟩
  have hcentral_eq : ∀ v ∈ Set.Ioo (-1 : ℝ) 2, F 0 v = γ v := by
    intro v hv
    change (expMap (I := I) g p (show TangentSpace I p from (ψ v • (x + φ 0 • w))) : M) = γ v
    rw [hψid v ⟨hv.1.le, hv.2.le⟩, hφ0, zero_smul, add_zero]
  have hcentral_ev : ∀ v ∈ Set.Ioo (-1 : ℝ) 2,
      (fun v' : ℝ => F 0 v') =ᶠ[𝓝 v] γ := by
    intro v hv
    filter_upwards [hwin_nhds v hv] with u hu
    exact hcentral_eq u hu
  have hJ_eq : ∀ v ∈ Set.Ioo (-1 : ℝ) 2, (Vc v : E) = (J v : E) := by
    intro v hv
    have hgerm : (fun u : ℝ => F u v) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ =>
          (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)]
        with u hu
      change (expMap (I := I) g p (show TangentSpace I p from (ψ v • (x + φ u • w))) : M) = _
      rw [hψid v ⟨hv.1.le, hv.2.le⟩, hφid u ⟨hu.1.le, hu.2.le⟩]
    have hmf : mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0
        = mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 :=
      hgerm.mfderiv_eq
    rw [hVcdef, hJdef]
    change (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0) (1 : ℝ) =
      (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0) (1 : ℝ)
    rw [hmf]
    rfl
  have hJ_ev : ∀ v ∈ Set.Ioo (-1 : ℝ) 2,
      ∀ᶠ u in 𝓝 v, (Vc u : E) = (J u : E) := by
    intro v hv
    filter_upwards [hwin_nhds v hv] with u hu
    exact hJ_eq u hu
  set Dc : ∀ v : ℝ, TangentSpace I ((fun v' : ℝ => F 0 v') v) := fun v : ℝ =>
    covDerivAlong (I := I) g (fun v' : ℝ => F 0 v') Vc v with hDcdef
  set D : ∀ v : ℝ, TangentSpace I (γ v) := fun v : ℝ =>
    covDerivAlong (I := I) g γ J v with hDdef
  have hD_ev : ∀ v ∈ Set.Ioo (-1 : ℝ) 2,
      ∀ᶠ u in 𝓝 v, (Dc u : E) = (D u : E) := by
    intro v hv
    filter_upwards [hwin_nhds v hv] with u hu
    rw [hDcdef, hDdef]
    exact covDerivAlong_congr_curve (I := I) g _ _ (hcentral_ev u hu) (hJ_ev u hu)
  refine ⟨?_, ?_⟩
  · intro t ht
    have htwin : t ∈ Set.Ioo (-1 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2, hb]⟩
    have hclamped : DifferentiableAt ℝ
        (chartRepAt (I := I) (fun v : ℝ => F 0 v) Vc t) t := by
      rw [hVcdef]
      exact variationField_chartRep_differentiableAt (I := I) g F hFsmooth t
    have hrep : chartRepAt (I := I) (fun v : ℝ => F 0 v) Vc t
        =ᶠ[𝓝 t] chartRepAt (I := I) γ J t :=
      chartRep_congr_curve (I := I) Vc J (hcentral_ev t htwin) (hJ_ev t htwin)
    exact hrep.differentiableAt_iff.mp hclamped
  · intro t ht
    have htwin : t ∈ Set.Ioo (-1 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2, hb]⟩
    have hclamped : DifferentiableAt ℝ
        (chartRepAt (I := I) (fun v : ℝ => F 0 v) Dc t) t := by
      rw [hDcdef, hVcdef]
      exact variationField_covDeriv_chartRep_differentiableAt (I := I) g F hFsmooth t
    have hrep : chartRepAt (I := I) (fun v : ℝ => F 0 v) Dc t
        =ᶠ[𝓝 t] chartRepAt (I := I) γ D t :=
      chartRep_congr_curve (I := I) Dc D (hcentral_ev t htwin) (hD_ev t htwin)
    change DifferentiableAt ℝ (chartRepAt (I := I) γ D t) t
    exact hrep.differentiableAt_iff.mp hclamped

omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_jacobi_diff (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r → ∀ {b : ℝ}, b ≤ 1 →
      (∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I)
            (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
            (fun v : ℝ => show TangentSpace I
              ((expMap (I := I) g p (show TangentSpace I p from (v • x)) : M)) from
                mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
                  (expMap (I := I) g p
                    (show TangentSpace I p from (v • (x + s • w))) : M)) 0 (1 : ℝ)) t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I)
            (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
            (fun v : ℝ =>
              covDerivAlong (I := I) g
                (fun u : ℝ => (expMap (I := I) g p
                  (show TangentSpace I p from (u • x)) : M))
                (fun u : ℝ => show TangentSpace I
                  ((expMap (I := I) g p (show TangentSpace I p from (u • x)) : M)) from
                    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
                      (expMap (I := I) g p
                        (show TangentSpace I p from (u • (x + s • w))) : M)) 0
                          (1 : ℝ)) v) t) t) := by
  refine ⟨jacobiVarRadius (I := I) g p, jacobiVarRadius_pos (I := I) g p, ?_⟩
  intro x w hx hw
  exact jacobi_diff_of_lt (I := I) g p hx hw

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
theorem radial_jacobi_zero (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
      (expMap (I := I) g p (show TangentSpace I p from ((0 : ℝ) • (x + s • w))) : M))
      0 (1 : ℝ) = 0 := by
  have hconst : (fun s : ℝ =>
      (expMap (I := I) g p (show TangentSpace I p from ((0 : ℝ) • (x + s • w))) : M))
      = fun _ : ℝ => p := by
    funext s
    rw [show (show TangentSpace I p from ((0 : ℝ) • (x + s • w))) = (0 : TangentSpace I p) from
      zero_smul ℝ _]
    exact expMap_zero (I := I) g p
  rw [hconst, mfderiv_const]
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem radial_jacobi_one (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) :
    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
      (expMap (I := I) g p (show TangentSpace I p from ((1 : ℝ) • (x + s • w))) : M))
      0 (1 : ℝ)
    = mfderiv (𝓘(ℝ, E)) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x w := by
  have hfoot : (fun s : ℝ => x + s • w) 0 = x := by simp
  have hone : (fun s : ℝ =>
      (expMap (I := I) g p (show TangentSpace I p from ((1 : ℝ) • (x + s • w))) : M))
      = (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ∘ (fun s : ℝ => x + s • w) := by
    funext s
    simp only [Function.comp_apply, one_smul]
  have hexp_md : MDifferentiableAt (𝓘(ℝ, E)) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x :=
    (expMap_contMDiffAt2_of_norm_lt_radius (I := I) g p hx).mdifferentiableAt (by decide)
  have hexp_md' : MDifferentiableAt (𝓘(ℝ, E)) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
      ((fun s : ℝ => x + s • w) 0) := by
    rw [hfoot]
    exact hexp_md
  have hline_md : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun s : ℝ => x + s • w) 0 := by
    have hMD : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (fun s : ℝ => x + s • w) :=
      contMDiff_const.add (contMDiff_id.smul contMDiff_const)
    exact hMD.contMDiffAt.mdifferentiableAt (by decide)
  have hline : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun s : ℝ => x + s • w) 0 (1 : ℝ) = w := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt (fun s : ℝ => x + s • w)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w) 0 := by
      simpa using ((hasFDerivAt_id (0 : ℝ)).smul_const w).const_add x
    rw [h.fderiv]
    change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w) (1 : ℝ) = w
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  have hfootCLM : (mfderiv (𝓘(ℝ, E)) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
      ((fun s : ℝ => x + s • w) 0) : E →L[ℝ] E)
      = (mfderiv (𝓘(ℝ, E)) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x : E →L[ℝ] E) := by
    rw [hfoot]
  rw [hone]
  have hstep := mfderiv_comp_apply (f := fun s : ℝ => x + s • w) (x := (0 : ℝ))
    hexp_md' hline_md (1 : ℝ)
  have hgoal : (mfderiv (𝓘(ℝ, E)) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
      ((fun s : ℝ => x + s • w) 0))
      ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun s : ℝ => x + s • w) 0) (1 : ℝ))
      = (mfderiv (𝓘(ℝ, E)) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x) w := by
    rw [hline]
    exact congrArg (fun L : E →L[ℝ] E => L w) hfootCLM
  exact hstep.trans hgoal

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
/-- At a velocity in the raw exponential domain, the time-one radial variation
has the same derivative as the raw exponential map in the fiber direction. -/
theorem radial_jacobi_dom (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    (hx : (show TangentSpace I p from x) ∈ expDomain (I := I) g p) :
    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
      (expMap (I := I) g p (show TangentSpace I p from ((1 : ℝ) • (x + s • w))) : M))
      0 (1 : ℝ)
    = mfderiv (𝓘(ℝ, E)) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x w := by
  have hfoot : (fun s : ℝ => x + s • w) 0 = x := by simp
  have hone : (fun s : ℝ =>
      (expMap (I := I) g p (show TangentSpace I p from ((1 : ℝ) • (x + s • w))) : M))
      = (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ∘ (fun s : ℝ => x + s • w) := by
    funext s
    simp only [Function.comp_apply, one_smul]
  have hexp_md : MDifferentiableAt (𝓘(ℝ, E)) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x :=
    (expMap_contMDiffAt (I := I) g p hx).mdifferentiableAt (by decide)
  have hexp_md' : MDifferentiableAt (𝓘(ℝ, E)) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
      ((fun s : ℝ => x + s • w) 0) := by
    rw [hfoot]
    exact hexp_md
  have hline_md : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun s : ℝ => x + s • w) 0 := by
    have hMD : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (fun s : ℝ => x + s • w) :=
      contMDiff_const.add (contMDiff_id.smul contMDiff_const)
    exact hMD.contMDiffAt.mdifferentiableAt (by decide)
  have hline : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun s : ℝ => x + s • w) 0 (1 : ℝ) = w := by
    rw [mfderiv_eq_fderiv]
    have h : HasFDerivAt (fun s : ℝ => x + s • w)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w) 0 := by
      simpa using ((hasFDerivAt_id (0 : ℝ)).smul_const w).const_add x
    rw [h.fderiv]
    change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) w) (1 : ℝ) = w
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  have hfootCLM : (mfderiv (𝓘(ℝ, E)) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
      ((fun s : ℝ => x + s • w) 0) : E →L[ℝ] E)
      = (mfderiv (𝓘(ℝ, E)) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x : E →L[ℝ] E) := by
    rw [hfoot]
  rw [hone]
  have hstep := mfderiv_comp_apply (f := fun s : ℝ => x + s • w) (x := (0 : ℝ))
    hexp_md' hline_md (1 : ℝ)
  have hgoal : (mfderiv (𝓘(ℝ, E)) I
      (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
      ((fun s : ℝ => x + s • w) 0))
      ((mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun s : ℝ => x + s • w) 0) (1 : ℝ))
      = (mfderiv (𝓘(ℝ, E)) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x) w := by
    rw [hline]
    exact congrArg (fun L : E →L[ℝ] E => L w) hfootCLM
  exact hstep.trans hgoal

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
    [CompleteSpace E] in
private lemma exists_dom_clamps
    (U : Set E) (hU : IsOpen U) (x w : E) (t₀ : ℝ) (hx : t₀ • x ∈ U) :
    ∃ ψ σ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ σ ∧
      ψ =ᶠ[𝓝 t₀] id ∧ σ =ᶠ[𝓝 (0 : ℝ)] id ∧
      ∀ s t : ℝ, ψ t • (x + σ s • w) ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (t₀ • x) hx
  let C : ℝ := 2 * ‖x‖ + 4 * (|t₀| + 1) * ‖w‖ + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  let δ : ℝ := min (1 / 2 : ℝ) (ε / (2 * C))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hC))
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp only [δ]
    exact min_le_left _ _
  have hδfrac : δ ≤ ε / (2 * C) := by
    dsimp only [δ]
    exact min_le_right _ _
  obtain ⟨ψ, hψ, hψid, _hψderiv, hψrange⟩ :=
    exists_smooth_time_clamp (t₀ - δ) (t₀ + δ) δ (by linarith) hδ
  obtain ⟨φ, hφ, hφid, hφbound⟩ :=
    exists_smooth_clamp (-1) 1 (by norm_num) (by norm_num)
  let σ : ℝ → ℝ := fun s => δ * φ (s / δ)
  have hσ : ContDiff ℝ ∞ σ := by
    dsimp only [σ]
    exact contDiff_const.mul (hφ.comp (contDiff_id.div_const δ))
  have hψev : ψ =ᶠ[𝓝 t₀] id := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show t₀ ∈ Set.Ioo (t₀ - δ) (t₀ + δ) by constructor <;> linarith)] with t ht
    simpa only [id_eq] using hψid t ⟨ht.1.le, ht.2.le⟩
  have hσev : σ =ᶠ[𝓝 (0 : ℝ)] id := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (0 : ℝ) ∈ Set.Ioo (-δ) δ by constructor <;> linarith)] with s hs
    have hsδ : s / δ ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · exact (le_div_iff₀ hδ).2 (by linarith [hs.1])
      · exact (div_le_iff₀ hδ).2 (by linarith [hs.2])
    change δ * φ (s / δ) = id s
    rw [hφid _ hsδ, id_eq]
    field_simp [hδ.ne']
  have hψdist : ∀ t : ℝ, |ψ t - t₀| ≤ 2 * δ := by
    intro t
    rw [abs_le]
    have ht := hψrange t
    constructor <;> linarith [ht.1, ht.2]
  have hψabs : ∀ t : ℝ, |ψ t| ≤ |t₀| + 1 := by
    intro t
    calc
      |ψ t| = |(ψ t - t₀) + t₀| := by ring_nf
      _ ≤ |ψ t - t₀| + |t₀| := abs_add_le _ _
      _ ≤ 2 * δ + |t₀| := add_le_add (hψdist t) le_rfl
      _ ≤ |t₀| + 1 := by linarith
  have hσabs : ∀ s : ℝ, |σ s| ≤ 4 * δ := by
    intro s
    change |δ * φ (s / δ)| ≤ 4 * δ
    rw [abs_mul, abs_of_pos hδ]
    have hφ4 : |φ (s / δ)| ≤ 4 := (hφbound _).trans (by norm_num)
    nlinarith
  have hδC : δ * C ≤ ε / 2 := by
    calc
      δ * C ≤ (ε / (2 * C)) * C := mul_le_mul_of_nonneg_right hδfrac hC.le
      _ = ε / 2 := by field_simp [hC.ne']
  refine ⟨ψ, σ, hψ, hσ, hψev, hσev, ?_⟩
  intro s t
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  have hsplit :
      ψ t • (x + σ s • w) - t₀ • x =
        (ψ t - t₀) • x + (ψ t * σ s) • w := by
    module
  rw [hsplit]
  have hprod : |ψ t * σ s| ≤ (|t₀| + 1) * (4 * δ) := by
    rw [abs_mul]
    exact mul_le_mul (hψabs t) (hσabs s) (abs_nonneg _) (by positivity)
  have hcoef : 2 * ‖x‖ + 4 * (|t₀| + 1) * ‖w‖ < C := by
    dsimp only [C]
    linarith
  have hδcoef :
      δ * (2 * ‖x‖ + 4 * (|t₀| + 1) * ‖w‖) < δ * C :=
    mul_lt_mul_of_pos_left hcoef hδ
  calc
    ‖(ψ t - t₀) • x + (ψ t * σ s) • w‖
        ≤ ‖(ψ t - t₀) • x‖ + ‖(ψ t * σ s) • w‖ := norm_add_le _ _
    _ = |ψ t - t₀| * ‖x‖ + |ψ t * σ s| * ‖w‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (2 * δ) * ‖x‖ + ((|t₀| + 1) * (4 * δ)) * ‖w‖ :=
      add_le_add
        (mul_le_mul_of_nonneg_right (hψdist t) (norm_nonneg x))
        (mul_le_mul_of_nonneg_right hprod (norm_nonneg w))
    _ = δ * (2 * ‖x‖ + 4 * (|t₀| + 1) * ‖w‖) := by ring
    _ < δ * C := hδcoef
    _ ≤ ε / 2 := hδC
    _ < ε := by linarith

omit [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace E] in
private lemma jacobiAt_of_var
    (g : SmoothRiemannianMetric I M) (F : ℝ → ℝ → M)
    (hF : IsSmoothVariation (I := I) F) (t₀ : ℝ)
    (hzero : ∀ s : ℝ,
      covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => F s u) v (1 : ℝ)) t₀ = 0) :
    IsJacobiAt (I := I) g (fun v : ℝ => F 0 v)
      (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
        (fun s : ℝ => F s v) 0 (1 : ℝ)) t₀ := by
  have houterL : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => F s t₀)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0) 0 := by
    have hev : (chartRepAt (I := I) (fun s : ℝ => F s t₀)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0)
        =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => (0 : E)) := by
      filter_upwards with s
      rw [chartRepAt_apply, hzero s]
      exact map_zero _
    exact (hev.differentiableAt_iff).mpr (differentiableAt_const _)
  have hsymm : ∀ v : ℝ,
      covDerivAlong (I := I) g (fun u : ℝ => F u v)
        (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u' : ℝ => F u u') v (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => F u v') 0 (1 : ℝ)) v :=
    fun v => commute_ds_dt_intrinsic (I := I) g F hF v
  have hfields : (fun v : ℝ =>
      covDerivAlong (I := I) g (fun u : ℝ => F u v)
        (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u' : ℝ => F u u') v (1 : ℝ)) 0)
      = (fun v : ℝ =>
        covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
          (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u : ℝ => F u v') 0 (1 : ℝ)) v) :=
    funext hsymm
  have houterR : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => F 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u' : ℝ => F u u') v (1 : ℝ)) 0) t₀) t₀ := by
    rw [hfields]
    exact variationField_covDeriv_chartRep_differentiableAt (I := I) g F hF t₀
  have hcomm := commute_ds_dt_curvature (I := I) g F hF t₀ houterL houterR
  have hT1 : covDerivAlong (I := I) g (fun s : ℝ => F s t₀)
      (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => F s u) v (1 : ℝ)) t₀) 0 = 0 := by
    have hfun : (fun s : ℝ =>
        covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u : ℝ => F s u) v (1 : ℝ)) t₀)
        = (fun s : ℝ => (0 : TangentSpace I (F s t₀))) :=
      funext hzero
    rw [hfun]
    exact covDerivAlong_zero (I := I) g (fun s : ℝ => F s t₀) 0
  rw [hT1, hfields, zero_sub, neg_eq_iff_eq_neg] at hcomm
  change covDerivAlong (I := I) g (fun v : ℝ => F 0 v)
      (fun v : ℝ => covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => F u v') 0 (1 : ℝ)) v) t₀
    + (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (F 0 t₀))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u t₀) 0 (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F 0 u) t₀ (1 : ℝ))
        (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F 0 u) t₀ (1 : ℝ)) = 0
  linear_combination (norm := module) hcomm

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
    [CompleteSpace E] in
private lemma diff_of_subsingle [Subsingleton E] (f : ℝ → E) (t : ℝ) :
    DifferentiableAt ℝ f t := by
  have hf : f = fun _ : ℝ => (0 : E) := funext fun _ => Subsingleton.elim _ _
  rw [hf]
  exact differentiableAt_const _

omit [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
    [CompleteSpace E] in
/-- Along a raw radial segment contained in the exponential domain, radial
variation fields have the differentiability and Jacobi properties used by
local comparison on the closed time interval. -/
private theorem radial_jacobi_on_ne
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {L : ℝ}
    (hdom : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun t =>
      (expMap (I := I) g p (show TangentSpace I p from t • x) : M)
    let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ)
    (∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun u => covDerivAlong (I := I) g γ J u) t) t) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) L, IsJacobiAt (I := I) g γ J t := by
  dsimp only
  let γ : ℝ → M := fun t =>
    (expMap (I := I) g p (show TangentSpace I p from t • x) : M)
  let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
      (expMap (I := I) g p
        (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ)
  let U : Set E := {v | (show TangentSpace I p from v) ∈ expDomain (I := I) g p}
  have hU : IsOpen U := by
    simpa only [U] using isOpen_expDomain (I := I) g p
  have hpoint : ∀ t₀ ∈ Set.Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t₀) t₀ ∧
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun u => covDerivAlong (I := I) g γ J u) t₀) t₀ ∧
      IsJacobiAt (I := I) g γ J t₀ := by
    intro t₀ ht₀
    have ht₀U : t₀ • x ∈ U := by
      simpa only [U] using hdom t₀ ⟨ht₀.1, ht₀.2⟩
    obtain ⟨ψ, σ, hψ, hσ, hψev, hσev, hlaunchU⟩ :=
      exists_dom_clamps U hU x w t₀ ht₀U
    let F : ℝ → ℝ → M := fun s t =>
      (expMap (I := I) g p
        (show TangentSpace I p from ψ t • (x + σ s • w)) : M)
    have hlaunch : ∀ s t : ℝ,
        (show TangentSpace I p from ψ t • (x + σ s • w)) ∈
          expDomain (I := I) g p := by
      intro s t
      simpa only [U] using hlaunchU s t
    have hFsmooth : IsSmoothVariation (I := I) F := by
      have hψMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
        rw [contMDiff_iff_contDiff]
        exact hψ
      have hσMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ := by
        rw [contMDiff_iff_contDiff]
        exact hσ
      have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
          (fun q : ℝ × ℝ => ψ q.2 • (x + σ q.1 • w)) :=
        (hψMD.comp contMDiff_snd).smul
          (contMDiff_const.add ((hσMD.comp contMDiff_fst).smul contMDiff_const))
      intro q
      have hexp : ContMDiffAt 𝓘(ℝ, E) I (8 : ℕ)
          (fun a : E =>
            (expMap (I := I) g p (show TangentSpace I p from a) : M))
          (ψ q.2 • (x + σ q.1 • w)) :=
        (expMap_contMDiffAt (I := I) g p (hlaunch q.1 q.2)).of_le
          ENat.LEInfty.out
      exact hexp.comp q (hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out)
    have hσ0 : σ 0 = 0 := by
      simpa only [id_eq] using hσev.eq_of_nhds
    have hcentral_ev : (fun t : ℝ => F 0 t) =ᶠ[𝓝 t₀] γ := by
      filter_upwards [hψev] with t ht
      change (expMap (I := I) g p
        (show TangentSpace I p from ψ t • (x + σ 0 • w)) : M) = γ t
      rw [ht, hσ0]
      simp only [id_eq, zero_smul, add_zero, γ]
    let Vc : ∀ t : ℝ, TangentSpace I (F 0 t) := fun t =>
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0 (1 : ℝ)
    have hJ_ev : (fun t : ℝ => (Vc t : E)) =ᶠ[𝓝 t₀]
        (fun t : ℝ => (J t : E)) := by
      filter_upwards [hψev] with t ht
      have hgerm : (fun s : ℝ => F s t) =ᶠ[𝓝 (0 : ℝ)]
          (fun s : ℝ =>
            (expMap (I := I) g p
              (show TangentSpace I p from t • (x + s • w)) : M)) := by
        filter_upwards [hσev] with s hs
        change (expMap (I := I) g p
          (show TangentSpace I p from ψ t • (x + σ s • w)) : M) = _
        rw [ht, hs]
        simp only [id_eq]
      have hmf :
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0 =
            mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
              (expMap (I := I) g p
                (show TangentSpace I p from t • (x + s • w)) : M)) 0 :=
        hgerm.mfderiv_eq
      change ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0) (1 : ℝ) : E) =
        ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from t • (x + s • w)) : M)) 0) (1 : ℝ) : E)
      exact congrArg (fun L : ℝ →L[ℝ] TangentSpace I _ => L (1 : ℝ)) hmf
    let Dc : ∀ t : ℝ, TangentSpace I (F 0 t) := fun t =>
      covDerivAlong (I := I) g (fun u : ℝ => F 0 u) Vc t
    let D : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
      covDerivAlong (I := I) g γ J t
    have hD_ev : ∀ᶠ t in 𝓝 t₀, (Dc t : E) = (D t : E) := by
      filter_upwards [hcentral_ev.eventually_nhds, hJ_ev.eventually_nhds]
        with t hcurve hfield
      exact covDerivAlong_congr_curve (I := I) g Vc J hcurve hfield
    have hVdiff : DifferentiableAt ℝ
        (chartRepAt (I := I) γ J t₀) t₀ := by
      have hclamped : DifferentiableAt ℝ
          (chartRepAt (I := I) (fun t : ℝ => F 0 t) Vc t₀) t₀ := by
        exact variationField_chartRep_differentiableAt (I := I) g F hFsmooth t₀
      have hrep := chartRep_congr_curve (I := I) Vc J hcentral_ev hJ_ev
      exact hrep.differentiableAt_iff.mp hclamped
    have hDVdiff : DifferentiableAt ℝ
        (chartRepAt (I := I) γ D t₀) t₀ := by
      have hclamped : DifferentiableAt ℝ
          (chartRepAt (I := I) (fun t : ℝ => F 0 t) Dc t₀) t₀ := by
        exact variationField_covDeriv_chartRep_differentiableAt
          (I := I) g F hFsmooth t₀
      have hrep := chartRep_congr_curve (I := I) Dc D hcentral_ev hD_ev
      exact hrep.differentiableAt_iff.mp hclamped
    have hzero : ∀ s : ℝ,
        covDerivAlong (I := I) g (fun t : ℝ => F s t)
          (fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun u : ℝ => F s u) t (1 : ℝ)) t₀ = 0 := by
      intro s
      let a : E := x + σ s • w
      have hψt₀ : ψ t₀ = t₀ := by
        simpa only [id_eq] using hψev.eq_of_nhds
      have hatdom : (show TangentSpace I p from t₀ • a) ∈
          expDomain (I := I) g p := by
        simpa only [a, hψt₀] using hlaunch s t₀
      have hgeo_raw : HasGeodesicEquationAt (I := I) g
          (fun t : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from t • a) : M)) t₀ :=
        raw_radial_geo_at (I := I) g p (show TangentSpace I p from a) hatdom
      have hF_raw : (fun t : ℝ => F s t) =ᶠ[𝓝 t₀]
          (fun t : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from t • a) : M)) := by
        filter_upwards [hψev] with t ht
        change (expMap (I := I) g p
          (show TangentSpace I p from ψ t • (x + σ s • w)) : M) = _
        rw [ht]
        simp only [id_eq, a]
      have hgeo_F : HasGeodesicEquationAt (I := I) g (fun t : ℝ => F s t) t₀ :=
        HasGeodesicEquationAt.congr_of_eventuallyEq_at
          hF_raw.eq_of_nhds hF_raw hgeo_raw
      have hincl : ContMDiff 𝓘(ℝ, ℝ)
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
          (fun t : ℝ => (s, t)) := contMDiff_const.prodMk contMDiff_id
      have hsliceC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun t : ℝ => F s t) t₀ :=
        ((hFsmooth : ContMDiff _ _ _ _).comp hincl).contMDiffAt.of_le (by norm_num)
      exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
        (I := I) g _ t₀ hsliceC2 hgeo_F
    have hjac_clamped := jacobiAt_of_var (I := I) g F hFsmooth t₀ hzero
    have houter_eq :
        ((covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
          (fun t : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F 0 u) Vc t)
          t₀ : E))
        = ((covDerivAlong (I := I) g γ
          (fun t : ℝ => covDerivAlong (I := I) g γ J t) t₀ : E)) :=
      covDerivAlong_congr_curve (I := I) g Dc D hcentral_ev hD_ev
    have hfoot : F 0 t₀ = γ t₀ := hcentral_ev.eq_of_nhds
    have hfield : (Vc t₀ : E) = (J t₀ : E) := hJ_ev.eq_of_nhds
    have hvelocity :
        (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ (1 : ℝ) : E)
          = (curveVelocity (I := I) γ t₀ : E) := by
      have hmf : mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ =
          mfderiv (𝓘(ℝ, ℝ)) I γ t₀ := hcentral_ev.mfderiv_eq
      exact congrArg (fun L : ℝ →L[ℝ] TangentSpace I _ => (L (1 : ℝ) : E)) hmf
    have hfinal :
        (covDerivAlong (I := I) g γ
          (fun t : ℝ => covDerivAlong (I := I) g γ J t) t₀ : E)
        = -((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t₀))
            (J t₀) (curveVelocity (I := I) γ t₀)
            (curveVelocity (I := I) γ t₀) : E) := by
      rw [← houter_eq]
      change (covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
          (fun t : ℝ => covDerivAlong (I := I) g
            (fun u : ℝ => F 0 u) Vc t) t₀ : E)
        = -((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t₀))
            (J t₀) (curveVelocity (I := I) γ t₀)
            (curveVelocity (I := I) γ t₀) : E)
      have hclamped :
          (covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
            (fun t : ℝ => covDerivAlong (I := I) g
              (fun u : ℝ => F 0 u) Vc t) t₀ : E)
          = -((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (F 0 t₀))
              (Vc t₀)
              (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ (1 : ℝ))
              (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ (1 : ℝ)) : E) := by
        change covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
            (fun t : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F 0 u) Vc t) t₀
          + (DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (F 0 t₀))
              (Vc t₀)
              (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ (1 : ℝ))
              (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ (1 : ℝ)) = 0
          at hjac_clamped
        linear_combination (norm := module) hjac_clamped
      rw [hclamped, hfield, hvelocity]
      rw [riemannOp_congr_point (I := I) g hfoot]
      rfl
    have hJ : IsJacobiAt (I := I) g γ J t₀ := by
      change covDerivAlong (I := I) g γ
          (fun t : ℝ => covDerivAlong (I := I) g γ J t) t₀
        + (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t₀))
            (J t₀) (curveVelocity (I := I) γ t₀)
            (curveVelocity (I := I) γ t₀) = 0
      linear_combination (norm := module) hfinal
    exact ⟨hVdiff, hDVdiff, hJ⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (hpoint t ht).1
  · intro t ht
    exact (hpoint t ht).2.1
  · intro t ht
    exact (hpoint t ht).2.2

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] [CompleteSpace E] in
/-- Along a raw radial segment contained in the exponential domain, radial
variation fields have the differentiability and Jacobi properties used by
local comparison on the open time interval. -/
theorem radial_jacobi_on
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {L : ℝ}
    (hdom : ∀ t ∈ Set.Icc (0 : ℝ) L,
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun t =>
      (expMap (I := I) g p (show TangentSpace I p from t • x) : M)
    let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ)
    (∀ t ∈ Set.Ioo (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) L,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun u => covDerivAlong (I := I) g γ J u) t) t) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) L, IsJacobiAt (I := I) g γ J t := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · letI : Subsingleton E := Module.finrank_zero_iff.1 hdim
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · intro t _
      apply diff_of_subsingle
    · intro t _
      apply diff_of_subsingle
    · intro t _
      unfold IsJacobiAt
      exact @Subsingleton.elim E _ _ _
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    have hclosed := radial_jacobi_on_ne (I := I) g p x w hdom
    dsimp only at hclosed ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      exact hclosed.1 t ⟨ht.1.le, ht.2.le⟩
    · intro t ht
      exact hclosed.2.1 t ⟨ht.1.le, ht.2.le⟩
    · intro t ht
      exact hclosed.2.2 t ⟨ht.1.le, ht.2.le⟩

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] [CompleteSpace E] in
/-- A raw radial Jacobi variation satisfies the Jacobi equation at the pole,
without an ambient completeness assumption. -/
theorem radial_jacobi_at0
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    IsJacobiAt (I := I) g
      (fun t : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from t • x) : M))
      (fun t : ℝ => show TangentSpace I
          (expMap (I := I) g p (show TangentSpace I p from t • x)) from
        mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ))
      0 := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · letI : Subsingleton E := Module.finrank_zero_iff.1 hdim
    unfold IsJacobiAt
    exact @Subsingleton.elim E _ _ _
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    have hdom0 : ∀ t ∈ Set.Icc (0 : ℝ) 0,
        (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p := by
      intro t ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst t
      simpa only [zero_smul] using zero_mem_expDomain (I := I) g p
    have hclosed := radial_jacobi_on_ne (I := I) g p x w hdom0
    exact hclosed.2.2 0 ⟨le_rfl, le_rfl⟩

omit [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
/-- The covariant derivative at the pole of a raw radial Jacobi variation is
the prescribed fiber variation. -/
private theorem radial_jacobi_d0_ne
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    (covDerivAlong (I := I) g
      (fun t : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from t • x) : M))
      (fun t : ℝ => show TangentSpace I
          (expMap (I := I) g p (show TangentSpace I p from t • x)) from
        mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ))
      0 : E) = w := by
  let U : Set E := {v | (show TangentSpace I p from v) ∈ expDomain (I := I) g p}
  have hU : IsOpen U := by
    simpa only [U] using isOpen_expDomain (I := I) g p
  have hzeroU : (0 : ℝ) • x ∈ U := by
    simpa only [U, zero_smul] using zero_mem_expDomain (I := I) g p
  obtain ⟨ψ, σ, hψ, hσ, hψev, hσev, hlaunchU⟩ :=
    exists_dom_clamps U hU x w 0 hzeroU
  let F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p
      (show TangentSpace I p from ψ t • (x + σ s • w)) : M)
  have hlaunch : ∀ s t : ℝ,
      (show TangentSpace I p from ψ t • (x + σ s • w)) ∈
        expDomain (I := I) g p := by
    intro s t
    simpa only [U] using hlaunchU s t
  have hFsmooth : IsSmoothVariation (I := I) F := by
    have hψMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
      rw [contMDiff_iff_contDiff]
      exact hψ
    have hσMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ := by
      rw [contMDiff_iff_contDiff]
      exact hσ
    have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => ψ q.2 • (x + σ q.1 • w)) :=
      (hψMD.comp contMDiff_snd).smul
        (contMDiff_const.add ((hσMD.comp contMDiff_fst).smul contMDiff_const))
    intro q
    have hexp : ContMDiffAt 𝓘(ℝ, E) I (8 : ℕ)
        (fun a : E =>
          (expMap (I := I) g p (show TangentSpace I p from a) : M))
        (ψ q.2 • (x + σ q.1 • w)) :=
      (expMap_contMDiffAt (I := I) g p (hlaunch q.1 q.2)).of_le
        ENat.LEInfty.out
    exact hexp.comp q (hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out)
  let γ : ℝ → M := fun t =>
    (expMap (I := I) g p (show TangentSpace I p from t • x) : M)
  let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
      (expMap (I := I) g p
        (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ)
  have hψ0 : ψ 0 = 0 := by
    simpa only [id_eq] using hψev.eq_of_nhds
  have hσ0 : σ 0 = 0 := by
    simpa only [id_eq] using hσev.eq_of_nhds
  have hcentral_ev : (fun t : ℝ => F 0 t) =ᶠ[𝓝 (0 : ℝ)] γ := by
    filter_upwards [hψev] with t ht
    change (expMap (I := I) g p
      (show TangentSpace I p from ψ t • (x + σ 0 • w)) : M) = γ t
    rw [ht, hσ0]
    simp only [id_eq, zero_smul, add_zero, γ]
  have hJ_ev : (fun t : ℝ =>
      (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0 (1 : ℝ) : E)) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => (J t : E)) := by
    filter_upwards [hψev] with t ht
    have hgerm : (fun s : ℝ => F s t) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from t • (x + s • w)) : M)) := by
      filter_upwards [hσev] with s hs
      change (expMap (I := I) g p
        (show TangentSpace I p from ψ t • (x + σ s • w)) : M) = _
      rw [ht, hs]
      simp only [id_eq]
    have hmf :
        mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0 =
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p
              (show TangentSpace I p from t • (x + s • w)) : M)) 0 :=
      hgerm.mfderiv_eq
    change ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0) (1 : ℝ) : E) =
      ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from t • (x + s • w)) : M)) 0) (1 : ℝ) : E)
    exact congrArg (fun L : ℝ →L[ℝ] TangentSpace I _ => L (1 : ℝ)) hmf
  have hF0 : ∀ s : ℝ, F s 0 = p := by
    intro s
    change (expMap (I := I) g p
      (show TangentSpace I p from ψ 0 • (x + σ s • w)) : M) = p
    rw [hψ0, zero_smul]
    exact expMap_zero (I := I) g p
  have hF0_ev : (fun s : ℝ => F s 0) =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => p) :=
    Filter.Eventually.of_forall hF0
  have hlaunch_vel : ∀ s : ℝ,
      (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F s t) 0 (1 : ℝ) : E)
        = x + σ s • w := by
    intro s
    have hgerm : (fun t : ℝ => F s t) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from t • (x + σ s • w)) : M)) := by
      filter_upwards [hψev] with t ht
      change (expMap (I := I) g p
        (show TangentSpace I p from ψ t • (x + σ s • w)) : M) = _
      rw [ht]
      simp only [id_eq]
    rw [hgerm.mfderiv_eq]
    exact radialCurve_launch_velocity (I := I) g p (x + σ s • w)
  have hlaunch_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F s t) 0 (1 : ℝ) : E)
        = ((show TangentSpace I p from x + σ s • w : E)) :=
    Filter.Eventually.of_forall hlaunch_vel
  have hσderiv : HasDerivAt σ 1 0 :=
    (hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq hσev
  have hline : HasDerivAt (fun s : ℝ => x + σ s • w) w 0 := by
    have h := (hσderiv.smul_const w).const_add x
    simpa using h
  have hLHS := covDerivAlong_congr_curve (I := I) g
    (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
      (fun t : ℝ => F s t) 0 (1 : ℝ))
    (fun s : ℝ => (show TangentSpace I p from x + σ s • w)) hF0_ev hlaunch_ev
  have hconst := covDerivAlong_const (I := I) g p
    (fun s : ℝ => (show TangentSpace I p from x + σ s • w)) 0 hline.differentiableAt
  have hcomm := commute_ds_dt_intrinsic (I := I) g F hFsmooth 0
  have hcomm_E :
      (covDerivAlong (I := I) g (fun s : ℝ => F s 0)
          (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun t : ℝ => F s t) 0 (1 : ℝ)) 0 : E)
        = (covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
          (fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun s : ℝ => F s t) 0 (1 : ℝ)) 0 : E) := by
    rw [hcomm]
  have hRHS := covDerivAlong_congr_curve (I := I) g
    (fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
      (fun s : ℝ => F s t) 0 (1 : ℝ)) J hcentral_ev hJ_ev
  change (covDerivAlong (I := I) g γ J 0 : E) = w
  exact hRHS.symm.trans
    (hcomm_E.symm.trans (hLHS.trans (hconst.trans hline.deriv)))

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
/-- The covariant derivative at the pole of a raw radial Jacobi variation is
the prescribed fiber variation. -/
theorem radial_jacobi_d0
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    (covDerivAlong (I := I) g
      (fun t : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from t • x) : M))
      (fun t : ℝ => show TangentSpace I
          (expMap (I := I) g p (show TangentSpace I p from t • x)) from
        mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ))
      0 : E) = w := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · letI : Subsingleton E := Module.finrank_zero_iff.1 hdim
    exact @Subsingleton.elim E _ _ _
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact radial_jacobi_d0_ne (I := I) g p x w

omit [T2Space M] [SigmaCompactSpace M] [CompleteSpace E] in
/-- At a point in the raw exponential domain, a radial Jacobi variation field
and its covariant derivative have the chart regularity required by interval
arguments. -/
private theorem radial_jacobi_reg_ne
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : ℝ)
    (htx : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun t =>
      (expMap (I := I) g p (show TangentSpace I p from t • x) : M)
    let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ)
    DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t ∧
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun u => covDerivAlong (I := I) g γ J u) t) t := by
  dsimp only
  let U : Set E := {v | (show TangentSpace I p from v) ∈ expDomain (I := I) g p}
  have hU : IsOpen U := by
    simpa only [U] using isOpen_expDomain (I := I) g p
  obtain ⟨ψ, σ, hψ, hσ, hψev, hσev, hlaunchU⟩ :=
    exists_dom_clamps U hU x w t (by simpa only [U] using htx)
  let F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p
      (show TangentSpace I p from ψ t • (x + σ s • w)) : M)
  have hlaunch : ∀ s t : ℝ,
      (show TangentSpace I p from ψ t • (x + σ s • w)) ∈
        expDomain (I := I) g p := by
    intro s t
    simpa only [U] using hlaunchU s t
  have hFsmooth : IsSmoothVariation (I := I) F := by
    have hψMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
      rw [contMDiff_iff_contDiff]
      exact hψ
    have hσMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ := by
      rw [contMDiff_iff_contDiff]
      exact hσ
    have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => ψ q.2 • (x + σ q.1 • w)) :=
      (hψMD.comp contMDiff_snd).smul
        (contMDiff_const.add ((hσMD.comp contMDiff_fst).smul contMDiff_const))
    intro q
    have hexp : ContMDiffAt 𝓘(ℝ, E) I (8 : ℕ)
        (fun a : E =>
          (expMap (I := I) g p (show TangentSpace I p from a) : M))
        (ψ q.2 • (x + σ q.1 • w)) :=
      (expMap_contMDiffAt (I := I) g p (hlaunch q.1 q.2)).of_le
        ENat.LEInfty.out
    exact hexp.comp q (hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out)
  let γ : ℝ → M := fun t =>
    (expMap (I := I) g p (show TangentSpace I p from t • x) : M)
  let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
      (expMap (I := I) g p
        (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ)
  have hσ0 : σ 0 = 0 := by
    simpa only [id_eq] using hσev.eq_of_nhds
  have hcentral_ev : (fun u : ℝ => F 0 u) =ᶠ[𝓝 t] γ := by
    filter_upwards [hψev] with t ht
    change (expMap (I := I) g p
      (show TangentSpace I p from ψ t • (x + σ 0 • w)) : M) = γ t
    rw [ht, hσ0]
    simp only [id_eq, zero_smul, add_zero, γ]
  let Vc : ∀ t : ℝ, TangentSpace I (F 0 t) := fun t =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0 (1 : ℝ)
  have hJ_ev : (fun u : ℝ => (Vc u : E)) =ᶠ[𝓝 t]
      (fun u : ℝ => (J u : E)) := by
    filter_upwards [hψev] with t ht
    have hgerm : (fun s : ℝ => F s t) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from t • (x + s • w)) : M)) := by
      filter_upwards [hσev] with s hs
      change (expMap (I := I) g p
        (show TangentSpace I p from ψ t • (x + σ s • w)) : M) = _
      rw [ht, hs]
      simp only [id_eq]
    have hmf :
        mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0 =
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p
              (show TangentSpace I p from t • (x + s • w)) : M)) 0 :=
      hgerm.mfderiv_eq
    change ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0) (1 : ℝ) : E) =
      ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from t • (x + s • w)) : M)) 0) (1 : ℝ) : E)
    exact congrArg (fun L : ℝ →L[ℝ] TangentSpace I _ => L (1 : ℝ)) hmf
  let Dc : ∀ t : ℝ, TangentSpace I (F 0 t) := fun t =>
    covDerivAlong (I := I) g (fun u : ℝ => F 0 u) Vc t
  let D : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    covDerivAlong (I := I) g γ J t
  have hD_ev : ∀ᶠ u in 𝓝 t, (Dc u : E) = (D u : E) := by
    filter_upwards [hcentral_ev.eventually_nhds, hJ_ev.eventually_nhds]
      with t hcurve hfield
    exact covDerivAlong_congr_curve (I := I) g Vc J hcurve hfield
  constructor
  · have hclamped : DifferentiableAt ℝ
        (chartRepAt (I := I) (fun u : ℝ => F 0 u) Vc t) t :=
      variationField_chartRep_differentiableAt (I := I) g F hFsmooth t
    have hrep := chartRep_congr_curve (I := I) Vc J hcentral_ev hJ_ev
    exact hrep.differentiableAt_iff.mp hclamped
  · have hclamped : DifferentiableAt ℝ
        (chartRepAt (I := I) (fun u : ℝ => F 0 u) Dc t) t :=
      variationField_covDeriv_chartRep_differentiableAt
        (I := I) g F hFsmooth t
    have hrep := chartRep_congr_curve (I := I) Dc D hcentral_ev hD_ev
    exact hrep.differentiableAt_iff.mp hclamped

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
/-- At a point in the raw exponential domain, a radial Jacobi variation field
and its covariant derivative have the chart regularity required by interval
arguments. -/
theorem radial_jacobi_reg
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : ℝ)
    (htx : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun t =>
      (expMap (I := I) g p (show TangentSpace I p from t • x) : M)
    let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ)
    DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t ∧
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun u => covDerivAlong (I := I) g γ J u) t) t := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · letI : Subsingleton E := Module.finrank_zero_iff.1 hdim
    dsimp only
    exact ⟨diff_of_subsingle _ _, diff_of_subsingle _ _⟩
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact radial_jacobi_reg_ne (I := I) g p x w t htx

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
    [CompleteSpace E] in
/-- At the pole, a raw radial Jacobi variation field and its covariant
derivative have the chart regularity required by interval arguments. -/
theorem radial_jacobi_reg0
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    let γ : ℝ → M := fun t =>
      (expMap (I := I) g p (show TangentSpace I p from t • x) : M)
    let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ)
    DifferentiableAt ℝ (chartRepAt (I := I) γ J 0) 0 ∧
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun t => covDerivAlong (I := I) g γ J t) 0) 0 := by
  exact radial_jacobi_reg (I := I) g p x w 0 (by
    simpa only [zero_smul] using zero_mem_expDomain (I := I) g p)

open DifferentialGeometry.Geometry.Riemannian.Exponential in
omit [T2Space M] [SigmaCompactSpace M] in
theorem radial_deriv_of_lt (g : SmoothRiemannianMetric I M) (p : M)
    {x w : E} (hx : ‖x‖ < jacobiVarRadius (I := I) g p)
    (hw : ‖w‖ < jacobiVarRadius (I := I) g p) :
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (fun v : ℝ => show TangentSpace I
            ((expMap (I := I) g p (show TangentSpace I p from (v • x)) : M)) from
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 (1 : ℝ))
        0 : E) = w := by
  classical
  haveI : T2Space M := gauss_t2Space_base (I := I)
  obtain ⟨ψ, hψS, hψid, hψbd⟩ := exists_smooth_clamp (-1) 2 (by norm_num) (by norm_num)
  obtain ⟨φ, hφS, hφid, hφbd⟩ := exists_smooth_clamp (-1) 1 (by norm_num) (by norm_num)
  have hψbd5 : ∀ u : ℝ, |ψ u| ≤ 5 := fun u => (hψbd u).trans (by norm_num)
  have hφbd4 : ∀ u : ℝ, |φ u| ≤ 4 := fun u => (hφbd u).trans (by norm_num)
  set δ : ℝ := expMapC2Radius (I := I) g p
  have hδpos : 0 < δ := by simpa [δ] using expMapC2Radius_pos (I := I) g p
  change ‖x‖ < δ / 26 at hx
  change ‖w‖ < δ / 26 at hw
  have hslice_norm : ∀ s : ℝ, ‖x + φ s • w‖ < δ / 5 := by
    intro s
    have h1 : ‖x + φ s • w‖ ≤ ‖x‖ + |φ s| * ‖w‖ := by
      calc ‖x + φ s • w‖ ≤ ‖x‖ + ‖φ s • w‖ := norm_add_le _ _
        _ = ‖x‖ + |φ s| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h2 : |φ s| * ‖w‖ ≤ 4 * ‖w‖ :=
      mul_le_mul_of_nonneg_right (hφbd4 s) (norm_nonneg w)
    have hδ26 : ‖x‖ + 4 * ‖w‖ < 5 * (δ / 26) := by linarith [hx, hw, norm_nonneg w]
    have : (5 : ℝ) * (δ / 26) ≤ δ / 5 := by linarith [hδpos]
    linarith
  have hlaunch_norm : ∀ s t : ℝ, ‖ψ t • (x + φ s • w)‖ < δ := by
    intro s t
    have h0 : (0 : ℝ) ≤ ‖x + φ s • w‖ := norm_nonneg _
    calc ‖ψ t • (x + φ s • w)‖ = |ψ t| * ‖x + φ s • w‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 5 * ‖x + φ s • w‖ := mul_le_mul_of_nonneg_right (hψbd5 t) h0
      _ < 5 * (δ / 5) := by
          have := hslice_norm s
          nlinarith
      _ = δ := by ring
  set F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p (show TangentSpace I p from (ψ t • (x + φ s • w))) : M) with hFdef
  have hFsmooth : IsSmoothVariation (I := I) F := by
    have hψMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
      rw [contMDiff_iff_contDiff]; exact hψS
    have hφMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ φ := by
      rw [contMDiff_iff_contDiff]; exact hφS
    have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) :=
      (hψMD.comp contMDiff_snd).smul
        (contMDiff_const.add ((hφMD.comp contMDiff_fst).smul contMDiff_const))
    intro q
    have hexp : ContMDiffAt 𝓘(ℝ, E) I (8 : ℕ)
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ((fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) q) := by
      exact (expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) g p
        (hlaunch_norm q.1 q.2)).of_le ENat.LEInfty.out
    have hl8 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (8 : ℕ)
        (fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) q :=
      hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out
    exact hexp.comp q hl8
  set γ : ℝ → M :=
    fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M) with hγdef
  set J : ∀ v : ℝ, TangentSpace I (γ v) := fun v : ℝ =>
    show TangentSpace I (γ v) from
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 (1 : ℝ)
    with hJdef
  have hφ0 : φ 0 = 0 := hφid 0 ⟨by norm_num, by norm_num⟩
  have hcentral_eq : ∀ v ∈ Set.Ioo (-1 : ℝ) 2, F 0 v = γ v := by
    intro v hv
    change (expMap (I := I) g p (show TangentSpace I p from (ψ v • (x + φ 0 • w))) : M) = γ v
    rw [hψid v ⟨hv.1.le, hv.2.le⟩, hφ0, zero_smul, add_zero]
  have hcentral_ev : (fun v : ℝ => F 0 v) =ᶠ[𝓝 (0 : ℝ)] γ := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 2 by norm_num)] with u hu
    exact hcentral_eq u hu
  have hJ_eq : ∀ v ∈ Set.Ioo (-1 : ℝ) 2,
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0 (1 : ℝ) : E) = (J v : E) := by
    intro v hv
    have hgerm : (fun u : ℝ => F u v) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ =>
          (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)]
        with u hu
      change (expMap (I := I) g p (show TangentSpace I p from (ψ v • (x + φ u • w))) : M) = _
      rw [hψid v ⟨hv.1.le, hv.2.le⟩, hφid u ⟨hu.1.le, hu.2.le⟩]
    have hmf : mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0
        = mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 :=
      hgerm.mfderiv_eq
    rw [hmf]
    rfl
  have hJ_ev : ∀ᶠ v in 𝓝 (0 : ℝ),
      ((mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0 (1 : ℝ) : E)) = (J v : E) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 2 by norm_num)] with v hv
    exact hJ_eq v hv
  have hF0 : ∀ s : ℝ, F s 0 = p := by
    intro s
    change (expMap (I := I) g p (show TangentSpace I p from (ψ 0 • (x + φ s • w))) : M) = p
    rw [hψid 0 ⟨by norm_num, by norm_num⟩, zero_smul]
    exact expMap_zero (I := I) g p
  have hF0_ev : (fun s : ℝ => F s 0) =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => p) :=
    Filter.Eventually.of_forall hF0
  have hlaunch : ∀ s : ℝ,
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) 0 (1 : ℝ) : E) = x + φ s • w := by
    intro s
    have hgerm : (fun u : ℝ => F s u) =ᶠ[𝓝 (0 : ℝ)]
        (fun u : ℝ =>
          (expMap (I := I) g p (show TangentSpace I p from (u • (x + φ s • w))) : M)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)]
        with u hu
      change (expMap (I := I) g p (show TangentSpace I p from (ψ u • (x + φ s • w))) : M) = _
      rw [hψid u ⟨hu.1.le, by linarith [hu.2]⟩]
    have hmf : mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) 0
        = mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (u • (x + φ s • w))) : M)) 0 :=
      hgerm.mfderiv_eq
    rw [hmf]
    exact radialCurve_launch_velocity (I := I) g p (x + φ s • w)
  have hlaunch_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      ((mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) 0 (1 : ℝ) : E))
        = ((show TangentSpace I p from (x + φ s • w) : E)) :=
    Filter.Eventually.of_forall hlaunch
  have hφ_ev : φ =ᶠ[𝓝 (0 : ℝ)] id := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)] with u hu
    exact hφid u ⟨hu.1.le, hu.2.le⟩
  have hφderiv : HasDerivAt φ 1 0 := (hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq hφ_ev
  have hHDA : HasDerivAt (fun s : ℝ => x + φ s • w) w 0 := by
    have h2 : HasDerivAt (fun s : ℝ => x + φ s • w) ((1 : ℝ) • w) 0 :=
      (hφderiv.smul_const w).const_add x
    simpa using h2
  have hcomm := commute_ds_dt_intrinsic (I := I) g F hFsmooth 0
  have hRHS := covDerivAlong_congr_curve (I := I) g
    (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0 (1 : ℝ)) J hcentral_ev hJ_ev
  have hLHS := covDerivAlong_congr_curve (I := I) g
    (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) 0 (1 : ℝ))
    (fun s : ℝ => (show TangentSpace I p from (x + φ s • w))) hF0_ev hlaunch_ev
  have hdiff : DifferentiableAt ℝ
      (fun s : ℝ => ((show TangentSpace I p from (x + φ s • w)) : E)) 0 := hHDA.differentiableAt
  have hconst := covDerivAlong_const (I := I) g p
    (fun s : ℝ => (show TangentSpace I p from (x + φ s • w))) 0 hdiff
  have hderiv : deriv (fun s : ℝ => ((show TangentSpace I p from (x + φ s • w)) : E)) 0 = w :=
    hHDA.deriv
  have hcomm_E :
      (covDerivAlong (I := I) g (fun s : ℝ => F s 0)
          (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) 0 (1 : ℝ)) 0 : E)
        = (covDerivAlong (I := I) g (fun v : ℝ => F 0 v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0 (1 : ℝ)) 0 : E) := by
    rw [hcomm]
  exact hRHS.symm.trans (hcomm_E.symm.trans (hLHS.trans (hconst.trans hderiv)))

omit [T2Space M] [SigmaCompactSpace M] in
theorem exists_radial_jacobi_deriv_radius (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      (covDerivAlong (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (fun v : ℝ => show TangentSpace I
            ((expMap (I := I) g p (show TangentSpace I p from (v • x)) : M)) from
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 (1 : ℝ))
        0 : E) = w := by
  refine ⟨jacobiVarRadius (I := I) g p, jacobiVarRadius_pos (I := I) g p, ?_⟩
  intro x w hx hw
  exact radial_deriv_of_lt (I := I) g p hx hw

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem jacobi_zero_of_lt
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {x w : E}
    (hx : ‖x‖ < jacobiVarRadius (I := I) g p)
    (hw : ‖w‖ < jacobiVarRadius (I := I) g p) :
      IsJacobiAt (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (fun v : ℝ => show TangentSpace I
            ((expMap (I := I) g p (show TangentSpace I p from (v • x)) : M)) from
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0
              (1 : ℝ))
        0 := by
  classical
  haveI : T2Space M := gauss_t2Space_base (I := I)
  obtain ⟨ψ, hψS, hψid, hψbd⟩ := exists_smooth_clamp (-1) 2 (by norm_num) (by norm_num)
  obtain ⟨φ, hφS, hφid, hφbd⟩ := exists_smooth_clamp (-1) 1 (by norm_num) (by norm_num)
  have hψbd5 : ∀ u : ℝ, |ψ u| ≤ 5 := fun u => (hψbd u).trans (by norm_num)
  have hφbd4 : ∀ u : ℝ, |φ u| ≤ 4 := fun u => (hφbd u).trans (by norm_num)
  set δ : ℝ := expMapC2Radius (I := I) g p
  have hδpos : 0 < δ := by simpa [δ] using expMapC2Radius_pos (I := I) g p
  change ‖x‖ < δ / 26 at hx
  change ‖w‖ < δ / 26 at hw
  have hslice_norm : ∀ s : ℝ, ‖x + φ s • w‖ < δ / 5 := by
    intro s
    have h1 : ‖x + φ s • w‖ ≤ ‖x‖ + |φ s| * ‖w‖ := by
      calc ‖x + φ s • w‖ ≤ ‖x‖ + ‖φ s • w‖ := norm_add_le _ _
        _ = ‖x‖ + |φ s| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h2 : |φ s| * ‖w‖ ≤ 4 * ‖w‖ :=
      mul_le_mul_of_nonneg_right (hφbd4 s) (norm_nonneg w)
    have hδ26 : ‖x‖ + 4 * ‖w‖ < 5 * (δ / 26) := by linarith [hx, hw, norm_nonneg w]
    have : (5 : ℝ) * (δ / 26) ≤ δ / 5 := by linarith [hδpos]
    linarith
  have hlaunch_norm : ∀ s t : ℝ, ‖ψ t • (x + φ s • w)‖ < δ := by
    intro s t
    have h0 : (0 : ℝ) ≤ ‖x + φ s • w‖ := norm_nonneg _
    calc ‖ψ t • (x + φ s • w)‖ = |ψ t| * ‖x + φ s • w‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 5 * ‖x + φ s • w‖ := mul_le_mul_of_nonneg_right (hψbd5 t) h0
      _ < 5 * (δ / 5) := by
          have := hslice_norm s
          nlinarith
      _ = δ := by ring
  set F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p (show TangentSpace I p from (ψ t • (x + φ s • w))) : M) with hFdef
  have hFsmooth : IsSmoothVariation (I := I) F := by
    have hψMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
      rw [contMDiff_iff_contDiff]; exact hψS
    have hφMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ φ := by
      rw [contMDiff_iff_contDiff]; exact hφS
    have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) :=
      (hψMD.comp contMDiff_snd).smul
        (contMDiff_const.add ((hφMD.comp contMDiff_fst).smul contMDiff_const))
    intro q
    have hexp : ContMDiffAt 𝓘(ℝ, E) I (8 : ℕ)
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M))
        ((fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) q) := by
      exact (expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) g p
        (hlaunch_norm q.1 q.2)).of_le ENat.LEInfty.out
    have hl8 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (8 : ℕ)
        (fun q : ℝ × ℝ => ψ q.2 • (x + φ q.1 • w)) q :=
      hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out
    exact hexp.comp q hl8
  have houterL_field : ∀ s : ℝ,
      covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) v (1 : ℝ)) 0 = 0 := by
    intro s
    exact clamped_slice_covDeriv_velocity_zero_at_zero
      (I := I) g hEnorm p (x + φ s • w) ψ hψid
  have houterL : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun s : ℝ => F s 0)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) v (1 : ℝ)) 0) 0) 0 := by
    have hzero : (chartRepAt (I := I) (fun s : ℝ => F s 0)
        (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
          (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) v (1 : ℝ)) 0) 0)
        =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => (0 : E)) := by
      filter_upwards with s
      rw [chartRepAt_apply, houterL_field s]
      exact map_zero _
    exact (hzero.differentiableAt_iff).mpr (differentiableAt_const _)
  have hsymm : ∀ v : ℝ,
      covDerivAlong (I := I) g (fun u : ℝ => F u v)
        (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u' : ℝ => F u u') v (1 : ℝ)) 0
      = covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v :=
    fun v => commute_ds_dt_intrinsic (I := I) g F hFsmooth v
  have hfields : (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F u v)
      (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u' : ℝ => F u u') v (1 : ℝ)) 0)
      = (fun v : ℝ => covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v) :=
    funext hsymm
  have houterR : DifferentiableAt ℝ
      (chartRepAt (I := I) (fun v : ℝ => F 0 v)
        (fun v : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F u v)
          (fun u : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u' : ℝ => F u u') v (1 : ℝ)) 0) 0) 0 := by
    rw [hfields]
    exact variationField_covDeriv_chartRep_differentiableAt (I := I) g F hFsmooth 0
  have hcomm := commute_ds_dt_curvature (I := I) g F hFsmooth 0 houterL houterR
  have hT1 : covDerivAlong (I := I) g (fun s : ℝ => F s 0)
      (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) v (1 : ℝ)) 0) 0 = 0 := by
    have hfun : (fun s : ℝ => covDerivAlong (I := I) g (fun v : ℝ => F s v)
        (fun v : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F s u) v (1 : ℝ)) 0)
        = (fun s : ℝ => (0 : TangentSpace I ((fun s' : ℝ => F s' 0) s))) :=
      funext houterL_field
    rw [hfun]
    exact covDerivAlong_zero (I := I) g (fun s' : ℝ => F s' 0) 0
  rw [hT1, hfields, zero_sub, neg_eq_iff_eq_neg] at hcomm
  set γ : ℝ → M :=
    fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M) with hγdef
  set J : ∀ v : ℝ, TangentSpace I (γ v) := fun v : ℝ =>
    show TangentSpace I (γ v) from
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 (1 : ℝ)
    with hJdef
  have hwin_nhds : ∀ v : ℝ, v ∈ Set.Ioo (-1 : ℝ) 2 → Set.Ioo (-1 : ℝ) 2 ∈ 𝓝 v :=
    fun v hv => isOpen_Ioo.mem_nhds hv
  have h0win : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 2 := by norm_num
  have hφ0 : φ 0 = 0 := hφid 0 ⟨by norm_num, by norm_num⟩
  have hcentral_eq : ∀ v ∈ Set.Ioo (-1 : ℝ) 2, F 0 v = γ v := by
    intro v hv
    change (expMap (I := I) g p (show TangentSpace I p from (ψ v • (x + φ 0 • w))) : M) = γ v
    rw [hψid v ⟨hv.1.le, hv.2.le⟩, hφ0, zero_smul, add_zero]
  have hcentral_ev : ∀ v ∈ Set.Ioo (-1 : ℝ) 2,
      (fun v' : ℝ => F 0 v') =ᶠ[𝓝 v] γ := by
    intro v hv
    filter_upwards [hwin_nhds v hv] with u hu
    exact hcentral_eq u hu
  have hJ_eq : ∀ v ∈ Set.Ioo (-1 : ℝ) 2,
      (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0 (1 : ℝ) : E) = (J v : E) := by
    intro v hv
    have hgerm : (fun u : ℝ => F u v) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ =>
          (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 by norm_num)]
        with u hu
      change (expMap (I := I) g p (show TangentSpace I p from (ψ v • (x + φ u • w))) : M) = _
      rw [hψid v ⟨hv.1.le, hv.2.le⟩, hφid u ⟨hu.1.le, hu.2.le⟩]
    have hmf : mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v) 0
        = mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0 :=
      hgerm.mfderiv_eq
    rw [hmf]
    rfl
  have hJ_ev : ∀ v ∈ Set.Ioo (-1 : ℝ) 2,
      ∀ᶠ u in 𝓝 v, ((mfderiv (𝓘(ℝ, ℝ)) I (fun u' : ℝ => F u' u) 0 (1 : ℝ) : E)) = (J u : E) := by
    intro v hv
    filter_upwards [hwin_nhds v hv] with u hu
    exact hJ_eq u hu
  have hDJ_ev : ∀ᶠ v in 𝓝 (0 : ℝ),
      ((covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v : E))
      = ((covDerivAlong (I := I) g γ J v : E)) := by
    filter_upwards [hwin_nhds 0 h0win] with v hv
    exact covDerivAlong_congr_curve (I := I) g _ _ (hcentral_ev v hv) (hJ_ev v hv)
  have houter_eq : ((covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
      (fun v : ℝ => covDerivAlong (I := I) g (fun v' : ℝ => F 0 v')
        (fun v' : ℝ => mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u v') 0 (1 : ℝ)) v) 0 : E))
      = ((covDerivAlong (I := I) g γ
        (fun v : ℝ => covDerivAlong (I := I) g γ J v) 0 : E)) :=
    covDerivAlong_congr_curve (I := I) g _ _ (hcentral_ev 0 h0win) hDJ_ev
  have hfoot0 : F 0 0 = γ 0 := hcentral_eq 0 h0win
  have hS_eq : (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F u 0) 0 (1 : ℝ) : E) = (J 0 : E) :=
    hJ_eq 0 h0win
  have hT_eq : (mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F 0 u) 0 (1 : ℝ) : E)
      = (curveVelocity (I := I) γ 0 : E) := by
    have hmf : mfderiv (𝓘(ℝ, ℝ)) I (fun u : ℝ => F 0 u) 0 = mfderiv (𝓘(ℝ, ℝ)) I γ 0 :=
      (hcentral_ev 0 h0win).mfderiv_eq
    rw [show curveVelocity (I := I) γ 0 = mfderiv (𝓘(ℝ, ℝ)) I γ 0 (1 : ℝ) from rfl]
    rw [hmf]
    rfl
  change covDerivAlong (I := I) g γ (fun v : ℝ => covDerivAlong (I := I) g γ J v) 0
      + (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ 0))
          (J 0) (curveVelocity (I := I) γ 0) (curveVelocity (I := I) γ 0) = 0
  have hfinal : (covDerivAlong (I := I) g γ
      (fun v : ℝ => covDerivAlong (I := I) g γ J v) 0 : E)
      = - ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ 0))
          (J 0) (curveVelocity (I := I) γ 0) (curveVelocity (I := I) γ 0) : E) := by
    rw [← houter_eq, hcomm]
    rw [hS_eq, hT_eq]
    rw [riemannOp_congr_point (I := I) g hfoot0]
    rfl
  linear_combination (norm := module) hfinal

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem exists_jacobi_zero
    [PseudoEMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : E, ‖x‖ < r → ‖w‖ < r →
      IsJacobiAt (I := I) g
        (fun v : ℝ => (expMap (I := I) g p (show TangentSpace I p from (v • x)) : M))
        (fun v : ℝ => show TangentSpace I
            ((expMap (I := I) g p (show TangentSpace I p from (v • x)) : M)) from
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p (show TangentSpace I p from (v • (x + s • w))) : M)) 0
              (1 : ℝ))
        0 := by
  refine ⟨jacobiVarRadius (I := I) g p, jacobiVarRadius_pos (I := I) g p, ?_⟩
  intro x w hx hw
  exact jacobi_zero_of_lt (I := I) g hEnorm p hx hw

end Riemannian
end Geometry
end DifferentialGeometry

end
