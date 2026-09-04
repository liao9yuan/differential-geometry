import DifferentialGeometry.Analysis.ODE.IndexFormNegativeSmooth
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrameIndex
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariationMinimiser
import DifferentialGeometry.Geometry.Comparison.Variation.VariationFieldSmooth
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint
import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth
import DifferentialGeometry.Geometry.Exponential.Smoothness.RadialGeodesic
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff RealInnerProductSpace Bundle

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
private lemma raw_time_clamp
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    {L : ℝ} (hL : 0 < L)
    (hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧
      (∀ t : ℝ, (show TangentSpace I p from ρ t • u) ∈ expDomain (I := I) g p) ∧
      ∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) L ⊆ O ∧ Set.EqOn ρ id O := by
  let U : Set ℝ := {t | (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p}
  have hU : IsOpen U := by
    exact (isOpen_expDomain (I := I) g p).preimage
      (continuous_id.smul continuous_const)
  have hseg : Icc (0 : ℝ) L ⊆ U := fun t ht => hdom t ht
  obtain ⟨margin, hmargin, hbuffer⟩ :=
    isCompact_Icc.exists_cthickening_subset_open hU hseg
  let a : ℝ := -(margin / 2)
  let d : ℝ := L + margin / 2
  let eps : ℝ := margin / 4
  have ha0 : a < 0 := by dsimp only [a]; linarith
  have hLd : L < d := by dsimp only [d]; linarith
  have had : a < d := lt_trans ha0 (hL.trans hLd)
  have heps : 0 < eps := by dsimp only [eps]; linarith
  obtain ⟨ρ, hρ, hρ_id, _hρ_deriv, hρ_range⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp a d eps had heps
  have hρU : ∀ s : ℝ, ρ s ∈ U := by
    intro s
    apply hbuffer
    by_cases hs0 : ρ s ≤ 0
    · refine Metric.mem_cthickening_of_dist_le (ρ s) 0 margin
        (Icc (0 : ℝ) L) ⟨le_rfl, hL.le⟩ ?_
      rw [Real.dist_eq, sub_zero, abs_of_nonpos hs0]
      have hlo := (hρ_range s).1
      dsimp only [a, eps] at hlo
      linarith
    · by_cases hsL : ρ s ≤ L
      · refine Metric.mem_cthickening_of_dist_le (ρ s) (ρ s) margin
          (Icc (0 : ℝ) L) ⟨(not_le.mp hs0).le, hsL⟩ ?_
        simpa using hmargin.le
      · refine Metric.mem_cthickening_of_dist_le (ρ s) L margin
          (Icc (0 : ℝ) L) ⟨hL.le, le_rfl⟩ ?_
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (not_le.mp hsL).le)]
        have hhi := (hρ_range s).2
        dsimp only [d, eps] at hhi
        linarith
  refine ⟨ρ, hρ, fun t => hρU t, Ioo a d, isOpen_Ioo, ?_, ?_⟩
  · intro t ht
    exact ⟨lt_of_lt_of_le ha0 ht.1, lt_of_le_of_lt ht.2 hLd⟩
  · intro t ht
    simpa only [id_eq] using hρ_id t ⟨ht.1.le, ht.2.le⟩

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
private lemma riemann_self_zero
    (g : SmoothRiemannianMetric I M) (q : M) (v : TangentSpace I q) :
    (DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) q) v v v = 0 := by
  have hswap := DifferentialGeometry.Geometry.Curvature.riemannOp_swap
    (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) q v v v
  have hsum :
      (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) q) v v v +
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) q) v v v = 0 :=
    eq_neg_iff_add_eq_zero.mp hswap
  have htwo :
      (2 : ℝ) •
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) q) v v v = 0 := by
    rw [two_smul]
    exact hsum
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private lemma jacobi_perp_Ioo
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t))
    {L c : ℝ} (hL : 0 < L) (hc : c ∈ Ioo (0 : ℝ) L)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) L))
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) L, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hJac : ∀ t ∈ Ioo (0 : ℝ) L, IsJacobiAt (I := I) g γ J t)
    (hJ0 : J 0 = 0) (hJc : J c = 0) :
    (∀ t ∈ Icc (0 : ℝ) L,
      g.inner (γ t) (J t) (curveVelocity (I := I) γ t) = 0) ∧
      g.inner (γ 0) (covDerivAlong (I := I) g γ J 0)
        (curveVelocity (I := I) γ 0) = 0 := by
  let f : ℝ → ℝ := fun t =>
    g.inner (γ t) (curveVelocity (I := I) γ t) (J t)
  let q : ℝ → ℝ := fun t =>
    g.inner (γ t) (curveVelocity (I := I) γ t)
      (covDerivAlong (I := I) g γ J t)
  have hveldiff (t : ℝ) : DifferentiableAt ℝ
      (chartRepAt (I := I) γ (curveVelocity (I := I) γ) t) t := by
    simpa only [curveVelocity] using
      velocity_chartRepAt_differentiableAt (I := I) γ hγ t
  have hvelpar (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) t = 0 :=
    (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
      (I := I) g γ t hγ).mpr (hgeo.hasGeodesicEquationAt ht)
  have hcurvzero (t : ℝ) :
      g.inner (γ t) (curveVelocity (I := I) γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (γ t))
          (J t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t)) = 0 := by
    calc
      g.inner (γ t) (curveVelocity (I := I) γ t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
              (γ t))
            (J t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t)) =
        g.inner (γ t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
              (γ t))
            (J t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t))
          (curveVelocity (I := I) γ t) := g.symm (γ t) _ _
      _ = g.inner (γ t) (J t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
              (γ t))
            (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t)) :=
        DifferentialGeometry.Geometry.Curvature.riemannOp_diag_symm
          (I := I) g (γ t) (curveVelocity (I := I) γ t) (J t)
          (curveVelocity (I := I) γ t)
      _ = 0 := by rw [riemann_self_zero (I := I) g, map_zero]
  have hfderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      HasDerivAt f (q t) t := by
    have h := inner_deriv_at (I := I) (n := ∞) (by simp) g γ
      (curveVelocity (I := I) γ) J t hγ.contMDiffAt
      (hveldiff t) (hJdiff t ht)
    rw [hvelpar t ht] at h
    simpa only [f, q, map_zero, ContinuousLinearMap.zero_apply,
      zero_add] using h
  have hqdiff (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      DifferentiableAt ℝ q t := by
    exact (inner_deriv_at (I := I) (n := ∞) (by simp) g γ
      (curveVelocity (I := I) γ)
      (fun s => covDerivAlong (I := I) g γ J s) t hγ.contMDiffAt
      (hveldiff t) (hDJdiff t ht)).differentiableAt
  have hqderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) L) : HasDerivAt q 0 t := by
    have h := inner_deriv_at (I := I) (n := ∞) (by simp) g γ
      (curveVelocity (I := I) γ)
      (fun s => covDerivAlong (I := I) g γ J s) t hγ.contMDiffAt
      (hveldiff t) (hDJdiff t ⟨ht.1.le, ht.2.le⟩)
    rw [hvelpar t ⟨ht.1.le, ht.2.le⟩,
      jacobi_d2_eq (I := I) g γ J (hJac t ht)] at h
    simpa only [q, map_zero, ContinuousLinearMap.zero_apply, zero_add,
      map_neg, ContinuousLinearMap.neg_apply, hcurvzero t, neg_zero] using h
  have hqcont : ContinuousOn q (Icc (0 : ℝ) L) :=
    fun t ht => (hqdiff t ht).continuousAt.continuousWithinAt
  have hqeq : Set.EqOn q (fun _ => q c) (Ioo (0 : ℝ) L) := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s hs => (hqderiv s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hqderiv s hs).deriv) ht hc
  have hqeq_closed : Set.EqOn q (fun _ => q c) (Icc (0 : ℝ) L) :=
    hqeq.of_subset_closure hqcont continuousOn_const Ioo_subset_Icc_self (by
      rw [closure_Ioo hL.ne])
  let r : ℝ → ℝ := fun t => f t - t * q c
  have hrderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) L) : HasDerivAt r 0 t := by
    have hf := hfderiv t ⟨ht.1.le, ht.2.le⟩
    rw [hqeq_closed ⟨ht.1.le, ht.2.le⟩] at hf
    simpa only [r, sub_self] using hf.sub (hasDerivAt_mul_const (q c))
  have hfcont : ContinuousOn f (Icc (0 : ℝ) L) :=
    fun t ht => (hfderiv t ht).continuousAt.continuousWithinAt
  have hrcont : ContinuousOn r (Icc (0 : ℝ) L) := by
    exact hfcont.sub (continuousOn_id.mul continuousOn_const)
  have hreq : Set.EqOn r (fun _ => r c) (Ioo (0 : ℝ) L) := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s hs => (hrderiv s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hrderiv s hs).deriv) ht hc
  have hreq_closed : Set.EqOn r (fun _ => r c) (Icc (0 : ℝ) L) :=
    hreq.of_subset_closure hrcont continuousOn_const Ioo_subset_Icc_self (by
      rw [closure_Ioo hL.ne])
  have hf0 : f 0 = 0 := by simp only [f, hJ0, map_zero]
  have hfc : f c = 0 := by simp only [f, hJc, map_zero]
  have hqc : q c = 0 := by
    have hrc0 := hreq_closed (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL.le⟩)
    have hmul : c * q c = 0 := by
      dsimp only [r] at hrc0
      rw [hf0, hfc, zero_mul, sub_zero, zero_sub] at hrc0
      exact neg_eq_zero.mp hrc0.symm
    exact (mul_eq_zero.mp hmul).resolve_left hc.1.ne'
  constructor
  · intro t ht
    have hrt := hreq_closed ht
    dsimp only [r] at hrt
    simp only [hqc, mul_zero, sub_zero, hfc] at hrt
    calc
      g.inner (γ t) (J t) (curveVelocity (I := I) γ t) = f t :=
        g.symm (γ t) _ _
      _ = 0 := hrt
  · have hq0 := hqeq_closed (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL.le⟩)
    rw [hqc] at hq0
    dsimp only [q] at hq0
    rw [g.symm]
    exact hq0

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A minimizing raw radial segment has nonsingular exponential differential at
every interior point. -/
theorem raw_exp_inj_of_min
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (p : M) (u : E)
    (hunit : g.inner p u u = 1)
    (L : ℝ) (hL : 0 < L)
    (hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = p →
      η L = expMap (I := I) g p (show TangentSpace I p from L • u) →
      arcLength (I := I) g
          (fun t : ℝ =>
            (expMap (I := I) g p
              (show TangentSpace I p from t • u) : M)) 0 L ≤
        arcLength (I := I) g η 0 L)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) L) :
    Function.Injective
      (mfderiv 𝓘(ℝ, E) I
        (fun v : E =>
          (expMap (I := I) g p (show TangentSpace I p from v) : M))
        (c • u)) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  change E at z
  by_contra hz_ne
  let rawExp : E → M := fun v =>
    (expMap (I := I) g p (show TangentSpace I p from v) : M)
  let γr : ℝ → M := fun t => rawExp (t • u)
  let Jr : ∀ t : ℝ, TangentSpace I (γr t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => rawExp (t • (u + s • z))) 0 (1 : ℝ)
  let Dr : ∀ t : ℝ, TangentSpace I (γr t) := fun t =>
    covDerivAlong (I := I) g γr Jr t
  have hJr0 : Jr 0 = 0 := by
    simpa only [Jr, γr, rawExp] using
      radial_jacobi_zero (I := I) g p u z
  have hJrc : Jr c = 0 := by
    have hcdom : (show TangentSpace I p from c • u) ∈ expDomain (I := I) g p :=
      hdom c ⟨hc.1.le, hc.2.le⟩
    have hpath :
        (fun s : ℝ => rawExp (c • (u + s • z))) =
          fun s : ℝ => rawExp ((1 : ℝ) • (c • u + s • (c • z))) := by
      funext s
      congr 1
      module
    change (mfderiv 𝓘(ℝ, ℝ) I
      (fun s : ℝ => rawExp (c • (u + s • z))) 0 (1 : ℝ) : E) = 0
    rw [hpath]
    have hrad := radial_jacobi_dom (I := I) g p (c • u) (c • z) hcdom
    have hradE := congrArg (fun w => (w : E)) hrad
    have hradE' :
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun s : ℝ => rawExp ((1 : ℝ) • (c • u + s • (c • z))))
          0 (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, E) I rawExp (c • u) (c • z) : E) := by
      simpa only [rawExp] using hradE
    calc
      _ = (mfderiv 𝓘(ℝ, E) I rawExp (c • u) (c • z) : E) := hradE'
      _ = c • (mfderiv 𝓘(ℝ, E) I rawExp (c • u) z : E) :=
        ContinuousLinearMap.map_smul _ c z
      _ = 0 := by
        have hz' : (mfderiv 𝓘(ℝ, E) I rawExp (c • u) z : E) = 0 := by
          simpa only [rawExp] using hz
        rw [hz', smul_zero]
  obtain ⟨ρ, hρ, hρdom, O, hO, hsegO, hρO⟩ :=
    raw_time_clamp (I := I) g p u hL hdom
  let f : ℝ → ℝ → M := fun s t => rawExp (ρ t • (u + s • z))
  let γ : ℝ → M := fun t => f 0 t
  let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s t) 0 (1 : ℝ)
  let DJ : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    covDerivAlong (I := I) g γ J t
  have hρMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ρ := by
    rw [contMDiff_iff_contDiff]
    exact hρ
  have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × ℝ => ρ q.2 • (u + q.1 • z)) :=
    (hρMD.comp contMDiff_snd).smul
      (contMDiff_const.add (contMDiff_fst.smul contMDiff_const))
  have hf_at (t : ℝ) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : ℝ × ℝ => f q.1 q.2) (0, t) := by
    have hexp := expMap_contMDiffAt (I := I) g p (hρdom t)
    have hexp' : ContMDiffAt 𝓘(ℝ, E) I ∞ rawExp
        (ρ ((0 : ℝ), t).2 • (u + ((0 : ℝ), t).1 • z)) := by
      simpa only [rawExp, Prod.fst, Prod.snd, zero_smul, add_zero] using hexp
    have hcomp := hexp'.comp ((0 : ℝ), t) hlaunchMD.contMDiffAt
    simpa only [f] using hcomp
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
    intro t
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => ((0 : ℝ), s)) t :=
      contMDiffAt_const.prodMk contMDiffAt_id
    simpa only [γ, Function.comp_apply] using (hf_at t).comp t hincl
  have hJ_bundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (J t)) := by
    intro t
    simpa only [γ, J] using varField_smoothAt (I := I) f (hf_at t)
  have hρ_ev (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) : ρ =ᶠ[𝓝 t] id :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds (hsegO ht)) fun s hs => hρO hs
  have hγ_ev (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) : γ =ᶠ[𝓝 t] γr := by
    filter_upwards [hρ_ev t ht] with s hs
    simp only [γ, f, γr, zero_smul, add_zero, id_eq] at hs ⊢
    rw [hs]
  have hJ_ev (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      (fun s => (J s : E)) =ᶠ[𝓝 t] fun s => (Jr s : E) := by
    filter_upwards [hρ_ev t ht] with s hs
    change (mfderiv 𝓘(ℝ, ℝ) I
      (fun a : ℝ => rawExp (ρ s • (u + a • z))) 0 (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun a : ℝ => rawExp (s • (u + a • z))) 0 (1 : ℝ) : E)
    rw [hs]
    rfl
  have hD_ev (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      (fun s => (DJ s : E)) =ᶠ[𝓝 t] fun s => (Dr s : E) := by
    filter_upwards [(hγ_ev t ht).eventually_nhds, (hJ_ev t ht).eventually_nhds]
      with s hγs hJs
    exact covDerivAlong_congr_curve (I := I) g J Jr hγs hJs
  have hJdiff : ∀ t ∈ Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t := by
    intro t ht
    have hraw := (radial_jacobi_reg (I := I) g p u z t (hdom t ht)).1
    have hrep := chartRep_congr_curve (I := I) Jr J
      (hγ_ev t ht).symm (hJ_ev t ht).symm
    exact hrep.differentiableAt_iff.mp (by
      simpa only [γr, Jr, rawExp] using hraw)
  have hDJdiff : ∀ t ∈ Icc (0 : ℝ) L,
      DifferentiableAt ℝ (chartRepAt (I := I) γ DJ t) t := by
    intro t ht
    have hraw := (radial_jacobi_reg (I := I) g p u z t (hdom t ht)).2
    have hrep := chartRep_congr_curve (I := I) Dr DJ
      (hγ_ev t ht).symm (hD_ev t ht).symm
    exact hrep.differentiableAt_iff.mp (by
      simpa only [γr, Jr, Dr, rawExp] using hraw)
  have hJac : ∀ t ∈ Ioo (0 : ℝ) L, IsJacobiAt (I := I) g γ J t := by
    intro t ht
    have hraw := (radial_jacobi_on (I := I) g p u z hdom).2.2 t ht
    apply jacobiAt_congr (I := I) g Jr J
      (hγ_ev t ⟨ht.1.le, ht.2.le⟩).symm
      (hJ_ev t ⟨ht.1.le, ht.2.le⟩).symm
    simpa only [γr, Jr, rawExp] using hraw
  have hgeo : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) L) := by
    intro t ht
    have hraw := Exponential.raw_radial_geo_at (I := I) g p
      (show TangentSpace I p from u) (hdom t ht)
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
      (hγ_ev t ht).eq_of_nhds (hγ_ev t ht) (by
        simpa only [γr, rawExp] using hraw)
  have hJ0 : J 0 = 0 := by
    change (J 0 : E) = 0
    rw [(hJ_ev 0 ⟨le_rfl, hL.le⟩).eq_of_nhds]
    exact congrArg (fun w : TangentSpace I (γr 0) => (w : E)) hJr0
  have hJc : J c = 0 := by
    change (J c : E) = 0
    rw [(hJ_ev c ⟨hc.1.le, hc.2.le⟩).eq_of_nhds]
    exact congrArg (fun w : TangentSpace I (γr c) => (w : E)) hJrc
  have hDJ0 : (DJ 0 : E) = z := by
    rw [(hD_ev 0 ⟨le_rfl, hL.le⟩).eq_of_nhds]
    simpa only [Dr, γr, Jr, rawExp] using
      radial_jacobi_d0 (I := I) g p u z
  have hγ0 : γ 0 = p := by
    rw [(hγ_ev 0 ⟨le_rfl, hL.le⟩).eq_of_nhds]
    simpa only [γr, rawExp, zero_smul] using expMap_zero (I := I) g p
  have hvel0 : (curveVelocity (I := I) γ 0 : E) = u := by
    change (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = u
    rw [(hγ_ev 0 ⟨le_rfl, hL.le⟩).mfderiv_eq]
    simpa only [γr, rawExp] using radialCurve_launch_velocity (I := I) g p u
  have hveldiff : ∀ t ∈ Icc (0 : ℝ) L, DifferentiableAt ℝ
      (chartRepAt (I := I) γ (curveVelocity (I := I) γ) t) t :=
    fun t _ => by
      simpa only [curveVelocity] using
        velocity_chartRepAt_differentiableAt (I := I) γ hγ_smooth t
  have hvelpar : ∀ t ∈ Icc (0 : ℝ) L,
      covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) t = 0 := by
    intro t ht
    exact (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
      (I := I) g γ t hγ_smooth).mpr (hgeo t ht)
  have hUnit : ∀ t ∈ Icc (0 : ℝ) L,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = 1 := by
    intro t ht
    have hconst := parallel_transport_preserves_inner_product
      (I := I) g γ (N := 2) le_rfl
      (hγ_smooth.of_le (by exact_mod_cast le_top))
      (curveVelocity (I := I) γ) (curveVelocity (I := I) γ)
      hveldiff hveldiff hvelpar hvelpar t ht
    rw [hconst, hγ0]
    change g.inner p (show E from curveVelocity (I := I) γ 0)
      (show E from curveVelocity (I := I) γ 0) = 1
    rw [hvel0]
    exact hunit
  have hspeed : ∀ t ∈ Icc (0 : ℝ) L,
      0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by
    intro t ht
    rw [hUnit t ht]
    exact zero_lt_one
  have hperp := jacobi_perp_Ioo (I := I) g γ J hL hc
    hγ_smooth hgeo hJdiff hDJdiff hJac hJ0 hJc
  have hJperp := hperp.1
  have hDJperp := hperp.2
  obtain ⟨F, hFdiff, hFpar, hON, hFperp, hFbundle⟩ :=
    exists_parallel_perp_frame (I := I) g γ hγ_smooth
      hL hgeo (by
        rw [hγ0]
        change g.inner p (show E from curveVelocity (I := I) γ 0)
          (show E from curveVelocity (I := I) γ 0) = 1
        rw [hvel0]
        exact hunit)
  let e : Fin (Module.finrank ℝ E - 1) →
      ∀ t : ℝ, TangentSpace I (γ t) := fun i => (F i).toFun
  let R : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCurvOp (I := I) g γ e
  let y : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCoeff (I := I) g e J
  let v : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCoeff (I := I) g e DJ
  have hode : ∀ t ∈ Ioo (0 : ℝ) L,
      HasDerivAt y (v t) t ∧ HasDerivAt v (-(R t) (y t)) t := by
    intro t ht
    simpa only [y, v, R, e, DJ] using
      perpCoeff_ode (I := I) (n := ∞) (by simp) g γ e J t
        hγ_smooth.contMDiffAt
        (fun i => hFdiff i t ⟨ht.1.le, ht.2.le⟩)
        (hJdiff t ⟨ht.1.le, ht.2.le⟩)
        (hDJdiff t ⟨ht.1.le, ht.2.le⟩)
        (fun i => hFpar i t ⟨ht.1.le, ht.2.le⟩)
        (hJac t ht) (by simp) (hspeed t ⟨ht.1.le, ht.2.le⟩)
        (fun i => hFperp t ⟨ht.1.le, ht.2.le⟩ i)
        (hJperp t ⟨ht.1.le, ht.2.le⟩)
        (fun i j => hON t ⟨ht.1.le, ht.2.le⟩ i j)
  have hR_smooth : ContDiff ℝ ∞ R := by
    simpa only [R, e] using
      perpCurv_smooth (I := I) g γ hγ_smooth e
        (fun i => hFbundle i)
  have hR_symm : ∀ t, ∀ x x' :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)),
      ⟪R t x, x'⟫ = ⟪x, R t x'⟫ := by
    intro t x x'
    simpa only [R, e] using perpCurv_symm (I := I) g γ e t x x'
  have hy_smooth : ContDiff ℝ ∞ y := by
    simpa only [y, e] using perpCoeff_smooth (I := I) g e J
      (fun i => hFbundle i) hJ_bundle
  have hv_cont : ContinuousOn v (Icc (0 : ℝ) L) := by
    intro t ht
    let LE : (Fin (Module.finrank ℝ E - 1) → ℝ) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E - 1)) ℝ).symm
    have hpi : HasDerivAt
        (fun s => (fun i => g.inner (γ s) (e i s) (DJ s) :
          Fin (Module.finrank ℝ E - 1) → ℝ))
        (fun i => g.inner (γ t) (e i t)
          (covDerivAlong (I := I) g γ DJ t)) t :=
      hasDerivAt_pi.mpr fun i =>
        parInner_deriv (I := I) (n := ∞) (by simp) g γ (e i) DJ t
          hγ_smooth.contMDiffAt (hFdiff i t ht) (hDJdiff t ht)
          (hFpar i t ht)
    have hLv := LE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hpi
    have hvdiff : DifferentiableAt ℝ v t := by
      simpa only [v, perpCoeff, LE] using hLv.differentiableAt
    exact hvdiff.continuousAt.continuousWithinAt
  have hacc_cont : ContinuousOn (fun t => -(R t) (y t)) (Icc (0 : ℝ) L) :=
    (hR_smooth.continuous.clm_apply hy_smooth.continuous).neg.continuousOn
  have hsol : IsJacobiSolOn R 0 L y v :=
    IsJacobiSolOn.of_Ioo hL hy_smooth.continuous.continuousOn
      hv_cont hacc_cont hode
  have hy0 : y 0 = 0 := perpCoeff_zero (I := I) g e J 0 hJ0
  have hyc : y c = 0 := perpCoeff_zero (I := I) g e J c hJc
  have hderiv : ∀ t ∈ Icc (0 : ℝ) L, deriv y t = v t := by
    intro t ht
    have hsmooth : HasDerivWithinAt y (deriv y t) (Icc (0 : ℝ) L) t :=
      ((hy_smooth.differentiable (by simp)).differentiableAt.hasDerivAt).hasDerivWithinAt
    exact ((uniqueDiffOn_Icc hL) t ht).eq_deriv
      (Icc (0 : ℝ) L) hsmooth (hsol.deriv_fst t ht)
  have hDJ0_ne : DJ 0 ≠ 0 := by
    intro hzero
    apply hz_ne
    rw [← hDJ0]
    exact hzero
  have hv0_ne : v 0 ≠ 0 := by
    exact perpCoeff_ne_zero (I := I) g e DJ 0 (by simp)
      (hspeed 0 ⟨le_rfl, hL.le⟩)
      (fun i => hFperp 0 ⟨le_rfl, hL.le⟩ i)
      hDJperp (fun i j => hON 0 ⟨le_rfl, hL.le⟩ i j) hDJ0_ne
  have hne : ∃ t ∈ Icc (0 : ℝ) L, y t ≠ 0 := by
    have hyder0 : HasDerivAt y (v 0) 0 := by
      have hsmooth :=
        (hy_smooth.differentiable (by simp) (0 : ℝ)).hasDerivAt
      rw [hderiv 0 ⟨le_rfl, hL.le⟩] at hsmooth
      exact hsmooth
    have hev : {t : ℝ | y t ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := by
      simpa only [hy0] using
        (hyder0.eventually_ne hv0_ne :
          ∀ᶠ t in 𝓝[≠] (0 : ℝ), y t ≠ 0)
    obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    let t : ℝ := min (ε / 2) (L / 2)
    have htpos : 0 < t := lt_min (by linarith) (by linarith)
    have htε : t < ε := (min_le_left (ε / 2) (L / 2)).trans_lt (by linarith)
    have htL : t < L := (min_le_right (ε / 2) (L / 2)).trans_lt (by linarith)
    refine ⟨t, ⟨htpos.le, htL.le⟩, ?_⟩
    apply hUsub
    refine ⟨hball ?_, ?_⟩
    · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos] using htε
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using htpos.ne'
  obtain ⟨W, hW_smooth, hW0, hWL, hWneg⟩ :=
    hsol.exists_smooth_neg_on hc hR_smooth.continuous.continuousOn
      hR_symm hy_smooth hderiv hy0 hyc hne
  let V : ℝ → E := fun t => (perpFrameLift (I := I) e W t : E)
  have hV_bundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (V t)) := by
    simpa only [V] using perpLift_smooth (I := I) hγ_smooth e W hW_smooth
      (fun i => hFbundle i)
  have hVperp : ∀ t ∈ Icc (0 : ℝ) L,
      g.inner (γ t) (V t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 0 := by
    intro t ht
    simpa only [V, curveVelocity] using
      perpLift_perp (I := I) g e W t (curveVelocity (I := I) γ t)
        (fun i => hFperp t ht i)
  have hV0 : V 0 = 0 := perpLift_zero (I := I) e W 0 hW0
  have hVL : V L = 0 := perpLift_zero (I := I) e W L hWL
  have hindex_eq : indexForm (I := I) g γ 0 L V V =
      DifferentialGeometry.Analysis.ODE.indexForm R 0 L
        W (deriv W) W (deriv W) := by
    simpa only [V, R, e, uIcc_of_le hL.le] using
      perpLift_indexForm (I := I) g γ e W W 0 L
        (fun t _ => hW_smooth.differentiable (by simp) t)
        (fun t _ => hW_smooth.differentiable (by simp) t)
        (fun i t ht => hFdiff i t (by simpa only [uIcc_of_le hL.le] using ht))
        (fun i t ht => hFpar i t (by simpa only [uIcc_of_le hL.le] using ht))
        (fun t ht i j => hON t (by simpa only [uIcc_of_le hL.le] using ht) i j)
  have hgeom_neg : indexForm (I := I) g γ 0 L V V < 0 := by
    rw [hindex_eq]
    exact hWneg
  have hlen : arcLength (I := I) g γ 0 L =
      arcLength (I := I) g γr 0 L := by
    unfold arcLength
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) L := by
      simpa only [uIcc_of_le hL.le] using ht
    have hev := hγ_ev t ht'
    change Real.sqrt
        (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) =
      Real.sqrt
        (g.inner (γr t) (mfderiv 𝓘(ℝ, ℝ) I γr t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γr t (1 : ℝ)))
    rw [hev.eq_of_nhds, hev.mfderiv_eq]
  have hminγ : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = γ 0 → η L = γ L →
      arcLength (I := I) g γ 0 L ≤ arcLength (I := I) g η 0 L := by
    intro η hη hη0 hηL
    have hη0' : η 0 = p := hη0.trans hγ0
    have hγL : γ L = expMap (I := I) g p
        (show TangentSpace I p from L • u) := by
      rw [(hγ_ev L ⟨hL.le, le_rfl⟩).eq_of_nhds]
    have hηL' : η L = expMap (I := I) g p
        (show TangentSpace I p from L • u) := hηL.trans hγL
    rw [hlen]
    simpa only [γr, rawExp] using hmin η hη hη0' hηL'
  have hnonneg : 0 ≤ indexForm (I := I) g γ 0 L V V :=
    indexForm_nonneg_of_minimising_geodesic
      (I := I) g γ L V hL
      hV_bundle hgeo hminγ
      (by simpa only [curveVelocity] using hUnit) hVperp hV0 hVL
  exact (not_lt_of_ge hnonneg) hgeom_neg

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
theorem not_conj_of_min_len
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : E)
    (hunit : g.inner p u u = 1)
    (L : ℝ) (hL : 0 < L)
    (hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u)) 0 L ≤
        arcLength (I := I) g η 0 L)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) L) :
    ¬ IsConjVec (I := I) g hEnorm p (c • u) := by
  classical
  intro hconj
  obtain ⟨z, hz, hJc_raw⟩ :=
    conjVec_jacobi_at (I := I) g hEnorm p u hc.1.ne' hconj
  let f : ℝ → ℝ → M := fun s t =>
    intrinsicGeodesic (I := I) g hEnorm p
      (show TangentSpace I p from u + s • z) t
  let γ : ℝ → M := fun t => f 0 t
  have hγ :
      γ = intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) := by
    funext t
    simp only [γ, f, zero_smul, add_zero]
  let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => f s t) 0 (1 : ℝ)
  let DJ : ∀ t : ℝ, TangentSpace I (γ t) :=
    fun t => covDerivAlong (I := I) g γ J t
  have hγ_smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
    have hvar := intrinsicVar_smooth (I := I) g hEnorm p u 0
    have hincl : ContMDiff 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => ((0 : ℝ), t)) :=
      contMDiff_const.prodMk contMDiff_id
    simpa only [γ, f, Function.comp_apply, zero_smul, smul_zero, add_zero] using
      hvar.comp hincl
  have hgeo : IsGeodesic (I := I) g γ := by
    simpa only [γ, f, zero_smul, add_zero] using
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u)
  have hf_infty :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : ℝ × ℝ => f q.1 q.2) := by
    simpa only [f] using
      intrinsicVar_smooth (I := I) g hEnorm p u z
  have hf_smooth : IsSmoothVariation (I := I) f :=
    hf_infty.of_le ENat.LEInfty.out
  have hJ_bundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (J t)) := by
    simpa only [γ, J] using
      varField_smooth (I := I) f hf_infty
  have hJdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t := by
    simpa only [γ, J] using
      variationField_chartRep_differentiableAt
        (I := I) g f hf_smooth t
  have hDJdiff (t : ℝ) :
      DifferentiableAt ℝ (chartRepAt (I := I) γ DJ t) t := by
    simpa only [γ, J, DJ] using
      variationField_covDeriv_chartRep_differentiableAt
        (I := I) g f hf_smooth t
  have hJac : IsJacobiAlong (I := I) g γ J := by
    rw [hγ]
    simpa only [J, f] using
      intrinsic_jacobi (I := I) g hEnorm p u z
  have hJ0 : J 0 = 0 := by
    simpa only [γ, f, J, zero_smul, add_zero] using
      jacobiVar_zero (I := I) g hEnorm p u z
  have hJc : J c = 0 := by
    simpa only [γ, f, J] using hJc_raw
  have hJperp :
      ∀ t, g.inner (γ t) (J t) (curveVelocity (I := I) γ t) = 0 :=
    jacobi_perp_of_ends (I := I) g γ J hc.1.ne'
      hγ_smooth hgeo hJdiff hDJdiff hJac hJ0 hJc
  have hunit0 :
      g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 1 := by
    have hγ0 : γ 0 = p := by
      rw [hγ]
      simpa only using
        intrinsicGeodesic_zero (I := I) g hEnorm p
          (show TangentSpace I p from u)
    have hvel0 : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = u := by
      rw [hγ]
      simpa only using
        intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p
          (show TangentSpace I p from u)
    rw [hγ0]
    change g.inner p
      (show E from mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))
      (show E from mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 1
    rw [hvel0]
    exact hunit
  obtain ⟨F, hFdiff, hFpar, hON, hFperp, hFbundle⟩ :=
    exists_parallel_perp_frame (I := I) g γ hγ_smooth
      (L := L) hL (hgeo.isGeodesicOn (Icc 0 L)) hunit0
  let e : Fin (Module.finrank ℝ E - 1) →
      ∀ t : ℝ, TangentSpace I (γ t) :=
    fun i => (F i).toFun
  let R : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCurvOp (I := I) g γ e
  let y : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCoeff (I := I) g e J
  let v : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    perpCoeff (I := I) g e DJ
  have hspeed (t : ℝ) :
      0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by
    have hsq :=
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p
        (show TangentSpace I p from u) t
    have hsq' :
        g.inner (γ t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) = 1 := by
      rw [hγ]
      simpa only [curveVelocity] using hsq.trans hunit
    rw [hsq']
    exact zero_lt_one
  have hode (t : ℝ) (ht : t ∈ Icc (0 : ℝ) L) :
      HasDerivAt y (v t) t ∧
        HasDerivAt v (-(R t) (y t)) t := by
    simpa only [y, v, R, e, DJ] using
      perpCoeff_ode (I := I) (n := ∞) (by simp) g γ e J t
        hγ_smooth.contMDiffAt
        (fun i => hFdiff i t ht)
        (hJdiff t) (hDJdiff t)
        (fun i => hFpar i t ht)
        (hJac t) (by simp) (hspeed t)
        (fun i => hFperp t ht i)
        (hJperp t) (fun i j => hON t ht i j)
  have hsol : IsJacobiSolOn R 0 L y v :=
    { deriv_fst := fun t ht => (hode t ht).1.hasDerivWithinAt
      deriv_snd := fun t ht => (hode t ht).2.hasDerivWithinAt }
  have hR_smooth : ContDiff ℝ ∞ R := by
    simpa only [R, e] using
      perpCurv_smooth (I := I) g γ hγ_smooth e
        (fun i => hFbundle i)
  have hR_symm :
      ∀ t, ∀ x x' : EuclideanSpace ℝ
        (Fin (Module.finrank ℝ E - 1)),
        ⟪R t x, x'⟫ = ⟪x, R t x'⟫ := by
    intro t x x'
    simpa only [R, e] using
      perpCurv_symm (I := I) g γ e t x x'
  have hy_smooth : ContDiff ℝ ∞ y := by
    simpa only [y, e] using
      perpCoeff_smooth (I := I) g e J
        (fun i => hFbundle i) hJ_bundle
  have hy0 : y 0 = 0 := by
    exact perpCoeff_zero (I := I) g e J 0 hJ0
  have hyc : y c = 0 := by
    exact perpCoeff_zero (I := I) g e J c hJc
  have hderiv :
      ∀ t ∈ Icc (0 : ℝ) L, deriv y t = v t :=
    fun t ht => (hode t ht).1.deriv
  have hDJ0 : (DJ 0 : E) = z := by
    change (covDerivAlong (I := I) g γ J 0 : E) = z
    have hcurve_ev :
        γ =ᶠ[𝓝 (0 : ℝ)]
          intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u) :=
      Filter.Eventually.of_forall fun t => congrFun hγ t
    have hfield_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
        (J t : E) =
          (show TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm p
                (show TangentSpace I p from u) t) from
            mfderiv 𝓘(ℝ, ℝ) I
              (fun s : ℝ =>
                intrinsicGeodesic (I := I) g hEnorm p
                  (show TangentSpace I p from u + s • z) t)
              0 (1 : ℝ) : E) := by
      filter_upwards with t
      rfl
    have htransport :=
      covDerivAlong_congr_curve (I := I) g J
        (fun t : ℝ =>
          show TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm p
                (show TangentSpace I p from u) t) from
            mfderiv 𝓘(ℝ, ℝ) I
              (fun s : ℝ =>
                intrinsicGeodesic (I := I) g hEnorm p
                  (show TangentSpace I p from u + s • z) t)
              0 (1 : ℝ))
        hcurve_ev hfield_ev
    exact htransport.trans
      (intrinsic_jacobi_d0 (I := I) g hEnorm p u z)
  have hveldiff :
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ (curveVelocity (I := I) γ) 0) 0 := by
    simpa only [curveVelocity] using
      velocity_chartRepAt_differentiableAt (I := I) γ hγ_smooth 0
  have hvelpar :
      covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) 0 = 0 :=
    (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
      (I := I) g γ 0 hγ_smooth).mpr (hgeo.hasGeodesicEquationAt 0)
  have hinnerDeriv :
      HasDerivAt
        (fun t : ℝ =>
          g.inner (γ t) (curveVelocity (I := I) γ t) (J t))
        (g.inner (γ 0) (curveVelocity (I := I) γ 0) (DJ 0)) 0 := by
    simpa only [DJ] using
      parInner_deriv (I := I) (n := ∞) (by simp) g γ
        (curveVelocity (I := I) γ) J 0
        hγ_smooth.contMDiffAt hveldiff (hJdiff 0) hvelpar
  have hinnerZero :
      (fun t : ℝ =>
        g.inner (γ t) (curveVelocity (I := I) γ t) (J t)) =
        fun _ : ℝ => 0 := by
    funext t
    rw [g.symm]
    exact hJperp t
  have hDJperp :
      g.inner (γ 0) (DJ 0) (curveVelocity (I := I) γ 0) = 0 := by
    have hzero :
        g.inner (γ 0) (curveVelocity (I := I) γ 0) (DJ 0) = 0 := by
      rw [hinnerZero] at hinnerDeriv
      exact hinnerDeriv.unique (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
    rw [g.symm]
    exact hzero
  have hDJ0_ne : DJ 0 ≠ 0 := by
    intro hzero
    apply hz
    rw [← hDJ0]
    exact hzero
  have hv0_ne : v 0 ≠ 0 := by
    exact perpCoeff_ne_zero (I := I) g e DJ 0
      (by simp) (hspeed 0)
      (fun i => hFperp 0 ⟨le_rfl, hL.le⟩ i)
      hDJperp (fun i j => hON 0 ⟨le_rfl, hL.le⟩ i j) hDJ0_ne
  have hne : ∃ t ∈ Icc (0 : ℝ) L, y t ≠ 0 := by
    have hev : {t : ℝ | y t ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := by
      simpa only [hy0] using
        ((hode 0 ⟨le_rfl, hL.le⟩).1.eventually_ne hv0_ne :
          ∀ᶠ t in 𝓝[≠] (0 : ℝ), y t ≠ 0)
    obtain ⟨U, hU, hUsub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    let t : ℝ := min (ε / 2) (L / 2)
    have htpos : 0 < t := by
      exact lt_min (by linarith) (by linarith)
    have htε : t < ε :=
      (min_le_left (ε / 2) (L / 2)).trans_lt (by linarith)
    have htL : t < L :=
      (min_le_right (ε / 2) (L / 2)).trans_lt (by linarith)
    refine ⟨t, ⟨htpos.le, htL.le⟩, ?_⟩
    apply hUsub
    refine ⟨hball ?_, ?_⟩
    · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos] using htε
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using htpos.ne'
  obtain ⟨W, hW_smooth, hW0, hWL, hWneg⟩ :=
    hsol.exists_smooth_neg_on hc hR_smooth.continuous.continuousOn
      hR_symm hy_smooth hderiv hy0 hyc hne
  let V : ℝ → E := fun t =>
    (perpFrameLift (I := I) e W t : E)
  have hV_bundle : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun t => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) (γ t) (V t)) := by
    simpa only [V] using
      perpLift_smooth (I := I) hγ_smooth e W hW_smooth
        (fun i => hFbundle i)
  have hVperp :
      ∀ t ∈ Icc (0 : ℝ) L,
        g.inner (γ t) (V t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 0 := by
    intro t ht
    simpa only [V, curveVelocity] using
      perpLift_perp (I := I) g e W t
        (curveVelocity (I := I) γ t)
        (fun i => hFperp t ht i)
  have hV0 : V 0 = 0 := by
    exact perpLift_zero (I := I) e W 0 hW0
  have hVL : V L = 0 := by
    exact perpLift_zero (I := I) e W L hWL
  have hindex_eq :
      indexForm (I := I) g γ 0 L V V =
        DifferentialGeometry.Analysis.ODE.indexForm R 0 L
          W (deriv W) W (deriv W) := by
    have h0L : uIcc (0 : ℝ) L = Icc (0 : ℝ) L :=
      uIcc_of_le hL.le
    simpa only [V, R, e] using
      perpLift_indexForm (I := I) g γ e W W 0 L
        (fun t _ => hW_smooth.differentiable (by simp) t)
        (fun t _ => hW_smooth.differentiable (by simp) t)
        (fun i t ht => hFdiff i t (by simpa only [h0L] using ht))
        (fun i t ht => hFpar i t (by simpa only [h0L] using ht))
        (fun t ht i j => hON t (by simpa only [h0L] using ht) i j)
  have hgeom_neg : indexForm (I := I) g γ 0 L V V < 0 := by
    rw [hindex_eq]
    exact hWneg
  have hUnit :
      ∀ t ∈ Icc (0 : ℝ) L,
        g.inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 := by
    intro t _
    have hsq :=
      intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p
        (show TangentSpace I p from u) t
    rw [hγ]
    simpa only [hunit] using hsq
  have hminγ :
      ∀ η : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
        η 0 = γ 0 → η L = γ L →
        arcLength (I := I) g γ 0 L ≤
          arcLength (I := I) g η 0 L := by
    intro η hη hη0 hηL
    have hη0' : η 0 = p := hη0.trans (by
      rw [hγ]
      exact intrinsicGeodesic_zero (I := I) g hEnorm p
        (show TangentSpace I p from u))
    have hηL' :
        η L = intrinsicGeodesic (I := I) g hEnorm p
          (show TangentSpace I p from u) L := hηL.trans (by rw [hγ])
    simpa only [hγ] using hmin η hη hη0' hηL'
  have hnonneg :
      0 ≤ indexForm (I := I) g γ 0 L V V :=
    indexForm_nonneg_of_minimising_geodesic
      (I := I) g γ L V hL
      hV_bundle (hgeo.isGeodesicOn (Icc 0 L)) hminγ
      hUnit hVperp hV0 hVL
  exact (not_lt_of_ge hnonneg) hgeom_neg

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)] in
theorem not_conj_of_min
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : E)
    (hunit : g.inner p u u = 1)
    (hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 1) →
      η 0 = p →
      η 1 = intrinsicGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u) 1 →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p
            (show TangentSpace I p from u)) 0 1 ≤
        arcLength (I := I) g η 0 1)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    ¬ IsConjVec (I := I) g hEnorm p (c • u) :=
  not_conj_of_min_len (I := I) g hEnorm p u hunit 1
    (by norm_num) hmin hc

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
