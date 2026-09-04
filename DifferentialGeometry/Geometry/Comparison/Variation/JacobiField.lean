import DifferentialGeometry.Geometry.Comparison.Variation.CovariantCommutationCurvature
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

noncomputable def curveVelocity (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)

def IsJacobiAt (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ) : Prop :=
  covDerivAlong (I := I) g γ
      (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
    + (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
        (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
    = 0

def IsJacobiAlong (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) : Prop :=
  ∀ t : ℝ, IsJacobiAt (I := I) g γ J t

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private lemma chartRep_germ_congr
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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma covDeriv_germ_congr
    (g : SmoothRiemannianMetric I M) {γ γ' : ℝ → M}
    (V : ∀ s : ℝ, TangentSpace I (γ s)) (V' : ∀ s : ℝ, TangentSpace I (γ' s))
    {t : ℝ}
    (hγ : γ =ᶠ[𝓝 t] γ')
    (hV : ∀ᶠ s in 𝓝 t, (V s : E) = (V' s : E)) :
    (covDerivAlong (I := I) g γ V t : E) = (covDerivAlong (I := I) g γ' V' t : E) := by
  have hfoot : γ t = γ' t := hγ.eq_of_nhds
  have hcurve : chartCurve (I := I) (γ' t) γ =ᶠ[𝓝 t] chartCurve (I := I) (γ' t) γ' := by
    filter_upwards [hγ] with s hs
    simp only [chartCurve_def]
    rw [hs]
  have hrep : chartRepAt (I := I) γ V t =ᶠ[𝓝 t] chartRepAt (I := I) γ' V' t :=
    chartRep_germ_congr (I := I) V V' hγ hV
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [show (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
        = (trivializationAt E (TangentSpace I) (γ' t)).symmL ℝ (γ' t) from by rw [hfoot]]
  rw [show γ t = γ' t from hfoot]
  congr 1
  rw [chartCovDerivAlong_def, chartCovDerivAlong_def]
  rw [hrep.deriv_eq, hrep.eq_of_nhds, hcurve.deriv_eq, hcurve.eq_of_nhds]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma riemannOp_germ_congr
    (g : SmoothRiemannianMetric I M) {x y : M} (h : x = y) (A B C : E) :
    ((DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) x) A B C : E)
      = ((DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) y) A B C : E) := by
  subst h
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- The Jacobi equation at a point depends only on the germs of the base curve
and the vector field there. -/
theorem jacobiAt_congr
    (g : SmoothRiemannianMetric I M) {γ γ' : ℝ → M}
    (J : ∀ s : ℝ, TangentSpace I (γ s)) (J' : ∀ s : ℝ, TangentSpace I (γ' s))
    {t : ℝ}
    (hγ : γ =ᶠ[𝓝 t] γ')
    (hJ : ∀ᶠ s in 𝓝 t, (J s : E) = (J' s : E))
    (hjac : IsJacobiAt (I := I) g γ J t) :
    IsJacobiAt (I := I) g γ' J' t := by
  let D : ∀ s : ℝ, TangentSpace I (γ s) := fun s => covDerivAlong (I := I) g γ J s
  let D' : ∀ s : ℝ, TangentSpace I (γ' s) := fun s => covDerivAlong (I := I) g γ' J' s
  have hD : ∀ᶠ s in 𝓝 t, (D s : E) = (D' s : E) := by
    filter_upwards [hγ.eventually_nhds, hJ.eventually_nhds] with s hγs hJs
    exact covDeriv_germ_congr (I := I) g J J' hγs hJs
  have hD2 :
      (covDerivAlong (I := I) g γ D t : E) = (covDerivAlong (I := I) g γ' D' t : E) :=
    covDeriv_germ_congr (I := I) g D D' hγ hD
  have hfoot : γ t = γ' t := hγ.eq_of_nhds
  have hJt : (J t : E) = (J' t : E) :=
    (show (fun s : ℝ => (J s : E)) =ᶠ[𝓝 t] fun s : ℝ => (J' s : E) from hJ).eq_of_nhds
  have hvel : (curveVelocity (I := I) γ t : E) = (curveVelocity (I := I) γ' t : E) := by
    change (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) : E)
      = (mfderiv (𝓘(ℝ, ℝ)) I γ' t (1 : ℝ) : E)
    rw [hγ.mfderiv_eq]
    rfl
  have hcurv :
      ((DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) : E)
        = ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ' t))
            (J' t) (curveVelocity (I := I) γ' t) (curveVelocity (I := I) γ' t) : E) := by
    rw [hJt, hvel]
    exact riemannOp_germ_congr (I := I) g hfoot _ _ _
  change (covDerivAlong (I := I) g γ D t : E) + _ = 0 at hjac
  change (covDerivAlong (I := I) g γ' D' t : E) + _ = 0
  rw [← hD2, ← hcurv]
  exact hjac

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem isJacobiAlong_iff (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) :
    IsJacobiAlong (I := I) g γ J ↔
      ∀ t : ℝ,
        covDerivAlong (I := I) g γ
            (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
          = - (DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
              (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
  constructor
  · intro hJ t
    have h : covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        + (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
        = 0 := hJ t
    linear_combination (norm := module) h
  · intro hJ t
    have h := hJ t
    change covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        + (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
        = 0
    linear_combination (norm := module) h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem jacobi_d2_eq
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {t : ℝ}
    (hJ : IsJacobiAt (I := I) g γ J t) :
    covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
      = - (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
  change covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
      + (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
      = 0 at hJ
  linear_combination (norm := module) hJ

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma riemannOp_self_zero
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    (DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) x) v v v = 0 := by
  have hswap := DifferentialGeometry.Geometry.Curvature.riemannOp_swap
    (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) x v v v
  have htwo : (2 : ℝ) •
      (DifferentialGeometry.Geometry.Curvature.riemannOp
        (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) x) v v v = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hswap
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- A Jacobi field initially orthogonal to a geodesic, together with its
covariant derivative, stays orthogonal on the whole closed interval. -/
theorem jacobi_perp_of_init
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (gamma t)) {b : ℝ} (hb : 0 < b)
    (hgamma : ∀ t ∈ Icc (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I (2 : WithTop ℕ∞) gamma t)
    (hgeo : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOn
      (I := I) g gamma (Icc (0 : ℝ) b))
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) gamma J t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) gamma
        (fun s => covDerivAlong (I := I) g gamma J s) t) t)
    (hJac : ∀ t ∈ Ioo (0 : ℝ) b, IsJacobiAt (I := I) g gamma J t)
    (hJ0 : J 0 = 0)
    (hD0 : g.inner (gamma 0) (curveVelocity (I := I) gamma 0)
      (covDerivAlong (I := I) g gamma J 0) = 0) :
    (∀ t ∈ Icc (0 : ℝ) b,
      g.inner (gamma t) (curveVelocity (I := I) gamma t) (J t) = 0) ∧
    ∀ t ∈ Icc (0 : ℝ) b,
      g.inner (gamma t) (curveVelocity (I := I) gamma t)
        (covDerivAlong (I := I) g gamma J t) = 0 := by
  let DJ : ∀ t : ℝ, TangentSpace I (gamma t) := fun t =>
    covDerivAlong (I := I) g gamma J t
  let f : ℝ → ℝ := fun t =>
    g.inner (gamma t) (curveVelocity (I := I) gamma t) (J t)
  let q : ℝ → ℝ := fun t =>
    g.inner (gamma t) (curveVelocity (I := I) gamma t) (DJ t)
  have hveldiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) gamma (curveVelocity (I := I) gamma) t) t := by
    intro t ht
    simpa only [curveVelocity] using
      MFDerivAlongCurve.velocity_coord_diff (I := I) gamma t (hgamma t ht)
  have hvelpar : ∀ t ∈ Icc (0 : ℝ) b,
      covDerivAlong (I := I) g gamma (curveVelocity (I := I) gamma) t = 0 := by
    intro t ht
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
      (I := I) g gamma t (hgamma t ht) (hgeo.hasGeodesicEquationAt ht)
  have hcurvzero (t : ℝ) :
      g.inner (gamma t) (curveVelocity (I := I) gamma t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
            (gamma t))
          (J t) (curveVelocity (I := I) gamma t)
          (curveVelocity (I := I) gamma t)) = 0 := by
    calc
      _ = g.inner (gamma t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
              (gamma t))
            (J t) (curveVelocity (I := I) gamma t)
            (curveVelocity (I := I) gamma t))
          (curveVelocity (I := I) gamma t) := g.symm (gamma t) _ _
      _ = g.inner (gamma t) (J t)
          ((DifferentialGeometry.Geometry.Curvature.riemannOp
              (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
              (gamma t))
            (curveVelocity (I := I) gamma t) (curveVelocity (I := I) gamma t)
            (curveVelocity (I := I) gamma t)) :=
        DifferentialGeometry.Geometry.Curvature.riemannOp_diag_symm
          (I := I) g (gamma t) (curveVelocity (I := I) gamma t) (J t)
          (curveVelocity (I := I) gamma t)
      _ = 0 := by rw [riemannOp_self_zero (I := I) g, map_zero]
  have hfderiv : ∀ t ∈ Icc (0 : ℝ) b, HasDerivAt f (q t) t := by
    intro t ht
    have h := inner_deriv_at (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g gamma (curveVelocity (I := I) gamma) J t (hgamma t ht)
      (hveldiff t ht) (hJdiff t ht)
    rw [hvelpar t ht] at h
    simpa only [f, q, DJ, map_zero, ContinuousLinearMap.zero_apply,
      zero_add] using h
  have hqdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ q t := by
    intro t ht
    exact (inner_deriv_at (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g gamma (curveVelocity (I := I) gamma) DJ t (hgamma t ht)
      (hveldiff t ht) (hDJdiff t ht)).differentiableAt
  have hqderiv : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt q 0 t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) b := ⟨ht.1.le, ht.2.le⟩
    have h := inner_deriv_at (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g gamma (curveVelocity (I := I) gamma) DJ t (hgamma t ht')
      (hveldiff t ht') (hDJdiff t ht')
    rw [hvelpar t ht', jacobi_d2_eq (I := I) g gamma J (hJac t ht)] at h
    simpa only [q, DJ, map_zero, ContinuousLinearMap.zero_apply, zero_add,
      map_neg, ContinuousLinearMap.neg_apply, hcurvzero t, neg_zero] using h
  let c : ℝ := b / 2
  have hc : c ∈ Ioo (0 : ℝ) b := by
    dsimp only [c]
    constructor <;> linarith
  have hqcont : ContinuousOn q (Icc (0 : ℝ) b) :=
    fun t ht => (hqdiff t ht).continuousAt.continuousWithinAt
  have hqeq : Set.EqOn q (fun _ => q c) (Ioo (0 : ℝ) b) := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s hs => (hqderiv s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hqderiv s hs).deriv) ht hc
  have hqeq_closed : Set.EqOn q (fun _ => q c) (Icc (0 : ℝ) b) :=
    hqeq.of_subset_closure hqcont continuousOn_const Ioo_subset_Icc_self (by
      rw [closure_Ioo hb.ne])
  have hq0 : q 0 = 0 := by
    simpa only [q, DJ] using hD0
  have hqc : q c = 0 := by
    have h := hqeq_closed (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb.le⟩)
    exact h.symm.trans hq0
  have hqzero : ∀ t ∈ Icc (0 : ℝ) b, q t = 0 := by
    intro t ht
    exact (hqeq_closed ht).trans hqc
  have hfzero : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt f 0 t := by
    intro t ht
    simpa only [hqzero t ⟨ht.1.le, ht.2.le⟩] using
      hfderiv t ⟨ht.1.le, ht.2.le⟩
  have hfcont : ContinuousOn f (Icc (0 : ℝ) b) :=
    fun t ht => (hfderiv t ht).continuousAt.continuousWithinAt
  have hfeq : Set.EqOn f (fun _ => f c) (Ioo (0 : ℝ) b) := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s hs => (hfzero s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hfzero s hs).deriv) ht hc
  have hfeq_closed : Set.EqOn f (fun _ => f c) (Icc (0 : ℝ) b) :=
    hfeq.of_subset_closure hfcont continuousOn_const Ioo_subset_Icc_self (by
      rw [closure_Ioo hb.ne])
  have hf0 : f 0 = 0 := by simp only [f, hJ0, map_zero]
  have hfc : f c = 0 := by
    have h := hfeq_closed (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb.le⟩)
    exact h.symm.trans hf0
  constructor
  · intro t ht
    exact (hfeq_closed ht).trans hfc
  · intro t ht
    exact hqzero t ht

def jacobiWronskian
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ) : ℝ :=
  g.inner (γ t) (covDerivAlong (I := I) g γ J t) (K t) -
    g.inner (γ t) (J t) (covDerivAlong (I := I) g γ K t)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem wronskian_deriv_at
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hJdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJ : IsJacobiAt (I := I) g γ J t)
    (hK : IsJacobiAt (I := I) g γ K t) :
    HasDerivAt (jacobiWronskian (I := I) g γ J K) 0 t := by
  have hleft := inner_deriv_at (I := I) hn g γ
    (fun s => covDerivAlong (I := I) g γ J s) K t hγ hDJdiff hKdiff
  have hright := inner_deriv_at (I := I) hn g γ J
    (fun s => covDerivAlong (I := I) g γ K s) t hγ hJdiff hDKdiff
  have hsub := hleft.sub hright
  have hJ2 := jacobi_d2_eq (I := I) g γ J hJ
  have hK2 := jacobi_d2_eq (I := I) g γ K hK
  have hcurv := DifferentialGeometry.Geometry.Curvature.riemannOp_diag_symm
    (I := I) g (γ t) (curveVelocity (I := I) γ t) (J t) (K t)
  refine (hsub.congr_deriv ?_)
  rw [hJ2, hK2]
  simp only [map_neg, ContinuousLinearMap.neg_apply]
  linarith

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem hasDerivAt_wronsk
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) (t : ℝ)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hJdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJ : IsJacobiAt (I := I) g γ J t)
    (hK : IsJacobiAt (I := I) g γ K t) :
    HasDerivAt (jacobiWronskian (I := I) g γ J K) 0 t :=
  wronskian_deriv_at (I := I) hn g γ J K t hγ.contMDiffAt
    hJdiff hKdiff hDJdiff hDKdiff hJ hK

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
/-- The Wronskian of two Jacobi fields vanishing at the left endpoint is zero
on the closed interval when the Jacobi equation is known only in its interior. -/
theorem wronskian_zero_Ioo
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) {b : ℝ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJacJ : ∀ t ∈ Ioo (0 : ℝ) b, IsJacobiAt (I := I) g γ J t)
    (hJacK : ∀ t ∈ Ioo (0 : ℝ) b, IsJacobiAt (I := I) g γ K t)
    (hJ0 : J 0 = 0) (hK0 : K 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) b, jacobiWronskian (I := I) g γ J K t = 0 := by
  have hcont : ContinuousOn (jacobiWronskian (I := I) g γ J K)
      (Icc (0 : ℝ) b) := by
    intro t ht
    have hleft := inner_deriv_at (I := I) hn g γ
      (fun s => covDerivAlong (I := I) g γ J s) K t
      (hγ t ht) (hDJdiff t ht) (hKdiff t ht)
    have hright := inner_deriv_at (I := I) hn g γ J
      (fun s => covDerivAlong (I := I) g γ K s) t
      (hγ t ht) (hJdiff t ht) (hDKdiff t ht)
    exact (hleft.sub hright).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ico (0 : ℝ) b,
      HasDerivWithinAt (jacobiWronskian (I := I) g γ J K) 0 (Ici t) t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | htpos
    · have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) b := ⟨le_rfl, ht.2.le⟩
      have hleft := inner_deriv_at (I := I) hn g γ
        (fun s => covDerivAlong (I := I) g γ J s) K 0
        (hγ 0 h0) (hDJdiff 0 h0) (hKdiff 0 h0)
      have hright := inner_deriv_at (I := I) hn g γ J
        (fun s => covDerivAlong (I := I) g γ K s) 0
        (hγ 0 h0) (hJdiff 0 h0) (hDKdiff 0 h0)
      apply HasDerivAt.hasDerivWithinAt
      refine (hleft.sub hright).congr_deriv ?_
      simp only [hJ0, hK0, map_zero, ContinuousLinearMap.zero_apply,
        add_zero, zero_add, sub_self]
    · exact (wronskian_deriv_at (I := I) hn g γ J K t
        (hγ t ⟨ht.1, ht.2.le⟩)
        (hJdiff t ⟨ht.1, ht.2.le⟩) (hKdiff t ⟨ht.1, ht.2.le⟩)
        (hDJdiff t ⟨ht.1, ht.2.le⟩) (hDKdiff t ⟨ht.1, ht.2.le⟩)
        (hJacJ t ⟨htpos, ht.2⟩) (hJacK t ⟨htpos, ht.2⟩)).hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont hderiv
  have hzero : jacobiWronskian (I := I) g γ J K 0 = 0 := by
    simp only [jacobiWronskian, hJ0, hK0, map_zero,
      ContinuousLinearMap.zero_apply, sub_self]
  intro t ht
  rw [hconst t ht, hzero]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem wronskian_zero_on
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) {b : ℝ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJacJ : ∀ t ∈ Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ J t)
    (hJacK : ∀ t ∈ Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ K t)
    (hJ0 : J 0 = 0) (hK0 : K 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) b, jacobiWronskian (I := I) g γ J K t = 0 := by
  exact wronskian_zero_Ioo (I := I) hn g γ J K hγ hJdiff hKdiff hDJdiff hDKdiff
    (fun t ht => hJacJ t ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => hJacK t ⟨ht.1.le, ht.2.le⟩) hJ0 hK0

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem wronskian_eq_zero
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J K : ∀ t : ℝ, TangentSpace I (γ t)) {b : ℝ}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hJdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ J t) t)
    (hKdiff : ∀ t ∈ Icc (0 : ℝ) b,
      DifferentiableAt ℝ (chartRepAt (I := I) γ K t) t)
    (hDJdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ J s) t) t)
    (hDKdiff : ∀ t ∈ Icc (0 : ℝ) b, DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun s => covDerivAlong (I := I) g γ K s) t) t)
    (hJacJ : ∀ t ∈ Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ J t)
    (hJacK : ∀ t ∈ Icc (0 : ℝ) b, IsJacobiAt (I := I) g γ K t)
    (hJ0 : J 0 = 0) (hK0 : K 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) b, jacobiWronskian (I := I) g γ J K t = 0 :=
  wronskian_zero_on (I := I) hn g γ J K (fun _ _ => hγ.contMDiffAt)
    hJdiff hKdiff hDJdiff hDKdiff hJacJ hJacK hJ0 hK0

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ode_bound_of_isJacobiAt
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t : ℝ, TangentSpace I (γ t)) {K t : ℝ}
    (hJ : IsJacobiAt (I := I) g γ J t)
    (hcurv :
      g.inner (γ t)
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
        ((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
          (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t))
      ≤ K ^ 2 * g.inner (γ t) (J t) (J t)) :
    g.inner (γ t)
      (covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t)
      (covDerivAlong (I := I) g γ
        (fun s : ℝ => covDerivAlong (I := I) g γ J s) t)
      ≤ K ^ 2 * g.inner (γ t) (J t) (J t) := by
  have hD :
      covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        = - (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) := by
    have h := hJ
    change covDerivAlong (I := I) g γ
          (fun s : ℝ => covDerivAlong (I := I) g γ J s) t
        + (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t))
            (J t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t)
        = 0 at h
    linear_combination (norm := module) h
  rw [hD]
  simpa using hcurv

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
