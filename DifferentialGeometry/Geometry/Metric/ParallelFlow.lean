import DifferentialGeometry.Geometry.Connection.ParallelFlow
import DifferentialGeometry.Geometry.Metric.Pullback

/-!
# Metric preservation by parallel flows

This file proves that the spatial differential of the complete flow of a
parallel vector field preserves the Riemannian inner product.
-/

open Bundle Manifold Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
private lemma curveAt_push_diff
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurve γ (fun y : M ↦ X y))
    (x : M) (v : TangentSpace I x) (t : ℝ) :
    DifferentiableAt ℝ
      (chartRepAt (I := I)
        (fun s ↦ curveAt (fun y : M ↦ X y) hcomplete x s)
        (fun s ↦ mfderiv I I
          (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) x v) t) t := by
  classical
  obtain ⟨η, hηsm, _hηmem, hη0, hηv⟩ :=
    exists_smooth_curve (I := I) x v Set.univ isOpen_univ (Set.mem_univ x)
  subst x
  let f : ℝ → ℝ → M := fun r s ↦
    curveAt (fun y : M ↦ X y) hcomplete (η r) s
  have hflow :
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
        (fun p : ℝ × M ↦
          curveAt (fun y : M ↦ X y) hcomplete p.2 p.1) :=
    curveAt_contMDiff (I := I) (fun y : M ↦ X y) X.contMDiff hcomplete
  have hf_smooth :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
        (fun p : ℝ × ℝ ↦ f p.1 p.2) := by
    have hin :
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
          (𝓘(ℝ, ℝ).prod I) ∞
          (fun p : ℝ × ℝ ↦ (p.2, η p.1)) :=
      contMDiff_snd.prodMk (hηsm.comp contMDiff_fst)
    simpa only [f, Function.comp_apply] using hflow.comp hin
  have hf : IsSmoothVariation (I := I) f :=
    hf_smooth.of_le
      (WithTop.coe_le_coe.2 (le_top : (8 : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hdiff :=
    variationField_chartRep_differentiableAt (I := I) g f hf t
  have hcenter :
      (fun s ↦ f 0 s) =
        fun s ↦ curveAt (fun y : M ↦ X y) hcomplete (η 0) s := by
    rfl
  have hspace (s : ℝ) :
      (mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ f r s) 0 : ℝ →L[ℝ] _)
          (1 : ℝ) =
        mfderiv I I
          (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) (η 0) v := by
    have hslice : ContMDiff I I ∞
        (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) := by
      have hin : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞
          (fun y : M ↦ (s, y)) :=
        contMDiff_const.prodMk contMDiff_id
      simpa only [Function.comp_apply] using hflow.comp hin
    have hslice_md : MDifferentiableAt I I
        (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) (η 0) :=
      hslice.contMDiffAt.mdifferentiableAt (by simp)
    have hηmd : MDifferentiableAt 𝓘(ℝ, ℝ) I η 0 :=
      hηsm.contMDiffAt.mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp_apply
      (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := I)
      (f := η)
      (g := fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s)
      (x := (0 : ℝ)) hslice_md hηmd (1 : ℝ)
    rw [hηv] at hcomp
    simpa only [f, Function.comp_def] using hcomp
  have hspace_fun :
      (fun s ↦ (mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ f r s) 0 : ℝ →L[ℝ] _)
        (1 : ℝ)) =
        fun s ↦ mfderiv I I
          (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) (η 0) v :=
    funext hspace
  rw [hcenter, hspace_fun] at hdiff
  exact hdiff

/-- The spatial differential of the complete flow of a parallel vector field
preserves the Riemannian inner product. -/
theorem curveAt_inner_eq
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurve γ (fun y : M ↦ X y))
    (hpar : ∀ x : M,
      (LeviCivita (I := I) g).toFun (fun y : M ↦ X y) x = 0)
    (x : M) (v w : TangentSpace I x) (t : ℝ) :
    g.inner (curveAt (fun y : M ↦ X y) hcomplete x t)
        (mfderiv I I
          (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y t) x v)
        (mfderiv I I
          (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y t) x w) =
      g.inner x v w := by
  classical
  let γ : ℝ → M := fun s ↦
    curveAt (fun y : M ↦ X y) hcomplete x s
  let V : ∀ s, TangentSpace I (γ s) := fun s ↦
    mfderiv I I
      (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) x v
  let W : ∀ s, TangentSpace I (γ s) := fun s ↦
    mfderiv I I
      (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y s) x w
  have hflow :
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
        (fun p : ℝ × M ↦
          curveAt (fun y : M ↦ X y) hcomplete p.2 p.1) :=
    curveAt_contMDiff (I := I) (fun y : M ↦ X y) X.contMDiff hcomplete
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := by
    have hin : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
        (fun s : ℝ ↦ (s, x)) :=
      contMDiff_id.prodMk contMDiff_const
    simpa only [γ, Function.comp_apply] using hflow.comp hin
  have hinner_deriv (s : ℝ) :
      HasDerivAt (fun r : ℝ ↦ g.inner (γ r) (V r) (W r)) 0 s := by
    have hmc := metric_compat_hasDerivAt_inner (I := I) (n := ∞) (by simp)
      g γ V W s hγ
        (curveAt_push_diff (I := I) g X hcomplete x v s)
        (curveAt_push_diff (I := I) g X hcomplete x w s)
    rw [curveAt_mfderiv_par (I := I) g X hcomplete hpar x v s,
      curveAt_mfderiv_par (I := I) g X hcomplete hpar x w s] at hmc
    simpa only [map_zero, ContinuousLinearMap.zero_apply, zero_add] using hmc
  have hconst :
      g.inner (γ t) (V t) (W t) = g.inner (γ 0) (V 0) (W 0) :=
    is_const_of_deriv_eq_zero
      (fun s ↦ (hinner_deriv s).differentiableAt)
      (fun s ↦ (hinner_deriv s).deriv) t 0
  have hflow_zero :
      (fun y : M ↦ curveAt (fun z : M ↦ X z) hcomplete y 0) = id := by
    funext y
    exact curveAt_zero (fun z : M ↦ X z) hcomplete y
  have hγ0 : γ 0 = x := curveAt_zero (fun z : M ↦ X z) hcomplete x
  have hV0 : V 0 = v := by
    change mfderiv I I
      (fun y : M ↦ curveAt (fun z : M ↦ X z) hcomplete y 0) x v = v
    rw [hflow_zero, mfderiv_id]
    rfl
  have hW0 : W 0 = w := by
    change mfderiv I I
      (fun y : M ↦ curveAt (fun z : M ↦ X z) hcomplete y 0) x w = w
    rw [hflow_zero, mfderiv_id]
    rfl
  rw [hγ0, hV0, hW0] at hconst
  exact hconst

/-- Each fixed-time diffeomorphism of the complete flow of a parallel vector
field preserves the Riemannian metric. -/
theorem curveAt_pullback_eq
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hcomplete : ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurve γ (fun y : M ↦ X y))
    (hpar : ∀ x : M,
      (LeviCivita (I := I) g).toFun (fun y : M ↦ X y) x = 0)
    (t : ℝ) :
    Diffeomorph.pullbackMetric g
        (curveAtDiffeo (I := I) (fun y : M ↦ X y) X.contMDiff hcomplete t) = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  change g.inner (curveAt (fun y : M ↦ X y) hcomplete x t)
      (mfderiv I I
        (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y t) x v)
      (mfderiv I I
        (fun y ↦ curveAt (fun z : M ↦ X z) hcomplete y t) x w) =
    g.inner x v w
  exact curveAt_inner_eq (I := I) g X hcomplete hpar x v w t

end DifferentialGeometry.Geometry.Riemannian
