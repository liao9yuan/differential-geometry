import DifferentialGeometry.Integral.DivergenceTheorem.Closed
import DifferentialGeometry.Integral.DivergenceTheorem.Green
import DifferentialGeometry.Integral.DivergenceTheorem.Gradient
import DifferentialGeometry.Integral.DivergenceTheorem.Laplacian
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Tensor.RSTensor.TangentRiemannian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lichnerowicz's eigenvalue inequality on a closed Riemannian manifold

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` of
dimension `n ≥ 2` with Ricci-curvature lower bound `Ric ≥ (n - 1) K g` for
some positive `K`, every smooth eigenfunction of the Laplace-Beltrami
operator with eigenvalue `-λ` (`λ > 0`) satisfies `λ ≥ n K`.

The argument is the classical scalar Bochner-Weitzenböck argument:

1. **Bochner identity** (input as a hypothesis):
   `Δ |∇f|² = 2 |∇²f|² + 2 Ric(∇f, ∇f) + 2 g(∇f, ∇(Δf))` pointwise.
2. **Divergence theorem on a closed manifold**: `∫ Δ φ d μ_g = 0` for any
   smooth scalar `φ`.
3. **Eigenvalue equation**: `Δ f = -λ f` so `∇(Δf) = -λ ∇f`, hence
   `g(∇f, ∇(Δf)) = -λ |∇f|²`.
4. **Cauchy-Schwarz Hessian bound** (input as a hypothesis):
   `|∇²f|² ≥ (Δf)² / n`.
5. **Ricci bound** (input as a hypothesis): `Ric(∇f, ∇f) ≥ (n - 1) K |∇f|²`.
6. **Green's first identity** (integration by parts): `∫ |∇f|² = -∫ f Δf
    = λ ∫ f²`.
7. **Strict positivity of the L² self-integral** for the nonzero
   eigenfunction (input as a hypothesis): `0 < ∫ f²`.

Combining these inputs, the equation `0 = ∫ Δ |∇f|²` forces `λ ≥ n K`.

The Bochner identity, the Hessian-trace bound, and the Ricci bound enter as
hypotheses. The concrete pointwise Hessian and Ricci tensors, together with
the analytic proof of the Bochner identity in the concrete `mfderiv`
framework, are not part of the inputs at this level: they will be supplied
by downstream specialisations.

## Main result

* `lichnerowicz_inequality` : the eigenvalue lower bound `n K ≤ λ`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Auxiliary: integral of a smooth Laplacian on a closed manifold

On a closed manifold, the integral of `Δ_g φ` against the canonical Riemannian
volume measure vanishes. This is the divergence theorem applied to
`grad_g g (smoothness witness for φ)`. -/

/-- The Laplacian of a smooth function integrates to zero on a closed manifold. -/
private theorem integral_Δ_g_eq_zero
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) :
    ∫ x, Δ_g (I := I) g hφ x ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  -- `Δ_g g hφ = divergence_g g (grad_g g hφ)` definitionally; apply the
  -- closed-manifold divergence theorem.
  exact integral_divergence_eq_zero_of_compact (I := I) g (grad_g (I := I) g hφ)

/-! ## Auxiliary: Green's first identity for an eigenfunction

For an eigenfunction `f` with `Δf = -λ f`, Green's first identity gives
`∫ |∇f|² = -∫ f · Δf = λ ∫ f²`. We use the diagonal version (`f = h`) of
the standard Green's first identity. -/

/-- Green's first identity, specialised to `f = h`, on a closed manifold. -/
private theorem integral_inner_grad_self_eq_neg_integral_f_Δf
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ∫ x, g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * Δ_g (I := I) g hf x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  -- On a compact manifold, every smooth function has compact support.
  have hf_cs : HasCompactSupport f := HasCompactSupport.of_compactSpace _
  exact integral_inner_grad_eq_neg_integral_smul_laplacian (I := I) g hf hf hf_cs

/-! ## The Lichnerowicz eigenvalue inequality

The headline statement assumes the pointwise Bochner identity, a Cauchy-Schwarz
type bound on the Hessian Frobenius-norm-squared, and a Ricci lower bound, all
phrased as scalar functions on `M`. The dimension hypothesis `2 ≤ n` is
included explicitly: the inequality `λ ≥ n K` is the standard Lichnerowicz
form, and the algebraic chain in the proof requires `n ≥ 2` in order to close
by dividing through by `(n - 1) λ ∫ f²` (a positive quantity when `n ≥ 2`,
`λ > 0`, and `f ≠ 0`). -/

/-- **Lichnerowicz's eigenvalue inequality.**

Let `(M, g)` be a closed (compact and boundaryless) smooth Riemannian manifold
of dimension `n := finrank ℝ E ≥ 2`. Suppose:

* `K > 0` is a positive lower curvature parameter.
* `f : M → ℝ` is a smooth function.
* `λ > 0` and `Δ_g f = -λ f` pointwise (eigenfunction equation).
* `gradNormSqSmooth` is a smoothness witness for the function
  `x ↦ g(∇f, ∇f)(x)`, so that one can apply the Laplacian to it.
* `hessSqNorm : M → ℝ` is the pointwise Frobenius norm squared of the
  Hessian; it is required to be continuous.
* `RicAtGrad : M → ℝ` is the function `x ↦ Ric_x(∇f x, ∇f x)`; required
  to be continuous.
* `h_bochner` is the pointwise Bochner-Weitzenböck identity for `f`:
  `Δ |∇f|² = 2 |∇²f|² + 2 Ric(∇f, ∇f) + 2 g(∇f, ∇(Δf))`.
* `h_hess_lower_bound` is the Cauchy-Schwarz Hessian bound:
  `(Δ f)² / n ≤ |∇²f|²`.
* `h_ricci_lower_bound` is the Ricci lower bound:
  `(n - 1) K g(∇f, ∇f) ≤ Ric(∇f, ∇f)`.
* `h_f_sq_pos` records that `0 < ∫ f²` (this is automatic for a nonzero
  smooth function on a closed manifold; we expose it as an explicit
  hypothesis to keep the inequality block self-contained).

Then `n K ≤ λ`. -/
theorem lichnerowicz_inequality
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hn_ge_two : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {lam : ℝ} (hlam_pos : 0 < lam)
    (hf_eigen : ∀ x : M, Δ_g (I := I) g hf x = -lam * f x)
    (gradNormSqSmooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => g.inner x
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)))
    (hessSqNorm : M → ℝ) (h_hessSqNorm_cont : Continuous hessSqNorm)
    (RicAtGrad : M → ℝ) (h_RicAtGrad_cont : Continuous RicAtGrad)
    (h_bochner : ∀ x : M,
      Δ_g (I := I) g gradNormSqSmooth x =
        2 * hessSqNorm x + 2 * RicAtGrad x +
          2 * g.inner x
            ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g (Δ_g_contMDiff (I := I) g hf) :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
    (h_hess_lower_bound : ∀ x : M,
      (Δ_g (I := I) g hf x)^2 / (Module.finrank ℝ E : ℝ) ≤ hessSqNorm x)
    (h_ricci_lower_bound : ∀ x : M,
      ((Module.finrank ℝ E : ℝ) - 1) * K *
        g.inner x ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((grad_g (I := I) g hf :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ≤ RicAtGrad x)
    (h_f_sq_pos : 0 < ∫ x, f x * f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :
    (Module.finrank ℝ E : ℝ) * K ≤ lam := by
  classical
  -- Set up frequently used objects.
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  haveI : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  -- Dimension is at least 2.
  have hn_ge_two_real : (2 : ℝ) ≤ n := by
    rw [hn_def]; exact_mod_cast hn_ge_two
  have hn_pos : 0 < n := by linarith
  have hn_minus_one_pos : 0 < n - 1 := by linarith
  -- Smooth gradient sections used throughout.
  set Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hf with hGf_def
  -- Smoothness witness for `Δ f`.
  have hΔf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (Δ_g (I := I) g hf) :=
    Δ_g_contMDiff (I := I) g hf
  set GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := grad_g (I := I) g hΔf with hGΔf_def
  -- Continuity of the four scalar integrands.
  have hf_cont : Continuous f := hf.continuous
  have hΔf_cont : Continuous (Δ_g (I := I) g hf) := hΔf.continuous
  have hgrad_inner_cont :
      Continuous (fun x : M => g.inner x (Gf x) (Gf x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I) g Gf Gf
  have hgrad_Δ_inner_cont :
      Continuous (fun x : M => g.inner x (Gf x) (GΔf x)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I) g Gf GΔf
  -- Continuous functions on a compact manifold are integrable against the
  -- finite Riemannian volume measure.
  have integrable_of_cont :
      ∀ {φ : M → ℝ}, Continuous φ → Integrable φ μ := by
    intro φ hφ
    exact hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Step 1: Bochner identity is the pointwise input. Integrate both sides
  -- against `μ`. The left-hand side is zero by the divergence theorem on the
  -- closed manifold.
  have h_LHS_zero :
      ∫ x, Δ_g (I := I) g gradNormSqSmooth x ∂μ = 0 :=
    integral_Δ_g_eq_zero (I := I) g gradNormSqSmooth
  have h_bochner_int :
      ∫ x, Δ_g (I := I) g gradNormSqSmooth x ∂μ =
        ∫ x, (2 * hessSqNorm x + 2 * RicAtGrad x +
            2 * g.inner x (Gf x) (GΔf x)) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; exact h_bochner x
  -- Step 2: split the right-hand side using linearity of the integral.
  have h_int_hess2 : Integrable (fun x : M => 2 * hessSqNorm x) μ :=
    integrable_of_cont (continuous_const.mul h_hessSqNorm_cont)
  have h_int_ric2 : Integrable (fun x : M => 2 * RicAtGrad x) μ :=
    integrable_of_cont (continuous_const.mul h_RicAtGrad_cont)
  have h_int_inner2 :
      Integrable (fun x : M => 2 * g.inner x (Gf x) (GΔf x)) μ :=
    integrable_of_cont (continuous_const.mul hgrad_Δ_inner_cont)
  have h_int_first_two :
      Integrable (fun x : M => 2 * hessSqNorm x + 2 * RicAtGrad x) μ :=
    h_int_hess2.add h_int_ric2
  have h_sum :
      ∫ x, (2 * hessSqNorm x + 2 * RicAtGrad x +
            2 * g.inner x (Gf x) (GΔf x)) ∂μ =
        (∫ x, 2 * hessSqNorm x ∂μ) +
          (∫ x, 2 * RicAtGrad x ∂μ) +
          (∫ x, 2 * g.inner x (Gf x) (GΔf x) ∂μ) := by
    rw [integral_add h_int_first_two h_int_inner2,
        integral_add h_int_hess2 h_int_ric2]
  -- Step 3: pull constants out of each integral.
  have h_pullout1 :
      ∫ x, 2 * hessSqNorm x ∂μ = 2 * (∫ x, hessSqNorm x ∂μ) :=
    integral_const_mul _ _
  have h_pullout2 :
      ∫ x, 2 * RicAtGrad x ∂μ = 2 * (∫ x, RicAtGrad x ∂μ) :=
    integral_const_mul _ _
  have h_pullout3 :
      ∫ x, 2 * g.inner x (Gf x) (GΔf x) ∂μ =
        2 * (∫ x, g.inner x (Gf x) (GΔf x) ∂μ) :=
    integral_const_mul _ _
  have h_main_zero :
      0 = 2 * (∫ x, hessSqNorm x ∂μ) +
            2 * (∫ x, RicAtGrad x ∂μ) +
            2 * (∫ x, g.inner x (Gf x) (GΔf x) ∂μ) := by
    rw [← h_pullout1, ← h_pullout2, ← h_pullout3, ← h_sum, ← h_bochner_int,
      h_LHS_zero]
  -- Step 4: identify `g(∇f, ∇Δf) = -λ |∇f|²` pointwise. Use `inner_gradFun_right`
  -- and the fact that `Δf = -λ f` is a pointwise function equation.
  have h_eigen_inner :
      ∀ x : M, g.inner x (Gf x) (GΔf x) =
        -lam * g.inner x (Gf x) (Gf x) := by
    intro x
    have h_GΔf_apply : (GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g (Δ_g (I := I) g hf) x := by
      rw [hGΔf_def]; rfl
    have h_Gf_apply : (Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g f x := by
      rw [hGf_def]; rfl
    rw [h_GΔf_apply, h_Gf_apply]
    -- Both sides become `g.inner x (gradFun g f x) (gradFun g (Δ_g g hf) x)`
    -- and `(-λ) * g.inner x (gradFun g f x) (gradFun g f x)`.
    -- Pin the mfderiv codomain to `ℝ` for clean type handling.
    set d_f : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x with hd_f_def
    set d_Δf : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) (Δ_g (I := I) g hf) x
        with hd_Δf_def
    -- Use `inner_gradFun_right` (with the `: ℝ` codomain) to rewrite the LHS
    -- to `d_Δf v` where `v = gradFun g f x`.
    have h_lhs_eq :
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g (Δ_g (I := I) g hf) x)
          = d_Δf (gradFun (I := I) g f x) := by
      rw [hd_Δf_def]
      exact inner_gradFun_right (I := I) g (Δ_g (I := I) g hf) x
        (gradFun (I := I) g f x)
    have h_rhs_eq :
        g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)
          = d_f (gradFun (I := I) g f x) := by
      rw [hd_f_def]
      exact inner_gradFun (I := I) g f x (gradFun (I := I) g f x)
    rw [h_lhs_eq, h_rhs_eq]
    -- Goal: `d_Δf v = -λ * d_f v` where `v = gradFun g f x`.
    -- Use that `Δ_g g hf =ᶠ[𝓝 x] (-λ) • f` (pointwise equation), so
    -- `mfderiv (Δ_g g hf) x = mfderiv ((-λ) • f) x = (-λ) • mfderiv f x`.
    have h_eq_fun : ∀ y : M, Δ_g (I := I) g hf y = ((-lam) • f) y := by
      intro y; exact hf_eigen y
    have h_eqOn_nhd : Δ_g (I := I) g hf =ᶠ[𝓝 x] ((-lam) • f) :=
      Filter.Eventually.of_forall h_eq_fun
    have h_d_Δf_eq : d_Δf = (-lam) • d_f := by
      rw [hd_Δf_def, hd_f_def]
      rw [Filter.EventuallyEq.mfderiv_eq h_eqOn_nhd]
      exact const_smul_mfderiv (hf.mdifferentiable (by simp) x) (-lam)
    rw [h_d_Δf_eq]
    -- `((-λ) • d_f) v = -λ * d_f v` since `d_f v : ℝ`.
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h_int_eigen_inner :
      ∫ x, g.inner x (Gf x) (GΔf x) ∂μ =
        -lam * ∫ x, g.inner x (Gf x) (Gf x) ∂μ := by
    have h_pt :
        (fun x : M => g.inner x (Gf x) (GΔf x)) =
          (fun x : M => -lam * g.inner x (Gf x) (Gf x)) := by
      funext x; exact h_eigen_inner x
    rw [h_pt, integral_const_mul]
  -- Step 5: Green's first identity gives `∫ |∇f|² = -∫ f * Δf`. Substitute the
  -- eigenvalue equation: `f * Δf = -λ * f * f`. Hence `∫ |∇f|² = λ * ∫ f²`.
  have h_green :
      ∫ x, g.inner x (Gf x) (Gf x) ∂μ =
        -∫ x, f x * Δ_g (I := I) g hf x ∂μ :=
    integral_inner_grad_self_eq_neg_integral_f_Δf (I := I) g hf
  have h_f_Δf_pt : ∀ x : M, f x * Δ_g (I := I) g hf x = -lam * (f x * f x) := by
    intro x
    rw [hf_eigen x]
    ring
  have h_int_f_Δf :
      ∫ x, f x * Δ_g (I := I) g hf x ∂μ =
        -lam * ∫ x, f x * f x ∂μ := by
    have h_pt :
        (fun x : M => f x * Δ_g (I := I) g hf x) =
          (fun x : M => -lam * (f x * f x)) := by
      funext x; exact h_f_Δf_pt x
    rw [h_pt, integral_const_mul]
  have h_int_grad_sq :
      ∫ x, g.inner x (Gf x) (Gf x) ∂μ =
        lam * ∫ x, f x * f x ∂μ := by
    rw [h_green, h_int_f_Δf]
    ring
  -- Step 6: Hessian Frobenius lower bound integrated.
  have h_int_hess_bound :
      ∫ x, (Δ_g (I := I) g hf x)^2 / n ∂μ ≤
        ∫ x, hessSqNorm x ∂μ := by
    apply integral_mono_of_nonneg
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 : 0 ≤ (Δ_g (I := I) g hf x)^2 := sq_nonneg _
      exact div_nonneg h1 hn_pos.le
    · exact integrable_of_cont h_hessSqNorm_cont
    · refine Filter.Eventually.of_forall (fun x => ?_)
      exact h_hess_lower_bound x
  -- Pointwise non-negativity of `g.inner x v v` for any tangent vector `v`.
  have h_inner_self_nonneg : ∀ x : M, 0 ≤ g.inner x (Gf x) (Gf x) := by
    intro x
    by_cases hv : (Gf : ∀ x, TangentSpace I x) x = 0
    · rw [hv]; simp
    · exact (g.pos x _ hv).le
  have h_int_ricci_bound :
      ∫ x, (n - 1) * K *
          g.inner x (Gf x) (Gf x) ∂μ ≤
        ∫ x, RicAtGrad x ∂μ := by
    apply integral_mono_of_nonneg
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have h_prod1 : 0 ≤ (n - 1) * K := mul_nonneg hn_minus_one_pos.le hK.le
      exact mul_nonneg h_prod1 (h_inner_self_nonneg x)
    · exact integrable_of_cont h_RicAtGrad_cont
    · refine Filter.Eventually.of_forall (fun x => ?_)
      exact h_ricci_lower_bound x
  -- Step 7: simplify the Hessian lower bound using `(Δf)² = λ² f²`.
  have h_Δf_sq_eq : ∀ x : M, (Δ_g (I := I) g hf x)^2 = lam^2 * (f x * f x) := by
    intro x
    rw [hf_eigen x]
    ring
  have h_int_Δf_sq :
      ∫ x, (Δ_g (I := I) g hf x)^2 / n ∂μ =
        (lam^2 / n) * ∫ x, f x * f x ∂μ := by
    have h_pt :
        (fun x : M => (Δ_g (I := I) g hf x)^2 / n) =
          (fun x : M => (lam^2 / n) * (f x * f x)) := by
      funext x
      rw [h_Δf_sq_eq x]
      field_simp
    rw [h_pt, integral_const_mul]
  -- Simplify the Ricci lower bound using `∫ |∇f|² = λ ∫ f²`.
  have h_int_ricci_lower_simplified :
      ∫ x, (n - 1) * K *
          g.inner x (Gf x) (Gf x) ∂μ =
        ((n - 1) * K) * (lam * ∫ x, f x * f x ∂μ) := by
    have h_pt :
        (fun x : M => (n - 1) * K * g.inner x (Gf x) (Gf x)) =
          (fun x : M => ((n - 1) * K) * g.inner x (Gf x) (Gf x)) := by
      funext x; ring
    rw [h_pt, integral_const_mul, h_int_grad_sq]
  -- Step 8: assemble. `0 = 2 ∫ |∇²f|² + 2 ∫ Ric + 2 ∫ g(∇f, ∇Δf)`,
  -- and `∫ g(∇f, ∇Δf) = -λ * (λ * S) = -λ² S` where `S := ∫ f² > 0`.
  set S : ℝ := ∫ x, f x * f x ∂μ with hS_def
  have hS_pos : 0 < S := h_f_sq_pos
  have h_int_inner_grad_Δ : ∫ x, g.inner x (Gf x) (GΔf x) ∂μ = -lam * (lam * S) := by
    rw [h_int_eigen_inner, h_int_grad_sq, hS_def]
  -- So `0 = 2 (∫ hessSqNorm) + 2 (∫ Ric) - 2 λ² S`.
  have h_main_zero_subst :
      0 = 2 * (∫ x, hessSqNorm x ∂μ) +
            2 * (∫ x, RicAtGrad x ∂μ) -
            2 * lam^2 * S := by
    have := h_main_zero
    rw [h_int_inner_grad_Δ] at this
    linarith [this]
  -- Hence `2 λ² S = 2 (∫ hessSqNorm) + 2 (∫ Ric)`.
  have h_bochner_balanced :
      2 * lam^2 * S = 2 * (∫ x, hessSqNorm x ∂μ) +
            2 * (∫ x, RicAtGrad x ∂μ) := by
    linarith
  -- Apply the simplified lower bounds.
  have h_hess_int_lower : (lam^2 / n) * S ≤ ∫ x, hessSqNorm x ∂μ := by
    have := h_int_hess_bound
    rw [h_int_Δf_sq] at this
    exact this
  have h_ric_int_lower : ((n - 1) * K) * (lam * S) ≤ ∫ x, RicAtGrad x ∂μ := by
    have := h_int_ricci_bound
    rw [h_int_ricci_lower_simplified] at this
    exact this
  -- So `2 λ² S ≥ 2 (λ²/n) S + 2 (n-1) K λ S`.
  have h_chain :
      2 * (lam^2 / n) * S + 2 * ((n - 1) * K) * (lam * S) ≤
        2 * lam^2 * S := by
    rw [h_bochner_balanced]
    linarith [h_hess_int_lower, h_ric_int_lower]
  -- Divide by 2.
  have h_chain2 :
      (lam^2 / n) * S + ((n - 1) * K) * (lam * S) ≤ lam^2 * S := by
    linarith
  -- Move `(λ²/n) S` to the right: `(n-1) K λ S ≤ λ² S - (λ²/n) S = λ² S (n-1)/n`.
  have h_chain3 :
      ((n - 1) * K) * (lam * S) ≤ lam^2 * S * (n - 1) / n := by
    have h1 : lam^2 * S - lam^2 / n * S = lam^2 * S * (n - 1) / n := by
      have hne : n ≠ 0 := ne_of_gt hn_pos
      field_simp
    linarith [h_chain2, h1]
  -- Multiply by n on both sides:
  --     n * ((n-1) K) * (λ S) ≤ λ² S * (n-1).
  have hlam_S_pos : 0 < lam * S := mul_pos hlam_pos hS_pos
  have h_factor_pos : 0 < (n - 1) * (lam * S) := mul_pos hn_minus_one_pos hlam_S_pos
  have h_n_chain : n * (((n - 1) * K) * (lam * S)) ≤ lam^2 * S * (n - 1) := by
    have h1 : n * (lam^2 * S * (n - 1) / n) = lam^2 * S * (n - 1) := by
      field_simp
    have h2 : n * (((n - 1) * K) * (lam * S)) ≤ n * (lam^2 * S * (n - 1) / n) :=
      mul_le_mul_of_nonneg_left h_chain3 hn_pos.le
    linarith [h1, h2]
  -- Rearrange to the form `(n K) * a ≤ λ * a` with `a = (n-1) λ S > 0`.
  have h_rearrange1 :
      n * (((n - 1) * K) * (lam * S)) = (n * K) * ((n - 1) * (lam * S)) := by ring
  have h_rearrange2 :
      lam^2 * S * (n - 1) = lam * ((n - 1) * (lam * S)) := by ring
  rw [h_rearrange1, h_rearrange2] at h_n_chain
  -- `(n K) * a ≤ λ * a` and `a > 0` ⇒ `n K ≤ λ`.
  exact le_of_mul_le_mul_right (by linarith [h_n_chain]) h_factor_pos

end Laplacian
end Analysis
end DifferentialGeometry
