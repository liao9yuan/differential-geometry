import DifferentialGeometry.Integral.DivergenceTheorem.Closed
import DifferentialGeometry.Integral.DivergenceTheorem.Green
import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Geometry.Laplacian
import DifferentialGeometry.Geometry.NormGradSq
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Integral.Connection.BochnerConcrete
import DifferentialGeometry.Integral.Connection.ChartBridge.Hessian
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

1. **Bochner identity**:
   `Δ |∇f|² = 2 |∇²f|² + 2 Ric(∇f, ∇f) + 2 g(∇f, ∇(Δf))` pointwise.
2. **Divergence theorem on a closed manifold**: `∫ Δ φ d μ_g = 0` for any
   smooth scalar `φ`.
3. **Eigenvalue equation**: `Δ f = -λ f` so `∇(Δf) = -λ ∇f`, hence
   `g(∇f, ∇(Δf)) = -λ |∇f|²`.
4. **Cauchy-Schwarz Hessian bound**: `|∇²f|² ≥ (Δf)² / n`.
5. **Ricci bound**: `Ric(∇f, ∇f) ≥ (n - 1) K |∇f|²`.
6. **Green's first identity** (integration by parts): `∫ |∇f|² = -∫ f Δf
    = λ ∫ f²`.
7. **Strict positivity of the L² self-integral** for the nonzero
   eigenfunction: `0 < ∫ f²`.

Combining these inputs, the equation `0 = ∫ Δ |∇f|²` forces `λ ≥ n K`.

This file delivers the inequality in two forms:

* `lichnerowicz_inequality` is the abstract foundation: it takes the
  Bochner identity, the Hessian Cauchy-Schwarz bound, the Ricci bound, and
  the L² positivity of `f` as scalar hypotheses on `M`.
* `lichnerowicz_closed_unconditional` is the headline endpoint: with the
  abstract scalar witnesses replaced by the concrete `chartHessFrobeniusSq`
  and the abstract `ricciTensor`, all of the analytic ingredients (Bochner
  identity, Cauchy-Schwarz Hessian bound, smoothness witnesses, and
  continuity of the Hessian-Frobenius and Ricci-on-gradient functions) are
  discharged from the project's existing infrastructure. The user supplies
  only the eigenvalue equation, the universal Ricci lower bound, and the
  L²-positivity hypothesis.

## Main results

* `lichnerowicz_inequality` : the eigenvalue lower bound `n K ≤ λ` from the
  abstract scalar hypotheses.
* `lichnerowicz_closed_unconditional` : the same lower bound `n K ≤ λ` with
  all auxiliary continuity, Bochner, and Hessian-trace hypotheses
  discharged internally.
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
open DifferentialGeometry.Integral.Connection

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

/-! ## The Lichnerowicz eigenvalue inequality (abstract form)

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

/-! ## Unconditional form

The unconditional version takes the abstract scalar witnesses of
`lichnerowicz_inequality` and instantiates them with the concrete
`chartHessFrobeniusSq` and the abstract `ricciTensor`, discharging the
Bochner identity, the Cauchy-Schwarz Hessian bound, and the continuity
witnesses from the project's existing infrastructure. -/

/-! ### Helpers: Parseval-style expansion on a `g_x`-orthonormal basis -/

/-- **Parseval expansion of `|u|²_g` on a `g_x`-orthonormal basis.**
For any `g_x`-orthonormal basis `B : Fin n → T_x M` and any tangent vector
`u ∈ T_x M`, the squared `g_x`-norm of `u` equals the sum of squared inner
products with the basis vectors:
`g.inner x u u = ∑ j, (g.inner x u (B j))²`. -/
private theorem g_inner_self_eq_sum_sq_inner_orthonormal
    (g : SmoothRiemannianMetric I M) (x : M)
    (u : TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB_basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hB_eq : ∀ i, hB_basis i = B i)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    g.inner x u u =
      ∑ j : Fin (Module.finrank ℝ E), (g.inner x u (B j))^2 := by
  classical
  -- Decompose `u = ∑ j (hB_basis.repr u) j • B j`.
  -- Use a let-binding `c` for the coefficients to avoid rewriting them when
  -- substituting `u`.
  set c : Fin (Module.finrank ℝ E) → ℝ := fun j => hB_basis.repr u j with hc_def
  have hu_decomp : u =
      ∑ j : Fin (Module.finrank ℝ E),
        c j • (B j : TangentSpace I x) := by
    have h : (∑ i : Fin (Module.finrank ℝ E),
        hB_basis.repr u i • (hB_basis i : TangentSpace I x)) = u :=
      hB_basis.sum_repr u
    -- Goal after `← h`: `∑ i, hB_basis.repr u i • hB_basis i = ∑ j, c j • B j`.
    rw [← h]
    -- Both sums are indexed identically; congruence: `c j = hB_basis.repr u j`
    -- and `B j = hB_basis j`.
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hB_eq i]
  -- For each `k`, identify the basis-rep coefficient with `g.inner x u (B k)`.
  -- Compute `g.inner x u (B k) = g.inner x (∑ j c_j • B j) (B k) =
  --   ∑ j c_j * g.inner x (B j) (B k) = c_k`, using orthonormality.
  have h_coeff : ∀ k : Fin (Module.finrank ℝ E),
      g.inner x u (B k) = c k := by
    intro k
    -- LHS = g.inner x (B k) u (by g.symm).
    rw [g.symm x u (B k)]
    -- Apply g.inner x (B k) to both sides of `hu_decomp`.
    have hgoal :
        g.inner x (B k) u =
          ∑ j : Fin (Module.finrank ℝ E), c j * g.inner x (B k) (B j) := by
      have h_apply : (g.inner x (B k)) u =
          (g.inner x (B k)) (∑ j : Fin (Module.finrank ℝ E),
            c j • (B j : TangentSpace I x)) :=
        congrArg (g.inner x (B k)) hu_decomp
      rw [h_apply]
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [(g.inner x (B k)).map_smul (c j) (B j), smul_eq_mul]
    rw [hgoal]
    -- Apply orthonormality.
    rw [show (∑ j : Fin (Module.finrank ℝ E),
          c j * g.inner x (B k) (B j)) =
        ∑ j : Fin (Module.finrank ℝ E),
          c j * (if k = j then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hB_orth k j]]
    -- Only the `j = k` summand survives.
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  -- Now `g.inner x u u = ∑ j c j² = ∑ j (g.inner x u (B j))²`.
  -- Use `map_sum` on the second slot only.
  have hgoal :
      g.inner x u u = ∑ j : Fin (Module.finrank ℝ E),
        c j * g.inner x u (B j) := by
    -- `g.inner x u : T_x M →L ℝ`. Apply it to both sides of `hu_decomp`.
    have h_apply : (g.inner x u) u =
        (g.inner x u) (∑ j : Fin (Module.finrank ℝ E),
          c j • (B j : TangentSpace I x)) :=
      congrArg (g.inner x u) hu_decomp
    rw [h_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [(g.inner x u).map_smul (c j) (B j), smul_eq_mul]
  rw [hgoal]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [h_coeff j]
  ring

/-! ### Pointwise dimension-Laplacian Cauchy-Schwarz inequality

The argument works at a single point `x`. We pick the `g_x`-orthonormal frame
`B_i := smoothOrthoFrame g x i x`.

* `∑_i abstractHessian g f x (B_i) (B_i) = Δ_g g hf x`, via
  `sum_abstractHessian_orthonormal_eq_laplacian`.

* `∑_{ij} (abstractHessian g f x (B_i) (B_j))² = chartHessFrobeniusSq g f x`,
  using the Parseval identity above to expand
  `|T(B_i)|²_g = ∑_j (g(T(B_i), B_j))²` (where `T = LC g (∇f) x`) and the
  bridge `frobeniusSq_grad_vector_eq_chartHessFrobeniusSq`.

* The basis-naive Cauchy-Schwarz `bilinForm_trace_sq_le_card_mul_frobenius_sq`
  applied to the bilinear form `abstractHessianLin g f x` and the vectors `B`
  closes the inequality.
-/

/-- **Pointwise dimension-Laplacian inequality, unconditional form.**
For a closed-input smooth scalar `f` on a boundaryless smooth Riemannian
manifold,
`(Δ_g g hf x)² ≤ (finrank ℝ E) · chartHessFrobeniusSq g f x`. -/
private theorem laplacian_sq_le_dim_mul_chartHessFrobeniusSq_pointwise
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (Δ_g (I := I) g hf x)^2 ≤
      (Module.finrank ℝ E : ℝ) * chartHessFrobeniusSq (I := I) g f x := by
  classical
  -- Pick the smooth orthonormal frame at `x`, evaluated at `x`.
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  -- Step 1: the basis-naive Cauchy-Schwarz on `abstractHessianLin g f x`.
  have hCS :
      (∑ i : Fin (Module.finrank ℝ E),
        abstractHessianLin (I := I) g f x (B i) (B i))^2 ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) *
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (abstractHessianLin (I := I) g f x (B i) (B j))^2 :=
    bilinForm_trace_sq_le_card_mul_frobenius_sq
      (V := TangentSpace I x) (ι := Fin (Module.finrank ℝ E))
      (abstractHessianLin (I := I) g f x) B
  rw [Fintype.card_fin] at hCS
  -- Step 2: identify the LHS with `(Δ_g g hf x)²`.
  have hLHS_eq : ∑ i : Fin (Module.finrank ℝ E),
      abstractHessianLin (I := I) g f x (B i) (B i) =
      Δ_g (I := I) g hf x := by
    -- `abstractHessianLin = abstractHessian` and the orthonormal-frame trace
    -- identity `sum_abstractHessian_orthonormal_eq_laplacian` is in the
    -- `Connection` namespace.
    have h := sum_abstractHessian_orthonormal_eq_laplacian (I := I) g hf x B hB_orth
    refine h ▸ ?_
    refine Finset.sum_congr rfl ?_
    intro i _
    exact abstractHessianLin_apply (I := I) g f x (B i) (B i)
  rw [hLHS_eq] at hCS
  -- Step 3: identify the RHS with `n · chartHessFrobeniusSq g f x`.
  -- Each row sum `∑_j (abstractHessian g f x (B_i) (B_j))²` equals
  -- `|T(B_i)|²_g` where `T = LC g (∇f) x`, by the Parseval expansion.
  set T : TangentSpace I x →L[ℝ] TangentSpace I x :=
    (LeviCivita (I := I) g).toFun
      (fun b : M => gradFun (I := I) g f b) x with hT_def
  -- Bridge: `abstractHessianLin g f x v w = g.inner x (T v) w`.
  have h_AH_eq_inner : ∀ v w : TangentSpace I x,
      abstractHessianLin (I := I) g f x v w =
        g.inner x (T v) w := by
    intro v w
    rw [abstractHessianLin_apply (I := I) g f x v w]
    rw [hT_def]
    -- `abstractHessian g f x v w = g.inner x ((LC g)(∇f) x v) w`.
    rw [(abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf x v w).symm]
  -- Row-sum Parseval identity using the `g_x`-orthonormal basis structure on
  -- `B`. The `Module.finBasis ℝ E` is a basis of `TangentSpace I x = E`, but
  -- so is any orthonormal tuple. We assemble the basis from `B`:
  -- it has the right cardinality `n`, and is linearly independent because
  -- it is `g_x`-orthonormal in a positive-definite inner product.
  -- Construct the basis from B.
  have hB_li : LinearIndependent ℝ B := by
    rw [linearIndependent_iff']
    intro s c hsum k hk_mem
    -- `g_x(B_k, ∑ s_j c_j • B_j) = c_k` by orthonormality, but the sum is 0,
    -- so `c_k = 0`.
    have h_zero : g.inner x (B k) (∑ j ∈ s, c j • B j) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ s, g.inner x (B k) (c j • B j) =
        c j * g.inner x (B k) (B j) := by
      intro j _
      rw [(g.inner x (B k)).map_smul (c j) (B j), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    -- Use orthonormality: g.inner x (B k) (B j) = if k = j then 1 else 0
    -- (note the symmetry `B k, B j` vs `B j, B k`).
    have h_pull2 : ∀ j ∈ s, c j * g.inner x (B k) (B j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    -- Only `j = k` (in `s`) contributes.
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  -- Assemble the basis `hB_basis`.
  have hpos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    Fin.pos_iff_nonempty.mp hpos
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    -- TangentSpace I x = E definitionally.
    rfl
  -- `Module.Basis` from a linearly independent family of correct cardinality.
  set hB_basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hB_li hcard with hB_basis_def
  have hB_basis_eq : ∀ i, hB_basis i = B i := by
    intro i
    rw [hB_basis_def]
    -- Use the simp lemma `coe_basisOfLinearIndependentOfCardEqFinrank`.
    change (basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  -- Apply the Parseval identity row by row.
  have h_row : ∀ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
          (abstractHessianLin (I := I) g f x (B i) (B j))^2 =
        g.inner x (T (B i)) (T (B i)) := by
    intro i
    -- LHS = ∑_j (g(T(B_i), B_j))² (after `h_AH_eq_inner`).
    rw [show (∑ j : Fin (Module.finrank ℝ E),
            (abstractHessianLin (I := I) g f x (B i) (B j))^2) =
        ∑ j : Fin (Module.finrank ℝ E),
            (g.inner x (T (B i)) (B j))^2 from by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_AH_eq_inner (B i) (B j)]]
    -- This equals `|T(B_i)|²_g` by Parseval.
    exact (g_inner_self_eq_sum_sq_inner_orthonormal
      (g := g) (x := x) (u := T (B i)) (B := B)
      (hB_basis := hB_basis) (hB_eq := hB_basis_eq) (hB_orth := hB_orth)).symm
  -- Sum over `i`: `∑_{ij} = ∑_i |T(B_i)|²_g = frobeniusSq_grad_vector g (∇f) x`.
  have h_full_sum :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (abstractHessianLin (I := I) g f x (B i) (B j))^2 =
        frobeniusSq_grad_vector (I := I) g
          (fun b : M => gradFun (I := I) g f b) x := by
    rw [frobeniusSq_grad_vector_def]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact h_row i
  rw [h_full_sum] at hCS
  -- Bridge `frobeniusSq_grad_vector g (∇f) x = chartHessFrobeniusSq g f x`.
  rw [frobeniusSq_grad_vector_eq_chartHessFrobeniusSq (I := I) g hf x] at hCS
  exact hCS

/-! ### Continuity of the Ricci pairing on the gradient -/

/-- Smoothness of `b ↦ ricciTensor g b (∇f b) (∇f b)` for smooth `f`. -/
private theorem ricciTensor_grad_grad_contMDiff
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ricciTensor (I := I) g b
        (gradFun (I := I) g f b) (gradFun (I := I) g f b)) := by
  classical
  -- Ricci tensor as a smooth section of the (0,2)-tensor bundle.
  have hRic := ricciTensor_contMDiff (I := I) g
  -- Gradient as a smooth section of the tangent bundle.
  have hG := gradFun_contMDiff_total_section (I := I) g hf
  -- Apply `ContMDiff.clm_bundle_apply₂` to get smoothness of the scalar pairing.
  have happ :
      ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ricciTensor (I := I) g m
              (gradFun (I := I) g f m) (gradFun (I := I) g f m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hRic hG hG
  -- Extract the scalar smoothness from the `TotalSpace.mk'` form.
  intro m
  have hpm := happ m
  rw [Bundle.contMDiffAt_totalSpace] at hpm
  exact hpm.2

/-- Continuity of `b ↦ ricciTensor g b (∇f b) (∇f b)`. -/
private theorem ricciTensor_grad_grad_continuous
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun b : M => ricciTensor (I := I) g b
      (gradFun (I := I) g f b) (gradFun (I := I) g f b)) :=
  (ricciTensor_grad_grad_contMDiff (I := I) g hf).continuous

/-! ### Continuity of the Hessian Frobenius squared

Derived algebraically from the unconditional Bochner identity by isolating
`chartHessFrobeniusSq` and using continuity of the other three terms. -/

/-- Continuity of `b ↦ chartHessFrobeniusSq g f b`. -/
theorem chartHessFrobeniusSq_continuous
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun b : M => chartHessFrobeniusSq (I := I) g f b) := by
  classical
  -- Set up the smooth gradient sections.
  set Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g (I := I) g hf with hGf_def
  have hΔf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (Δ_g (I := I) g hf) :=
    Δ_g_contMDiff (I := I) g hf
  set GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    grad_g (I := I) g hΔf with hGΔf_def
  -- Continuity of the three "other" terms in the Bochner identity.
  have h1 : Continuous (Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf)) :=
    (Δ_g_contMDiff (I := I) g (normGradSqFun_contMDiff (I := I) g hf)).continuous
  have h2 : Continuous (fun b : M => ricciTensor (I := I) g b
      (gradFun (I := I) g f b) (gradFun (I := I) g f b)) :=
    ricciTensor_grad_grad_continuous (I := I) g hf
  have h3 : Continuous (fun b : M => g.inner b
      ((Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b)
      ((GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b)) :=
    TangentBundle.continuous_g_inner_of_smooth_sections (I := I) g Gf GΔf
  -- The Bochner identity:
  -- 2 * chartHessFrobeniusSq g f x =
  --   Δ_g(|∇f|²)(x) - 2 * ricciTensor(...) - 2 * g.inner(...).
  have h_bochner_isolate : ∀ x : M,
      chartHessFrobeniusSq (I := I) g f x =
        ((Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x) -
          2 * ricciTensor (I := I) g x
            (gradFun (I := I) g f x) (gradFun (I := I) g f x) -
          2 * g.inner x
            ((Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) / 2 := by
    intro x
    have hB := bochner_pointwise_concrete_metric_unconditional (I := I) g hf x
    -- `(Gf x) = gradFun g f x` and `(GΔf x) = gradFun g (Δ_g g hf) x` by `grad_g_apply`.
    have hGf_x : (Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g f x := by
      rw [hGf_def]; rfl
    have hGΔf_x : (GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g (Δ_g (I := I) g hf) x := by
      rw [hGΔf_def]; rfl
    rw [hGf_x, hGΔf_x]
    linarith [hB]
  -- Match continuity of the RHS function.
  have hRHS_cont : Continuous (fun x : M =>
      ((Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x) -
        2 * ricciTensor (I := I) g x
          (gradFun (I := I) g f x) (gradFun (I := I) g f x) -
        2 * g.inner x
          ((Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) / 2) := by
    refine ((h1.sub (continuous_const.mul h2)).sub
      (continuous_const.mul h3)).div_const 2
  refine hRHS_cont.congr ?_
  intro x
  exact (h_bochner_isolate x).symm

/-! ### The closed-manifold Lichnerowicz inequality (unconditional form) -/

/-- **Lichnerowicz's eigenvalue inequality on a closed Riemannian manifold,
unconditional form.**

Let `(M, g)` be a closed (compact and boundaryless) smooth Riemannian
manifold of dimension `n := finrank ℝ E ≥ 2`. Suppose:

* `K > 0` is a positive lower curvature parameter.
* `f : M → ℝ` is smooth with `Δ_g f = -λ f` pointwise for some `λ > 0`
  (the eigenfunction equation).
* `Ric ≥ (n - 1) K g`, expressed in the universal form
  `(n - 1) K g(X, X) ≤ Ric(X, X)` for every tangent vector `X`,
  using the abstract `ricciTensor` of the Levi-Civita connection.
* `0 < ∫ f²` (this is automatic for a nonzero smooth function on a closed
  manifold; we expose it as an explicit hypothesis to keep the inequality
  block self-contained).

Then `n K ≤ λ`.

The Bochner-Weitzenböck pointwise identity, the Cauchy-Schwarz Hessian-trace
inequality, the smoothness of `|∇f|²_g`, and the continuity of the
Hessian-Frobenius and Ricci-on-gradient witnesses are all discharged from
the project's existing infrastructure; the user supplies only the
eigenvalue equation, the universal Ricci lower bound, and the L²-positivity
hypothesis. -/
theorem lichnerowicz_closed_unconditional
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hn_ge_two : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {lam : ℝ} (hlam_pos : 0 < lam)
    (hf_eigen : ∀ x : M, Δ_g (I := I) g hf x = -lam * f x)
    (h_ricci : ∀ x : M, ∀ X : TangentSpace I x,
      ((Module.finrank ℝ E : ℝ) - 1) * K * g.inner x X X ≤
        ricciTensor (I := I) g x X X)
    (h_f_sq_pos : 0 < ∫ x, f x * f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :
    (Module.finrank ℝ E : ℝ) * K ≤ lam := by
  classical
  -- Smoothness of the gradient norm squared.
  have hgrad_norm_sq_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => g.inner x
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) :=
    contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g hf) (grad_g (I := I) g hf)
  -- Continuity of `chartHessFrobeniusSq g f`.
  have h_frob_cont :
      Continuous (fun x : M => chartHessFrobeniusSq (I := I) g f x) :=
    chartHessFrobeniusSq_continuous (I := I) g hf
  -- Continuity of `ricciTensor g x (∇f x) (∇f x)`.
  have h_ricci_cont :
      Continuous (fun x : M => ricciTensor (I := I) g x
        (gradFun (I := I) g f x) (gradFun (I := I) g f x)) :=
    ricciTensor_grad_grad_continuous (I := I) g hf
  -- Bochner identity, with `gradFun` replaced by `grad_g … x` (definitionally
  -- equal via `grad_g_apply`).
  have h_bochner_section : ∀ x : M,
      Δ_g (I := I) g hgrad_norm_sq_smooth x =
        2 * chartHessFrobeniusSq (I := I) g f x +
          2 * ricciTensor (I := I) g x
            ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) +
          2 * g.inner x
            ((grad_g (I := I) g hf :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((grad_g (I := I) g (Δ_g_contMDiff (I := I) g hf) :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    have hB := bochner_pointwise_concrete_metric_unconditional (I := I) g hf x
    -- `Δ_g_contMDiff` uses the same smoothness witness mechanism as
    -- `bochner_pointwise_concrete_metric_unconditional`. Both LHS use the
    -- `normGradSqFun_contMDiff` witness. The resulting LHS scalars are equal
    -- because `Δ_g` depends only on `f`, not on the witness chosen (see
    -- `Δ_g_def`: it is `divergence_g (grad_g …)` which depends on `f` via
    -- `gradFun`).
    -- We rewrite `(grad_g g hf x) = gradFun g f x` and similarly for `Δf`.
    have hGf_x : (grad_g (I := I) g hf :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g f x := grad_g_apply (I := I) g hf x
    have hGΔf_x : (grad_g (I := I) g (Δ_g_contMDiff (I := I) g hf) :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        gradFun (I := I) g (Δ_g (I := I) g hf) x :=
      grad_g_apply (I := I) g (Δ_g_contMDiff (I := I) g hf) x
    rw [hGf_x, hGΔf_x]
    -- Reduce `Δ_g g hgrad_norm_sq_smooth x = Δ_g g (normGradSqFun_contMDiff g hf) x`.
    -- Both witnesses prove the same function is smooth, so the values agree.
    have hLHS_eq : Δ_g (I := I) g hgrad_norm_sq_smooth x =
        Δ_g (I := I) g (normGradSqFun_contMDiff (I := I) g hf) x := rfl
    rw [hLHS_eq]
    exact hB
  -- Pointwise Hessian-trace bound from the unconditional CS.
  have h_hess_lower_bound : ∀ x : M,
      (Δ_g (I := I) g hf x)^2 / (Module.finrank ℝ E : ℝ) ≤
        chartHessFrobeniusSq (I := I) g f x := by
    intro x
    have hne : (Module.finrank ℝ E : ℕ) ≠ 0 := NeZero.ne _
    have hpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
      have : (0 : ℕ) < Module.finrank ℝ E := Nat.pos_of_ne_zero hne
      exact_mod_cast this
    have h := laplacian_sq_le_dim_mul_chartHessFrobeniusSq_pointwise
      (I := I) g hf x
    exact (div_le_iff₀ hpos).mpr (by linarith [h])
  -- Apply the abstract `lichnerowicz_inequality`.
  exact lichnerowicz_inequality (I := I) (M := M) g hn_ge_two hK hf hlam_pos
    hf_eigen hgrad_norm_sq_smooth
    (fun x => chartHessFrobeniusSq (I := I) g f x) h_frob_cont
    (fun x => ricciTensor (I := I) g x
      ((grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
    (by
      refine h_ricci_cont.congr ?_
      intro x
      simp only [grad_g_apply])
    h_bochner_section
    h_hess_lower_bound
    (by
      intro x
      exact h_ricci x ((grad_g (I := I) g hf :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
    h_f_sq_pos

end Laplacian
end Analysis
end DifferentialGeometry

end
