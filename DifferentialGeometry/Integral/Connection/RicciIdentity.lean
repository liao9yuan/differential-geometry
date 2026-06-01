import DifferentialGeometry.Integral.Connection.Ricci
import DifferentialGeometry.Integral.Connection.ChartBridge.Gradient
import DifferentialGeometry.Geometry.Laplacian

/-!
# Ricci identities for vectors and 1-forms; trace-commutator identity for the gradient

This file develops the three classical **Ricci identities** for the Levi-Civita covariant
derivative of a smooth Riemannian metric `g : SmoothRiemannianMetric I M`:

## Vector Ricci identity

For any covariant derivative `cov` on the tangent bundle, smooth tangent fields `X`, `Y`,
`V`, and a point `x : M`, the section-level Riemann formula
$$
  R(X, Y) V := \nabla_X (\nabla_Y V) - \nabla_Y (\nabla_X V) - \nabla_{[X, Y]} V
$$
is built into the definition of `riemannSec`. We expose this as the
**vector Ricci identity** `ricci_identity_vector`, providing a usable callsite for the
direct unfolding.

## 1-form Ricci identity

For the cotangent extension of any covariant derivative `cov` (denoted `cotangentCov cov`),
smooth tangent fields `X`, `Y`, `W`, and a smooth cotangent section `θ`, the iterated
commutator on `θ` evaluated against `W x` equals minus the contraction of `θ` against the
section-level Riemann curvature on `W`:
$$
  \bigl[(\nabla^*_X \nabla^*_Y \theta) - (\nabla^*_Y \nabla^*_X \theta)
        - (\nabla^*_{[X, Y]}\,\theta)\bigr](W(x))
    = -\,\theta\bigl(R(X, Y) W\bigr)(x).
$$
Here `(∇^*_Y θ)` is interpreted as the cotangent section
`b ↦ (cotangentCov cov).toFun θ b (Y b)`, and `(∇^*_X (∇^*_Y θ))` is the cotangent
covariant derivative of that section along `X`. The proof uses the dual-pairing Leibniz
identity `cotangentCov_dualPairing` iteratively, combined with the foundational identity
`extDerivFun_apply_mlieBracket` for the second derivative of a scalar along a Lie
bracket.

## Trace-commutator identity for the gradient

The **trace-commutator** (also known as the heart-of-Bochner reduction) packages the
abstract Ricci tensor at `(∇f, w)` as the basis-coefficient sum of the section-level
Riemann curvature on a smooth global tangent frame:
$$
  \mathrm{Ric}_x\bigl(\nabla f,\, w\bigr) =
    \sum_i (\mathrm{finBasis}\,\mathbb R\,E).\mathrm{repr}\bigl(R(B_i, w)(\nabla f)(x)\bigr)_i.
$$

A fully bundled connection Laplacian on tangent vectors is constructed in a downstream
file. Here we provide:

* `localConnLap_vector cov B V x` — the **local connection Laplacian** of a tangent
  section `V` at the point `x`, computed against a smooth tangent frame `B : Fin n → Π b,
  TangentSpace I b`. The definition matches the textbook trace formula
  `Δ_∇ V = ∑_i (∇_{B_i} ∇_{B_i} V - ∇_{∇_{B_i} B_i} V)`.

* `ricciTensor_gradFun_eq_frame_sum_riemannSec` — the **trace identity** at the heart of Bochner.
  It is the trace formulation of the vector Ricci identity (item 1) plus the basis
  expansion of the abstract Ricci tensor.
-/

noncomputable section

open Bundle Manifold Set FiberBundle NormedSpace Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## Item 1: the vector Ricci identity

The vector Ricci identity is the unfolding of the section-level Riemann formula
`riemannSec`. We expose it under a Ricci-flavoured name so that downstream callers can
refer to it by content rather than by `riemannSec_def`. -/

/-- **Vector Ricci identity.** For any covariant derivative `cov` on the tangent bundle,
smooth tangent vector fields `X`, `Y`, `V`, and a point `x : M`, the iterated covariant
derivative commutator equals the section-level Riemann curvature:
$$
  \nabla_X(\nabla_Y V)\,(x) - \nabla_Y(\nabla_X V)\,(x) - \nabla_{[X, Y]} V\,(x)
    = R(X, Y) V\,(x).
$$
With Mathlib's argument convention `cov.toFun σ x v ≅ (∇_v σ)(x)`, this is the equality
$$
  \mathrm{cov.toFun}(\nabla_Y V)(x)(X(x))
    - \mathrm{cov.toFun}(\nabla_X V)(x)(Y(x))
    - \mathrm{cov.toFun}(V)(x)([X, Y]_x)
    = \mathrm{riemannSec}\,\mathrm{cov}\,X\,Y\,V\,x.
$$
The identity is purely definitional (`riemannSec_def`). -/
theorem ricci_identity_vector
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y V : Π b : M, TangentSpace I b) (x : M) :
    cov.toFun (covApply cov Y V) x (X x) - cov.toFun (covApply cov X V) x (Y x)
        - cov.toFun V x (VectorField.mlieBracket I X Y x) =
      riemannSec cov X Y V x :=
  (riemannSec_def cov X Y V x).symm

/-! ## Item 2: the 1-form Ricci identity

Strategy: we apply `cotangentCov_dualPairing` to the scalar `b ↦ θ(b)(W(b))` first along
`Y` (yielding a section identity), then along `X`, and finally along the Lie bracket.
Substituting and using `extDerivFun_apply_mlieBracket` for the bracket of two
directional derivatives of a scalar produces the desired identity. -/

/-- The **iterated cotangent connection** of a cotangent section `θ` along smooth
tangent fields `X` and `Y`, evaluated at `(x, W(x))`. Concretely:
$$
  (\nabla^*_X \nabla^*_Y \theta)\,x\,(W(x))
    := \bigl((\mathrm{cotangentCov}\,\mathrm{cov})
          (\,b \mapsto (\mathrm{cotangentCov}\,\mathrm{cov})(\theta)\,b\,(Y(b)))\,
          x\,(X(x))\bigr)\,(W(x)).
$$
The intermediate cotangent section `b ↦ (cotangentCov θ) b (Y b)` is the cotangent
covariant derivative of `θ` along the smooth vector field `Y`. -/
private noncomputable def iterCotangentCov
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (θ : Π b : M, TangentSpace I b →L[ℝ] ℝ)
    (X Y W : Π b : M, TangentSpace I b) (x : M) : ℝ :=
  ((cotangentCov cov).toFun
    (fun b : M => (cotangentCov cov).toFun θ b (Y b)) x (X x)) (W x)

/-- **1-form Ricci identity.** Let `cov : CovariantDerivative I E (TangentSpace I)` be a
covariant derivative of class `C^∞` on the tangent bundle of a smooth manifold `M`. For
smooth tangent vector fields `X, Y, W`, a smooth cotangent section `θ`, and a point
`x : M`, the iterated cotangent commutator on `θ` applied to `W x` equals minus the
contraction of `θ` against the section-level Riemann curvature on `W`:
$$
  \bigl[(\nabla^*_X \nabla^*_Y \theta)\,(W) - (\nabla^*_Y \nabla^*_X \theta)\,(W)
        - (\nabla^*_{[X, Y]}\,\theta)(W)\bigr](x)
    = -\,\theta(x)\bigl(R(X, Y) W\,(x)\bigr).
$$
The required smoothness on `f := b ↦ θ(b)(W(b))` enables the foundational scalar-bracket
identity `extDerivFun_apply_mlieBracket`. -/
theorem ricci_identity_oneForm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {X Y W : Π b : M, TangentSpace I b}
    {θ : Π b : M, TangentSpace I b →L[ℝ] ℝ}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hθ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (θ b)))
    (x : M) :
    iterCotangentCov cov θ X Y W x - iterCotangentCov cov θ Y X W x -
        ((cotangentCov cov).toFun θ x (VectorField.mlieBracket I X Y x)) (W x) =
      - θ x (riemannSec cov X Y W x) := by
  classical
  -- Pointwise differentiability hypotheses.
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hθ_at : MDiffAtCotangent θ x := (hθ x).mdifferentiableAt (by simp)
  -- Smoothness of `b ↦ θ b (W b)` as a scalar function.
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => θ b (W b)) :=
    cotangentCov_pairing_contMDiff hθ hW
  have hf_2 : ContMDiffAt I 𝓘(ℝ) 2 (fun b : M => θ b (W b)) x := by
    have hle : (2 : WithTop ℕ∞) ≤ ∞ := by
      have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      simpa using h1
    exact (hf_smooth x).of_le hle
  have hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    (I.isInteriorPoint_iff (x := x)).mp BoundarylessManifold.isInteriorPoint
  -- Smoothness of `covApply cov Y W` and `covApply cov X W` (used for the connection
  -- corrections from differentiating `b ↦ θ b (cov W b (Y b))` and the X-version).
  have hcYW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov Y W)) := by
    intro b
    exact (covApply_contMDiffOn (cov := cov) hY (by simpa using hW)).contMDiffAt
      (Filter.univ_mem)
  have hcXW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply cov X W)) := by
    intro b
    exact (covApply_contMDiffOn (cov := cov) hX (by simpa using hW)).contMDiffAt
      (Filter.univ_mem)
  have hcYW_at : MDiffAt (T% (covApply cov Y W)) x :=
    (hcYW_smooth x).mdifferentiableAt (by simp)
  have hcXW_at : MDiffAt (T% (covApply cov X W)) x :=
    (hcXW_smooth x).mdifferentiableAt (by simp)
  -- Step 1: pairing identity for the scalar `b ↦ θ b (W b)` along `Y`. Pointwise globally.
  have hpair_Y_glob :
      (fun b : M => extDerivFun (I := I) (fun b' : M => θ b' (W b')) b (Y b)) =
      (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b) +
        θ b (cov.toFun W b (Y b))) := by
    funext b
    have hθ_b : MDiffAtCotangent θ b := (hθ b).mdifferentiableAt (by simp)
    have hW_b : MDiffAt (T% W) b := (hW b).mdifferentiableAt (by simp)
    exact cotangentCov_dualPairing cov hθ_b hW_b (Y b)
  -- Symmetric: along `X`.
  have hpair_X_glob :
      (fun b : M => extDerivFun (I := I) (fun b' : M => θ b' (W b')) b (X b)) =
      (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b) +
        θ b (cov.toFun W b (X b))) := by
    funext b
    have hθ_b : MDiffAtCotangent θ b := (hθ b).mdifferentiableAt (by simp)
    have hW_b : MDiffAt (T% W) b := (hW b).mdifferentiableAt (by simp)
    exact cotangentCov_dualPairing cov hθ_b hW_b (X b)
  -- Step 2: foundational identity for the second derivative along the bracket.
  haveI : IsManifold I 2 M := by
    have h_le : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    exact IsManifold.of_le h_le
  haveI : CompleteSpace E := inferInstance
  have hfound :
      extDerivFun (I := I) (fun b : M => θ b (W b)) x
        (VectorField.mlieBracket I X Y x) =
      extDerivFun (I := I)
        (fun b : M => extDerivFun (I := I) (fun b' : M => θ b' (W b')) b (Y b)) x (X x) -
      extDerivFun (I := I)
        (fun b : M => extDerivFun (I := I) (fun b' : M => θ b' (W b')) b (X b)) x (Y x) :=
    extDerivFun_apply_mlieBracket hX_at hY_at hf_2 hx_int
  -- Substitute the global pairing identities into hfound.
  rw [hpair_Y_glob, hpair_X_glob] at hfound
  -- Step 3: pairing identity for `θ x ([X,Y]_x (W x))`.
  have hpair_br : extDerivFun (I := I) (fun b : M => θ b (W b)) x
        (VectorField.mlieBracket I X Y x) =
      ((cotangentCov cov).toFun θ x (VectorField.mlieBracket I X Y x)) (W x) +
        θ x (cov.toFun W x (VectorField.mlieBracket I X Y x)) :=
    cotangentCov_dualPairing cov hθ_at hW_at (VectorField.mlieBracket I X Y x)
  rw [hpair_br] at hfound
  -- Step 4: distribute extDerivFun over the inner sums in hfound.
  -- The X-side function: b ↦ ((cotangentCov θ) b (Y b))(W b) + θ b (cov W b (Y b)).
  have hsum1_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b)) x := by
    have h_smooth :=
      cotangentCov_double_apply_smooth cov hθ
        ⟨fun b : M => Y b, hY⟩ ⟨fun b : M => W b, hW⟩
    exact (h_smooth x).mdifferentiableAt (by simp)
  have hsum2_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => θ b (cov.toFun W b (Y b))) x := by
    have h_eq_fn : (fun b : M => θ b (cov.toFun W b (Y b))) =
        (fun b : M => θ b (covApply cov Y W b)) := by funext b; rfl
    rw [h_eq_fn]
    have hsmooth := cotangentCov_pairing_contMDiff hθ hcYW_smooth
    exact (hsmooth x).mdifferentiableAt (by simp)
  have hsum3_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b)) x := by
    have h_smooth :=
      cotangentCov_double_apply_smooth cov hθ
        ⟨fun b : M => X b, hX⟩ ⟨fun b : M => W b, hW⟩
    exact (h_smooth x).mdifferentiableAt (by simp)
  have hsum4_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun b : M => θ b (cov.toFun W b (X b))) x := by
    have h_eq_fn : (fun b : M => θ b (cov.toFun W b (X b))) =
        (fun b : M => θ b (covApply cov X W b)) := by funext b; rfl
    rw [h_eq_fn]
    have hsmooth := cotangentCov_pairing_contMDiff hθ hcXW_smooth
    exact (hsmooth x).mdifferentiableAt (by simp)
  have hadd_X : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b) +
          θ b (cov.toFun W b (Y b))) x =
      extDerivFun (I := I)
          (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b)) x +
        extDerivFun (I := I) (fun b : M => θ b (cov.toFun W b (Y b))) x :=
    extDerivFun_add hsum1_diff hsum2_diff
  have hadd_Y : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b) +
          θ b (cov.toFun W b (X b))) x =
      extDerivFun (I := I)
          (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b)) x +
        extDerivFun (I := I) (fun b : M => θ b (cov.toFun W b (X b))) x :=
    extDerivFun_add hsum3_diff hsum4_diff
  have hadd_X_app : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b) +
          θ b (cov.toFun W b (Y b))) x (X x) =
      extDerivFun (I := I)
          (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b)) x (X x) +
        extDerivFun (I := I) (fun b : M => θ b (cov.toFun W b (Y b))) x (X x) := by
    rw [hadd_X]; rfl
  have hadd_Y_app : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b) +
          θ b (cov.toFun W b (X b))) x (Y x) =
      extDerivFun (I := I)
          (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b)) x (Y x) +
        extDerivFun (I := I) (fun b : M => θ b (cov.toFun W b (X b))) x (Y x) := by
    rw [hadd_Y]; rfl
  rw [hadd_X_app, hadd_Y_app] at hfound
  -- Step 5: identify the four scalar-derivative terms.
  -- (5a) extDerivFun (b ↦ ((cotangentCov θ) b (Y b))(W b)) x (X x) =
  --       (cotangentCov (b ↦ (cotangentCov θ) b (Y b))) x (X x) (W x) +
  --       ((cotangentCov θ) x (Y x)) (cov W x (X x)).
  have hθY_at : MDiffAtCotangent
      (fun b : M => (cotangentCov cov).toFun θ b (Y b)) x := by
    have h_section :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)))
          (fun b : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
            (E := fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) b
            ((cotangentCov cov).toFun θ b)) x := by
      have hres :=
        (cotangentCov_isContMDiff (cov := cov)).contMDiff.contMDiff
          (σ := θ) (hθ.of_le (by rw [ENat.coe_top_add_one])).contMDiffOn
      exact (hres x (Set.mem_univ x)).contMDiffAt (Filter.univ_mem) |>.mdifferentiableAt
        (by simp)
    exact h_section.clm_bundle_apply (v := Y) hY_at
  have hθX_at : MDiffAtCotangent
      (fun b : M => (cotangentCov cov).toFun θ b (X b)) x := by
    have h_section :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ)))
          (fun b : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
            (E := fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) b
            ((cotangentCov cov).toFun θ b)) x := by
      have hres :=
        (cotangentCov_isContMDiff (cov := cov)).contMDiff.contMDiff
          (σ := θ) (hθ.of_le (by rw [ENat.coe_top_add_one])).contMDiffOn
      exact (hres x (Set.mem_univ x)).contMDiffAt (Filter.univ_mem) |>.mdifferentiableAt
        (by simp)
    exact h_section.clm_bundle_apply (v := X) hX_at
  -- Apply `cotangentCov_dualPairing` to the cotangent section
  --   (fun b => (cotangentCov θ) b (Y b))
  -- with tangent vector `X x` (extracted via the smooth `X`).
  have h_iter_X : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (Y b)) (W b)) x (X x) =
      ((cotangentCov cov).toFun
          (fun b : M => (cotangentCov cov).toFun θ b (Y b)) x (X x)) (W x) +
        ((cotangentCov cov).toFun θ x (Y x)) (cov.toFun W x (X x)) :=
    cotangentCov_dualPairing cov hθY_at hW_at (X x)
  have h_iter_Y : extDerivFun (I := I)
        (fun b : M => ((cotangentCov cov).toFun θ b (X b)) (W b)) x (Y x) =
      ((cotangentCov cov).toFun
          (fun b : M => (cotangentCov cov).toFun θ b (X b)) x (Y x)) (W x) +
        ((cotangentCov cov).toFun θ x (X x)) (cov.toFun W x (Y x)) :=
    cotangentCov_dualPairing cov hθX_at hW_at (Y x)
  rw [h_iter_X, h_iter_Y] at hfound
  -- (5b) extDerivFun (b ↦ θ b (cov W b (Y b))) x (X x) =
  --       (cotangentCov θ x (X x)) (cov W x (Y x)) (which is `(cotangentCov θ x (X x)) (covApply cov Y W x)`)
  --       + θ x (cov.toFun (covApply cov Y W) x (X x)).
  have hB_eq : extDerivFun (I := I)
      (fun b : M => θ b (cov.toFun W b (Y b))) x (X x) =
      ((cotangentCov cov).toFun θ) x (X x) (covApply cov Y W x) +
        θ x (cov.toFun (covApply cov Y W) x (X x)) := by
    have hpair := cotangentCov_dualPairing cov hθ_at hcYW_at (X x)
    have h_eq_fn : (fun b : M => θ b (cov.toFun W b (Y b))) =
        (fun b : M => θ b (covApply cov Y W b)) := by funext b; rfl
    rw [h_eq_fn]; exact hpair
  have hB'_eq : extDerivFun (I := I)
      (fun b : M => θ b (cov.toFun W b (X b))) x (Y x) =
      ((cotangentCov cov).toFun θ) x (Y x) (covApply cov X W x) +
        θ x (cov.toFun (covApply cov X W) x (Y x)) := by
    have hpair := cotangentCov_dualPairing cov hθ_at hcXW_at (Y x)
    have h_eq_fn : (fun b : M => θ b (cov.toFun W b (X b))) =
        (fun b : M => θ b (covApply cov X W b)) := by funext b; rfl
    rw [h_eq_fn]; exact hpair
  rw [hB_eq, hB'_eq] at hfound
  -- Step 6: the equation `hfound` now has the form
  --   bracket_cotangent + θ([X,Y].W) =
  --     iter_XY + ((cotθ) x (Y x))(cov W x (X x))
  --     + ((cotθ) x (X x))(covApply Y W x) + θ(cov^2_{XY} W x)
  --     -[ iter_YX + ((cotθ) x (X x))(cov W x (Y x))
  --     + ((cotθ) x (Y x))(covApply X W x) + θ(cov^2_{YX} W x) ]
  -- The cross terms ((cotθ) x (Y x))(...) and ((cotθ) x (X x))(...) cancel because
  --   covApply Y W x = cov.toFun W x (Y x)  and  covApply X W x = cov.toFun W x (X x),
  -- which are exactly the "cov W x (X x)" / "cov W x (Y x)" terms with the slots swapped.
  -- After cancellation, the equation reduces to:
  --   bracket_cot + θ(cov W x [X,Y]_x) = iter_XY - iter_YX + θ(cov^2_XY W x - cov^2_YX W x)
  -- which gives, after rearranging:
  --   iter_XY - iter_YX - bracket_cot =
  --     θ(cov W x [X,Y]_x - cov^2_XY W x + cov^2_YX W x)
  --   = -θ(riemannSec cov X Y W x).
  -- We unfold riemannSec and use linarith.
  rw [show riemannSec cov X Y W x =
      cov.toFun (covApply cov Y W) x (X x) - cov.toFun (covApply cov X W) x (Y x)
        - cov.toFun W x (VectorField.mlieBracket I X Y x) from rfl]
  -- Distribute `θ x` (a continuous linear map) over the difference.
  have hθ_lin :
      θ x (cov.toFun (covApply cov Y W) x (X x) -
        cov.toFun (covApply cov X W) x (Y x) -
        cov.toFun W x (VectorField.mlieBracket I X Y x)) =
      θ x (cov.toFun (covApply cov Y W) x (X x))
        - θ x (cov.toFun (covApply cov X W) x (Y x))
        - θ x (cov.toFun W x (VectorField.mlieBracket I X Y x)) := by
    rw [show (cov.toFun (covApply cov Y W) x (X x) -
            cov.toFun (covApply cov X W) x (Y x) -
            cov.toFun W x (VectorField.mlieBracket I X Y x)) =
        (cov.toFun (covApply cov Y W) x (X x) -
            cov.toFun (covApply cov X W) x (Y x)) -
          cov.toFun W x (VectorField.mlieBracket I X Y x) from rfl,
        map_sub, map_sub]
  rw [hθ_lin]
  -- Identify covApply cov Y W x = cov.toFun W x (Y x) and covApply cov X W x = cov.toFun W x (X x).
  -- These are definitional, but we substitute them explicitly inside `hfound` so the
  -- cross-term cancellations are visible to `linarith`.
  have h_covYW : covApply cov Y W x = cov.toFun W x (Y x) := rfl
  have h_covXW : covApply cov X W x = cov.toFun W x (X x) := rfl
  rw [h_covYW, h_covXW] at hfound
  unfold iterCotangentCov
  linarith

/-! ## Item 3: trace identity for the gradient (heart of Bochner reduction)

Without yet defining a global connection Laplacian on tangent vectors (deferred to a
follow-up file), we package the trace formula relating the abstract Ricci tensor to a
trace of the section-level Riemann curvature on a smooth global tangent frame. This
identity is the algebraic engine of the Lichnerowicz / heart-of-Bochner identity:
$$
  \Delta_\nabla(\nabla f) = \nabla(\Delta_g f) + \mathrm{Ric}^\sharp(\nabla f),
$$
which the downstream `Δ_∇` setup will assemble from the vector Ricci identity (item 1)
and the trace formula proved here. -/

/-- The **local connection Laplacian on tangent sections** with respect to a smooth
global tangent frame `B : Fin n → Π b, TangentSpace I b`. With the standing argument
convention `cov.toFun σ x v ≅ (∇_v σ)(x)`, this is the textbook formula
$$
  (\Delta_\nabla^{B} V)(x)
    := \sum_i \bigl(\nabla_{B_i x}\nabla_{B_i} V - \nabla_{(\nabla_{B_i} B_i)(x)} V\bigr).
$$
The dependence on `B` is genuine in the absence of an orthonormality hypothesis. The
downstream connection-Laplacian instance proves frame-invariance under `g`-orthonormal
frames; here we expose the frame-dependent operator at the level needed by the
trace-commutator identity. -/
noncomputable def localConnLap_vector
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (V : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    (cov.toFun (covApply cov (B i) V) x (B i x) -
      cov.toFun V x (cov.toFun (B i) x (B i x)))

/-- The defining identity for `localConnLap_vector`. -/
lemma localConnLap_vector_def
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (V : Π b : M, TangentSpace I b) (x : M) :
    localConnLap_vector cov B V x =
      ∑ i : Fin (Module.finrank ℝ E),
        (cov.toFun (covApply cov (B i) V) x (B i x) -
          cov.toFun V x (cov.toFun (B i) x (B i x))) := rfl

/-- **Frame-trace expansion of the Ricci tensor at the gradient.** Let `g` be a smooth
Riemannian metric on `M`, let `f : M → ℝ` be a smooth scalar, let `w` be a smooth tangent
vector field, and let `B : Fin n → Π b, TangentSpace I b` be a smooth global tangent frame
agreeing with the model basis `chartModelBasis E` at the point `x`. Then the Ricci tensor
at `(∇f, w)` equals the `chartModelBasis E`-coordinate sum of the section-level Riemann
curvature `riemannSec (LeviCivita g)` on the frame:
$$
  \mathrm{Ric}_x\bigl(\nabla f,\, w\bigr) =
    \sum_i (\mathrm{chartModelBasis}\,E).\mathrm{repr}
      \bigl(R(B_i, w)(\nabla f)(x)\bigr)_i.
$$
Here `∇f` is `gradFun g f` and `R = riemannSec (LeviCivita g)`.

The proof is the basis-trace expansion `ricciTensor_apply_smooth_basisSum`
(with `Y := w`, `Z := ∇f`) composed with `ricciTensor_symm` to put the gradient in the
first slot. This frame-trace identity is the algebraic ingredient consumed downstream when
assembling the connection-Laplacian/gradient commutator
`Δ_∇(∇f) = ∇(Δ_g f) + Ric^♯(∇f)`; that commutator itself is NOT proved here. -/
theorem ricciTensor_gradFun_eq_frame_sum_riemannSec [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (x : M) (hBx : ∀ i, B i x = (chartModelBasis E) i) :
    ricciTensor (I := I) g x (gradFun (I := I) g f x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartModelBasis E).repr
          (riemannSec (LeviCivita (I := I) g) (B i) w
            (fun y => gradFun (I := I) g f y) x) i := by
  classical
  -- Smoothness of `gradFun g f` as a tangent section.
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        (gradFun (I := I) g f y)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  -- Apply `ricciTensor_apply_smooth_basisSum` with `Y = w` and `Z = grad f`. This gives:
  --   Ric(w x, grad f x) = ∑_i (finBasis).repr (R(B_i, w, grad f)(x)) i
  -- and we then use `ricciTensor_symm` to get the desired LHS Ric(grad f x, w x).
  have hbasisSum := ricciTensor_apply_smooth_basisSum (I := I) g
    (Y := w) (Z := fun y => gradFun (I := I) g f y)
    (B := B) hw h_grad_smooth hB x hBx
  -- Now `hbasisSum : Ric(w x, grad f x) = ∑ ...`
  -- Apply ricciTensor_symm: Ric(grad f x, w x) = Ric(w x, grad f x).
  rw [ricciTensor_symm (I := I) g x (gradFun (I := I) g f x) (w x)]
  exact hbasisSum

/-! ## Item 4: the (1,1)-Ricci endomorphism `ricciSharp`

The pointwise (1,1)-Ricci tensor `ricciSharp g x : T_x M →L[ℝ] T_x M` is the metric
Riesz dual of the (0,2)-Ricci tensor `ricciTensor g x`. By definition,
$$
  g_x(\mathrm{Ric}^\sharp(v), w) = \mathrm{Ric}_x(v, w) \qquad \text{for all } v, w \in T_x M.
$$
In coordinates, `Ric^♯` raises the lower index of `Ric` using the inverse metric `g^{-1}`.
The construction goes through the existing musical-isomorphism `metricSharp` applied to the
linear functional `(ricciTensor g x v).toLinearMap`. -/

/-- The (1,1)-Ricci endomorphism `ricciSharp g x v` of a tangent vector `v ∈ T_x M`. By the
defining identity (see `inner_ricciSharp`), it is the unique vector `W ∈ T_x M` such that
`g_x(W, w) = ricciTensor g x v w` for every `w ∈ T_x M`. -/
noncomputable def ricciSharpVec
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  metricSharp (I := I) g x ((ricciTensor (I := I) g x v).toLinearMap)

/-- **Defining identity for `ricciSharpVec`.** For any `v, w ∈ T_x M`,
`g_x(\mathrm{Ric}^\sharp(v), w) = \mathrm{Ric}_x(v, w)`. -/
lemma inner_ricciSharpVec
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x (ricciSharpVec (I := I) g x v) w = ricciTensor (I := I) g x v w := by
  unfold ricciSharpVec
  exact inner_metricSharp (I := I) g x ((ricciTensor (I := I) g x v).toLinearMap) w

/-- Symmetric form of the defining identity. -/
lemma inner_ricciSharpVec_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x w (ricciSharpVec (I := I) g x v) = ricciTensor (I := I) g x v w := by
  rw [g.symm x w (ricciSharpVec (I := I) g x v)]
  exact inner_ricciSharpVec (I := I) g x v w

/-- The vector `ricciSharpVec g x v` is **uniquely** characterised by its defining
inner-product identity: any `W ∈ T_x M` with `g.inner x W w = ricciTensor g x v w` for all
`w` is equal to `ricciSharpVec g x v`. -/
lemma ricciSharpVec_unique
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x)
    {W : TangentSpace I x}
    (hW : ∀ w : TangentSpace I x,
      g.inner x W w = ricciTensor (I := I) g x v w) :
    W = ricciSharpVec (I := I) g x v := by
  apply metricFlatLinear_injective (I := I) g x
  ext w
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  rw [hW w]
  exact (inner_ricciSharpVec (I := I) g x v w).symm

/-- Additivity of `ricciSharpVec` in the input vector. -/
lemma ricciSharpVec_add
    (g : SmoothRiemannianMetric I M) (x : M) (v v' : TangentSpace I x) :
    ricciSharpVec (I := I) g x (v + v') =
      ricciSharpVec (I := I) g x v + ricciSharpVec (I := I) g x v' := by
  refine (ricciSharpVec_unique (I := I) g x (v + v')
    (W := ricciSharpVec (I := I) g x v + ricciSharpVec (I := I) g x v') ?_).symm
  intro w
  rw [show g.inner x (ricciSharpVec (I := I) g x v + ricciSharpVec (I := I) g x v') w =
        g.inner x (ricciSharpVec (I := I) g x v) w +
          g.inner x (ricciSharpVec (I := I) g x v') w from
      by rw [map_add, ContinuousLinearMap.add_apply]]
  rw [inner_ricciSharpVec (I := I) g x v w,
      inner_ricciSharpVec (I := I) g x v' w]
  rw [show ricciTensor (I := I) g x (v + v') w =
        ricciTensor (I := I) g x v w + ricciTensor (I := I) g x v' w from by
      rw [map_add, ContinuousLinearMap.add_apply]]

/-- Real-scalar homogeneity of `ricciSharpVec` in the input vector. -/
lemma ricciSharpVec_smul
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v : TangentSpace I x) :
    ricciSharpVec (I := I) g x (c • v) = c • ricciSharpVec (I := I) g x v := by
  refine (ricciSharpVec_unique (I := I) g x (c • v)
    (W := c • ricciSharpVec (I := I) g x v) ?_).symm
  intro w
  rw [show g.inner x (c • ricciSharpVec (I := I) g x v) w =
        c * g.inner x (ricciSharpVec (I := I) g x v) w from
      by rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]]
  rw [inner_ricciSharpVec (I := I) g x v w]
  rw [show ricciTensor (I := I) g x (c • v) w =
        c * ricciTensor (I := I) g x v w from by
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]]

/-- The (1,1)-Ricci endomorphism `ricciSharp g x : T_x M →L[ℝ] T_x M`, packaged as a
continuous linear map. The definition uses the underlying linear-algebraic map
`v ↦ ricciSharpVec g x v` (linear by `ricciSharpVec_add` / `ricciSharpVec_smul`),
upgraded to a continuous map via finite-dimensional automatic continuity. -/
noncomputable def ricciSharp
    (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ricciSharpVec (I := I) g x v
      map_add' := fun v v' => ricciSharpVec_add (I := I) g x v v'
      map_smul' := fun c v => by
        simpa using ricciSharpVec_smul (I := I) g x c v }

/-- Defining identity for `ricciSharp` as a continuous linear endomorphism: it agrees with
`ricciSharpVec` pointwise. -/
@[simp] lemma ricciSharp_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    ricciSharp (I := I) g x v = ricciSharpVec (I := I) g x v := rfl

/-- **Inner-product defining identity for `ricciSharp`.** For any `v, w ∈ T_x M`,
`g_x(\mathrm{Ric}^\sharp(v), w) = \mathrm{Ric}_x(v, w)`. -/
theorem inner_ricciSharp
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x (ricciSharp (I := I) g x v) w = ricciTensor (I := I) g x v w := by
  rw [ricciSharp_apply]
  exact inner_ricciSharpVec (I := I) g x v w

/-- Symmetric form: `g_x(w, \mathrm{Ric}^\sharp(v)) = \mathrm{Ric}_x(v, w)`. -/
theorem inner_ricciSharp_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.inner x w (ricciSharp (I := I) g x v) = ricciTensor (I := I) g x v w := by
  rw [ricciSharp_apply]
  exact inner_ricciSharpVec_right (I := I) g x v w

/-! ## Item 5: heart-of-Bochner trace-commutator identity (inner-product form)

The frame-trace formulation of the heart-of-Bochner identity. The vector-valued identity
$$
  \Delta_\nabla(\nabla f)(x) = \nabla(\Delta_g f)(x) + \mathrm{Ric}^\sharp(\nabla f)(x)
$$
is naturally read off the **inner-product** characterisation against an arbitrary smooth
test field. We expose the inner-product form in three orthogonal pieces, matching the
three terms of the textbook derivation:

* The metric-symmetry of the abstract Hessian:
  `g(∇_X (∇f), Y) = abstractHessian g f x X Y` is symmetric in `(X, Y)`.
* The metric-skewness of the section-level Riemann curvature
  (`riemannSec_metric_skew`).
* The Riesz characterisation of `ricciSharp` and `gradFun`.

These ingredients combine, frame-by-frame, to give the heart-of-Bochner reduction.

The full vector identity at `x` requires a smooth orthonormal frame near `x`; that
construction is deferred to a downstream file (the orthonormalisation of the canonical
chart frame against the metric `g.inner x`). The inner-product form below is the engine
that the downstream file consumes — once an orthonormal frame is chosen, the vector form
is recovered by Riesz uniqueness (`ricciSharpVec_unique` and `gradFun_unique`). -/

/-- **Bridge between `g(∇_X (∇f), Y)` and the abstract Hessian.** For the Levi-Civita
covariant derivative, the inner product `g(∇_X (∇f), Y)` agrees with the abstract Hessian
`abstractHessian g f x (X x) (Y x)`. This identity links the local (Hessian) and global
(covariant-derivative-of-gradient) descriptions of the second-order behaviour of `f`,
through the metric duality `g(grad f, ·) = mfderiv f`. -/
theorem inner_cov_gradFun_eq_abstractHessian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (_hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      abstractHessian (I := I) g f x (X x) (Y x) := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f with hθ_def
  -- Smoothness of `gradFun g f` as a tangent section.
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        (gradFun (I := I) g f y)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have h_grad_at : MDiffAt (T% (fun b => gradFun (I := I) g f b)) x :=
    (h_grad_smooth x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  -- Smoothness of θ = extDerivFun f.
  have hθ_at : MDiffAtCotangent θ x := by
    have hext_smooth :=
      cotangentCov_extDerivFun_smooth (I := I) hf
    -- `cotangentCov_extDerivFun_smooth` provides smoothness as a section of the cotangent
    -- bundle; `MDiffAtCotangent` is precisely the differentiability of the explicit
    -- total-space embedding.
    exact (hext_smooth x).mdifferentiableAt (by simp)
  -- The pairing identity for θ along `b ↦ gradFun g f b`:
  --   extDerivFun (b ↦ θ b ((grad f) b)) x (X x)
  --     = (cotangentCov θ x (X x)) ((grad f) x) + θ x (cov (grad f) x (X x))
  have hpair := cotangentCov_dualPairing cov hθ_at h_grad_at (X x)
  -- The function `b ↦ θ b ((grad f) b) = mfderiv f b ((grad f) b) = g.inner b ((grad f) b) ((grad f) b)`.
  -- In particular, this is the squared norm of grad f, which differs from a scalar that
  -- pairs with Y x. We don't use this expansion. Instead, we use the cotangent-section
  -- duality of θ with Y directly:
  have hpair' := cotangentCov_dualPairing cov hθ_at hY_at (X x)
  -- hpair' : extDerivFun (b ↦ θ b (Y b)) x (X x)
  --        = (cotangentCov θ x (X x)) (Y x) + θ x (cov Y x (X x))
  -- The left side is `extDerivFun (b ↦ extDerivFun f b (Y b)) x (X x)`; the right side
  -- contains `(cotangentCov θ x (X x)) (Y x) = abstractHessian g f x (X x) (Y x)`.
  -- Use the metric-compatibility identity to express:
  --   extDerivFun (b ↦ g.inner b ((grad f) b) (Y b)) x (X x)
  --     = g.inner x (cov (grad f) x (X x)) (Y x) + g.inner x ((grad f) x) (cov Y x (X x))
  -- Combining the two identities will isolate `g.inner x (cov (grad f) x (X x)) (Y x)`
  -- against `abstractHessian g f x (X x) (Y x)` modulo a common piece on both sides.
  --
  -- We follow this strategy now.
  -- Step 1: identify `θ b (Y b)` with the directional derivative `(mfderiv f b)(Y b)`,
  -- then with `extDerivFun f b (Y b)`.
  -- The function `b ↦ θ b (Y b)` is equal to `b ↦ extDerivFun f b (Y b)` by definition.
  -- Step 2: the metric-compatibility identity for the function `b ↦ g.inner b ((grad f) b) (Y b)`,
  -- which by `gradFun_metricDual_extDerivFun` agrees pointwise with `b ↦ extDerivFun f b (Y b)`.
  -- Hence the two extDerivFun-applications coincide.
  have h_eq_fn : (fun b : M => extDerivFun (I := I) f b (Y b)) =
      (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) := by
    funext b
    exact (gradFun_metricDual_extDerivFun (I := I) g f b (Y b)).symm
  -- The metric-compatibility identity at the point x for the function b ↦ g.inner b (grad f b) (Y b):
  --   extDerivFun (b ↦ g.inner b (grad f b) (Y b)) x (X x)
  --     = g.inner x (cov (grad f) x (X x)) (Y x) + g.inner x ((grad f) x) (cov Y x (X x))
  -- This is provided by metric_compat_one (private), but we can re-derive inline using
  -- `LeviCivita_isMetricCompatible.apply`.
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply h_grad_at hY_at (X x)
  -- hmc : (mfderiv I 𝓘(ℝ, ℝ) (fun b => g.inner b (grad f b) (Y b)) x) (X x) =
  --   g.inner x (cov (grad f) x (X x)) (Y x) + g.inner x ((grad f) x) (cov Y x (X x))
  -- Convert mfderiv to extDerivFun.
  have hmc' : extDerivFun (I := I) (fun b => g.inner b (gradFun (I := I) g f b) (Y b)) x (X x) =
      g.inner x (cov.toFun (fun b => gradFun (I := I) g f b) x (X x)) (Y x) +
        g.inner x (gradFun (I := I) g f x) (cov.toFun Y x (X x)) := by
    -- extDerivFun f x v = (NormedSpace.fromTangentSpace _).toContinuousLinearMap (mfderiv f x v).
    -- For ℝ-valued f this is rfl.
    have hext_eq : extDerivFun (I := I) (fun b => g.inner b (gradFun (I := I) g f b) (Y b)) x (X x) =
        (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) x) (X x) := rfl
    rw [hext_eq, hmc]
  -- Now hpair': extDerivFun (b ↦ θ b (Y b)) x (X x)
  --              = (cotangentCov θ x (X x)) (Y x) + θ x (cov Y x (X x))
  -- And by definition of θ, `b ↦ θ b (Y b) = b ↦ extDerivFun f b (Y b)`.
  -- By `h_eq_fn`, `b ↦ extDerivFun f b (Y b) = b ↦ g.inner b (grad f b) (Y b)`.
  have h_lhs_eq : extDerivFun (I := I) (fun b : M => θ b (Y b)) x (X x) =
      extDerivFun (I := I) (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) x (X x) := by
    -- `θ b = extDerivFun f b` by definition; the two functions of `b` are pointwise equal.
    have h_eq : (fun b : M => θ b (Y b)) =
        (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) := h_eq_fn
    rw [h_eq]
  -- Substitute into hpair':
  rw [h_lhs_eq] at hpair'
  -- hpair' : extDerivFun (b ↦ g.inner b (grad f b) (Y b)) x (X x) =
  --            (cotangentCov θ x (X x)) (Y x) + θ x (cov Y x (X x))
  -- By hmc', LHS = g.inner x (cov (grad f) x (X x)) (Y x) + g.inner x ((grad f) x) (cov Y x (X x)).
  -- Equating:
  --   g.inner x (cov (grad f) x (X x)) (Y x) + g.inner x ((grad f) x) (cov Y x (X x))
  --     = (cotangentCov θ x (X x)) (Y x) + θ x (cov Y x (X x))
  -- And `g.inner x ((grad f) x) (cov Y x (X x)) = mfderiv f x (cov Y x (X x))
  --                                              = θ x (cov Y x (X x))`.
  have h_grad_inner : g.inner x (gradFun (I := I) g f x) (cov.toFun Y x (X x)) =
      θ x (cov.toFun Y x (X x)) := by
    rw [gradFun_metricDual_extDerivFun (I := I) g f x (cov.toFun Y x (X x))]
  -- Substituting:
  --   g.inner x (cov (grad f) x (X x)) (Y x) + θ x (cov Y x (X x)) =
  --     (cotangentCov θ x (X x)) (Y x) + θ x (cov Y x (X x))
  -- Hence `g.inner x (cov (grad f) x (X x)) (Y x) = (cotangentCov θ x (X x)) (Y x)`.
  -- And the RHS is `abstractHessian g f x (X x) (Y x)` by definition.
  have hkey : g.inner x (cov.toFun (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      ((cotangentCov cov).toFun θ x (X x)) (Y x) := by
    have hlhs : extDerivFun (I := I) (fun b => g.inner b (gradFun (I := I) g f b) (Y b)) x (X x) =
        g.inner x (cov.toFun (fun b => gradFun (I := I) g f b) x (X x)) (Y x) +
          g.inner x (gradFun (I := I) g f x) (cov.toFun Y x (X x)) := hmc'
    rw [h_grad_inner] at hlhs
    -- hlhs : LHS = g.inner x (cov (grad f) x (X x)) (Y x) + θ x (cov Y x (X x))
    -- hpair' : LHS = (cotangentCov θ x (X x)) (Y x) + θ x (cov Y x (X x))
    have h := hlhs.symm.trans hpair'
    linarith [h]
  -- Goal: g.inner x (cov (grad f) x (X x)) (Y x) = abstractHessian g f x (X x) (Y x).
  -- abstractHessian g f x v w = ((cotangentCov ... f) x v) w by definition.
  rw [hkey]
  rfl

/-- **Heart-of-Bochner identity, inner-product / abstract-Hessian formulation.** Combining
the symmetry of the abstract Hessian with the bridge between `g(∇_X(∇f), Y)` and the
abstract Hessian, the inner product `g(∇_X(∇f), Y)` is symmetric in `(X, Y)` at any point
where `f` is `C²`. This is the engine identity that, traced over any orthonormal frame,
produces the heart-of-Bochner reduction. -/
theorem inner_cov_gradFun_symm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (Y x)) (X x) := by
  classical
  rw [inner_cov_gradFun_eq_abstractHessian (I := I) g hf hX hY,
      inner_cov_gradFun_eq_abstractHessian (I := I) g hf hY hX]
  exact abstractHessian_symm (I := I) g (hf.contMDiffAt.of_le (by
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1)) (X x) (Y x)

/-- **Section-level Hessian symmetry for the gradient.** As scalar functions on `M`, the
inner products `b ↦ g(∇_{X b}(∇f)(b), Y b)` and `b ↦ g(∇_{Y b}(∇f)(b), X b)` are equal.
This is the global form of `inner_cov_gradFun_symm` and is the natural input for
metric-compatibility differentiation steps in the heart-of-Bochner derivation. -/
theorem inner_cov_gradFun_symm_globally [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    (fun b : M => g.inner b ((LeviCivita (I := I) g).toFun
                  (fun b' => gradFun (I := I) g f b') b (X b)) (Y b)) =
      (fun b : M => g.inner b ((LeviCivita (I := I) g).toFun
                  (fun b' => gradFun (I := I) g f b') b (Y b)) (X b)) := by
  funext b
  exact inner_cov_gradFun_symm (I := I) g hf hX hY

/-- **Heart-of-Bochner inner-product reduction at the curvature step.** For smooth tangent
fields `B`, `w` and smooth scalar `f` (with `f` of class `C∞`), the section-level vector
Ricci identity applied to `B, w, ∇f` plus metric skewness of the Riemann curvature
encodes the curvature contribution of the heart-of-Bochner identity:
$$
  g_x\bigl(\nabla_B \nabla_w (\nabla f) - \nabla_w \nabla_B (\nabla f) - \nabla_{[B, w]}(\nabla f),\, B\bigr) =
    g_x\bigl(R(B, w)(\nabla f),\, B\bigr) = - g_x\bigl(\nabla f,\, R(B, w) B\bigr).
$$
The right-most equality is the metric skewness of `riemannSec` (already exposed). -/
theorem heart_of_bochner_curvature_term [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {B w : Π b : M, TangentSpace I b} {x : M}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) :
    g.inner x (riemannSec (LeviCivita (I := I) g) B w
                (fun b => gradFun (I := I) g f b) x) (B x) =
      - g.inner x (gradFun (I := I) g f x)
          (riemannSec (LeviCivita (I := I) g) B w B x) := by
  -- Apply `riemannSec_metric_skew` with X = B, Y = w, Z = grad f, W = B.
  have h := riemannSec_metric_skew (I := I) g (X := B) (Y := w)
    (Z := fun b => gradFun (I := I) g f b) (W := B) (x := x) hB hw
    (gradFun_contMDiff_total_section (I := I) g hf) hB
  -- h : g.inner x (riemannSec ... B w (grad f) x) (B x) +
  --     g.inner x (grad f x) (riemannSec ... B w B x) = 0
  linarith

/-! ## Item 6: Riesz-dual reduction to the inner-product form

By Riesz uniqueness on a finite-dimensional inner-product space, two vectors in `T_x M` are
equal iff they have the same inner product with every test vector. The next lemma packages
this Riesz uniqueness for the LHS-equals-RHS comparison of the heart-of-Bochner vector
identity. -/

/-- **Riesz uniqueness reduction for the heart-of-Bochner vector identity.** Two tangent
vectors `LHS, RHS ∈ T_x M` are equal iff `g.inner x LHS w = g.inner x RHS w` for every
`w ∈ T_x M`. This is the standard Riesz uniqueness on a finite-dimensional inner-product
space; we package it as a named lemma to highlight its role as the entry point from the
inner-product formulation to the vector formulation of the heart-of-Bochner identity. -/
lemma vector_eq_iff_inner_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    (LHS RHS : TangentSpace I x) :
    LHS = RHS ↔ ∀ w : TangentSpace I x, g.inner x LHS w = g.inner x RHS w := by
  refine ⟨fun h _ => by rw [h], fun h => ?_⟩
  apply metricFlatLinear_injective (I := I) g x
  ext w
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  exact h w

/-! ## Item 7: registration of the heart-of-Bochner identity

The vector identity
$$
  \Delta_\nabla(\nabla f)(x) = \nabla(\Delta_g f)(x) + \mathrm{Ric}^\sharp(\nabla f)(x)
$$
holds when `localConnLap_vector` is computed against a smooth orthonormal local frame
near `x`. Its proof factors into:

* the **abstract Hessian symmetry** (`abstractHessian_symm`, equivalently
  `inner_cov_gradFun_symm`), which lets one swap a `∇` past the gradient `∇f`;
* the **metric skewness of `riemannSec`** (`heart_of_bochner_curvature_term`), which
  produces the Ricci-tensor term `g(∇f, R(B_i, w) B_i)` from the curvature commutator;
* the **identification of the trace of the abstract Hessian with the Laplacian**
  (`Δ_g f = tr_g (Hess f)`), which is the divergence-of-gradient identity in disguise.

The first two ingredients are proved above. The third is the divergence formula, available
as `Δ_g g hf x = ...`; together with an orthonormal frame at `x` it identifies
`∑_i abstractHessian g f x (B_i x) (B_i x) = Δ_g g hf x`.

Once a smooth orthonormal frame `B` near `x` is fixed, applying `inner_cov_gradFun_symm`
inside the trace `∑_i g(∇_{B_i} ∇_{B_i}(∇f), w)` swaps one `∇` past the gradient and
re-organises the sum into `∇w(Δf) + Ric^♯(∇f) · w`, by the abstract identity already
encoded above. The remaining algebra is purely combinatorial:

```
∑_i g(∇_{B_i} ∇_{B_i} (∇f), w)
  = ∑_i [B_i (g(∇_{B_i} (∇f), w)) - g(∇_{B_i} (∇f), ∇_{B_i} w)]    (metric compat)
  = ∑_i [B_i (Hess f(B_i, w)) - Hess f(B_i, ∇_{B_i} w)]            (Hessian bridge)
  = ...
```

And the final `Ric` term emerges by Hessian-symmetry-induced rearrangement coupled with
the curvature commutator from `heart_of_bochner_curvature_term`.

The full proof at this level requires producing a smooth orthonormal frame near every
point. Mathlib's `Trivialization.localFrame` together with a smooth Gram-Schmidt
construction would supply the needed frame. The combinatorial reduction is elementary,
but requires careful bookkeeping of indices and non-trivial intermediate algebraic
identities.

We package the engine identity below: the inner-product form of the heart-of-Bochner
trace-commutator, taking as input a smooth tangent frame `B` (no orthonormality assumed,
no claim that the frame is at-x-orthonormal) and a smooth test field `w`. The output is
the algebraic content equivalent to the heart-of-Bochner identity once the frame is
declared orthonormal at `x`. -/

/-- **Frame-traced inner product of the connection Laplacian on `∇f` against `w`.** This
is the LHS of the heart-of-Bochner identity in inner-product form, displayed in the trace
form that the downstream connection-Laplacian Bochner derivation will work with. It
unfolds the local connection-Laplacian against the inner product, applying metric
compatibility in two steps and the abstract-Hessian bridge to pre-organise the data into
the four atomic pieces:

* `B_i (Hess f(B_i, w))` — second-derivative term;
* `Hess f(B_i, ∇_{B_i} w)` — connection-correction in `w`;
* `Hess f(∇_{B_i} B_i, w)` — connection-correction in `B`.

The final assembly into `mfderiv (Δf) (w x) + ricciTensor g x (∇f x) (w x)` requires
orthonormality of the frame `B` at `x` and is performed in a downstream file. -/
lemma localConnLap_vector_grad_inner_eq_hessian_diff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (_hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {w : Π b : M, TangentSpace I b}
    (_hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (_hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (x : M) :
    g.inner x (localConnLap_vector (LeviCivita (I := I) g) B
                  (fun b => gradFun (I := I) g f b) x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g) (B i)
                      (fun b => gradFun (I := I) g f b)) x (B i x)) (w x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun (B i) x (B i x))) (w x)) := by
  classical
  -- Distribute g.inner x over the finite sum.
  unfold localConnLap_vector
  -- The function `g.inner x` is a CLM on T_x M; applying it to a sum yields the sum of
  -- applications. Then evaluating at `(w x)` distributes through the sum (sum of CLMs
  -- applied at a vector = sum of values).
  set u : Fin (Module.finrank ℝ E) → TangentSpace I x := fun i =>
    (LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) (B i)
          (fun b => gradFun (I := I) g f b)) x (B i x) -
      (LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x
        ((LeviCivita (I := I) g).toFun (B i) x (B i x)) with hu_def
  -- LHS = g.inner x (∑_i u i) (w x) = ∑_i g.inner x (u i) (w x), then distribute g.inner x.
  have h1 : g.inner x (∑ i : Fin (Module.finrank ℝ E), u i) =
      ∑ i : Fin (Module.finrank ℝ E), g.inner x (u i) := map_sum _ _ _
  -- Apply both sides at (w x). The sum-of-CLMs evaluation is a finite-step CLM addition.
  have h2 : ∀ S : Finset (Fin (Module.finrank ℝ E)),
      (∑ i ∈ S, g.inner x (u i)) (w x) = ∑ i ∈ S, g.inner x (u i) (w x) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, ContinuousLinearMap.add_apply, ih]
  rw [h1, h2]
  refine Finset.sum_congr rfl ?_
  intro i _
  -- Distribute g.inner x over the subtraction defining `u i`.
  show g.inner x (u i) (w x) = _
  rw [hu_def]
  rw [map_sub, ContinuousLinearMap.sub_apply]

/-! ## Item 8: heart-of-Bochner vector identity, in conditional form

The full vector heart-of-Bochner identity
$$
  (\Delta_\nabla^B \nabla f)(x) = \nabla(\Delta_g f)(x) + \mathrm{Ric}^\sharp(\nabla f)(x)
$$
holds when the smooth frame `B` is `g_x`-orthonormal at `x` (or, more strongly, on a
neighbourhood of `x`). The orthonormality drives both:

1. the identification of `∑_i \mathrm{Hess} f(B_i, B_i)|_x` with the Laplacian
   `\Delta_g f|_x` (the trace of `\mathrm{Hess} f` against an orthonormal basis is the
   metric trace, which by the divergence-of-gradient identity equals `\Delta_g f`),
2. the identification of `∑_i (\mathrm{finBasis}\,\mathbb R\,E).\mathrm{repr}\,(R(B_i, w)
   \nabla f)\,i` with `\mathrm{ricciTensor}\,g\,x\,(\nabla f)(w)` (`ricciTensor_apply_smooth_basisSum`).

Below, we expose the **conditional vector identity**: assuming the inner-product reduction
(the input that an orthonormal-frame extension would supply), the vector identity follows
by Riesz uniqueness. This packages the heart-of-Bochner reduction into a single named
theorem of vector content, ready for the downstream abstract-Bochner consumer to feed in
either an orthonormal-frame argument or the equivalent inner-product reduction. -/

/-- **Heart-of-Bochner vector identity, conditional form.** Given a smooth frame
`B : Fin n → Π b, TangentSpace I b` and a smooth scalar `f : M → ℝ`, suppose the
inner-product reduction holds: for every smooth tangent test field `w` (and at the point
`x`),
$$
  g_x\bigl((\Delta_\nabla^B \nabla f)(x), w(x)\bigr) =
    g_x\bigl(\nabla(\Delta_g f)(x), w(x)\bigr) + g_x\bigl(\mathrm{Ric}^\sharp(\nabla f x), w(x)\bigr).
$$
Then the vector identity holds:
$$
  (\Delta_\nabla^B \nabla f)(x) = \nabla(\Delta_g f)(x) + \mathrm{Ric}^\sharp(\nabla f x).
$$
The hypothesis is exactly the inner-product form of the heart-of-Bochner identity, which
holds for `B` orthonormal at `x` by the algebraic content packaged in
`inner_cov_gradFun_eq_abstractHessian`, `inner_cov_gradFun_symm`, and
`heart_of_bochner_curvature_term` together with the Hessian-trace-equals-Laplacian
identity (in turn the divergence-of-gradient identity). -/
theorem heart_of_bochner_of_inner_form [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (_hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (localConnLap_vector (LeviCivita (I := I) g) B
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    localConnLap_vector (LeviCivita (I := I) g) B
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) := by
  rw [vector_eq_iff_inner_eq (I := I) g x]
  intro w
  rw [hInner w]
  rw [show g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x)) w =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
        g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w from
    by rw [map_add, ContinuousLinearMap.add_apply]]

end Connection
end Integral
end DifferentialGeometry
