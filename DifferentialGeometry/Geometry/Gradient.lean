import DifferentialGeometry.Integral.DivergenceTheorem.LocalFormula
import DifferentialGeometry.Integral.DivergenceTheorem.TangentAction
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Gradient of a smooth function on a Riemannian manifold

Given a smooth Riemannian metric `g` on the tangent bundle of a smooth manifold
`M` and a smooth scalar function `f : M → ℝ`, this file defines the gradient
`grad_g g hf` (where `hf` is a smoothness witness) as a smooth tangent
section, and establishes its defining duality with the differential of `f` and
basic algebraic properties.

## Construction

At each point `x : M`, the metric `g.inner x : E →L[ℝ] E →L[ℝ] ℝ` (where
`E := TangentSpace I x` definitionally) is a positive-definite continuous
bilinear form. The "musical flat" map `v ↦ g.inner x v` is an `ℝ`-linear map
from `E` into `E →ₗ[ℝ] ℝ`. By positive-definiteness it is injective; since `E`
is finite-dimensional, the spaces `E` and `E →ₗ[ℝ] ℝ` have the same dimension,
so the flat map is a linear equivalence.

The gradient at `x` is then defined as the preimage under this equivalence of
the differential `mfderiv I 𝓘(ℝ) f x`, viewed as a linear functional on
`TangentSpace I x`. This gives the duality identity
$$g(\nabla_g f, v) = (\mathrm{d}f)(v)$$
for all tangent vectors `v` at `x`.

## Smoothness

Smoothness of `grad_g g hf` is established by exhibiting it pointwise on each
chart base set as the linear combination
$$(\nabla_g f)(x) = \sum_{i,j} G^{ij}(x)\, \partial_j \tilde f(\varphi(x))\,
    e_i(x),$$
where `G^{ij}` is the entrywise inverse of the chart Gram matrix `G_{ij} =
g.inner x (e_i, e_j)`, the `e_i` are the chart-basis frame vectors, and
$\tilde f = f \circ \varphi^{-1}$ is the chart-pullback of `f`. The inverse
Gram matrix is smooth on the chart base set since the Gram matrix is smooth
and positive-definite there.

## Compact support

If `f : M → ℝ` has compact support, so does `grad_g g hf`: the gradient
vanishes wherever `mfderiv f x` does (in particular, off `tsupport f` where
`f` is locally zero).

## Main definitions

* `metricFlatMap g x` : the flat linear equivalence
  `TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ)` induced by `g.inner x`.
* `metricSharp g x α` : the gradient (sharp) of a covector `α` at `x`, defined
  as the inverse of `metricFlatMap g x`.
* `gradFun g f` : the underlying pointwise gradient function.
* `grad_g g hf` : the smooth gradient of a smooth scalar `f` (with smoothness
  proof `hf`) as a smooth tangent section.

## Main results

* `tangentSectionAction_grad_g_eq_inner` : duality with the differential.
* `inner_grad_g_symm` : symmetry of the metric on two gradients.
* `hasCompactSupport_grad_g` : compact support of the gradient when `f` has
  compact support.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

/-! ## Pointwise flat map and its inverse

For each `x : M`, the metric `g.inner x` defines a continuous bilinear form on
`TangentSpace I x`. Currying gives a linear map `metricFlatLinear g x` from
the tangent space into its `ℝ`-linear dual; positive-definiteness makes this
map injective, and hence (by finite-dimensionality and equality of dimensions)
a linear equivalence. -/

/-- The "musical flat" linear map at `x : M`: sends a tangent vector `v` to the
linear functional `w ↦ g.inner x v w`. -/
def metricFlatLinear (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    rw [map_add, ContinuousLinearMap.add_apply]
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    rw [map_smul, ContinuousLinearMap.smul_apply]

@[simp] lemma metricFlatLinear_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatLinear (I := I) g x v w = g.inner x v w := rfl

/-- The flat linear map is injective: from positive-definiteness of `g.inner x`. -/
lemma metricFlatLinear_injective (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (metricFlatLinear (I := I) g x) := by
  intro v w hvw
  have hzero : ∀ z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L z) hvw
    simp only [metricFlatLinear_apply] at h
    -- Goal: `g.inner x (v - w) z = 0`. By bilinearity, this equals
    -- `g.inner x v z - g.inner x w z`, which is `0` by `h`.
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub, ContinuousLinearMap.sub_apply]
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl 0) (hzero (v - w) ▸ hpos)

/-- `TangentSpace I x` is finite-dimensional over `ℝ`. -/
private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-- The flat map's domain and codomain have the same finite dimension over `ℝ`. -/
private lemma metricFlatLinear_finrank_eq (x : M) :
    Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace I x →ₗ[ℝ] ℝ) :=
  Subspace.dual_finrank_eq.symm

/-- The flat linear equivalence `TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ)`
induced by the metric `g` at `x`. -/
def metricFlatMap (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) :=
  LinearMap.linearEquivOfInjective
    (metricFlatLinear (I := I) g x)
    (metricFlatLinear_injective (I := I) g x)
    (metricFlatLinear_finrank_eq (I := I) (M := M) x)

@[simp] lemma metricFlatMap_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatMap (I := I) g x v w = g.inner x v w := rfl

/-- Defining property of `metricFlatMap.symm`: it sends a covector `α` to the
unique `v` with `g.inner x v w = α w` for all `w`. -/
lemma metricFlatMap_apply_symm (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x ((metricFlatMap (I := I) g x).symm α) w = α w := by
  have h := (metricFlatMap (I := I) g x).apply_symm_apply α
  have hh : metricFlatMap (I := I) g x ((metricFlatMap (I := I) g x).symm α) w = α w :=
    congrArg (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L w) h
  rw [metricFlatMap_apply] at hh
  exact hh

/-! ## Pointwise gradient (sharp) -/

/-- The pointwise gradient (sharp) of a covector at a point. -/
def metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) : TangentSpace I x :=
  (metricFlatMap (I := I) g x).symm α

@[simp] lemma metricSharp_def (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) :
    metricSharp (I := I) g x α = (metricFlatMap (I := I) g x).symm α := rfl

/-- Defining identity for the sharp: `g.inner x (sharp α) w = α w`. -/
lemma inner_metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x (metricSharp (I := I) g x α) w = α w :=
  metricFlatMap_apply_symm (I := I) g x α w

/-- Symmetric form: `g.inner x w (sharp α) = α w`. -/
lemma inner_metricSharp_right (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x w (metricSharp (I := I) g x α) = α w := by
  rw [g.symm x w (metricSharp (I := I) g x α)]
  exact inner_metricSharp (I := I) g x α w

/-! ## The gradient as a function -/

/-- The pointwise gradient of a function `f : M → ℝ` at `x : M`. -/
def gradFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap

@[simp] lemma gradFun_def (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradFun (I := I) g f x =
      metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := rfl

/-- Defining identity: `g.inner x (gradFun g f x) v = mfderiv f x v`. -/
lemma inner_gradFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradFun (I := I) g f x) v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  rw [gradFun_def]
  exact inner_metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap v

/-- Symmetric form: `g.inner x v (gradFun g f x) = mfderiv f x v`. -/
lemma inner_gradFun_right (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x v (gradFun (I := I) g f x) = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  rw [g.symm x v (gradFun (I := I) g f x)]
  exact inner_gradFun (I := I) g f x v

/-- The gradient vanishes wherever the differential vanishes. -/
lemma gradFun_eq_zero_of_mfderiv_eq_zero
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) {x : M}
    (hf : mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    gradFun (I := I) g f x = (0 : TangentSpace I x) := by
  unfold gradFun metricSharp
  have htoLM : (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap =
      (0 : TangentSpace I x →ₗ[ℝ] ℝ) := by
    rw [hf]; rfl
  rw [htoLM]
  exact LinearEquiv.map_zero _

/-! ## Inverse Gram matrix and its smoothness -/

/-- The inverse Gram matrix at `(α, x)`. On the chart base set this is the
matrix inverse of the (positive-definite) Gram matrix; off the base set it is a
default value. -/
def chartInvGramMatrix (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartGramMatrix (I := I) g α x)⁻¹

/-- On the chart base set, the inverse Gram matrix is a one-sided inverse. -/
lemma chartInvGramMatrix_mul_chartGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartInvGramMatrix (I := I) g α x * chartGramMatrix (I := I) g α x = 1 := by
  have hpos := chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.nonsing_inv_mul _ hdet_unit

/-- Symmetric form. -/
lemma chartGramMatrix_mul_chartInvGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartGramMatrix (I := I) g α x * chartInvGramMatrix (I := I) g α x = 1 := by
  have hpos := chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.mul_nonsing_inv _ hdet_unit

/-- Each adjugate entry of the Gram matrix is smooth on the trivialization base
set. The adjugate entry is the determinant of an updated submatrix, hence a
polynomial expression in the (smooth) Gram-matrix entries. -/
lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp : (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j) =
      (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ))).det) := by
    funext x
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 : (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ))).det) =
      (fun x : M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, (chartGramMatrix (I := I) g α x).updateRow j
              (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq : (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun _ : M => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i
          (1 : ℝ)) k) := by
      funext x
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq : (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun x : M => chartGramMatrix (I := I) g α x (σ k) k) := by
      funext x
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

/-- Each entry of the inverse Gram matrix is smooth on the chart base set. -/
lemma chartInvGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  -- On the base set, `A⁻¹ = Ring.inverse A.det • adjugate A`. Hence the (i,j) entry is
  -- `Ring.inverse (det A) * adjugate A i j = (det A)⁻¹ * adjugate A i j`.
  have hcongr : ∀ x ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartInvGramMatrix (I := I) g α x i j =
        ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j := by
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 := ne_of_gt hdet_pos
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    -- Now `A⁻¹ i j = (det⁻¹ʳ • adjugate A) i j`.
    change (Ring.inverse (chartGramMatrix (I := I) g α x).det •
            (chartGramMatrix (I := I) g α x).adjugate) i j =
      ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    -- For `ℝ` (a field), `Ring.inverse a = a⁻¹` (and `Ring.inverse 0 = 0`).
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ ?_
  · -- `(det · )⁻¹` is smooth where `det · ≠ 0`.
    have hdet_smooth : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M => (chartGramMatrix (I := I) g α x).det)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartGramMatrix_det_contMDiffOn (I := I) g α
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 := ne_of_gt hdet_pos
    have hsmooth_inv : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹)
        (chartGramMatrix (I := I) g α x).det := contDiffAt_inv _ hdet_ne
    have h_at := hdet_smooth x hx
    exact hsmooth_inv.contMDiffAt.comp_contMDiffWithinAt x h_at
  · exact chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j

/-! ## Chart-local representation of the gradient -/

/-- The `i`-th chart-basis component of the gradient at `x`, in the chart at `α`.
This is `∑_j G^{ij}(x) · ∂_j f̃(φ x)`. -/
def gradChartCoeff (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α x i j *
      partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x)

@[simp] lemma gradChartCoeff_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    gradChartCoeff (I := I) g α f i x =
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) := rfl

/-- The chart-local representation of the gradient as a linear combination of
the chart-basis frame at `α`. -/
def gradChartLocal (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    gradChartCoeff (I := I) g α f i x •
      chartBasisVecFiber (I := I) α i x

/-! ## A version of `mfderiv_chartBasisVecFiber` requiring only `MDifferentiableAt` -/

/-- A version of `mfderiv_chartBasisVecFiber` that requires only
`MDifferentiableAt I 𝓘(ℝ, ℝ) f x` rather than full smoothness of `f`. -/
lemma mfderiv_chartBasisVecFiber_of_mdifferentiableAt
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hxchart : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ, ℝ) f x (chartBasisVecFiber (I := I) α i x) =
      partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hxchart
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hxchart
  have hcomp_eq : ∀ᶠ y in 𝓝 x, f y = (scalarOnE (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    rw [scalarOnE_def, φ.left_inv hy]
  have hcong : f =ᶠ[𝓝 x] (scalarOnE (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ, ℝ) f x =
      mfderiv I 𝓘(ℝ, ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  -- Differentiability of `scalarOnE α f` at `φ x`. Use that
  -- `scalarOnE α f = f ∘ (extChartAt I α).symm`, plus the fact that the symm
  -- map is mdiff at `φ x` and `f` is mdiff at `x = symm(φ x)`.
  have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
  -- Use `EventuallyEq.mdifferentiableAt_iff` to lift `MDifferentiableAt` from `f` to the
  -- composition. Actually we already have `hcong`, we can use the symmetric form
  -- giving us `MDifferentiableAt (scalarOnE α f ∘ φ) x`.
  have hcomp_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x := by
    have h := hcong.mdifferentiableAt_iff (𝕜 := ℝ) (I := I) (I' := 𝓘(ℝ, ℝ))
    exact h.mp hf
  -- We need `MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE α f) (φ x)`. This follows
  -- because the composition `(scalarOnE α f) ∘ φ = (something differentiable at x)`
  -- and `φ` is a local diffeomorphism (in particular has nonsingular mfderiv).
  -- We use a more direct argument: the `extChartAt I α` near `x` is essentially the
  -- chart map; reading off the chain rule and the fact that the chart map is locally
  -- a homeomorphism, we can extract differentiability of the composite at `φ x`.
  -- Alternative: use that `scalarOnE α f =ᶠ[𝓝 (φ x)] f ∘ (φ.symm)`, and `f ∘ φ.symm`
  -- is mdiff at `φ x`.
  have hphi_symm_mdiff : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm (φ x) := by
    have hcontMDiffOn : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
    have htgt_int : (extChartAt I α).target ∈ 𝓝 (φ x) := by
      have hint_open : IsOpen (interior (extChartAt I α).target) := isOpen_interior
      exact mem_nhds_iff.mpr ⟨interior _, interior_subset, hint_open, hx_int⟩
    have hcont_at : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (φ x) :=
      (hcontMDiffOn (φ x) (interior_subset hx_int)).contMDiffAt htgt_int
    exact hcont_at.mdifferentiableAt (by simp)
  have hsymm_at_x : (extChartAt I α).symm (φ x) = x := φ.left_inv hxsrc
  -- `f ∘ (extChartAt I α).symm` is mdiff at `φ x`.
  have hf_at_symm : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I α).symm (φ x)) := by
    rw [hsymm_at_x]; exact hf
  have hf_comp_symm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (f ∘ (extChartAt I α).symm) (φ x) :=
    hf_at_symm.comp (φ x) hphi_symm_mdiff
  -- And `(scalarOnE α f) = f ∘ (extChartAt I α).symm` definitionally.
  have hscalar_eq : (scalarOnE (I := I) α f) = f ∘ (extChartAt I α).symm := by
    funext y; rfl
  have hg_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (scalarOnE (I := I) α f) (φ x) := by
    rw [hscalar_eq]; exact hf_comp_symm
  -- Now apply chain rule.
  have hchain :
      mfderiv I 𝓘(ℝ, ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x hg_mdiff hphi_mdiff
  rw [hchain]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE (I := I) α f) (φ x)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  -- Identify `mfderiv (extChartAt I α) x (chartBasisVecFiber α i x) = (chartModelBasis E) i`.
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (chartBasisVecFiber (I := I) α i x)
        = (chartModelBasis E) i := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hxchart]
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) α
    have heq : chartBasisVecFiber (I := I) α i x = T.symm x ((chartModelBasis E) i) :=
      rfl
    rw [heq]
    have h_apply :
        T.continuousLinearMapAt ℝ x (T.symm x ((chartModelBasis E) i))
          = (chartModelBasis E) i := by
      have heqsymm : T.symm x ((chartModelBasis E) i)
            = T.symmL ℝ x ((chartModelBasis E) i) := by
        rw [Trivialization.symmL_apply]
      rw [heqsymm, Trivialization.continuousLinearMapAt_symmL T (b := x) hbase]
    exact h_apply
  change fderiv ℝ (scalarOnE (I := I) α f) (φ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x (chartBasisVecFiber (I := I) α i x))
      = partialDeriv (E := E) i (scalarOnE (I := I) α f) (φ x)
  rw [hmfderiv_chartBasis]
  rfl

/-! ## Identification of `gradChartLocal` with `gradFun` -/

/-- The inner product of `gradChartLocal` with a chart-basis frame vector `e_k` is
the `k`-th chart-pullback partial derivative of `f`. Pure linear-algebra step. -/
lemma inner_gradChartLocal_chartBasis
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner x (gradChartLocal (I := I) g α f x)
        (chartBasisVecFiber (I := I) α k x)
      = partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  unfold gradChartLocal
  -- LHS: g.inner x (∑ i, a_i • e_i) e_k = ∑ i, a_i * G_{ik} where a_i = gradChartCoeff i x.
  rw [show g.inner x (∑ i, gradChartCoeff (I := I) g α f i x •
            chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α k x) =
        ∑ i, gradChartCoeff (I := I) g α f i x *
          g.inner x (chartBasisVecFiber (I := I) α i x)
            (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · -- finite-sum expansion of g.inner.
    rw [show (g.inner x (∑ i, gradChartCoeff (I := I) g α f i x •
              chartBasisVecFiber (I := I) α i x)) =
          (∑ i, gradChartCoeff (I := I) g α f i x •
              g.inner x (chartBasisVecFiber (I := I) α i x)) from ?_]
    · rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
  -- Substitute `gradChartCoeff i x = ∑ j, G^{ij} ∂f j`.
  have ha : ∀ i, gradChartCoeff (I := I) g α f i x =
      ∑ j, chartInvGramMatrix (I := I) g α x i j *
        partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) := fun i => rfl
  rw [show ∑ i, gradChartCoeff (I := I) g α f i x *
            g.inner x (chartBasisVecFiber (I := I) α i x)
              (chartBasisVecFiber (I := I) α k x) =
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x)) *
              chartGramMatrix (I := I) g α x i k from ?_]
  swap
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [ha i]
    -- chartGramMatrix g α x i k = g.inner x (e_i x) (e_k x)
    rfl
  -- Now interchange sums and use the Gram-inverse identity.
  -- ∑ i, (∑ j, Ginv_{ij} ∂f j) * G_{ik} = ∑ j, (∑ i, Ginv_{ij} G_{ik}) * ∂f j.
  rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
              partialDeriv (E := E) j (scalarOnE (I := I) α f)
                (extChartAt I α x)) *
                chartGramMatrix (I := I) g α x i k =
          ∑ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
              chartGramMatrix (I := I) g α x i k) *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) from ?_]
  swap
  · -- Step 1: factor each summand: (∑ j, Ginv ij * dfj) * G ik = ∑ j, (Ginv ij * dfj) * G ik
    -- = ∑ j, (Ginv ij * G ik) * dfj.
    rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                partialDeriv (E := E) j (scalarOnE (I := I) α f)
                  (extChartAt I α x)) *
                  chartGramMatrix (I := I) g α x i k =
              ∑ i, ∑ j, (chartInvGramMatrix (I := I) g α x i j *
                  chartGramMatrix (I := I) g α x i k) *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f)
                    (extChartAt I α x) from ?_]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.sum_mul]
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
  -- Now use ∑ i, Ginv_{ij} * G_{ik} = δ_{jk}, by the Gram-mul-inverse identity (G * G⁻¹ = 1)
  -- combined with the symmetry of G.
  have hsym : ∀ i, chartGramMatrix (I := I) g α x i k =
      chartGramMatrix (I := I) g α x k i := fun i => g.symm x _ _
  have hkron : ∀ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
        chartGramMatrix (I := I) g α x i k) =
      if k = j then (1 : ℝ) else 0 := by
    intro j
    rw [show (∑ i, chartInvGramMatrix (I := I) g α x i j *
              chartGramMatrix (I := I) g α x i k) =
            (∑ i, chartGramMatrix (I := I) g α x k i *
              chartInvGramMatrix (I := I) g α x i j) from ?_]
    swap
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsym i]
      ring
    -- ∑ i, G_{k,i} * Ginv_{i,j} = (G * Ginv)_{k,j} = (1)_{k,j} = δ_{k,j}.
    have hidentity : (chartGramMatrix (I := I) g α x *
          chartInvGramMatrix (I := I) g α x) k j =
        if k = j then (1 : ℝ) else 0 := by
      rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hx]
      rw [Matrix.one_apply]
    rw [← hidentity]
    rw [Matrix.mul_apply]
  rw [show ∑ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
            chartGramMatrix (I := I) g α x i k) *
              partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) =
          ∑ j, (if k = j then (1 : ℝ) else 0) *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) from
      Finset.sum_congr rfl (fun j _ => by rw [hkron j])]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    rw [if_neg (Ne.symm hjk), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The chart-local representation `gradChartLocal` agrees with `gradFun` at every
chart-base-set point where `f` is differentiable and the chart map lands in the
interior of the chart target. -/
lemma gradChartLocal_eq_gradFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    gradChartLocal (I := I) g α f x = gradFun (I := I) g f x := by
  classical
  have hxchart : x ∈ (chartAt H α).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx; exact hx
  -- Set up an explicit CLM into ℝ for the mfderiv to avoid TangentSpace-vs-ℝ confusion.
  set f' : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x with hf'_def
  -- The mfderiv evaluation: `mfderiv f x v = f' v` (by hf'_def, definitional).
  have hmfderiv_basis : ∀ k, f' (chartBasisVecFiber (I := I) α k x) =
      partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro k
    rw [hf'_def]
    exact mfderiv_chartBasisVecFiber_of_mdifferentiableAt
      (I := I) α hf hxchart hx_int k
  -- Both sides are determined by their inner product with arbitrary tangent vectors.
  apply metricFlatLinear_injective (I := I) g x
  ext v
  change g.inner x (gradChartLocal (I := I) g α f x) v =
    g.inner x (gradFun (I := I) g f x) v
  rw [inner_gradFun (I := I) g f x v]
  -- Replace `mfderiv f x v` by `f' v`.
  change g.inner x (gradChartLocal (I := I) g α f x) v = f' v
  -- Decompose `v = ∑ k, c k • e_k x`.
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    chartBasisFamily (I := I) α hx
  set c : Fin (Module.finrank ℝ E) → ℝ := fun k => b.repr v k
  have hv_decomp : v = ∑ k, c k • chartBasisVecFiber (I := I) α k x := by
    have h1 : v = ∑ k, b.repr v k • b k := (b.sum_repr v).symm
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [chartBasisFamily_apply (I := I) α hx k]
  rw [hv_decomp]
  -- Both sides are linear in `v`, so commute with the finite sum.
  -- LHS: g.inner x (gradChartLocal g α f x) (∑ k, c k • e_k x)
  -- RHS: f' (∑ k, c k • e_k x)
  rw [show g.inner x (gradChartLocal (I := I) g α f x)
        (∑ k, c k • chartBasisVecFiber (I := I) α k x) =
        ∑ k, c k * g.inner x (gradChartLocal (I := I) g α f x)
          (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · -- Apply `g.inner x` linearity in the second argument over the sum.
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [show f' (∑ k, c k • chartBasisVecFiber (I := I) α k x) =
        ∑ k, c k * f' (chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  rw [inner_gradChartLocal_chartBasis (I := I) g α f hx k, hmfderiv_basis k]

/-! ## Smoothness of `gradFun` -/

/-- `gradChartCoeff g α f i` is `C^∞` on the smoothness domain (the chart base
set restricted to where the chart map lands in the interior of the chart target). -/
private lemma gradChartCoeff_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeff (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  refine contMDiffOn_finset_sum (fun j _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  · -- `chartInvGramMatrix g α x i j` is smooth on the chart base set.
    have h1 : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => chartInvGramMatrix (I := I) g α x i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  · -- The chart-pulled-back partial derivative is smooth on the smoothness domain.
    have hpartial : ContDiffOn ℝ ∞
        (partialDeriv (E := E) j (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) := by
      have hbase : ContDiffOn ℝ ∞
          (scalarOnE (I := I) α f) (extChartAt I α).target :=
        scalarOnE_contDiffOn (I := I) α hf
      have hbase_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
          (interior (extChartAt I α).target) := hbase.mono interior_subset
      have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
          (interior (extChartAt I α).target) :=
        hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
      have hconst : ContDiffOn ℝ ∞ (fun _ : E => (chartModelBasis E) j)
          (interior (extChartAt I α).target) := contDiffOn_const
      exact hfderiv.clm_apply hconst
    have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
        (partialDeriv (E := E) j (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) := hpartial.contMDiffOn
    have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
        (chartAt H α).source := contMDiffOn_extChartAt
    have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
        ((extChartAt I α).source ∩
          (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
      refine hchart.mono ?_
      intro x hx
      have h1 : x ∈ (extChartAt I α).source := hx.1
      rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
      exact h1
    have hsubset : (extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target ⊆
          (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
      fun _ hx => hx.2
    exact hpartialM.comp hchart' hsubset

/-- The chart-local representation `gradChartLocal g α f` is smooth as a
tangent-bundle section on the smoothness domain. -/
private lemma gradChartLocal_contMDiffOn_total
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocal (I := I) g α f x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  -- Each summand is `gradChartCoeff α f i x • chartBasisVecFiber α i x`, smooth.
  -- Sum them.
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeff (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    fun i => gradChartCoeff_contMDiffOn (I := I) g α hf i
  have hbasis : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    intro i
    refine (chartBasisVec_contMDiffOn (I := I) α i).mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  have hsmul : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (gradChartCoeff (I := I) g α f i x • chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    intro i
    exact (hcoeff i).smul_section (hbasis i)
  -- Sum.
  have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (∑ i, gradChartCoeff (I := I) g α f i x •
          chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    ContMDiffOn.sum_section (fun i _ => hsmul i)
  exact hsum

/-- Under `[I.Boundaryless]`, the smoothness domain of `gradChartLocal` reduces to the
chart base set. -/
private lemma gradChartLocal_contMDiffOn_total_baseSet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocal (I := I) g α f x))
      (chartAt H α).source := by
  refine (gradChartLocal_contMDiffOn_total (I := I) g α hf).mono ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  · rw [show (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target =
          (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target from ?_]
    · exact (extChartAt I α).map_source
        (by rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx)
    · congr 1
      exact (isOpen_extChartAt_target (I := I) α).interior_eq

/-- Under `[I.Boundaryless]`, `gradFun g f` is smooth as a tangent-bundle section. -/
lemma gradFun_contMDiff_total [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x)) := by
  intro x
  have hx_src : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_open : IsOpen ((chartAt H x).source) := (chartAt H x).open_source
  have hsmooth_local : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (gradChartLocal (I := I) g x f y))
      (chartAt H x).source :=
    gradChartLocal_contMDiffOn_total_baseSet (I := I) g x hf
  have heq_on_src : ∀ y ∈ (chartAt H x).source,
      gradChartLocal (I := I) g x f y = gradFun (I := I) g f y := by
    intro y hy
    have hbase : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact hy
    have hy_int : extChartAt I x y ∈ interior (extChartAt I x).target := by
      have hys : y ∈ (extChartAt I x).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy
      have hytgt : extChartAt I x y ∈ (extChartAt I x).target :=
        (extChartAt I x).map_source hys
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) x hytgt
    have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
      hf.mdifferentiable (by simp) y
    exact gradChartLocal_eq_gradFun (I := I) g x hf_mdiff hbase hy_int
  have hsmooth_local2 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (gradFun (I := I) g f y))
      (chartAt H x).source := by
    refine hsmooth_local.congr ?_
    intro y hy
    -- Need: `gradFun = gradChartLocal` here. `heq_on_src` gives `gradChartLocal = gradFun`.
    have h := heq_on_src y hy
    change TotalSpace.mk' E y (gradFun (I := I) g f y) =
      TotalSpace.mk' E y (gradChartLocal (I := I) g x f y)
    rw [h]
  exact (hsmooth_local2 x hx_src).contMDiffAt (hsrc_open.mem_nhds hx_src)

/-! ## The smooth gradient as a `ContMDiffSection` -/

/-- The smooth gradient of a smooth scalar function `f` (with smoothness proof
`hf`) as a smooth tangent-bundle section. -/
def grad_g [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => gradFun (I := I) g f x, gradFun_contMDiff_total (I := I) g hf⟩

@[simp] lemma grad_g_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      gradFun (I := I) g f x := rfl

/-! ## Duality with the tangent-section action -/

/-- **Duality of gradient and tangent action.** The action of a smooth tangent
section `X` on a smooth scalar `f` equals the metric inner product of `X` with
the gradient `grad_g g hf`. -/
theorem tangentSectionAction_grad_g_eq_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) X f x =
      g.inner x (X x)
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  rw [grad_g_apply]
  rw [inner_gradFun_right (I := I) g f x (X x)]
  rfl

/-! ## Symmetry -/

/-- The metric inner product on two gradients is symmetric. -/
theorem inner_grad_g_symm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (x : M) :
    g.inner x ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g hh : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((grad_g (I := I) g hh : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((grad_g (I := I) g hf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) :=
  g.symm x _ _

/-! ## Compact support -/

/-- If `f` is locally zero near `x`, then the gradient of `f` vanishes at `x`. -/
lemma gradFun_eq_zero_of_eventuallyEq_zero
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ))) :
    gradFun (I := I) g f x = (0 : TangentSpace I x) := by
  apply gradFun_eq_zero_of_mfderiv_eq_zero
  rw [Filter.EventuallyEq.mfderiv_eq hf]
  rw [mfderiv_const]
  rfl

/-- The support of `gradFun g f` is contained in the topological support of `f`. -/
lemma support_gradFun_subset
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    Function.support (fun x : M => gradFun (I := I) g f x) ⊆ tsupport f := by
  intro x hx
  by_contra hxnotin
  have h_open : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hev : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_open.mem_nhds hxnotin] with y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  exact hx (gradFun_eq_zero_of_eventuallyEq_zero (I := I) g hev)

/-- If `f` has compact support, then so does the section `grad_g g hf`. -/
lemma hasCompactSupport_grad_g [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hf_cs : HasCompactSupport f) :
    HasCompactSupport ((grad_g (I := I) g hf :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) := by
  refine HasCompactSupport.of_support_subset_isCompact (hf_cs : IsCompact (tsupport f)) ?_
  intro x hx
  show x ∈ tsupport f
  exact support_gradFun_subset (I := I) g f hx

end DivergenceTheorem
end Integral
end DifferentialGeometry
