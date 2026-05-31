import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Geometry.Laplacian

/-!
# Codifferential and form Laplacian on a Riemannian manifold

For a smooth Riemannian metric `g` on a smooth manifold `M`, the **codifferential**
`δ` is the formal adjoint of the exterior derivative with respect to the `L²`
inner product on differential forms. On a closed Riemannian manifold,
$$\int_M \langle d\omega, \eta\rangle_g \, dV_g
  = \int_M \langle \omega, \delta\eta\rangle_g \, dV_g,$$
which characterises `δ` uniquely (modulo `L²`-extensions).

The **form Laplacian** (Hodge Laplacian) is then
`Δ_H = d δ + δ d` on differential forms; on functions (0-forms) it reduces to
`Δ_H f = δ d f`, which equals `−Δ_g f` (with the geometer convention used
throughout the project, where `Δ_g = div ∘ grad` is non-positive).

## Scope of this file

The full algebraic apparatus for differential forms of arbitrary degree is
substantial. This file develops the codifferential and the form Laplacian on
**0-forms** and **1-forms** — the simplest case — using chart-local
infrastructure:

* For a smooth tangent section `X` (which represents the metric-dual `1`-form
  `X^♭ = g(X, \cdot)`), the codifferential of `X^♭` is `-div_g X`.
* For a smooth scalar function `f` (a 0-form), the differential `d f` is the
  1-form whose metric-dual is `grad_g f`. Hence the form Laplacian on a 0-form
  is `δ d f = -div_g(grad_g f) = -Δ_g f`.

The general `k`-form codifferential, expressed in chart coordinates via the
Christoffel symbols of the metric, is a separate development that requires
chart-Christoffel infrastructure for tensorial divergence on higher-rank forms.

## Main definitions

* `codifferentialOfVectorField g X` : the codifferential of the metric-dual
  `1`-form of a smooth tangent section `X`, defined as `−divergence_g g X`.
  This is a smooth real-valued function on `M`.
* `formLaplacianScalar g hf` : the form Laplacian (Hodge Laplacian) of a smooth
  scalar function `f`, defined as the codifferential of its differential.

## Main results

* `codifferentialOfVectorField_contMDiff` : the codifferential of (the dual of)
  a smooth vector field is `C^∞`.
* `codifferentialOfVectorField_add` : additivity in the vector-field argument.
* `codifferentialOfVectorField_zero` : the codifferential of the zero
  vector field vanishes.
* `formLaplacianScalar_eq_neg_Δ_g` : the form Laplacian of a 0-form is the
  negative of the Laplace–Beltrami operator with the geometer sign convention,
  $$\Delta_H f \;=\; -\Delta_g f.$$
* `formLaplacianScalar_contMDiff` : smoothness of the form Laplacian on 0-forms.

## Sign convention

The geometer convention is used: `Δ_g = div ∘ grad`, so `Δ_g` is non-positive
on a closed manifold. With this choice the form Laplacian `Δ_H = δ d + d δ`
is non-negative on closed manifolds, and on 0-forms one has
`Δ_H f = δ d f = -Δ_g f`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Forms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

/-! ## Codifferential on 1-forms (via the metric-dual vector field)

For a smooth tangent section `X : Cₛ^∞⟮I; E, TangentSpace I⟯`, the associated
smooth 1-form is the *flat* `X^♭` defined by `X^♭_y(v) := g_y(X y, v)`. The
codifferential of `X^♭` is the unique real-valued smooth function on `M`
satisfying
$$\int_M (\delta X^\flat)(y) \cdot f(y) \, dV_g(y)
   = \int_M g_y(X y, \nabla_g f) \, dV_g(y)$$
for every smooth compactly supported test function `f`. The right-hand side,
by integration by parts, equals `-∫_M f · div_g X`, so
$$\delta X^\flat = -\operatorname{div}_g X.$$
We take this identity as the definition, and verify the basic algebraic
properties (smoothness, additivity, vanishing on zero). -/

/-- The codifferential of the `1`-form dual to a smooth tangent section `X`,
defined chart-locally as `δ X^♭(y) := -div_g X(y)`. -/
def codifferentialOfVectorField [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun y => -divergence_g (I := I) g X y

@[simp] lemma codifferentialOfVectorField_def [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    codifferentialOfVectorField (I := I) g X y =
      -divergence_g (I := I) g X y := rfl

/-- The codifferential of (the metric-dual `1`-form of) a smooth tangent
section is `C^∞`. -/
theorem codifferentialOfVectorField_contMDiff [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (codifferentialOfVectorField (I := I) g X) := by
  -- `δ X^♭ = -divergence_g g X`, and `divergence_g g X` is `C^∞`.
  have hdiv : ContMDiff I 𝓘(ℝ) ∞ (divergence_g (I := I) g X) :=
    divergence_g_contMDiff (I := I) g X
  -- Negation preserves smoothness pointwise.
  have hneg : ContMDiff I 𝓘(ℝ) ∞ (fun y : M => -divergence_g (I := I) g X y) :=
    hdiv.neg
  -- Identify the function under consideration.
  exact hneg

/-- The codifferential of (the metric-dual `1`-form of) a sum of smooth tangent
sections is the sum of the codifferentials. -/
theorem codifferentialOfVectorField_add [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    codifferentialOfVectorField (I := I) g (X + Y) y =
      codifferentialOfVectorField (I := I) g X y +
        codifferentialOfVectorField (I := I) g Y y := by
  -- Unfold both sides; apply `divergence_g_add`; algebra of negation on reals.
  change -divergence_g (I := I) g (X + Y) y =
    -divergence_g (I := I) g X y + -divergence_g (I := I) g Y y
  rw [divergence_g_add (I := I) g X Y y]
  ring

/-- The codifferential of (the metric-dual `1`-form of) the zero tangent
section vanishes pointwise. -/
@[simp] theorem codifferentialOfVectorField_zero [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (y : M) :
    codifferentialOfVectorField (I := I) g
        (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y = 0 := by
  change -divergence_g (I := I) g
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y = 0
  rw [divergence_g_zero (I := I) g y]
  exact neg_zero

/-! ## Form Laplacian on 0-forms

On a 0-form (scalar function) `f`, the Hodge–Laplace operator
`Δ_H = d δ + δ d` reduces to `δ d f`, since `δ` vanishes on 0-forms by
convention (a 0-form has no antecedent in degree `-1`). The differential
`d f` is the smooth 1-form whose metric-dual is the gradient `grad_g f`.
Hence the form Laplacian on a 0-form is the codifferential of (the metric-dual
of) `grad_g f`, i.e., `-div_g(grad_g f) = -Δ_g f`.

We adopt this as the definition. The identification `Δ_H f = -Δ_g f` then
holds **by definition** in a single rewrite, and serves as the cleanest bridge
between the form Laplacian and the Laplace–Beltrami operator under the
project's geometer sign convention. -/

/-- The Hodge–Laplace operator (form Laplacian) applied to a smooth scalar
function `f` (a 0-form): `Δ_H f := δ (d f)`. With `d f` represented through its
metric dual `grad_g f`, this is `−div_g (grad_g f) = −Δ_g f`. -/
def formLaplacianScalar [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : M → ℝ :=
  codifferentialOfVectorField (I := I) g (grad_g (I := I) g hf)

@[simp] lemma formLaplacianScalar_def [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    formLaplacianScalar (I := I) g hf y =
      codifferentialOfVectorField (I := I) g (grad_g (I := I) g hf) y := rfl

/-- The form Laplacian of a 0-form equals the negative of the Laplace–Beltrami
operator: `Δ_H f = -Δ_g f`. This is the standard relation between the Hodge
Laplacian and the geometer's `div ∘ grad` Laplacian, and follows directly from
the definitions of both operators in this file and `Geometry/Laplacian.lean`. -/
theorem formLaplacianScalar_eq_neg_Δ_g [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    formLaplacianScalar (I := I) g hf y =
      -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hf y := by
  -- `formLaplacianScalar g hf y = codifferentialOfVectorField g (grad_g g hf) y`
  --   = `-divergence_g g (grad_g g hf) y`
  --   = `-Δ_g g hf y`     (by `Δ_g_def`).
  change codifferentialOfVectorField (I := I) g (grad_g (I := I) g hf) y =
    -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hf y
  rw [codifferentialOfVectorField_def (I := I) g (grad_g (I := I) g hf) y]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def (I := I) g hf y]

/-- The form Laplacian of a smooth 0-form is smooth. -/
theorem formLaplacianScalar_contMDiff [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (formLaplacianScalar (I := I) g hf) :=
  codifferentialOfVectorField_contMDiff (I := I) g (grad_g (I := I) g hf)

/-! ## Algebraic properties of `Δ_H` on 0-forms

These follow from the corresponding properties of `Δ_g` (proved in
`Geometry/Laplacian.lean`) through the bridge identity
`Δ_H f = -Δ_g f`. We restate only the most basic ones — additivity and
behaviour on the zero function — leaving the spectral / `L²`-adjoint
identities to downstream development. -/

/-- `Δ_H` of the zero function vanishes. -/
@[simp] theorem formLaplacianScalar_zero [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (h0 : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ))) (y : M) :
    formLaplacianScalar (I := I) g h0 y = 0 := by
  -- `Δ_H 0 = -Δ_g 0`. The gradient of 0 is the zero section, hence the
  -- divergence vanishes. Conclude via `formLaplacianScalar_eq_neg_Δ_g`.
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g h0 y]
  -- Reduce to `Δ_g 0 = 0`.
  -- `Δ_g 0 y = div_g(grad_g 0) y = 0` since `grad_g 0` is the zero section.
  -- We need `grad_g g h0 = 0` to apply `divergence_g_zero`.
  have hgrad_zero : (grad_g (I := I) g h0 :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
    -- Section-level extensionality: both sections equal pointwise.
    apply ContMDiffSection.ext
    intro x
    change gradFun (I := I) g (fun _ : M => (0 : ℝ)) x =
        (0 : TangentSpace I x)
    -- The differential of a constant function is zero.
    apply gradFun_eq_zero_of_mfderiv_eq_zero
    -- `mfderiv I 𝓘(ℝ, ℝ) (fun _ => 0) x = 0`.
    exact mfderiv_const
  -- Apply.
  change -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g h0 y = 0
  rw [DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def (I := I) g h0 y]
  rw [hgrad_zero]
  rw [divergence_g_zero (I := I) g y]
  exact neg_zero

/-- Additivity of `Δ_H` on 0-forms (sum rule). -/
theorem formLaplacianScalar_add [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hfh : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f + h)) (y : M) :
    formLaplacianScalar (I := I) g hfh y =
      formLaplacianScalar (I := I) g hf y +
        formLaplacianScalar (I := I) g hh y := by
  -- Bridge through `Δ_g`, then use linearity of `Δ_g` (well, gradient first).
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g hfh y]
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g hf y]
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g hh y]
  -- Reduce to `Δ_g (f + h) y = Δ_g f y + Δ_g h y`.
  -- Use the structure of `Δ_g`: `Δ_g g hfh = div_g (grad_g g hfh)`, and
  -- `grad_g g hfh = grad_g g hf + grad_g g hh` pointwise (by `gradFun_add`).
  have hgrad_sum :
      (grad_g (I := I) g hfh : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
        (grad_g (I := I) g hf :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) +
        (grad_g (I := I) g hh :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
    apply ContMDiffSection.ext
    intro x
    -- `gradFun g (f + h) x = gradFun g f x + gradFun g h x` (by `gradFun_add`).
    change gradFun (I := I) g (f + h) x =
      gradFun (I := I) g f x + gradFun (I := I) g h x
    exact gradFun_add (I := I) g
      (hf.mdifferentiable (by simp) x) (hh.mdifferentiable (by simp) x)
  change -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hfh y =
    -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hf y +
      -DifferentialGeometry.Integral.DivergenceTheorem.Δ_g (I := I) g hh y
  rw [DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def (I := I) g hfh y]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def (I := I) g hf y]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.Δ_g_def (I := I) g hh y]
  rw [hgrad_sum]
  rw [divergence_g_add (I := I) g
        (grad_g (I := I) g hf) (grad_g (I := I) g hh) y]
  ring

end Forms
end Riemannian
end Geometry
end DifferentialGeometry
