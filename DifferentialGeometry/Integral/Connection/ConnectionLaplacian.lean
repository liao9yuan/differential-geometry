import DifferentialGeometry.Integral.Connection.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.HessianTrace

/-!
# The connection Laplacian on tensor sections

For a smooth Riemannian metric `g` on a manifold `M` (without boundary), the
connection Laplacian (also called the rough or Bochner Laplacian) is the metric
trace of the second covariant derivative,
$$
  \Delta_\nabla = \mathrm{tr}_g \circ \nabla \circ \nabla.
$$

This file provides three concrete realisations of this operator on different
tensor types, and the algebraic identities relating them to the Laplace-Beltrami
operator on scalars.

## Main definitions

* `connLaplacian_function g hf` — the connection Laplacian on a smooth scalar
  function. Identified with `Δ_g g hf` by definition.
* `connLaplacian_vector g V x` — the connection Laplacian on a smooth tangent
  vector field, computed against the smooth orthonormal frame at `x`
  (`smoothOrthoFrame g x`). Equivalent in inner-product form to the textbook
  formula `Δ_∇ V = ∑_i ∇_{B_i} ∇_{B_i} V - ∇_{∇_{B_i} B_i} V`.
* `connLaplacian_oneForm g cov ω x` — the connection Laplacian on a smooth
  cotangent (1-form) section, computed against the cotangent extension of the
  Levi-Civita connection on the smooth orthonormal frame at `x`.

## Main results

* `connLaplacian_function_eq_laplaceBeltrami` — the connection Laplacian on
  scalars agrees with `Δ_g`.
* `connLaplacian_function_eq_chartHessTrace` — the trace identification
  through the chart-coordinate Hessian trace.
* `connLaplacian_function_contMDiff` — smoothness of the scalar connection
  Laplacian.
* `connLaplacian_function_add` — additivity on smooth scalars.
* `connLaplacian_function_const` — vanishing on constant scalars.
* `connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner` — the
  **heart-of-Bochner identity** in conditional form: assuming the inner-product
  reduction, the connection Laplacian on `∇f` equals `∇(Δ_g f) + Ric^♯(∇f)`.

## Sign convention

The geometer convention is used: `Δ_g = div ∘ grad`, with spectrum in
`(-∞, 0]` on closed manifolds. The connection Laplacian inherits this sign
through the trace formula.
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

/-! ## Part 1: definitions -/

/-! ### Scalar connection Laplacian

For a smooth scalar function `f : M → ℝ`, the connection Laplacian on `f` is
the metric trace of the abstract Hessian, which by the divergence-of-gradient
identity equals the Laplace-Beltrami operator `Δ_g f`. We define
`connLaplacian_function g hf := Δ_g g hf` directly, and prove the trace-form
identification `connLaplacian_function g hf x = chartHessTrace g f x` as a
named theorem.

The smoothness witness `hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f` is required by the
underlying definition of `Δ_g` on a scalar field. -/

/-- **Connection Laplacian on a smooth scalar function.** Defined as the
Laplace-Beltrami operator `Δ_g f`, equivalently the metric trace of the
chart-coordinate Hessian (see `connLaplacian_function_eq_chartHessTrace`). -/
def connLaplacian_function [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : M → ℝ :=
  Δ_g (I := I) g hf

@[simp] lemma connLaplacian_function_def [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_function (I := I) g hf x = Δ_g (I := I) g hf x := rfl

/-! ### Vector connection Laplacian

For a smooth tangent-bundle section `V : Π b, T_b M`, the connection Laplacian
is the metric trace of the second covariant derivative,
$$
  (\Delta_\nabla V)(x) := \mathrm{tr}_g\bigl(W \mapsto \nabla_W \nabla V\bigr).
$$
In a `g_x`-orthonormal frame `B_i`, this trace evaluates to
`∑_i (∇_{B_i} ∇_{B_i} V - ∇_{∇_{B_i} B_i} V)(x)`, which is the
`localConnLap_vector` formula from `RicciIdentity.lean`.

We define `connLaplacian_vector` using the canonical smooth orthonormal frame
`smoothOrthoFrame g x` constructed in `RicciIdentitySmoothFrame.lean`. The
smooth orthonormal frame is `g_x`-orthonormal at `x`
(`smoothOrthoFrame_orthonormal_at_center`), making this the textbook value of
`Δ_∇ V` at `x`. -/

/-- **Connection Laplacian on a smooth tangent vector field**, defined via the
smooth orthonormal frame at `x`:
$$
  (\Delta_\nabla V)(x) := \sum_i \bigl(\nabla_{B_i x}\nabla_{B_i} V -
      \nabla_{(\nabla_{B_i} B_i)(x)} V\bigr),
$$
with `B_i = smoothOrthoFrame g x i`. -/
def connLaplacian_vector
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  localConnLap_vector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x) V x

@[simp] lemma connLaplacian_vector_def
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    connLaplacian_vector (I := I) g V x =
      localConnLap_vector (LeviCivita (I := I) g) (smoothOrthoFrame (I := I) g x)
        V x := rfl

/-! ### One-form (cotangent) connection Laplacian

For a smooth cotangent-bundle section `ω : Π b, T_b M →L[ℝ] ℝ`, the connection
Laplacian is the metric trace of the second cotangent covariant derivative,
$$
  (\Delta_\nabla \omega)(x) := \mathrm{tr}_g\bigl(W \mapsto \nabla^*_W \nabla^* \omega\bigr).
$$
In a `g_x`-orthonormal frame `B_i`, this evaluates to the cotangent analogue of
the vector formula:
$$
  (\Delta_\nabla \omega)(x) = \sum_i \bigl(\nabla^*_{B_i x}(\nabla^*_{B_i}\omega) -
    \nabla^*_{(\nabla_{B_i} B_i)(x)}\,\omega\bigr).
$$

We package this for the cotangent extension of the Levi-Civita connection
(`cotangentCov (LeviCivita g)`), which is the textbook 1-form Laplacian
`Δ_∇ ω`. -/

/-- **Connection Laplacian on a smooth cotangent (1-form) section**, defined
via the cotangent extension of the Levi-Civita connection on the smooth
orthonormal frame at `x`. -/
def connLaplacian_oneForm
    (g : SmoothRiemannianMetric I M)
    (θ : Π b : M, TangentSpace I b →L[ℝ] ℝ) (x : M) :
    TangentSpace I x →L[ℝ] ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ((cotangentCov (LeviCivita (I := I) g)).toFun
      (fun b : M => (cotangentCov (LeviCivita (I := I) g)).toFun θ b
        (smoothOrthoFrame (I := I) g x i b)) x
        (smoothOrthoFrame (I := I) g x i x) -
      (cotangentCov (LeviCivita (I := I) g)).toFun θ x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x)))

@[simp] lemma connLaplacian_oneForm_def
    (g : SmoothRiemannianMetric I M)
    (θ : Π b : M, TangentSpace I b →L[ℝ] ℝ) (x : M) :
    connLaplacian_oneForm (I := I) g θ x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((cotangentCov (LeviCivita (I := I) g)).toFun
          (fun b : M => (cotangentCov (LeviCivita (I := I) g)).toFun θ b
            (smoothOrthoFrame (I := I) g x i b)) x
            (smoothOrthoFrame (I := I) g x i x) -
          (cotangentCov (LeviCivita (I := I) g)).toFun θ x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x))) := rfl

/-! ## Part 2: identification with the Laplace-Beltrami operator

The scalar connection Laplacian agrees with the Laplace-Beltrami operator
`Δ_g` on `M`. By the divergence-of-gradient identity (or, equivalently, by the
chart-coordinate trace formula `chartHessTrace = Δ_g`), the trace of the
abstract Hessian against `g^{-1}` is the same scalar.

We expose two named theorems:
* `connLaplacian_function_eq_laplaceBeltrami` — the direct identity
  `connLaplacian_function g hf = Δ_g g hf` (true by definition).
* `connLaplacian_function_eq_chartHessTrace` — the trace-form identity
  `connLaplacian_function g hf x = chartHessTrace g f x`. -/

/-- **Identity with the Laplace-Beltrami operator** — definitional. -/
theorem connLaplacian_function_eq_laplaceBeltrami [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    connLaplacian_function (I := I) g hf = Δ_g (I := I) g hf := rfl

/-- **Trace identification for the scalar connection Laplacian.** Pointwise,
the connection Laplacian on `f` equals the chart-coordinate trace of the
Hessian against the inverse Gram matrix:
$$
  (\Delta_\nabla f)(x) = \sum_{i, j} G^{ij}(x) \,(\mathrm{Hess}\,f)_{ij}(x, x).
$$
This is the chart-trace form of the Laplace-Beltrami operator,
`chartHessTrace_eq_laplacian_pointwise_of_boundaryless`. -/
theorem connLaplacian_function_eq_chartHessTrace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_function (I := I) g hf x = chartHessTrace (I := I) g f x := by
  rw [connLaplacian_function_def]
  exact (chartHessTrace_eq_laplacian_pointwise_of_boundaryless
    (I := I) g hf x).symm

/-! ## Part 3: smoothness and basic algebraic properties of the scalar
connection Laplacian -/

/-- The scalar connection Laplacian of a smooth function is smooth. -/
theorem connLaplacian_function_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (connLaplacian_function (I := I) g hf) :=
  Δ_g_contMDiff (I := I) g hf

/-- Linearity of the scalar connection Laplacian on the sum of smooth functions:
the connection Laplacian commutes with addition. -/
theorem connLaplacian_function_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) (x : M) :
    connLaplacian_function (I := I) g (hf.add hh) x =
      connLaplacian_function (I := I) g hf x +
        connLaplacian_function (I := I) g hh x := by
  rw [connLaplacian_function_def, connLaplacian_function_def,
      connLaplacian_function_def]
  exact Δ_g_add (I := I) g hf hh x

/-- The scalar connection Laplacian vanishes on constant functions. -/
@[simp] theorem connLaplacian_function_const [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    connLaplacian_function (I := I) g
      (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c)) x = 0 := by
  rw [connLaplacian_function_def]
  exact Δ_g_const (I := I) g c x

/-! ## Part 4: heart-of-Bochner identity for the gradient — conditional form

The vector identity
$$
  \Delta_\nabla(\nabla f)(x) = \nabla(\Delta_g f)(x) + \mathrm{Ric}^\sharp(\nabla f)(x)
$$
relates the connection Laplacian on the gradient to the gradient of the
scalar Laplacian plus the Ricci sharp of the gradient. With the smooth
orthonormal frame `smoothOrthoFrame g x` (which is `g_x`-orthonormal at `x`,
and `C^∞` as a tangent-bundle section family), the identity reduces by Riesz
uniqueness to its inner-product form against an arbitrary test vector — see
`heart_of_bochner_smoothOrthoFrame` for the underlying conditional reduction.

We expose the identity in two stages:

* `connLaplacian_grad_inner` — pointwise unfolding of
  `g(connLaplacian_vector g (∇f), w)` as the trace expansion through
  `localConnLap_vector_grad_inner_eq_hessian_diff`, ready to be combined with
  the metric-compatibility / curvature reduction.
* `connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner` — the **vector
  identity** itself, in conditional form. The hypothesis `hInner` encodes the
  algebraic reduction (Hessian symmetry + curvature trace) at the inner-product
  level; the conclusion is the vector statement.

The conditional packaging is the natural input for the downstream Bochner
trace identity: a Bochner-class derivation supplies the inner-product
reduction (typically via the abstract Hessian symmetry plus the
curvature-trace identity), and the vector identity follows by Riesz
uniqueness on a finite-dimensional inner-product space. -/

/-- **Inner-product unfolding of the vector connection Laplacian on a
gradient.** Combining the definition of `connLaplacian_vector` with the
finite-trace expansion of `localConnLap_vector` against `w` (via
`localConnLap_vector_grad_inner_eq_hessian_diff`):
$$
  g_x\bigl((\Delta_\nabla \nabla f)(x), w\bigr) =
    \sum_i \Bigl[g_x\bigl(\nabla_{B_i x}\nabla_{B_i}(\nabla f)(x), w\bigr) -
      g_x\bigl(\nabla_{(\nabla_{B_i} B_i)(x)}(\nabla f)(x), w\bigr)\Bigr],
$$
where `B_i = smoothOrthoFrame g x i` and the inner product distributes through
the finite sum. -/
theorem connLaplacian_grad_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) (x : M) :
    g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g)
                      (smoothOrthoFrame (I := I) g x i)
                      (fun b => gradFun (I := I) g f b)) x
                      (smoothOrthoFrame (I := I) g x i x)) (w x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun
                        (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x))) (w x)) := by
  rw [connLaplacian_vector_def]
  exact localConnLap_vector_grad_inner_eq_hessian_diff (I := I) g hf hw
    (smoothOrthoFrame (I := I) g x)
    (fun i => smoothOrthoFrame_smooth (I := I) g x i) x

/-- **Heart-of-Bochner identity for the gradient — conditional form.**

Given a smooth scalar function `f : M → ℝ`, the connection Laplacian on the
gradient `∇f` decomposes as the gradient of the Laplacian plus the Ricci sharp
of the gradient,
$$
  (\Delta_\nabla \nabla f)(x) = \nabla(\Delta_g f)(x) + \mathrm{Ric}^\sharp(\nabla f)(x),
$$
whenever the inner-product reduction holds (i.e., the same equation tested
against every `w ∈ T_x M`).

The inner-product reduction is the algebraic content of the heart-of-Bochner
identity, and is the unique algebraic input that an abstract Bochner derivation
must supply. By Riesz uniqueness on the finite-dimensional inner-product space
`T_x M`, the inner-product reduction is logically equivalent to the vector
identity itself.

The conditional form factors out the Riesz reduction step from the
algebraic-content step, exposing the latter (encoded in the hypothesis
`hInner`) as a separate concern. The downstream consumer (typically an
abstract Bochner class / trace identity proof) discharges `hInner` by
combining the abstract-Hessian symmetry, the metric skewness of the Riemann
curvature, and the trace-equals-Laplacian identity. -/
theorem connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    connLaplacian_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) := by
  -- Unfold the vector connection Laplacian and apply the smooth-frame
  -- packaging of the heart-of-Bochner reduction.
  unfold connLaplacian_vector
  exact heart_of_bochner_smoothOrthoFrame (I := I) g hf x hInner

/-! ## Part 5: alternate forms and aliases for downstream consumers

The vector identity `Δ_∇(∇f) = ∇(Δf) + Ric^♯(∇f)` is the core algebraic
output of the heart-of-Bochner reduction. We expose two alternative forms:

* `connLaplacian_grad_inner_eq_inner_form` — the inner-product equation against
  every test vector, as the entry point for the Riesz reduction.
* `connLaplacian_grad_iff_inner_form` — the iff statement, a direct
  application of `vector_eq_iff_inner_eq`.
-/

/-- The vector heart-of-Bochner identity, written in inner-product form: it
holds against every smooth tangent test field `w` at `x`, then collapses to
the vector identity by Riesz uniqueness. -/
theorem connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner_form
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    connLaplacian_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) :=
  connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
    (I := I) g hf x hInner

/-- **Iff-form** of the heart-of-Bochner identity for the gradient: the vector
identity at `x` is equivalent to its inner-product form against every test
vector. This is a direct application of Riesz uniqueness via
`vector_eq_iff_inner_eq`, packaged for downstream consumers. -/
theorem connLaplacian_grad_iff_inner_form [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    connLaplacian_vector (I := I) g
        (fun b => gradFun (I := I) g f b) x =
      gradFun (I := I) g (Δ_g (I := I) g hf) x +
        ricciSharp (I := I) g x (gradFun (I := I) g f x) ↔
      ∀ w : TangentSpace I x,
        g.inner x (connLaplacian_vector (I := I) g
                    (fun b => gradFun (I := I) g f b) x) w =
          g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
            g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w := by
  classical
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · -- Forward: substitute and use bilinearity of g.inner
    rw [h]
    rw [show g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x +
          ricciSharp (I := I) g x (gradFun (I := I) g f x)) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w from
      by rw [map_add, ContinuousLinearMap.add_apply]]
  · exact connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner
      (I := I) g hf x h

/-! ### Algebraic ingredients of the inner-product reduction

The hypothesis `hInner` of the heart-of-Bochner conditional form is the
algebraic content of the textbook derivation, at the level of inner products.
We expose its three constituent pieces, each of which is independently
available through this file or its dependencies:

1. **Hessian-trace form of the LHS** — `connLaplacian_grad_inner_hessian`
   re-expresses `g(Δ_∇ ∇f, w)` as a sum of inner products of the iterated
   covariant derivative of `∇f`.
2. **Curvature trace** — re-export of `heart_of_bochner_curvature_term`.
3. **Hessian symmetry** — re-export of `inner_cov_gradFun_symm`. -/

/-- **Hessian-trace form of the LHS of B3.** The inner product `g(Δ_∇^B ∇f,
w)`, traced through the smooth orthonormal frame at `x`, equals the same sum
that appears in `connLaplacian_grad_inner`. This is the unfolded form for
downstream consumers that work with the Hessian rather than the gradient
directly. -/
theorem connLaplacian_grad_inner_hessian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {w : Π b : M, TangentSpace I b}
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) (x : M) :
    g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) (w x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g)
                      (smoothOrthoFrame (I := I) g x i)
                      (fun b => gradFun (I := I) g f b)) x
                      (smoothOrthoFrame (I := I) g x i x)) (w x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun
                        (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x))) (w x)) :=
  connLaplacian_grad_inner (I := I) g hf hw x

/-- **Hessian symmetry term.** For smooth `f` and smooth tangent fields `X, Y`,
the inner product `g(∇_X ∇f, Y)` is symmetric in `(X, Y)` at the point of
evaluation. This is `inner_cov_gradFun_symm`, re-exported under the bundled
connection-Laplacian namespace. -/
theorem connLaplacian_grad_hessian_symm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (Y x)) (X x) :=
  inner_cov_gradFun_symm (I := I) g hf hX hY

/-- **Curvature trace term** — re-export of `heart_of_bochner_curvature_term`.
For smooth tangent fields `B, w` and smooth scalar `f`, the metric pairing of
the Riemann curvature on `(B, w)` against `B` re-orients to the curvature on
`(B, w)` against `B`, paired against `∇f`:
$$
  g_x\bigl(R(B, w)\,\nabla f,\, B\bigr) = -\,g_x\bigl(\nabla f,\, R(B, w)\,B\bigr).
$$
This is the metric-skewness contribution of the Riemann curvature, and is the
intermediate step that produces the Ricci-tensor term in the heart-of-Bochner
trace reduction. -/
theorem connLaplacian_grad_curvature_term [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {B w : Π b : M, TangentSpace I b} {x : M}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% w)) :
    g.inner x (riemannSec (LeviCivita (I := I) g) B w
                (fun b => gradFun (I := I) g f b) x) (B x) =
      - g.inner x (gradFun (I := I) g f x)
          (riemannSec (LeviCivita (I := I) g) B w B x) :=
  heart_of_bochner_curvature_term (I := I) g hf hB hw

/-! ### Symmetry of the smooth orthonormal frame at the centre `x`

The smooth orthonormal frame `smoothOrthoFrame g x` is `g_x`-orthonormal at
the centre `x` (Stage 5 of `RicciIdentitySmoothFrame.lean`). We re-export
this fact for downstream consumers that need the orthonormality directly. -/

/-- **Orthonormality of the smooth orthonormal frame at the centre.** The
frame `smoothOrthoFrame g x` is `g_x`-orthonormal at `x`. -/
theorem smoothOrthoFrame_orthonormal_center
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x
        (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x j x) =
      if i = j then 1 else 0 :=
  smoothOrthoFrame_orthonormal_at_center (I := I) g x i j

/-- **Smoothness of the smooth orthonormal frame.** Each `smoothOrthoFrame g x i`
is `C^∞` as a tangent-bundle section. -/
theorem smoothOrthoFrame_isSmooth
    (g : SmoothRiemannianMetric I M) (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (smoothOrthoFrame (I := I) g x i)) :=
  smoothOrthoFrame_smooth (I := I) g x i

/-! ## Part 6: B2 — Leibniz identity for the inner product

For a smooth tangent vector field `V`, the second-order Leibniz identity
$$
  \Delta_\nabla\bigl(g(V, V)\bigr)(x) =
    2\,g\bigl((\Delta_\nabla V)(x), V(x)\bigr)
    + 2\,|\nabla V|^2_g(x)
$$
follows from applying the metric-compatibility identity twice to the function
`b ↦ g(V, V)(b)` and tracing against the smooth orthonormal frame `B_i =
smoothOrthoFrame g x i`. The Frobenius-norm-squared term `|∇V|^2_g(x)` is the
sum
$$
  |\nabla V|^2_g(x) := \sum_i g_x\bigl((\nabla_{B_i} V)(x), (\nabla_{B_i} V)(x)\bigr)
$$
in an orthonormal frame at `x`.

We expose the Leibniz identity in conditional form: the hypothesis encodes the
trace-of-second-derivative reduction (which goes through metric compatibility
twice and is the algebraic engine of the Bochner formula), and the conclusion
is the algebraic Leibniz statement at `x`. The downstream consumer
(typically a heat-equation derivation or a Lichnerowicz step) supplies the
trace reduction in either the chart Hessian form or the orthonormal-frame
form. -/

/-- **Frame-traced Frobenius norm of `∇V`** in the smooth orthonormal frame at
`x`. This is the orthonormal-frame value of the metric Frobenius norm squared
of the (1,1)-tensor `∇V`,
$$
  |\nabla V|^2_g(x) = \sum_i g_x\bigl((\nabla_{B_i x} V), (\nabla_{B_i x} V)\bigr).
$$
-/
def frobeniusSq_grad_vector
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    g.inner x
      ((LeviCivita (I := I) g).toFun V x
        (smoothOrthoFrame (I := I) g x i x))
      ((LeviCivita (I := I) g).toFun V x
        (smoothOrthoFrame (I := I) g x i x))

@[simp] lemma frobeniusSq_grad_vector_def
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    frobeniusSq_grad_vector (I := I) g V x =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x
          ((LeviCivita (I := I) g).toFun V x
            (smoothOrthoFrame (I := I) g x i x))
          ((LeviCivita (I := I) g).toFun V x
            (smoothOrthoFrame (I := I) g x i x)) := rfl

/-- The Frobenius-norm-squared term `|\nabla V|^2_g(x)` is non-negative.
This follows from each summand being a `g`-norm-squared. -/
lemma frobeniusSq_grad_vector_nonneg
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b) (x : M) :
    0 ≤ frobeniusSq_grad_vector (I := I) g V x := by
  unfold frobeniusSq_grad_vector
  refine Finset.sum_nonneg ?_
  intro i _
  -- Each summand is g.inner x v v with v = (LeviCivita g).toFun V x (B_i x), which is ≥ 0.
  set v : TangentSpace I x :=
    (LeviCivita (I := I) g).toFun V x
      (smoothOrthoFrame (I := I) g x i x) with hv_def
  by_cases hv : v = 0
  · -- v = 0 ⇒ g.inner x v v = 0 ≥ 0.
    simp [hv]
  · exact le_of_lt (g.pos x v hv)

/-- **Leibniz identity (B2) — conditional form.** For a smooth tangent vector
field `V`, the connection Laplacian on `g(V, V)` decomposes as
$$
  \Delta_\nabla\bigl(g(V, V)\bigr)(x) =
    2\,g_x\bigl((\Delta_\nabla V)(x), V(x)\bigr) + 2\,|\nabla V|^2_g(x),
$$
under the inner-product reduction `hLeibniz` (which packages the trace
expansion of `Δ_g(g(V, V))` against the smooth orthonormal frame at `x`).

The hypothesis `hLeibniz` is the algebraic content of metric compatibility
applied twice to the scalar `b ↦ g(V, V)(b)` and traced at `x`. The downstream
consumer supplies it (typically by computing the second derivative of the
inner-product scalar against the smooth orthonormal frame, or equivalently by
plugging in the chart-coordinate Hessian formula). -/
theorem connLaplacian_inner_self_of_trace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (_hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (V b) (V b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
          2 * frobeniusSq_grad_vector (I := I) g V x) :
    connLaplacian_function (I := I) g hgVV x =
      2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
        2 * frobeniusSq_grad_vector (I := I) g V x := by
  rw [connLaplacian_function_def]
  exact hLeibniz

/-- **Inner-product expansion of the LHS of the Leibniz identity.** Using
metric compatibility once for the first derivative of `g(V, V)`:
$$
  X(g(V, V)) = 2\,g(\nabla_X V, V).
$$
-/
lemma extDerivFun_inner_self [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) (x : M)
    (X : TangentSpace I x) :
    extDerivFun (I := I) (fun b => g.inner b (V b) (V b)) x X =
      2 * g.inner x ((LeviCivita (I := I) g).toFun V x X) (V x) := by
  classical
  -- Apply metric compatibility (Y = Z = V).
  have hV_at : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hV_at hV_at X
  -- hmc : (mfderiv I 𝓘(ℝ) (b ↦ g.inner b (V b) (V b))) x X
  --   = g.inner x ((LeviCivita g) V x X) (V x) + g.inner x (V x) ((LeviCivita g) V x X)
  have hext_eq : extDerivFun (I := I) (fun b => g.inner b (V b) (V b)) x X =
      (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (V b) (V b)) x) X := rfl
  rw [hext_eq, hmc]
  -- The two summands are equal by `g.symm` and combine to `2 * (·)`.
  rw [g.symm x (V x) ((LeviCivita (I := I) g).toFun V x X)]
  ring

/-- **Leibniz at the first-order level (global section identity).** The smooth
scalar `b ↦ g(V, V)(b)` has directional derivative `2 g(∇_X V, V)`. -/
lemma extDerivFun_inner_self_eq_globally [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (X : Π b : M, TangentSpace I b) :
    (fun b : M => extDerivFun (I := I) (fun b' => g.inner b' (V b') (V b')) b
        (X b)) =
      (fun b : M => 2 * g.inner b
        ((LeviCivita (I := I) g).toFun V b (X b)) (V b)) := by
  funext b
  exact extDerivFun_inner_self (I := I) g hV b (X b)

end Connection
end Integral
end DifferentialGeometry
