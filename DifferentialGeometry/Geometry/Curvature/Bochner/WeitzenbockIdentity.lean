import DifferentialGeometry.Geometry.Connection.Laplacian.ConnectionLaplacian
import DifferentialGeometry.Geometry.Connection.ChartBridge.Laplacian
import DifferentialGeometry.Geometry.Connection.ChartBridge.HessFrobenius
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace

/-!
# Coordinate-free Bochner-Weitzenböck identity

For a smooth Riemannian metric `g` on a manifold `M` (without boundary) and a smooth
real-valued scalar function `f : M → ℝ`, the **Bochner-Weitzenböck identity** reads
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(\nabla f, \nabla f)\bigr) =
    g(\Delta_\nabla \nabla f, \nabla f) + |\nabla^2 f|_g^2
  = g(\nabla \Delta_g f, \nabla f) + \mathrm{Ric}(\nabla f, \nabla f) + |\nabla^2 f|_g^2.
$$
The first equality is the trace form of the **Leibniz identity** for the inner product
applied to the gradient; the second equality is the **heart-of-Bochner** commutator
identity exchanging the connection Laplacian on the gradient with the gradient of the
scalar Laplacian, modulo a Ricci correction.

This file develops the four building blocks of the identity:

* **B1 — Inner-product Leibniz** (`leibniz_inner`): for any two smooth tangent fields,
  the directional derivative of `b ↦ g(V, W)(b)` decomposes as a sum of two
  inner-product terms. This is the metric-compatibility identity for the Levi-Civita
  connection.
* **B2 — Trace formula for `Δ_g(g(V, V))`** (`laplacian_inner_self`): conditional on
  the trace reduction `hLeibniz`, the scalar Laplacian on `g(V, V)` decomposes as
  `2 g(Δ_∇ V, V) + 2 |∇V|²_g`.
* **B3 — Connection-Laplacian-gradient commutator** (`laplacian_grad_eq_grad_laplacian_plus_ricciSharp`):
  conditional on the inner-product reduction `hInner`, the connection Laplacian on
  `∇f` equals `∇(Δ_g f) + Ric^♯(∇f)`.
* **B4 — Bochner main identity** (`bochner_abstract`): conditional on both `hLeibniz`
  and `hInner`, the Bochner-Weitzenböck identity holds at `x`.

The unconditional fallback packages the heart-of-Bochner identity as a hypothesis:
* **`bochner_abstract_of_heart_of_bochner`**: given the vector heart-of-Bochner
  identity as input, the trace reduction `hLeibniz` (already conditional in B2)
  collapses the inner-product expansion of the Laplacian on `g(∇f, ∇f)` into the
  Bochner-Weitzenböck right-hand side.

## Sign convention

The geometer convention is used: `Δ_g = div ∘ grad`, with spectrum in `(-∞, 0]` on
closed manifolds. The connection Laplacian `Δ_∇` shares this sign through its trace
formula. The Ricci tensor `ricciTensor` and its sharp `ricciSharp` are unsigned (the
defining identity is `g(Ric^♯(v), w) = Ric(v, w)`).
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

/-- **B1 — Inner-product Leibniz identity (Levi-Civita).** For smooth tangent
fields `V`, `W` and a tangent vector `X ∈ T_x M`, the directional derivative of
the scalar `b ↦ g(V, W)(b)` along `X` decomposes via the metric-compatibility
identity for the Levi-Civita connection:
$$
  X\bigl(g(V, W)\bigr) = g\bigl((\nabla_X V), W\bigr) + g\bigl(V, (\nabla_X W)\bigr).
$$
Here `X` is identified with a tangent vector at `x`, and the left-hand side is the
manifold differential `mfderiv I 𝓘(ℝ) (b ↦ g.inner b (V b) (W b)) x X`. -/
theorem leibniz_inner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V W : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    {x : M} (X : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (V b) (W b)) x) X =
      g.inner x ((LeviCivita (I := I) g).toFun V x X) (W x) +
        g.inner x (V x) ((LeviCivita (I := I) g).toFun W x X) := by
  classical
  have hV_at : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  exact (LeviCivita_isMetricCompatible (I := I) g).apply hV_at hW_at X

/-- **B1 — Inner-product Leibniz identity, section form.** For smooth tangent
fields `V`, `W` and a smooth tangent field `X`, the directional derivative of
`b ↦ g(V, W)(b)` along `X` is, as a scalar function on `M`:
$$
  b \mapsto X(g(V, W))(b) =
    g_b\bigl((\nabla_{X b} V)(b), W(b)\bigr) + g_b\bigl(V(b), (\nabla_{X b} W)(b)\bigr).
$$
-/
theorem leibniz_inner_globally [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V W : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (X : Π b : M, TangentSpace I b) :
    (fun b : M => (mfderiv I 𝓘(ℝ) (fun b' : M => g.inner b' (V b') (W b')) b)
        (X b)) =
      (fun b : M =>
        g.inner b ((LeviCivita (I := I) g).toFun V b (X b)) (W b) +
          g.inner b (V b) ((LeviCivita (I := I) g).toFun W b (X b))) := by
  funext b
  exact leibniz_inner (I := I) g hV hW (X b)

/-- **B2 — Trace formula for `Δ_g(g(V, V))` (conditional).** For a smooth tangent
vector field `V`, conditional on the trace reduction `hLeibniz` (which packages
the second-derivative trace of `b ↦ g(V, V)(b)` into the Laplacian),
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(V, V)\bigr)(x) =
    g_x\bigl((\Delta_\nabla V)(x), V(x)\bigr) + |\nabla V|^2_g(x).
$$

The smoothness witness `hgVV : ContMDiff … (b ↦ g(V, V)(b))` is required in order
to apply `Δ_g` to the inner-product scalar. The frame-traced Frobenius norm of
`∇V` is `frobeniusSq_grad_vector g V x`.

The hypothesis `hLeibniz` collapses the second-derivative trace expansion of
`b ↦ g(V, V)(b)` against the smooth orthonormal frame at `x` into the equation
displayed below; this is the algebraic engine of metric compatibility applied
twice to the scalar `b ↦ g(V, V)(b)` and traced. -/
theorem laplacian_inner_self [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (V b) (V b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
          2 * frobeniusSq_grad_vector (I := I) g V x) :
    Δ_g (I := I) g hgVV x =
      2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
        2 * frobeniusSq_grad_vector (I := I) g V x := by
  have h := connLaplacian_inner_self_of_trace (I := I) g hV hgVV x hLeibniz
  rw [connLaplacian_function_def] at h
  exact h

/-- **B2 — Half-form of the trace formula.** Dividing both sides of B2 by 2 (or
equivalently, multiplying the right-hand side by 1/2 in the `½ Δ_g(g(V, V))` form)
gives the conventional "half" identity
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(V, V)\bigr)(x) =
    g_x\bigl((\Delta_\nabla V)(x), V(x)\bigr) + |\nabla V|^2_g(x).
$$
-/
theorem laplacian_inner_self_half [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (V b) (V b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
          2 * frobeniusSq_grad_vector (I := I) g V x) :
    (1 / 2 : ℝ) * Δ_g (I := I) g hgVV x =
      g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
        frobeniusSq_grad_vector (I := I) g V x := by
  rw [laplacian_inner_self (I := I) g hV hgVV x hLeibniz]
  ring

/-- **B3 — Connection-Laplacian-gradient commutator (conditional).** For a smooth
scalar `f : M → ℝ`, conditional on the inner-product reduction `hInner` (which
packages the Hessian-symmetry + curvature-trace combinatorial argument at `x`),
$$
  \Delta_\nabla(\nabla f)(x) = \nabla(\Delta_g f)(x) + \mathrm{Ric}^\sharp(\nabla f)(x).
$$

The hypothesis `hInner` expresses the inner-product form of the heart-of-Bochner
identity: for every test vector `w ∈ T_x M`, the inner products of the LHS and the
RHS coincide. By Riesz uniqueness on the finite-dimensional inner-product space
`T_x M`, this is logically equivalent to the vector identity itself. -/
theorem laplacian_grad_eq_grad_laplacian_plus_ricciSharp [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
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

/-- **B3 — Tested form of the heart-of-Bochner identity.** Pairing the vector
heart-of-Bochner identity against an arbitrary vector `w ∈ T_x M`,
$$
  g_x\bigl((\Delta_\nabla \nabla f)(x), w\bigr) =
    g_x\bigl(\nabla(\Delta_g f)(x), w\bigr) +
      \mathrm{Ric}_x\bigl(\nabla f(x), w\bigr).
$$
The RHS uses the defining identity `g(Ric^♯(v), w) = Ric(v, w)`. -/
theorem laplacian_grad_inner_eq_grad_laplacian_plus_ricci [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w)
    (w : TangentSpace I x) :
    g.inner x (connLaplacian_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x) w =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
        ricciTensor (I := I) g x (gradFun (I := I) g f x) w := by
  rw [hInner w, inner_ricciSharp (I := I) g x (gradFun (I := I) g f x) w]

/-- **B4 — Bochner main identity (conditional).** For a smooth scalar `f : M → ℝ`,
conditional on the trace reduction `hLeibniz` (B2 hypothesis) and the inner-product
reduction `hInner` (B3 hypothesis), the Bochner-Weitzenböck identity holds at `x`:
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    g_x\bigl(\nabla(\Delta_g f)(x), \nabla f(x)\bigr)
    + \mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr)
    + |\nabla^2 f|_g^2(x).
$$

The LHS uses `Δ_g g hgVV`, where `hgVV` is the smoothness witness of
`b ↦ g(∇f, ∇f)(b)`. The Frobenius-norm-squared term uses
`frobeniusSq_grad_vector g (gradFun g f) x`. -/
theorem bochner_abstract [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (gradFun (I := I) g f b) (gradFun (I := I) g f b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g
                        (fun b => gradFun (I := I) g f b) x)
                       (gradFun (I := I) g f x) +
          2 * frobeniusSq_grad_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    (1 / 2 : ℝ) * Δ_g (I := I) g hgVV x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x := by
  classical
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g f b)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB2 :=
    laplacian_inner_self_half (I := I) g h_grad_smooth hgVV x hLeibniz
  rw [hB2]
  have hB3 :=
    laplacian_grad_inner_eq_grad_laplacian_plus_ricci (I := I) g hf x hInner
      (gradFun (I := I) g f x)
  rw [hB3]

/-- **Bochner identity given heart-of-Bochner as input.** For a smooth scalar
`f : M → ℝ`, given the heart-of-Bochner vector identity at `x` and the trace
reduction `hLeibniz` for `b ↦ g(∇f, ∇f)(b)`, the Bochner-Weitzenböck identity
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    g_x\bigl(\nabla(\Delta_g f)(x), \nabla f(x)\bigr)
    + \mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr)
    + |\nabla^2 f|_g^2(x)
$$
holds.

This is the vector-form variant of `bochner_abstract`: the inner-product reduction
`hInner` is replaced by the vector heart-of-Bochner identity directly. -/
theorem bochner_abstract_of_heart_of_bochner [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (gradFun (I := I) g f b) (gradFun (I := I) g f b)))
    (x : M)
    (hLeibniz :
      Δ_g (I := I) g hgVV x =
        2 * g.inner x (connLaplacian_vector (I := I) g
                        (fun b => gradFun (I := I) g f b) x)
                       (gradFun (I := I) g f x) +
          2 * frobeniusSq_grad_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x)
    (hHeart :
      connLaplacian_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x =
        gradFun (I := I) g (Δ_g (I := I) g hf) x +
          ricciSharp (I := I) g x (gradFun (I := I) g f x)) :
    (1 / 2 : ℝ) * Δ_g (I := I) g hgVV x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x := by
  classical
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g f b)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB2 :=
    laplacian_inner_self_half (I := I) g h_grad_smooth hgVV x hLeibniz
  rw [hB2]
  rw [hHeart]
  rw [show g.inner x
        (gradFun (I := I) g (Δ_g (I := I) g hf) x +
          ricciSharp (I := I) g x (gradFun (I := I) g f x))
        (gradFun (I := I) g f x) =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
      g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x))
        (gradFun (I := I) g f x) from by
    rw [map_add, ContinuousLinearMap.add_apply]]
  rw [inner_ricciSharp (I := I) g x (gradFun (I := I) g f x)
        (gradFun (I := I) g f x)]

/-- **Smoothness of `b ↦ g(∇f, ∇f)(b)`.** For a smooth scalar `f`, the inner
product of the gradient with itself is `C^∞` on `M`. -/
theorem normGradSq_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (gradFun (I := I) g f b)
        (gradFun (I := I) g f b)) := by
  exact normGradSqFun_contMDiff (I := I) g hf

/-- **B4 — Bochner main identity, packaged form.** Same as `bochner_abstract`,
with the smoothness witness for `b ↦ g(∇f, ∇f)(b)` produced inline from `hf`. -/
theorem bochner_abstract_packaged [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hLeibniz :
      Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
        2 * g.inner x (connLaplacian_vector (I := I) g
                        (fun b => gradFun (I := I) g f b) x)
                       (gradFun (I := I) g f x) +
          2 * frobeniusSq_grad_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x)
    (hInner : ∀ w : TangentSpace I x,
      g.inner x (connLaplacian_vector (I := I) g
                  (fun b => gradFun (I := I) g f b) x) w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
          g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_abstract (I := I) g hf (normGradSq_contMDiff (I := I) g hf) x
    hLeibniz hInner

/-- **Bochner identity given heart-of-Bochner, packaged form.** Same as
`bochner_abstract_of_heart_of_bochner`, with the smoothness witness for
`b ↦ g(∇f, ∇f)(b)` produced inline from `hf`. -/
theorem bochner_abstract_of_heart_of_bochner_packaged [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hLeibniz :
      Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
        2 * g.inner x (connLaplacian_vector (I := I) g
                        (fun b => gradFun (I := I) g f b) x)
                       (gradFun (I := I) g f x) +
          2 * frobeniusSq_grad_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x)
    (hHeart :
      connLaplacian_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x =
        gradFun (I := I) g (Δ_g (I := I) g hf) x +
          ricciSharp (I := I) g x (gradFun (I := I) g f x)) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_abstract_of_heart_of_bochner (I := I) g hf
    (normGradSq_contMDiff (I := I) g hf) x hLeibniz hHeart

/-- **Chart orthonormality at `x`**. The canonical chart at `x` is
`g`-orthonormal at `x` precisely when the inverse Gram matrix
`chartInvGramMatrix g x x` is the identity matrix. Equivalent geometric
condition: the chart-basis frame `chartBasisVecFiber x i x = (Module.finBasis
ℝ E) i` is `g_x`-orthonormal as a basis of `T_x M`. -/
def IsChartOrthonormalAt
    (g : SmoothRiemannianMetric I M) (x : M) : Prop :=
  ∀ i j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0

/-- **B2 — Conditional trace reduction packaged as a Prop.** The trace
reduction `hLeibniz` of the inner-product Laplacian (B2 hypothesis), packaged
as a predicate on the metric `g`, the tangent vector field `V`, and the point
`x`. The unfolder `IsLeibnizTraceAt_def` gives the definitional equality. -/
@[reducible] def IsLeibnizTraceAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (V : Π b : M, TangentSpace I b)
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => g.inner b (V b) (V b)))
    (x : M) : Prop :=
  Δ_g (I := I) g hgVV x =
    2 * g.inner x (connLaplacian_vector (I := I) g V x) (V x) +
      2 * frobeniusSq_grad_vector (I := I) g V x

/-- **B3 — Conditional heart-of-Bochner reduction packaged as a Prop.** The
inner-product reduction `hInner` (B3 hypothesis), packaged as a predicate on
the metric `g`, the smooth scalar `f`, and the point `x`. -/
@[reducible] def IsHeartOfBochnerInnerAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) : Prop :=
  ∀ w : TangentSpace I x,
    g.inner x (connLaplacian_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x) w =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w +
        g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w

/-- **B2 + B3 packaging**. Both Bochner reductions at the same point, packaged
as a `BochnerReductionAt` record. -/
structure BochnerReductionAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) : Prop where
  leibniz : IsLeibnizTraceAt (I := I) g
    (fun b => gradFun (I := I) g f b) (normGradSq_contMDiff (I := I) g hf) x
  heart : IsHeartOfBochnerInnerAt (I := I) g hf x

/-- **Bochner-Weitzenböck identity from a packaged reduction**. Given a
`BochnerReductionAt g hf x` record packaging both the trace reduction `hLeibniz`
and the heart-of-Bochner inner-product reduction `hInner`, the
Bochner-Weitzenböck identity holds at `x` in its conventional half-form:
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    g_x\bigl(\nabla(\Delta_g f)(x), \nabla f(x)\bigr)
    + \mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr)
    + |\nabla^2 f|_g^2(x).
$$
-/
theorem bochner_pointwise_abstract_of_reduction [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hRed : BochnerReductionAt (I := I) g hf x) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_abstract_packaged (I := I) g hf x hRed.leibniz hRed.heart

/-- **Bochner-Weitzenböck identity at `x`, packaged with both reductions inlined**.
The Bochner-Weitzenböck identity in its conventional half-form, packaged as a
single statement that takes the two algebraic reductions (`hLeibniz` and
`hInner`) as inputs. This is the cleanest "reduction-input" form of the identity,
suitable as the entry point for downstream consumers that supply both reductions.

The hypotheses are:

* `hLeibniz`: the trace reduction (B2 input). Expresses
  `Δ_g(g(∇f, ∇f))(x) = 2 g_x(Δ_∇ ∇f, ∇f) + 2 |∇²f|_g²(x)` algebraically.

* `hInner`: the heart-of-Bochner inner-product reduction (B3 input). Expresses
  the inner-product form of the heart-of-Bochner identity, against every test
  vector `w ∈ T_x M`.

This is the cleanest single-statement packaging suitable for downstream
consumers; each hypothesis is supplied at the callsite via either the chart
orthonormality route or the direct metric-compatibility route. -/
theorem bochner_pointwise_abstract [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hLeibniz :
      IsLeibnizTraceAt (I := I) g
        (fun b => gradFun (I := I) g f b)
        (normGradSq_contMDiff (I := I) g hf) x)
    (hInner : IsHeartOfBochnerInnerAt (I := I) g hf x) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_pointwise_abstract_of_reduction (I := I) g hf x ⟨hLeibniz, hInner⟩

/-- **Sum of `abstractHessian` on a `g_x`-orthonormal frame equals the Laplacian.**
For any `g_x`-orthonormal basis `(B_i)` of `T_x M` and any smooth scalar
`f : M → ℝ`:
$$
  \sum_i \mathrm{abstractHessian}\,g\,f\,x\,(B_i)\,(B_i) = \Delta_g f x.
$$
-/
theorem sum_abstractHessian_orthonormal_eq_laplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ i : Fin (Module.finrank ℝ E),
      abstractHessian (I := I) g f x (B i) (B i) =
      Δ_g (I := I) g hf x := by
  classical
  have htrace := orthonormal_basis_bilin_trace (I := I) g x
    (abstractHessian (I := I) g f x) B hB
  rw [htrace]
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          abstractHessian (I := I) g f x ((chartModelBasis E) k)
            ((chartModelBasis E) l)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          chartHessianTensor (I := I) g x f k l x from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [hM k l]]
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          chartHessianTensor (I := I) g x f k l x) =
      chartHessTrace (I := I) g f x from rfl]
  exact chartHessTrace_eq_laplacian_pointwise_of_boundaryless (I := I) g hf x

/-- **Sum of `abstractHessian` on the smooth orthonormal frame at `x` equals the Laplacian.**
For any smooth scalar `f : M → ℝ`:
$$
  \sum_i \mathrm{abstractHessian}\,g\,f\,x\,(\mathrm{smoothOrthoFrame}\,g\,x\,i\,x)
    \,(\mathrm{smoothOrthoFrame}\,g\,x\,i\,x) = \Delta_g f x.
$$
-/
theorem sum_abstractHessian_smoothOrthoFrame_eq_laplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
      abstractHessian (I := I) g f x
        (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x i x) =
      Δ_g (I := I) g hf x :=
  sum_abstractHessian_orthonormal_eq_laplacian (I := I) g hf x
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)

/-- **Per-summand abstract Hessian of an inner-product squared.** For smooth
tangent fields `V, Y` on `M`, the abstract Hessian of `b ↦ g(V, V)(b)` evaluated
at `(Y x, Y x)` admits the metric-compatibility expansion: the algebraic
content of the Leibniz identity for `g` applied twice to the inner-product
scalar. -/
theorem abstractHessian_innerSelf_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V))
    {Y : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (V b) (V b)))
    (x : M) :
    abstractHessian (I := I) g
        (fun b : M => g.inner b (V b) (V b)) x (Y x) (Y x) =
      2 * (g.inner x ((LeviCivita (I := I) g).toFun
              (covApply (LeviCivita (I := I) g) Y V) x (Y x)) (V x) -
            g.inner x ((LeviCivita (I := I) g).toFun V x
              ((LeviCivita (I := I) g).toFun Y x (Y x))) (V x)) +
        2 * g.inner x
          ((LeviCivita (I := I) g).toFun V x (Y x))
          ((LeviCivita (I := I) g).toFun V x (Y x)) := by
  classical
  set f' : M → ℝ := fun b => g.inner b (V b) (V b) with hf'_def
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f' with hθ_def
  have hθ_at : MDiffAtCotangent θ x := by
    have hθ_smooth := cotangentCov_extDerivFun_smooth (I := I) hgVV
    exact (hθ_smooth x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hdual := cotangentCov_dualPairing (LeviCivita (I := I) g) hθ_at hY_at (Y x)
  have habsH : abstractHessian (I := I) g f' x (Y x) (Y x) =
      ((cotangentCov (LeviCivita (I := I) g)).toFun θ x (Y x)) (Y x) := rfl
  rw [habsH]
  have h_isolate :
      ((cotangentCov (LeviCivita (I := I) g)).toFun θ x (Y x)) (Y x) =
        extDerivFun (I := I) (fun b : M => θ b (Y b)) x (Y x) -
          θ x ((LeviCivita (I := I) g).toFun Y x (Y x)) := by
    linarith [hdual]
  rw [h_isolate]
  have hθY_eq : ∀ b : M, θ b (Y b) =
      2 * g.inner b ((LeviCivita (I := I) g).toFun V b (Y b)) (V b) := by
    intro b
    exact extDerivFun_inner_self (I := I) g hV b (Y b)
  have h_func_eq : (fun b : M => θ b (Y b)) =
      (fun b : M => 2 * g.inner b
        ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) := by
    funext b
    exact hθY_eq b
  rw [h_func_eq]
  have h_2_factor :
      extDerivFun (I := I)
        (fun b : M => 2 * g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x (Y x) =
      2 * extDerivFun (I := I)
        (fun b : M => g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x (Y x) := by
    have hP_smooth0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (covApply (LeviCivita (I := I) g) Y V)) :=
      contMDiffOn_univ.mp
        (covApply_contMDiffOn (cov := LeviCivita (I := I) g) hY hV)
    have h_inner_at : MDiffAt
        (fun b : M => g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x := by
      have hsmooth :
          ContMDiff I 𝓘(ℝ, ℝ) ∞
            (fun b : M => g.inner b (covApply (LeviCivita (I := I) g) Y V b) (V b)) := by
        have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
            (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
              (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
              b (g.inner b)) :=
          g.contMDiff
        have happ :
            ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
              (fun m : M => (⟨m,
                  g.inner m (covApply (LeviCivita (I := I) g) Y V m) (V m)⟩ :
                    TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
          ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
            (b := id) hg hP_smooth0 hV
        intro m
        have hpm := happ m
        rw [Bundle.contMDiffAt_totalSpace] at hpm
        exact hpm.2
      have hsmooth_eq : (fun b : M => g.inner b
            ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) =
          (fun b : M => g.inner b (covApply (LeviCivita (I := I) g) Y V b) (V b)) := rfl
      rw [hsmooth_eq]
      exact (hsmooth x).mdifferentiableAt (by simp)
    have h_mul : (fun b : M => 2 * g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) =
        ((2 : ℝ) • fun b : M => g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) := by
      funext b
      change (2 : ℝ) * _ = (2 : ℝ) • _
      rw [smul_eq_mul]
    rw [h_mul]
    change (mfderiv I 𝓘(ℝ, ℝ) ((2 : ℝ) • fun b : M => g.inner b
        ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x) (Y x) = _
    rw [const_smul_mfderiv h_inner_at (2 : ℝ)]
    simp [smul_eq_mul]
    rfl
  rw [h_2_factor]
  set P : Π b : M, TangentSpace I b :=
    fun b : M => (LeviCivita (I := I) g).toFun V b (Y b) with hP_def
  have hP_eq_covApply : P = covApply (LeviCivita (I := I) g) Y V := rfl
  have hP_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% P) := by
    rw [hP_eq_covApply]
    exact contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := LeviCivita (I := I) g) hY hV)
  have hP_at : MDiffAt (T% P) x := (hP_smooth x).mdifferentiableAt (by simp)
  have hV_at : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hP_at hV_at (Y x)
  have h_extDerivFun_eq :
      extDerivFun (I := I) (fun b : M => g.inner b
        ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x (Y x) =
      g.inner x ((LeviCivita (I := I) g).toFun P x (Y x)) (V x) +
        g.inner x (P x) ((LeviCivita (I := I) g).toFun V x (Y x)) := hmc
  have hPx : P x = (LeviCivita (I := I) g).toFun V x (Y x) := rfl
  rw [hPx] at h_extDerivFun_eq
  rw [h_extDerivFun_eq]
  have hLCP : (LeviCivita (I := I) g).toFun P x (Y x) =
      (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y V) x (Y x) :=
    by rw [hP_eq_covApply]
  rw [hLCP]
  have hθ_x_LC : θ x ((LeviCivita (I := I) g).toFun Y x (Y x)) =
      2 * g.inner x ((LeviCivita (I := I) g).toFun V x
        ((LeviCivita (I := I) g).toFun Y x (Y x))) (V x) := by
    change extDerivFun (I := I) f' x ((LeviCivita (I := I) g).toFun Y x (Y x)) =
      2 * g.inner x ((LeviCivita (I := I) g).toFun V x
        ((LeviCivita (I := I) g).toFun Y x (Y x))) (V x)
    exact extDerivFun_inner_self (I := I) g hV x
      ((LeviCivita (I := I) g).toFun Y x (Y x))
  rw [hθ_x_LC]
  ring

/-- **Discharge of `hLeibniz` for `V = ∇f`.** The trace reduction
$$
  \Delta_g(g(\nabla f, \nabla f))(x) =
    2 g_x(\Delta_\nabla \nabla f, \nabla f) + 2 |\nabla \nabla f|^2_g(x)
$$
holds unconditionally for every smooth scalar `f` on a smooth boundaryless
Riemannian manifold. The proof combines:

1. The orthonormal-frame trace identity
   `sum_abstractHessian_smoothOrthoFrame_eq_laplacian`, which expresses
   `Δ_g(g(\nabla f, \nabla f))(x)` as the basis-naive sum
   `∑_i abstractHessian g (g(\nabla f, \nabla f)) x (B_i x) (B_i x)`.

2. The per-summand abstract-Hessian identity
   `abstractHessian_innerSelf_apply`, which expands each summand as
   `2 (g(LC P_i x (B_i x), \nabla f x) - g(LC \nabla f x (LC B_i x (B_i x)), \nabla f x))
   + 2 g(LC \nabla f x (B_i x), LC \nabla f x (B_i x))`,
   where `P_i = covApply LC B_i \nabla f`.

3. The definition of `localConnLap_vector` and `frobeniusSq_grad_vector`,
   matching the per-summand sum to the LHS components of the trace reduction. -/
theorem hLeibniz_discharge [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    IsLeibnizTraceAt (I := I) g
      (fun b => gradFun (I := I) g f b)
      (normGradSq_contMDiff (I := I) g hf) x := by
  classical
  change Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
    2 * g.inner x (connLaplacian_vector (I := I) g
                    (fun b => gradFun (I := I) g f b) x)
                   (gradFun (I := I) g f x) +
      2 * frobeniusSq_grad_vector (I := I) g
            (fun b => gradFun (I := I) g f b) x
  set V : Π b : M, TangentSpace I b := fun b => gradFun (I := I) g f b with hV_def
  set hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞
    (fun b : M => g.inner b (V b) (V b)) := normGradSq_contMDiff (I := I) g hf with hgVV_def
  have hV_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have h_trace := sum_abstractHessian_smoothOrthoFrame_eq_laplacian (I := I) g hgVV x
  rw [← h_trace]
  rw [show ∑ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g
          (fun b : M => g.inner b (V b) (V b)) x
          (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x i x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (2 * (g.inner x ((LeviCivita (I := I) g).toFun
                (covApply (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x i) V) x
                  (smoothOrthoFrame (I := I) g x i x)) (V x) -
              g.inner x ((LeviCivita (I := I) g).toFun V x
                ((LeviCivita (I := I) g).toFun
                  (smoothOrthoFrame (I := I) g x i) x
                  (smoothOrthoFrame (I := I) g x i x))) (V x)) +
          2 * g.inner x
            ((LeviCivita (I := I) g).toFun V x
              (smoothOrthoFrame (I := I) g x i x))
            ((LeviCivita (I := I) g).toFun V x
              (smoothOrthoFrame (I := I) g x i x))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact abstractHessian_innerSelf_apply (I := I) g hV_smooth
      (smoothOrthoFrame_smooth (I := I) g x i) hgVV x]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h_frob : ∑ i : Fin (Module.finrank ℝ E),
        g.inner x
            ((LeviCivita (I := I) g).toFun V x
              (smoothOrthoFrame (I := I) g x i x))
            ((LeviCivita (I := I) g).toFun V x
              (smoothOrthoFrame (I := I) g x i x)) =
      frobeniusSq_grad_vector (I := I) g V x := rfl
  rw [h_frob]
  have h_LCV : ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
              (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i) V) x
                (smoothOrthoFrame (I := I) g x i x)) (V x) -
            g.inner x ((LeviCivita (I := I) g).toFun V x
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x
                (smoothOrthoFrame (I := I) g x i x))) (V x)) =
      g.inner x (connLaplacian_vector (I := I) g V x) (V x) := by
    rw [show g.inner x (connLaplacian_vector (I := I) g V x) (V x) =
      g.inner x (∑ i : Fin (Module.finrank ℝ E),
        ((LeviCivita (I := I) g).toFun
            (covApply (LeviCivita (I := I) g)
              (smoothOrthoFrame (I := I) g x i) V) x
              (smoothOrthoFrame (I := I) g x i x) -
          (LeviCivita (I := I) g).toFun V x
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x
              (smoothOrthoFrame (I := I) g x i x)))) (V x) from rfl]
    rw [map_sum]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_sub]
    rw [ContinuousLinearMap.sub_apply]
  rw [h_LCV]

/-- **Bochner-Weitzenböck identity, with the orthonormal-frame Hessian-trace
identity absorbed.** Same as `bochner_pointwise_abstract`, but with the
trace-collapse pillar of `hLeibniz` (the Hessian-trace identity for
`b ↦ g(∇f, ∇f)(b)`) discharged via the orthonormal-frame trace identity.
The remaining content of `hLeibniz` is the *per-summand* abstract Hessian
identity, exposed as `hPerSummand_Leibniz`.

The reduction `hLeibniz` of `bochner_pointwise_abstract` factors as:
$$
  \Delta_g(g(\nabla f, \nabla f))(x)
    \overset{(*)}{=}
      \sum_i \mathrm{abstractHessian}\,g\,(g(\nabla f, \nabla f))\,x\,(B_i x)\,(B_i x)
    \overset{(\dagger)}{=}
      2 g_x(\Delta_\nabla \nabla f, \nabla f) + 2 |\nabla \nabla f|^2_g(x),
$$
with `(*)` discharged by `sum_abstractHessian_smoothOrthoFrame_eq_laplacian`
(and `B_i x = smoothOrthoFrame g x i x`), and `(†)` the per-summand identity
that the consumer supplies. -/
theorem bochner_pointwise_abstract_via_orthonormalTrace [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hPerSummand_Leibniz :
      ∑ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g
          (fun b : M => g.inner b
            (gradFun (I := I) g f b) (gradFun (I := I) g f b)) x
          (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x i x) =
        2 * g.inner x (connLaplacian_vector (I := I) g
                        (fun b => gradFun (I := I) g f b) x)
                       (gradFun (I := I) g f x) +
          2 * frobeniusSq_grad_vector (I := I) g
                (fun b => gradFun (I := I) g f b) x)
    (hInner : IsHeartOfBochnerInnerAt (I := I) g hf x) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x := by
  classical
  have hLeibniz : IsLeibnizTraceAt (I := I) g
      (fun b => gradFun (I := I) g f b)
      (normGradSq_contMDiff (I := I) g hf) x := by
    change Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      2 * g.inner x (connLaplacian_vector (I := I) g
                      (fun b => gradFun (I := I) g f b) x)
                     (gradFun (I := I) g f x) +
        2 * frobeniusSq_grad_vector (I := I) g
              (fun b => gradFun (I := I) g f b) x
    have h1 := sum_abstractHessian_smoothOrthoFrame_eq_laplacian (I := I) g
      (normGradSq_contMDiff (I := I) g hf) x
    rw [← h1]
    exact hPerSummand_Leibniz
  exact bochner_pointwise_abstract (I := I) g hf x hLeibniz hInner

/-- **Bochner-Weitzenböck identity, with `hLeibniz` discharged unconditionally.**
For a smooth scalar `f : M → ℝ` on a smooth boundaryless Riemannian manifold,
conditional only on the heart-of-Bochner inner-product reduction `hInner`,
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    g_x\bigl(\nabla(\Delta_g f)(x), \nabla f(x)\bigr)
    + \mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr)
    + |\nabla^2 f|_g^2(x).
$$

The trace reduction `hLeibniz` (B2 hypothesis) is discharged unconditionally
via `hLeibniz_discharge`. The remaining input `hInner` packages the algebraic
content of the heart-of-Bochner reduction (Hessian symmetry + curvature trace),
expressed at the inner-product level against any test vector `w ∈ T_x M`. -/
theorem bochner_pointwise_abstract_hLeibniz_discharged [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hInner : IsHeartOfBochnerInnerAt (I := I) g hf x) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_pointwise_abstract (I := I) g hf x
    (hLeibniz_discharge (I := I) g hf x) hInner

section HessianSkewVanishing

variable (g : SmoothRiemannianMetric I M)

/-- **Antisymmetric × symmetric vanishing for the Hessian on orthonormal frame.**
For a smooth scalar `f`, the sum
`∑_i abstractHessian g f x (B_i x) (∇_{Y x} B_i x)` vanishes when `B_i =
smoothOrthoFrame g x i` (orthonormal at `x`). -/
private theorem sum_abstractHessian_smoothOrthoFrame_cov_eq_zero
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (v : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
      abstractHessian (I := I) g f x
        (smoothOrthoFrame (I := I) g x i x)
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x v) = 0 := by
  classical
  have hRiesz : ∀ i : Fin (Module.finrank ℝ E),
      (LeviCivita (I := I) g).toFun
        (smoothOrthoFrame (I := I) g x i) x v =
      ∑ j : Fin (Module.finrank ℝ E),
        g.inner x ((LeviCivita (I := I) g).toFun
            (smoothOrthoFrame (I := I) g x i) x v)
          (smoothOrthoFrame (I := I) g x j x) •
          (smoothOrthoFrame (I := I) g x j x) := by
    intro i
    apply (vector_eq_iff_inner_eq (I := I) g x _ _).mpr
    intro w
    rw [show g.inner x (∑ j : Fin (Module.finrank ℝ E),
            g.inner x ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x j x) •
              (smoothOrthoFrame (I := I) g x j x)) w =
          ∑ j : Fin (Module.finrank ℝ E),
            g.inner x ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x j x) *
              g.inner x (smoothOrthoFrame (I := I) g x j x) w from by
      rw [map_sum, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [show ((g.inner x)
                (g.inner x ((LeviCivita (I := I) g).toFun
                  (smoothOrthoFrame (I := I) g x i) x v)
                  (smoothOrthoFrame (I := I) g x j x) •
                  smoothOrthoFrame (I := I) g x j x)) w =
            g.inner x ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x j x) •
              ((g.inner x) (smoothOrthoFrame (I := I) g x j x)) w from by
        rw [ContinuousLinearMap.map_smul]; rfl]
      rw [smul_eq_mul]]
    exact g_inner_eq_orthonormal_parseval_sum (I := I) g x
      ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v) w
      (fun j => smoothOrthoFrame (I := I) g x j x)
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)
  have h_expand : (∑ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g f x
          (smoothOrthoFrame (I := I) g x i x)
          ((LeviCivita (I := I) g).toFun
            (smoothOrthoFrame (I := I) g x i) x v)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x v)
            (smoothOrthoFrame (I := I) g x j x) *
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x j x) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    conv_lhs => rw [hRiesz i]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [show ((abstractHessian (I := I) g f x (smoothOrthoFrame (I := I) g x i x))
              (g.inner x ((LeviCivita (I := I) g).toFun
                  (smoothOrthoFrame (I := I) g x i) x v)
                (smoothOrthoFrame (I := I) g x j x) •
                smoothOrthoFrame (I := I) g x j x)) =
          g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x v)
            (smoothOrthoFrame (I := I) g x j x) •
            (abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x i x))
              (smoothOrthoFrame (I := I) g x j x) from
      ContinuousLinearMap.map_smul
        (abstractHessian (I := I) g f x (smoothOrthoFrame (I := I) g x i x))
        _ _]
    rw [smul_eq_mul]
  rw [h_expand]
  have h_skew_pair : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x j) x v)
        (smoothOrthoFrame (I := I) g x i x) =
      - g.inner x ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x v)
        (smoothOrthoFrame (I := I) g x j x) := by
    intro i j
    rw [smoothOrthoFrame_cov_skew (I := I) g x j i v]
    rw [g.symm x (smoothOrthoFrame (I := I) g x j x)
      ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x v)]
  have h_hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) (2 : ℕ∞) f x := hf.contMDiffAt.of_le (by
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1)
  have h_hess_symm : ∀ a b : TangentSpace I x,
      abstractHessian (I := I) g f x a b =
      abstractHessian (I := I) g f x b a := fun a b =>
    abstractHessian_symm (I := I) g h_hf_2 a b
  set S : ℝ := ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        g.inner x ((LeviCivita (I := I) g).toFun
            (smoothOrthoFrame (I := I) g x i) x v)
          (smoothOrthoFrame (I := I) g x j x) *
          abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x j x) with hS_def
  change S = 0
  have h_step1 : S =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x j) x v)
            (smoothOrthoFrame (I := I) g x i x) *
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x j x)
              (smoothOrthoFrame (I := I) g x i x) := by
    rw [hS_def, Finset.sum_comm]
  have h_step2 : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x j) x v)
            (smoothOrthoFrame (I := I) g x i x) *
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x j x)
              (smoothOrthoFrame (I := I) g x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (- g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x v)
            (smoothOrthoFrame (I := I) g x j x)) *
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x j x) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [h_skew_pair i j, h_hess_symm
      (smoothOrthoFrame (I := I) g x j x)
      (smoothOrthoFrame (I := I) g x i x)]
  have h_step3 : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (- g.inner x ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x v)
            (smoothOrthoFrame (I := I) g x j x)) *
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x j x)) = -S := by
    rw [hS_def]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (- g.inner x ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x j x)) *
              abstractHessian (I := I) g f x
                (smoothOrthoFrame (I := I) g x i x)
                (smoothOrthoFrame (I := I) g x j x)) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            -(g.inner x ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x v)
              (smoothOrthoFrame (I := I) g x j x) *
              abstractHessian (I := I) g f x
                (smoothOrthoFrame (I := I) g x i x)
                (smoothOrthoFrame (I := I) g x j x)) from by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      ring]
    simp_rw [← Finset.sum_neg_distrib]
  have h_S_eq_neg_S : S = -S := h_step1.trans (h_step2.trans h_step3)
  linarith

end HessianSkewVanishing

section LaplacianTraceOnNbhd

variable (g : SmoothRiemannianMetric I M)

/-- **Hessian-trace = Laplacian on `smoothOrthoFrameNbhd x`.** On the
orthonormal-frame neighborhood, the function
`b ↦ ∑_i abstractHessian g f b (B_i b) (B_i b)` agrees with `Δ_g f`. -/
private lemma sum_abstractHessian_smoothOrthoFrame_eventuallyEq_laplacian
    [I.Boundaryless]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g f b
          (smoothOrthoFrame (I := I) g x i b)
          (smoothOrthoFrame (I := I) g x i b)) =ᶠ[𝓝 x]
      (fun b : M => Δ_g (I := I) g hf b) := by
  classical
  have h_open : smoothOrthoFrameNbhd (I := I) (M := M) x ∈ 𝓝 x :=
    smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x
  filter_upwards [h_open] with b hb
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b
          (smoothOrthoFrame (I := I) g x i b)
          (smoothOrthoFrame (I := I) g x j b) =
        if i = j then 1 else 0 := fun i j =>
    smoothOrthoFrame_orthonormal (I := I) g x hb i j
  exact sum_abstractHessian_orthonormal_eq_laplacian (I := I) g hf b
    (fun i => smoothOrthoFrame (I := I) g x i b) hB_orth

end LaplacianTraceOnNbhd

private lemma heart_per_summand_swap [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (W : Π b : M, TangentSpace I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (i : Fin (Module.finrank ℝ E)) :
    g.inner x ((LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i)
          (fun b => gradFun (I := I) g f b)) x
          (smoothOrthoFrame (I := I) g x i x)) (W x) -
      g.inner x ((LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) (W x) =
      g.inner x ((LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) W
          (fun b => gradFun (I := I) g f b)) x
          (smoothOrthoFrame (I := I) g x i x))
        (smoothOrthoFrame (I := I) g x i x) -
      g.inner x ((LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x
        ((LeviCivita (I := I) g).toFun W x
          (smoothOrthoFrame (I := I) g x i x)))
        (smoothOrthoFrame (I := I) g x i x) := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  set B : Π b : M, TangentSpace I b := smoothOrthoFrame (I := I) g x i with hB_def
  set Gf : Π b : M, TangentSpace I b := fun b => gradFun (I := I) g f b with hGf_def
  set Q : Π b : M, TangentSpace I b := covApply cov B Gf with hQ_def
  set P : Π b : M, TangentSpace I b := covApply cov W Gf with hP_def
  have hB_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hGf_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Gf) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB_at : MDiffAt (T% B) x := (hB_smooth x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hGf_at : MDiffAt (T% Gf) x := (hGf_smooth x).mdifferentiableAt (by simp)
  have hQ_at : MDiffAt (T% Q) x :=
    covApply_mdifferentiableAt_local (cov := cov) hB_at
      (by simpa using hGf_smooth)
  have hP_at : MDiffAt (T% P) x :=
    covApply_mdifferentiableAt_local (cov := cov) hW_at
      (by simpa using hGf_smooth)
  have hmc_QW :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hQ_at hW_at (B x)
  have hmc_PB :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hP_at hB_at (B x)
  have hHess_section : (fun b : M => g.inner b (Q b) (W b)) =
      (fun b : M => g.inner b (P b) (B b)) := by
    have h := inner_cov_gradFun_symm_globally (I := I) g hf
      (X := B) (Y := W) hB_smooth hW
    funext b
    have hQb : Q b = cov.toFun Gf b (B b) := rfl
    have hPb : P b = cov.toFun Gf b (W b) := rfl
    rw [hQb, hPb]
    exact congrFun h b
  have h_mfderiv_eq :
      (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (Q b) (W b)) x) (B x) =
        (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (P b) (B b)) x) (B x) := by
    rw [hHess_section]
    rfl
  have h_combined :
      g.inner x (cov.toFun Q x (B x)) (W x) + g.inner x (Q x) (cov.toFun W x (B x)) =
        g.inner x (cov.toFun P x (B x)) (B x) +
          g.inner x (P x) (cov.toFun B x (B x)) := by
    rw [← hmc_QW, h_mfderiv_eq, hmc_PB]
  have hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) (2 : ℕ∞) f x := hf.contMDiffAt.of_le (by
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1)
  have hQx_inner : g.inner x (Q x) (cov.toFun W x (B x)) =
      g.inner x (cov.toFun Gf x (cov.toFun W x (B x))) (B x) := by
    have hQx_eq : Q x = cov.toFun Gf x (B x) := rfl
    rw [hQx_eq]
    set v : TangentSpace I x := cov.toFun W x (B x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    have h_sym := inner_cov_gradFun_symm (I := I) g hf
      (X := B) (Y := Xv) (x := x) hB_smooth hXv_smooth
    rw [show v = Xv x from hXv_eq.symm]
    exact h_sym
  have hPx_inner : g.inner x (P x) (cov.toFun B x (B x)) =
      g.inner x (cov.toFun Gf x (cov.toFun B x (B x))) (W x) := by
    have hPx_eq : P x = cov.toFun Gf x (W x) := rfl
    rw [hPx_eq]
    set v : TangentSpace I x := cov.toFun B x (B x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    have h_sym := inner_cov_gradFun_symm (I := I) g hf
      (X := W) (Y := Xv) (x := x) hW hXv_smooth
    rw [show v = Xv x from hXv_eq.symm]
    exact h_sym
  rw [hQx_inner, hPx_inner] at h_combined
  linarith

private lemma heart_per_summand_riemann_form [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (_hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (W : Π b : M, TangentSpace I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (i : Fin (Module.finrank ℝ E)) :
    g.inner x ((LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g) W
          (fun b => gradFun (I := I) g f b)) x
          (smoothOrthoFrame (I := I) g x i x))
        (smoothOrthoFrame (I := I) g x i x) -
      g.inner x ((LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x
        ((LeviCivita (I := I) g).toFun W x
          (smoothOrthoFrame (I := I) g x i x)))
        (smoothOrthoFrame (I := I) g x i x) =
      g.inner x (riemannSec (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x i) W
                  (fun b => gradFun (I := I) g f b) x)
        (smoothOrthoFrame (I := I) g x i x) +
      g.inner x ((LeviCivita (I := I) g).toFun
                  (covApply (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i)
                    (fun b => gradFun (I := I) g f b)) x (W x))
        (smoothOrthoFrame (I := I) g x i x) -
      g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x
                  ((LeviCivita (I := I) g).toFun
                    (smoothOrthoFrame (I := I) g x i) x (W x)))
        (smoothOrthoFrame (I := I) g x i x) := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  set B : Π b : M, TangentSpace I b := smoothOrthoFrame (I := I) g x i with hB_def
  set Gf : Π b : M, TangentSpace I b := fun b => gradFun (I := I) g f b with hGf_def
  have hB_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hB_at : MDiffAt (T% B) x := (hB_smooth x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hriem :=
    LeviCivita_riemannSec_torsionFree_form (I := I) g
      (X := B) (Y := W) (Z := Gf) (x := x) hB_at hW_at
  have hriem' :
      riemannSec cov B W Gf x =
        cov.toFun (covApply cov W Gf) x (B x) -
          cov.toFun (covApply cov B Gf) x (W x) -
          (cov.toFun Gf x (cov.toFun W x (B x)) -
            cov.toFun Gf x (cov.toFun B x (W x))) := by
    change riemannSec (LeviCivita (I := I) g) B W Gf x =
      (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) W Gf) x (B x) -
        (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) B Gf) x (W x) -
        ((LeviCivita (I := I) g).toFun Gf x ((LeviCivita (I := I) g).toFun W x (B x)) -
          (LeviCivita (I := I) g).toFun Gf x ((LeviCivita (I := I) g).toFun B x (W x)))
    exact hriem
  have hP_split :
      cov.toFun (covApply cov W Gf) x (B x) =
        riemannSec cov B W Gf x +
          cov.toFun (covApply cov B Gf) x (W x) +
          (cov.toFun Gf x (cov.toFun W x (B x)) -
            cov.toFun Gf x (cov.toFun B x (W x))) := by
    rw [hriem']; abel
  have h_inner_split :
      g.inner x (cov.toFun (covApply cov W Gf) x (B x)) (B x) =
        g.inner x (riemannSec cov B W Gf x) (B x) +
          g.inner x (cov.toFun (covApply cov B Gf) x (W x)) (B x) +
          g.inner x (cov.toFun Gf x (cov.toFun W x (B x))) (B x) -
          g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) := by
    rw [hP_split]
    rw [map_add, ContinuousLinearMap.add_apply]
    rw [map_add, ContinuousLinearMap.add_apply]
    rw [map_sub, ContinuousLinearMap.sub_apply]
    ring
  linarith

private lemma heart_per_summand_assembled [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (W : Π b : M, TangentSpace I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (i : Fin (Module.finrank ℝ E)) :
    g.inner x ((LeviCivita (I := I) g).toFun
        (covApply (LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i)
          (fun b => gradFun (I := I) g f b)) x
          (smoothOrthoFrame (I := I) g x i x)) (W x) -
      g.inner x ((LeviCivita (I := I) g).toFun
        (fun b => gradFun (I := I) g f b) x
        ((LeviCivita (I := I) g).toFun
          (smoothOrthoFrame (I := I) g x i) x
          (smoothOrthoFrame (I := I) g x i x))) (W x) =
      g.inner x (riemannSec (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x i) W
                  (fun b => gradFun (I := I) g f b) x)
        (smoothOrthoFrame (I := I) g x i x) +
      extDerivFun (I := I) (fun b : M =>
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x (W x) -
      2 * abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x (W x)) := by
  classical
  set cov := LeviCivita (I := I) g with hcov
  set B : Π b : M, TangentSpace I b := smoothOrthoFrame (I := I) g x i with hB_def
  set Gf : Π b : M, TangentSpace I b := fun b => gradFun (I := I) g f b with hGf_def
  set Q : Π b : M, TangentSpace I b := covApply cov B Gf with hQ_def
  have h_swap := heart_per_summand_swap (I := I) g hf x W hW i
  have h_riem := heart_per_summand_riemann_form (I := I) g hf x W hW i
  have hB_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hGf_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Gf) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB_at : MDiffAt (T% B) x := (hB_smooth x).mdifferentiableAt (by simp)
  have hQ_at : MDiffAt (T% Q) x :=
    covApply_mdifferentiableAt_local (cov := cov) hB_at
      (by simpa using hGf_smooth)
  have hmc_QB :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hQ_at hB_at (W x)
  have h_QB_section : (fun b : M => g.inner b (Q b) (B b)) =
      (fun b : M => abstractHessian (I := I) g f b (B b) (B b)) := by
    funext b
    have hQb : Q b = cov.toFun Gf b (B b) := rfl
    rw [hQb]
    exact inner_cov_gradFun_eq_abstractHessian (I := I) g hf
      (X := B) (Y := B) (x := b) hB_smooth hB_smooth
  rw [show (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (Q b) (B b)) x) (W x) =
      (mfderiv I 𝓘(ℝ) (fun b : M =>
          abstractHessian (I := I) g f b (B b) (B b)) x) (W x) from by
    rw [h_QB_section]; rfl] at hmc_QB
  have h_QcovBW : g.inner x (Q x) (cov.toFun B x (W x)) =
      g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) := by
    have hQx_eq : Q x = cov.toFun Gf x (B x) := rfl
    rw [hQx_eq]
    set v : TangentSpace I x := cov.toFun B x (W x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    have h_sym := inner_cov_gradFun_symm (I := I) g hf
      (X := B) (Y := Xv) (x := x) hB_smooth hXv_smooth
    rw [show v = Xv x from hXv_eq.symm]
    exact h_sym
  have h_LCQW_B :
      g.inner x (cov.toFun Q x (W x)) (B x) =
        extDerivFun (I := I) (fun b : M =>
            abstractHessian (I := I) g f b (B b) (B b)) x (W x) -
          g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) := by
    have hext : extDerivFun (I := I) (fun b : M =>
            abstractHessian (I := I) g f b (B b) (B b)) x (W x) =
        (mfderiv I 𝓘(ℝ, ℝ) (fun b : M =>
            abstractHessian (I := I) g f b (B b) (B b)) x) (W x) := rfl
    rw [hext]
    rw [show (mfderiv I 𝓘(ℝ, ℝ) (fun b : M =>
            abstractHessian (I := I) g f b (B b) (B b)) x) (W x) =
        g.inner x (cov.toFun Q x (W x)) (B x) +
          g.inner x (Q x) (cov.toFun B x (W x)) from hmc_QB]
    rw [h_QcovBW]
    ring
  have h_Hess_BcovBW :
      g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) =
        abstractHessian (I := I) g f x (B x) (cov.toFun B x (W x)) := by
    set v : TangentSpace I x := cov.toFun B x (W x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    rw [show v = Xv x from hXv_eq.symm]
    rw [inner_cov_gradFun_eq_abstractHessian (I := I) g hf
        (X := Xv) (Y := B) (x := x) hXv_smooth hB_smooth]
    exact (abstractHessian_symm (I := I) g (hf.contMDiffAt.of_le (by
      have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      simpa using h1)) (Xv x) (B x))
  rw [h_Hess_BcovBW] at h_LCQW_B
  rw [h_swap, h_riem, h_LCQW_B, h_Hess_BcovBW]
  ring

/-- **Heart-of-Bochner inner-product reduction, unconditional discharge.**
For any smooth scalar `f : M → ℝ` on a smooth boundaryless Riemannian manifold,
the predicate `IsHeartOfBochnerInnerAt g hf x` holds at every point `x`, with no
additional algebraic input. -/
theorem hInner_discharge [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    IsHeartOfBochnerInnerAt (I := I) g hf x := by
  classical
  intro w
  set W : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hW_def
  have hW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) :=
    smoothExtensionTangent_contMDiff x w
  have hW_eq : W x = w := smoothExtensionTangent_eq x w
  rw [show w = W x from hW_eq.symm]
  rw [connLaplacian_grad_inner (I := I) g hf hW_smooth x]
  rw [show ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x ((LeviCivita (I := I) g).toFun
                    (covApply (LeviCivita (I := I) g)
                      (smoothOrthoFrame (I := I) g x i)
                      (fun b => gradFun (I := I) g f b)) x
                      (smoothOrthoFrame (I := I) g x i x)) (W x) -
          g.inner x ((LeviCivita (I := I) g).toFun
                      (fun b => gradFun (I := I) g f b) x
                      ((LeviCivita (I := I) g).toFun
                        (smoothOrthoFrame (I := I) g x i) x
                        (smoothOrthoFrame (I := I) g x i x))) (W x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x (riemannSec (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x i) W
                  (fun b => gradFun (I := I) g f b) x)
        (smoothOrthoFrame (I := I) g x i x) +
      extDerivFun (I := I) (fun b : M =>
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x (W x) -
      2 * abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x (W x))) from by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact heart_per_summand_assembled (I := I) g hf x W hW_smooth i]
  rw [show ∑ i : Fin (Module.finrank ℝ E),
        (g.inner x (riemannSec (LeviCivita (I := I) g)
                  (smoothOrthoFrame (I := I) g x i) W
                  (fun b => gradFun (I := I) g f b) x)
        (smoothOrthoFrame (I := I) g x i x) +
      extDerivFun (I := I) (fun b : M =>
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x (W x) -
      2 * abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x (W x))) =
      (∑ i : Fin (Module.finrank ℝ E),
          g.inner x (riemannSec (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i) W
                    (fun b => gradFun (I := I) g f b) x)
          (smoothOrthoFrame (I := I) g x i x)) +
      (∑ i : Fin (Module.finrank ℝ E),
          extDerivFun (I := I) (fun b : M =>
                    abstractHessian (I := I) g f b
                      (smoothOrthoFrame (I := I) g x i b)
                      (smoothOrthoFrame (I := I) g x i b)) x (W x)) -
      2 * ∑ i : Fin (Module.finrank ℝ E),
            abstractHessian (I := I) g f x
              (smoothOrthoFrame (I := I) g x i x)
              ((LeviCivita (I := I) g).toFun
                (smoothOrthoFrame (I := I) g x i) x (W x)) from by
    rw [Finset.mul_sum]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
          (g.inner x (riemannSec (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i) W
                    (fun b => gradFun (I := I) g f b) x)
            (smoothOrthoFrame (I := I) g x i x) +
            extDerivFun (I := I) (fun b : M =>
                      abstractHessian (I := I) g f b
                        (smoothOrthoFrame (I := I) g x i b)
                        (smoothOrthoFrame (I := I) g x i b)) x (W x) -
            2 * abstractHessian (I := I) g f x
                  (smoothOrthoFrame (I := I) g x i x)
                  ((LeviCivita (I := I) g).toFun
                    (smoothOrthoFrame (I := I) g x i) x (W x)))) =
        ∑ i : Fin (Module.finrank ℝ E),
          ((g.inner x (riemannSec (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i) W
                    (fun b => gradFun (I := I) g f b) x)
            (smoothOrthoFrame (I := I) g x i x) +
            extDerivFun (I := I) (fun b : M =>
                      abstractHessian (I := I) g f b
                        (smoothOrthoFrame (I := I) g x i b)
                        (smoothOrthoFrame (I := I) g x i b)) x (W x)) -
            2 * abstractHessian (I := I) g f x
                  (smoothOrthoFrame (I := I) g x i x)
                  ((LeviCivita (I := I) g).toFun
                    (smoothOrthoFrame (I := I) g x i) x (W x))) from by
      refine Finset.sum_congr rfl ?_
      intro i _
      ring]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib]]
  have h_curv_sum_eq :
      (∑ i : Fin (Module.finrank ℝ E),
          g.inner x (riemannSec (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i) W
                    (fun b => gradFun (I := I) g f b) x)
          (smoothOrthoFrame (I := I) g x i x)) =
      ricciTensor (I := I) g x (gradFun (I := I) g f x) w := by
    have h_per_summand : ∀ i : Fin (Module.finrank ℝ E),
        g.inner x (riemannSec (LeviCivita (I := I) g)
                    (smoothOrthoFrame (I := I) g x i) W
                    (fun b => gradFun (I := I) g f b) x)
          (smoothOrthoFrame (I := I) g x i x) =
        g.inner x (riemannOp (LeviCivita (I := I) g) x
            (smoothOrthoFrame (I := I) g x i x) w
            (gradFun (I := I) g f x))
          (smoothOrthoFrame (I := I) g x i x) := by
      intro i
      have h_riemOp :=
        riemannOp_apply_smooth (cov := LeviCivita (I := I) g)
          (X := smoothOrthoFrame (I := I) g x i) (Y := W)
          (Z := fun b => gradFun (I := I) g f b) (x := x)
          (smoothOrthoFrame_smooth (I := I) g x i) hW_smooth
          (gradFun_contMDiff_total_section (I := I) g hf)
      rw [show (smoothOrthoFrame (I := I) g x i x) =
              (smoothOrthoFrame (I := I) g x i) x from rfl,
          show w = W x from hW_eq.symm,
          show gradFun (I := I) g f x =
              (fun b => gradFun (I := I) g f b) x from rfl,
          h_riemOp]
    rw [Finset.sum_congr rfl (fun i _ => h_per_summand i)]
    exact heart_curvature_orthonormal_sum_eq_ricci (I := I) g hf x w
  rw [h_curv_sum_eq]
  have h_hess_sum_eventuallyEq :=
    sum_abstractHessian_smoothOrthoFrame_eventuallyEq_laplacian (I := I) g hf x
  have h_extDerivFun_sum_eq :
      (∑ i : Fin (Module.finrank ℝ E),
          extDerivFun (I := I) (fun b : M =>
                    abstractHessian (I := I) g f b
                      (smoothOrthoFrame (I := I) g x i b)
                      (smoothOrthoFrame (I := I) g x i b)) x (W x)) =
      extDerivFun (I := I) (Δ_g (I := I) g hf) x w := by
    have hB_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (smoothOrthoFrame (I := I) g x i)) :=
      fun i => smoothOrthoFrame_smooth (I := I) g x i
    have hGf_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b => gradFun (I := I) g f b)) :=
      gradFun_contMDiff_total_section (I := I) g hf
    have h_each_diff : ∀ i : Fin (Module.finrank ℝ E),
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M =>
          abstractHessian (I := I) g f b
            (smoothOrthoFrame (I := I) g x i b)
            (smoothOrthoFrame (I := I) g x i b)) x := by
      intro i
      have h_conv : (fun b : M =>
            abstractHessian (I := I) g f b
              (smoothOrthoFrame (I := I) g x i b)
              (smoothOrthoFrame (I := I) g x i b)) =
          (fun b : M => g.inner b (covApply (LeviCivita (I := I) g)
            (smoothOrthoFrame (I := I) g x i)
            (fun b' => gradFun (I := I) g f b') b)
          (smoothOrthoFrame (I := I) g x i b)) := by
        funext b
        exact (inner_cov_gradFun_eq_abstractHessian (I := I) g hf
          (X := smoothOrthoFrame (I := I) g x i)
          (Y := smoothOrthoFrame (I := I) g x i) (x := b)
          (hB_smooth i) (hB_smooth i)).symm
      rw [h_conv]
      have hQ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (covApply (LeviCivita (I := I) g)
            (smoothOrthoFrame (I := I) g x i)
            (fun b' => gradFun (I := I) g f b'))) x :=
        covApply_mdifferentiableAt_local
          (cov := LeviCivita (I := I) g)
          ((hB_smooth i x).mdifferentiableAt (by simp))
          (by simpa using hGf_smooth)
      have hg_contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
            b (g.inner b)) := g.contMDiff
      have hg_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
          (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
            (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
            b (g.inner b)) x :=
        (hg_contMDiff x).mdifferentiableAt (by simp)
      have hB_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (smoothOrthoFrame (I := I) g x i)) x :=
        ((hB_smooth i) x).mdifferentiableAt (by simp)
      have happ : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
          (fun m : M => (⟨m,
              g.inner m (covApply (LeviCivita (I := I) g)
                (smoothOrthoFrame (I := I) g x i)
                (fun b' => gradFun (I := I) g f b') m)
                (smoothOrthoFrame (I := I) g x i m)⟩ :
                TotalSpace ℝ (Bundle.Trivial M ℝ))) x :=
        MDifferentiableAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
          (b := id)
          hg_at hQ_at hB_at
      rw [mdifferentiableAt_totalSpace] at happ
      exact happ.2
    have h_sum_mfderiv :
        extDerivFun (I := I) (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x (W x) =
          ∑ i : Fin (Module.finrank ℝ E),
            extDerivFun (I := I) (fun b : M =>
                    abstractHessian (I := I) g f b
                      (smoothOrthoFrame (I := I) g x i b)
                      (smoothOrthoFrame (I := I) g x i b)) x (W x) := by
      induction (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        using Finset.induction_on with
      | empty => simp
      | @insert a s ha IH =>
        rw [Finset.sum_insert ha]
        have hsplit : (fun b : M => ∑ i ∈ insert a s,
              abstractHessian (I := I) g f b
                (smoothOrthoFrame (I := I) g x i b)
                (smoothOrthoFrame (I := I) g x i b)) =
            (fun b : M =>
              abstractHessian (I := I) g f b
                (smoothOrthoFrame (I := I) g x a b)
                (smoothOrthoFrame (I := I) g x a b) +
              ∑ i ∈ s,
                abstractHessian (I := I) g f b
                  (smoothOrthoFrame (I := I) g x i b)
                  (smoothOrthoFrame (I := I) g x i b)) := by
          funext b
          rw [Finset.sum_insert ha]
        rw [hsplit]
        have h_sum_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => ∑ i ∈ s,
              abstractHessian (I := I) g f b
                (smoothOrthoFrame (I := I) g x i b)
                (smoothOrthoFrame (I := I) g x i b)) x := by
          have h := MDifferentiableAt.sum (z := x) (t := s)
            (f := fun i b => abstractHessian (I := I) g f b
              (smoothOrthoFrame (I := I) g x i b)
              (smoothOrthoFrame (I := I) g x i b))
            (fun i _ => h_each_diff i)
          have heq : (∑ i ∈ s, fun b : M => abstractHessian (I := I) g f b
                  (smoothOrthoFrame (I := I) g x i b)
                  (smoothOrthoFrame (I := I) g x i b)) =
              (fun b : M => ∑ i ∈ s,
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) := by
            funext b
            simp [Finset.sum_apply]
          rw [heq] at h
          exact h
        rw [show (fun b : M =>
              abstractHessian (I := I) g f b
                (smoothOrthoFrame (I := I) g x a b)
                (smoothOrthoFrame (I := I) g x a b) +
              ∑ i ∈ s,
                abstractHessian (I := I) g f b
                  (smoothOrthoFrame (I := I) g x i b)
                  (smoothOrthoFrame (I := I) g x i b)) =
            ((fun b : M => abstractHessian (I := I) g f b
                  (smoothOrthoFrame (I := I) g x a b)
                  (smoothOrthoFrame (I := I) g x a b)) +
              (fun b : M => ∑ i ∈ s,
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b))) from rfl]
        rw [extDerivFun_add (h_each_diff a) h_sum_diff,
            ContinuousLinearMap.add_apply, IH]
    rw [← h_sum_mfderiv]
    have h_extDerivFun_eq :
        extDerivFun (I := I) (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x =
        extDerivFun (I := I) (Δ_g (I := I) g hf) x := by
      change (NormedSpace.fromTangentSpace _).toContinuousLinearMap ∘L
            (mfderiv I 𝓘(ℝ, ℝ) (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
                      abstractHessian (I := I) g f b
                        (smoothOrthoFrame (I := I) g x i b)
                        (smoothOrthoFrame (I := I) g x i b)) x) =
            (NormedSpace.fromTangentSpace _).toContinuousLinearMap ∘L
            (mfderiv I 𝓘(ℝ, ℝ) (Δ_g (I := I) g hf) x)
      have h_mf_eq : (mfderiv I 𝓘(ℝ, ℝ) (fun b : M =>
                  ∑ i : Fin (Module.finrank ℝ E),
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x) =
          mfderiv I 𝓘(ℝ, ℝ) (Δ_g (I := I) g hf) x :=
        Filter.EventuallyEq.mfderiv_eq h_hess_sum_eventuallyEq
      have h_base_eq : (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x =
          Δ_g (I := I) g hf x := by
        exact h_hess_sum_eventuallyEq.self_of_nhds
      rw [h_mf_eq]
      congr 1
    rw [h_extDerivFun_eq, hW_eq]
  rw [h_extDerivFun_sum_eq]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x (W x))) = 0 from by
    rw [hW_eq]
    exact sum_abstractHessian_smoothOrthoFrame_cov_eq_zero (I := I) g hf x w]
  rw [show extDerivFun (I := I) (Δ_g (I := I) g hf) x w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w from
    (gradFun_metricDual_extDerivFun (I := I) g (Δ_g (I := I) g hf) x w).symm]
  rw [show ricciTensor (I := I) g x (gradFun (I := I) g f x) w =
        g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w from
    (inner_ricciSharp (I := I) g x (gradFun (I := I) g f x) w).symm]
  rw [hW_eq]
  ring

/-- **Truly unconditional pointwise Bochner-Weitzenböck identity.**
For any smooth scalar `f : M → ℝ` on a smooth boundaryless Riemannian manifold,
the Bochner-Weitzenböck identity holds pointwise at every `x : M`:
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    g_x\bigl(\nabla(\Delta_g f)(x), \nabla f(x)\bigr)
    + \mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr)
    + |\nabla^2 f|_g^2(x).
$$
Both algebraic input hypotheses (`hLeibniz` and `hInner`) are discharged
unconditionally via `hLeibniz_discharge` and `hInner_discharge`. -/
theorem bochner_pointwise_abstract_unconditional [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    (1 / 2 : ℝ) * Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x)
        (gradFun (I := I) g f x) +
        ricciTensor (I := I) g x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) +
        frobeniusSq_grad_vector (I := I) g
          (fun b => gradFun (I := I) g f b) x :=
  bochner_pointwise_abstract (I := I) g hf x
    (hLeibniz_discharge (I := I) g hf x)
    (hInner_discharge (I := I) g hf x)

end Connection
end Integral
end DifferentialGeometry
