import DifferentialGeometry.Integral.Connection.ConnectionLaplacian
import DifferentialGeometry.Integral.Connection.ChartBridge.Laplacian
import DifferentialGeometry.Integral.Connection.ChartBridge.HessFrobenius
import DifferentialGeometry.Geometry.NormGradSq

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

/-! ## B1 — Inner-product Leibniz identity

For the Levi-Civita connection of `g`, the directional derivative of the scalar
function `b ↦ g(V, W)(b)` is the sum of two inner-product terms involving the
covariant derivatives of `V` and `W`. This is the chart-free statement of
metric-compatibility, exposed at the level of `mfderiv`.

The identity is the cornerstone for trace-based identities on `g`-pairings; in
particular, the diagonal case `W = V` is the input to B2 below. -/

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

/-! ## B2 — Trace formula for `Δ_g(g(V, V))` (conditional)

Applying B1 twice (and the metric symmetry) to the scalar `b ↦ g(V, V)(b)` and
tracing against the smooth orthonormal frame at `x` produces the identity
$$
  \Delta_g\bigl(g(V, V)\bigr)(x) =
    2\,g_x\bigl((\Delta_\nabla V)(x), V(x)\bigr) + 2\,|\nabla V|^2_g(x).
$$
The trace reduction itself (the chart-or-frame computation collapsing the second
derivative trace into the Laplacian formula) is exposed as the hypothesis
`hLeibniz`. The downstream consumer supplies it via the chart-coordinate Hessian
formula or by direct frame-trace computation.

We re-export the conditional version `connLaplacian_inner_self_of_trace`
(`ConnectionLaplacian.lean`) under the name expected by the Bochner derivation. -/

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
  -- Re-export of `connLaplacian_inner_self_of_trace` modulo `connLaplacian_function = Δ_g`.
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

/-! ## B3 — Connection-Laplacian-gradient commutator (conditional)

The vector identity
$$
  \Delta_\nabla(\nabla f)(x) = \nabla(\Delta_g f)(x) + \mathrm{Ric}^\sharp(\nabla f)(x)
$$
is the heart-of-Bochner reduction. Its proof at the inner-product level combines:

1. **Hessian symmetry** (`inner_cov_gradFun_symm_globally`): `g(∇_X(∇f), Y)` is
   symmetric in `(X, Y)` at every point.
2. **Curvature trace** (`heart_of_bochner_curvature_term`): the metric pairing of
   the Riemann curvature on `(B, w)` against `B` re-orients to the Ricci-tensor
   contribution.
3. **Hessian-trace-equals-Laplacian**: the trace of the abstract Hessian against
   an orthonormal frame is the Laplace-Beltrami operator.

We re-export the conditional version `connLaplacian_grad_eq_grad_laplacian_plus_ricciSharp_of_inner`
(`ConnectionLaplacian.lean`) under the Bochner-derivation name. -/

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

/-! ## B4 — Bochner main identity (conditional)

Combining B2 (with `V = ∇f`) and B3 produces the Bochner-Weitzenböck identity
$$
  \tfrac{1}{2}\,\Delta_g\bigl(g(\nabla f, \nabla f)\bigr)(x) =
    g_x\bigl(\nabla(\Delta_g f)(x), \nabla f(x)\bigr)
    + \mathrm{Ric}_x\bigl(\nabla f(x), \nabla f(x)\bigr)
    + |\nabla^2 f|_g^2(x).
$$
The Frobenius norm of the Hessian, `|\nabla^2 f|_g^2(x) = |\nabla(\nabla f)|_g^2(x)`,
is the connection-Laplacian Frobenius norm of `∇f`,
`frobeniusSq_grad_vector g (gradFun g f) x`.

The identity below is conditional on **both** `hLeibniz` (the trace reduction in
B2) and `hInner` (the heart-of-Bochner reduction in B3). The downstream consumer
(typically a chart-Christoffel calculation or a Realization bridge) supplies both
hypotheses; the orchestrator combines them via the algebraic Bochner identity. -/

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
  -- Step 1: apply B2 with V = grad f.
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g f b)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB2 :=
    laplacian_inner_self_half (I := I) g h_grad_smooth hgVV x hLeibniz
  -- hB2 : (1/2) * Δ_g g hgVV x =
  --   g.inner x (Δ_∇ ∇f) (∇f x) + |∇∇f|²_g(x)
  rw [hB2]
  -- Step 2: identify g.inner x (Δ_∇ ∇f) (∇f x) using B3 (inner form).
  have hB3 :=
    laplacian_grad_inner_eq_grad_laplacian_plus_ricci (I := I) g hf x hInner
      (gradFun (I := I) g f x)
  -- hB3 : g.inner x (Δ_∇ ∇f) (∇f x) =
  --   g.inner x (∇(Δ_g f)) (∇f x) + Ric (∇f x) (∇f x)
  rw [hB3]

/-! ## Unconditional Bochner identity given heart-of-Bochner as input

The unconditional fallback packages the heart-of-Bochner identity as a hypothesis
in **vector form** (a single equation between two tangent vectors at `x`). The
trace reduction `hLeibniz` is supplied by the consumer; the heart-of-Bochner
identity replaces the inner-product reduction `hInner` by its vector content,
which is logically equivalent (Riesz uniqueness) but more directly used by some
consumers. -/

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
  -- Step 1: apply B2 with V = grad f.
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => gradFun (I := I) g f b)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB2 :=
    laplacian_inner_self_half (I := I) g h_grad_smooth hgVV x hLeibniz
  rw [hB2]
  -- Step 2: substitute the vector heart-of-Bochner identity into the inner
  -- product `g.inner x (Δ_∇ ∇f) (∇f x)`.
  rw [hHeart]
  -- Step 3: distribute g.inner x over the sum and use the Ricci-sharp inner
  -- product identity.
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

/-! ## Smoothness witness for `b ↦ g(∇f, ∇f)(b)`

The Laplacian `Δ_g` of `g(∇f, ∇f)` requires a smoothness witness for the inner
product. The lemma `normGradSq_contMDiff` re-exports `normGradSqFun_contMDiff`
under a name natural to the Bochner context. -/

/-- **Smoothness of `b ↦ g(∇f, ∇f)(b)`.** For a smooth scalar `f`, the inner
product of the gradient with itself is `C^∞` on `M`. -/
theorem normGradSq_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => g.inner b (gradFun (I := I) g f b)
        (gradFun (I := I) g f b)) := by
  -- `normGradSqFun_contMDiff` provides the same smoothness statement under a
  -- different name; we adapt the function shape via `congr` (the two sides agree
  -- pointwise by definition of `normGradSqFun`).
  exact normGradSqFun_contMDiff (I := I) g hf

/-! ## Convenience packaging: B4 with the smoothness witness inlined

For downstream consumers, we expose B4 with the smoothness witness for
`b ↦ g(∇f, ∇f)(b)` produced inline from `hf`. This eliminates the need to
manually construct the smoothness witness at the callsite. -/

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

/-! ## Heart-of-Bochner identity discharged via the chart-orthonormality predicate

The conditional Bochner-Weitzenböck identity above hinges on two algebraic
reductions: the trace reduction `hLeibniz` (B2) and the heart-of-Bochner
inner-product reduction `hInner` (B3). Both reductions express the metric
trace at the point `x` of certain bilinear forms in tangent space —
specifically of the abstract Hessian of the inner product `b ↦ g(V, V)(b)`
(for B2) and of the abstract Hessian of the scalar `f` itself (for B3).

The trace-bridge from the metric `chartHessTrace` formula to a basis-naive
trace against the smooth orthonormal frame `smoothOrthoFrame g x` requires
identifying the smooth orthonormal frame at `x` with the chart-basis frame at
`x`. This identification holds precisely when the chart at `x` is `g`-orthonormal
at `x` — i.e. when the inverse Gram matrix at `x` is the identity. Equivalent
geometric conditions: the chart-frame at `x` is already `g_x`-orthonormal, so
the Gram-Schmidt step `chartFrameNorm` is the identity at `x`.

We expose a clean predicate `IsChartOrthonormalAt g x` packaging this single
geometric condition, and then state Bochner-flavoured packaging theorems that
take this predicate as their only remaining hypothesis. Downstream consumers
either:

* discharge `IsChartOrthonormalAt g x` explicitly by inspecting their chart
  (e.g. when working with normal coordinates centred at `x`); or

* extend the chart frame using a downstream pointwise basis-change argument.

The full unconditional Bochner-Weitzenböck identity (with `IsChartOrthonormalAt`
discharged automatically) requires further infrastructure. The remaining gap is
purely linear-algebraic: a basis-change identity expressing the metric trace
`∑ ij G^{ij}(x, x) H_{ij}(x, x)` of an arbitrary symmetric bilinear form `H`
as the basis-naive trace `∑ i H(B_i, B_i)` against any `g_x`-orthonormal basis
`(B_i)` at `x`. This is the standard "trace-via-orthonormal-basis" identity
from finite-dimensional inner-product space theory; once added to Mathlib (or
established locally via the change-of-basis matrix `B^T G B = I` and its
consequence `∑ i (B_i)^k (B_i)^l = G^{kl}`), the full unconditional Bochner
identity follows by composing with the present orthonormal-frame packaging.
-/

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

/-! ### Bochner identity from `BochnerReductionAt`

Combining the two packaged hypotheses produces the Bochner-Weitzenböck identity
verbatim. This is the "single-input" form: a downstream consumer that has
established both reductions (e.g. via chart orthonormality, normal coordinates,
or any other route) can invoke the identity by supplying a single
`BochnerReductionAt` value. -/

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

/-! ## Discharge of `IsHeartOfBochnerInnerAt` from chart orthonormality at `x`

The heart-of-Bochner inner-product reduction `hInner` (B3 hypothesis) follows
from the unconditional engine identities `inner_cov_gradFun_eq_abstractHessian`,
`inner_cov_gradFun_symm`, `heart_of_bochner_curvature_term`, `ricciTensor_apply_smooth_basisSum`,
and the orthonormal-frame trace identity for the abstract Hessian (which is
discharged from chart orthonormality at `x` via `traceFun_abstractHessian_eq_laplacian`).

The discharge requires identifying the smooth orthonormal frame
`smoothOrthoFrame g x i` at `x` with the chart-basis frame `chartBasisVecFiber
x i` at `x` — this identification holds when the chart at `x` is `g`-orthonormal
at `x` (then the Gram-Schmidt step is a no-op).

We expose the discharge in two parts:

* `IsChartOrthonormalAt_implies_smoothOrthoFrame_eq_chartBasis_at_self` —
  under chart orthonormality at `x`, the smooth orthonormal frame at `x`
  agrees with the chart basis at `x`. This isolates the Gram-Schmidt
  identification.

* The combined discharge of `IsHeartOfBochnerInnerAt` requires combining the
  smooth-orthonormal-frame identification with the orthonormal-frame trace of
  the abstract Hessian, an algebraic computation that we leave to a downstream
  task. The packaging exposed here is sufficient for a downstream client to
  perform the discharge once the missing identification is added.

The current file does **not** discharge `IsHeartOfBochnerInnerAt` from
`IsChartOrthonormalAt`; that discharge requires the orthonormal-frame trace
identity for the abstract Hessian (i.e., the identity
`∑_i abstractHessian g f x (B_i x) (B_i x) = traceFun (abstractHessianBilin g f) x`
when `(B_i)` is `g_x`-orthonormal at `x`). The identity is purely linear-algebraic
and is the natural "next step" after chart orthonormality.
-/

/-! ## Bochner-Weitzenböck identity assuming both reductions

The unconditional Bochner-Weitzenböck identity is exposed in its packaged form
`bochner_pointwise_abstract_of_reduction`, accepting a `BochnerReductionAt`
record. The remaining gap is in producing the `BochnerReductionAt` record from
metric-only data (e.g. chart orthonormality at `x`).

The downstream client is responsible for supplying the `BochnerReductionAt`
record. The two natural routes:

1. **Chart-orthonormality route**: discharge B2 and B3 via the orthonormal-frame
   trace identity, in turn from chart orthonormality at `x`. This requires the
   pure-algebra orthonormal-frame trace identity (currently not in this file).

2. **Direct metric-compatibility route**: discharge B2 directly by computing the
   metric Laplacian on the inner-product scalar via metric compatibility twice;
   discharge B3 directly via `inner_cov_gradFun_symm` and
   `heart_of_bochner_curvature_term` combined with the metric-trace formula
   for the Hessian.

Both routes go through the same algebraic content (the orthonormal-frame trace
identity for symmetric bilinear forms on `T_x M`).

The naming convention `bochner_pointwise_abstract_unconditional_*` reserves the
`unconditional` suffix for the discharge-from-metric variant; the present
file's `bochner_pointwise_abstract_of_reduction` is the discharge-from-reduction
variant. -/

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

/-! ## Re-exports under canonical names

For downstream consumers, the canonical name `bochner_pointwise_abstract` is
the entry point to the Bochner-Weitzenböck identity. The conditional form
`bochner_abstract_packaged` is preserved as the standard call shape, and the
reduction-input form `bochner_pointwise_abstract_of_reduction` takes the two
reductions as a single packaged record. -/

/-! ## Orthonormal-frame trace identity for symmetric bilinear forms

This section establishes a pure linear-algebra identity: for any continuous
bilinear form `H : T_x M →L T_x M →L ℝ` and any `g_x`-orthonormal basis
`(B_i)` of `T_x M`, the basis-naive sum `∑ i, H (B i) (B i)` equals the
metric trace of `H` against the model basis `(e_k) = Module.finBasis ℝ E`:
$$
  \sum_i H(B_i, B_i) = \sum_{k l} G^{kl}(x, x) \cdot H(e_k, e_l),
$$
where `G^{kl}(x, x) = chartInvGramMatrix g x x k l` is the inverse Gram matrix
of the model basis under `g_x`.

The proof expands `B_i = ∑_k a_{ik} \cdot e_k`, applies bilinearity of `H`,
and identifies `∑_i a_{ik} a_{il}` with `G^{kl}(x, x)` via orthonormality
(equivalent to the matrix identity `A^T A = G^{-1}` where `A_{ik} = a_{ik}`
is the change-of-basis matrix and `G_{kl} = g_x(e_k, e_l)` is the Gram
matrix). -/

section OrthonormalFrameTrace

variable (g : SmoothRiemannianMetric I M) (x : M)

/-- The change-of-basis matrix from a frame `B : Fin n → T_x M` to the model
basis `(Module.finBasis ℝ E)`. The `(i, k)`-th entry is the `k`-th coordinate
of `B_i` in the model basis. -/
private noncomputable def coBchange
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i k => (Module.finBasis ℝ E).repr (B i) k

@[simp] private lemma coBchange_apply
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i k : Fin (Module.finrank ℝ E)) :
    coBchange (I := I) (x := x) B i k =
      (Module.finBasis ℝ E).repr (B i) k := rfl

/-- The Gram matrix of the model basis at `x`, using `g.inner x`. By
definition, this equals `chartGramMatrix g x x` (since `chartBasisVecFiber x i x =
(Module.finBasis ℝ E) i`). -/
private noncomputable def modelGramMatrix :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k l =>
    g.inner x ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l)

@[simp] private lemma modelGramMatrix_apply
    (k l : Fin (Module.finrank ℝ E)) :
    modelGramMatrix (I := I) g x k l =
      g.inner x ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l) := rfl

/-- The model Gram matrix at `x` agrees with `chartGramMatrix g x x`, since the
chart-basis fibre vectors at the chart base point equal the model basis. -/
private lemma modelGramMatrix_eq_chartGramMatrix :
    modelGramMatrix (I := I) g x = chartGramMatrix (I := I) g x x := by
  classical
  ext k l
  rw [modelGramMatrix_apply, chartGramMatrix_apply]
  rw [chartBasisVecFiber_self (I := I) x k]
  rw [chartBasisVecFiber_self (I := I) x l]

/-- Each tangent vector `B_i` decomposes against the model basis as a finite
linear combination of `(Module.finBasis ℝ E) k` with coefficients
`a_{ik} = (Module.finBasis ℝ E).repr (B_i) k`. -/
private lemma decompose_in_modelBasis
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) :
    B i = ∑ k : Fin (Module.finrank ℝ E),
      coBchange (I := I) (x := x) B i k •
        ((Module.finBasis ℝ E) k : TangentSpace I x) := by
  classical
  have h := (Module.finBasis ℝ E).sum_repr (B i)
  -- `Basis.sum_repr` gives `∑ k, b.repr (Bᵢ) k • b k = Bᵢ`.
  exact h.symm

/-- **Bilinear expansion of `Hb(B i, B j)` against the model basis.** -/
private lemma bilin_expand_modelBasis
    (Hb : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i j : Fin (Module.finrank ℝ E)) :
    Hb (B i) (B j) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i k *
          coBchange (I := I) (x := x) B j l *
            Hb ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l) := by
  classical
  -- Direct approach: expand using bilinearity of Hb.
  -- Step 1: Hb (B i) = ∑ k, a_ik • Hb (e_k), as an equation in (T_x M →L ℝ).
  have hHb_first : Hb (B i) =
      ∑ k : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i k •
          Hb ((Module.finBasis ℝ E) k) := by
    have hi := decompose_in_modelBasis (I := I) (x := x) B i
    rw [show Hb (B i) = Hb (∑ k : Fin (Module.finrank ℝ E),
            coBchange (I := I) (x := x) B i k •
              ((Module.finBasis ℝ E) k : TangentSpace I x))
          from congrArg Hb hi]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    exact Hb.map_smul (coBchange (I := I) (x := x) B i k)
      ((Module.finBasis ℝ E) k : TangentSpace I x)
  rw [hHb_first]
  -- Step 2: Apply `(∑ k, a_ik • Hb e_k)` to `B j` ⇒ ∑ k, a_ik • Hb e_k (B j).
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  -- Each summand: (a_ik • Hb e_k) (B j) = a_ik * Hb e_k (B j).
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- Step 3: Hb e_k (B j) = Hb e_k (∑ l, a_jl • e_l) = ∑ l, a_jl * Hb e_k e_l.
  have hHb_second : Hb ((Module.finBasis ℝ E) k) (B j) =
      ∑ l : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B j l *
          Hb ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l) := by
    have hj := decompose_in_modelBasis (I := I) (x := x) B j
    rw [show Hb ((Module.finBasis ℝ E) k) (B j) =
          Hb ((Module.finBasis ℝ E) k)
            (∑ l : Fin (Module.finrank ℝ E),
              coBchange (I := I) (x := x) B j l •
                ((Module.finBasis ℝ E) l : TangentSpace I x))
        from congrArg (Hb ((Module.finBasis ℝ E) k)) hj]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    -- Goal: (Hb e_k) (a_jl • e_l) = a_jl * (Hb e_k) e_l.
    -- Apply CLM map_smul, then `smul_eq_mul`.
    have hsmul : Hb ((Module.finBasis ℝ E) k)
        (coBchange (I := I) (x := x) B j l •
          ((Module.finBasis ℝ E) l : TangentSpace I x)) =
        coBchange (I := I) (x := x) B j l •
          Hb ((Module.finBasis ℝ E) k)
            ((Module.finBasis ℝ E) l : TangentSpace I x) :=
      (Hb ((Module.finBasis ℝ E) k)).map_smul
        (coBchange (I := I) (x := x) B j l)
        ((Module.finBasis ℝ E) l : TangentSpace I x)
    rw [hsmul, smul_eq_mul]
  rw [hHb_second]
  -- Final: a_ik * (∑ l, a_jl * Hb e_k e_l) = ∑ l, a_ik * a_jl * Hb e_k e_l.
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  ring

/-- **Bilinear expansion of `g_x(B i, B j)` against the model basis (Gram form).**
This is the case `H = g.inner x` in `bilin_expand_modelBasis`. -/
private lemma gram_expand_modelBasis
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x (B i) (B j) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i k *
          coBchange (I := I) (x := x) B j l *
            modelGramMatrix (I := I) g x k l := by
  classical
  have h := bilin_expand_modelBasis (I := I) (x := x) (g.inner x) B i j
  refine h.trans ?_
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [modelGramMatrix_apply]

/-- **Matrix form of orthonormality.** If `(B_i)` is `g_x`-orthonormal, then
the change-of-basis matrix `A_{ik} := (Module.finBasis ℝ E).repr (B_i) k`
satisfies `A G A^T = I`, where `G = modelGramMatrix g x`. -/
private lemma orthonormal_matrix_form
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    coBchange (I := I) (x := x) B *
        modelGramMatrix (I := I) g x *
          (coBchange (I := I) (x := x) B).transpose =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
  classical
  ext i j
  -- `(A G A^T) i j = ∑ k l, A_{ik} G_{kl} A_{jl}`. Use `gram_expand_modelBasis` to
  -- match `g(Bᵢ, Bⱼ)`.
  have hg := gram_expand_modelBasis (I := I) g x B i j
  rw [hB i j] at hg
  -- hg : (if i = j then 1 else 0) =
  --   ∑ k l, A_{ik} A_{jl} G_{kl}
  -- Goal: (A G Aᵀ) i j = (1 : Matrix _ _ _) i j
  -- Compute (A G Aᵀ) i j:
  rw [Matrix.mul_apply]
  -- Goal: ∑ k, (A * G) i k * (Aᵀ) k j = (1 : Matrix _ _ _) i j
  have h_inner : ∀ k : Fin (Module.finrank ℝ E),
      (coBchange (I := I) (x := x) B *
          modelGramMatrix (I := I) g x) i k *
        (coBchange (I := I) (x := x) B).transpose k j =
      ∑ l : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i l *
          modelGramMatrix (I := I) g x l k *
          coBchange (I := I) (x := x) B j k := by
    intro k
    rw [Matrix.mul_apply]
    rw [Matrix.transpose_apply]
    rw [Finset.sum_mul]
  rw [show (∑ k, (coBchange (I := I) (x := x) B *
        modelGramMatrix (I := I) g x) i k *
      (coBchange (I := I) (x := x) B).transpose k j) =
    ∑ k, ∑ l,
      coBchange (I := I) (x := x) B i l *
          modelGramMatrix (I := I) g x l k *
          coBchange (I := I) (x := x) B j k from
    Finset.sum_congr rfl (fun k _ => h_inner k)]
  -- Now match this double sum with the one from `gram_expand_modelBasis`.
  -- Goal: ∑ k l, A_{il} G_{lk} A_{jk} = (1 : Matrix _ _ _) i j
  -- And hg : (if i = j then 1 else 0) = ∑ k l, A_{ik} A_{jl} G_{kl}
  -- After renaming dummies k ↔ l on the RHS of hg, both sums match.
  rw [show (1 : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) i j =
      (if i = j then (1 : ℝ) else 0) from by
    rw [Matrix.one_apply]]
  rw [hg]
  -- Now show: ∑ k l, A_{il} G_{lk} A_{jk} = ∑ k l, A_{ik} A_{jl} G_{kl}.
  -- Swap the order of summation on the LHS (∑ k ∑ l → ∑ l ∑ k).
  rw [Finset.sum_comm]
  -- Now the LHS is ∑ l, ∑ k, A_{il} * G_{lk} * A_{jk}.
  -- RHS is ∑ k, ∑ l, A_{ik} * A_{jl} * G_{kl}.
  -- Match by relabeling the outer variable of the LHS (currently `l`) with the
  -- outer variable of the RHS (currently `k`), and the inner of the LHS (currently
  -- `k`) with the inner of the RHS (currently `l`). Both sides become equivalent
  -- by `ring` after `Finset.sum_congr`.
  refine Finset.sum_congr rfl ?_
  intro l₀ _
  refine Finset.sum_congr rfl ?_
  intro k₀ _
  ring

/-- **Inverse-matrix consequence of orthonormality.** If `(B_i)` is `g_x`-orthonormal,
then `Aᵀ * A = G⁻¹`, where `A_{ik} = (Module.finBasis ℝ E).repr (B_i) k` and
`G = modelGramMatrix g x`. -/
private lemma orthonormal_matrix_inverse
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    (coBchange (I := I) (x := x) B).transpose *
        coBchange (I := I) (x := x) B =
      (modelGramMatrix (I := I) g x)⁻¹ := by
  classical
  have hAGA := orthonormal_matrix_form (I := I) g x B hB
  -- A G Aᵀ = 1 means A * (G * Aᵀ) = 1, so G * Aᵀ is the right inverse of A.
  -- Hence A⁻¹ = G * Aᵀ. Then A⁻¹ * A = 1, so G * Aᵀ * A = 1, so Aᵀ * A = G⁻¹.
  set A : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := coBchange (I := I) (x := x) B with hA_def
  set G : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := modelGramMatrix (I := I) g x with hG_def
  -- hAGA : A * G * A.transpose = 1
  have hAGA_right : A * (G * A.transpose) = 1 := by
    rw [← Matrix.mul_assoc]; exact hAGA
  -- A * (G * A.transpose) = 1 ⇒ A⁻¹ = G * A.transpose.
  have hG_At_eq_inv : G * A.transpose = A⁻¹ :=
    (Matrix.inv_eq_right_inv hAGA_right).symm
  -- (G * A.transpose) * A = A⁻¹ * A = 1 (using mul_eq_one_comm via IsDedekindFiniteMonoid).
  have hA_left_inv : (G * A.transpose) * A = 1 :=
    (mul_eq_one_comm).mp hAGA_right
  -- (G * A.transpose) * A = G * (A.transpose * A), so G * (A.transpose * A) = 1.
  rw [Matrix.mul_assoc] at hA_left_inv
  -- hA_left_inv : G * (A.transpose * A) = 1.
  -- Hence A.transpose * A = G⁻¹.
  exact (Matrix.inv_eq_right_inv hA_left_inv).symm

/-- **Sum of products of change-of-basis entries equals inverse Gram entries.**
For an `g_x`-orthonormal basis `(B_i)`, the sum `∑ i, a_{ik} a_{il}` (over the
frame index `i`) equals the inverse Gram matrix entry `G^{kl}`. -/
private lemma sum_coBchange_eq_invGram
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0)
    (k l : Fin (Module.finrank ℝ E)) :
    ∑ i : Fin (Module.finrank ℝ E),
      coBchange (I := I) (x := x) B i k *
        coBchange (I := I) (x := x) B i l =
      chartInvGramMatrix (I := I) g x x k l := by
  classical
  have h := orthonormal_matrix_inverse (I := I) g x B hB
  -- h : Aᵀ * A = G⁻¹.
  -- Compute (Aᵀ * A) k l:
  have heq : (coBchange (I := I) (x := x) B).transpose *
      coBchange (I := I) (x := x) B =
        (chartGramMatrix (I := I) g x x)⁻¹ := by
    rw [h]
    rw [modelGramMatrix_eq_chartGramMatrix (I := I) g x]
  have heval : ((coBchange (I := I) (x := x) B).transpose *
      coBchange (I := I) (x := x) B) k l =
        (chartGramMatrix (I := I) g x x)⁻¹ k l := by
    rw [heq]
  -- (Aᵀ * A) k l = ∑ i, Aᵀ k i * A i l = ∑ i, A i k * A i l.
  rw [Matrix.mul_apply] at heval
  rw [show ∑ i, (coBchange (I := I) (x := x) B).transpose k i *
            coBchange (I := I) (x := x) B i l =
         ∑ i, coBchange (I := I) (x := x) B i k *
            coBchange (I := I) (x := x) B i l from by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.transpose_apply]] at heval
  rw [heval]
  -- chartInvGramMatrix g x x = (chartGramMatrix g x x)⁻¹ by definition.
  rfl

/-- **Orthonormal-frame trace identity for a continuous bilinear form.**
For any continuous bilinear form `Hb : T_x M →L T_x M →L ℝ` and any `g_x`-
orthonormal basis `(B_i)`, the sum on the frame equals the metric trace
against the model basis:
$$
  \sum_i Hb(B_i, B_i) = \sum_{kl} G^{kl}(x, x) \cdot Hb(e_k, e_l).
$$
-/
theorem orthonormal_basis_bilin_trace
    (Hb : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          Hb ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l) := by
  classical
  -- Step 1: expand each `Hb (B i) (B i)` as a double sum.
  have h_expand : ∀ i : Fin (Module.finrank ℝ E),
      Hb (B i) (B i) =
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          coBchange (I := I) (x := x) B i k *
            coBchange (I := I) (x := x) B i l *
              Hb ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l) :=
    fun i => bilin_expand_modelBasis (I := I) (x := x) Hb B i i
  -- Step 2: sum over i, swap the order of summation.
  rw [show ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          coBchange (I := I) (x := x) B i k *
            coBchange (I := I) (x := x) B i l *
              Hb ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l) from
    Finset.sum_congr rfl (fun i _ => h_expand i)]
  -- Swap ∑ i with ∑ k ∑ l.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  -- Swap the outer ∑ i: (a*b)*c = c*(a*b), and pull out the constant Hb term.
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i k *
          coBchange (I := I) (x := x) B i l *
            Hb ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l)) =
      (∑ i : Fin (Module.finrank ℝ E),
        coBchange (I := I) (x := x) B i k *
          coBchange (I := I) (x := x) B i l) *
        Hb ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l) from by
    rw [Finset.sum_mul]]
  rw [sum_coBchange_eq_invGram (I := I) g x B hB k l]

end OrthonormalFrameTrace

/-! ## Specialisation to the abstract Hessian

For the abstract Hessian `H = abstractHessianBilin g f`, the orthonormal-frame
trace identity combined with `chartHessianMatrixIdentity_holds` and
`chartHessTrace_eq_laplacian_pointwise_of_boundaryless` gives:
$$
  \sum_i \mathrm{abstractHessian}\,g\,f\,x\,(B_i)\,(B_i) =
    \mathrm{chartHessTrace}\,g\,f\,x = \Delta_g f x.
$$

This is the Hessian-trace pillar that discharges the Bochner reductions. -/

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
  -- Step 1: orthonormal trace identity for H = abstractHessian g f x (as a CLM).
  have htrace := orthonormal_basis_bilin_trace (I := I) g x
    (abstractHessian (I := I) g f x) B hB
  rw [htrace]
  -- Step 2: identify each `abstractHessian g f x e_k e_l` with `chartHessianTensor g x f k l x`.
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          abstractHessian (I := I) g f x ((Module.finBasis ℝ E) k)
            ((Module.finBasis ℝ E) l)) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          chartHessianTensor (I := I) g x f k l x from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [hM k l]]
  -- Step 3: this is `chartHessTrace g f x` by definition, which equals `Δ_g f x`.
  rw [show (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          chartHessianTensor (I := I) g x f k l x) =
      chartHessTrace (I := I) g f x from rfl]
  exact chartHessTrace_eq_laplacian_pointwise_of_boundaryless (I := I) g hf x

/-! ## Specialisation of the orthonormal-frame trace to the smooth orthonormal frame

Combining `sum_abstractHessian_orthonormal_eq_laplacian` with the smooth
orthonormal frame `smoothOrthoFrame g x` (which is `g_x`-orthonormal at `x` by
`smoothOrthoFrame_orthonormal_at_center`), we obtain the discharge of the
Hessian-trace pillar in a form directly compatible with `connLaplacian_vector`. -/

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

/-! ## Per-summand abstract Hessian of the inner-product squared

The abstract Hessian of `b ↦ g(V, V)(b)` on a pair `(Y_x, Y_x)` decomposes
through the cotangent-cov dual-pairing identity (`cotangentCov_dualPairing`)
and the metric-compatibility identity (`LeviCivita_isMetricCompatible`)
applied twice:
$$
  \mathrm{abstractHessian}\,g\,(b \mapsto g(V, V)(b))\,x\,(Y x)\,(Y x) =
    2 g_x(\nabla_{Y x} \nabla_Y V, V x) -
      2 g_x(\nabla_{\nabla_Y x Y} V, V x) +
      2 g_x(\nabla_{Y x} V, \nabla_{Y x} V).
$$
This is the per-summand input to discharging the trace reduction `hLeibniz`
(B2 hypothesis of the Bochner identity). -/

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
  -- Step 1: Apply cotangent-cov dual-pairing with θ = extDerivFun(g(V, V)), Y = Y, v = Y x.
  -- abstractHessian g f' x (Y x) (Y x) = ((cotangentCov LC) θ x (Y x)) (Y x).
  -- = extDerivFun(b ↦ θ_b (Y_b)) x (Y x) - θ_x (LC Y x (Y x)).
  set f' : M → ℝ := fun b => g.inner b (V b) (V b) with hf'_def
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f' with hθ_def
  -- Smoothness: θ as cotangent section is C∞ at x via cotangentCov_extDerivFun_smooth.
  have hθ_at : MDiffAtCotangent θ x := by
    have hθ_smooth := cotangentCov_extDerivFun_smooth (I := I) hgVV
    exact (hθ_smooth x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  -- Apply `cotangentCov_dualPairing` at v = Y x.
  have hdual := cotangentCov_dualPairing (LeviCivita (I := I) g) hθ_at hY_at (Y x)
  -- hdual : extDerivFun(b ↦ θ_b (Y_b)) x (Y x)
  --       = ((cotangentCov LC) θ x (Y x)) (Y x) + θ_x (LC Y x (Y x)).
  have habsH : abstractHessian (I := I) g f' x (Y x) (Y x) =
      ((cotangentCov (LeviCivita (I := I) g)).toFun θ x (Y x)) (Y x) := rfl
  rw [habsH]
  have h_isolate :
      ((cotangentCov (LeviCivita (I := I) g)).toFun θ x (Y x)) (Y x) =
        extDerivFun (I := I) (fun b : M => θ b (Y b)) x (Y x) -
          θ x ((LeviCivita (I := I) g).toFun Y x (Y x)) := by
    linarith [hdual]
  rw [h_isolate]
  -- Step 2: θ_b (Y_b) = mfderiv f' b (Y b) = 2 g(LC V b (Y b), V b) by extDerivFun_inner_self.
  have hθY_eq : ∀ b : M, θ b (Y b) =
      2 * g.inner b ((LeviCivita (I := I) g).toFun V b (Y b)) (V b) := by
    intro b
    exact extDerivFun_inner_self (I := I) g hV b (Y b)
  -- The function b ↦ θ_b (Y_b) equals b ↦ 2 * g(LC V b (Y b), V b) pointwise.
  -- We need to show extDerivFun is the same on both functions (they agree pointwise).
  have h_func_eq : (fun b : M => θ b (Y b)) =
      (fun b : M => 2 * g.inner b
        ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) := by
    funext b
    exact hθY_eq b
  rw [h_func_eq]
  -- Step 3: extDerivFun(b ↦ 2 g(LC V b (Y b), V b)) x (Y x) =
  --   2 * extDerivFun(b ↦ g(LC V b (Y b), V b)) x (Y x).
  -- Use const_smul_mfderiv: mfderiv (s • f) x = s • mfderiv f x.
  have h_2_factor :
      extDerivFun (I := I)
        (fun b : M => 2 * g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x (Y x) =
      2 * extDerivFun (I := I)
        (fun b : M => g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x (Y x) := by
    -- Smoothness of inner-product scalar (needed for const_smul_mfderiv).
    -- Smoothness of P (= covApply LC Y V) and of g(P, V).
    have hP_smooth0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (covApply (LeviCivita (I := I) g) Y V)) :=
      contMDiffOn_univ.mp
        (covApply_contMDiffOn (cov := LeviCivita (I := I) g) hY hV)
    -- For g(LC V b (Y b), V b), use contMDiff of inner-product applied to two smooth sections.
    -- We'll route through `g.contMDiff` and `clm_bundle_apply₂`.
    have h_inner_at : MDiffAt
        (fun b : M => g.inner b
          ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x := by
      -- Since `LC V b (Y b) = covApply LC Y V b` by definition:
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
    -- extDerivFun ((2 : ℝ) • h) x = 2 • extDerivFun h x.
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
    -- Goal: ((2 : ℝ) • mfderiv ...) (Y x) = 2 * extDerivFun ... (Y x).
    -- Simp closes via `smul_eq_mul` (and identification of `extDerivFun = mfderiv` for ℝ).
    simp [smul_eq_mul]
    rfl
  rw [h_2_factor]
  -- Step 4: Apply metric-compat to `b ↦ g(P_b, V_b)` where P_b = LC V b (Y b) = covApply LC Y V b.
  -- This gives: extDerivFun(b ↦ g(P, V)) x (Y x) = g(LC P x (Y x), V x) + g(P x, LC V x (Y x)).
  -- We use LeviCivita_isMetricCompatible.
  set P : Π b : M, TangentSpace I b :=
    fun b : M => (LeviCivita (I := I) g).toFun V b (Y b) with hP_def
  -- P = covApply LC Y V (definitionally).
  have hP_eq_covApply : P = covApply (LeviCivita (I := I) g) Y V := rfl
  -- Smoothness of P: by `covApply_contMDiffOn` (covApply preserves smoothness).
  have hP_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% P) := by
    rw [hP_eq_covApply]
    exact contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := LeviCivita (I := I) g) hY hV)
  have hP_at : MDiffAt (T% P) x := (hP_smooth x).mdifferentiableAt (by simp)
  have hV_at : MDiffAt (T% V) x := (hV x).mdifferentiableAt (by simp)
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hP_at hV_at (Y x)
  -- hmc : (mfderiv I 𝓘(ℝ) (b ↦ g(P b, V b))) x (Y x)
  --     = g(LC P x (Y x), V x) + g(P x, LC V x (Y x)).
  have h_extDerivFun_eq :
      extDerivFun (I := I) (fun b : M => g.inner b
        ((LeviCivita (I := I) g).toFun V b (Y b)) (V b)) x (Y x) =
      g.inner x ((LeviCivita (I := I) g).toFun P x (Y x)) (V x) +
        g.inner x (P x) ((LeviCivita (I := I) g).toFun V x (Y x)) := hmc
  -- P x = LC V x (Y x).
  have hPx : P x = (LeviCivita (I := I) g).toFun V x (Y x) := rfl
  rw [hPx] at h_extDerivFun_eq
  rw [h_extDerivFun_eq]
  -- Step 5: Identify LC P x (Y x) = LC.toFun (covApply LC Y V) x (Y x).
  have hLCP : (LeviCivita (I := I) g).toFun P x (Y x) =
      (LeviCivita (I := I) g).toFun (covApply (LeviCivita (I := I) g) Y V) x (Y x) :=
    by rw [hP_eq_covApply]
  rw [hLCP]
  -- Step 6: θ_x (LC Y x (Y x)) = 2 * g(LC V x (LC Y x (Y x)), V x).
  have hθ_x_LC : θ x ((LeviCivita (I := I) g).toFun Y x (Y x)) =
      2 * g.inner x ((LeviCivita (I := I) g).toFun V x
        ((LeviCivita (I := I) g).toFun Y x (Y x))) (V x) := by
    -- Apply `extDerivFun_inner_self` at b = x with vector `LC Y x (Y x)`.
    -- θ_x v = mfderiv f' x v = extDerivFun f' x v = 2 g(LC V x v, V x).
    change extDerivFun (I := I) f' x ((LeviCivita (I := I) g).toFun Y x (Y x)) =
      2 * g.inner x ((LeviCivita (I := I) g).toFun V x
        ((LeviCivita (I := I) g).toFun Y x (Y x))) (V x)
    exact extDerivFun_inner_self (I := I) g hV x
      ((LeviCivita (I := I) g).toFun Y x (Y x))
  rw [hθ_x_LC]
  -- Final algebraic combination:
  -- 2 * (g(LC P x (Y x), V x) + g(LC V x (Y x), LC V x (Y x))) - 2 * g(LC V x (LC Y x (Y x)), V x)
  --   = 2 * (g(LC (covApply LC Y V) x (Y x), V x) - g(LC V x (LC Y x (Y x)), V x)) + 2 * g(LC V x (Y x), LC V x (Y x)).
  -- This is just rearrangement (subtract the third term, group).
  ring

/-! ## Bochner identity reduced to per-summand Hessian identities

The orthonormal-frame trace identity collapses the global Laplacian
`Δ_g(g(\nabla f, \nabla f))(x)` and the global heart-of-Bochner inner-product
identity into per-summand identities about `abstractHessian` evaluated on the
smooth orthonormal frame. We expose the resulting "per-summand" form of the
Bochner identity, which is the cleanest single-step discharge of the
conditional Bochner-Weitzenböck identity.

The per-summand identities required are:

* **Leibniz per-summand**: For each `i`, the abstract Hessian of `b ↦ g(V, V)(b)`
  at `x` against `(B_i x, B_i x)` equals the metric-compatibility expansion
  `2 g(∇_{B_i} ∇_{B_i} V - ∇_{∇_{B_i} B_i} V, V) + 2 g(∇_{B_i} V, ∇_{B_i} V)`,
  which, summed over `i`, is `2 g(Δ_∇ V, V) + 2 |∇V|^2`. This is the
  cotangent-cov Leibniz expansion plus metric-compat applied twice to the
  scalar `b ↦ g(V, V)(b)`.

* **Heart-of-Bochner per-summand**: The inner-product form of the Hessian-trace
  identity for `f` itself, traced over the smooth orthonormal frame, plus the
  curvature-skew identity (`heart_of_bochner_curvature_term`), gives the
  inner-product equation against any test vector `w`. -/

/-! ## Discharge of `hLeibniz` for `V = ∇f`

Combining `abstractHessian_innerSelf_apply` (the per-summand expansion of the
abstract Hessian of an inner-product squared) with
`sum_abstractHessian_smoothOrthoFrame_eq_laplacian` (the Hessian-trace =
Laplacian identity), the trace reduction `hLeibniz` for `V = ∇f` is fully
discharged. The smooth orthonormal frame `B = smoothOrthoFrame g x` provides
the orthonormality at `x` and the smoothness of each `B_i`. -/

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
  -- Unfold IsLeibnizTraceAt to its underlying identity.
  change Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
    2 * g.inner x (connLaplacian_vector (I := I) g
                    (fun b => gradFun (I := I) g f b) x)
                   (gradFun (I := I) g f x) +
      2 * frobeniusSq_grad_vector (I := I) g
            (fun b => gradFun (I := I) g f b) x
  -- Step 1: orthonormal-frame Hessian-trace identity.
  set V : Π b : M, TangentSpace I b := fun b => gradFun (I := I) g f b with hV_def
  set hgVV : ContMDiff I 𝓘(ℝ, ℝ) ∞
    (fun b : M => g.inner b (V b) (V b)) := normGradSq_contMDiff (I := I) g hf with hgVV_def
  have hV_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have h_trace := sum_abstractHessian_smoothOrthoFrame_eq_laplacian (I := I) g hgVV x
  -- h_trace : ∑ i, abstractHessian g (g(V,V)) x (B_i x) (B_i x) = Δ_g g hgVV x.
  -- We need the reverse direction:
  rw [← h_trace]
  -- Step 2: expand each summand via abstractHessian_innerSelf_apply.
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
  -- Step 3: split the sum into two parts.
  rw [Finset.sum_add_distrib]
  -- Step 4: pull out the factor 2 in each summand.
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- Step 5: identify the two sums with `g(connLaplacian_vector V x, V x)` and
  -- `frobeniusSq_grad_vector g V x`.
  -- The second sum is exactly `frobeniusSq_grad_vector g V x` by definition.
  have h_frob : ∑ i : Fin (Module.finrank ℝ E),
        g.inner x
            ((LeviCivita (I := I) g).toFun V x
              (smoothOrthoFrame (I := I) g x i x))
            ((LeviCivita (I := I) g).toFun V x
              (smoothOrthoFrame (I := I) g x i x)) =
      frobeniusSq_grad_vector (I := I) g V x := rfl
  rw [h_frob]
  -- The first sum is `g(connLaplacian_vector g V x, V x)`. By definition,
  -- `connLaplacian_vector g V x = localConnLap_vector LC smoothOrthoFrame V x =
  --   ∑ i (LC (covApply LC B_i V) x (B_i x) - LC V x (LC B_i x (B_i x)))`.
  -- Then `g.inner x (∑_i (...)) (V x) = ∑_i g.inner x (...) (V x) = ∑_i (g.inner _ _ - g.inner _ _)`.
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
    -- By def: connLaplacian_vector g V x = localConnLap_vector LC smoothOrthoFrame V x
    --       = ∑_i (LC (covApply LC B_i V) x (B_i x) - LC V x (LC B_i x (B_i x))).
    -- g.inner x (∑_i u_i) (V x) = ∑_i g.inner x u_i (V x).
    -- Then split the difference: g.inner x (a - b) (V x) = g.inner x a (V x) - g.inner x b (V x).
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
    -- Distribute the inner product.
    rw [map_sum]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    -- g.inner x (a - b) (V x) = g.inner x a (V x) - g.inner x b (V x).
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
  -- Discharge `hLeibniz` from `hPerSummand_Leibniz` via the orthonormal-frame trace identity.
  have hLeibniz : IsLeibnizTraceAt (I := I) g
      (fun b => gradFun (I := I) g f b)
      (normGradSq_contMDiff (I := I) g hf) x := by
    -- IsLeibnizTraceAt unfolds to:
    --   Δ_g g (normGradSq_contMDiff g hf) x
    --     = 2 * g.inner x (Δ_∇ ∇f) (∇f x) + 2 * frobeniusSq_grad_vector g ∇f x.
    -- Use `sum_abstractHessian_smoothOrthoFrame_eq_laplacian` for the LHS.
    change Δ_g (I := I) g (normGradSq_contMDiff (I := I) g hf) x =
      2 * g.inner x (connLaplacian_vector (I := I) g
                      (fun b => gradFun (I := I) g f b) x)
                     (gradFun (I := I) g f x) +
        2 * frobeniusSq_grad_vector (I := I) g
              (fun b => gradFun (I := I) g f b) x
    -- Step 1: rewrite Δ_g(g(∇f, ∇f)) as the orthonormal-frame trace.
    have h1 := sum_abstractHessian_smoothOrthoFrame_eq_laplacian (I := I) g
      (normGradSq_contMDiff (I := I) g hf) x
    -- h1 : ∑ i, abstractHessian g (g(∇f,∇f)) x (B_i x) (B_i x) = Δ_g g _ x.
    -- We need to prove the equation in the other direction:
    rw [← h1]
    exact hPerSummand_Leibniz
  -- Now apply the conditional Bochner identity.
  exact bochner_pointwise_abstract (I := I) g hf x hLeibniz hInner

/-! ## Truly unconditional Bochner identity (modulo `hInner`)

With the trace reduction `hLeibniz` discharged unconditionally via
`hLeibniz_discharge`, the only remaining input is the heart-of-Bochner
inner-product reduction `hInner` (B3 hypothesis). This is the cleanest possible
form of the conditional Bochner-Weitzenböck identity. -/

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

/-! ## Discharge of `hInner` (heart-of-Bochner inner-product reduction)

The remaining algebraic input for the unconditional Bochner-Weitzenböck identity
is the heart-of-Bochner inner-product reduction `hInner`. This section provides
a closed proof that the reduction holds for every smooth scalar `f` on a smooth
boundaryless Riemannian manifold; combining with `hLeibniz_discharge` gives the
truly unconditional pointwise Bochner-Weitzenböck identity.

The mathematical content is the textbook derivation of the heart of Bochner via
metric compatibility, Hessian symmetry, the (section-level) Riemann curvature
operator, and the orthonormal-frame trace formula for Ricci. We organise the
proof in the following helper lemmas:

* **`linearMap_trace_eq_invGram_bilin_sum`** — for any linear endomorphism
  `T : T_x M → T_x M`, the trace `tr T = ∑_{kl} G^{kl} g(T(e_k), e_l)`
  where `G^{kl} = chartInvGramMatrix g x x k l` and `e_k = (Module.finBasis
  ℝ E) k`. This is the trace formula in the model basis weighted by the
  inverse Gram matrix.

* **`finBasis_repr_eq_invGram_inner_sum`** — for `e = Module.finBasis ℝ E`
  and `X ∈ T_x M`, `e.repr X i = ∑_l G^{il} g(X, e_l)`. The dual of the model
  basis under `g_x` factors through the inverse Gram matrix.

* **`ricciTensor_orthonormal_endo_trace`** — for the smooth orthonormal frame
  `B_i = smoothOrthoFrame g x i x` (a `g_x`-orthonormal basis of `T_x M`),
  `Ric(v, w) = ∑_i g(R(B_i, v) w, B_i)` (orthonormal trace).

* **`heart_curvature_orthonormal_sum_eq_ricci`** — the key combinatorial
  identity for the curvature contribution: `∑_i g(R(B_i, w) ∇f, B_i) =
  Ric(∇f, w)` (using Ric symmetry to exchange the two slot positions).

* **`smoothOrthoFrame_cov_metric_skew`** — differentiating the orthonormality
  identity `g(B_i, B_j) = δ_{ij}` along a tangent direction `Y x` shows that
  the matrix `a_{ij} = g(∇_{Y x} B_i, B_j x)` is antisymmetric in `(i, j)`.

* **`sum_abstractHessian_smoothOrthoFrame_cov_eq_zero`** — combining the
  antisymmetry of `a_{ij}` with the symmetry of the abstract Hessian gives
  `∑_i abstractHessian g f x (B_i x) (∇_{Y x} B_i x) = 0`.

* **`smoothOrthoFrameNbhd_sum_abstractHessian_eq_laplacian`** — on the
  neighborhood `smoothOrthoFrameNbhd x` where the frame is orthonormal, the
  pointwise sum `b ↦ ∑_i abstractHessian g f b (B_i b) (B_i b)` agrees with
  `Δ_g f`.

* **`hInner_discharge`** — the full discharge of `IsHeartOfBochnerInnerAt`.

* **`bochner_pointwise_abstract_unconditional`** — the truly unconditional
  pointwise Bochner-Weitzenböck identity, with both `hLeibniz` and `hInner`
  discharged.
-/

/-! ### Trace identity for endomorphisms: trace = Gram-weighted bilinear sum

For a linear endomorphism `T : T_x M → T_x M`, the basis-independent
`LinearMap.trace ℝ T` admits the chart-coordinate / Gram-weighted form
$$
  \mathrm{tr}\,T = \sum_{k l} G^{k l}(x, x)\, g_x\bigl(T(e_k),\, e_l\bigr),
$$
where `G^{kl} = chartInvGramMatrix g x x k l` and `(e_k) = Module.finBasis ℝ E`
is the model-space basis (also a basis of `T_x M = E`).

The proof factors through the basis-coordinate trace formula
`LinearMap.trace_eq_matrix_trace`:
$$
  \mathrm{tr}\,T = \sum_k (e.\mathrm{repr}\,T(e_k))_k.
$$
The single basis-coordinate `(e.repr X)_k` is then expressed in terms of the
metric inner products `g(X, e_l)` via the inverse Gram matrix:
`(e.repr X)_k = ∑_l G^{kl} g(X, e_l)`. Substituting and summing yields the
desired trace formula.

This is the key linear-algebraic identity that allows us to convert traces of
Riemann-derived endomorphisms (such as `Z ↦ R(Z, w) ∇f x`) into orthonormal-
frame trace sums, which the smooth orthonormal frame can produce.
-/

section TraceIdentity

variable (g : SmoothRiemannianMetric I M) (x : M)

/-- **Decomposition of the model basis representation against the metric.**
For `e = Module.finBasis ℝ E` and `X ∈ T_x M`:
$$
  (e.\mathrm{repr}\,X)_k = \sum_l G^{k l}(x, x)\, g_x(X,\, e_l),
$$
where `G^{kl} = chartInvGramMatrix g x x k l`. The proof proceeds by
expanding `X` against the model basis, evaluating `g(X, e_l)` as a linear
combination of Gram entries, and inverting the Gram matrix. -/
private lemma finBasis_repr_eq_invGram_inner_sum
    (X : TangentSpace I x) (k : Fin (Module.finrank ℝ E)) :
    (Module.finBasis ℝ E).repr X k =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          g.inner x X ((Module.finBasis ℝ E) l) := by
  classical
  -- Expand X in the model basis: X = ∑ k, (e.repr X) k • e_k.
  have hX_decomp : X = ∑ p : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).repr X p •
        ((Module.finBasis ℝ E) p : TangentSpace I x) :=
    ((Module.finBasis ℝ E).sum_repr X).symm
  -- Compute g(X, e_l):
  --   g(X, e_l) = g(∑ p (e.repr X) p • e_p, e_l)
  --             = ∑ p (e.repr X) p * g(e_p, e_l)
  --             = ∑ p (e.repr X) p * G_{pl}(x, x).
  have h_inner_decomp : ∀ l : Fin (Module.finrank ℝ E),
      g.inner x X ((Module.finBasis ℝ E) l) =
        ∑ p : Fin (Module.finrank ℝ E),
          (Module.finBasis ℝ E).repr X p *
            chartGramMatrix (I := I) g x x p l := by
    intro l
    -- Use the symmetric form: g(X, e_l) = g(e_l, X) by g.symm.
    rw [g.symm x X ((Module.finBasis ℝ E) l)]
    -- Now decompose X in the right slot.
    rw [show g.inner x ((Module.finBasis ℝ E) l) X =
          g.inner x ((Module.finBasis ℝ E) l) (∑ p : Fin (Module.finrank ℝ E),
            (Module.finBasis ℝ E).repr X p •
              ((Module.finBasis ℝ E) p : TangentSpace I x)) from
      congrArg (g.inner x ((Module.finBasis ℝ E) l)) hX_decomp]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    -- For each p: g(e_l, c_p • e_p) = c_p * g(e_l, e_p) = c_p * g(e_p, e_l) = c_p * G_{pl}.
    -- We need: g.inner x e_l (c_p • e_p) = c_p * G_{pl}.
    -- Use the explicit smul/map_smul of the CLM (linear functional `g.inner x e_l`).
    show g.inner x ((Module.finBasis ℝ E) l)
        (((Module.finBasis ℝ E).repr X) p •
          ((Module.finBasis ℝ E) p : TangentSpace I x)) =
      ((Module.finBasis ℝ E).repr X) p *
        chartGramMatrix (I := I) g x x p l
    -- Apply linearity in the second slot: g(a, c • b) = c * g(a, b).
    rw [show g.inner x ((Module.finBasis ℝ E) l)
            (((Module.finBasis ℝ E).repr X) p •
              ((Module.finBasis ℝ E) p : TangentSpace I x)) =
        ((Module.finBasis ℝ E).repr X) p •
          g.inner x ((Module.finBasis ℝ E) l)
            ((Module.finBasis ℝ E) p) from
      ContinuousLinearMap.map_smul (g.inner x ((Module.finBasis ℝ E) l)) _ _]
    rw [smul_eq_mul]
    rw [g.symm x ((Module.finBasis ℝ E) l) ((Module.finBasis ℝ E) p)]
    rw [show g.inner x ((Module.finBasis ℝ E) p) ((Module.finBasis ℝ E) l) =
          chartGramMatrix (I := I) g x x p l from by
      rw [← modelGramMatrix_apply (I := I) g x p l,
          modelGramMatrix_eq_chartGramMatrix (I := I) g x]]
  -- Sum over l of G^{kl} * g(X, e_l):
  --   ∑ l G^{kl} ∑ p (e.repr X) p * G_{pl}
  --   = ∑ p (e.repr X) p ∑ l G^{kl} G_{pl}
  --   = ∑ p (e.repr X) p (G^{-1} G)_{kp}
  --   = ∑ p (e.repr X) p δ_{kp}^T
  --   = ∑ p (e.repr X) p * G^{kl}_l G_{pl}, where (G^{-1} G^T)_{kp} = ?
  -- Since G is symmetric (chartGramMatrix is symmetric), G^{-1} is symmetric,
  -- and (G^{-1} G)_{kp} = δ_{kp}.
  -- We compute step-by-step:
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          g.inner x X ((Module.finBasis ℝ E) l)) =
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (∑ p : Fin (Module.finrank ℝ E),
            (Module.finBasis ℝ E).repr X p *
              chartGramMatrix (I := I) g x x p l) from
    Finset.sum_congr rfl (fun l _ => by rw [h_inner_decomp])]
  -- Distribute and swap sums.
  rw [show (∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          (∑ p : Fin (Module.finrank ℝ E),
            (Module.finBasis ℝ E).repr X p *
              chartGramMatrix (I := I) g x x p l)) =
      ∑ l : Fin (Module.finrank ℝ E),
        ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            ((Module.finBasis ℝ E).repr X p *
              chartGramMatrix (I := I) g x x p l) from by
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [Finset.mul_sum]]
  rw [Finset.sum_comm]
  -- Now the sum is ∑ p, ∑ l, G^{kl} * (e.repr X p * G_{pl}).
  -- Rearrange to: ∑ p, (e.repr X p) * (∑ l, G^{kl} * G_{pl}).
  rw [show (∑ p : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            ((Module.finBasis ℝ E).repr X p *
              chartGramMatrix (I := I) g x x p l)) =
      ∑ p : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).repr X p *
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              chartGramMatrix (I := I) g x x p l from by
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    ring]
  -- ∑ l, G^{kl} * G_{pl} = (G^{-1} * G^T)_{kp}. Since G is symmetric, G^T = G.
  -- So this = (G^{-1} * G)_{kp} = δ_{kp}.
  -- We need to identify ∑ l, G^{kl} * G_{pl} as δ_{kp}.
  -- Use: G is symmetric (chartGramMatrix is symmetric), and G^{-1} G = 1.
  have h_invGram_gram_eq : ∀ p : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          chartGramMatrix (I := I) g x x p l =
      if k = p then (1 : ℝ) else 0 := by
    intro p
    -- ∑ l, G^{-1}_{kl} * G_{pl} = ∑ l, G^{-1}_{kl} * G_{lp} (by G symmetric)
    --                          = (G^{-1} * G)_{kp} = δ_{kp}.
    -- Step 1: substitute G_{pl} = G_{lp} (chartGramMatrix is symmetric).
    have h_gram_symm : ∀ l : Fin (Module.finrank ℝ E),
        chartGramMatrix (I := I) g x x p l =
        chartGramMatrix (I := I) g x x l p := by
      intro l
      rw [chartGramMatrix_apply, chartGramMatrix_apply, g.symm]
    rw [show (∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x k l *
          chartGramMatrix (I := I) g x x p l) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            chartGramMatrix (I := I) g x x l p from by
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [h_gram_symm]]
    -- This is (G^{-1} * G)_{kp} = (1)_{kp} = δ_{kp}, using
    -- chartInvGramMatrix * chartGramMatrix = 1 at x.
    -- We need x ∈ trivializationAt baseSet. By BoundarylessManifold, x is
    -- always in the chart at x, so x ∈ baseSet at x.
    have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' x
    have hmul := chartInvGramMatrix_mul_chartGramMatrix (I := I) g x hx_base
    have heval : (chartInvGramMatrix (I := I) g x x *
        chartGramMatrix (I := I) g x x) k p =
        (1 : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) k p := by
      rw [hmul]
    rw [Matrix.mul_apply] at heval
    rw [heval, Matrix.one_apply]
  rw [show (∑ p : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).repr X p *
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              chartGramMatrix (I := I) g x x p l) =
      ∑ p : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).repr X p *
          (if k = p then (1 : ℝ) else 0) from by
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [h_invGram_gram_eq]]
  -- The sum collapses: the only non-zero term is at p = k.
  rw [show (∑ p : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).repr X p *
          (if k = p then (1 : ℝ) else 0)) =
      (Module.finBasis ℝ E).repr X k from by
    rw [Finset.sum_eq_single k]
    · simp
    · intro p _ hpk
      rw [if_neg (fun h => hpk h.symm)]; ring
    · intro hk
      exact absurd (Finset.mem_univ k) hk]

/-- **Trace formula in chart coordinates.** For any linear endomorphism
`T : T_x M →ₗ[ℝ] T_x M`, the basis-independent trace `LinearMap.trace ℝ T`
admits the Gram-weighted bilinear sum form:
$$
  \mathrm{tr}\,T = \sum_{k l} G^{k l}(x, x)\, g_x(T(e_k),\, e_l),
$$
where `G^{kl} = chartInvGramMatrix g x x k l`. This is the chart-coordinate
trace identity converting `LinearMap.trace ℝ T` into a metric-weighted bilinear
sum. -/
private lemma linearMap_trace_eq_invGram_bilin_sum
    (T : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x) T =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            g.inner x (T ((Module.finBasis ℝ E) k))
              ((Module.finBasis ℝ E) l) := by
  classical
  -- Use trace_eq_matrix_trace with basis e = Module.finBasis ℝ E.
  rw [LinearMap.trace_eq_matrix_trace ℝ
        (Module.finBasis ℝ (TangentSpace I x)) T]
  unfold Matrix.trace
  -- Goal: ∑ i, (T_e).diag i = ∑ k l, G^{kl} g(T e_k, e_l).
  -- Apply finBasis_repr_eq_invGram_inner_sum entry by entry.
  refine Finset.sum_congr rfl ?_
  intro k _
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply]
  -- Goal: e.repr (T e_k) k = ∑ l, G^{kl} g(T e_k, e_l).
  exact finBasis_repr_eq_invGram_inner_sum (I := I) g x
    (T ((Module.finBasis ℝ E) k)) k

/-- **Trace formula via orthonormal frame.** For any linear endomorphism
`T : T_x M →ₗ[ℝ] T_x M` and any `g_x`-orthonormal basis `(B_i)` of `T_x M`,
the trace `LinearMap.trace ℝ T` equals the orthonormal-frame trace sum:
$$
  \mathrm{tr}\,T = \sum_i g_x\bigl(T(B_i),\, B_i\bigr).
$$
The proof composes `linearMap_trace_eq_invGram_bilin_sum` with
`orthonormal_basis_bilin_trace` applied to the bilinear form `Hb(Z, W) :=
g(T(Z), W)`. -/
private theorem linearMap_trace_eq_orthonormal_bilin_sum
    (T : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    LinearMap.trace ℝ (TangentSpace I x) T =
      ∑ i : Fin (Module.finrank ℝ E), g.inner x (T (B i)) (B i) := by
  classical
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  -- Promote T to a CLM (automatic in finite dimensions).
  set Tc : TangentSpace I x →L[ℝ] TangentSpace I x :=
    LinearMap.toContinuousLinearMap T with hTc_def
  have hTc_apply : ∀ Z : TangentSpace I x, Tc Z = T Z := fun _ => rfl
  -- Define Hb(Z, W) := g(Tc(Z), W) as a CLM (composition).
  set Hb : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    (g.inner x).comp Tc with hHb_def
  have hHb_apply : ∀ Z W : TangentSpace I x,
      Hb Z W = g.inner x (T Z) W := by
    intro Z W
    change ((g.inner x).comp Tc) Z W = g.inner x (T Z) W
    rw [ContinuousLinearMap.comp_apply, hTc_apply]
  -- Apply orthonormal_basis_bilin_trace.
  have hortho := orthonormal_basis_bilin_trace (I := I) g x Hb B hB
  rw [show (∑ i : Fin (Module.finrank ℝ E), g.inner x (T (B i)) (B i)) =
      ∑ i : Fin (Module.finrank ℝ E), Hb (B i) (B i) from
    Finset.sum_congr rfl (fun i _ => (hHb_apply (B i) (B i)).symm)]
  rw [hortho]
  -- Match RHS via linearMap_trace_eq_invGram_bilin_sum.
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            Hb ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) l)) =
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x k l *
            g.inner x (T ((Module.finBasis ℝ E) k))
              ((Module.finBasis ℝ E) l) from by
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [hHb_apply]]
  exact linearMap_trace_eq_invGram_bilin_sum (I := I) g x T

end TraceIdentity

/-! ### Orthonormal-frame trace formula for the Ricci tensor

The Ricci tensor `ricciTensor g x v w = LinearMap.trace ℝ (Z ↦ R(Z, v) w)` admits
the orthonormal-frame trace expansion
$$
  \mathrm{Ric}_x(v, w) = \sum_i g_x\bigl(R(B_i, v) w,\, B_i\bigr)
$$
for any `g_x`-orthonormal basis `(B_i)` of `T_x M`. This is `linearMap_trace_eq_
orthonormal_bilin_sum` applied to the Ricci endomorphism `Z ↦ riemannOp LC x Z v w`.

We expose this in two forms: directly with `(v, w)` as `(∇f x, w_x)`, and via
Ricci symmetry (`ricciTensor_symm`) to obtain the form
`Ric(∇f, w) = ∑_i g(R(B_i, w) ∇f, B_i)` matching the curvature term that emerges
from the heart-of-Bochner derivation. -/

section RicciOrthonormalTrace

variable (g : SmoothRiemannianMetric I M) (x : M)

/-- The endomorphism `Z ↦ R(Z, v) w` on `T_x M`, packaged as a `LinearMap`. -/
private def riemannCurvatureEndo
    (v w : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun Z := riemannOp (LeviCivita (I := I) g) x Z v w
  map_add' Z Z' := by
    have h := (riemannOp (LeviCivita (I := I) g) x).map_add Z Z'
    set_option linter.unnecessarySimpa false in
    simpa using h
  map_smul' c Z := by
    have h := (riemannOp (LeviCivita (I := I) g) x).map_smul c Z
    set_option linter.unnecessarySimpa false in
    simpa using h

@[simp] private lemma riemannCurvatureEndo_apply
    (v w Z : TangentSpace I x) :
    riemannCurvatureEndo (I := I) g x v w Z =
      riemannOp (LeviCivita (I := I) g) x Z v w := rfl

/-- The Ricci tensor at `(v, w)` equals the orthonormal-frame trace of the
endomorphism `Z ↦ R(Z, v) w`:
$$
  \mathrm{Ric}_x(v, w) = \sum_i g_x\bigl(R(B_i, v) w,\, B_i\bigr).
$$
This is the "Ricci as orthonormal trace" formula. -/
private theorem ricciTensor_eq_orthonormal_trace
    (v w : TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ricciTensor (I := I) g x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (riemannOp (LeviCivita (I := I) g) x (B i) v w) (B i) := by
  classical
  -- ricciTensor g x v w = LinearMap.trace ℝ (ricciEndo g x v w).
  -- And ricciEndo g x v w Z = riemannOp LC x Z v w = riemannCurvatureEndo g x v w Z.
  have hRic : ricciTensor (I := I) g x v w =
      LinearMap.trace ℝ (TangentSpace I x)
        (riemannCurvatureEndo (I := I) g x v w) := by
    -- ricciTensor_apply gives ricciTensor = trace of ricciEndo. We then
    -- match ricciEndo (I := I) g x v w with riemannCurvatureEndo (I := I) g x v w
    -- by extensionality.
    rw [ricciTensor_apply]
    rfl
  rw [hRic]
  -- Apply linearMap_trace_eq_orthonormal_bilin_sum.
  rw [linearMap_trace_eq_orthonormal_bilin_sum (I := I) g x
    (riemannCurvatureEndo (I := I) g x v w) B hB]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [riemannCurvatureEndo_apply]

/-- **Curvature term identity for the heart of Bochner.** For the smooth
orthonormal frame `B_i = smoothOrthoFrame g x i x` and any tangent vector
`w ∈ T_x M`, the curvature term sum
$$
  \sum_i g_x\bigl(R(B_i, w)\,\nabla f x,\, B_i\bigr) = \mathrm{Ric}_x(\nabla f x,\, w).
$$
The proof uses Ricci symmetry to identify `Ric(∇f, w) = Ric(w, ∇f)` and the
orthonormal-frame trace formula for the latter. -/
private theorem heart_curvature_orthonormal_sum_eq_ricci
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (_hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (w : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (riemannOp (LeviCivita (I := I) g) x
        (smoothOrthoFrame (I := I) g x i x) w (gradFun (I := I) g f x))
        (smoothOrthoFrame (I := I) g x i x) =
      ricciTensor (I := I) g x (gradFun (I := I) g f x) w := by
  classical
  -- By Ricci symmetry, Ric(∇f, w) = Ric(w, ∇f).
  rw [ricciTensor_symm (I := I) g x (gradFun (I := I) g f x) w]
  -- Now apply the orthonormal-frame trace identity for Ric(w, ∇f).
  -- Note: Ric(w, ∇f) = ∑_i g(R(B_i, w) ∇f, B_i).
  rw [ricciTensor_eq_orthonormal_trace (I := I) g x w
        (gradFun (I := I) g f x)
        (fun i => smoothOrthoFrame (I := I) g x i x)
        (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)]

end RicciOrthonormalTrace

/-! ### Antisymmetry of cov-derivative of orthonormal frame

For the smooth orthonormal frame `B_i = smoothOrthoFrame g x i`, orthonormality
`g(B_i, B_j) = δ_{ij}` holds on `smoothOrthoFrameNbhd x`. Differentiating along
any tangent direction `Y x` and applying metric compatibility produces the
antisymmetry identity
$$
  g_x(\nabla_{Y x} B_i, B_j x) + g_x(B_i x, \nabla_{Y x} B_j) = 0.
$$
This is the standard "orthonormal-frame skew-derivative" identity, the engine
of the Killing-vector formula for orthonormal frames. -/

section OrthonormalFrameSkewDerivative

variable (g : SmoothRiemannianMetric I M) (x : M)

/-- Differentiating `g(B_i, B_j) = δ_{ij}` along a tangent direction `v` at `x`
gives, via metric compatibility, the antisymmetry of the matrix
`a_{ij} := g(∇_v B_i, B_j x)`:
$$
  g_x(\nabla_v B_i, B_j x) = - g_x(B_i x, \nabla_v B_j).
$$
The proof differentiates the constant function `b ↦ g(B_i b, B_j b) = δ_{ij}`
on the orthonormal neighborhood, then uses metric compatibility. -/
private theorem smoothOrthoFrame_cov_skew
    (i j : Fin (Module.finrank ℝ E))
    (v : TangentSpace I x) :
    g.inner x ((LeviCivita (I := I) g).toFun
        (smoothOrthoFrame (I := I) g x i) x v)
        (smoothOrthoFrame (I := I) g x j x) =
      - g.inner x (smoothOrthoFrame (I := I) g x i x)
          ((LeviCivita (I := I) g).toFun
            (smoothOrthoFrame (I := I) g x j) x v) := by
  classical
  -- Smooth orthonormal frame B_k is C^∞ as a section.
  have hBi := smoothOrthoFrame_smooth (I := I) g x i
  have hBj := smoothOrthoFrame_smooth (I := I) g x j
  -- The function b ↦ g(B_i b, B_j b) is constant = δ_{ij} on smoothOrthoFrameNbhd x.
  have h_constant_on_nbhd : ∀ᶠ b in 𝓝 x,
      g.inner b (smoothOrthoFrame (I := I) g x i b)
        (smoothOrthoFrame (I := I) g x j b) =
      (if i = j then (1 : ℝ) else 0) := by
    have h_open : smoothOrthoFrameNbhd (I := I) (M := M) x ∈ 𝓝 x :=
      smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x
    filter_upwards [h_open] with b hb
    exact smoothOrthoFrame_orthonormal (I := I) g x hb i j
  -- The mfderiv at x of a constant function is zero.
  have h_eq : (fun b : M => g.inner b
        (smoothOrthoFrame (I := I) g x i b)
        (smoothOrthoFrame (I := I) g x j b)) =ᶠ[𝓝 x]
      (fun _ : M => (if i = j then (1 : ℝ) else 0)) := h_constant_on_nbhd
  have h_mfderiv : mfderiv I 𝓘(ℝ) (fun b : M =>
        g.inner b (smoothOrthoFrame (I := I) g x i b)
          (smoothOrthoFrame (I := I) g x j b)) x =
      mfderiv I 𝓘(ℝ) (fun _ : M => (if i = j then (1 : ℝ) else 0)) x :=
    Filter.EventuallyEq.mfderiv_eq h_eq
  -- The derivative of the constant function is zero.
  have h_const_zero : mfderiv I 𝓘(ℝ)
      (fun _ : M => (if i = j then (1 : ℝ) else 0)) x = 0 :=
    mfderiv_const ..
  -- Apply metric compatibility for the inner product b ↦ g(B_i, B_j) at x.
  have hBi_at : MDiffAt (T% (smoothOrthoFrame (I := I) g x i)) x :=
    (hBi x).mdifferentiableAt (by simp)
  have hBj_at : MDiffAt (T% (smoothOrthoFrame (I := I) g x j)) x :=
    (hBj x).mdifferentiableAt (by simp)
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hBi_at hBj_at v
  -- hmc : (mfderiv I 𝓘(ℝ) (b ↦ g(B_i, B_j)(b))) x v
  --     = g(LC B_i x v, B_j x) + g(B_i x, LC B_j x v).
  -- Combining: 0 = g(LC B_i x v, B_j x) + g(B_i x, LC B_j x v).
  -- Hence g(LC B_i x v, B_j x) = -g(B_i x, LC B_j x v).
  have h_zero : (mfderiv I 𝓘(ℝ) (fun b : M =>
        g.inner b (smoothOrthoFrame (I := I) g x i b)
          (smoothOrthoFrame (I := I) g x j b)) x) v = 0 := by
    rw [h_mfderiv, h_const_zero]
    rfl
  rw [h_zero] at hmc
  -- hmc : 0 = g(LC B_i v, B_j x) + g(B_i x, LC B_j v).
  -- Goal: g(LC B_i v, B_j x) = -g(B_i x, LC B_j v).
  -- From 0 = A + B, we get A = -B by `eq_neg_of_add_eq_zero_left` or algebra.
  exact eq_neg_of_add_eq_zero_left hmc.symm

end OrthonormalFrameSkewDerivative

/-! ### Orthonormal Riesz expansion

For a `g_x`-orthonormal basis `(B_i)` of `T_x M`, every vector `X ∈ T_x M`
admits the Riesz expansion
$$
  X = \sum_i g_x(X,\, B_i)\, B_i.
$$
This is the standard "orthonormal expansion" / Parseval identity for the
inner product `g_x`. We prove it from the orthonormal-frame trace identity
applied to the bilinear form `Hb(Z, W) := g(X, Z) g(W, ·)` (using a custom
inner product CLM packaging). -/

section OrthonormalRiesz

variable (g : SmoothRiemannianMetric I M) (x : M)

/-- **Parseval identity for `g_x` against an orthonormal basis.** For any
`g_x`-orthonormal basis `(B_i)` of `T_x M` and any pair `(X, Y) ∈ T_x M × T_x M`:
$$
  g_x(X,\, Y) = \sum_i g_x(X,\, B_i) \cdot g_x(B_i,\, Y).
$$
The proof uses `orthonormal_basis_bilin_trace` applied to the bilinear form
`Hb(Z₁, Z₂) := g(X, Z₁) * g(Z₂, Y)` and the trace formula
`linearMap_trace_eq_invGram_bilin_sum` for the unique linear endomorphism
`T : T_x M → T_x M` satisfying `g(T(Z), W) = g(X, Z) * g(W, Y)`. The endomorphism
`T` is the rank-one operator `Z ↦ g(X, Z) • Y_♯` where `Y_♯` is the metric-flat
of `Y`; its trace is `g(X, Y)` directly. -/
private theorem g_inner_eq_orthonormal_parseval_sum
    (X Y : TangentSpace I x)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    g.inner x X Y =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner x X (B i) * g.inner x (B i) Y := by
  classical
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  -- Build the rank-one endomorphism T(Z) := g(X, Z) • Y.
  -- Then g(T(Z), W) = g(X, Z) * g(Y, W) = g(X, Z) * g(W, Y) (by g.symm).
  set T : TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
    { toFun := fun Z => g.inner x X Z • Y
      map_add' := fun Z Z' => by
        rw [(g.inner x X).map_add Z Z', add_smul]
      map_smul' := fun c Z => by
        rw [(g.inner x X).map_smul c Z, smul_eq_mul,
            show (c * g.inner x X Z) • Y = c • (g.inner x X Z) • Y from by
              rw [smul_smul]]
        rfl } with hT_def
  have hT_apply : ∀ Z : TangentSpace I x, T Z = g.inner x X Z • Y := fun _ => rfl
  -- Compute g(T(Z), W) = g(X, Z) * g(Y, W) = g(X, Z) * g(W, Y).
  have hT_pair : ∀ Z W : TangentSpace I x,
      g.inner x (T Z) W = g.inner x X Z * g.inner x W Y := by
    intro Z W
    rw [hT_apply]
    rw [show g.inner x (g.inner x X Z • Y) W =
          g.inner x X Z * g.inner x Y W from by
      rw [(g.inner x).map_smul (g.inner x X Z) Y]
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]]
    rw [g.symm x Y W]
  -- The trace of T equals g(X, Y), since T(Z) = g(X, Z) • Y is rank-one with
  -- expected trace g(X, Y).
  -- Specifically: for the basis e = Module.finBasis ℝ E, T(e_k) = g(X, e_k) • Y,
  -- and (e.repr T(e_k)) k = g(X, e_k) * (e.repr Y) k. Sum over k:
  --   tr T = ∑ k g(X, e_k) * (e.repr Y) k = ∑ k g(X, e_k) * (e.repr Y) k.
  -- We compute this via the formula linearMap_trace_eq_invGram_bilin_sum:
  --   tr T = ∑ kl G^{kl} g(T(e_k), e_l) = ∑ kl G^{kl} g(X, e_k) g(e_l, Y).
  -- And by orthonormal_basis_bilin_trace applied to Hb(Z, W) := g(T(Z), W):
  --   ∑ i g(T(B_i), B_i) = ∑ kl G^{kl} g(T(e_k), e_l).
  -- Combine: ∑ i g(T(B_i), B_i) = tr T.
  -- Compute trace via diagonal of T in basis e:
  --   tr T = ∑ k (e.repr T(e_k)) k.
  -- And T(e_k) = g(X, e_k) • Y, so (e.repr T(e_k)) k = g(X, e_k) * (e.repr Y) k.
  -- BUT we want g(X, Y) directly. Let me compute g(X, Y) as the trace via a
  -- specific basis where this becomes obvious.
  -- Direct approach: tr T equals g(X, Y) via the rank-one formula `LinearMap.trace`
  -- of `(g.inner x X) ⊗ Y`-style. Use `LinearMap.trace_one_eq_one` or rank-one trace.
  -- Let me bypass and just compute directly using linearMap_trace_eq_orthonormal_bilin_sum.
  have hT_trace_orthonormal :
      LinearMap.trace ℝ (TangentSpace I x) T =
        ∑ i : Fin (Module.finrank ℝ E), g.inner x (T (B i)) (B i) :=
    linearMap_trace_eq_orthonormal_bilin_sum (I := I) g x T B hB
  -- And tr T equals g(X, Y) via the rank-one trace identity.
  -- This is the standard identity tr(X ⊗ Y) = g(X, Y) for rank-one operators in
  -- inner-product spaces. Compute via Module.finBasis directly.
  have hT_trace_xy : LinearMap.trace ℝ (TangentSpace I x) T = g.inner x X Y := by
    -- Use linearMap_trace_eq_invGram_bilin_sum.
    rw [linearMap_trace_eq_invGram_bilin_sum (I := I) g x T]
    -- Goal: ∑ k l, G^{kl} * g(T e_k, e_l) = g(X, Y).
    -- T(e_k) = g(X, e_k) • Y, so g(T e_k, e_l) = g(X, e_k) * g(Y, e_l).
    -- ∑ k l, G^{kl} g(X, e_k) g(Y, e_l).
    -- Substitute g(T e_k, e_l) = g(X, e_k) * g(Y, e_l):
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              g.inner x (T ((Module.finBasis ℝ E) k))
                ((Module.finBasis ℝ E) l)) =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              (g.inner x X ((Module.finBasis ℝ E) k) *
                g.inner x ((Module.finBasis ℝ E) l) Y) from by
      refine Finset.sum_congr rfl ?_
      intro k _
      refine Finset.sum_congr rfl ?_
      intro l _
      rw [hT_pair]]
    -- ∑ k l G^{kl} (g(X, e_k) * g(e_l, Y)) = ∑ k g(X, e_k) * (∑ l G^{kl} g(e_l, Y)).
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              (g.inner x X ((Module.finBasis ℝ E) k) *
                g.inner x ((Module.finBasis ℝ E) l) Y)) =
        ∑ k : Fin (Module.finrank ℝ E),
          g.inner x X ((Module.finBasis ℝ E) k) *
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x k l *
                g.inner x ((Module.finBasis ℝ E) l) Y) from by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro l _
      ring]
    -- ∑ l G^{kl} g(e_l, Y) = (e.repr Y) k by finBasis_repr_eq_invGram_inner_sum.
    rw [show (∑ k : Fin (Module.finrank ℝ E),
          g.inner x X ((Module.finBasis ℝ E) k) *
            (∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x k l *
                g.inner x ((Module.finBasis ℝ E) l) Y)) =
        ∑ k : Fin (Module.finrank ℝ E),
          g.inner x X ((Module.finBasis ℝ E) k) *
            (Module.finBasis ℝ E).repr Y k from by
      refine Finset.sum_congr rfl ?_
      intro k _
      have h := finBasis_repr_eq_invGram_inner_sum (I := I) g x Y k
      -- h : (e.repr Y) k = ∑ l, G^{kl} * g(Y, e_l).
      -- We have ∑ l G^{kl} * g(e_l, Y); by g.symm, g(Y, e_l) = g(e_l, Y).
      have h' : (Module.finBasis ℝ E).repr Y k =
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x k l *
              g.inner x ((Module.finBasis ℝ E) l) Y := by
        rw [h]
        refine Finset.sum_congr rfl ?_
        intro l _
        rw [g.symm x Y ((Module.finBasis ℝ E) l)]
      rw [h']]
    -- ∑ k g(X, e_k) * (e.repr Y) k.
    -- Use Y = ∑ k (e.repr Y) k • e_k and g.inner x X linearity:
    --   g(X, Y) = g(X, ∑ k (e.repr Y) k • e_k) = ∑ k (e.repr Y) k * g(X, e_k).
    -- Rewriting: g(X, Y) = ∑ k g(X, e_k) * (e.repr Y) k.
    have hY_decomp : Y = ∑ k : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).repr Y k •
          ((Module.finBasis ℝ E) k : TangentSpace I x) :=
      ((Module.finBasis ℝ E).sum_repr Y).symm
    rw [show g.inner x X Y = g.inner x X
            (∑ k : Fin (Module.finrank ℝ E),
              (Module.finBasis ℝ E).repr Y k •
                ((Module.finBasis ℝ E) k : TangentSpace I x)) from
      congrArg (g.inner x X) hY_decomp]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [show g.inner x X
            ((Module.finBasis ℝ E).repr Y k •
              ((Module.finBasis ℝ E) k : TangentSpace I x)) =
          (Module.finBasis ℝ E).repr Y k *
            g.inner x X ((Module.finBasis ℝ E) k) from by
      rw [show ((g.inner x) X)
              (((Module.finBasis ℝ E).repr Y k) •
                ((Module.finBasis ℝ E) k : TangentSpace I x)) =
            ((Module.finBasis ℝ E).repr Y k) •
              ((g.inner x) X) ((Module.finBasis ℝ E) k) from
        ContinuousLinearMap.map_smul ((g.inner x) X) _ _]
      rw [smul_eq_mul]]
    ring
  -- Combine: g(X, Y) = ∑ i g(T(B_i), B_i) = ∑ i g(X, B_i) * g(B_i, Y).
  rw [← hT_trace_xy, hT_trace_orthonormal]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [hT_pair]

end OrthonormalRiesz

/-! ### Hessian-skew vanishing on the orthonormal frame

Combining the antisymmetry of `a_{ij} := g(∇_{Y x} B_i, B_j x)` with the
symmetry of the abstract Hessian gives
$$
  \sum_i \mathrm{abstractHessian}\,g\,f\,x\,(B_i x,\, \nabla_{Y x} B_i x) = 0.
$$
This is the cancellation that closes the heart-of-Bochner derivation: the
"connection-correction" term involving `∇_{Y x} B_i` vanishes upon summation
over the orthonormal frame, due to the antisymmetric × symmetric structure.
-/

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
  -- Step 1: Riesz expansion. ∇_v B_i = ∑_j g(∇_v B_i, B_j x) • B_j x.
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
  -- Step 2: expand each Hess summand using bilinearity of Hess in second argument.
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
    -- Apply hRiesz to rewrite ∇_v B_i.
    conv_lhs => rw [hRiesz i]
    -- Now Hess(B_i, ∑ j, c_j • B_j x) = ∑ j Hess(B_i, c_j • B_j x).
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    -- Hess(B_i, c_j • B_j x) = c_j • Hess(B_i, B_j x) = c_j * Hess(B_i, B_j x).
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
  -- Step 3: rewrite the double sum so each term has matching antisymmetric × symmetric pair.
  -- Set S := ∑ i j a_{ij} H_{ij} (with a antisym, H symm).
  -- Reindex: ∑ i j a_{ij} H_{ij} = ∑ i j a_{ji} H_{ji}  (j ↔ i swap)
  --                              = ∑ i j (-a_{ij}) H_{ij}  (a antisym + H symm).
  -- So S = -S, hence 2S = 0, hence S = 0.
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
  -- Hess symm at point x.
  have h_hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) (2 : ℕ∞) f x := hf.contMDiffAt.of_le (by
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1)
  have h_hess_symm : ∀ a b : TangentSpace I x,
      abstractHessian (I := I) g f x a b =
      abstractHessian (I := I) g f x b a := fun a b =>
    abstractHessian_symm (I := I) g h_hf_2 a b
  -- Define S as the sum.
  set S : ℝ := ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        g.inner x ((LeviCivita (I := I) g).toFun
            (smoothOrthoFrame (I := I) g x i) x v)
          (smoothOrthoFrame (I := I) g x j x) *
          abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x j x) with hS_def
  change S = 0
  -- Reindex: S = ∑ i j (a_ij * H_ij)
  --            = ∑ j i (a_ij * H_ij)              [Finset.sum_comm]
  --            = ∑ i j (a_ji * H_ji)              [renaming]
  --            = ∑ i j ((-a_ij) * H_ij)           [a antisym + H symm]
  --            = -∑ i j (a_ij * H_ij) = -S.
  -- Define S' = ∑ i j a_ji H_ji and T = ∑ i j -a_ij H_ij.
  -- We have S = S' (via sum_comm + relabel). And S' = T (via antisym/symm). And T = -S (algebra).
  -- Hence S = -S, so 2S = 0, so S = 0.
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
    -- Goal: ∑ i ∑ j -(inner) = -∑ i ∑ j inner.
    -- Use simp_rw to apply Finset.sum_neg_distrib at both levels.
    simp_rw [← Finset.sum_neg_distrib]
  -- Combine: S = S (h_step1) = ... (h_step2) = -S (h_step3).
  have h_S_eq_neg_S : S = -S := h_step1.trans (h_step2.trans h_step3)
  linarith

end HessianSkewVanishing

/-! ### Hessian-trace = Laplacian on the orthonormal frame neighborhood

On `smoothOrthoFrameNbhd x`, the smooth orthonormal frame is `g_b`-orthonormal
at every point `b`. Thus `∑_i abstractHessian g f b (B_i b) (B_i b)` equals
`Δ_g f b` for every `b` in the neighborhood, by the orthonormal-frame
Hessian-trace identity `sum_abstractHessian_orthonormal_eq_laplacian`.

Differentiating this pointwise identity along a tangent direction at `x`
extracts the gradient `∇(Δ_g f) x` paired with the test direction. -/

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
  -- At each b ∈ nbhd, B_i b is g_b-orthonormal.
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b
          (smoothOrthoFrame (I := I) g x i b)
          (smoothOrthoFrame (I := I) g x j b) =
        if i = j then 1 else 0 := fun i j =>
    smoothOrthoFrame_orthonormal (I := I) g x hb i j
  -- Apply sum_abstractHessian_orthonormal_eq_laplacian at b.
  exact sum_abstractHessian_orthonormal_eq_laplacian (I := I) g hf b
    (fun i => smoothOrthoFrame (I := I) g x i b) hB_orth

end LaplacianTraceOnNbhd

/-! ### Heart-of-Bochner discharge: main proof

We now combine the orthonormal-frame Hessian-trace identity, the Hessian-skew
vanishing on the orthonormal frame, the Ricci-as-orthonormal-trace formula,
and the section-level Riemann curvature identity to discharge the
heart-of-Bochner inner-product reduction `hInner` unconditionally for every
smooth scalar `f` on a smooth boundaryless Riemannian manifold.

The textbook derivation:

1. Start with `connLaplacian_grad_inner` for the LHS:
   $$
     g_x((\Delta_\nabla \nabla f)(x), W x) =
       \sum_i \bigl(g_x(\nabla_{B_i x} (\nabla_{B_i} \nabla f), W x) -
         g_x(\nabla_{(\nabla_{B_i} B_i)(x)} \nabla f, W x)\bigr).
   $$

2. Apply metric compatibility (B1) once to differentiate the inner-product:
   $$
     B_i x \bigl(g(\nabla_{B_i} \nabla f, W)\bigr) =
       g_x(\nabla_{B_i x}(\nabla_{B_i} \nabla f), W x) +
       g_x(\nabla_{B_i x} \nabla f, \nabla_{B_i x} W).
   $$
   So $g_x(\nabla_{B_i x} (\nabla_{B_i} \nabla f), W x) = B_i x(g(\nabla_{B_i}
   \nabla f, W)) - g_x(\nabla_{B_i x} \nabla f, \nabla_{B_i x} W)$.

3. By Hessian symmetry: $g(\nabla_{B_i} \nabla f, W) = g(\nabla_W \nabla f, B_i)$
   pointwise, so the section is the same. Apply metric compatibility to
   `b ↦ g(∇_{W b} ∇f, B_i b)` along `B_i x`:
   $$
     B_i x \bigl(g(\nabla_W \nabla f, B_i)\bigr) =
       g_x(\nabla_{B_i x}(\nabla_W \nabla f), B_i x) +
       g_x(\nabla_{W x} \nabla f, \nabla_{B_i x} B_i).
   $$

4. Use the section-level `riemannSec` (which is `R(B_i, W) ∇f`) plus
   torsion-freeness (`[B_i, W] = ∇_{B_i} W - ∇_W B_i`):
   $$
     \nabla_{B_i x}(\nabla_W \nabla f) - \nabla_{W x}(\nabla_{B_i} \nabla f) =
       R(B_i, W) \nabla f x + \nabla_{[B_i, W] x} \nabla f.
   $$

5. Sum over i, apply the orthonormal-frame trace formula for Ric, and use the
   Hessian-skew vanishing to cancel the connection-correction terms.

The final algebraic content:
$$
  g_x((\Delta_\nabla \nabla f)(x), w) =
    \mathrm{Ric}_x(\nabla f x, w) + \mathrm{mfderiv}\,(\Delta_g f)\,x\,w.
$$
By `gradFun_metricDual_extDerivFun`, the second term is `g_x(\nabla(\Delta_g f) x, w)`.
By `inner_ricciSharp`, the first term is `g_x(\mathrm{Ric}^\sharp(\nabla f x), w)`.
This matches the heart-of-Bochner inner-product reduction.

**Implementation note.** The full step-by-step derivation requires careful
case analysis on the section-level identities. We package the individual
algebraic ingredients as separate lemmas where needed, and combine them in
the main `hInner_discharge` theorem. -/

/-! #### Per-summand expansion via metric compat + Hessian symmetry + curvature

The next two helper theorems encode the per-summand transformations of the
LHS of the heart-of-Bochner identity in inner-product form.

**`heart_of_bochner_per_summand_swap`**: For each `i`, the per-summand quantity
`g(∇_{B_i x} (covApply LC B_i ∇f), w) - g(∇_{∇_{B_i x} B_i} ∇f, w)` equals
the "swapped" form `g(∇_{B_i x} (covApply LC W ∇f), B_i x) - g(∇_{∇_{B_i x} W}
∇f, B_i x)`. The proof applies metric compatibility (B1) twice combined with
Hessian symmetry to swap the two slots.

**`heart_of_bochner_per_summand_riemann_form`**: The "swapped" form rewrites
via `riemannSec` (the section-level Riemann curvature) into
`g(R(B_i, W) ∇f, B_i x) + g(∇_{W x} (covApply LC B_i ∇f), B_i x)
- g(∇_{∇_{W x} B_i} ∇f, B_i x)`.

These two transformations together produce the per-summand decomposition that
sums to `Ric(∇f, w) + g(∇(Δf), w)` after using the Hessian-skew vanishing and
the Δ_g-orthonormal-trace identity.

NOTE: The full proofs of these helper theorems require detailed metric-compat
manipulations at the level of `extDerivFun` and the section-level cov; we
provide the statements (with the transformations being the Bochner content) and
leave the per-summand details to a downstream completion. -/

/-! ### Status of the heart-of-Bochner discharge

The supporting infrastructure for the unconditional discharge of
`IsHeartOfBochnerInnerAt` is fully assembled in this file:

- `linearMap_trace_eq_invGram_bilin_sum` and `linearMap_trace_eq_orthonormal_bilin_sum`:
  basis-free trace formulas for endomorphisms of `T_x M`, expressed as
  inverse-Gram-weighted bilinear sums or orthonormal-frame bilinear sums.
- `ricciTensor_eq_orthonormal_trace` and `heart_curvature_orthonormal_sum_eq_ricci`:
  Ricci tensor as orthonormal-frame trace, including the form
  `Ric(∇f, w) = ∑_i g(R(B_i, w) ∇f, B_i)` matching the curvature term in the
  heart-of-Bochner derivation.
- `smoothOrthoFrame_cov_skew`: antisymmetry of the matrix
  `g(∇_v B_i, B_j x)` from differentiating orthonormality.
- `g_inner_eq_orthonormal_parseval_sum`: Parseval / Riesz expansion in any
  `g_x`-orthonormal basis.
- `sum_abstractHessian_smoothOrthoFrame_cov_eq_zero`: vanishing of the
  Hessian-skew sum on the orthonormal frame, via antisymmetric × symmetric
  cancellation.
- `sum_abstractHessian_smoothOrthoFrame_eventuallyEq_laplacian`: pointwise
  Hessian-trace = Laplacian on the orthonormal-frame neighborhood, ready for
  differentiation.

The remaining step is to assemble these into the per-summand textbook
Bochner derivation:
1. Apply `connLaplacian_grad_inner` (a re-export of
   `localConnLap_vector_grad_inner_eq_hessian_diff`) with the smooth
   extension `W := smoothExtensionTangent x w`.
2. Use `metric_compat_one` (B1) twice and `inner_cov_gradFun_symm_globally`
   (Hessian symmetry as sections) to swap derivatives and identify the
   per-summand "swapped" form with `g(∇_{B_i x} (∇_W ∇f), B_i x) -
   g(∇_{B_i x} ∇f, ∇_{B_i x} W)`.
3. Apply `riemannSec_def` and the torsion-free identity
   `[B_i, W] = ∇_{B_i} W - ∇_W B_i` to express the second-derivative
   difference as `R(B_i, W) ∇f` plus connection corrections.
4. Sum over i. The Hessian-skew vanishing eliminates the
   "connection-correction" terms; the orthonormal Hessian-trace identity
   identifies the trace of the second derivative as `mfderiv (Δ_g f) x w`,
   which equals `g(∇(Δ_g f), w)` via `gradFun_metricDual_extDerivFun`.
5. The curvature term sum equals `Ric(∇f x, w)` via
   `heart_curvature_orthonormal_sum_eq_ricci`, and `Ric(v, w) =
   g(Ric^♯(v), w)` via `inner_ricciSharp`.

The mechanical assembly of these ingredients into a single equation chain is
left as a final completion. The file as-is contains all ingredients needed,
with no `sorry`, `axiom`, or `admit`.

#### Mathematical derivation (worked out)

For each `i`, with `W := smoothExtensionTangent x w` (so `W x = w`),
`B_i := smoothOrthoFrame g x i`, `Q_i := covApply LC B_i ∇f`,
`P := covApply LC W ∇f`:

(a) **First metric compat (on `(Q_i, W)` along `B_i x`).** With
    `metric_compat_one (LeviCivita g) hQ_i hW (B_i x)`:
    $$
      B_i x \bigl(g(Q_i, W)\bigr) =
        g_x(\mathrm{LC}\, Q_i\, x\, (B_i x), W x) +
        g_x(Q_i x, \mathrm{LC}\, W\, x\, (B_i x)).
    $$
    Note `Q_i x = LC ∇f x (B_i x)`, so
    `g_x(Q_i x, LC W x (B_i x)) = abstractHessian g f x (B_i x, LC W x (B_i x))`
    via `inner_cov_gradFun_eq_abstractHessian`. By Hessian symmetry, this
    equals `abstractHessian g f x (LC W x (B_i x), B_i x) = g_x(LC ∇f x (LC W x (B_i x)), B_i x)`.

(b) **Hessian symmetry (section level).** The function `b ↦ g(Q_i b, W b) =
    abstractHessian g f b (B_i b) (W b)` agrees with `b ↦ abstractHessian g f b
    (W b) (B_i b) = g(P b, B_i b)` pointwise via `inner_cov_gradFun_symm_globally`.

(c) **Second metric compat (on `(P, B_i)` along `B_i x`).** With
    `metric_compat_one (LeviCivita g) hP hB_i (B_i x)`:
    $$
      B_i x \bigl(g(P, B_i)\bigr) =
        g_x(\mathrm{LC}\, P\, x\, (B_i x), B_i x) +
        g_x(P x, \mathrm{LC}\, B_i\, x\, (B_i x)).
    $$
    Note `g_x(P x, LC B_i x (B_i x)) = abstractHessian g f x (W x, LC B_i x (B_i x))`
    via `inner_cov_gradFun_eq_abstractHessian`. By Hessian symmetry, this
    equals `abstractHessian g f x (LC B_i x (B_i x), W x) =
    g_x(LC ∇f x (LC B_i x (B_i x)), W x)`.

(d) **Combining (a), (b), (c).**
    $$
      g_x(\mathrm{LC}\, Q_i\, x\, (B_i x), W x) -
      g_x(\mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, B_i\, x\, (B_i x)), W x) =
      g_x(\mathrm{LC}\, P\, x\, (B_i x), B_i x) -
      g_x(\mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, W\, x\, (B_i x)), B_i x).
    $$
    (The "swap" identity at the per-summand level.)

(e) **Apply `riemannSec_def` (with X = B_i, Y = W, Z = ∇f):**
    $$
      \mathrm{LC}\, P\, x\, (B_i x) = R(B_i, W) \nabla f|_x +
        \mathrm{LC}\, Q_i\, x\, (W x) +
        \mathrm{LC}\, \nabla f\, x\, ([B_i, W]_x).
    $$
    By torsion-freeness `[B_i, W]_x = LC W x (B_i x) - LC B_i x (W x)`:
    $$
      \mathrm{LC}\, \nabla f\, x\, ([B_i, W]_x) =
        \mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, W\, x\, (B_i x)) -
        \mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, B_i\, x\, (W x)).
    $$
    Pairing with `B_i x` and substituting:
    $$
      g_x(\mathrm{LC}\, P\, x\, (B_i x), B_i x) -
      g_x(\mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, W\, x\, (B_i x)), B_i x) =
      g_x(R(B_i, W) \nabla f, B_i x) +
      g_x(\mathrm{LC}\, Q_i\, x\, (W x), B_i x) -
      g_x(\mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, B_i\, x\, (W x)), B_i x).
    $$

(f) **Third metric compat (on `(Q_i, B_i)` along `W x`).**
    $$
      W x \bigl(g(Q_i, B_i)\bigr) =
        g_x(\mathrm{LC}\, Q_i\, x\, (W x), B_i x) +
        g_x(Q_i x, \mathrm{LC}\, B_i\, x\, (W x)).
    $$
    Note `g_x(Q_i x, LC B_i x (W x)) = abstractHessian g f x (B_i x, LC B_i x (W x))`
    by `inner_cov_gradFun_eq_abstractHessian`. By Hessian symmetry, this
    equals `g_x(LC ∇f x (LC B_i x (W x)), B_i x)`.
    So:
    $$
      g_x(\mathrm{LC}\, Q_i\, x\, (W x), B_i x) -
      g_x(\mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, B_i\, x\, (W x)), B_i x) =
      W x\,(g(Q_i, B_i)) -
      2\, g_x(\mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, B_i\, x\, (W x)), B_i x).
    $$
    Note the "two-fold cancellation": the Hessian symmetry produces TWO
    copies of `g_x(LC ∇f x (LC B_i x (W x)), B_i x)`, both subtracted.

(g) **Per-summand assembly.**
    $$
      \text{LHS}_i =
        g_x(R(B_i, W) \nabla f, B_i x) +
        W x\,(b \mapsto g(Q_i b, B_i b)) -
        2\, g_x(\mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, B_i\, x\, (W x)), B_i x).
    $$
    Equivalently, with `g(Q_i, B_i) = abstractHessian(B_i, B_i)` as sections:
    $$
      \text{LHS}_i =
        g_x(R(B_i, W) \nabla f, B_i x) +
        W x\,(b \mapsto \mathrm{abstractHessian}\, g\, f\, b\, (B_i b)\, (B_i b)) -
        2\, \mathrm{abstractHessian}\, g\, f\, x\, (B_i x,\, \mathrm{LC}\, B_i\, x\, (W x)).
    $$

(h) **Sum over i.**
    - Sum of curvature term: `Ric(∇f x, w)` via
      `heart_curvature_orthonormal_sum_eq_ricci`.
    - `W x (b ↦ ∑_i abstractHessian(B_i, B_i)(b))`: by
      `sum_abstractHessian_smoothOrthoFrame_eventuallyEq_laplacian`, this
      function equals `Δ_g f` on `smoothOrthoFrameNbhd x`. So the derivative
      at `x` along `W x = w` equals `mfderiv (Δ_g f) x w =
      extDerivFun (Δ_g f) x w = g(∇(Δ_g f), w)` via
      `gradFun_metricDual_extDerivFun`.
    - Sum of `2 abstractHessian(B_i x, LC B_i x (W x))` = `2 ∑_i Hess(B_i x,
      ∇_{W x} B_i)` = 0 by `sum_abstractHessian_smoothOrthoFrame_cov_eq_zero`.

    Therefore:
    $$
      \sum_i \text{LHS}_i = \mathrm{Ric}_x(\nabla f x, w) +
        g_x(\nabla(\Delta_g f) x, w) - 0 =
        g_x(\nabla(\Delta_g f) x, w) + g_x(\mathrm{Ric}^\sharp(\nabla f x), w),
    $$
    using `inner_ricciSharp` for the last step. -/

/-! #### Per-summand "swap" identity

Algebraic identity at the per-summand level: combining the first two metric-compat
applications and the section-level Hessian symmetry gives
$$
  g_x(\mathrm{LC}\, Q_i\, x\, (B_i x), W x) -
  g_x(\mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, B_i\, x\, (B_i x)), W x) =
  g_x(\mathrm{LC}\, P\, x\, (B_i x), B_i x) -
  g_x(\mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, W\, x\, (B_i x)), B_i x),
$$
where `Q_i = covApply LC B_i ∇f`, `P = covApply LC W ∇f`. This is the "swap"
identity at item (d) of the textbook derivation. -/
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
  -- Smoothness / differentiability hypotheses.
  have hB_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hGf_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Gf) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB_at : MDiffAt (T% B) x := (hB_smooth x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  have hGf_at : MDiffAt (T% Gf) x := (hGf_smooth x).mdifferentiableAt (by simp)
  -- Smoothness of Q = covApply cov B Gf and P = covApply cov W Gf at x.
  have hQ_at : MDiffAt (T% Q) x :=
    covApply_mdifferentiableAt_local (cov := cov) hB_at
      (by simpa using hGf_smooth)
  have hP_at : MDiffAt (T% P) x :=
    covApply_mdifferentiableAt_local (cov := cov) hW_at
      (by simpa using hGf_smooth)
  -- Step (a) — first metric compat on `(Q, W)` along `B x`.
  have hmc_QW :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hQ_at hW_at (B x)
  -- hmc_QW : (mfderiv ... (b ↦ g.inner b (Q b) (W b))) x (B x) =
  --   g.inner x (cov.toFun Q x (B x)) (W x) + g.inner x (Q x) (cov.toFun W x (B x))
  -- Step (c) — second metric compat on `(P, B)` along `B x`.
  have hmc_PB :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hP_at hB_at (B x)
  -- Step (b) — section-level Hessian symmetry: g(Q b, W b) = g(P b, B b).
  have hHess_section : (fun b : M => g.inner b (Q b) (W b)) =
      (fun b : M => g.inner b (P b) (B b)) := by
    have h := inner_cov_gradFun_symm_globally (I := I) g hf
      (X := B) (Y := W) hB_smooth hW
    -- h : (b ↦ g.inner b (cov Gf b (B b)) (W b)) = (b ↦ g.inner b (cov Gf b (W b)) (B b))
    -- Since covApply cov B Gf b = cov.toFun Gf b (B b) and covApply cov W Gf b = cov.toFun Gf b (W b),
    -- this is exactly hQ_def vs hP_def by definitional equality.
    funext b
    have hQb : Q b = cov.toFun Gf b (B b) := rfl
    have hPb : P b = cov.toFun Gf b (W b) := rfl
    rw [hQb, hPb]
    exact congrFun h b
  -- Differentiating the section-level identity gives equality of mfderivs at x along B x.
  have h_mfderiv_eq :
      (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (Q b) (W b)) x) (B x) =
        (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (P b) (B b)) x) (B x) := by
    rw [hHess_section]
    rfl
  -- Combining (a), (b), (c):
  -- g(LC Q x (B x), W x) + g(Q x, LC W x (B x)) =
  --   (mfderiv ... (b ↦ g(Q b, W b))) x (B x)
  --   = (mfderiv ... (b ↦ g(P b, B b))) x (B x)
  --   = g(LC P x (B x), B x) + g(P x, LC B x (B x))
  have h_combined :
      g.inner x (cov.toFun Q x (B x)) (W x) + g.inner x (Q x) (cov.toFun W x (B x)) =
        g.inner x (cov.toFun P x (B x)) (B x) +
          g.inner x (P x) (cov.toFun B x (B x)) := by
    rw [← hmc_QW, h_mfderiv_eq, hmc_PB]
  -- Identify the inner-product/Hessian terms via inner_cov_gradFun_eq_abstractHessian.
  -- g(Q x, LC W x (B x)) = abstractHessian g f x (B x, LC W x (B x))
  -- via Q x = LC Gf x (B x). Hess sym swaps to (LC W x (B x), B x).
  -- Similarly g(P x, LC B x (B x)) = abstractHessian g f x (W x, LC B x (B x))
  -- via P x = LC Gf x (W x). Hess sym swaps to (LC B x (B x), W x).
  have hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) (2 : ℕ∞) f x := hf.contMDiffAt.of_le (by
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1)
  -- Express g(Q x, LC W x (B x)) as Hessian, then swap by Hessian symmetry.
  have hQx_inner : g.inner x (Q x) (cov.toFun W x (B x)) =
      g.inner x (cov.toFun Gf x (cov.toFun W x (B x))) (B x) := by
    -- Q x = cov.toFun Gf x (B x). Apply inner_cov_gradFun_eq_abstractHessian twice with Hess sym.
    have hQx_eq : Q x = cov.toFun Gf x (B x) := rfl
    rw [hQx_eq]
    -- LHS = g(LC Gf x (B x), LC W x (B x))
    --     = abstractHessian g f x (B x) (LC W x (B x))   [inner_cov_gradFun_eq_abstractHessian, with X=B, Y=smoothExt of LC W x (B x)]
    -- RHS = g(LC Gf x (LC W x (B x)), B x)
    --     = abstractHessian g f x (LC W x (B x)) (B x).
    -- Use Hess sym to convert.
    -- Write X' := smoothExtensionTangent x (LC W x (B x)) (a smooth section with that value at x).
    set v : TangentSpace I x := cov.toFun W x (B x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    -- We want g.inner x (cov Gf x (B x)) v = g.inner x (cov Gf x v) (B x).
    -- Use inner_cov_gradFun_symm with X = B, Y = Xv; both are smooth.
    have h_sym := inner_cov_gradFun_symm (I := I) g hf
      (X := B) (Y := Xv) (x := x) hB_smooth hXv_smooth
    rw [show v = Xv x from hXv_eq.symm]
    -- h_sym : g.inner x (cov Gf x (B x)) (Xv x) = g.inner x (cov Gf x (Xv x)) (B x)
    exact h_sym
  -- Similarly for P x.
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
  -- Substitute into h_combined:
  -- g(LC Q x (B x), W x) + g(LC Gf x (LC W x (B x)), B x) =
  --   g(LC P x (B x), B x) + g(LC Gf x (LC B x (B x)), W x)
  rw [hQx_inner, hPx_inner] at h_combined
  -- Algebraic rearrangement:
  -- g(LC Q x (B x), W x) - g(LC Gf x (LC B x (B x)), W x) =
  --   g(LC P x (B x), B x) - g(LC Gf x (LC W x (B x)), B x).
  linarith

/-! #### Per-summand riemann form

Applying `riemannSec_def` and torsion-freeness to the swap form (e) gives the
equivalent expression with the curvature term explicit:
$$
  \mathrm{LHS}_i = g_x(R(B_i, W) \nabla f, B_i x) +
    g_x(\mathrm{LC}\, Q_i\, x\, (W x), B_i x) -
    g_x(\mathrm{LC}\, \nabla f\, x\, (\mathrm{LC}\, B_i\, x\, (W x)), B_i x).
$$
-/
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
  -- Smoothness / differentiability of B, W at x.
  have hB_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hB_at : MDiffAt (T% B) x := (hB_smooth x).mdifferentiableAt (by simp)
  have hW_at : MDiffAt (T% W) x := (hW x).mdifferentiableAt (by simp)
  -- Apply `LeviCivita_riemannSec_torsionFree_form` with X = B, Y = W, Z = Gf.
  have hriem :=
    LeviCivita_riemannSec_torsionFree_form (I := I) g
      (X := B) (Y := W) (Z := Gf) (x := x) hB_at hW_at
  -- hriem : riemannSec cov B W Gf x =
  --   cov.toFun (covApply cov W Gf) x (B x)
  --   - cov.toFun (covApply cov B Gf) x (W x)
  --   - (cov.toFun Gf x (cov.toFun W x (B x)) - cov.toFun Gf x (cov.toFun B x (W x)))
  -- Pair both sides with B x via g.inner.
  -- The goal is to convert
  --   g(LC P x (B x), B x) - g(LC Gf x (LC W x (B x)), B x)
  -- into
  --   g(R(B, W) Gf x, B x) + g(LC Q x (W x), B x) - g(LC Gf x (LC B x (W x)), B x)
  -- where Q := covApply cov B Gf, P := covApply cov W Gf.
  -- From hriem, we have:
  --   cov.toFun P x (B x) = riemannSec cov B W Gf x + cov.toFun Q x (W x)
  --     + cov.toFun Gf x (cov.toFun W x (B x)) - cov.toFun Gf x (cov.toFun B x (W x))
  -- Pairing with B x and using bilinearity of g.inner on the first slot:
  -- g(LC P x (B x), B x) = g(R(B, W) Gf x, B x) + g(LC Q x (W x), B x)
  --   + g(LC Gf x (LC W x (B x)), B x) - g(LC Gf x (LC B x (W x)), B x).
  -- Rearrange to obtain the goal.
  -- Step 1: Rewrite cov.toFun P x (B x) using hriem.
  -- Re-apply LeviCivita_riemannSec_torsionFree_form with `cov` matched.
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
  -- Step 2: rewrite the pairing on the LHS.
  -- g(cov.toFun P x (B x), B x) = g(riemannSec cov B W Gf x, B x)
  --   + g(cov.toFun Q x (W x), B x) + g(LC Gf x (LC W x (B x)), B x)
  --   - g(LC Gf x (LC B x (W x)), B x).
  have h_inner_split :
      g.inner x (cov.toFun (covApply cov W Gf) x (B x)) (B x) =
        g.inner x (riemannSec cov B W Gf x) (B x) +
          g.inner x (cov.toFun (covApply cov B Gf) x (W x)) (B x) +
          g.inner x (cov.toFun Gf x (cov.toFun W x (B x))) (B x) -
          g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) := by
    rw [hP_split]
    -- Distribute g.inner x · over the sum (left-linear), then subtraction.
    rw [map_add, ContinuousLinearMap.add_apply]
    rw [map_add, ContinuousLinearMap.add_apply]
    rw [map_sub, ContinuousLinearMap.sub_apply]
    ring
  -- Step 3: substitute into the goal.
  linarith

/-! #### Per-summand final form (after third metric compat)

Combining `heart_per_summand_swap`, `heart_per_summand_riemann_form`, and the third
metric compat (step (f)) plus Hessian symmetry:
$$
  \mathrm{LHS}_i = g_x(R(B_i, W) \nabla f, B_i x) +
    W x \bigl(b \mapsto \mathrm{abstractHessian}\,g\,f\,b\,(B_i b, B_i b)\bigr) -
    2\, \mathrm{abstractHessian}\,g\,f\,x\,(B_i x, \mathrm{LC}\, B_i\, x\, (W x)).
$$
-/
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
  -- Step 1: apply heart_per_summand_swap and heart_per_summand_riemann_form.
  have h_swap := heart_per_summand_swap (I := I) g hf x W hW i
  have h_riem := heart_per_summand_riemann_form (I := I) g hf x W hW i
  -- Combine: LHS = swap RHS = riemann RHS.
  -- Let me track:
  -- swap: LHS_i = g(LC P x (B x), B x) - g(LC ∇f x (LC W x (B x)), B x)
  -- riem: that = g(R(B,W) ∇f, B x) + g(LC Q x (W x), B x) - g(LC ∇f x (LC B x (W x)), B x)
  -- Step 2: third metric compat on (Q, B) along W x.
  -- Smoothness / differentiability of Q at x.
  have hB_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% B) :=
    smoothOrthoFrame_smooth (I := I) g x i
  have hGf_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Gf) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have hB_at : MDiffAt (T% B) x := (hB_smooth x).mdifferentiableAt (by simp)
  have hQ_at : MDiffAt (T% Q) x :=
    covApply_mdifferentiableAt_local (cov := cov) hB_at
      (by simpa using hGf_smooth)
  -- Third metric compat on (Q, B) along W x.
  have hmc_QB :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hQ_at hB_at (W x)
  -- hmc_QB : (mfderiv ... (b ↦ g.inner b (Q b) (B b))) x (W x) =
  --   g.inner x (cov.toFun Q x (W x)) (B x) + g.inner x (Q x) (cov.toFun B x (W x))
  -- Identify g.inner b (Q b) (B b) = abstractHessian g f b (B b, B b).
  have h_QB_section : (fun b : M => g.inner b (Q b) (B b)) =
      (fun b : M => abstractHessian (I := I) g f b (B b) (B b)) := by
    funext b
    have hQb : Q b = cov.toFun Gf b (B b) := rfl
    rw [hQb]
    -- abstractHessian g f b (B b) (B b) is by definition `cotangentCov ... extDerivFun f b (B b) (B b)`.
    -- And `g.inner b (cov Gf b (B b)) (B b) = abstractHessian g f b (B b) (B b)` by `inner_cov_gradFun_eq_abstractHessian`.
    -- This requires X = B and Y = B (smooth at b). Both are smooth.
    exact inner_cov_gradFun_eq_abstractHessian (I := I) g hf
      (X := B) (Y := B) (x := b) hB_smooth hB_smooth
  -- Substitute in hmc_QB.
  rw [show (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (Q b) (B b)) x) (W x) =
      (mfderiv I 𝓘(ℝ) (fun b : M =>
          abstractHessian (I := I) g f b (B b) (B b)) x) (W x) from by
    rw [h_QB_section]; rfl] at hmc_QB
  -- hmc_QB now says:
  --   (mfderiv ... (b ↦ Hess(B,B)(b))) x (W x) = g.inner x (cov.toFun Q x (W x)) (B x) + g.inner x (Q x) (cov.toFun B x (W x))
  -- Identify g.inner x (Q x) (cov.toFun B x (W x)) using inner_cov_gradFun_eq_abstractHessian + Hess sym.
  have h_QcovBW : g.inner x (Q x) (cov.toFun B x (W x)) =
      g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) := by
    have hQx_eq : Q x = cov.toFun Gf x (B x) := rfl
    rw [hQx_eq]
    -- LHS = g.inner x (cov Gf x (B x)) (cov B x (W x))
    -- RHS = g.inner x (cov Gf x (cov B x (W x))) (B x)
    -- This is inner_cov_gradFun_symm with X = B, Y = smoothExt (cov B x (W x)).
    set v : TangentSpace I x := cov.toFun B x (W x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    have h_sym := inner_cov_gradFun_symm (I := I) g hf
      (X := B) (Y := Xv) (x := x) hB_smooth hXv_smooth
    rw [show v = Xv x from hXv_eq.symm]
    exact h_sym
  -- Apply hmc_QB:
  -- (mfderiv ... (b ↦ Hess(B,B)(b))) x (W x) = g(LC Q x (W x), B x) + g(Q x, LC B x (W x))
  -- => g(LC Q x (W x), B x) = (mfderiv ...) - g(Q x, LC B x (W x))
  --                          = (mfderiv ...) - g(LC Gf x (LC B x (W x)), B x)
  have h_LCQW_B :
      g.inner x (cov.toFun Q x (W x)) (B x) =
        extDerivFun (I := I) (fun b : M =>
            abstractHessian (I := I) g f b (B b) (B b)) x (W x) -
          g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) := by
    -- Rewrite extDerivFun as mfderiv composition (definitionally `rfl` for ℝ-valued).
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
  -- Step 3: identify g(LC Gf x (LC B x (W x)), B x) with abstractHessian g f x (B x) (LC B x (W x)) via Hess sym.
  -- abstractHessian g f x (B x) (LC B x (W x)) = g(LC Gf x (B x), LC B x (W x))
  -- and by Hess sym = g(LC Gf x (LC B x (W x)), B x).
  have h_Hess_BcovBW :
      g.inner x (cov.toFun Gf x (cov.toFun B x (W x))) (B x) =
        abstractHessian (I := I) g f x (B x) (cov.toFun B x (W x)) := by
    -- We need: g(LC Gf x (LC B x (W x)), B x) = abstractHessian g f x (B x, LC B x (W x))
    -- = g(LC Gf x (B x), LC B x (W x)) by inner_cov_gradFun_eq_abstractHessian.
    -- Use inner_cov_gradFun_symm to swap.
    set v : TangentSpace I x := cov.toFun B x (W x) with hv_def
    set Xv : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hXv_def
    have hXv_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Xv) :=
      smoothExtensionTangent_contMDiff x v
    have hXv_eq : Xv x = v := smoothExtensionTangent_eq x v
    -- LHS = g.inner x (cov Gf x (Xv x)) (B x)
    --     = g.inner x (cov Gf x (B x)) (Xv x)   [by inner_cov_gradFun_symm with X=Xv, Y=B]
    --     = abstractHessian g f x (B x) (Xv x)  [by inner_cov_gradFun_eq_abstractHessian]
    --     = abstractHessian g f x (B x) v       [by hXv_eq]
    rw [show v = Xv x from hXv_eq.symm]
    rw [inner_cov_gradFun_eq_abstractHessian (I := I) g hf
        (X := Xv) (Y := B) (x := x) hXv_smooth hB_smooth]
    -- Goal: abstractHessian g f x (Xv x) (B x) = abstractHessian g f x (B x) (Xv x).
    exact (abstractHessian_symm (I := I) g (hf.contMDiffAt.of_le (by
      have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      simpa using h1)) (Xv x) (B x))
  -- Combine h_LCQW_B and h_Hess_BcovBW:
  -- g(LC Q x (W x), B x) = (mfderiv ...) - abstractHessian g f x (B x, LC B x (W x))
  rw [h_Hess_BcovBW] at h_LCQW_B
  -- Now combine with h_swap and h_riem.
  -- h_swap LHS = (Q-version) - (Gf at LC B B-version), all paired with W x.
  -- = (P-version paired with B x) - (Gf at LC W B-version, B x)   [from h_swap]
  -- = R + (LC Q W, B) - (LC Gf x (LC B W), B)   [from h_riem]
  -- Now substitute h_LCQW_B.
  -- Result:
  -- LHS = R + ((mfderiv) - Hess(B, LC B W)) - g(LC Gf x (LC B W), B)
  -- And g(LC Gf x (LC B W), B) = Hess(B, LC B W) by h_Hess_BcovBW.
  -- So: LHS = R + (mfderiv) - Hess(B, LC B W) - Hess(B, LC B W)
  --        = R + (mfderiv) - 2 Hess(B, LC B W).
  rw [h_swap, h_riem, h_LCQW_B, h_Hess_BcovBW]
  ring

/-! ## Main discharge theorem

The unconditional discharge of `IsHeartOfBochnerInnerAt`. Combines the per-summand
assembly `heart_per_summand_assembled` with the three closing facts:
- `heart_curvature_orthonormal_sum_eq_ricci`: curvature trace = Ricci tensor.
- `sum_abstractHessian_smoothOrthoFrame_eventuallyEq_laplacian`: Hessian trace =
  Laplacian on the orthonormal-frame neighborhood.
- `sum_abstractHessian_smoothOrthoFrame_cov_eq_zero`: connection-correction sum
  vanishes by antisymmetric × symmetric cancellation.
And `inner_ricciSharp` + `gradFun_metricDual_extDerivFun` to reformulate the result
in `ricciSharp` / `gradFun` form. -/

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
  -- Set up the smooth extension W of w at x.
  set W : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hW_def
  have hW_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W) :=
    smoothExtensionTangent_contMDiff x w
  have hW_eq : W x = w := smoothExtensionTangent_eq x w
  -- Step 1: rewrite g(connLap_∇ ∇f, w) using connLaplacian_grad_inner with hW_smooth.
  rw [show w = W x from hW_eq.symm]
  rw [connLaplacian_grad_inner (I := I) g hf hW_smooth x]
  -- Apply heart_per_summand_assembled per-summand.
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
  -- Distribute the sum: ∑ (a+b-c) = ∑a + ∑b - ∑c.
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
  -- Curvature sum: ∑_i g(R(B_i, W) ∇f, B_i x) = Ric(∇f x, w).
  -- Convert riemannSec to riemannOp.
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
      -- h_riemOp : riemannOp LC x (B_i x) (W x) (Gf x) = riemannSec LC B_i W Gf x.
      rw [show (smoothOrthoFrame (I := I) g x i x) =
              (smoothOrthoFrame (I := I) g x i) x from rfl,
          show w = W x from hW_eq.symm,
          show gradFun (I := I) g f x =
              (fun b => gradFun (I := I) g f b) x from rfl,
          h_riemOp]
    rw [Finset.sum_congr rfl (fun i _ => h_per_summand i)]
    exact heart_curvature_orthonormal_sum_eq_ricci (I := I) g hf x w
  rw [h_curv_sum_eq]
  -- Hessian trace differentiation:
  -- ∑_i extDerivFun (b ↦ Hess(B_i b, B_i b)) x (W x) = extDerivFun (Δ_g f) x w.
  -- We use sum_abstractHessian_smoothOrthoFrame_eventuallyEq_laplacian:
  -- (b ↦ ∑_i Hess(B_i b, B_i b)) =ᶠ[𝓝 x] Δ_g f.
  -- mfderiv of this at x agrees with mfderiv (Δ_g f) at x.
  have h_hess_sum_eventuallyEq :=
    sum_abstractHessian_smoothOrthoFrame_eventuallyEq_laplacian (I := I) g hf x
  -- We can pull the sum out of the mfderiv only when each summand is differentiable at x.
  -- But the cleaner approach: use extDerivFun_sum-style.
  -- Better: use the eventually-equal version. Construct the full target via Filter.EventuallyEq.
  -- (b ↦ ∑_i Hess(B_i b, B_i b)) =ᶠ[𝓝 x] (Δ_g f).
  -- Both are smooth functions of b near x. Their mfderiv at x agree. So:
  --   mfderiv (b ↦ ∑_i Hess(B_i b, B_i b)) x w = mfderiv (Δ_g f) x w
  --   = extDerivFun (Δ_g f) x w
  --   = g(grad(Δ_g f) x, w) (by gradFun_metricDual_extDerivFun).
  -- For the LHS: we need ∑_i extDerivFun (h_i) x (W x) = extDerivFun (∑_i h_i) x (W x).
  -- This requires mfderiv-distributivity over finite sums of (smooth) functions.
  -- Avoid that by reasoning at the level of the sum function directly.
  have h_extDerivFun_sum_eq :
      (∑ i : Fin (Module.finrank ℝ E),
          extDerivFun (I := I) (fun b : M =>
                    abstractHessian (I := I) g f b
                      (smoothOrthoFrame (I := I) g x i b)
                      (smoothOrthoFrame (I := I) g x i b)) x (W x)) =
      extDerivFun (I := I) (Δ_g (I := I) g hf) x w := by
    -- Each summand is locally `g.inner b (Q_i b) (B_i b)`, where Q_i is smooth at x.
    -- Each summand is `MDifferentiableAt I 𝓘(ℝ, ℝ) (b ↦ Hess(B_i b, B_i b)) x`.
    -- The sum of mfderivs equals mfderiv of the sum (for finite sums of MDiff funs).
    -- Then by the eventual equality, mfderiv of the sum equals mfderiv (Δ_g f).
    -- We show each summand differentiable via inner_cov_gradFun_eq_abstractHessian
    -- applied at varying points b.
    -- Alternative simpler path: identify each summand as `g.inner b (Q_i b) (B_i b)`
    -- via the section-level identity, then both summands have explicit smoothness via
    -- ContMDiffAt.inner_bundle / clm_bundle_apply.
    -- Each Q_i is differentiable at x.
    have hB_smooth : ∀ i : Fin (Module.finrank ℝ E),
        ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (smoothOrthoFrame (I := I) g x i)) :=
      fun i => smoothOrthoFrame_smooth (I := I) g x i
    have hGf_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun b => gradFun (I := I) g f b)) :=
      gradFun_contMDiff_total_section (I := I) g hf
    -- Each `b ↦ g.inner b (Q_i b) (B_i b)` is `C^∞`.
    -- We don't need full smoothness of the per-summand H_i at x — only differentiability.
    -- We just need MDifferentiableAt for each summand to apply HasMFDerivAt.sum.
    -- Each summand `b ↦ Hess(B_i b, B_i b)` equals `g.inner b (Q_i b) (B_i b)` (by
    -- inner_cov_gradFun_eq_abstractHessian); we obtain MDifferentiableAt from the
    -- metric-compatibility differentiability of inner products of differentiable sections.
    have h_each_diff : ∀ i : Fin (Module.finrank ℝ E),
        MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M =>
          abstractHessian (I := I) g f b
            (smoothOrthoFrame (I := I) g x i b)
            (smoothOrthoFrame (I := I) g x i b)) x := by
      intro i
      -- Convert via section-level identification: H_i = g.inner b (Q_i b) (B_i b).
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
      -- We need MDifferentiableAt at x for `b ↦ g.inner b (Q_i b) (B_i b)`.
      -- Use MDifferentiableAt.clm_bundle_apply₂ with the metric `g.inner` as
      -- a smooth bilinear-form section.
      have hQ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (T% (covApply (LeviCivita (I := I) g)
            (smoothOrthoFrame (I := I) g x i)
            (fun b' => gradFun (I := I) g f b'))) x :=
        covApply_mdifferentiableAt_local
          (cov := LeviCivita (I := I) g)
          ((hB_smooth i x).mdifferentiableAt (by simp))
          (by simpa using hGf_smooth)
      -- g.inner is smooth as a bilinear-form section of the bundle of bilinear forms.
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
      -- Extract the second component to get the scalar ℝ-valued differentiability.
      rw [mdifferentiableAt_totalSpace] at happ
      exact happ.2
    -- mfderiv distributes over finite sums (of smooth functions).
    -- Strategy: switch to extDerivFun (which has codomain `ℝ` directly, not
    -- `TangentSpace 𝓘(ℝ, ℝ) (f x)`). This avoids the dependent codomain issue.
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
      -- extDerivFun is additive (extDerivFun_add); apply by induction on the finset.
      induction (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        using Finset.induction_on with
      | empty => simp
      | @insert a s ha IH =>
        -- Take care of LHS: extDerivFun (b ↦ ∑ i ∈ insert a s, h_i b) x (W x).
        -- And RHS: ∑ i ∈ insert a s, extDerivFun (h_i) x (W x).
        -- Use Finset.sum_insert on RHS first.
        rw [Finset.sum_insert ha]
        -- Goal: extDerivFun (b ↦ ∑ i ∈ insert a s, h_i b) x (W x) =
        --       extDerivFun (h_a) x (W x) + ∑ i ∈ s, extDerivFun (h_i) x (W x).
        -- Now split the LHS sum.
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
        -- LHS = extDerivFun (b ↦ h_a b + ∑_{i∈s} h_i b) x (W x).
        -- Use the additive structure: (b ↦ h_a b + ∑_{i∈s} h_i b) = h_a + (b ↦ ∑_{i∈s} h_i b).
        -- Apply extDerivFun_add.
        have h_sum_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => ∑ i ∈ s,
              abstractHessian (I := I) g f b
                (smoothOrthoFrame (I := I) g x i b)
                (smoothOrthoFrame (I := I) g x i b)) x := by
          have h := MDifferentiableAt.sum (z := x) (t := s)
            (f := fun i b => abstractHessian (I := I) g f b
              (smoothOrthoFrame (I := I) g x i b)
              (smoothOrthoFrame (I := I) g x i b))
            (fun i _ => h_each_diff i)
          -- h has form `MDifferentiableAt I 𝓘(ℝ, ℝ) (∑ i ∈ s, fun b => h_i b) x`.
          -- We need it for `fun b => ∑ i ∈ s, h_i b`. They're equal:
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
    -- Use h_hess_sum_eventuallyEq + Filter.EventuallyEq.mfderiv_eq to identify
    -- the mfderiv of the sum with the mfderiv of Δ_g f.
    -- Then apply at W x.
    rw [← h_sum_mfderiv]
    -- Goal: extDerivFun (b ↦ ∑ i, h_i b) x (W x) = extDerivFun (Δ_g f) x w.
    -- Use h_hess_sum_eventuallyEq: (b ↦ ∑ i, h_i b) =ᶠ[𝓝 x] Δ_g f.
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
      -- Both sides equal at the corresponding base-point: (b ↦ ∑_i Hess(B_i, B_i))(x) =
      -- Δ_g f x (by sum_abstractHessian_smoothOrthoFrame_eq_laplacian).
      -- So the `fromTangentSpace` casts are compatible.
      have h_base_eq : (fun b : M => ∑ i : Fin (Module.finrank ℝ E),
                  abstractHessian (I := I) g f b
                    (smoothOrthoFrame (I := I) g x i b)
                    (smoothOrthoFrame (I := I) g x i b)) x =
          Δ_g (I := I) g hf x := by
        exact h_hess_sum_eventuallyEq.self_of_nhds
      rw [h_mf_eq]
      -- The `fromTangentSpace`-CLM depends on the base-point value `(f x)`;
      -- with both base values equal (h_base_eq), the casts are equal.
      congr 1
    rw [h_extDerivFun_eq, hW_eq]
  rw [h_extDerivFun_sum_eq]
  -- Hessian-skew sum vanishing.
  -- ∑_i abstractHessian g f x (B_i x, LC B_i x (W x)) = 0
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          abstractHessian (I := I) g f x
            (smoothOrthoFrame (I := I) g x i x)
            ((LeviCivita (I := I) g).toFun
              (smoothOrthoFrame (I := I) g x i) x (W x))) = 0 from by
    rw [hW_eq]
    exact sum_abstractHessian_smoothOrthoFrame_cov_eq_zero (I := I) g hf x w]
  -- Now the residual goal: extDerivFun (Δ_g f) x w + Ric(∇f, w) - 2*0 = ...
  -- Convert extDerivFun (Δ_g f) x w to g(grad(Δ_g f), w) via gradFun_metricDual_extDerivFun.
  rw [show extDerivFun (I := I) (Δ_g (I := I) g hf) x w =
        g.inner x (gradFun (I := I) g (Δ_g (I := I) g hf) x) w from
    (gradFun_metricDual_extDerivFun (I := I) g (Δ_g (I := I) g hf) x w).symm]
  -- Convert Ric(∇f x, w) to g(ricciSharp g x (∇f x), w) via inner_ricciSharp.
  rw [show ricciTensor (I := I) g x (gradFun (I := I) g f x) w =
        g.inner x (ricciSharp (I := I) g x (gradFun (I := I) g f x)) w from
    (inner_ricciSharp (I := I) g x (gradFun (I := I) g f x) w).symm]
  -- The RHS still has `W x` from the initial substitution; revert to `w`.
  rw [hW_eq]
  -- Final goal: g(grad(Δf), w) + g(ricciSharp(∇f), w) - 0 = g(grad(Δf), w) + g(ricciSharp(∇f), w).
  ring

/-! ## Truly unconditional Bochner identity

Combining `hLeibniz_discharge` and `hInner_discharge` gives the truly unconditional
pointwise Bochner-Weitzenböck identity, with no algebraic-input hypotheses. -/

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
