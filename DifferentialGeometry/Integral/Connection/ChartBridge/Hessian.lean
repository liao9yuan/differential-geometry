import DifferentialGeometry.Integral.Connection.RicciIdentity
import DifferentialGeometry.Integral.Connection.ChartBridge.Gradient

/-!
# Bridge between the chart Hessian carrier and the Levi-Civita Hessian

The chart Hessian carrier `hessFun g f : pointwiseBilin I` (defined in
`Integral.Geometry.Hessian`) is the bilinear form on the tangent bundle whose
matrix in the chart basis is the chart Hessian tensor
$$
  (\operatorname{Hess} f)_{ij}(x) = \partial_i \partial_j (f \circ \varphi_x^{-1})(\varphi_x x)
    - \sum_k \Gamma^k{}_{ij}(g, x)(\varphi_x x) \cdot
        \partial_k (f \circ \varphi_x^{-1})(\varphi_x x).
$$

The abstract Hessian `abstractHessian g f x v w` (defined in
`Integral.Connection.TensorExtension`) is the (0,2)-tensor at `x` obtained by applying the
cotangent extension of the Levi-Civita connection to the differential `df = extDerivFun f`:
$$
  \operatorname{Hess}_{LC} f(x)(v, w) :=
    \bigl((\nabla^*_v\,(\mathrm{d} f))_x\bigr)(w) =
    \bigl((\mathrm{cotangentCov}\,(\nabla^{LC})\,(\mathrm{d} f))(x, v)\bigr)(w).
$$

The abstract Hessian is symmetric (`abstractHessian_symm`, proved in `TensorExtension`) and
agrees on smooth tangent sections with the inner product of the gradient's Levi-Civita
covariant derivative against a test vector
(`inner_cov_gradFun_eq_abstractHessian`, proved in `RicciIdentity`).

This bridge file packages the abstract Hessian as a `pointwiseBilin` and exposes the
identification with the chart Hessian carrier through the inner-product / gradient
connection. The key statement is the **pointwise gradient–Hessian identity**:
$$
  g_x\bigl(\nabla^{LC}_v\,(\nabla f),\, w\bigr) = \mathrm{abstractHessian}\,g\,f\,x\,v\,w
$$
for *arbitrary* tangent vectors `v, w ∈ T_x M`. Together with `abstractHessian_symm` this is
the engine identity feeding the downstream consumers (Laplacian = trace bridge, Hessian
Frobenius bridge, Bochner identity).

## Main definitions

* `abstractHessianLin g f x : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ` —
  the LinearMap form of `abstractHessian g f x`. Definitionally, `LinearMap.toContinuousLinearMap`
  in reverse, so the two are pointwise equal.
* `abstractHessianBilin g f` — the bundled `pointwiseBilin I` carrier built from
  `abstractHessianLin g f`. Suitable for direct consumption by `traceFun`, `frobeniusSqFun`,
  and the Cauchy-Schwarz Bochner inequality.

## Main theorems

* `abstractHessianLin_apply` — pointwise equality `abstractHessianLin g f x v w =
  abstractHessian g f x v w`.
* `abstractHessianLin_symm` — the bilinear-form symmetry
  `abstractHessianLin g f x v w = abstractHessianLin g f x w v` for `f` of class `C²`.
* `abstractHessianBilin_isPointwiseSymm` — the carrier-level symmetry, ready for clients
  that consume `IsPointwiseSymm` predicates.
* `abstractHessian_eq_inner_cov_gradFun_extend` — for any `v w : TangentSpace I x` and
  smooth `f`, `abstractHessian g f x v w = g.inner x ((LeviCivita g) (gradFun g f) x v) w`
  (using `FiberBundle.extend` to provide local smooth extensions). This is the
  arbitrary-`v`-`w` form of `inner_cov_gradFun_eq_abstractHessian`.
* `abstractHessian_eq_inner_cov_gradFun_smooth` — the smooth-section form:
  `inner_cov_gradFun_eq_abstractHessian` re-exported.
* `traceFun_abstractHessianBilin_def` — unfolding identity for `traceFun
  (abstractHessianBilin g f)` in terms of the model-basis sum.
* `frobeniusSqFun_abstractHessianBilin_def` — unfolding identity for `frobeniusSqFun
  (abstractHessianBilin g f)` in terms of the model-basis sum of squares.
* `traceFun_abstractHessianBilin_sq_le_dim_mul_frobeniusSqFun` — the Cauchy-Schwarz
  Bochner-Lichnerowicz inequality for the abstract Hessian.

The chart-coordinate identification `chartHessianTensor g x f i j x` of the matrix entries
`abstractHessianLin g f x e_i e_j` (where `e := chartModelBasis E`) requires unfolding the
chart Christoffel formula for the Levi-Civita connection at the chart base point. That deep
chart-formula identification is the subject of a separate downstream development; this file
provides the bridge layer that consumes it once available.
-/

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-! ## The `LinearMap` view of `abstractHessian`

The abstract Hessian `abstractHessian g f x : T_x M →L[ℝ] T_x M →L[ℝ] ℝ` is a continuous
bilinear form. Downstream consumers that work with `pointwiseBilin I = ∀ x, T_x M →ₗ[ℝ] T_x
M →ₗ[ℝ] ℝ` (the carrier defined in `Geometry.Hessian`) need its `LinearMap` form.

`abstractHessianLin g f x` is built directly from the CLM form by stripping the continuity
on each side, using `ContinuousLinearMap.toLinearMap` twice. The bilinearity is preserved
on the nose; the values agree pointwise. -/

/-- **`LinearMap` form of `abstractHessian`.** Strips the continuity tags on the two outer
arguments of `abstractHessian g f x`, leaving a pure bilinear LinearMap suitable for the
`pointwiseBilin` carrier. -/
def abstractHessianLin (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  let L : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
    abstractHessian (I := I) g f x
  { toFun := fun v =>
      { toFun := fun w => L v w
        map_add' := fun w₁ w₂ => by simp
        map_smul' := fun c w => by simp }
    map_add' := fun v₁ v₂ => by
      ext w
      change L (v₁ + v₂) w = L v₁ w + L v₂ w
      rw [map_add]; rfl
    map_smul' := fun c v => by
      ext w
      change L (c • v) w = c * L v w
      rw [map_smul]; rfl }

@[simp] lemma abstractHessianLin_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    abstractHessianLin (I := I) g f x v w =
      abstractHessian (I := I) g f x v w := rfl

/-! ## The `pointwiseBilin` carrier of the abstract Hessian

We package `abstractHessianLin g f` into a single `pointwiseBilin I` value. This is the
form consumed by `traceFun`, `frobeniusSqFun`, and the Cauchy-Schwarz Bochner inequality. -/

/-- **Bundled `pointwiseBilin` carrier of the abstract Hessian.** -/
def abstractHessianBilin (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    pointwiseBilin (M := M) I :=
  fun x => abstractHessianLin (I := I) g f x

@[simp] lemma abstractHessianBilin_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    abstractHessianBilin (I := I) g f x v w =
      abstractHessian (I := I) g f x v w := rfl

/-! ## Symmetry of the abstract Hessian, in carrier form

We now restate `abstractHessian_symm` in the language of the `pointwiseBilin` carrier. -/

/-- **Symmetry of `abstractHessianLin`.** For a function `f : M → ℝ` of class `C²` at `x`,
the LinearMap form of the abstract Hessian is symmetric in its two slots:
`abstractHessianLin g f x v w = abstractHessianLin g f x w v`. -/
theorem abstractHessianLin_symm
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (v w : TangentSpace I x) :
    abstractHessianLin (I := I) g f x v w =
      abstractHessianLin (I := I) g f x w v :=
  abstractHessian_symm (I := I) g hf v w

/-- **Carrier-level symmetry of `abstractHessianBilin`** for `f : M → ℝ` of class `C²`. -/
theorem abstractHessianBilin_isPointwiseSymm
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    IsPointwiseSymm (abstractHessianBilin (I := I) (M := M) g f) := by
  intro x v w
  apply abstractHessianLin_symm (I := I) g
  exact (hf.contMDiffAt).of_le (by
    -- 2 ≤ ∞ in `WithTop ℕ∞`.
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1)

/-! ## Pointwise inner-product / gradient-flow identity

The abstract Hessian admits a useful inner-product representation: at a point `x` and on a
pair of tangent vectors `v, w`, it equals `g.inner x (∇^{LC}_v (∇f)) w`, the inner product
of the Levi-Civita covariant derivative of the gradient (along `v`) against `w`.

The smooth-section form `inner_cov_gradFun_eq_abstractHessian` (proved in `RicciIdentity`)
requires globally smooth tangent fields `X, Y` with `X x = v` and `Y x = w`. We extend it
to **arbitrary** `v, w` by smoothly extending each via Mathlib's `FiberBundle.extend`
construction, then re-using the proof structure with the local-only smoothness data
(`MDiffAt`, `MDiffAtCotangent`). -/

/-- **Pointwise inner-product / gradient-flow identity for `abstractHessian`.**
For any tangent vectors `v, w ∈ T_x M`,
`g.inner x ((LeviCivita g) (gradFun g f) x v) w = abstractHessian g f x v w`.
This is the arbitrary-input form of `inner_cov_gradFun_eq_abstractHessian`; the smooth
extensions are constructed internally via `FiberBundle.extend`. -/
theorem abstractHessian_eq_inner_cov_gradFun_extend [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) (v w : TangentSpace I x) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x v) w =
      abstractHessian (I := I) g f x v w := by
  classical
  -- Use `FiberBundle.extend` to produce smooth sections `V, W` with `V x = v`, `W x = w`.
  set V : Π b : M, TangentSpace I b := FiberBundle.extend E v with hV_def
  set W : Π b : M, TangentSpace I b := FiberBundle.extend E w with hW_def
  have hVx : V x = v := by simp [V]
  have hWx : W x = w := by simp [W]
  have hV_at : MDiffAt (T% V) x := mdifferentiableAt_extend ..
  have hW_at : MDiffAt (T% W) x := mdifferentiableAt_extend ..
  -- The proof now mirrors `inner_cov_gradFun_eq_abstractHessian`, but with `MDiffAt`-only
  -- hypotheses. We re-derive the full chain inline.
  set cov := LeviCivita (I := I) g with hcov
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f with hθ_def
  -- Smoothness of `gradFun g f` as a tangent section.
  have h_grad_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        (gradFun (I := I) g f y)) :=
    gradFun_contMDiff_total_section (I := I) g hf
  have h_grad_at : MDiffAt (T% (fun b => gradFun (I := I) g f b)) x :=
    (h_grad_smooth x).mdifferentiableAt (by simp)
  -- Smoothness of θ = extDerivFun f at x.
  have hθ_at : MDiffAtCotangent θ x := by
    have hext_smooth :=
      cotangentCov_extDerivFun_smooth (I := I) hf
    exact (hext_smooth x).mdifferentiableAt (by simp)
  -- The two dual-pairing identities at the chosen tangent vectors.
  have hpair_W := cotangentCov_dualPairing cov hθ_at hW_at v
  -- hpair_W : extDerivFun (b => θ b (W b)) x v
  --             = ((cotangentCov cov) θ x v) (W x) + θ x (cov W x v)
  -- We want the identity on (v, w), i.e. with W x = w. So we'll use hpair_V_via_grad and
  -- hpair_W in tandem. Specifically, hpair_W is the right shape directly.
  -- Function-level identity used in metric compatibility step.
  have h_eq_fn : (fun b : M => extDerivFun (I := I) f b (W b)) =
      (fun b : M => g.inner b (gradFun (I := I) g f b) (W b)) := by
    funext b
    exact (gradFun_metricDual_extDerivFun (I := I) g f b (W b)).symm
  -- Metric-compatibility identity for the function b ↦ g.inner b (grad f b) (W b).
  have hmc :=
    (LeviCivita_isMetricCompatible (I := I) g).apply h_grad_at hW_at v
  -- Convert `mfderiv` to `extDerivFun`.
  have hmc' : extDerivFun (I := I) (fun b => g.inner b (gradFun (I := I) g f b) (W b)) x v =
      g.inner x (cov.toFun (fun b => gradFun (I := I) g f b) x v) (W x) +
        g.inner x (gradFun (I := I) g f x) (cov.toFun W x v) := by
    have hext_eq : extDerivFun (I := I)
        (fun b => g.inner b (gradFun (I := I) g f b) (W b)) x v =
          (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (gradFun (I := I) g f b) (W b)) x) v := rfl
    rw [hext_eq, hmc]
  -- The LHS of hpair_W can be rewritten using h_eq_fn:
  have h_lhs_eq : extDerivFun (I := I) (fun b : M => θ b (W b)) x v =
      extDerivFun (I := I) (fun b : M => g.inner b (gradFun (I := I) g f b) (W b)) x v := by
    have h_eq : (fun b : M => θ b (W b)) =
        (fun b : M => g.inner b (gradFun (I := I) g f b) (W b)) := h_eq_fn
    rw [h_eq]
  rw [h_lhs_eq] at hpair_W
  -- The third term in hmc' is g.inner x (grad f x) (cov W x v) = θ x (cov W x v).
  have h_grad_inner :
      g.inner x (gradFun (I := I) g f x) (cov.toFun W x v) =
        θ x (cov.toFun W x v) := by
    rw [gradFun_metricDual_extDerivFun (I := I) g f x (cov.toFun W x v)]
  -- Equating hmc' and hpair_W (both equal extDerivFun (...) x v) and simplifying:
  have hkey :
      g.inner x (cov.toFun (fun b => gradFun (I := I) g f b) x v) (W x) =
        ((cotangentCov cov).toFun θ x v) (W x) := by
    have hlhs := hmc'
    rw [h_grad_inner] at hlhs
    -- hlhs : LHS = g.inner x (cov (grad f) x v) (W x) + θ x (cov W x v)
    -- hpair_W : LHS = ((cotangentCov cov) θ x v) (W x) + θ x (cov W x v)
    have h := hlhs.symm.trans hpair_W
    linarith [h]
  -- Finally substitute W x = w on both sides.
  rw [hWx] at hkey
  rw [hkey]
  -- The RHS is `abstractHessian g f x v w`, by definition.
  rfl

/-- **Smooth-section form of the gradient-flow identity** (re-export of
`inner_cov_gradFun_eq_abstractHessian`). For smooth tangent fields `X, Y` and any `x : M`,
`g.inner x ((LeviCivita g) (gradFun g f) x (X x)) (Y x) = abstractHessian g f x (X x) (Y x)`. -/
theorem abstractHessian_eq_inner_cov_gradFun_smooth [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    g.inner x ((LeviCivita (I := I) g).toFun
                  (fun b => gradFun (I := I) g f b) x (X x)) (Y x) =
      abstractHessian (I := I) g f x (X x) (Y x) :=
  inner_cov_gradFun_eq_abstractHessian (I := I) g hf hX hY

/-! ## `traceFun` and `frobeniusSqFun` of the abstract-Hessian carrier

We unfold the carrier-level `traceFun` and `frobeniusSqFun` for the abstract Hessian. Both
are computed against the canonical model basis `chartModelBasis E` and consume the values
`abstractHessian g f x e_i e_j` (with `e := chartModelBasis E`) on the diagonal and
off-diagonal entries respectively. -/

/-- The basis-naive trace of the abstract Hessian carrier in the canonical model basis. -/
@[simp] lemma traceFun_abstractHessianBilin_def
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      ∑ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g f x
          ((chartModelBasis E) i) ((chartModelBasis E) i) := by
  unfold traceFun
  rfl

/-- The basis-naive Frobenius norm squared of the abstract Hessian carrier in the canonical
model basis. -/
@[simp] lemma frobeniusSqFun_abstractHessianBilin_def
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (abstractHessian (I := I) g f x
            ((chartModelBasis E) i) ((chartModelBasis E) j))^2 := by
  unfold frobeniusSqFun
  rfl

/-! ## Cauchy-Schwarz Bochner inequality for the abstract Hessian

Combining the carrier-level `traceFun_sq_le_dim_mul_frobeniusSqFun` with the unfolding
identities above, we obtain the basis-naive Cauchy-Schwarz inequality
`(traceFun H x)² ≤ n · frobeniusSqFun H x` for `H = abstractHessianBilin g f`. -/

/-- **Cauchy-Schwarz Bochner inequality for the abstract Hessian (basis-naive form).** The
square of the basis-naive trace is bounded by the dimension times the basis-naive Frobenius
norm squared. The inequality holds with no orthonormality hypothesis on the basis: this is
a pure linear-algebra Cauchy-Schwarz. -/
theorem traceFun_abstractHessianBilin_sq_le_dim_mul_frobeniusSqFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    (traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
  traceFun_sq_le_dim_mul_frobeniusSqFun
    (I := I) (M := M) (abstractHessianBilin (I := I) g f) x

/-- **Divided form** of the Cauchy-Schwarz Bochner inequality for the abstract Hessian. -/
theorem traceFun_abstractHessianBilin_sq_div_dim_le_frobeniusSqFun
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    (traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x)^2 /
      (Module.finrank ℝ E : ℝ) ≤
      frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
  traceFun_sq_div_dim_le_frobeniusSqFun
    (I := I) (M := M) (abstractHessianBilin (I := I) g f) x

/-! ## Bridge to the chart Hessian carrier `hessFun`

The chart Hessian carrier `hessFun g f : pointwiseBilin I` is defined in
`Geometry.Hessian` by the matrix entries `chartHessianTensor g x f i j x` (with
chart basepoint `α = x`, evaluated at the manifold point `x`). The two carriers
`hessFun g f` and `abstractHessianBilin g f` agree as bilinear forms on the tangent space
*if and only if* their matrix entries against the model basis agree, i.e. iff
$$
  \mathrm{abstractHessian}\,g\,f\,x\,e_i\,e_j = \mathrm{chartHessianTensor}\,g\,x\,f\,i\,j\,x.
$$

This identification is the **chart-coordinate formula for the Levi-Civita Hessian** at the
chart base point. The proof requires unfolding the Levi-Civita connection along its
chart-Christoffel formula (`LeviCivita_chart_apply`) and then matching the resulting
expression with `chartHessianTensor`. We expose the bridge **statement** here as an
abstract `Prop` predicate `chartHessianMatrixIdentity g f x` and the consequences
that follow from it, deferring the full chart-formula proof to a separate downstream
development.

The basic consequences are:

* `hessFun_eq_abstractHessianBilin_of_matrix_identity` — under the matrix-entry identity,
  the two carriers agree as bilinear forms.
* `traceFun_hessFun_eq_traceFun_abstractHessianBilin_of_matrix_identity` — the trace of
  the chart Hessian carrier equals the trace of the abstract Hessian carrier.
* `frobeniusSqFun_hessFun_eq_frobeniusSqFun_abstractHessianBilin_of_matrix_identity` — and
  the Frobenius squared.

Once a downstream task discharges `chartHessianMatrixIdentity g f x` (it is purely a
chart-coordinate-formula identity for the Levi-Civita connection), all of the chart
Hessian's `traceFun` and `frobeniusSqFun` reductions transfer to the abstract Hessian. -/

/-- The matrix-entry identity bridging the abstract Hessian and the chart Hessian
tensor on the canonical model basis: `abstractHessian g f x e_i e_j = chartHessianTensor g
x f i j x` for all `i, j`. -/
def chartHessianMatrixIdentity
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) : Prop :=
  ∀ i j : Fin (Module.finrank ℝ E),
    abstractHessian (I := I) g f x
        ((chartModelBasis E) i) ((chartModelBasis E) j) =
      chartHessianTensor (I := I) g x f i j x

/-- Under `chartHessianMatrixIdentity g f x`, the chart Hessian carrier `hessFun g f x`
agrees with the abstract Hessian carrier `abstractHessianBilin g f x` as bilinear forms on
the tangent space at `x`. -/
theorem hessFun_eq_abstractHessianBilin_of_matrix_identity
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (hM : chartHessianMatrixIdentity (I := I) g f x)
    (v w : TangentSpace I x) :
    hessFun (I := I) g f x v w =
      abstractHessianBilin (I := I) g f x v w := by
  classical
  -- Both sides are bilinear in (v, w) on T_x M; we check matrix entries via the model basis.
  -- LHS (chart-Hessian carrier): ∑ i j, v^i w^j H_{ij}(x, x).
  rw [hessFun_apply]
  -- RHS: abstractHessian g f x v w. Decompose v, w in the model basis, then expand both
  -- sides in the same way and match term-by-term using `hM`.
  rw [abstractHessianBilin_apply]
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E with hb_def
  -- The first slot is a continuous linear map T_x M →L[ℝ] (T_x M →L[ℝ] ℝ).
  -- The second slot is a continuous linear map T_x M →L[ℝ] ℝ. Both are linear, so the
  -- value `(absH x v) w` decomposes via the basis representations of v and w.
  -- Step 1: bilinearity of the CLM-evaluated form `(absH x v) w` as a function of (v, w).
  have h_abs : abstractHessian (I := I) g f x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (b.repr v i * b.repr w j) *
            abstractHessian (I := I) g f x (b i) (b j) := by
    -- Decompose v in the model basis: `v = ∑ i, v^i • b i`.
    have hv_decomp : v = ∑ i : Fin (Module.finrank ℝ E), b.repr v i • b i :=
      (Module.Basis.sum_repr b v).symm
    have hw_decomp : w = ∑ j : Fin (Module.finrank ℝ E), b.repr w j • b j :=
      (Module.Basis.sum_repr b w).symm
    -- Apply the CLM `abstractHessian g f x` to the v-decomposition. We use `congrArg`
    -- to introduce the basis sum form and then map_sum to distribute.
    have h1 : abstractHessian (I := I) g f x v =
        ∑ i : Fin (Module.finrank ℝ E),
          b.repr v i • abstractHessian (I := I) g f x (b i) := by
      have happ_eq : abstractHessian (I := I) g f x v =
          abstractHessian (I := I) g f x
            (∑ i : Fin (Module.finrank ℝ E), b.repr v i • b i) :=
        congrArg (abstractHessian (I := I) g f x) hv_decomp
      rw [happ_eq, map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      exact (abstractHessian (I := I) g f x).map_smul (b.repr v i) (b i)
    -- Apply each summand to w; this is now a sum of scalars.
    have h2 : abstractHessian (I := I) g f x v w =
        ∑ i : Fin (Module.finrank ℝ E),
          b.repr v i • abstractHessian (I := I) g f x (b i) w := by
      rw [h1]
      rw [ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rfl
    -- Now decompose each `abstractHessian g f x (b i) w` using the w-decomposition.
    have h3 : ∀ i : Fin (Module.finrank ℝ E),
        abstractHessian (I := I) g f x (b i) w =
          ∑ j : Fin (Module.finrank ℝ E),
            b.repr w j • abstractHessian (I := I) g f x (b i) (b j) := by
      intro i
      have happ_eq : abstractHessian (I := I) g f x (b i) w =
          abstractHessian (I := I) g f x (b i)
            (∑ j : Fin (Module.finrank ℝ E), b.repr w j • b j) :=
        congrArg (abstractHessian (I := I) g f x (b i)) hw_decomp
      rw [happ_eq, map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      exact (abstractHessian (I := I) g f x (b i)).map_smul (b.repr w j) (b j)
    -- Combine h2 and h3.
    rw [h2]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [h3 i]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [smul_eq_mul, smul_eq_mul]
    ring
  -- Now substitute `hM` to rewrite each `abstractHessian (b i) (b j)` as
  -- `chartHessianTensor i j`. The two sums then match term-by-term.
  rw [h_abs]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hM i j, mul_assoc]

/-- Under `chartHessianMatrixIdentity g f x`, the chart trace of the chart Hessian carrier
`traceFun (hessFun g f) x` agrees with the basis-naive trace of the abstract Hessian
carrier `traceFun (abstractHessianBilin g f) x`. -/
theorem traceFun_hessFun_eq_traceFun_abstractHessianBilin_of_matrix_identity
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (hM : chartHessianMatrixIdentity (I := I) g f x) :
    traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      traceFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x := by
  classical
  unfold traceFun
  refine Finset.sum_congr rfl ?_
  intro i _
  exact hessFun_eq_abstractHessianBilin_of_matrix_identity (I := I) g f x hM
    ((chartModelBasis E) i) ((chartModelBasis E) i)

/-- Under `chartHessianMatrixIdentity g f x`, the basis-naive Frobenius squared of the
chart Hessian carrier `frobeniusSqFun (hessFun g f) x` agrees with the basis-naive
Frobenius squared of the abstract Hessian carrier
`frobeniusSqFun (abstractHessianBilin g f) x`. -/
theorem frobeniusSqFun_hessFun_eq_frobeniusSqFun_abstractHessianBilin_of_matrix_identity
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (hM : chartHessianMatrixIdentity (I := I) g f x) :
    frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x =
      frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x := by
  classical
  unfold frobeniusSqFun
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hessFun_eq_abstractHessianBilin_of_matrix_identity (I := I) g f x hM
    ((chartModelBasis E) i) ((chartModelBasis E) j)]

/-! ## Direct chart-Hessian-tensor identity from the gradient-flow form

When the matrix-identity hypothesis is available, we can also restate the chart Hessian
matrix entries in terms of the gradient-flow inner product: this is the form used in
applications where the chart Christoffel symbols are not directly accessible. -/

/-- Under `chartHessianMatrixIdentity`, the chart Hessian matrix entry equals the inner
product of the Levi-Civita gradient-derivative against the corresponding model-basis
vector. -/
theorem chartHessianTensor_eq_inner_cov_gradFun_basis_of_matrix_identity
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (hM : chartHessianMatrixIdentity (I := I) g f x)
    (i j : Fin (Module.finrank ℝ E)) :
    chartHessianTensor (I := I) g x f i j x =
      g.inner x ((LeviCivita (I := I) g).toFun
                    (fun b => gradFun (I := I) g f b) x ((chartModelBasis E) i))
        ((chartModelBasis E) j) := by
  rw [← hM i j]
  exact (abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf x
    ((chartModelBasis E) i) ((chartModelBasis E) j)).symm

/-! ## Chart-formula proof of the matrix identity

We now discharge `chartHessianMatrixIdentity g f x` directly, by unfolding the abstract
Hessian using `cotangentCov_dualPairing`, the chart-local Levi-Civita formula
(`chartLeviCivita_apply`), the trivialization round-trip identities at the chart
basepoint (`trivToE α α = id`, `trivFromE α α = id`), and the chart-pulled-back form
of `mfderiv` (`mfderiv_scalar_eq_chart_fderiv`). The matching identifies each ingredient
with its chart-coordinate counterpart:

* the second-derivative term of `b ↦ θ b (Y b)` along `e_i` (with `Y x = e_j`) becomes the
  iterated partial `∂_i ∂_j (f ∘ φ.symm)(φ x)`;
* the Levi-Civita correction `θ x (∇_{e_i} Y x)` becomes the Christoffel sum
  `∑_k Γ^k{}_{ij}(φ x) ∂_k (f ∘ φ.symm)(φ x)`.

The two combine to `chartHessianTensor g x f i j x`.

The infrastructure consists of a small set of basepoint identities for the canonical
tangent-bundle trivialization, the chart-basis section, and a chart-pulled-back form
of the dual-pairing scalar. -/

/-! ### Trivialization at the basepoint is the identity -/

/-- At the chart basepoint, the canonical tangent-bundle trivialization is the identity
on `E` (using the defeq `TangentSpace I x = E`). This combines
`TangentBundle.continuousLinearMapAt_trivializationAt` with `mfderiv_extChartAt_self`. -/
lemma trivToE_self_eq_id (x : M) :
    (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  classical
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
    (x₀ := x) (x := x) (mem_chart_source H x)
  rw [show (trivToE (I := I) x x : TangentSpace I x →L[ℝ] E) =
        (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x from rfl]
  rw [h]
  exact mfderiv_extChartAt_self (I := I) (x := x)

/-- Pointwise form of `trivToE_self_eq_id`. -/
lemma trivToE_self_apply (x : M) (v : TangentSpace I x) :
    trivToE (I := I) x x v = v := by
  rw [trivToE_self_eq_id (I := I) x]
  rfl

/-- At the chart basepoint, the canonical tangent-bundle inverse trivialization is the
identity on `E`. This follows from `trivToE_self_eq_id` and the round-trip identity. -/
lemma trivFromE_self_apply (x : M) (w : E) :
    trivFromE (I := I) x x w = w := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  -- Use the round-trip: `trivToE x x (trivFromE x x w) = w`, and `trivToE x x` is the
  -- identity by `trivToE_self_apply`, so the round-trip becomes `trivFromE x x w = w`.
  have h := trivToE_trivFromE (I := I) x hbase w
  rwa [trivToE_self_apply (I := I) x (trivFromE (I := I) x x w)] at h

/-- At the chart basepoint, the `i`-th chart-basis fibre vector equals the `i`-th
model-space basis vector. -/
lemma chartBasisVecFiber_self
    (x : M) (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) x i x = (chartModelBasis E) i := by
  unfold chartBasisVecFiber
  -- `chartBasisVecFiber x i x = (trivializationAt _ _ x).symm x ((chartModelBasis E) i)`,
  -- and on the base set `T.symm x = T.symmL ℝ x = trivFromE x x` (definitionally).
  change trivFromE (I := I) x x ((chartModelBasis E) i) = (chartModelBasis E) i
  exact trivFromE_self_apply (I := I) x ((chartModelBasis E) i)

/-! ### `chartE_section_repr` of `chartBasisVec` is locally constant -/

/-- For `b` in the trivialization base set at `x`, the chart-trivialised representation
of the chart-basis section `chartBasisVec x j` evaluates to the constant model-basis
vector `e_j`. -/
private lemma chartE_section_repr_chartBasisVec_apply
    (x : M) (j : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    chartE_section_repr (I := I) x
        (fun y : M => chartBasisVecFiber (I := I) x j y) b =
      (chartModelBasis E) j := by
  classical
  unfold chartE_section_repr
  -- `chartE_section_repr x σ b = trivToE x b (σ b)` and
  -- `trivToE x b (chartBasisVecFiber x j b) = (chartModelBasis E) j` for `b ∈ baseSet`.
  change trivToE (I := I) x b (chartBasisVecFiber (I := I) x j b) =
    (chartModelBasis E) j
  -- The trivialization composed with its inverse on `e_j ∈ E` gives `e_j`.
  have h := trivToE_trivFromE (I := I) x hb ((chartModelBasis E) j)
  -- `chartBasisVecFiber x j b = trivFromE x b ((chartModelBasis E) j)` by definition.
  have heq : chartBasisVecFiber (I := I) x j b =
      trivFromE (I := I) x b ((chartModelBasis E) j) := rfl
  rw [heq]
  exact h

/-- The chart-trivialised representation of the chart-basis section as a function on
`E`, pulled back through `extChartAt I x` inverse, is locally constant on
`(extChartAt I x).target` (when restricted to `φ.symm`-image of the base set). -/
private lemma chartE_section_repr_chartBasisVec_pullback_constOn
    (x : M) (j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : (extChartAt I x).symm y ∈
        (trivializationAt E (TangentSpace I) x).baseSet) :
    (chartE_section_repr (I := I) x
        (fun b : M => chartBasisVecFiber (I := I) x j b) ∘ (extChartAt I x).symm) y =
      (chartModelBasis E) j := by
  classical
  change chartE_section_repr (I := I) x
      (fun b : M => chartBasisVecFiber (I := I) x j b) ((extChartAt I x).symm y) =
    (chartModelBasis E) j
  exact chartE_section_repr_chartBasisVec_apply (I := I) x j hy

/-! ### Smoothness of the chart-basis section at the basepoint -/

/-- The chart-basis section `chartBasisVec x j`, viewed as a tangent-bundle section,
is `MDifferentiableAt I (I.prod 𝓘(ℝ, E))` at every point of the trivialization base set,
in particular at the basepoint `x`. -/
private lemma chartBasisVec_mdifferentiableAt_self
    (x : M) (j : Fin (Module.finrank ℝ E)) :
    MDiffAt (T% (fun b : M => chartBasisVecFiber (I := I) x j b)) x := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have hcontMDiff_on :=
    chartBasisVec_contMDiffOn (I := I) x j
  have hopen : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  -- Use `ContMDiffAt` from `ContMDiffOn` on an open set.
  have hcontMDiff_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (chartBasisVec (I := I) x j) x :=
    (hcontMDiff_on x hbase).contMDiffAt (hopen.mem_nhds hbase)
  -- Convert to `MDifferentiableAt`.
  exact hcontMDiff_at.mdifferentiableAt (by simp)

/-! ### Pullback identification of `θ b (Y b)` for `Y = chartBasisVec x j`

For `b` in the chart source at `x`, the scalar `θ b (Y b) = mfderiv f b (Y b)` equals
the chart-pulled-back partial derivative `partialDeriv j (scalarOnE x f) (φ b)`. -/

/-- For `b` in the chart source at `x`, the dual-pairing scalar
`(extDerivFun f) b (chartBasisVecFiber x j b)` equals
`partialDeriv j (scalarOnE x f) (extChartAt I x b)`. -/
private lemma extDerivFun_chartBasisVec_apply_of_mem
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (j : Fin (Module.finrank ℝ E)) {b : M}
    (hb_chart : b ∈ (chartAt H x).source)
    (hb_int : extChartAt I x b ∈ interior ((extChartAt I x).target : Set E)) :
    extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) x j b) =
      partialDeriv (E := E) j (scalarOnE (I := I) x f) (extChartAt I x b) := by
  classical
  have hf_at : MDiffAt f b := (hf b).mdifferentiableAt (by simp)
  -- `extDerivFun f b v = mfderiv f b v` (definitionally, via `fromTangentSpace` on ℝ).
  change (mfderiv I 𝓘(ℝ, ℝ) f b) (chartBasisVecFiber (I := I) x j b) = _
  exact mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) x hf_at
    hb_chart hb_int j

/-- The function `b ↦ (extDerivFun f) b (chartBasisVecFiber x j b)` is eventually
equal (around `x`) to `(partialDeriv j (scalarOnE x f)) ∘ (extChartAt I x)` on the chart
source intersected with the chart-target-interior preimage. -/
private lemma extDerivFun_chartBasisVec_eventuallyEq
    [I.Boundaryless]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (j : Fin (Module.finrank ℝ E)) :
    (fun b : M => extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) x j b)) =ᶠ[𝓝 x]
      (fun b : M =>
        partialDeriv (E := E) j (scalarOnE (I := I) x f) (extChartAt I x b)) := by
  classical
  -- The intersection of the chart source with the preimage of the chart-target interior
  -- under `extChartAt I x` is open and contains `x`.
  set S : Set M :=
    (chartAt H x).source ∩
      ((extChartAt I x) ⁻¹' interior ((extChartAt I x).target : Set E)) with hS_def
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hxS : x ∈ S := ⟨hxsrc, hxint⟩
  have hS_open : IsOpen S := by
    have hcont : ContinuousOn (extChartAt I x) (chartAt H x).source := by
      have h := continuousOn_extChartAt (I := I) (x := x)
      have heq : (extChartAt I x).source = (chartAt H x).source :=
        extChartAt_source (I := I) x
      rw [heq] at h
      exact h
    have hpre : IsOpen ((chartAt H x).source ∩
        (extChartAt I x) ⁻¹' interior ((extChartAt I x).target : Set E)) :=
      hcont.isOpen_inter_preimage ((chartAt H x).open_source) isOpen_interior
    -- `S = (chartAt H x).source ∩ (φ ⁻¹' interior target)`, but the definition has
    -- `(chartAt H x).source ∩ (φ ⁻¹' interior target)`, so they coincide.
    convert hpre using 1
  have hS_nhds : S ∈ 𝓝 x := hS_open.mem_nhds hxS
  filter_upwards [hS_nhds] with b hb
  obtain ⟨hb_chart, hb_int⟩ := hb
  exact extDerivFun_chartBasisVec_apply_of_mem (I := I) hf x j hb_chart hb_int

/-! ### Computing `extDerivFun (b ↦ θ b (Y b)) x e_i` -/

/-- The directional derivative of the dual-pairing scalar `b ↦ (extDerivFun f) b
(chartBasisVecFiber x j b)` along the model-basis vector `e_i`, at the basepoint `x`,
equals the chart-iterated partial derivative `∂_i ∂_j (scalarOnE x f)(φ x)`. -/
private lemma extDerivFun_pairing_chartBasisVec_apply_basis
    [I.Boundaryless]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    extDerivFun (I := I) (fun b => extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) x j b)) x ((chartModelBasis E) i) =
      chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) := by
  classical
  -- Step 1: rewrite the dual-pairing scalar via the chart-pulled-back form.
  have hev := extDerivFun_chartBasisVec_eventuallyEq (I := I) hf x j
  have hf_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) x f)
      (extChartAt I x).target :=
    scalarOnE_contDiffOn (I := I) x hf
  have hf_smooth_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) x f)
      (interior ((extChartAt I x).target : Set E)) :=
    hf_smooth_target.mono interior_subset
  have hopen_int : IsOpen (interior ((extChartAt I x).target : Set E)) := isOpen_interior
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  -- Step 2: We compute via a chain of equalities, working at the value level rather
  -- than rewriting on CLM-objects (which can be obscured by the `fromTangentSpace` cast).
  set g : M → ℝ :=
    fun b => partialDeriv (E := E) j (scalarOnE (I := I) x f) (extChartAt I x b) with hg_def
  -- `extDerivFun h x v = mfderiv h x v` for ℝ-valued h (definitional).
  -- Step 3: Smoothness data for `g`.
  -- `g = (partialDeriv j (scalarOnE x f)) ∘ (extChartAt I x)`. The first factor is
  -- smooth at `φ x` (an interior point of chart target), the second is smooth at `x`.
  have hu_smooth_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) x f) (extChartAt I x x) :=
    hf_smooth_int.contDiffAt (hopen_int.mem_nhds hxint)
  -- Smoothness of `fderiv u` near `(extChartAt I x x)`.
  have hfd_contDiffOn : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) x f))
      (interior ((extChartAt I x).target : Set E)) :=
    hf_smooth_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hfd_contDiffAt : ContDiffAt ℝ ∞ (fderiv ℝ (scalarOnE (I := I) x f))
      (extChartAt I x x) :=
    hfd_contDiffOn.contDiffAt (hopen_int.mem_nhds hxint)
  -- Smoothness of `partialDeriv j u`.
  have hPD_contDiffAt : ContDiffAt ℝ ∞
      (partialDeriv (E := E) j (scalarOnE (I := I) x f)) (extChartAt I x x) := by
    -- `partialDeriv j u y = fderiv u y (e_j) = (apply e_j) ∘ (fderiv u) y`.
    have hcomp_eq :
        partialDeriv (E := E) j (scalarOnE (I := I) x f) =
          (ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) j) :
            (E →L[ℝ] ℝ) →L[ℝ] ℝ) ∘
          (fderiv ℝ (scalarOnE (I := I) x f)) := by
      funext y
      rfl
    rw [hcomp_eq]
    exact (ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) j)).contDiff.contDiffAt.comp
      (extChartAt I x x) hfd_contDiffAt
  -- Smoothness of `extChartAt I x` at `x` (manifold-side).
  have hphi_mdiff : MDiffAt (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (I := I) (x := x) hxsrc
  -- Mdifferentiability of `g = partialDeriv j (...) ∘ (extChartAt I x)` at `x`.
  have hPD_mdiff_at : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (partialDeriv (E := E) j (scalarOnE (I := I) x f)) (extChartAt I x x) := by
    -- ContDiffAt → DifferentiableAt → MDifferentiableAt for vector-space domain/codomain.
    have hd : DifferentiableAt ℝ
        (partialDeriv (E := E) j (scalarOnE (I := I) x f)) (extChartAt I x x) :=
      hPD_contDiffAt.differentiableAt (by simp)
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hd
  have hg_mdiff : MDiffAt g x :=
    hPD_mdiff_at.comp x hphi_mdiff
  -- Step 4: Compute `mfderiv g x e_i = chartIteratedPartialDeriv ...` via the chart bridge.
  have htgt_nhds : ((extChartAt I x).target : Set E) ∈ 𝓝 (extChartAt I x x) := by
    refine mem_nhds_iff.mpr ?_
    refine ⟨interior ((extChartAt I x).target : Set E),
      interior_subset, hopen_int, hxint⟩
  have hcompose_eq : (g ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)]
      (partialDeriv (E := E) j (scalarOnE (I := I) x f)) := by
    filter_upwards [htgt_nhds] with y hy
    change partialDeriv (E := E) j (scalarOnE (I := I) x f)
        (extChartAt I x ((extChartAt I x).symm y)) =
      partialDeriv (E := E) j (scalarOnE (I := I) x f) y
    rw [(extChartAt I x).right_inv hy]
  -- Combined value-level computation.
  have hg_value :
      (mfderiv I 𝓘(ℝ) g x : TangentSpace I x →L[ℝ] _)
          ((chartModelBasis E) i) =
        chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) := by
    rw [mfderiv_scalar_eq_chart_fderiv (I := I) x g hxsrc hxint hg_mdiff
      ((chartModelBasis E) i)]
    rw [hcompose_eq.fderiv_eq]
    rw [trivToE_self_apply (I := I) x ((chartModelBasis E) i)]
    rw [chartIteratedPartialDeriv_def]
    rfl
  -- Step 5: Bridge `extDerivFun (...) x e_i` to `mfderiv g x e_i` via EventuallyEq.
  -- The EventuallyEq `hev` lets us replace the function inside mfderiv.
  -- Use `extDerivFun = mfderiv` (definitional) and substitute via the EventuallyEq.
  -- Definitionally, `extDerivFun h x v = mfderiv h x v` for ℝ-valued h.
  have hed_to_mfderiv : ∀ (h : M → ℝ) (v : TangentSpace I x),
      extDerivFun (I := I) h x v = (mfderiv I 𝓘(ℝ) h x : TangentSpace I x →L[ℝ] _) v := by
    intro h v; rfl
  rw [hed_to_mfderiv]
  rw [Filter.EventuallyEq.mfderiv_eq hev]
  exact hg_value

/-! ### Computing `LeviCivita g (chartBasisVec x j) x e_i`

We use the chart-local Levi-Civita formula at `α = x`. The chart pullback of
`chartBasisVec x j` is constant `e_j`, so its `fderiv` vanishes; the Christoffel
correction collapses to `∑_k Γ^k{}_{ij}(φ x) • e_k`. -/

/-- The fderiv at `(φ x)` of the chart-pulled-back chart-basis section vanishes. -/
private lemma fderiv_chartE_chartBasisVec_self_eq_zero
    [I.Boundaryless]
    (x : M) (j : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (chartE_section_repr (I := I) x
        (fun b : M => chartBasisVecFiber (I := I) x j b) ∘ (extChartAt I x).symm)
        (extChartAt I x x) = 0 := by
  classical
  -- The function is locally constant on a neighborhood of `(φ x)`.
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  -- The base set `(triv x).baseSet` is open and contains `x`.
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  set U : Set E :=
    (extChartAt I x) '' ((extChartAt I x).source ∩
      (trivializationAt E (TangentSpace I) x).baseSet) with hU_def
  -- The image `U` is open since the chart on its source is a homeomorphism (over chart target),
  -- but rather than working with images we work with neighborhoods of `(φ x)`.
  -- Alternative: use `(extChartAt I x).symm ⁻¹' baseSet ∩ target` as open neighborhood
  -- of `(φ x)` in chart target; the function pulled through `φ.symm` is constant `e_j` there.
  set V : Set E :=
    (extChartAt I x).target ∩
      (extChartAt I x).symm ⁻¹' (trivializationAt E (TangentSpace I) x).baseSet with hV_def
  have hxV : extChartAt I x x ∈ V := by
    refine ⟨hxtgt, ?_⟩
    rw [Set.mem_preimage]
    rw [(extChartAt I x).left_inv hxsrc_ext]
    exact hbase
  -- Openness of V using continuity of `(extChartAt I x).symm` on `(extChartAt I x).target`.
  have hcont_symm : ContinuousOn (extChartAt I x).symm (extChartAt I x).target :=
    continuousOn_extChartAt_symm x
  have hopen_V : IsOpen V := by
    refine ContinuousOn.isOpen_inter_preimage hcont_symm
      (isOpen_extChartAt_target (I := I) x) ?_
    exact (trivializationAt E (TangentSpace I) x).open_baseSet
  -- The function is constant on V.
  have hconstOn : ∀ y ∈ V,
      (chartE_section_repr (I := I) x
          (fun b : M => chartBasisVecFiber (I := I) x j b) ∘ (extChartAt I x).symm) y =
        (chartModelBasis E) j := by
    intro y hy
    obtain ⟨_hy_target, hy_pre⟩ := hy
    rw [Set.mem_preimage] at hy_pre
    exact chartE_section_repr_chartBasisVec_pullback_constOn (I := I) x j hy_pre
  -- The function is eventually equal to a constant near `(φ x)`.
  have hev : (chartE_section_repr (I := I) x
      (fun b : M => chartBasisVecFiber (I := I) x j b) ∘ (extChartAt I x).symm) =ᶠ[𝓝
        (extChartAt I x x)]
      (fun _ : E => ((chartModelBasis E) j : E)) := by
    filter_upwards [hopen_V.mem_nhds hxV] with y hy
    exact hconstOn y hy
  rw [hev.fderiv_eq]
  -- `fderiv (fun _ => c) y = 0`.
  exact fderiv_const_apply ((chartModelBasis E) j)

/-- The Christoffel correction at the basepoint `(α, x) = (x, x)` applied to the
constant section component `e_j` and the model-basis input `e_i` collapses to the
Christoffel sum `∑_k Γ^k{}_{ij}(φ x) • e_k`. -/
private lemma christoffelCorrection_self_basis_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    christoffelCorrection (I := I) g x x ((chartModelBasis E) j)
        ((chartModelBasis E) i) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x i j k (extChartAt I x x) •
          (chartModelBasis E) k := by
  classical
  rw [christoffelCorrection_apply (I := I) g x x ((chartModelBasis E) j)
        ((chartModelBasis E) i)]
  -- Simplify the inner triple sum: `(b.repr (trivToE x x e_i)) i' = δ(i', i)`,
  -- `(b.repr e_j) j' = δ(j', j)`. Both Kronecker collapses.
  rw [trivToE_self_apply (I := I) x ((chartModelBasis E) i)]
  -- Now both `trivToE x x e_i` and `e_j` are model-basis vectors, with
  -- `b.repr (b k) = single k 1` (Finsupp).
  -- Collapse the i'-sum: `∑ i', (b.repr e_i) i' * ... = ((b.repr e_i) i) * ... = ...` at i' = i.
  rw [show (∑ i' : Fin (Module.finrank ℝ E),
        ∑ j' : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr ((chartModelBasis E) i)) i' *
                ((chartModelBasis E).repr ((chartModelBasis E) j)) j' *
                chartChristoffel (I := I) g x i' j' k (extChartAt I x x)) •
              (chartModelBasis E) k) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x i j k (extChartAt I x x) •
          (chartModelBasis E) k from ?_]
  -- The reduction: the only non-zero contribution is at (i', j') = (i, j).
  -- `(b.repr (b r)) s = if r = s then 1 else 0` via `Module.Basis.repr_self`.
  classical
  -- We extract the sum reduction in two steps using `Finset.sum_eq_single` on i' and j'.
  have hrepr_basis : ∀ (r s : Fin (Module.finrank ℝ E)),
      ((chartModelBasis E).repr ((chartModelBasis E) r)) s =
        if r = s then (1 : ℝ) else 0 := by
    intro r s
    rw [Module.Basis.repr_self]
    -- `Finsupp.single r 1 s = if r = s then 1 else 0`.
    by_cases h : r = s
    · subst h; simp
    · simp [h]
  -- Outer sum on i': only i' = i contributes.
  rw [Finset.sum_eq_single i (fun i' _ hi'_ne_i => ?_) (fun hi_mem => ?_)]
  · -- The case i' = i.
    -- Inner sum on j': only j' = j contributes.
    rw [Finset.sum_eq_single j (fun j' _ hj'_ne_j => ?_) (fun hj_mem => ?_)]
    · -- The case (i', j') = (i, j): collapse the scalar.
      have hrepr_ii : ((chartModelBasis E).repr ((chartModelBasis E) i)) i = 1 := by
        rw [hrepr_basis i i, if_pos rfl]
      have hrepr_jj : ((chartModelBasis E).repr ((chartModelBasis E) j)) j = 1 := by
        rw [hrepr_basis j j, if_pos rfl]
      rw [hrepr_ii, hrepr_jj]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring_nf
    · -- The case j' ≠ j: the j'-th entry of `b.repr e_j` is 0.
      have hrepr_jj' : ((chartModelBasis E).repr ((chartModelBasis E) j)) j' = 0 := by
        rw [hrepr_basis j j', if_neg (fun h => hj'_ne_j h.symm)]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [hrepr_jj']
      simp
    · exact (hj_mem (Finset.mem_univ j)).elim
  · -- The case i' ≠ i: the i'-th entry of `b.repr e_i` is 0.
    refine Finset.sum_eq_zero (fun j' _ => ?_)
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have hrepr_ii' : ((chartModelBasis E).repr ((chartModelBasis E) i)) i' = 0 := by
      rw [hrepr_basis i i', if_neg (fun h => hi'_ne_i h.symm)]
    rw [hrepr_ii']
    simp
  · exact (hi_mem (Finset.mem_univ i)).elim

/-! ### Combined formula for the Levi-Civita on the chart-basis section -/

/-- The bundled Levi-Civita derivative of the chart-basis section `chartBasisVec x j`
at the basepoint `x` along the model-basis vector `e_i`, evaluated to a tangent vector,
equals the Christoffel sum `∑_k Γ^k{}_{ij}(φ x) • e_k`. -/
private lemma LeviCivita_chartBasisVec_self_basis_apply
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (LeviCivita (I := I) g).toFun
        (fun b : M => chartBasisVecFiber (I := I) x j b) x
        ((chartModelBasis E) i) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x i j k (extChartAt I x x) •
          (chartModelBasis E) k := by
  classical
  -- Use the chart-overlap formula at `α = x` (good set: x ∈ goodSet x).
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hY_at : MDiffAt (T% (fun b : M => chartBasisVecFiber (I := I) x j b)) x :=
    chartBasisVec_mdifferentiableAt_self (I := I) x j
  rw [LeviCivita_chart_apply (I := I) g x hx_good hY_at ((chartModelBasis E) i)]
  -- Apply `chartLeviCivita_apply` at `α = x`.
  rw [chartLeviCivita_apply (I := I) g x
        (fun b : M => chartBasisVecFiber (I := I) x j b) hx_good
        ((chartModelBasis E) i)]
  -- The fderiv piece vanishes; the Christoffel piece collapses.
  rw [fderiv_chartE_chartBasisVec_self_eq_zero (I := I) x j]
  rw [show
        chartE_section_repr (I := I) x
          (fun b : M => chartBasisVecFiber (I := I) x j b) x =
        (chartModelBasis E) j from
      chartE_section_repr_chartBasisVec_apply (I := I) x j
        (FiberBundle.mem_baseSet_trivializationAt' x)]
  rw [christoffelCorrection_self_basis_apply (I := I) g x i j]
  -- Simplify `0 + S = S` and `trivFromE x x` is identity.
  simp only [ContinuousLinearMap.zero_apply, zero_add]
  -- `trivFromE x x (∑_k c_k • e_k) = ∑_k c_k • e_k`. We distribute trivFromE over the sum
  -- and over each scalar, then apply `trivFromE_self_apply` to identify each summand.
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [(trivFromE (I := I) x x).map_smul]
  rw [trivFromE_self_apply (I := I) x ((chartModelBasis E) k)]
  rfl

/-- The cotangent-section pairing `θ x (LeviCivita g (chartBasisVec x j) x e_i)` for
`θ = extDerivFun f`, at the basepoint, equals the Christoffel-weighted sum of
chart-pullback partial derivatives `∑_k Γ^k{}_{ij}(φ x) * ∂_k (scalarOnE x f)(φ x)`. -/
private lemma extDerivFun_LeviCivita_chartBasisVec_self_basis
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    extDerivFun (I := I) f x
        ((LeviCivita (I := I) g).toFun
          (fun b : M => chartBasisVecFiber (I := I) x j b) x
          ((chartModelBasis E) i)) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g x i j k (extChartAt I x x) *
          partialDeriv (E := E) k (scalarOnE (I := I) x f) (extChartAt I x x) := by
  classical
  rw [LeviCivita_chartBasisVec_self_basis_apply (I := I) g x i j]
  -- Distribute `extDerivFun f x` over the sum and the scalar via the bundled CLM.
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxsrc
  have hxtgt : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc_ext
  have hxint : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hxtgt
  have hf_at : MDiffAt f x := (hf x).mdifferentiableAt (by simp)
  -- The bundled CLM `extDerivFun f x : TangentSpace I x →L[ℝ] ℝ` is linear.
  -- Step 1: distribute the CLM over the finite sum and over each scalar.
  have h_distribute :
      extDerivFun (I := I) f x
          (∑ k : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g x i j k (extChartAt I x x) •
              (chartModelBasis E) k) =
        ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g x i j k (extChartAt I x x) *
            extDerivFun (I := I) f x ((chartModelBasis E) k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    -- `(extDerivFun f x) (c • v) = c • (extDerivFun f x) v = c * (extDerivFun f x) v`.
    rw [show (extDerivFun (I := I) f x)
            (chartChristoffel (I := I) g x i j k (extChartAt I x x) •
              (chartModelBasis E) k) =
          chartChristoffel (I := I) g x i j k (extChartAt I x x) •
            (extDerivFun (I := I) f x) ((chartModelBasis E) k) from
        (extDerivFun (I := I) f x).map_smul
          (chartChristoffel (I := I) g x i j k (extChartAt I x x))
          ((chartModelBasis E) k)]
    rw [smul_eq_mul]
  -- Combine `h_distribute` with the identification `(extDerivFun f x) e_k = partialDeriv k (...)`.
  have h_summand : ∀ (k : Fin (Module.finrank ℝ E)),
      extDerivFun (I := I) f x ((chartModelBasis E) k) =
        partialDeriv (E := E) k (scalarOnE (I := I) x f) (extChartAt I x x) := by
    intro k
    -- `extDerivFun f x v = mfderiv f x v` (definitionally for ℝ-valued f).
    change (mfderiv I 𝓘(ℝ, ℝ) f x : TangentSpace I x →L[ℝ] _) ((chartModelBasis E) k) = _
    rw [mfderiv_scalar_eq_chart_fderiv (I := I) x f hxsrc hxint hf_at
      ((chartModelBasis E) k)]
    rw [trivToE_self_apply (I := I) x ((chartModelBasis E) k)]
    rfl
  -- Substitute and conclude.
  refine h_distribute.trans ?_
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [h_summand k]

/-! ### The matrix identity, unconditionally -/

/-- **Discharge of `chartHessianMatrixIdentity`.** The matrix identity
`abstractHessian g f x e_i e_j = chartHessianTensor g x f i j x` holds unconditionally
for every smooth scalar function `f` on a smooth boundaryless Riemannian manifold.

The proof unfolds the abstract Hessian via `cotangentCov_dualPairing`, identifies the
chart-pulled-back form of each ingredient using the chart-local Levi-Civita formula
(`chartLeviCivita_apply`) and the basepoint-trivialization identities
(`trivToE x x = id`, `trivFromE x x = id`), and matches the resulting expression with
`chartHessianTensor`. -/
theorem chartHessianMatrixIdentity_holds [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    chartHessianMatrixIdentity (I := I) g f x := by
  classical
  intro i j
  -- Unfold the abstract Hessian as the cotangent-pairing form.
  -- `abstractHessian g f x v w = ((cotangentCov LC) (extDerivFun f) x v) w`.
  rw [abstractHessian_apply]
  -- Set up the data for `cotangentCov_dualPairing`.
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f with hθ_def
  set Y : Π b : M, TangentSpace I b :=
    fun b : M => chartBasisVecFiber (I := I) x j b with hY_def
  -- Smoothness of `θ` as a cotangent-bundle section, at the point `x`.
  have hθ_at : MDiffAtCotangent θ x := by
    have hext_smooth := cotangentCov_extDerivFun_smooth (I := I) hf
    exact (hext_smooth x).mdifferentiableAt (by simp)
  -- Smoothness of `Y` at `x`.
  have hY_at : MDiffAt (T% Y) x := chartBasisVec_mdifferentiableAt_self (I := I) x j
  -- Apply the dual-pairing identity at `v = e_i`.
  have hpair := cotangentCov_dualPairing (LeviCivita (I := I) g) hθ_at hY_at
    ((chartModelBasis E) i)
  -- `hpair`: `extDerivFun (b ↦ θ b (Y b)) x e_i =
  --           ((cotangentCov LC) θ x e_i) (Y x) + θ x (LC Y x e_i)`.
  -- We rewrite this to isolate `((cotangentCov LC) θ x e_i) (Y x)`.
  have hYx : Y x = (chartModelBasis E) j := by
    -- `Y x = chartBasisVecFiber x j x = (chartModelBasis E) j`.
    exact chartBasisVecFiber_self (I := I) x j
  -- Substitute `Y x = e_j` in `hpair`.
  rw [hYx] at hpair
  -- Step A: Identify the LHS of hpair with `chartIteratedPartialDeriv (...)`.
  have hLHS := extDerivFun_pairing_chartBasisVec_apply_basis (I := I) hf x i j
  -- Step B: Identify the second RHS term `θ x (LC Y x e_i)` with the Christoffel sum.
  have hRHS_2 := extDerivFun_LeviCivita_chartBasisVec_self_basis (I := I) g hf x i j
  -- Combine: `((cotangentCov LC) θ x e_i) e_j = LHS - θ x (LC Y x e_i) = chartHessianTensor`.
  have hkey :
      ((cotangentCov (LeviCivita (I := I) g)).toFun θ x ((chartModelBasis E) i))
          ((chartModelBasis E) j) =
        extDerivFun (I := I) (fun b => θ b (Y b)) x ((chartModelBasis E) i) -
          θ x ((LeviCivita (I := I) g).toFun Y x ((chartModelBasis E) i)) := by
    linarith [hpair]
  rw [hkey]
  -- Substitute the chart-pulled-back forms.
  rw [hLHS, hRHS_2]
  -- Now match with `chartHessianTensor g x f i j x`.
  rw [chartHessianTensor_def]

/-! ## Chart-α matrix identity at general points in the chart-α good set

We extend the chart-x version to a chart at a different base point α : M, for
manifold points x in the chart-α good set. The chart-α tensor Hessian entries
match the abstract Hessian evaluated on the chart-α basis pair
`(chartBasisVecFiber α i x, chartBasisVecFiber α j x)`.

This is the chart-α analog of `chartHessianMatrixIdentity_holds`. The key
simplifications at general x in chart-α good set:
- `trivToE α x (chartBasisVecFiber α i x) = e_i` (round-trip via `trivToE_trivFromE`).
- `(extDerivFun f) x (chartBasisVecFiber α j x) =
    partialDeriv j (scalarOnE α f) (extChartAt α x)` (chart pullback identification).
- `chartE_section_repr α (chartBasisVecFiber α j ·)` is constantly `e_j` on a
  neighborhood of x in chart-α base set, hence its fderiv vanishes. -/

/-! ### Pullback identification of `(extDerivFun f) b (chartBasisVec α j b)` -/

/-- For `b` in the chart-α good set, the dual-pairing scalar
`(extDerivFun f) b (chartBasisVecFiber α j b)` equals
`partialDeriv j (scalarOnE α f) (extChartAt α b)`. -/
private lemma extDerivFun_chartBasisVec_alpha_apply_of_mem
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (α : M)
    (j : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) α j b) =
      partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α b) := by
  classical
  have hf_at : MDiffAt f b := (hf b).mdifferentiableAt (by simp)
  have hb_chart : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  change (mfderiv I 𝓘(ℝ, ℝ) f b) (chartBasisVecFiber (I := I) α j b) = _
  exact mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) α hf_at
    hb_chart hb_int j

/-- The function `b ↦ (extDerivFun f) b (chartBasisVecFiber α j b)` is eventually
equal (around `x`) to `(partialDeriv j (scalarOnE α f)) ∘ (extChartAt α)` on
the chart-α good set (an open neighborhood of `x`). -/
private lemma extDerivFun_chartBasisVec_alpha_eventuallyEq
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (α : M)
    (j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (fun b : M => extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) α j b)) =ᶠ[𝓝 x]
      (fun b : M =>
        partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α b)) := by
  classical
  have hopen : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  have hnhd : chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 x := hopen.mem_nhds hx
  filter_upwards [hnhd] with b hb
  exact extDerivFun_chartBasisVec_alpha_apply_of_mem (I := I) hf α j hb

/-! ### Computing the directional derivative at the chart-α basis pair -/

/-- The directional derivative of the dual-pairing scalar along
`chartBasisVecFiber α i x`, at a chart-α good-set point `x`, equals the
chart-iterated partial derivative. -/
private lemma extDerivFun_pairing_chartBasisVec_alpha_apply
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    extDerivFun (I := I) (fun b => extDerivFun (I := I) f b
        (chartBasisVecFiber (I := I) α j b)) x
        (chartBasisVecFiber (I := I) α i x) =
      chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x) := by
  classical
  have hev := extDerivFun_chartBasisVec_alpha_eventuallyEq (I := I) hf α j hx
  have hf_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α hf
  have hf_smooth_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
      (interior ((extChartAt I α).target : Set E)) :=
    hf_smooth_target.mono interior_subset
  have hopen_int : IsOpen (interior ((extChartAt I α).target : Set E)) :=
    isOpen_interior
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxchart
  have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  set g : M → ℝ :=
    fun b => partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α b) with hg_def
  have hu_smooth_at : ContDiffAt ℝ ∞ (scalarOnE (I := I) α f) (extChartAt I α x) :=
    hf_smooth_int.contDiffAt (hopen_int.mem_nhds hxint)
  have hfd_contDiffOn : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (interior ((extChartAt I α).target : Set E)) :=
    hf_smooth_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hfd_contDiffAt : ContDiffAt ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
      (extChartAt I α x) :=
    hfd_contDiffOn.contDiffAt (hopen_int.mem_nhds hxint)
  have hPD_contDiffAt : ContDiffAt ℝ ∞
      (partialDeriv (E := E) j (scalarOnE (I := I) α f)) (extChartAt I α x) := by
    have hcomp_eq :
        partialDeriv (E := E) j (scalarOnE (I := I) α f) =
          (ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) j) :
            (E →L[ℝ] ℝ) →L[ℝ] ℝ) ∘
          (fderiv ℝ (scalarOnE (I := I) α f)) := by
      funext y; rfl
    rw [hcomp_eq]
    exact (ContinuousLinearMap.apply ℝ ℝ ((chartModelBasis E) j)).contDiff.contDiffAt.comp
      (extChartAt I α x) hfd_contDiffAt
  have hphi_mdiff : MDiffAt (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
  have hPD_mdiff_at : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (partialDeriv (E := E) j (scalarOnE (I := I) α f)) (extChartAt I α x) := by
    have hd : DifferentiableAt ℝ
        (partialDeriv (E := E) j (scalarOnE (I := I) α f)) (extChartAt I α x) :=
      hPD_contDiffAt.differentiableAt (by simp)
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hd
  have hg_mdiff : MDiffAt g x :=
    hPD_mdiff_at.comp x hphi_mdiff
  have htgt_nhds : ((extChartAt I α).target : Set E) ∈ 𝓝 (extChartAt I α x) := by
    refine mem_nhds_iff.mpr ?_
    refine ⟨interior ((extChartAt I α).target : Set E),
      interior_subset, hopen_int, hxint⟩
  -- Compute `mfderiv g x (chartBasisVecFiber α i x)` via the chart bridge.
  have hg_value :
      (mfderiv I 𝓘(ℝ) g x : TangentSpace I x →L[ℝ] _)
          (chartBasisVecFiber (I := I) α i x) =
        chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x) := by
    rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) α
        hg_mdiff hxchart hxint i]
    -- `scalarOnE α g =ᶠ[𝓝 (extChartAt α x)] partialDeriv j (scalarOnE α f)`.
    have hscalar_eq : (scalarOnE (I := I) α g) =ᶠ[𝓝 (extChartAt I α x)]
        (partialDeriv (E := E) j (scalarOnE (I := I) α f)) := by
      filter_upwards [htgt_nhds] with y hy
      change g ((extChartAt I α).symm y) =
        partialDeriv (E := E) j (scalarOnE (I := I) α f) y
      change partialDeriv (E := E) j (scalarOnE (I := I) α f)
          (extChartAt I α ((extChartAt I α).symm y)) =
        partialDeriv (E := E) j (scalarOnE (I := I) α f) y
      rw [(extChartAt I α).right_inv hy]
    -- Identify `partialDeriv i (scalarOnE α g) (extChartAt α x)` with
    -- `partialDeriv i (partialDeriv j (scalarOnE α f)) (extChartAt α x)`,
    -- then with `chartIteratedPartialDeriv α f i j (extChartAt α x)`.
    change partialDeriv (E := E) i (scalarOnE (I := I) α g) (extChartAt I α x) =
        chartIteratedPartialDeriv (I := I) α f i j (extChartAt I α x)
    have h_pd : partialDeriv (E := E) i (scalarOnE (I := I) α g) (extChartAt I α x) =
        partialDeriv (E := E) i
          (partialDeriv (E := E) j (scalarOnE (I := I) α f))
          (extChartAt I α x) := by
      change (fderiv ℝ (scalarOnE (I := I) α g) (extChartAt I α x))
          ((chartModelBasis E) i) =
        (fderiv ℝ (partialDeriv (E := E) j (scalarOnE (I := I) α f))
            (extChartAt I α x))
          ((chartModelBasis E) i)
      congr 1
      exact Filter.EventuallyEq.fderiv_eq hscalar_eq
    rw [h_pd]
    rw [chartIteratedPartialDeriv_def]
  -- Bridge `extDerivFun (...) x v` to `mfderiv g x v`.
  have hed_to_mfderiv : ∀ (h : M → ℝ) (v : TangentSpace I x),
      extDerivFun (I := I) h x v = (mfderiv I 𝓘(ℝ) h x : TangentSpace I x →L[ℝ] _) v := by
    intro h v; rfl
  rw [hed_to_mfderiv]
  rw [Filter.EventuallyEq.mfderiv_eq hev]
  exact hg_value

/-! ### Smoothness of the chart-α basis section at a chart-α good-set point -/

lemma chartBasisVec_alpha_mdifferentiableAt
    (α : M) (j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    MDiffAt (T% (fun b : M => chartBasisVecFiber (I := I) α j b)) x := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hcontMDiff_on := chartBasisVec_contMDiffOn (I := I) α j
  have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hcontMDiff_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (chartBasisVec (I := I) α j) x :=
    (hcontMDiff_on x hbase).contMDiffAt (hopen.mem_nhds hbase)
  exact hcontMDiff_at.mdifferentiableAt (by simp)

/-! ### Vanishing of the fderiv of the chart-α basis pullback at a chart-α good-set point -/

lemma fderiv_chartE_chartBasisVec_alpha_eq_zero [I.Boundaryless]
    (α : M) (j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    fderiv ℝ (chartE_section_repr (I := I) α
        (fun b : M => chartBasisVecFiber (I := I) α j b) ∘ (extChartAt I α).symm)
        (extChartAt I α x) = 0 := by
  classical
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]; exact hxchart
  have hxtgt : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc_ext
  have hxint : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  set V : Set E :=
    (extChartAt I α).target ∩
      (extChartAt I α).symm ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet with hV_def
  have hxV : extChartAt I α x ∈ V := by
    refine ⟨hxtgt, ?_⟩
    rw [Set.mem_preimage]
    rw [(extChartAt I α).left_inv hxsrc_ext]
    exact hbase
  have hcont_symm : ContinuousOn (extChartAt I α).symm (extChartAt I α).target :=
    continuousOn_extChartAt_symm α
  have hopen_V : IsOpen V := by
    refine ContinuousOn.isOpen_inter_preimage hcont_symm
      (isOpen_extChartAt_target (I := I) α) ?_
    exact (trivializationAt E (TangentSpace I) α).open_baseSet
  have hconstOn : ∀ y ∈ V,
      (chartE_section_repr (I := I) α
          (fun b : M => chartBasisVecFiber (I := I) α j b) ∘ (extChartAt I α).symm) y =
        (chartModelBasis E) j := by
    intro y hy
    obtain ⟨_hy_target, hy_pre⟩ := hy
    rw [Set.mem_preimage] at hy_pre
    change trivToE (I := I) α ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y)) =
      (chartModelBasis E) j
    have heq : chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y) =
        trivFromE (I := I) α ((extChartAt I α).symm y) ((chartModelBasis E) j) := rfl
    rw [heq]
    exact trivToE_trivFromE (I := I) α hy_pre ((chartModelBasis E) j)
  have hev : (chartE_section_repr (I := I) α
      (fun b : M => chartBasisVecFiber (I := I) α j b) ∘ (extChartAt I α).symm) =ᶠ[𝓝
        (extChartAt I α x)]
      (fun _ : E => ((chartModelBasis E) j : E)) := by
    filter_upwards [hopen_V.mem_nhds hxV] with y hy
    exact hconstOn y hy
  rw [hev.fderiv_eq]
  exact fderiv_const_apply ((chartModelBasis E) j)

/-! ### Constancy of the chart-trivialised representation of the basis section at chart-α good-set points -/

lemma chartE_section_repr_chartBasisVec_alpha_apply
    (α : M) (j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartE_section_repr (I := I) α
        (fun b : M => chartBasisVecFiber (I := I) α j b) x =
      (chartModelBasis E) j := by
  classical
  unfold chartE_section_repr
  change trivToE (I := I) α x (chartBasisVecFiber (I := I) α j x) =
    (chartModelBasis E) j
  have heq : chartBasisVecFiber (I := I) α j x =
      trivFromE (I := I) α x ((chartModelBasis E) j) := rfl
  rw [heq]
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  exact trivToE_trivFromE (I := I) α hbase ((chartModelBasis E) j)

/-! ### Christoffel correction at a chart-α good-set point -/

private lemma christoffelCorrection_alpha_basis_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    christoffelCorrection (I := I) g α x ((chartModelBasis E) j)
        (chartBasisVecFiber (I := I) α i x) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k (extChartAt I α x) •
          (chartModelBasis E) k := by
  classical
  rw [christoffelCorrection_apply (I := I) g α x ((chartModelBasis E) j)
        (chartBasisVecFiber (I := I) α i x)]
  -- `trivToE α x (chartBasisVecFiber α i x) = e_i` (round-trip).
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have h_round : trivToE (I := I) α x (chartBasisVecFiber (I := I) α i x) =
      (chartModelBasis E) i := by
    have heq : chartBasisVecFiber (I := I) α i x =
        trivFromE (I := I) α x ((chartModelBasis E) i) := rfl
    rw [heq]
    exact trivToE_trivFromE (I := I) α hbase ((chartModelBasis E) i)
  rw [h_round]
  have hrepr_basis : ∀ (r s : Fin (Module.finrank ℝ E)),
      ((chartModelBasis E).repr ((chartModelBasis E) r)) s =
        if r = s then (1 : ℝ) else 0 := by
    intro r s
    rw [Module.Basis.repr_self]
    by_cases h : r = s
    · subst h; simp
    · simp [h]
  rw [Finset.sum_eq_single i (fun i' _ hi'_ne_i => ?_) (fun hi_mem => ?_)]
  · rw [Finset.sum_eq_single j (fun j' _ hj'_ne_j => ?_) (fun hj_mem => ?_)]
    · have hrepr_ii : ((chartModelBasis E).repr ((chartModelBasis E) i)) i = 1 := by
        rw [hrepr_basis i i, if_pos rfl]
      have hrepr_jj : ((chartModelBasis E).repr ((chartModelBasis E) j)) j = 1 := by
        rw [hrepr_basis j j, if_pos rfl]
      rw [hrepr_ii, hrepr_jj]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring_nf
    · have hrepr_jj' : ((chartModelBasis E).repr ((chartModelBasis E) j)) j' = 0 := by
        rw [hrepr_basis j j', if_neg (fun h => hj'_ne_j h.symm)]
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [hrepr_jj']
      simp
    · exact (hj_mem (Finset.mem_univ j)).elim
  · refine Finset.sum_eq_zero (fun j' _ => ?_)
    refine Finset.sum_eq_zero (fun k _ => ?_)
    have hrepr_ii' : ((chartModelBasis E).repr ((chartModelBasis E) i)) i' = 0 := by
      rw [hrepr_basis i i', if_neg (fun h => hi'_ne_i h.symm)]
    rw [hrepr_ii']
    simp
  · exact (hi_mem (Finset.mem_univ i)).elim

/-! ### Levi-Civita on the chart-α basis section at chart-α good-set points -/

lemma LeviCivita_chartBasisVec_alpha_basis_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    (LeviCivita (I := I) g).toFun
        (fun b : M => chartBasisVecFiber (I := I) α j b) x
        (chartBasisVecFiber (I := I) α i x) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k (extChartAt I α x) •
          chartBasisVecFiber (I := I) α k x := by
  classical
  have hY_at : MDiffAt (T% (fun b : M => chartBasisVecFiber (I := I) α j b)) x :=
    chartBasisVec_alpha_mdifferentiableAt (I := I) α j hx
  rw [LeviCivita_chart_apply (I := I) g α hx hY_at
        (chartBasisVecFiber (I := I) α i x)]
  rw [chartLeviCivita_apply (I := I) g α
        (fun b : M => chartBasisVecFiber (I := I) α j b) hx
        (chartBasisVecFiber (I := I) α i x)]
  rw [fderiv_chartE_chartBasisVec_alpha_eq_zero (I := I) α j hx]
  rw [show
        chartE_section_repr (I := I) α
          (fun b : M => chartBasisVecFiber (I := I) α j b) x =
        (chartModelBasis E) j from
      chartE_section_repr_chartBasisVec_alpha_apply (I := I) α j hx]
  simp only [ContinuousLinearMap.zero_apply, zero_add]
  rw [christoffelCorrection_alpha_basis_apply (I := I) g α i j hx]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [(trivFromE (I := I) α x).map_smul]
  rfl

/-! ### `extDerivFun f` paired with the chart-α Levi-Civita derivative -/

private lemma extDerivFun_LeviCivita_chartBasisVec_alpha_basis [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    extDerivFun (I := I) f x
        ((LeviCivita (I := I) g).toFun
          (fun b : M => chartBasisVecFiber (I := I) α j b) x
          (chartBasisVecFiber (I := I) α i x)) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α i j k (extChartAt I α x) *
          partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  rw [LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g α i j hx]
  have h_distribute :
      extDerivFun (I := I) f x
          (∑ k : Fin (Module.finrank ℝ E),
            chartChristoffel (I := I) g α i j k (extChartAt I α x) •
              chartBasisVecFiber (I := I) α k x) =
        ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g α i j k (extChartAt I α x) *
            extDerivFun (I := I) f x (chartBasisVecFiber (I := I) α k x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (extDerivFun (I := I) f x)
            (chartChristoffel (I := I) g α i j k (extChartAt I α x) •
              chartBasisVecFiber (I := I) α k x) =
          chartChristoffel (I := I) g α i j k (extChartAt I α x) •
            (extDerivFun (I := I) f x) (chartBasisVecFiber (I := I) α k x) from
        (extDerivFun (I := I) f x).map_smul
          (chartChristoffel (I := I) g α i j k (extChartAt I α x))
          (chartBasisVecFiber (I := I) α k x)]
    rw [smul_eq_mul]
  have h_summand : ∀ (k : Fin (Module.finrank ℝ E)),
      extDerivFun (I := I) f x (chartBasisVecFiber (I := I) α k x) =
        partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro k
    exact extDerivFun_chartBasisVec_alpha_apply_of_mem (I := I) hf α k hx
  refine h_distribute.trans ?_
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [h_summand k]

/-! ### The chart-α matrix identity at general good-set points -/

/-- **Chart-α matrix identity (unconditional, on the chart-α good set).** For
a chart base point `α : M`, a smooth scalar `f : M → ℝ`, and a manifold point
`x ∈ chartLeviCivitaGoodSet α`, the abstract Hessian evaluated on the chart-α
basis pair `(chartBasisVecFiber α i x, chartBasisVecFiber α j x)` equals the
chart-α tensor Hessian entry `chartHessianTensor g α f i j x`. -/
theorem chartAlphaMatrixIdentity_holds_on_goodSet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (i j : Fin (Module.finrank ℝ E)) :
    abstractHessian (I := I) g f x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      chartHessianTensor (I := I) g α f i j x := by
  classical
  rw [abstractHessian_apply]
  set θ : Π b : M, TangentSpace I b →L[ℝ] ℝ := extDerivFun (I := I) f with hθ_def
  set Y : Π b : M, TangentSpace I b :=
    fun b : M => chartBasisVecFiber (I := I) α j b with hY_def
  have hθ_at : MDiffAtCotangent θ x := by
    have hext_smooth := cotangentCov_extDerivFun_smooth (I := I) hf
    exact (hext_smooth x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x :=
    chartBasisVec_alpha_mdifferentiableAt (I := I) α j hx
  have hpair := cotangentCov_dualPairing (LeviCivita (I := I) g) hθ_at hY_at
    (chartBasisVecFiber (I := I) α i x)
  have hYx : Y x = chartBasisVecFiber (I := I) α j x := rfl
  have hkey :
      ((cotangentCov (LeviCivita (I := I) g)).toFun θ x
            (chartBasisVecFiber (I := I) α i x))
          (chartBasisVecFiber (I := I) α j x) =
        extDerivFun (I := I) (fun b => θ b (Y b)) x
            (chartBasisVecFiber (I := I) α i x) -
          θ x ((LeviCivita (I := I) g).toFun Y x
            (chartBasisVecFiber (I := I) α i x)) := by
    rw [← hYx]
    linarith [hpair]
  rw [hkey]
  have hLHS := extDerivFun_pairing_chartBasisVec_alpha_apply (I := I) hf α i j hx
  have hRHS_2 := extDerivFun_LeviCivita_chartBasisVec_alpha_basis (I := I) g hf α i j hx
  rw [hLHS, hRHS_2]
  rw [chartHessianTensor_def]

/-- **Chart-α matrix identity (unconditional, on the chart-α source).** For
`x ∈ (chartAt H α).source`, the chart-α matrix identity holds. -/
theorem chartAlphaMatrixIdentity_holds [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ (chartAt H α).source)
    (i j : Fin (Module.finrank ℝ E)) :
    abstractHessian (I := I) g f x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      chartHessianTensor (I := I) g α f i j x := by
  classical
  have hx_src_ext : x ∈ (extChartAt I α).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hx_tgt : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx_src_ext
  have hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hx_tgt
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hx_good : x ∈ chartLeviCivitaGoodSet (I := I) α :=
    mem_chartLeviCivitaGoodSet_iff.mpr ⟨hx_src_ext, hbase, hx_int⟩
  exact chartAlphaMatrixIdentity_holds_on_goodSet
    (I := I) (M := M) g α hf hx_good i j

end Connection
end Integral
end DifferentialGeometry
