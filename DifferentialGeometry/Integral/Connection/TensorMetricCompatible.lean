import DifferentialGeometry.Integral.Connection.TensorRSNabla
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Connection.Tensor0SCovariantDerivativeAgreementSucc
import DifferentialGeometry.Integral.Connection.RicciIdentitySmoothFrame
import DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval

/-!
# Directional metric compatibility of the tensor Levi-Civita connection

For a smooth Riemannian manifold `(M, g)` modelled on a real inner-product space
`E`, the Levi-Civita connection on the tangent bundle induces a covariant
derivative on every tensor bundle. The pointwise metric-induced inner product
`tensorInnerPointwise_0s` / `tensorInnerPointwise` is *covariantly constant* with
respect to that induced connection: the directional Leibniz identity

  `∇_v ⟨w, S⟩ = ⟨∇_v w, S⟩ + ⟨w, ∇_v S⟩`

holds for every direction `v` and every pair of tensor sections `w`, `S`.

This file establishes the identity at covariant rank `0` — the
`(0, 0)`-tensor case, where the inner product is ordinary multiplication of the
two scalar components and the covariant derivative is the exterior derivative of
the corresponding scalar function. Stated directly against
`tensorInnerPointwise_0s` and the recursive `(0, s)`-tensor covariant derivative
`tensor0SCovariantDerivative`, this is the base of the induction on covariant
rank that yields metric compatibility on every `(0, s)`-tensor bundle and,
through metric lowering, on every mixed `(r, s)`-tensor bundle.

## Main results

* `tensor0SCovariantDerivative_zero_toModel_apply` — the model-fibre coercion of
  the `(0, 0)`-tensor covariant derivative is the exterior derivative of the
  scalar function attached to the section.
* `tensorInnerPointwise_0s_zero_eq_scalarFn_mul` — the pointwise `(0, 0)`-inner
  product of two sections is the product of their scalar functions.
* `tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_zero` — **the
  directional metric-compatibility identity at covariant rank `0`**: the
  exterior derivative of the pointwise inner product of two `(0, 0)`-tensor
  sections decomposes by the covariant Leibniz rule.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-! ## The model-fibre coercion of the `(0, 0)`-tensor covariant derivative

The `(0, 0)`-tensor bundle `fun x => Tensor0SSpace 0 I x` has fibre the space of
`0`-ary continuous multilinear maps `E [×0]→L ℝ`, canonically `≃L ℝ`. The
recursive covariant derivative `tensor0SCovariantDerivative 0` acts on a section
`T` by `v ↦ (tensor0Iso x).symm (extDerivFun (scalarFn T) x v)`, i.e. it is the
exterior derivative of the scalar function `scalarFn T`, repackaged into the
fibre. The model coercion `Tensor0SSpace.toModel` evaluated on the empty tuple
recovers exactly that scalar derivative. -/

/-- The scalar attached to a `(0, 0)`-tensor section value, read off through the
model coercion at the empty tuple, equals `scalarFn`. -/
lemma scalarFn_eq_toModel_elim0
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    scalarFn I M T x = (Tensor0SSpace.toModel (T x)) (fun i => Fin.elim0 i) := by
  -- `tensor0Iso x = (tensor0SSpace_continuousLinearEquiv 0 x).trans
  --   (continuousMultilinearCurryFin0 ℝ E ℝ)`; the curry equiv evaluates the
  -- `0`-ary multilinear map at the (unique) empty tuple.
  change tensor0Iso I M x (T x) = (Tensor0SSpace.toModel (T x)) (fun i => Fin.elim0 i)
  rw [tensor0Iso]
  change (continuousMultilinearCurryFin0 ℝ E ℝ)
      ((tensor0SSpace_continuousLinearEquiv (I := I) 0 x) (T x)) =
    (Tensor0SSpace.toModel (T x)) (fun i => Fin.elim0 i)
  rw [continuousMultilinearCurryFin0_apply]
  -- `toModel` is `tensor0SSpace_continuousLinearEquiv`; the empty tuple `0` and
  -- `fun i => i.elim0` agree by `Subsingleton`.
  change (tensor0SSpace_continuousLinearEquiv (I := I) 0 x) (T x) (0 : Fin 0 → E) =
    (tensor0SSpace_continuousLinearEquiv (I := I) 0 x) (T x) (fun i => Fin.elim0 i)
  congr 1
  exact Subsingleton.elim _ _

/-- **The model coercion of the `(0, 0)`-tensor covariant derivative.** For a
`(0, 0)`-tensor section `T` and a tangent vector `v`, the model-fibre coercion
of `tensor0SCovariantDerivative 0 (LeviCivita g) T x v`, evaluated on the empty
tuple, is the directional derivative `mfderiv` of the scalar function
`scalarFn T` at `x` along `v`. -/
lemma tensor0SCovariantDerivative_zero_toModel_apply
    (g : SmoothRiemannianMetric I M)
    (T : Π x : M, Tensor0SSpace 0 I x) (x : M) (v : TangentSpace I x) :
    (Tensor0SSpace.toModel
        (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v))
      (fun i => Fin.elim0 i) =
      mfderiv I 𝓘(ℝ, ℝ) (scalarFn I M T) x v := by
  -- Unfold the `(0, 0)`-covariant derivative through its apply lemma.
  rw [tensor0SCovariantDerivative_apply_zero (I := I) (M := M)
    (LeviCivita (I := I) g) T x v]
  -- The model coercion at the empty tuple is `tensor0Iso`; it cancels the
  -- `tensor0Iso.symm` in the covariant-derivative formula.
  have hcoe : (Tensor0SSpace.toModel
        ((tensor0Iso I M x).symm
          (extDerivFun (I := I) (scalarFn I M T) x v)))
        (fun i => Fin.elim0 i) =
      tensor0Iso I M x
        ((tensor0Iso I M x).symm (extDerivFun (I := I) (scalarFn I M T) x v)) :=
    (scalarFn_eq_toModel_elim0 (I := I) (M := M)
      (fun _ : M => (tensor0Iso I M x).symm
        (extDerivFun (I := I) (scalarFn I M T) x v)) x).symm
  rw [hcoe, ContinuousLinearEquiv.apply_symm_apply]
  -- `extDerivFun f x v = mfderiv f x v` since the codomain `ℝ`'s tangent space
  -- is canonically `ℝ` and `fromTangentSpace` is the identity coercion there.
  change (NormedSpace.fromTangentSpace ((scalarFn I M T) x)).toContinuousLinearMap
      ((mfderiv I 𝓘(ℝ, ℝ) (scalarFn I M T) x) v) =
    mfderiv I 𝓘(ℝ, ℝ) (scalarFn I M T) x v
  rfl

/-! ## The pointwise `(0, 0)`-inner product is a scalar product

`tensorInnerPointwise_0s 0 g x S T` is, by definition, `S 0 * T 0` — the product
of the two `0`-ary multilinear maps evaluated on the empty tuple. Hence for two
`(0, 0)`-tensor sections it is the pointwise product of their scalar functions
`scalarFn`. -/

/-- The pointwise `(0, 0)`-tensor inner product of two section values is the
product of the corresponding scalar functions. -/
lemma tensorInnerPointwise_0s_zero_eq_scalarFn_mul
    (g : SmoothRiemannianMetric I M)
    (W T : Π x : M, Tensor0SSpace 0 I x) (x : M) :
    tensorInnerPointwise_0s (I := I) (M := M) 0 g x
        (Tensor0SSpace.toModel (W x)) (Tensor0SSpace.toModel (T x)) =
      scalarFn I M W x * scalarFn I M T x := by
  rw [tensorInnerPointwise_0s_zero_arity, scalarFn_eq_toModel_elim0 (I := I) (M := M) W x,
    scalarFn_eq_toModel_elim0 (I := I) (M := M) T x]

/-! ## Directional metric compatibility at covariant rank `0`

For two `(0, 0)`-tensor sections `W`, `T` whose scalar functions are
manifold-differentiable at `x`, the scalar function
`y ↦ ⟨W y, T y⟩ = scalarFn W y * scalarFn T y` is the product of two
manifold-differentiable scalar functions, so its exterior derivative obeys the
ordinary product rule (`extDerivFun_mul_apply`). The two summands of the product
rule are precisely the two covariant-Leibniz terms, since the `(0, 0)`-tensor
covariant derivative is the exterior derivative of the scalar function (by
`tensor0SCovariantDerivative_zero_toModel_apply`). -/

/-- **Directional metric compatibility at covariant rank `0`.** For two
`(0, 0)`-tensor sections `W`, `T` whose scalar functions `scalarFn` are
manifold-differentiable at `x`, and every tangent vector `v`, the directional
derivative of the pointwise `(0, 0)`-inner product `y ↦ ⟨W y, T y⟩` decomposes
by the covariant Leibniz rule:

  `∇_v ⟨W, T⟩ = ⟨∇_v W, T⟩ + ⟨W, ∇_v T⟩`,

where `∇` is the `(0, 0)`-tensor covariant derivative induced by the Levi-Civita
connection of `g`. This is the base of the induction on covariant rank for
metric compatibility of the tensor Levi-Civita connection. -/
theorem tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_zero
    (g : SmoothRiemannianMetric I M)
    (W T : Π x : M, Tensor0SSpace 0 I x) {x : M}
    (hW : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M W) x)
    (hT : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T) x)
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => tensorInnerPointwise_0s (I := I) (M := M) 0 g y
          (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) x v =
      tensorInnerPointwise_0s (I := I) (M := M) 0 g x
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W x v))
          (Tensor0SSpace.toModel (T x))
        + tensorInnerPointwise_0s (I := I) (M := M) 0 g x
          (Tensor0SSpace.toModel (W x))
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v)) := by
  classical
  -- Scalar functions of the two sections.
  set f : M → ℝ := scalarFn I M W with hf_def
  set h : M → ℝ := scalarFn I M T with hh_def
  -- The pointwise-inner-product integrand is the scalar product `f * h`.
  have hintegrand : (fun y : M => tensorInnerPointwise_0s (I := I) (M := M) 0 g y
        (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) =
      fun y : M => f y * h y := by
    funext y
    rw [tensorInnerPointwise_0s_zero_eq_scalarFn_mul (I := I) (M := M) g W T y]
  rw [hintegrand]
  -- The exterior derivative `extDerivFun` of a scalar function applied to a
  -- vector is definitionally the `mfderiv`; pass to `extDerivFun`.
  change extDerivFun (I := I) (fun y : M => f y * h y) x v =
    tensorInnerPointwise_0s (I := I) (M := M) 0 g x
        (Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W x v))
        (Tensor0SSpace.toModel (T x))
      + tensorInnerPointwise_0s (I := I) (M := M) 0 g x
        (Tensor0SSpace.toModel (W x))
        (Tensor0SSpace.toModel
          (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v))
  -- The exterior derivative of the scalar product obeys the product rule.
  rw [extDerivFun_mul_apply (I := I) (p := f) (q := h) hW hT v]
  -- Identify the two product-rule terms with the covariant-Leibniz terms.
  rw [tensorInnerPointwise_0s_zero_eq_scalarFn_mul (I := I) (M := M) g
    (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W x v) T x,
    tensorInnerPointwise_0s_zero_eq_scalarFn_mul (I := I) (M := M) g
    W (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v) x]
  -- The scalar of the constant section `tensor0SCovariantDerivative … x v` is
  -- the exterior derivative of the section's scalar function.
  have hWcov : scalarFn I M
        (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W x v) x =
      extDerivFun (I := I) f x v := by
    rw [hf_def,
      scalarFn_eq_toModel_elim0 (I := I) (M := M)
        (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) W x v) x,
      tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g W x v]
    -- `extDerivFun (scalarFn W) x v = mfderiv (scalarFn W) x v` definitionally.
    rfl
  have hTcov : scalarFn I M
        (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v) x =
      extDerivFun (I := I) h x v := by
    rw [hh_def,
      scalarFn_eq_toModel_elim0 (I := I) (M := M)
        (fun _ : M => tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g) T x v) x,
      tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g T x v]
    rfl
  rw [hWcov, hTcov]
  -- Both sides are now scalar arithmetic.
  change f x * extDerivFun (I := I) h x v + h x * extDerivFun (I := I) f x v =
    extDerivFun (I := I) f x v * h x + f x * extDerivFun (I := I) h x v
  ring

/-! ## Currying bridge: the model coercion of `tensor0S_curry`

The fiberwise currying equivalence `tensor0S_curry s x` carries a
`(0, s + 1)`-tensor to a continuous linear map `T_xM → (0, s)`-tensor. Its
model coercion `Tensor0SSpace.toModel` is `ContinuousMultilinearMap.curryLeft`
on the model fibre: evaluating `toModel (tensor0S_curry s x A v)` on a tuple
`m` agrees with evaluating `toModel A` on `Fin.cons v m`. -/

open Tensor0SBundle in
/-- **Model coercion of the currying equivalence.** For a `(0, s + 1)`-tensor
`A` at `x` and a tangent vector `v`, the model-fibre coercion of
`tensor0S_curry s x A v` is the curry-left of the model coercion of `A`. -/
lemma toModel_tensor0S_curry_eq_curryLeft {s : ℕ} {x : M}
    (A : Tensor0SSpace (s + 1) I x) (v : TangentSpace I x) :
    Tensor0SSpace.toModel (tensor0S_curry (I := I) (M := M) s x A v) =
      (Tensor0SSpace.toModel A).curryLeft v := by
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [ContinuousMultilinearMap.curryLeft_apply]
  exact TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := A) (v0 := v) (vs := m)

/-! ## Frame independence of the `(0, s + 1)` pointwise inner product

The recursion defining `tensorInnerPointwise_0s (s + 1)` contracts the leading
slot through the inverse Gram matrix of the *canonical model basis*
`chartModelBasis E`. The result is, however, frame independent: contracting
the leading slot of a continuous bilinear form `K` through the inverse Gram
matrix of any frame yields the same scalar. We only need the special case of a
`g`-orthonormal frame, for which the Gram matrix is the identity and the
contraction is the plain diagonal sum.

The proof goes through the matrix identity `Sᵀ G⁻¹ S = 1`, where
`Sᵢₐ = g(eᵢ, Eₐ)` is the mixed Gram matrix between the model basis `{eᵢ}` and
the orthonormal frame `{Eₐ}`, and `G` is the model Gram matrix. -/

/-- The mixed Gram matrix `Sᵢₐ = g(x)(eᵢ, Eₐ)` between the canonical model
basis `chartModelBasis E` and a tangent-vector family `frame`. -/
private noncomputable def mixedGramMatrix
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i a => g.inner x ((chartModelBasis E) i) (frame a)

private lemma mixedGramMatrix_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i a : Fin (Module.finrank ℝ E)) :
    mixedGramMatrix (I := I) (M := M) g x frame i a =
      g.inner x ((chartModelBasis E) i) (frame a) := rfl

/-- A `g(x)`-orthonormal family that is also a basis expands every vector:
`v = ∑ₐ g(x)(v, Eₐ) • Eₐ`. -/
private lemma orthonormal_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (v : TangentSpace I x) :
    v = ∑ a : Fin (Module.finrank ℝ E), g.inner x v (frame a) • frame a := by
  classical
  -- Expand `v` in the basis `frame` and identify the coordinates with the
  -- `g`-projections, using orthonormality.
  conv_lhs => rw [← frame.sum_repr v]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  -- `g.inner x v (frame a) = frame.repr v a`.
  have hv : g.inner x v (frame a) =
      ∑ b : Fin (Module.finrank ℝ E),
        frame.repr v b * g.inner x (frame b) (frame a) := by
    conv_lhs => rw [show v = ∑ b : Fin (Module.finrank ℝ E),
      frame.repr v b • frame b from (frame.sum_repr v).symm]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hv]
  rw [Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba
    rw [horth b a, if_neg (by simpa [eq_comm] using hba), mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ a) hb

/-- The model Gram matrix factors as `G = S Sᵀ` through the mixed Gram matrix of
a `g(x)`-orthonormal basis frame. -/
private lemma gramMatrixAt_eq_mixed_mul_transpose
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    gramMatrixAt (I := I) (M := M) g x =
      mixedGramMatrix (I := I) (M := M) g x frame *
        (mixedGramMatrix (I := I) (M := M) g x frame)ᵀ := by
  classical
  ext i j
  rw [gramMatrixAt_apply, Matrix.mul_apply]
  -- `Gᵢⱼ = g(eᵢ, eⱼ) = g(eᵢ, ∑ₐ g(eⱼ,Eₐ) • Eₐ) = ∑ₐ g(eⱼ,Eₐ) g(eᵢ,Eₐ)`.
  have hexp : (chartModelBasis E) j =
      ∑ a : Fin (Module.finrank ℝ E),
        g.inner x ((chartModelBasis E) j) (frame a) • frame a :=
    orthonormal_expansion (I := I) (M := M) g x frame horth ((chartModelBasis E) j)
  calc g.inner x ((chartModelBasis E) i) ((chartModelBasis E) j)
      = g.inner x ((chartModelBasis E) i)
          (∑ a : Fin (Module.finrank ℝ E),
            g.inner x ((chartModelBasis E) j) (frame a) • frame a) := by
        rw [← hexp]
    _ = ∑ a : Fin (Module.finrank ℝ E),
          mixedGramMatrix (I := I) (M := M) g x frame i a *
            (mixedGramMatrix (I := I) (M := M) g x frame)ᵀ a j := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [ContinuousLinearMap.map_smul, smul_eq_mul,
          mixedGramMatrix_apply, Matrix.transpose_apply, mixedGramMatrix_apply]
        ring

/-- The mixed Gram matrix of a `g(x)`-orthonormal basis frame is invertible:
it is a square factor of the invertible model Gram matrix. -/
private lemma mixedGramMatrix_isUnit
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    IsUnit (mixedGramMatrix (I := I) (M := M) g x frame) := by
  classical
  -- `det S ≠ 0`: from `G = S Sᵀ` and `det G ≠ 0`, since `det Sᵀ = det S`.
  rw [Matrix.isUnit_iff_isUnit_det]
  have hG := gramMatrixAt_eq_mixed_mul_transpose (I := I) (M := M) g x frame horth
  have hdetG : (gramMatrixAt (I := I) (M := M) g x).det ≠ 0 := by
    have := gramMatrixAt_isUnit (I := I) (M := M) g x
    rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
  rw [hG, Matrix.det_mul, Matrix.det_transpose] at hdetG
  rw [isUnit_iff_ne_zero]
  intro h
  rw [h] at hdetG
  simp at hdetG

/-- **The key matrix identity** `Sᵀ G⁻¹ S = 1` for the mixed Gram matrix `S` of
a `g(x)`-orthonormal basis frame. -/
private lemma mixedGram_transpose_mul_inv_mul
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    (mixedGramMatrix (I := I) (M := M) g x frame)ᵀ *
        ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
          mixedGramMatrix (I := I) (M := M) g x frame) = 1 := by
  classical
  set S := mixedGramMatrix (I := I) (M := M) g x frame with hS_def
  have hS_unit : IsUnit S := mixedGramMatrix_isUnit (I := I) (M := M) g x frame horth
  have hG : gramMatrixAt (I := I) (M := M) g x = S * Sᵀ :=
    gramMatrixAt_eq_mixed_mul_transpose (I := I) (M := M) g x frame horth
  -- `G⁻¹ = (S Sᵀ)⁻¹ = (Sᵀ)⁻¹ S⁻¹`.
  have hGinv : (gramMatrixAt (I := I) (M := M) g x)⁻¹ = Sᵀ⁻¹ * S⁻¹ := by
    rw [hG, Matrix.mul_inv_rev]
  rw [hGinv]
  -- `Sᵀ (Sᵀ⁻¹ S⁻¹ S) = (Sᵀ Sᵀ⁻¹)(S⁻¹ S) = 1`.
  have hSdet : IsUnit S.det := Matrix.isUnit_iff_isUnit_det _ |>.mp hS_unit
  have hSTdet : IsUnit Sᵀ.det := by
    rw [Matrix.det_transpose]; exact hSdet
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Sᵀ hSTdet,
    Matrix.one_mul, Matrix.nonsing_inv_mul S hSdet]

/-- Bilinear expansion of `tensorInnerPointwise_0s` over a finite sum of
scalar-weighted tensors in the first argument. -/
private lemma tensorInnerPointwise_0s_sum_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (a : ι → ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x (∑ i ∈ A, a i • ψ i) T =
      ∑ i ∈ A, a i *
        tensorInnerPointwise_0s (I := I) (M := M) s g x (ψ i) T := by
  classical
  induction A using Finset.induction with
  | empty => simp [tensorInnerPointwise_0s_zero_left]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, tensorInnerPointwise_0s_add_left,
        tensorInnerPointwise_0s_smul_left, ih, Finset.sum_insert hi]

/-- Bilinear expansion of `tensorInnerPointwise_0s` over a finite sum of
scalar-weighted tensors in the second argument. -/
private lemma tensorInnerPointwise_0s_sum_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (a : ι → ℝ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x S (∑ i ∈ A, a i • ψ i) =
      ∑ i ∈ A, a i *
        tensorInnerPointwise_0s (I := I) (M := M) s g x S (ψ i) := by
  classical
  induction A using Finset.induction with
  | empty => simp [tensorInnerPointwise_0s_zero_right]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, tensorInnerPointwise_0s_add_right,
        tensorInnerPointwise_0s_smul_right, ih, Finset.sum_insert hi]

/-- Double bilinear expansion of `tensorInnerPointwise_0s` over finite sums of
scalar-weighted tensors in both arguments. -/
private lemma tensorInnerPointwise_0s_bisum
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (c d : ι → ℝ)
    (ψ φ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x
        (∑ a ∈ A, c a • ψ a) (∑ b ∈ A, d b • φ b) =
      ∑ a ∈ A, ∑ b ∈ A,
        (c a * d b) *
          tensorInnerPointwise_0s (I := I) (M := M) s g x (ψ a) (φ b) := by
  classical
  rw [tensorInnerPointwise_0s_sum_smul_left]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [tensorInnerPointwise_0s_sum_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b _
  ring

/-- `curryLeft` of a continuous multilinear map is continuous linear in the
leading vector argument: it commutes with finite sums of scalar multiples. -/
private lemma curryLeft_sum_smul {s : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    {ι : Type*} (A : Finset ι) (c : ι → ℝ) (w : ι → E) :
    P.curryLeft (∑ a ∈ A, c a • w a) =
      ∑ a ∈ A, c a • P.curryLeft (w a) := by
  classical
  induction A using Finset.induction with
  | empty => simp
  | insert a A ha ih =>
      rw [Finset.sum_insert ha, map_add, map_smul, ih, Finset.sum_insert ha]

/-- **Frame independence of the `(0, s + 1)` pointwise inner product.** For a
`g(x)`-orthonormal basis frame `{Eₐ}` of `T_xM`, the leading-slot contraction
in the recursion of `tensorInnerPointwise_0s (s + 1)` equals the plain diagonal
sum over the orthonormal frame. -/
private lemma tensorInnerPointwise_0s_succ_orthoFrame
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x S T =
      ∑ a : Fin (Module.finrank ℝ E),
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame a)) := by
  classical
  -- The leading-slot contracted form.
  rw [tensorInnerPointwise_0s_succ]
  -- Expand each model basis vector in the orthonormal frame.
  have hmodel_exp : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E) i =
        ∑ a : Fin (Module.finrank ℝ E),
          mixedGramMatrix (I := I) (M := M) g x frame i a • frame a := by
    intro i
    have hexp := orthonormal_expansion (I := I) (M := M) g x frame horth
      ((chartModelBasis E) i)
    rw [hexp]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [mixedGramMatrix_apply]
  -- `curryLeft` is a continuous linear map: it commutes with the sum and the
  -- scalar multiples.
  have hcurry_exp : ∀ (P : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
      (i : Fin (Module.finrank ℝ E)),
      P.curryLeft ((chartModelBasis E) i) =
        ∑ a : Fin (Module.finrank ℝ E),
          mixedGramMatrix (I := I) (M := M) g x frame i a • P.curryLeft (frame a) := by
    intro P i
    rw [hmodel_exp i]
    exact curryLeft_sum_smul (E := E) P Finset.univ _ _
  -- Substitute and use bilinearity of the rank-`s` inner product to pull the
  -- mixed-Gram-matrix entries out.
  have hstep : ∀ i j : Fin (Module.finrank ℝ E),
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j)) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (mixedGramMatrix (I := I) (M := M) g x frame i a *
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              mixedGramMatrix (I := I) (M := M) g x frame j b) *
            tensorInnerPointwise_0s (I := I) (M := M) s g x
              (S.curryLeft (frame a)) (T.curryLeft (frame b)) := by
    intro i j
    rw [hcurry_exp S i, hcurry_exp T j]
    rw [tensorInnerPointwise_0s_bisum (I := I) (M := M) g x s
      (A := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro b _
    ring
  rw [show (∑ i, ∑ j,
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j))) =
      ∑ i, ∑ j, ∑ a, ∑ b,
        (mixedGramMatrix (I := I) (M := M) g x frame i a *
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGramMatrix (I := I) (M := M) g x frame j b) *
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (S.curryLeft (frame a)) (T.curryLeft (frame b))
    from by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact hstep i j]
  -- The four-fold sum `∑ᵢ∑ⱼ∑ₐ∑ᵦ`, reindexed with `(a, b)` outermost.
  have hkey := mixedGram_transpose_mul_inv_mul (I := I) (M := M) g x frame horth
  set F := fun (i j a b : Fin (Module.finrank ℝ E)) =>
    (mixedGramMatrix (I := I) (M := M) g x frame i a *
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
        mixedGramMatrix (I := I) (M := M) g x frame j b) *
      tensorInnerPointwise_0s (I := I) (M := M) s g x
        (S.curryLeft (frame a)) (T.curryLeft (frame b)) with hF_def
  -- Reindex `∑ᵢ∑ⱼ∑ₐ∑ᵦ F = ∑ₐ∑ᵦ∑ᵢ∑ⱼ F` by four adjacent swaps.
  have hreindex :
      ∑ i, ∑ j, ∑ a, ∑ b, F i j a b =
        ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm
      (f := fun j a => ∑ b, F i j a b))]
    rw [Finset.sum_comm (f := fun i a => ∑ j, ∑ b, F i j a b)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm
      (f := fun j b => F i j a b))]
    rw [Finset.sum_comm (f := fun i b => ∑ j, F i j a b)]
  rw [hreindex]
  -- For each `(a, b)`, the `(i, j)`-sum collapses to the matrix product.
  have hcollapse : ∀ a b : Fin (Module.finrank ℝ E),
      ∑ i, ∑ j, F i j a b =
        ((mixedGramMatrix (I := I) (M := M) g x frame)ᵀ *
            ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
              mixedGramMatrix (I := I) (M := M) g x frame)) a b *
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (S.curryLeft (frame a)) (T.curryLeft (frame b)) := by
    intro a b
    rw [Matrix.mul_apply]
    rw [show (∑ i, (mixedGramMatrix (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
            mixedGramMatrix (I := I) (M := M) g x frame) i b) *
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      = ∑ i, ((mixedGramMatrix (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
            mixedGramMatrix (I := I) (M := M) g x frame) i b) *
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      from by rw [Finset.sum_mul]]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_apply]
    rw [show ((mixedGramMatrix (I := I) (M := M) g x frame)ᵀ a i *
          ∑ j, (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGramMatrix (I := I) (M := M) g x frame j b) *
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      = ∑ j, ((mixedGramMatrix (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGramMatrix (I := I) (M := M) g x frame j b)) *
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      from by rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.transpose_apply, hF_def]
    ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hcollapse a b))]
  rw [hkey]
  -- The identity matrix collapses the `(a, b)`-sum to the diagonal.
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro b _ hba
    rw [Matrix.one_apply_ne (Ne.symm hba), zero_mul]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-! ## The smooth orthonormal frame as a pointwise basis

Near a point `x`, the smooth orthonormal frame `smoothOrthoFrame g x` is, at
every point `y` of its orthonormality neighbourhood `smoothOrthoFrameNbhd x`, a
`g(y)`-orthonormal basis of `T_yM`. Orthonormality with respect to the
positive-definite metric forces linear independence; the count of vectors
matches `Module.finrank ℝ E`, so the family is a basis. -/

/-- A `g(y)`-orthonormal family of `Module.finrank ℝ E` tangent vectors is
linearly independent. -/
private lemma linearIndependent_of_orthonormal
    (g : SmoothRiemannianMetric I M) {y : M}
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (horth : ∀ a b, g.inner y (frame a) (frame b) = if a = b then 1 else 0) :
    LinearIndependent ℝ frame := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  -- Pair the vanishing combination with `frame b`: `0 = ∑ₐ cₐ g(Eₐ, E_b) = c_b`.
  have hpair : g.inner y (∑ a, c a • frame a) (frame b) = 0 := by
    rw [hc]; simp
  rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
  rw [Finset.sum_eq_single b] at hpair
  · rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, horth b b,
      if_pos rfl, smul_eq_mul, mul_one] at hpair
    exact hpair
  · intro a _ hab
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, horth a b,
      if_neg (by simpa using hab), smul_zero]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

/-- The smooth orthonormal frame at `x`, evaluated at a point `y` of its
orthonormality neighbourhood, packaged as a `Module.Basis` of `T_yM`. -/
private noncomputable def smoothOrthoBasis
    (g : SmoothRiemannianMetric I M) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y) :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun a : Fin (Module.finrank ℝ E) =>
      smoothOrthoFrame (I := I) g x a y)
    (linearIndependent_of_orthonormal (I := I) (M := M) g
      (fun a => smoothOrthoFrame (I := I) g x a y)
      (fun a b => smoothOrthoFrame_orthonormal (I := I) g x hy a b))
    (by
      rw [Fintype.card_fin]
      -- `TangentSpace I y` is definitionally the model space `E`.
      rfl)

@[simp]
private lemma smoothOrthoBasis_apply
    (g : SmoothRiemannianMetric I M) (x : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x)
    (a : Fin (Module.finrank ℝ E)) :
    smoothOrthoBasis (I := I) (M := M) g x hy a =
      smoothOrthoFrame (I := I) g x a y := by
  unfold smoothOrthoBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

/-! ## The directional metric-compatibility differential

The right-hand side of the metric-compatibility identity, as a continuous
linear functional `v ↦ ⟨∇_v W, T⟩ + ⟨W, ∇_v T⟩` on `T_xM`. This packages the
covariant-Leibniz form so that the `HasMFDerivAt` machinery composes cleanly
through the inductive step. -/

open Tensor0SNabla in
/-- The directional metric-compatibility differential for `(0, s)`-tensor
sections `W`, `T`: the continuous linear functional
`v ↦ ⟨(∇_v W) x, T x⟩ + ⟨W x, (∇_v T) x⟩` on `T_xM`. -/
noncomputable def tensorMetricCompatDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W T : Π x : M, Tensor0SSpace s I x) (x : M) :
    TangentSpace I x →L[ℝ] ℝ :=
  ((DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM (I := I) (M := M) g s x).flip
        (Tensor0SSpace.toModel (T x))).comp
      ((Tensor0SSpace.toModelL s x).comp
        (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) W x)) +
    ((DifferentialGeometry.Tensor.Tensor0SRiemannian.innerModelCLM (I := I) (M := M) g s x)
        (Tensor0SSpace.toModel (W x))).comp
      ((Tensor0SSpace.toModelL s x).comp
        (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) T x))

@[simp]
lemma tensorMetricCompatDiff_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W T : Π x : M, Tensor0SSpace s I x) (x : M) (v : TangentSpace I x) :
    tensorMetricCompatDiff (I := I) (M := M) g s W T x v =
      tensorInnerPointwise_0s (I := I) (M := M) s g x
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) W x v))
          (Tensor0SSpace.toModel (T x))
        + tensorInnerPointwise_0s (I := I) (M := M) s g x
          (Tensor0SSpace.toModel (W x))
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) T x v)) := by
  rfl

/-! ## The Hom-Leibniz recursion for the `(0, s)`-tensor covariant derivative

The `(0, s + 1)`-tensor covariant derivative is, by construction, the
`tensor0S_curry`-transport of the Hom-bundle covariant derivative. Unfolding
the Hom-bundle product rule yields the recursion: the rank-`s` covariant
derivative of the partial evaluation `y ↦ (curriedSection W) y (Y y)`
decomposes as the curry of the rank-`(s + 1)` covariant derivative applied to
`Y x`, plus a correction term carrying the tangent-bundle covariant derivative
of the vector field `Y`. -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Tensor0SNabla HomConnection in
/-- **The Hom-Leibniz recursion.** For a `(0, s + 1)`-tensor section `W`
differentiable at `x`, a smooth vector field `Y`, and a tangent vector `v`:

  `∇^s_v (curriedSection W · (Y ·))
     = (curry of ∇^{s+1}_v W) (Y x) + curriedSection W x (∇^{TM}_v Y)`. -/
private lemma tensor0SCovariantDerivative_curriedSection_hom_leibniz
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y : M => curriedSection I M W y (Y y)) x v =
      tensor0S_curry (I := I) (M := M) s x
          (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) W x v)
          (Y x) +
        curriedSection I M W x
          ((LeviCivita (I := I) g).toFun (fun y => Y y) x v) := by
  classical
  -- The curried Hom-bundle section is differentiable at `x`.
  have hC := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  -- A smooth vector field with value `v` at `x`.
  obtain ⟨Vfield, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hVfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Vfield y)) x :=
    Vfield.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hYfield : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  -- The Hom-bundle product rule, unfolded.
  have hHom := HomConnection.homBundleCovariantDerivativeFun_apply_eq
    (I := I) (M := M) (F := Tensor0SModel s ℝ E)
    (V := fun x : M => Tensor0SSpace s I x)
    (cov_TM := LeviCivita (I := I) g)
    (cov_V := tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (τ := curriedSection I M W) (x := x) hC
    (V_field := fun y => Vfield y) (Y := fun y => Y y) hVfield hYfield
  -- `∇^{s+1}_v W` is the curry-transport of the Hom-bundle covariant derivative.
  have hsucc : tensor0S_curry (I := I) (M := M) s x
      (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) W x v) =
      HomConnection.homBundleCovariantDerivativeFun (I := I) (M := M)
        (F := Tensor0SModel s ℝ E)
        (V := fun x : M => Tensor0SSpace s I x)
        (cov_TM := LeviCivita (I := I) g)
        (cov_V := tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (τ := curriedSection I M W) x v := by
    rw [tensor0SCovariantDerivative_succ_eq, tensor0SCovariantDerivative_succ_apply]
    exact (tensor0S_curry (I := I) (M := M) s x).apply_symm_apply _
  -- Combine: rewrite `v` as `Vfield x` so `hHom` applies, then rearrange.
  rw [hsucc]
  rw [show v = Vfield x from hVx.symm]
  rw [hHom]
  -- `hHom`'s RHS is `cov_s (curriedSection W · (Y ·)) x (Vfield x)
  --  − curriedSection W x (∇^{TM} Y x (Vfield x))`.
  abel

/-! ## Skew-symmetry of the connection in the smooth orthonormal frame

The smooth orthonormal frame `smoothOrthoFrame g x` is `g`-orthonormal on the
open neighbourhood `smoothOrthoFrameNbhd x`, so each pairing
`y ↦ g(E_a y, E_b y)` is *locally constant* there. Tangent-bundle metric
compatibility of the Levi-Civita connection then forces the connection 1-form
to be skew-symmetric: `g(∇_v E_a, E_b) + g(E_a, ∇_v E_b) = 0`. -/

/-- **Skew-symmetry of the Levi-Civita connection on a smooth orthonormal
frame.** For the smooth orthonormal frame `smoothOrthoFrame g x` and any
direction `v`, the symmetric part of the connection vanishes at the centre. -/
private lemma smoothOrthoFrame_connection_skew
    (g : SmoothRiemannianMetric I M) (x : M)
    (a b : Fin (Module.finrank ℝ E)) (v : TangentSpace I x) :
    g.inner x
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x a) x v)
        (smoothOrthoFrame (I := I) g x b x)
      + g.inner x
        (smoothOrthoFrame (I := I) g x a x)
        ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x b) x v) = 0 := by
  classical
  -- The smooth orthonormal frame components are smooth sections, hence
  -- manifold-differentiable at `x`.
  have hEa : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x a y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x a).contMDiffAt.mdifferentiableAt (by simp)
  have hEb : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x b y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x b).contMDiffAt.mdifferentiableAt (by simp)
  -- The pairing `y ↦ g(E_a y, E_b y)` is locally constant near `x`.
  have hconst : (fun y : M => g.inner y
        (smoothOrthoFrame (I := I) g x a y)
        (smoothOrthoFrame (I := I) g x b y)) =ᶠ[nhds x]
      (fun _ : M => (if a = b then (1 : ℝ) else 0)) := by
    filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
    exact smoothOrthoFrame_orthonormal (I := I) g x hy a b
  -- A locally-constant function has vanishing directional derivative.
  have hmfderiv0 : mfderiv I 𝓘(ℝ) (fun y : M => g.inner y
        (smoothOrthoFrame (I := I) g x a y)
        (smoothOrthoFrame (I := I) g x b y)) x v = 0 := by
    rw [hconst.mfderiv_eq, mfderiv_const]
    rfl
  -- Tangent-bundle metric compatibility relates this derivative to the
  -- symmetric part of the connection.
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply
    (Y := fun y => smoothOrthoFrame (I := I) g x a y)
    (Z := fun y => smoothOrthoFrame (I := I) g x b y)
    (x := x) hEa hEb v
  rw [hmfderiv0] at hmc
  exact hmc.symm

/-! ## The smooth orthonormal frame packaged as a smooth section -/

open Tensor0SNabla in
/-- The `a`-th component of the smooth orthonormal frame at `x`, packaged as a
smooth section `Cₛ^∞⟮I; E, TangentSpace I⟯`. -/
private noncomputable def smoothOrthoFrameSection
    (g : SmoothRiemannianMetric I M) (x : M) (a : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨smoothOrthoFrame (I := I) g x a, smoothOrthoFrame_smooth (I := I) g x a⟩

@[simp]
private lemma smoothOrthoFrameSection_apply
    (g : SmoothRiemannianMetric I M) (x : M) (a : Fin (Module.finrank ℝ E)) (y : M) :
    smoothOrthoFrameSection (I := I) (M := M) g x a y =
      smoothOrthoFrame (I := I) g x a y := rfl

open Tensor0SNabla in
/-- The partial evaluation `y ↦ (curriedSection W) y (Y y)` of a `(0, s + 1)`-tensor
section `W` differentiable at `x` against a smooth vector field `Y` is a
`(0, s)`-tensor section differentiable at `x`. -/
private lemma tensorSectionMDiffAt_curriedSection_apply
    (s : ℕ) (W : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    TensorSectionMDiffAt (I := I) s
      (fun y : M => curriedSection I M W y (Y y)) x := by
  classical
  unfold TensorSectionMDiffAt
  have hCurried := mdifferentiableAt_curriedSection_of_section (I := I) (M := M) s W hW
  have hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (Y y)) x :=
    Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (𝕜 := ℝ)
    (F₁ := E) (F₂ := Tensor0SModel s ℝ E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => Tensor0SSpace s I x)
    (IM := I) (IB := I)
    (b := id) (ϕ := fun y : M => curriedSection I M W y)
    (v := fun y : M => Y y) hCurried hY

/-! ## The crux: assembling the rank-`(s + 1)` differential from the rank-`s`
differentials of the frame partial evaluations

The inductive step expresses the rank-`(s + 1)` metric-compatibility differential
as the sum, over the smooth orthonormal frame, of the rank-`s` differentials of
the partial evaluations. The Hom-Leibniz recursion splits each summand into a
"genuine gradient" part — which reassembles, by frame independence, into the
rank-`(s + 1)` differential — and an "error" part carrying the covariant
derivative of the frame; the error part vanishes by skew-symmetry of the
connection on the orthonormal frame. -/

open Tensor0SNabla in
/-- **The crux identity.** The sum, over the smooth orthonormal frame, of the
rank-`s` metric-compatibility differentials of the frame partial evaluations of
`W`, `T` equals the rank-`(s + 1)` metric-compatibility differential of `W`,
`T`. -/
private lemma tensorMetricCompatDiff_succ_eq_sum
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W T : Π x : M, Tensor0SSpace (s + 1) I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) (s + 1) W x)
    (hT : TensorSectionMDiffAt (I := I) (s + 1) T x) :
    ∑ a : Fin (Module.finrank ℝ E),
        tensorMetricCompatDiff (I := I) (M := M) g s
          (fun y : M => curriedSection I M W y
            (smoothOrthoFrameSection (I := I) (M := M) g x a y))
          (fun y : M => curriedSection I M T y
            (smoothOrthoFrameSection (I := I) (M := M) g x a y)) x =
      tensorMetricCompatDiff (I := I) (M := M) g (s + 1) W T x := by
  classical
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.sum_apply, tensorMetricCompatDiff_apply]
  -- Notation for the frame, the frame partial evaluations, and the
  -- orthonormal basis at `x`.
  set n := Module.finrank ℝ E with hn_def
  set E_ := fun a : Fin n => smoothOrthoFrameSection (I := I) (M := M) g x a with hE_def
  set WC := fun a : Fin n => fun y : M => curriedSection I M W y (E_ a y) with hWC_def
  set TC := fun a : Fin n => fun y : M => curriedSection I M T y (E_ a y) with hTC_def
  have hx_mem : x ∈ smoothOrthoFrameNbhd (I := I) (M := M) x :=
    mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x
  set frameB := smoothOrthoBasis (I := I) (M := M) g x hx_mem with hframeB_def
  have hframeB_orth : ∀ a b, g.inner x (frameB a) (frameB b) = if a = b then 1 else 0 := by
    intro a b
    rw [hframeB_def, smoothOrthoBasis_apply, smoothOrthoBasis_apply]
    exact smoothOrthoFrame_orthonormal (I := I) g x hx_mem a b
  have hframeB_apply : ∀ a, frameB a = smoothOrthoFrame (I := I) g x a x := by
    intro a; rw [hframeB_def, smoothOrthoBasis_apply]
  have hframeB_E : ∀ a : Fin n, frameB a = E_ a x := by
    intro a; rw [hframeB_apply a, hE_def]; rfl
  -- Abbreviations for the rank-`(s + 1)` covariant derivatives and the
  -- connection coefficients of the frame.
  set Pw := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) W x v
    with hPw_def
  set Pt := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) T x v
    with hPt_def
  set omgW := fun a : Fin n =>
    (LeviCivita (I := I) g).toFun (fun y => E_ a y) x v with homgW_def
  -- Per-`a` Hom-Leibniz expansion of the two rank-`s` covariant derivatives.
  have hWleib : ∀ a : Fin n,
      tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) (WC a) x v =
        tensor0S_curry (I := I) (M := M) s x Pw (E_ a x) +
          curriedSection I M W x (omgW a) := by
    intro a
    exact tensor0SCovariantDerivative_curriedSection_hom_leibniz
      (I := I) (M := M) g s W hW (E_ a) v
  have hTleib : ∀ a : Fin n,
      tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) (TC a) x v =
        tensor0S_curry (I := I) (M := M) s x Pt (E_ a x) +
          curriedSection I M T x (omgW a) := by
    intro a
    exact tensor0SCovariantDerivative_curriedSection_hom_leibniz
      (I := I) (M := M) g s T hT (E_ a) v
  -- The model coercion `toModel` of a `tensor0S_curry`-image is `curryLeft`.
  have hcurryW : ∀ a : Fin n, Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x Pw (E_ a x)) =
      (Tensor0SSpace.toModel Pw).curryLeft (E_ a x) := fun a =>
    toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) Pw (E_ a x)
  have hcurryT : ∀ a : Fin n, Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) s x Pt (E_ a x)) =
      (Tensor0SSpace.toModel Pt).curryLeft (E_ a x) := fun a =>
    toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) Pt (E_ a x)
  -- The model coercion of `WC a x` / `TC a x` is `curryLeft` of `W x` / `T x`.
  have hWCmodel : ∀ a : Fin n,
      Tensor0SSpace.toModel (WC a x) =
        (Tensor0SSpace.toModel (W x)).curryLeft (E_ a x) := by
    intro a
    rw [hWC_def]
    exact toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) (W x) (E_ a x)
  have hTCmodel : ∀ a : Fin n,
      Tensor0SSpace.toModel (TC a x) =
        (Tensor0SSpace.toModel (T x)).curryLeft (E_ a x) := by
    intro a
    rw [hTC_def]
    exact toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) (T x) (E_ a x)
  -- Expand each summand via `tensorMetricCompatDiff_apply` and the Hom-Leibniz
  -- splittings; then use additivity of the rank-`s` inner product.
  have hsummand : ∀ a : Fin n,
      tensorMetricCompatDiff (I := I) (M := M) g s (WC a) (TC a) x v =
        (tensorInnerPointwise_0s (I := I) (M := M) s g x
            ((Tensor0SSpace.toModel Pw).curryLeft (E_ a x))
            (Tensor0SSpace.toModel (TC a x)) +
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (Tensor0SSpace.toModel (WC a x))
            ((Tensor0SSpace.toModel Pt).curryLeft (E_ a x))) +
        (tensorInnerPointwise_0s (I := I) (M := M) s g x
            (Tensor0SSpace.toModel (curriedSection I M W x (omgW a)))
            (Tensor0SSpace.toModel (TC a x)) +
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (Tensor0SSpace.toModel (WC a x))
            (Tensor0SSpace.toModel (curriedSection I M T x (omgW a)))) := by
    intro a
    rw [tensorMetricCompatDiff_apply]
    rw [hWleib a, hTleib a]
    rw [Tensor0SBundle.Tensor0SSpace.toModel_add,
      Tensor0SBundle.Tensor0SSpace.toModel_add]
    rw [tensorInnerPointwise_0s_add_left, tensorInnerPointwise_0s_add_right]
    rw [hcurryW a, hcurryT a]
    ring
  rw [Finset.sum_congr rfl (fun a _ => hsummand a)]
  rw [Finset.sum_add_distrib]
  -- The "genuine gradient" part reassembles via frame independence.
  have hmain :
      ∑ a : Fin n,
          (tensorInnerPointwise_0s (I := I) (M := M) s g x
              ((Tensor0SSpace.toModel Pw).curryLeft (E_ a x))
              (Tensor0SSpace.toModel (TC a x)) +
            tensorInnerPointwise_0s (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (WC a x))
              ((Tensor0SSpace.toModel Pt).curryLeft (E_ a x))) =
        tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x
            (Tensor0SSpace.toModel Pw) (Tensor0SSpace.toModel (T x)) +
          tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x
            (Tensor0SSpace.toModel (W x)) (Tensor0SSpace.toModel Pt) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [tensorInnerPointwise_0s_succ_orthoFrame (I := I) (M := M) g x s frameB
        hframeB_orth]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hframeB_E a, hTCmodel a]
    · rw [tensorInnerPointwise_0s_succ_orthoFrame (I := I) (M := M) g x s frameB
        hframeB_orth]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hframeB_E a, hWCmodel a]
  -- The "error" part vanishes by skew-symmetry of the connection.
  have herror :
      ∑ a : Fin n,
          (tensorInnerPointwise_0s (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (curriedSection I M W x (omgW a)))
              (Tensor0SSpace.toModel (TC a x)) +
            tensorInnerPointwise_0s (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (WC a x))
              (Tensor0SSpace.toModel (curriedSection I M T x (omgW a)))) = 0 := by
    -- Expand `omgW a` in the orthonormal basis: `omgW a = ∑ᵦ omg a b • frameB b`.
    set omg := fun a b : Fin n => g.inner x (omgW a) (frameB b) with homg_def
    have homgexp : ∀ a : Fin n, omgW a = ∑ b : Fin n, omg a b • frameB b := by
      intro a
      rw [homg_def]
      exact orthonormal_expansion (I := I) (M := M) g x frameB hframeB_orth (omgW a)
    -- `curriedSection W x (omgW a) = ∑ᵦ (omg a b) • WC b x`, and likewise for `T`.
    have hWcurried : ∀ a : Fin n,
        Tensor0SSpace.toModel (curriedSection I M W x (omgW a)) =
          ∑ b : Fin n, omg a b • Tensor0SSpace.toModel (WC b x) := by
      intro a
      have htensor : curriedSection I M W x (omgW a) =
          ∑ b : Fin n, omg a b • WC b x := by
        rw [homgexp a, map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul]
        congr 1
        rw [hWC_def, hframeB_E b]
      rw [htensor]
      rw [← Tensor0SBundle.Tensor0SSpace.toModelL_apply, map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [map_smul, Tensor0SBundle.Tensor0SSpace.toModelL_apply]
    have hTcurried : ∀ a : Fin n,
        Tensor0SSpace.toModel (curriedSection I M T x (omgW a)) =
          ∑ b : Fin n, omg a b • Tensor0SSpace.toModel (TC b x) := by
      intro a
      have htensor : curriedSection I M T x (omgW a) =
          ∑ b : Fin n, omg a b • TC b x := by
        rw [homgexp a, map_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [map_smul]
        congr 1
        rw [hTC_def, hframeB_E b]
      rw [htensor]
      rw [← Tensor0SBundle.Tensor0SSpace.toModelL_apply, map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [map_smul, Tensor0SBundle.Tensor0SSpace.toModelL_apply]
    -- Substitute and expand the rank-`s` inner products bilinearly.
    have hexpand : ∀ a : Fin n,
        tensorInnerPointwise_0s (I := I) (M := M) s g x
            (Tensor0SSpace.toModel (curriedSection I M W x (omgW a)))
            (Tensor0SSpace.toModel (TC a x)) +
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (Tensor0SSpace.toModel (WC a x))
            (Tensor0SSpace.toModel (curriedSection I M T x (omgW a))) =
        ∑ b : Fin n,
          (omg a b * tensorInnerPointwise_0s (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (WC b x)) (Tensor0SSpace.toModel (TC a x)) +
            omg a b * tensorInnerPointwise_0s (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (WC a x)) (Tensor0SSpace.toModel (TC b x))) := by
      intro a
      rw [hWcurried a, hTcurried a]
      rw [tensorInnerPointwise_0s_sum_smul_left (I := I) (M := M) g x s
        (A := (Finset.univ : Finset (Fin n)))]
      rw [tensorInnerPointwise_0s_sum_smul_right (I := I) (M := M) g x s
        (A := (Finset.univ : Finset (Fin n)))]
      rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun a _ => hexpand a)]
    -- Split the double sum and swap indices in the second part so both parts
    -- pair the same inner products `⟨WC b x, TC a x⟩`.
    have hsplit :
        ∑ a : Fin n, ∑ b : Fin n,
            (omg a b * tensorInnerPointwise_0s (I := I) (M := M) s g x
                (Tensor0SSpace.toModel (WC b x)) (Tensor0SSpace.toModel (TC a x)) +
              omg a b * tensorInnerPointwise_0s (I := I) (M := M) s g x
                (Tensor0SSpace.toModel (WC a x)) (Tensor0SSpace.toModel (TC b x))) =
          ∑ a : Fin n, ∑ b : Fin n,
            (omg a b + omg b a) * tensorInnerPointwise_0s (I := I) (M := M) s g x
              (Tensor0SSpace.toModel (WC b x)) (Tensor0SSpace.toModel (TC a x)) := by
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib)]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_comm
        (f := fun a b => omg a b * tensorInnerPointwise_0s (I := I) (M := M) s g x
          (Tensor0SSpace.toModel (WC a x)) (Tensor0SSpace.toModel (TC b x)))]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [add_mul]
    rw [hsplit]
    -- Each summand vanishes by skew-symmetry of the connection.
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    -- `omg a b + omg b a = g(∇E_a, E_b x) + g(E_a x, ∇E_b) = 0`.
    have hskew : omg a b + omg b a = 0 := by
      have homg_ab : omg a b =
          g.inner x
            ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x a) x v)
            (smoothOrthoFrame (I := I) g x b x) := by
        simp only [homg_def, homgW_def, hE_def, smoothOrthoFrameSection_apply]
        rw [hframeB_apply b]
      have homg_ba : omg b a =
          g.inner x
            (smoothOrthoFrame (I := I) g x a x)
            ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x b) x v) := by
        simp only [homg_def, homgW_def, hE_def, smoothOrthoFrameSection_apply]
        rw [hframeB_apply a]
        exact g.symm x _ _
      rw [homg_ab, homg_ba]
      exact smoothOrthoFrame_connection_skew (I := I) (M := M) g x a b v
    rw [hskew, zero_mul]
  rw [hmain, herror, add_zero]

/-! ## The directional metric-compatibility identity for `(0, s)`-tensors

The auxiliary induction. We prove the `HasMFDerivAt` form (which simultaneously
records differentiability and the value of the derivative), since this is what
the `HasMFDerivAt.sum` step of the induction consumes. -/

open Tensor0SNabla in
/-- **Auxiliary `HasMFDerivAt` induction.** For all `(0, s)`-tensor sections
`W`, `T` differentiable at `x`, the pointwise inner product
`y ↦ ⟨W y, T y⟩` has manifold-derivative `tensorMetricCompatDiff g s W T x` at
`x`. The induction is on covariant rank `s`. -/
theorem tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_aux
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∀ (W T : Π x : M, Tensor0SSpace s I x) {x : M},
      TensorSectionMDiffAt (I := I) s W x → TensorSectionMDiffAt (I := I) s T x →
      HasMFDerivAt I 𝓘(ℝ, ℝ)
        (fun y : M => tensorInnerPointwise_0s (I := I) (M := M) s g y
          (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) x
        (tensorMetricCompatDiff (I := I) (M := M) g s W T x) := by
  classical
  induction s with
  | zero =>
      intro W T x hW hT
      -- The `(0, 0)` pointwise inner product is the product of scalar functions.
      have hW' : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M W) x :=
        (mdifferentiableAt_scalarFn_iff_section (I := I) (M := M) W).mpr hW
      have hT' : MDifferentiableAt I 𝓘(ℝ, ℝ) (scalarFn I M T) x :=
        (mdifferentiableAt_scalarFn_iff_section (I := I) (M := M) T).mpr hT
      have hfun : (fun y : M => tensorInnerPointwise_0s (I := I) (M := M) 0 g y
            (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) =
          fun y : M => scalarFn I M W y * scalarFn I M T y := by
        funext y
        rw [tensorInnerPointwise_0s_zero_eq_scalarFn_mul (I := I) (M := M) g W T y]
      rw [hfun]
      -- The product of two differentiable scalars is differentiable.
      have hmdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun y : M => scalarFn I M W y * scalarFn I M T y) x :=
        (hW'.hasMFDerivAt.mul hT'.hasMFDerivAt).mdifferentiableAt
      -- Identify `mfderiv` with the metric-compatibility differential via the
      -- shipped rank-`0` identity.
      refine hmdiff.hasMFDerivAt.congr_mfderiv (ContinuousLinearMap.ext (fun v => ?_))
      have hzero := tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_zero
        (I := I) (M := M) g W T hW' hT' v
      rw [hfun] at hzero
      exact hzero.trans (tensorMetricCompatDiff_apply (I := I) (M := M) g 0 W T x v).symm
  | succ s ih =>
      intro W T x hW hT
      -- The smooth orthonormal frame and the frame partial evaluations.
      set WC := fun a : Fin (Module.finrank ℝ E) => fun y : M =>
        curriedSection I M W y
          (smoothOrthoFrameSection (I := I) (M := M) g x a y) with hWC_def
      set TC := fun a : Fin (Module.finrank ℝ E) => fun y : M =>
        curriedSection I M T y
          (smoothOrthoFrameSection (I := I) (M := M) g x a y) with hTC_def
      -- Each frame partial evaluation is a `(0, s)`-tensor section differentiable
      -- at `x`.
      have hWCdiff : ∀ a, TensorSectionMDiffAt (I := I) s (WC a) x := fun a =>
        tensorSectionMDiffAt_curriedSection_apply (I := I) (M := M) s W hW
          (smoothOrthoFrameSection (I := I) (M := M) g x a)
      have hTCdiff : ∀ a, TensorSectionMDiffAt (I := I) s (TC a) x := fun a =>
        tensorSectionMDiffAt_curriedSection_apply (I := I) (M := M) s T hT
          (smoothOrthoFrameSection (I := I) (M := M) g x a)
      -- The inductive hypothesis applied to each frame partial evaluation.
      have hIH : ∀ a, HasMFDerivAt I 𝓘(ℝ, ℝ)
          (fun y : M => tensorInnerPointwise_0s (I := I) (M := M) s g y
            (Tensor0SSpace.toModel (WC a y)) (Tensor0SSpace.toModel (TC a y))) x
          (tensorMetricCompatDiff (I := I) (M := M) g s (WC a) (TC a) x) := fun a =>
        ih (WC a) (TC a) (hWCdiff a) (hTCdiff a)
      -- Sum the `HasMFDerivAt` statements over the frame.
      have hSum := HasMFDerivAt.sum (t := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        (f := fun a => fun y : M => tensorInnerPointwise_0s (I := I) (M := M) s g y
          (Tensor0SSpace.toModel (WC a y)) (Tensor0SSpace.toModel (TC a y)))
        (f' := fun a => tensorMetricCompatDiff (I := I) (M := M) g s (WC a) (TC a) x)
        (fun a _ => hIH a)
      -- The headline function is locally the diagonal frame sum.
      have hEq : (fun y : M => tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g y
            (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) =ᶠ[nhds x]
          (∑ a : Fin (Module.finrank ℝ E),
            fun y : M => tensorInnerPointwise_0s (I := I) (M := M) s g y
              (Tensor0SSpace.toModel (WC a y)) (Tensor0SSpace.toModel (TC a y))) := by
        filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
        rw [Finset.sum_apply]
        -- Frame independence at `y` for the orthonormal basis `smoothOrthoBasis g x hy`.
        rw [tensorInnerPointwise_0s_succ_orthoFrame (I := I) (M := M) g y s
          (smoothOrthoBasis (I := I) (M := M) g x hy)
          (fun a b => by
            rw [smoothOrthoBasis_apply, smoothOrthoBasis_apply]
            exact smoothOrthoFrame_orthonormal (I := I) g x hy a b)]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        -- `(toModel (W y)).curryLeft (frame a) = toModel (WC a y)`.
        rw [hWC_def, hTC_def]
        rw [show smoothOrthoBasis (I := I) (M := M) g x hy a =
            smoothOrthoFrameSection (I := I) (M := M) g x a y from by
          rw [smoothOrthoBasis_apply]; rfl]
        rw [← toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) (W y),
          ← toModel_tensor0S_curry_eq_curryLeft (I := I) (M := M) (T y)]
        rfl
      -- Transport the summed `HasMFDerivAt` across the local equality, and
      -- identify the summed differential with the rank-`(s + 1)` differential.
      have hSum' := hSum.congr_of_eventuallyEq hEq
      rwa [tensorMetricCompatDiff_succ_eq_sum (I := I) (M := M) g s W T hW hT] at hSum'

/-! ## Directional metric compatibility of the `(0, s)`-tensor connection -/

open Tensor0SNabla in
/-- Directional metric compatibility (covariant Leibniz rule) of the `(0, s)`-tensor
Levi-Civita connection, for arbitrary covariant rank `s`. For two `(0, s)`-tensor
sections `W`, `T` (given in total-space form) that are tensor-section
differentiable at `x`, and every tangent vector `v`, the directional derivative
at `x` (along `v`) of the pointwise metric-induced inner product
`y ↦ tensorInnerPointwise_0s s g y (W y) (T y)` equals

  `⟨∇_v W, T⟩ + ⟨W, ∇_v T⟩`,

where `∇` is `tensor0SCovariantDerivative` for the Levi-Civita connection of `g`.
This is the general-rank statement, proved by induction on `s` from the
covariant-rank-`0` base case
`tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_zero`. -/
theorem tensorInnerPointwise_0s_mfderiv_metricCompatible
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W T : Π x : M, Tensor0SSpace s I x) {x : M}
    (hW : TensorSectionMDiffAt (I := I) s W x)
    (hT : TensorSectionMDiffAt (I := I) s T x)
    (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, ℝ)
        (fun y : M => tensorInnerPointwise_0s (I := I) (M := M) s g y
          (Tensor0SSpace.toModel (W y)) (Tensor0SSpace.toModel (T y))) x v =
      tensorInnerPointwise_0s (I := I) (M := M) s g x
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) W x v))
          (Tensor0SSpace.toModel (T x))
        + tensorInnerPointwise_0s (I := I) (M := M) s g x
          (Tensor0SSpace.toModel (W x))
          (Tensor0SSpace.toModel
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g) T x v)) := by
  have hmf := (tensorInnerPointwise_0s_hasMFDerivAt_metricCompatible_aux
    (I := I) (M := M) g s W T hW hT).mfderiv
  rw [hmf]
  exact tensorMetricCompatDiff_apply (I := I) (M := M) g s W T x v

end Connection
end Integral
end DifferentialGeometry

end
