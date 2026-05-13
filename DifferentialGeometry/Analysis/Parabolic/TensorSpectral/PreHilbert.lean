import DifferentialGeometry.Integral.L2.SmoothSections.PreHilbert
import DifferentialGeometry.Integral.L2.SmoothSections.Integrability
import DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import DifferentialGeometry.Integral.Connection.TensorRSNabla
import DifferentialGeometry.Integral.Connection.Curvature
import DifferentialGeometry.Integral.Connection.LeviCivita
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Tensor.Multilinear.MetricLowering
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
import DifferentialGeometry.Tensor.RSTensor.TensorRSRiemannian
import DifferentialGeometry.Geometry.Gradient
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousOn

/-!
# H^1 pre-Hilbert structure on compactly-supported smooth tensor sections

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file installs an `H^1` (gradient-augmented)
pre-Hilbert structure on a wrapper type around `SmoothCcTensor g r s`.

The `H^1` inner product is the sum of the `L^2` inner product of the sections
and the `L^2` inner product of their covariant derivatives, the latter
computed against the inverse Gram matrix of `g` on the canonical model basis:

  ⟨S, T⟩_{H^1} := tensorL2Inner g r s S.toFun T.toFun
                + ∫_M ∑_{i, j} (G(x)⁻¹)_{ij}
                    ⟨(∇S)(x)(e_i), (∇T)(x)(e_j)⟩_g dvol_g

where `∇` is the Levi-Civita-induced covariant derivative on the
`(r, s)`-tensor bundle, `e_i = chartModelBasis E i` is the fixed model-fibre
basis, `(G(x)⁻¹)_{ij} = (gramMatrixAt g x)⁻¹ i j` is the inverse Gram matrix
of `g` on that basis, and `⟨·, ·⟩_g` is the pointwise metric inner product
on tensor fibres.

## Main constructions

* `tensorCovDerivAt g r s S x v` — the directional covariant derivative of a
  smooth compactly-supported `(r, s)`-tensor section at a point.
* `tensorCovDerivPointwiseInner g r s S T x` — the metric-induced pointwise
  Hilbert-Schmidt inner product of two covariant derivatives at a point.
* `tensorH1Inner g r s S T` — the global `H^1` inner product.
* `SmoothCcTensorH1 g r s` — a wrapper around `SmoothCcTensor g r s` carrying
  the `H^1` pre-Hilbert structure.
* `instPreInnerProductSpaceCore` (in the `SmoothCcTensorH1` setting),
  `instSeminormedAddCommGroup`, `instInnerProductSpace`.

## Strategy

The four `PreInnerProductSpace.Core` axioms reduce to algebraic properties
of `tensorL2Inner` (the `L^2` part, already established in companion files)
together with the analogous algebraic properties of the gradient term:

* symmetry, additivity, and homogeneity hold pointwise and integrate;
* non-negativity of the gradient term on the diagonal follows from the same
  spectral argument used in `tensorInnerPointwise_0s_nonneg`.

Integrability of the cross-gradient term is the key analytic ingredient. On a
closed manifold the Riemannian volume measure is finite, so it suffices to
bound the integrand by a continuous (hence bounded on compact `M`) function
and to verify AE-strong measurability. Both properties are obtained by a
chart-by-chart argument that converts the model-frame double sum to the
chart-basis-frame double sum, the latter built from smooth bundle sections
via `covApply_contMDiffOn`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Directional covariant derivative on `SmoothCcTensor` -/

/-- The directional covariant derivative of a smooth compactly-supported
`(r, s)`-tensor section at a point `x`, along a model-fibre direction `v : E`
(canonically identified with `TangentSpace I x`). -/
noncomputable def tensorCovDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (v : E) :
    TensorRSSpace r s I x :=
  tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    (fun y : M => S.toSection y) x v

/-- Unfolding lemma for `tensorCovDerivAt`. -/
lemma tensorCovDerivAt_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s S x v =
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
        (fun y : M => S.toSection y) x v := rfl

/-! ## Algebraic properties of `tensorCovDerivAt` -/

/-- The directional covariant derivative is additive in the section. -/
lemma tensorCovDerivAt_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s (S₁ + S₂) x v =
      tensorCovDerivAt (I := I) (M := M) g r s S₁ x v +
        tensorCovDerivAt (I := I) (M := M) g r s S₂ x v := by
  unfold tensorCovDerivAt
  have hpt : (fun y : M => (S₁ + S₂).toSection y) =
      (fun y : M => S₁.toSection y) + (fun y : M => S₂.toSection y) := by
    funext y
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [hpt]
  have hadd := (tensorRSCovariantDerivative I M r s
    (LeviCivita (I := I) g)).isCovariantDerivativeOn.add
    (σ := fun y : M => S₁.toSection y)
    (σ' := fun y : M => S₂.toSection y)
    (S₁.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
    (S₂.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
    (by trivial : x ∈ (Set.univ : Set M))
  have hclm : (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
        (fun y : M => S₁.toSection y + S₂.toSection y) x =
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => S₁.toSection y) x +
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => S₂.toSection y) x := hadd
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      (fun y : M => S₁.toSection y + S₂.toSection y) x v = _
  rw [hclm]
  -- `(A + B) v = A v + B v` for CLMs.
  rfl

/-- The directional covariant derivative is `ℝ`-homogeneous in the section. -/
lemma tensorCovDerivAt_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s (c • S) x v =
      c • tensorCovDerivAt (I := I) (M := M) g r s S x v := by
  unfold tensorCovDerivAt
  have hpt : (fun y : M => (c • S).toSection y) =
      (fun _ : M => c) • (fun y : M => S.toSection y) := by
    funext y
    rw [SmoothCcTensor.toSection_smul]
    rfl
  rw [hpt]
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  -- The constant function `M → ℝ` is differentiable at `x`.
  have hf_mdiff : MDiffAt (fun y : M => c) x :=
    (hf_smooth.mdifferentiable (by norm_num)).mdifferentiableAt
  have hcov_leibniz :=
    (tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.leibniz
      (σ := fun y : M => S.toSection y)
      (g := fun _ : M => c)
      (hσ := (S.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt)
      (hg := hf_mdiff)
      (hx := (by trivial : x ∈ (Set.univ : Set M)))
  -- `extDerivFun (fun _ => c) x = 0` since constant functions have zero derivative.
  have hext_zero : extDerivFun (I := I) (fun _ : M => c) x = 0 := by
    unfold extDerivFun
    simp [mfderiv_const]
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      ((fun _ : M => c) • fun y : M => S.toSection y) x v = _
  rw [hcov_leibniz]
  -- After leibniz: `c • cov σ x + (extDerivFun (const c) x).smulRight (σ x)`,
  -- applied to `v`. The second term has factor `extDerivFun (const c) x = 0`.
  rw [hext_zero]
  simp [ContinuousLinearMap.smul_apply]

/-! ## Pointwise H^1 gradient inner product -/

/-- The pointwise Hilbert-Schmidt-type inner product of the covariant
derivatives of two smooth compactly-supported `(r, s)`-tensor sections at a
point `x`, expanded against the inverse Gram matrix of `g(x)` on the canonical
model-fibre basis. -/
noncomputable def tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) i)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T x ((chartModelBasis E) j)))

/-- Unfolding lemma for `tensorCovDerivPointwiseInner`. -/
lemma tensorCovDerivPointwiseInner_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise (I := I) (M := M) g r s x
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S x
                ((chartModelBasis E) i)))
            (TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s T x
                ((chartModelBasis E) j))) := rfl

/-! ## Algebraic properties of `tensorCovDerivPointwiseInner` -/

/-- Symmetry of the pointwise gradient inner product. -/
lemma tensorCovDerivPointwiseInner_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s T S x := by
  unfold tensorCovDerivPointwiseInner
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  have hG : (gramMatrixAt (I := I) (M := M) g x)⁻¹ j i =
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j := by
    have hherm := gramMatrixAt_inv_isHermitian (I := I) (M := M) g x
    have := hherm.apply i j
    simpa [star_trivial] using this
  rw [hG]
  rw [tensorInnerPointwise_symm]

/-- Additivity in the first argument of the pointwise gradient inner product. -/
lemma tensorCovDerivPointwiseInner_add_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s (S₁ + S₂) T x =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₁ T x +
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₂ T x := by
  unfold tensorCovDerivPointwiseInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hAdd : tensorCovDerivAt (I := I) (M := M) g r s (S₁ + S₂) x
        ((chartModelBasis E) i) =
      tensorCovDerivAt (I := I) (M := M) g r s S₁ x ((chartModelBasis E) i) +
        tensorCovDerivAt (I := I) (M := M) g r s S₂ x ((chartModelBasis E) i) :=
    tensorCovDerivAt_add (I := I) (M := M) g r s S₁ S₂ x ((chartModelBasis E) i)
  rw [hAdd, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  ring

/-- Homogeneity in the first argument of the pointwise gradient inner product. -/
lemma tensorCovDerivPointwiseInner_smul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s (c • S) T x =
      c * tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x := by
  unfold tensorCovDerivPointwiseInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hSmul : tensorCovDerivAt (I := I) (M := M) g r s (c • S) x
        ((chartModelBasis E) i) =
      c • tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) i) :=
    tensorCovDerivAt_smul (I := I) (M := M) g r s c S x ((chartModelBasis E) i)
  rw [hSmul, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left]
  ring

/-- Non-negativity of the pointwise gradient inner product on the diagonal,
proved by the spectral argument: diagonalise the inverse Gram matrix,
re-expand the sum into a sum of squares of the pointwise inner product, each
of which is non-negative. -/
lemma tensorCovDerivPointwiseInner_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) :
    0 ≤ tensorCovDerivPointwiseInner (I := I) (M := M) g r s S S x := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set Ginv : Matrix (Fin n) (Fin n) ℝ :=
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv
  have hGinv_psd : Ginv.PosSemidef := by
    simpa [hGinv] using gramMatrixAt_inv_posSemidef (I := I) (M := M) g x
  have hGinv_herm : Ginv.IsHermitian := hGinv_psd.isHermitian
  set vfam : Fin n → TensorRSModel r s ℝ E :=
    fun i => TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) i))
    with hvfam_def
  have hspec := hGinv_herm.spectral_theorem
  set U : Matrix (Fin n) (Fin n) ℝ :=
    (hGinv_herm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU_def
  set μ : Fin n → ℝ := hGinv_herm.eigenvalues with hμ_def
  have hμ_nonneg : ∀ k, 0 ≤ μ k := hGinv_psd.eigenvalues_nonneg
  have hGinv_entry :
      ∀ i j : Fin n,
        Ginv i j = ∑ k : Fin n, μ k * (U i k * U j k) := by
    intro i j
    have hUDstar : Ginv = U * (Matrix.diagonal μ) * star U := by
      have := hspec
      simp only [Unitary.conjStarAlgAut_apply] at this
      have hofReal : (RCLike.ofReal ∘ hGinv_herm.eigenvalues :
          Fin n → ℝ) = hGinv_herm.eigenvalues := by
        funext k
        simp
      rw [hofReal] at this
      exact this
    rw [hUDstar]
    rw [Matrix.mul_apply]
    have hUD_entry : ∀ k : Fin n,
        (U * Matrix.diagonal μ) i k = U i k * μ k := by
      intro k
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single k]
      · simp [Matrix.diagonal]
      · intro l _ hl
        simp [Matrix.diagonal, hl]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hUD_entry k]
    have hstar : (star U) k j = U j k := by
      simp [Matrix.star_apply, star_trivial]
    rw [hstar]
    ring
  unfold tensorCovDerivPointwiseInner
  change 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
    Ginv i j * tensorInnerPointwise (I := I) (M := M) g r s x (vfam i) (vfam j)
  have hrewrite :
      ∑ i : Fin n, ∑ j : Fin n,
        Ginv i j *
          tensorInnerPointwise (I := I) (M := M) g r s x (vfam i) (vfam j)
        = ∑ k : Fin n, μ k *
          tensorInnerPointwise (I := I) (M := M) g r s x
            (∑ i : Fin n, U i k • vfam i)
            (∑ j : Fin n, U j k • vfam j) := by
    -- Generic helper: bilinearity in the first argument over a finite sum.
    have hsum_left :
        ∀ (A : Finset (Fin n)) (a : Fin n → ℝ)
          (φ : Fin n → TensorRSModel r s ℝ E)
          (T₀ : TensorRSModel r s ℝ E),
          tensorInnerPointwise (I := I) (M := M) g r s x
              (∑ i ∈ A, a i • φ i) T₀
              =
            ∑ i ∈ A,
              tensorInnerPointwise (I := I) (M := M) g r s x
                (a i • φ i) T₀ := by
      intro A a φ T₀
      classical
      induction A using Finset.induction with
      | empty =>
          simp [tensorInnerPointwise_zero_left]
      | insert i A hi ih =>
          rw [Finset.sum_insert hi]
          rw [tensorInnerPointwise_add_left]
          rw [ih]
          rw [Finset.sum_insert hi]
    -- Generic helper: bilinearity in the second argument over a finite sum.
    have hsum_right :
        ∀ (A : Finset (Fin n))
          (S₀ : TensorRSModel r s ℝ E)
          (a : Fin n → ℝ) (φ : Fin n → TensorRSModel r s ℝ E),
          tensorInnerPointwise (I := I) (M := M) g r s x
              S₀ (∑ j ∈ A, a j • φ j)
              =
            ∑ j ∈ A,
              tensorInnerPointwise (I := I) (M := M) g r s x
                S₀ (a j • φ j) := by
      intro A S₀ a φ
      classical
      induction A using Finset.induction with
      | empty =>
          simp [tensorInnerPointwise_zero_right]
      | insert j A hj ih =>
          rw [Finset.sum_insert hj]
          rw [tensorInnerPointwise_add_right]
          rw [ih]
          rw [Finset.sum_insert hj]
    have hbilin :
        ∀ k : Fin n,
          tensorInnerPointwise (I := I) (M := M) g r s x
              (∑ i : Fin n, U i k • vfam i)
              (∑ j : Fin n, U j k • vfam j)
            = ∑ i : Fin n, ∑ j : Fin n,
              U i k * U j k *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (vfam i) (vfam j) := by
      intro k
      rw [hsum_left Finset.univ (fun i => U i k) vfam
        (∑ j : Fin n, U j k • vfam j)]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsum_right Finset.univ (U i k • vfam i) (fun j => U j k) vfam]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
      ring
    have hRHS :
        ∑ k : Fin n, μ k *
          tensorInnerPointwise (I := I) (M := M) g r s x
            (∑ i : Fin n, U i k • vfam i)
            (∑ j : Fin n, U j k • vfam j)
          = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              (μ k * (U i k * U j k)) *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (vfam i) (vfam j) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [hbilin k, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [hRHS]
    have hLHS :
        ∑ i : Fin n, ∑ j : Fin n,
          Ginv i j *
            tensorInnerPointwise (I := I) (M := M) g r s x (vfam i) (vfam j)
          = ∑ i : Fin n, ∑ j : Fin n,
              ∑ k : Fin n,
                (μ k * (U i k * U j k)) *
                  tensorInnerPointwise (I := I) (M := M) g r s x
                    (vfam i) (vfam j) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [hGinv_entry i j, Finset.sum_mul]
    rw [hLHS]
    have h_swap_inner :
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            (μ k * (U i k * U j k)) *
              tensorInnerPointwise (I := I) (M := M) g r s x
                (vfam i) (vfam j)
          = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
            (μ k * (U i k * U j k)) *
              tensorInnerPointwise (I := I) (M := M) g r s x
                (vfam i) (vfam j) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_comm]
    rw [h_swap_inner, Finset.sum_comm]
  rw [hrewrite]
  refine Finset.sum_nonneg ?_
  intro k _
  refine mul_nonneg (hμ_nonneg k) ?_
  exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x
    (∑ i : Fin n, U i k • vfam i)

/-! ## Global H^1 inner product on smooth Cc tensor sections

The H^1 inner product of two smooth compactly-supported `(r, s)`-tensor
sections is the sum of the `L^2` inner product `tensorL2Inner g r s` (already
in the codebase) and the integral of the pointwise gradient inner product
`tensorCovDerivPointwiseInner g r s` against the Riemannian volume measure. -/

/-- The global H^1 inner product of two smooth compactly-supported
`(r, s)`-tensor sections on a closed Riemannian manifold:

  `⟨S, T⟩_{H^1} := tensorL2Inner g r s S.toFun T.toFun
                 + ∫_M tensorCovDerivPointwiseInner g r s S T x dvol_g(x)`. -/
noncomputable def tensorH1Inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) : ℝ :=
  tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun +
    ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)

/-- Unfolding lemma for the global H^1 inner product. -/
lemma tensorH1Inner_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s S T =
      tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun +
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := rfl

/-! ## Vanishing of the directional covariant derivative off the section support

The directional covariant derivative `tensorCovDerivAt g r s S x v` vanishes whenever
`x ∉ tsupport S.toSection`. The key tool is the local-germ characterisation of the
covariant derivative: if `S.toSection` agrees with the zero section on a neighbourhood of
`x`, then `tensorRSCovariantDerivative ... x` agrees with the covariant derivative of the
zero section at `x`, which is `0` by `IsCovariantDerivativeOn.zero`. -/

/-- Auxiliary: if `S.toSection y = 0` for all `y` in a neighbourhood of `x`, then
the directional covariant derivative of `S` at `x` vanishes in every direction. -/
private lemma tensorCovDerivAt_eq_zero_of_eventuallyEq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M)
    (hx_nhds : ∀ᶠ y in 𝓝 x, S.toSection y = 0) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s S x v = 0 := by
  classical
  -- The covariant derivative of `S.toSection` at `x` equals the covariant derivative
  -- of the zero section at `x` by `congr_of_eventuallyEq`, then `0` by `zero`.
  set cov := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
  -- Smoothness of `S.toSection` at `x`.
  have hS_diff :=
    (S.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt (x := x)
  -- Smoothness of the zero section at `x`.
  have hzero_diff :
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (Bundle.zeroSection (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y)) x :=
    (Bundle.mdifferentiable_zeroSection
      (𝕜 := ℝ) (IB := I) (F := TensorRSModel r s ℝ E)
      (E := fun y : M => TensorRSSpace r s I y)).mdifferentiableAt
  -- Eventually-equal: `S.toSection y = 0` near `x`.
  have hev : ∀ᶠ y in 𝓝 x,
      (fun y : M => S.toSection y) y =
        ((0 : (y : M) → TensorRSSpace r s I y)) y := hx_nhds
  have hcongr := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (σ := fun y : M => S.toSection y)
    (σ' := (0 : (y : M) → TensorRSSpace r s I y))
    hS_diff hzero_diff (Filter.univ_mem) hev
  -- `cov(0) x = 0`.
  have hcov_zero := cov.isCovariantDerivativeOnUniv.zero
    (x := x) (hx := (by trivial : x ∈ (Set.univ : Set M)))
  -- Combine: cov(S.toSection) x = cov(0) x = 0.
  unfold tensorCovDerivAt
  change cov.toFun (fun y : M => S.toSection y) x v = (0 : E →L[ℝ] _) v
  rw [hcongr, hcov_zero]
  rfl

/-- If `x ∉ tsupport S.toFun`, then the directional covariant derivative of `S` at `x`
vanishes in every direction. -/
private lemma tensorCovDerivAt_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport S.toFun) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s S x v = 0 := by
  classical
  -- Outside `tsupport S.toFun`, the function `S.toFun` vanishes on an open
  -- neighbourhood of `x`. Since `S.toFun = toModel ∘ S.toSection` and `toModel` is
  -- injective, `S.toSection` vanishes on the same neighbourhood.
  have hopen : IsOpen (tsupport S.toFun)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hmem : x ∈ (tsupport S.toFun)ᶜ := hx
  have hnhd : (tsupport S.toFun)ᶜ ∈ 𝓝 x := hopen.mem_nhds hmem
  -- On this neighbourhood, `S.toFun y = 0`, hence `S.toSection y = 0`.
  have hev : ∀ᶠ y in 𝓝 x, S.toSection y = 0 := by
    filter_upwards [hnhd] with y hy
    -- `y ∉ tsupport S.toFun` ⇒ `y ∉ support S.toFun` ⇒ `S.toFun y = 0`.
    have hy_notsupp : y ∉ Function.support S.toFun := fun hyS => hy (subset_tsupport _ hyS)
    have hy_zero : S.toFun y = 0 := by
      simpa [Function.support, Function.mem_support] using hy_notsupp
    -- Translate `S.toFun y = 0` to `S.toSection y = 0` via `toModel` injectivity.
    have hto : TensorRSSpace.toModel (S.toSection y) = 0 := by
      have : S.toFun y = TensorRSSpace.toModel (S.toSection y) := rfl
      rw [this] at hy_zero
      exact hy_zero
    have htoModel_zero : TensorRSSpace.toModel
        (0 : TensorRSSpace r s I y) = 0 := TensorRSSpace.toModel_zero
    -- `toModel` injective: from `toModel (S.toSection y) = 0 = toModel 0`, conclude
    -- `S.toSection y = 0`.
    have hcomb : TensorRSSpace.toModel (S.toSection y) =
        TensorRSSpace.toModel (0 : TensorRSSpace r s I y) := by
      rw [hto, htoModel_zero]
    exact TensorRSSpace.toModel_injective
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := y) hcomb
  exact tensorCovDerivAt_eq_zero_of_eventuallyEq_zero
    (I := I) (M := M) g r s S x hev v

/-! ## Compact support of the pointwise gradient inner product -/

/-- The integrand vanishes at any point outside `tsupport S.toFun`. -/
private lemma tensorCovDerivPointwiseInner_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) {x : M} (hx : x ∉ tsupport S.toFun) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T x = 0 := by
  unfold tensorCovDerivPointwiseInner
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hSi : tensorCovDerivAt (I := I) (M := M) g r s S x
      ((chartModelBasis E) i) = 0 :=
    tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s S
      hx ((chartModelBasis E) i)
  rw [hSi, TensorRSSpace.toModel_zero, tensorInnerPointwise_zero_left]
  ring

/-- The integrand `tensorCovDerivPointwiseInner g r s S T` has compact support: it
vanishes outside `tsupport S.toFun`, which is compact in `M`. -/
theorem tensorCovDerivPointwiseInner_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    HasCompactSupport
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) := by
  -- We show `tsupport F ⊆ tsupport S.toFun`. Using `IsCompact.of_isClosed_subset`
  -- with `tsupport S.toFun` (compact, by `S.hasCompactSupport`) and `tsupport F`
  -- closed (always closed).
  refine IsCompact.of_isClosed_subset S.hasCompactSupport (isClosed_tsupport _) ?_
  -- `tsupport F = closure (support F)` and `tsupport S.toFun` is closed. So it
  -- suffices to show `support F ⊆ tsupport S.toFun`, then take closure.
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  -- `hx : F x ≠ 0`. Suppose `x ∉ tsupport S.toFun`. Then `F x = 0`, contradiction.
  by_contra hx_notsupp
  exact hx (tensorCovDerivPointwiseInner_eq_zero_off_tsupport
    (I := I) (M := M) g r s S T hx_notsupp)

/-! ## Coordinate-invariance of the trace expression

The integrand `tensorCovDerivPointwiseInner` is the metric-induced trace of the
bilinear form `(u, v) ↦ ⟨cov_S(b)(u), cov_T(b)(v)⟩_{g(b)}` on `TangentSpace I b`.
This trace is independent of the basis of `TangentSpace I b` used to compute it.
We prove this invariance for the canonical choice of `chartBasisVecFiber α i b`
versus `chartModelBasis E i`, with the corresponding Gram matrices.

The proof is a linear-algebra identity: if `T : E ≃L[ℝ] E` is the change-of-basis
isomorphism sending `chartModelBasis E i` to `chartBasisVecFiber α i b`
(i.e. `(triv α).symm b`), and `G'_{ij} := g(b)(e_i', e_j')`,
`G_{ij} := g(b)(e_i, e_j)` are the two Gram matrices, then
`G' = T^T G T` (with `T_{ki}` the `k`-th coefficient of `e_i'` in basis `e_·`),
and the trace formula
`∑_{ij} G'⁻¹_{ij} B(e_i', e_j') = ∑_{kl} G⁻¹_{kl} B(e_k, e_l)`
follows by algebraic manipulation. -/

/-- An abstract linear-algebra identity: for any change-of-basis matrix `T` and
any inner product matrix `G` with `G' := T^T G T` (the Gram matrix under the new
basis), the trace expression `∑_{ij} G⁻¹_{ij} ⟨L(e_i), L(e_j)⟩` is independent of
the basis, when `L` is linear and `⟨·,·⟩` is a bilinear form.

Formulated as: if `e_i' = ∑_k T_{ki} e_k`, then
`∑_{ij} G'⁻¹_{ij} B(e_i', e_j') = ∑_{ij} G⁻¹_{ij} B(e_i, e_j)`
where `B(u, v) := ⟨L(u), L(v)⟩` and `G'_{ij} := ⟨e_i', e_j'⟩` (Gram), provided
`G_{ij} := ⟨e_i, e_j⟩`. -/
private lemma trace_invariance_under_change_of_basis
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : IsUnit G)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    let G' := Tᵀ * G * T
    let B' := Tᵀ * B * T
    ∑ i : Fin n, ∑ j : Fin n, G'⁻¹ i j * B' i j =
      ∑ i : Fin n, ∑ j : Fin n, G⁻¹ i j * B i j := by
  classical
  -- The sum `∑_{ij} M_{ij} N_{ij}` is the trace of `M Nᵀ` (Frobenius inner product).
  -- Equivalently, `Matrix.trace (M * Nᵀ)`. We prove that `Matrix.trace (G'⁻¹ * B'ᵀ) =
  -- Matrix.trace (G⁻¹ * Bᵀ)` using the cyclic property of trace and the explicit
  -- formulas `G' = Tᵀ G T`, `B' = Tᵀ B T`.
  simp only
  -- Step 1: rewrite the double sum as a trace.
  have hsum_eq : ∀ M N : Matrix (Fin n) (Fin n) ℝ,
      ∑ i : Fin n, ∑ j : Fin n, M i j * N i j = Matrix.trace (M * Nᵀ) := by
    intro M N
    rw [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [Matrix.transpose_apply]
  rw [hsum_eq, hsum_eq]
  -- Step 2: simplify `G'⁻¹ = T⁻¹ G⁻¹ T⁻ᵀ` (after standard algebra).
  set G' : Matrix (Fin n) (Fin n) ℝ := Tᵀ * G * T with hG'_def
  have hG'_inv : G'⁻¹ = T⁻¹ * G⁻¹ * (Tᵀ)⁻¹ := by
    rw [hG'_def]
    have hT_unit : IsUnit T := hT
    have hTT_unit : IsUnit Tᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det] at hT ⊢
      simpa [Matrix.det_transpose] using hT
    have hG_unit : IsUnit G := hG
    -- (Tᵀ * G * T)⁻¹ = T⁻¹ * G⁻¹ * (Tᵀ)⁻¹.
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, mul_assoc]
  rw [hG'_inv]
  -- Step 3: also rewrite B' = Tᵀ * B * T, so (B')ᵀ = Tᵀ * Bᵀ * T.
  set B' : Matrix (Fin n) (Fin n) ℝ := Tᵀ * B * T with hB'_def
  have hB'_trans : B'ᵀ = Tᵀ * Bᵀ * T := by
    rw [hB'_def, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      mul_assoc]
  rw [hB'_trans]
  -- Goal: trace (T⁻¹ * G⁻¹ * (Tᵀ)⁻¹ * (Tᵀ * Bᵀ * T)) = trace (G⁻¹ * Bᵀ).
  -- Reassociate to combine `(Tᵀ)⁻¹ * Tᵀ = 1`.
  have hTT_unit : IsUnit Tᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det] at hT ⊢
    simpa [Matrix.det_transpose] using hT
  have hT_inv_T : (Tᵀ)⁻¹ * Tᵀ = 1 := Matrix.nonsing_inv_mul _
    (by simpa [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose] using hT)
  have hT_T_inv : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _
    (by simpa [Matrix.isUnit_iff_isUnit_det] using hT)
  -- Reassociate: T⁻¹ * G⁻¹ * (Tᵀ)⁻¹ * (Tᵀ * Bᵀ * T) = T⁻¹ * G⁻¹ * ((Tᵀ)⁻¹ * Tᵀ) * Bᵀ * T.
  -- We use only matrix monoid associativity.
  have hcyc :
      T⁻¹ * G⁻¹ * (Tᵀ)⁻¹ * (Tᵀ * Bᵀ * T) =
        T⁻¹ * G⁻¹ * ((Tᵀ)⁻¹ * Tᵀ) * Bᵀ * T := by
    -- Both sides equal `((T⁻¹ * G⁻¹) * (Tᵀ)⁻¹) * (Tᵀ * Bᵀ * T)` =
    -- `(T⁻¹ * G⁻¹) * ((Tᵀ)⁻¹ * (Tᵀ * Bᵀ * T))` =
    -- `(T⁻¹ * G⁻¹) * (((Tᵀ)⁻¹ * Tᵀ) * (Bᵀ * T))`, etc.
    -- Use `mul_assoc` repeatedly.
    -- `mul_assoc` applied at various positions handles this.
    repeat rw [mul_assoc]
  rw [hcyc, hT_inv_T, mul_one]
  -- Goal: trace (T⁻¹ * G⁻¹ * Bᵀ * T) = trace (G⁻¹ * Bᵀ).
  -- Use cyclic property: trace(A * B) = trace(B * A) with A = T⁻¹, B = (G⁻¹ * Bᵀ * T).
  -- Then trace(T⁻¹ * (G⁻¹ * Bᵀ * T)) = trace((G⁻¹ * Bᵀ * T) * T⁻¹) = trace(G⁻¹ * Bᵀ * (T * T⁻¹)) =
  -- trace(G⁻¹ * Bᵀ * 1) = trace(G⁻¹ * Bᵀ).
  have hreassoc : T⁻¹ * G⁻¹ * Bᵀ * T = T⁻¹ * (G⁻¹ * Bᵀ * T) := by
    rw [mul_assoc T⁻¹ G⁻¹ Bᵀ, mul_assoc T⁻¹ (G⁻¹ * Bᵀ) T]
  rw [hreassoc, Matrix.trace_mul_comm T⁻¹ (G⁻¹ * Bᵀ * T)]
  -- Goal: trace (G⁻¹ * Bᵀ * T * T⁻¹) = trace (G⁻¹ * Bᵀ).
  rw [mul_assoc (G⁻¹ * Bᵀ) T T⁻¹, hT_T_inv, mul_one]

/-- The integrand `tensorCovDerivPointwiseInner g r s S T b` rewritten using the
chart-α basis `chartBasisVecFiber α i b` instead of `chartModelBasis E i`. The
expression involves the chart-α Gram matrix `chartGramMatrix g α b`. -/
private noncomputable def chartTensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (chartGramMatrix (I := I) g α b)⁻¹ i j *
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (chartBasisVecFiber (I := I) α j b)))

/-- The change-of-basis matrix from `chartModelBasis E` to `chartBasisFamily α b`
(at base-set points `b`). The `(k, i)` entry is the `e_k`-coefficient of
`chartBasisVecFiber α i b` in the basis `chartModelBasis E`. -/
private noncomputable def chartBasisTransitionMatrix (α : M) (b : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun k i =>
    ((chartModelBasis E).repr (chartBasisVecFiber (I := I) α i b)) k

/-- Recovery formula: `chartBasisVecFiber α i b = ∑_k T_{ki} (chartModelBasis E k)`,
where `T = chartBasisTransitionMatrix α b`. This is `Module.Basis.sum_repr` for the
basis `chartModelBasis E` applied to the vector `chartBasisVecFiber α i b`. -/
private lemma chartBasisVecFiber_eq_sum_chartModelBasis
    (α : M) (b : M) (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) α i b =
      ∑ k : Fin (Module.finrank ℝ E),
        chartBasisTransitionMatrix (I := I) α b k i • (chartModelBasis E) k := by
  classical
  unfold chartBasisTransitionMatrix
  simp only [Matrix.of_apply]
  -- `Module.Basis.sum_repr`: any vector `v : E` is `∑_k ((basis.repr v) k) • basis k`.
  exact (((chartModelBasis E).sum_repr
    (chartBasisVecFiber (I := I) α i b))).symm

/-- Identification: `chartBasisTransitionMatrix α b = (chartModelBasis E).toMatrix
(fun i => chartBasisVecFiber α i b)`. -/
private lemma chartBasisTransitionMatrix_eq_toMatrix
    (α : M) (b : M) :
    chartBasisTransitionMatrix (I := I) α b =
      (chartModelBasis E).toMatrix
        (fun i : Fin (Module.finrank ℝ E) =>
          chartBasisVecFiber (I := I) α i b) := by
  classical
  unfold chartBasisTransitionMatrix
  ext k i
  rw [Module.Basis.toMatrix_apply, Matrix.of_apply]

/-- The change-of-basis matrix is invertible at base-set points. -/
private lemma chartBasisTransitionMatrix_isUnit
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (chartBasisTransitionMatrix (I := I) α b) := by
  classical
  -- At base-set points, `chartBasisFamily α b` is a basis (since it's LI and
  -- has `Module.finrank ℝ E` elements in a `Module.finrank ℝ E`-dimensional space).
  -- So `chartBasisTransitionMatrix = (chartModelBasis E).toMatrix (chartBasisFamily)`
  -- is the transition matrix between two bases, hence invertible.
  rw [chartBasisTransitionMatrix_eq_toMatrix]
  -- Build the basis from the family
  set chartBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    chartBasisFamily (I := I) α hb with hCB_def
  -- The toMatrix of `chartBasisFamily` interpreted as a family is the same
  -- as toMatrix of `chartBasis` (the basis).
  have hfam_eq : (fun i : Fin (Module.finrank ℝ E) =>
      chartBasisVecFiber (I := I) α i b)
      = (chartBasis : Fin (Module.finrank ℝ E) → E) := by
    funext i
    rw [hCB_def]
    exact (chartBasisFamily_apply (I := I) α hb i).symm
  rw [hfam_eq]
  -- Now `(chartModelBasis E).toMatrix chartBasis` is invertible.
  refine ⟨⟨_, chartBasis.toMatrix (chartModelBasis E), ?_, ?_⟩, rfl⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
  · exact Module.Basis.toMatrix_mul_toMatrix_flip _ _


/-- A helper: a continuous bilinear form on `E` evaluated on linear combinations of
basis vectors. -/
private lemma g_inner_bilinear_expand
    (g : SmoothRiemannianMetric I M) (b : M) {n : ℕ}
    (a c : Fin n → ℝ) (u : Fin n → E) :
    g.inner b (∑ k : Fin n, a k • u k) (∑ l : Fin n, c l • u l) =
      ∑ k : Fin n, ∑ l : Fin n,
        a k * c l * g.inner b (u k) (u l) := by
  classical
  -- Apply `g.inner b` outer-linearly: `g.inner b (∑ k a_k • u_k) = ∑ k a_k • (g.inner b (u_k))`.
  have houter : g.inner b (∑ k : Fin n, a k • u k) =
      ∑ k : Fin n, a k • (g.inner b (u k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [houter, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [map_smul, smul_eq_mul]
  ring

/-- Gram-matrix transformation: `chartGramMatrix g α b = T^T * gramMatrixAt g b * T`
where `T = chartBasisTransitionMatrix α b`. This holds for all `b`. -/
private lemma chartGramMatrix_eq_transition
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    chartGramMatrix (I := I) g α b =
      (chartBasisTransitionMatrix (I := I) α b)ᵀ *
        gramMatrixAt (I := I) (M := M) g b *
        chartBasisTransitionMatrix (I := I) α b := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set T : Matrix (Fin n) (Fin n) ℝ :=
    chartBasisTransitionMatrix (I := I) α b with hT_def
  ext i j
  rw [chartGramMatrix_apply]
  rw [chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b i,
      chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b j]
  rw [g_inner_bilinear_expand g b
        (fun k => T k i) (fun l => T l j) (chartModelBasis E)]
  -- LHS: ∑_{kl} T_{ki} * T_{lj} * g(e_k, e_l)
  -- RHS: ((Tᵀ * G * T) i j) = ∑_a (Tᵀ * G)_{ia} * T_{aj} = ∑_a (∑_b T^T_{ib} * G_{ba}) * T_{aj}
  --     = ∑_a (∑_b T_{bi} * G_{ba}) * T_{aj} = ∑_{ab} T_{bi} * G_{ba} * T_{aj}.
  -- We want LHS = RHS. The mapping (k, l) → (b, a) is k=b, l=a, so:
  -- LHS = ∑_{kl} T_{ki} * T_{lj} * g(e_k, e_l)
  -- RHS = ∑_{ab} T_{bi} * G_{ba} * T_{aj} = ∑_{kl} (k=b, l=a) T_{ki} * G_{kl} * T_{lj}.
  -- Both should match if G_{kl} = g(e_k, e_l), which is gramMatrixAt_apply.
  -- The issue: ∑ swap needed.
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Matrix.transpose_apply, gramMatrixAt_apply]
  ring

/-- Bilinearity of `tensorInnerPointwise` in the left argument over a finite sum. -/
private lemma tensorInnerPointwise_sum_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    {ι : Type*} (s' : Finset ι) (A : ι → TensorRSModel r s ℝ E)
    (c : ι → ℝ) (B : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s b (∑ k ∈ s', c k • A k) B =
      ∑ k ∈ s', c k *
        tensorInnerPointwise (I := I) (M := M) g r s b (A k) B := by
  classical
  induction s' using Finset.induction with
  | empty =>
      simp [tensorInnerPointwise_zero_left]
  | insert i₀ s'' hi₀ ih =>
      rw [Finset.sum_insert hi₀, tensorInnerPointwise_add_left,
          tensorInnerPointwise_smul_left, ih, Finset.sum_insert hi₀]

/-- Bilinearity of `tensorInnerPointwise` in the right argument over a finite sum. -/
private lemma tensorInnerPointwise_sum_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    {ι : Type*} (s' : Finset ι) (A : TensorRSModel r s ℝ E)
    (B : ι → TensorRSModel r s ℝ E) (c : ι → ℝ) :
    tensorInnerPointwise (I := I) (M := M) g r s b A (∑ l ∈ s', c l • B l) =
      ∑ l ∈ s', c l *
        tensorInnerPointwise (I := I) (M := M) g r s b A (B l) := by
  classical
  induction s' using Finset.induction with
  | empty =>
      simp [tensorInnerPointwise_zero_right]
  | insert j₀ s'' hj₀ ih =>
      rw [Finset.sum_insert hj₀, tensorInnerPointwise_add_right,
          tensorInnerPointwise_smul_right, ih, Finset.sum_insert hj₀]

/-- The B-matrix transformation: `B'_{ij} = (T^T B T)_{ij}` where
`B'_{ij} = tensorInnerPointwise (toModel(cov_S e'_i)) (toModel(cov_T e'_j))`,
`B_{ij}` is the same with `e_i`, and `T = chartBasisTransitionMatrix α b`. -/
private lemma chartTensorCovDeriv_innerMatrix_eq_transition
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (b : M)
    (i j : Fin (Module.finrank ℝ E)) :
    tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (chartBasisVecFiber (I := I) α j b))) =
      ((chartBasisTransitionMatrix (I := I) α b)ᵀ *
          (Matrix.of fun k l : Fin (Module.finrank ℝ E) =>
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  ((chartModelBasis E) k)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T b
                  ((chartModelBasis E) l)))) *
          chartBasisTransitionMatrix (I := I) α b) i j := by
  classical
  -- Notation: T = the change-of-basis matrix.
  set Tmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartBasisTransitionMatrix (I := I) α b with hTmat_def
  -- Expand `chartBasisVecFiber α i b` as a sum.
  have hexp_i := chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b i
  have hexp_j := chartBasisVecFiber_eq_sum_chartModelBasis (I := I) α b j
  -- Apply CLM linearity of `cov_S b`, `cov_T b` (these are CLMs `E →L[ℝ] TensorRSSpace`).
  have hSi : tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b) =
      ∑ k : Fin (Module.finrank ℝ E), Tmat k i •
        tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k) := by
    rw [hexp_i]
    unfold tensorCovDerivAt
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  have hTj : tensorCovDerivAt (I := I) (M := M) g r s T b
        (chartBasisVecFiber (I := I) α j b) =
      ∑ l : Fin (Module.finrank ℝ E), Tmat l j •
        tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l) := by
    rw [hexp_j]
    unfold tensorCovDerivAt
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]
  rw [hSi, hTj]
  -- Linearity of `toModel` on finite sums.
  have htoM_sum : ∀ (s' : Finset (Fin (Module.finrank ℝ E)))
      (f : Fin (Module.finrank ℝ E) → TensorRSSpace r s I b)
      (c : Fin (Module.finrank ℝ E) → ℝ),
      TensorRSSpace.toModel (∑ k ∈ s', c k • f k) =
        ∑ k ∈ s', c k • TensorRSSpace.toModel (f k) := by
    intro s' f c
    classical
    induction s' using Finset.induction with
    | empty => simp [TensorRSSpace.toModel_zero]
    | insert i₀ s'' hi₀ ih =>
        rw [Finset.sum_insert hi₀, TensorRSSpace.toModel_add,
            TensorRSSpace.toModel_smul, ih, Finset.sum_insert hi₀]
  have htoM_left := htoM_sum Finset.univ
    (fun k => tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k))
    (fun k => Tmat k i)
  have htoM_right := htoM_sum Finset.univ
    (fun l => tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l))
    (fun l => Tmat l j)
  rw [htoM_left, htoM_right]
  -- Bilinearity of `tensorInnerPointwise`:
  rw [tensorInnerPointwise_sum_left (I := I) (M := M) g r s b Finset.univ]
  -- Expand each inner sum.
  conv_lhs =>
    rhs
    ext k
    rw [tensorInnerPointwise_sum_right (I := I) (M := M) g r s b Finset.univ]
    rw [Finset.mul_sum]
  -- Now LHS is `∑ k, ∑ l, T_{ki} * (T_{lj} * tensorInnerPointwise g ((cov_S e_k).toModel) ((cov_T e_l).toModel))`.
  -- RHS = `(Tᵀ * B * T) i j = ∑_a (Tᵀ * B)_{ia} * T_{aj} = ∑_a (∑_b Tᵀ_{ib} * B_{ba}) * T_{aj} =
  --       ∑_a (∑_b T_{bi} * B_{ba}) * T_{aj}`.
  -- We need: LHS = RHS via index renaming k = b, l = a.
  rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k _
  -- Goal-ish: ∑ l, T_{ki} * (T_{lj} * B_{kl}) = (Tᵀ * B) i k * T k j
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro l _
  -- Goal: T_{ki} * (T_{lj} * B_{kl}) = (Tᵀ_{ik?} ...) ... — index check needed.
  rw [Matrix.transpose_apply, Matrix.of_apply]
  ring

/-- **The coordinate-invariance identity**: on the chart base set,
the chart-α-frame integrand equals the model-basis integrand. -/
private lemma chartTensorCovDerivPointwiseInner_eq_tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartTensorCovDerivPointwiseInner (I := I) (M := M) g α r s S T b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b := by
  classical
  set n := Module.finrank ℝ E
  set Tmat : Matrix (Fin n) (Fin n) ℝ :=
    chartBasisTransitionMatrix (I := I) α b with hTmat_def
  set Gmat : Matrix (Fin n) (Fin n) ℝ :=
    gramMatrixAt (I := I) (M := M) g b with hGmat_def
  set Bmat : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun k l : Fin n =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b ((chartModelBasis E) k)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b ((chartModelBasis E) l)))
    with hBmat_def
  -- The chart-frame integrand is ∑_{ij} (Tmatᵀ * Gmat * Tmat)⁻¹_{ij} * (Tmatᵀ * Bmat * Tmat)_{ij}.
  -- By the abstract trace lemma, this equals ∑_{kl} Gmat⁻¹_{kl} * Bmat_{kl}.
  -- And the latter is the model-basis integrand.
  unfold chartTensorCovDerivPointwiseInner
  unfold tensorCovDerivPointwiseInner
  -- Rewrite both sides using the matrix structure.
  -- LHS = ∑_{ij} (chartGramMatrix g α b)⁻¹ i j * (Bmat-prime)_{ij}
  --     where Bmat-prime = Tmatᵀ * Bmat * Tmat.
  have hG_eq : chartGramMatrix (I := I) g α b = Tmatᵀ * Gmat * Tmat :=
    chartGramMatrix_eq_transition (I := I) g α b
  -- Apply abstract trace lemma:
  have hLHS_term_eq : ∀ i j : Fin n,
      tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b
              (chartBasisVecFiber (I := I) α j b))) =
        (Tmatᵀ * Bmat * Tmat) i j := by
    intro i j
    exact chartTensorCovDeriv_innerMatrix_eq_transition (I := I) (M := M) g α r s S T b i j
  -- Goal: ∑_{ij} G_chart⁻¹_{ij} * (...) = ∑_{kl} G⁻¹_{kl} * tensorInnerPointwise(...)
  -- Rewrite both sides to expose matrix structure.
  have hLHS_rewrite :
      ∑ i : Fin n, ∑ j : Fin n,
          (chartGramMatrix (I := I) g α b)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T b
                  (chartBasisVecFiber (I := I) α j b))) =
        ∑ i : Fin n, ∑ j : Fin n,
          (Tmatᵀ * Gmat * Tmat)⁻¹ i j * (Tmatᵀ * Bmat * Tmat) i j := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hLHS_term_eq i j, hG_eq]
  rw [hLHS_rewrite]
  -- Now apply abstract trace lemma.
  have hT_unit : IsUnit Tmat := chartBasisTransitionMatrix_isUnit (I := I) α hb
  have hG_unit : IsUnit Gmat := by
    rw [hGmat_def]
    -- `gramMatrixAt_isUnit` is private in the source file but we can derive
    -- invertibility from `gramMatrixAt_posSemidef` and the fact that
    -- `gramMatrixAt_inv_isHermitian` exists (the inverse is well-defined).
    -- Alternative: use that the matrix is positive definite (g is Riemannian).
    -- We use the fact that the inverse exists as a Hermitian matrix, which
    -- gives `IsUnit`.
    have hinv_herm := gramMatrixAt_inv_isHermitian (I := I) (M := M) g b
    -- For a square matrix M over a field, M is a unit iff its inverse is well-defined
    -- (via `Matrix.nonsing_inv`).
    -- `gramMatrixAt_inv_posSemidef.isHermitian` gives us that the inverse is hermitian,
    -- meaning the inverse exists (otherwise it'd be junk = 0 which is hermitian, but
    -- we have it positive semidefinite which rules out 0).
    -- Direct: use gramMatrixAt_posDef.isUnit if accessible.
    have hpos := gramMatrixAt_inv_posSemidef (I := I) (M := M) g b
    -- The Gram matrix at b is the inverse of `gramMatrixAt_inv`, which is positive semidefinite.
    -- We argue via `Matrix.PosDef.isUnit` (the original matrix is PD).
    -- Simpler: use that `gramMatrixAt` is the matrix of a positive-definite quadratic
    -- form, hence invertible. This is essentially what `gramMatrixAt_isUnit` proves
    -- (privately). We restate the argument.
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    -- Use that PosDef ⇒ det ≠ 0.
    have hposdef : (gramMatrixAt (I := I) (M := M) g b).PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos
        (gramMatrixAt_isHermitian (I := I) (M := M) g b) ?_
      intro v hv
      -- Same proof as `gramMatrixAt_posDef` (private). Reproduce.
      let w : E := ∑ i : Fin (Module.finrank ℝ E),
        v i • (chartModelBasis E) i
      have hw_ne : w ≠ 0 := by
        intro h
        have hlin : LinearIndependent ℝ ((chartModelBasis E) : Fin _ → E) :=
          (chartModelBasis E).linearIndependent
        rw [Fintype.linearIndependent_iff] at hlin
        exact hv (funext (hlin v h))
      have hquad : star v ⬝ᵥ (gramMatrixAt (I := I) (M := M) g b) *ᵥ v =
          g.inner b w w := by
        -- Same expansion as in `gramMatrixAt_posDef`.
        have hexp : g.inner b w w =
            ∑ j : Fin (Module.finrank ℝ E),
              v j * ∑ i : Fin (Module.finrank ℝ E),
                v i * gramMatrixAt (I := I) (M := M) g b i j := by
          change g.inner b (∑ i, v i • (chartModelBasis E) i)
              (∑ j, v j • (chartModelBasis E) j) = _
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          have hsm1 : (g.inner b (∑ i, v i • (chartModelBasis E) i))
                (v j • (chartModelBasis E) j) =
              v j * (g.inner b (∑ i, v i • (chartModelBasis E) i))
                ((chartModelBasis E) j) := by
            rw [map_smul, smul_eq_mul]
          rw [hsm1]
          congr 1
          rw [map_sum, ContinuousLinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          have hsm2 : (g.inner b (v i • (chartModelBasis E) i))
                ((chartModelBasis E) j) =
              v i * (g.inner b ((chartModelBasis E) i)) ((chartModelBasis E) j) := by
            rw [show (g.inner b) (v i • (chartModelBasis E) i) =
                v i • (g.inner b) ((chartModelBasis E) i) from by rw [map_smul]]
            rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
          rw [hsm2, gramMatrixAt_apply]
        rw [hexp]
        -- Unfold star v ⬝ᵥ M *ᵥ v as a sum.
        change ∑ j : Fin (Module.finrank ℝ E),
            star (v j) * (gramMatrixAt (I := I) (M := M) g b *ᵥ v) j =
          ∑ j : Fin (Module.finrank ℝ E),
            v j * ∑ i : Fin (Module.finrank ℝ E),
              v i * gramMatrixAt (I := I) (M := M) g b i j
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [star_trivial]
        rw [show (gramMatrixAt (I := I) (M := M) g b *ᵥ v) j =
              ∑ i : Fin (Module.finrank ℝ E),
                gramMatrixAt (I := I) (M := M) g b j i * v i from rfl]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => ?_)
        rw [gramMatrixAt_apply, gramMatrixAt_apply, g.symm]
        ring
      rw [hquad]
      exact g.pos b w hw_ne
    -- Now apply: PosDef ⇒ det > 0 ⇒ det ≠ 0.
    have hdet_pos := hposdef.det_pos
    exact ne_of_gt hdet_pos
  exact trace_invariance_under_change_of_basis Tmat hT_unit Gmat hG_unit Bmat

/-! ## Chart-local smoothness of the covariant derivative applied to chart basis -/

/-- The covariant derivative of a smooth compactly-supported tensor section
applied to a chart-basis tangent vector field is smooth as a tensor section
on the chart base set. -/
private lemma tensorCovDeriv_chartBasis_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun y : M => TensorRSSpace r s I y) b
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  -- The covariant derivative `cov σ` is smooth as a Hom(TM, V) bundle section globally.
  -- Restricted to chart α base set, it's smooth on that set.
  set covLC := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
  haveI hcovLC_inst : CovariantDerivative.ContMDiffCovariantDerivative covLC ∞ :=
    inferInstance
  -- Smoothness of `cov S` as a Hom-bundle section, globally (i.e., on `Set.univ`).
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun b : M => (⟨b, covLC.toFun (fun y : M => S.toSection y) b⟩ :
        TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun b : M => TangentSpace I b →L[ℝ] TensorRSSpace r s I b)) Set.univ :=
    hcovLC_inst.contMDiff.contMDiff (σ := fun y : M => S.toSection y)
      (S.toSection.contMDiff.contMDiffOn)
  -- Smoothness of `chartBasisVec α i` on chart α base set.
  have hX_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (chartBasisVecFiber (I := I) α i b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    have := chartBasisVec_contMDiffOn (I := I) α i
    -- `chartBasisVec α i b = TotalSpace.mk' E b (chartBasisVecFiber α i b)` by def.
    exact this
  -- Apply `ContMDiffOn.clm_bundle_apply`.
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  have hcov_at : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun b : M => (⟨b, covLC.toFun (fun y : M => S.toSection y) b⟩ :
        TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun b : M => TangentSpace I b →L[ℝ] TensorRSSpace r s I b)) x₀ :=
    hop.contMDiffAt (Filter.univ_mem)
  have hX_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
        (chartBasisVecFiber (I := I) α i b)) x₀ :=
    (hX_on x₀ hx₀).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  -- `tensorCovDerivAt g r s S b v = covLC.toFun (fun y => S.toSection y) b v` by def.
  exact hcov_at.clm_bundle_apply hX_at

/-- The trivialization-α-image of `cov_S b · chartBasisVecFiber α i b` is smooth on
chart α base set. By bundle smoothness of the section, the chart-α trivialization
image is smooth in `b`. -/
private lemma tensorCovDeriv_chartBasis_trivImage_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E) ∞
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
          ⟨b, tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)⟩).2)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  -- Use `contMDiffOn_section_baseSet_iff` for the tensorRS bundle.
  have hsection := tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g r s S α i
  -- The relevant trivialization has baseSet equal to chart α source = trivializationAt E TangentSpace α baseSet.
  have hbase_eq : (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet =
        (trivializationAt E (TangentSpace I) α).baseSet := by
    -- Both equal `(chartAt H α).source`.
    change ((trivializationAt (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
        ((trivializationAt (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x) α).baseSet) =
          (trivializationAt E (TangentSpace I) α).baseSet
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet =
            (trivializationAt E (TangentSpace I) α).baseSet
    exact Set.inter_self _
  rw [← hbase_eq]
  rw [← Bundle.Trivialization.contMDiffOn_section_baseSet_iff
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α)]
  rw [hbase_eq]
  exact hsection

/-! ## Local replays of private helpers from `Tensor.Multilinear.MetricLowering`

The two helpers below mirror private lemmas inside
`TensorMetricLowering`: `loweredCompose_at_basis_tuple` (an unfolding lemma)
and `contMDiffOn_into_tensor0SModel_of_eval_basis` (a basis-tuple smoothness
bridge into `Tensor0SModel`). We replay them here as `private` so they can be
called from this file. -/

/-- Linear "evaluation at all basis tuples" map on `Tensor0SModel n ℝ E`. -/
private noncomputable def evalAtBasisLinearLocal (n : ℕ) :
    Tensor0SModel n ℝ E →ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun Φ φ => Φ (fun k : Fin n => (chartModelBasis E) (φ k))
  map_add' Φ₁ Φ₂ := by
    funext φ
    simp [ContinuousMultilinearMap.add_apply]
  map_smul' c Φ := by
    funext φ
    simp [ContinuousMultilinearMap.smul_apply]

@[simp] private lemma evalAtBasisLinearLocal_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisLinearLocal (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

/-- `evalAtBasisLinearLocal` is injective: two multilinear forms agreeing on
all model-basis tuples are equal. -/
private lemma evalAtBasisLinearLocal_injective (n : ℕ) :
    Function.Injective (evalAtBasisLinearLocal (E := E) n) := by
  intro Φ₁ Φ₂ h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (e := fun _ : Fin n => chartModelBasis E) ?_
  intro v
  exact congr_fun h v

/-- Dimension of the model fibre `Tensor0SModel n ℝ E`. -/
private lemma finrank_tensor0SModel_local (n : ℕ) :
    Module.finrank ℝ (Tensor0SModel n ℝ E) =
      (Module.finrank ℝ E) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      rw [(continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.finrank_eq]
      exact Module.finrank_self ℝ
  | succ n ih =>
      rw [(continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) ℝ).toLinearEquiv.finrank_eq]
      let φ : (E →L[ℝ] Tensor0SModel n ℝ E) ≃ₗ[ℝ]
          (E →ₗ[ℝ] Tensor0SModel n ℝ E) :=
        { toFun := fun f => f.toLinearMap
          invFun := fun f => LinearMap.toContinuousLinearMap f
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      rw [φ.finrank_eq, Module.finrank_linearMap, ih]
      ring

private lemma finrank_basis_pi_local (n : ℕ) :
    Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) =
      (Module.finrank ℝ E) ^ n := by
  rw [Module.finrank_pi, Fintype.card_pi]
  simp [Fintype.card_fin]

private lemma evalAtBasisLinearLocal_bijective (n : ℕ) :
    Function.Bijective (evalAtBasisLinearLocal (E := E) n) := by
  have h_inj := evalAtBasisLinearLocal_injective (E := E) n
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (Tensor0SModel n ℝ E) =
      Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
    rw [finrank_tensor0SModel_local, finrank_basis_pi_local]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

private noncomputable def evalAtBasisCLELocal (n : ℕ) :
    Tensor0SModel n ℝ E ≃L[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  (LinearEquiv.ofBijective (evalAtBasisLinearLocal (E := E) n)
    (evalAtBasisLinearLocal_bijective (E := E) n)).toContinuousLinearEquiv

@[simp] private lemma evalAtBasisCLELocal_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    evalAtBasisCLELocal (E := E) n Φ φ =
      Φ (fun k : Fin n => (chartModelBasis E) (φ k)) := rfl

/-- Smoothness into `Tensor0SModel n ℝ E` from smoothness of basis-tuple
evaluations. Sister of the private
`TensorMetricLowering.contMDiffOn_into_tensor0SModel_of_eval_basis`. -/
private lemma contMDiffOn_into_tensor0SModel_of_eval_basis_local
    {n : ℕ} {U : Set M} (Φ : M → Tensor0SModel n ℝ E)
    (h : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
        Φ b (fun k : Fin n => (chartModelBasis E) (φ k))) U) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U := by
  have hpi : ContMDiffOn I 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun b : M => evalAtBasisCLELocal (E := E) n (Φ b)) U := by
    rw [contMDiffOn_pi_space]
    intro φ
    exact h φ
  have hsymm_smooth :
      ContMDiff 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ)
        𝓘(ℝ, Tensor0SModel n ℝ E) ∞
        (evalAtBasisCLELocal (E := E) n).symm :=
    (evalAtBasisCLELocal (E := E) n).symm.toContinuousLinearMap.contMDiff
  have hcomp := hsymm_smooth.comp_contMDiffOn hpi
  refine hcomp.congr ?_
  intro b _
  exact ((evalAtBasisCLELocal (E := E) n).symm_apply_apply (Φ b)).symm

/-- Local unfolding of `loweredCompose` at a model-basis tuple. -/
private lemma loweredCompose_at_basis_tuple_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E)
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    loweredCompose (I := I) (M := M) g r s α b T
        (fun i : Fin (r + s) => (chartModelBasis E) (φ i)) =
      lowerAllUpperIndices (I := I) (M := M) g r s b T
        (fun i : Fin (r + s) =>
          chartBasisVecFiber (I := I) α (φ i) b) := by
  rw [loweredCompose_apply]
  rfl

/-! ## Smoothness of inverse-Gram-matrix entries on the chart base set

The inverse of `chartGramMatrix g α b`, entrywise, is smooth on the chart base
set at `α`. Proof: `A⁻¹ = (det A)⁻¹ • adjugate A`, so each entry is the product
of `(det)⁻¹` (smooth from `chartGramMatrix_det_contMDiffOn` and strict positivity
of the determinant) and the adjugate entry (smooth from
`chartGramMatrix_adjugate_entry_contMDiffOn`). -/

/-- Smoothness of `(chartGramMatrix g α ·)⁻¹ i j` on the chart-α base set. -/
private lemma chartGramMatrixInv_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (chartGramMatrix (I := I) g α b)⁻¹ i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun b : M => (chartGramMatrix (I := I) g α b)⁻¹ i j)
        = (fun b : M => (chartGramMatrix (I := I) g α b).det⁻¹ *
              (chartGramMatrix (I := I) g α b).adjugate i j) := by
    funext b
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]
  intro b hb
  have hdet := chartGramMatrix_det_contMDiffOn (I := I) g α b hb
  have hadj := chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j b hb
  have hpos : 0 < (chartGramMatrix (I := I) g α b).det :=
    chartGramMatrix_det_pos (I := I) g α hb
  have hpos_ne : (chartGramMatrix (I := I) g α b).det ≠ 0 := ne_of_gt hpos
  exact (ContMDiffWithinAt.inv₀ hdet hpos_ne).mul hadj

/-! ## Chart-local smoothness of the `loweredCompose`-image of the chart-α
covariant-derivative-evaluation

This block parallels `TensorMetricLowering.contMDiffOn_loweredCompose` and its
auxiliary `contMDiffOn_lower_at_chartBasis_aux`, but takes a chart-locally
smooth bundle section as input instead of a globally smooth one. Specifically,
we prove smoothness on the chart-α base set of

  `b ↦ loweredCompose g r s α b (TensorRSSpace.toModel
                                  (cov_S(b) · chartBasisVecFiber α i b))`.

The proof structure mirrors the existing one: combine the smooth
`(0, r)`-separable-form bundle section with the chart-locally-smooth
`(r, s)`-section (which here is `cov_S · chartBasisVec α i`, smooth via
`tensorCovDeriv_chartBasis_contMDiffOn`) via `clm_bundle_apply`, then apply
the pointwise multilinear-bundle-evaluation lemma. -/

/-- The `(0, r)` separable-form bundle section, attached to a chart-α base
point, evaluated at the chart-α basis indexed by `φ_first`. The trivialisation
fibre at `α` evaluates, on a model-basis tuple `e_ψ`, to a product of
chart-Gram-matrix entries. -/
private noncomputable def separableFormBundleSectionLocal
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    M → TotalSpace (Tensor0SModel r ℝ E) (fun y : M => Tensor0SSpace r I y) :=
  fun b => TotalSpace.mk' (Tensor0SModel r ℝ E)
    (E := fun y : M => Tensor0SSpace r I y) b
    (Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)))

/-- The trivialisation fibre at `α` of the `(0, r)` separable-form bundle
section, evaluated on a model-basis tuple `e_ψ`, equals a product of
chart-Gram-matrix entries. -/
private theorem trivializationAt_separableFormBundleSectionLocal_eval_basis
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) {b : M}
    (_hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (ψ : Fin r → Fin (Module.finrank ℝ E)) :
    (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α
        (separableFormBundleSectionLocal (I := I) (M := M) g r α φ_first b)).2
        (fun k : Fin r => (chartModelBasis E) (ψ k)) =
      ∏ k : Fin r,
        chartGramMatrix (I := I) g α b (φ_first k) (ψ k) := by
  unfold separableFormBundleSectionLocal
  -- Unfold trivialisation-fibre as in the existing proof.
  change ((separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)).compContinuousLinearMap
        (fun _ : Fin r => (trivializationAt E (TangentSpace I) α).symmL ℝ b))
      (fun k : Fin r => (chartModelBasis E) (ψ k)) = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [separableFormAt_apply]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [chartGramMatrix_apply]
  rfl

/-- The `(0, r)` separable-form bundle section is smooth on the chart base set
at `α` — a sister of `TensorMetricLowering.contMDiffOn_separableFormBundleSection`
that we re-derive here to avoid the `private` qualifier on the original. -/
private lemma contMDiffOn_separableFormBundleSectionLocal
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (separableFormBundleSectionLocal (I := I) (M := M) g r α φ_first)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  set e : Trivialization (Tensor0SModel r ℝ E)
    (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) → M) :=
    trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α
  have hbaseSet_eq : e.baseSet = (trivializationAt E (TangentSpace I) α).baseSet := rfl
  have h_iff := e.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)
    (s := fun b => Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g b r
        (fun k : Fin r => chartBasisVecFiber (I := I) α (φ_first k) b)))
  rw [hbaseSet_eq] at h_iff
  refine h_iff.mpr ?_
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_local
    (I := I) (M := M) _ ?_
  intro ψ
  have h_prod_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => ∏ k : Fin r,
        chartGramMatrix (I := I) g α b (φ_first k) (ψ k))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    refine contMDiffOn_finset_prod (fun k _ => ?_)
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (φ_first k) (ψ k)
  refine h_prod_smooth.congr (fun b hb => ?_)
  exact trivializationAt_separableFormBundleSectionLocal_eval_basis
    (I := I) (M := M) g r α φ_first hb ψ

/-! ## Chart-local `loweredCompose` smoothness for the chart-α covariant derivative -/

/-- Chart-local smoothness of
`b ↦ lowerAllUpperIndices g r s b (toModel (cov_S(b) · chartBasisVecFiber α i b))
        (chartBasisVec α (φ ·) b)`
on the chart base set. -/
private lemma contMDiffOn_lower_chartCov_at_basis
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E))
    (φ : Fin (r + s) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => lowerAllUpperIndices (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (fun j : Fin (r + s) =>
          chartBasisVecFiber (I := I) α (φ j) b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro x₀ hx₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  -- Step 1: Smoothness of the (0, r) separable-form bundle section at x₀.
  have h_sep_smooth_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
        (separableFormBundleSectionLocal (I := I) (M := M) g r α
          (fun k : Fin r => φ (Fin.castAdd s k)))
        x₀ :=
    (contMDiffOn_separableFormBundleSectionLocal (I := I) (M := M) g r α
      (fun k : Fin r => φ (Fin.castAdd s k))).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  -- Step 2: Smoothness of the chart-locally smooth (r, s) section
  -- `b ↦ cov_S(b) · chartBasisVecFiber α i b` at x₀.
  have h_S_smooth_on := tensorCovDeriv_chartBasis_contMDiffOn
    (I := I) (M := M) g r s S α i
  have h_S_smooth_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun b : M =>
          TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) b
            (tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b))) x₀ :=
    h_S_smooth_on.contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  -- Step 3: clm_bundle_apply gives smoothness of the (0, s) bundle section.
  have h_applied : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b : M =>
        TotalSpace.mk' (Tensor0SModel s ℝ E)
          (E := fun y : M => Tensor0SSpace s I y) b
          ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α i b))
            (Tensor0SSpace.ofModel
              (separableFormAt (I := I) (M := M) g b r
                (fun k : Fin r =>
                  chartBasisVecFiber (I := I) α (φ (Fin.castAdd s k)) b))))) x₀ :=
    ContMDiffAt.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SModel r ℝ E) (F₂ := Tensor0SModel s ℝ E)
      (E₁ := fun y : M => Tensor0SSpace r I y)
      (E₂ := fun y : M => Tensor0SSpace s I y)
      (IM := I) (IB := I)
      (b := id)
      (ϕ := fun b : M =>
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
      (v := fun b : M =>
        Tensor0SSpace.ofModel
          (separableFormAt (I := I) (M := M) g b r
            (fun k : Fin r =>
              chartBasisVecFiber (I := I) α (φ (Fin.castAdd s k)) b)))
      h_S_smooth_at h_sep_smooth_at
  -- Step 4: Smoothness of `chartBasisVec` for the remaining s slots at x₀.
  have h_tangent_smooth_at : ∀ j : Fin s,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M =>
          TotalSpace.mk' E (E := fun y : M => TangentSpace I y) b
            (chartBasisVecFiber (I := I) α (φ (Fin.natAdd r j)) b)) x₀ := by
    intro j
    exact (chartBasisVec_contMDiffOn (I := I) α (φ (Fin.natAdd r j))).contMDiffAt
      ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx₀)
  -- Step 5: Pointwise multilinear-bundle-evaluation lemma.
  have h_eval := TensorMultilinear.contMDiffAt_section_apply (I := I) (M := M)
    (T := fun b : M =>
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b))
        (Tensor0SSpace.ofModel
          (separableFormAt (I := I) (M := M) g b r
            (fun k : Fin r =>
              chartBasisVecFiber (I := I) α (φ (Fin.castAdd s k)) b))))
    h_applied
    (v := fun (j : Fin s) (b : M) =>
      chartBasisVecFiber (I := I) α (φ (Fin.natAdd r j)) b)
    h_tangent_smooth_at
  refine h_eval.congr_of_eventuallyEq ?_
  filter_upwards with b
  rw [lowerAllUpperIndices_apply]
  rfl

/-- Chart-local smoothness of
`b ↦ loweredCompose g r s α b (toModel (cov_S(b) · chartBasisVecFiber α i b))`
as a function valued in `Tensor0SModel (r + s) ℝ E`, on the chart base set. -/
private lemma contMDiffOn_loweredCompose_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b))))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_local
    (I := I) (M := M) _ ?_
  intro φ
  refine ContMDiffOn.congr ?_ (fun b _ =>
    (loweredCompose_at_basis_tuple_local
      (I := I) (M := M) g r s α b
      (TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α i b))) φ).symm)
  exact contMDiffOn_lower_chartCov_at_basis (I := I) (M := M) g r s S α i φ

/-- Chart-local continuity (as `ContinuousOn`) of the above. -/
private lemma continuousOn_loweredCompose_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
  (contMDiffOn_loweredCompose_chartCov (I := I) (M := M) g r s S α i).continuousOn

/-! ## Chart-local continuity of `tensorInnerPointwise` on the chart-α covariant
derivative -/

/-- Chart-local continuity, on the chart-α base set, of
`b ↦ tensorInnerPointwise g r s b
       (toModel (cov_S(b) · chartBasisVecFiber α i b))
       (toModel (cov_T(b) · chartBasisVecFiber α j b))`. -/
private lemma continuousOn_tensorInnerPointwise_chartCov
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α i b)))
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (chartBasisVecFiber (I := I) α j b))))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hSα := continuousOn_loweredCompose_chartCov (I := I) (M := M) g r s S α i
  have hTα := continuousOn_loweredCompose_chartCov (I := I) (M := M) g r s T α j
  have hchart :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartTensorInnerPointwise_continuousOn
      (I := I) (M := M) g α r s
      (fun b : M => TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α i b)))
      (fun b : M => TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s T b
          (chartBasisVecFiber (I := I) α j b)))
      hSα hTα
  -- `tensorInnerPointwise = chartTensorInnerPointwise` on the chart base set,
  -- by `tensorInnerPointwise_bridge_identity`.
  refine ContinuousOn.congr hchart ?_
  intro b hb
  exact tensorInnerPointwise_bridge_identity
    (I := I) (M := M) g α r s hb
    (TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α i b)))
    (TensorRSSpace.toModel
      (tensorCovDerivAt (I := I) (M := M) g r s T b
        (chartBasisVecFiber (I := I) α j b)))

/-! ## Chart-local continuity of `chartTensorCovDerivPointwiseInner`

We now combine the previous lemma (continuous `tensorInnerPointwise`) with
chart-local smoothness of the inverse Gram-matrix entries to obtain chart-local
continuity of `chartTensorCovDerivPointwiseInner g α r s S T`. -/

private lemma chartTensorCovDerivPointwiseInner_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (chartTensorCovDerivPointwiseInner (I := I) (M := M) g α r s S T)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  unfold chartTensorCovDerivPointwiseInner
  refine continuousOn_finset_sum _ (fun i _ => ?_)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine ContinuousOn.mul ?_ ?_
  · exact (chartGramMatrixInv_entry_contMDiffOn (I := I) (M := M) g α i j).continuousOn
  · exact continuousOn_tensorInnerPointwise_chartCov (I := I) (M := M) g r s S T α i j

/-! ## Step 2: Global continuity of `tensorCovDerivPointwiseInner` -/

/-- **Global continuity** of the gradient integrand
`tensorCovDerivPointwiseInner g r s S T`. The proof glues chart-local continuity
(via the coordinate-invariance identity) over the chart cover of `M`. -/
theorem tensorCovDerivPointwiseInner_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    Continuous (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T) := by
  rw [continuous_iff_continuousAt]
  intro x
  -- Every point lies in some chart-α base set, in particular for α = x.
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ x
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) x).baseSet :=
    (trivializationAt E (TangentSpace I) x).open_baseSet
  -- Chart-x continuity of the chart-x form.
  have h_chart_cont := chartTensorCovDerivPointwiseInner_continuousOn
    (I := I) (M := M) g r s S T x
  -- Convert to chart-x continuity of `tensorCovDerivPointwiseInner` via the
  -- coordinate-invariance identity, which holds on the chart base set.
  have h_cong : ∀ b ∈ (trivializationAt E (TangentSpace I) x).baseSet,
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T b =
        chartTensorCovDerivPointwiseInner (I := I) (M := M) g x r s S T b := by
    intro b hb
    exact (chartTensorCovDerivPointwiseInner_eq_tensorCovDerivPointwiseInner
      (I := I) (M := M) g x r s S T hb).symm
  have h_local : ContinuousOn
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T)
      (trivializationAt E (TangentSpace I) x).baseSet :=
    h_chart_cont.congr h_cong
  exact h_local.continuousAt (hOpen.mem_nhds hx_base)

/-! ## Step 3: Integrability of the gradient integrand -/

/-- **Integrability** of the gradient integrand against the Riemannian volume
measure on a closed manifold. Follows from continuity and compact support of
the integrand, plus the local-finiteness of the Riemannian volume measure. -/
theorem tensorCovDerivPointwiseInner_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    MeasureTheory.Integrable
      (tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (tensorCovDerivPointwiseInner_continuous
      (I := I) (M := M) g r s S T).integrable_of_hasCompactSupport
    (tensorCovDerivPointwiseInner_hasCompactSupport
      (I := I) (M := M) g r s S T)

/-! ## Step 4: Algebraic properties of the H^1 inner product -/

/-- Symmetry of `tensorH1Inner`. -/
theorem tensorH1Inner_symm (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s S T =
      tensorH1Inner (I := I) (M := M) g r s T S := by
  unfold tensorH1Inner
  congr 1
  · exact tensorL2Inner_symm (I := I) (M := M) g r s S.toFun T.toFun
  · refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact tensorCovDerivPointwiseInner_symm (I := I) (M := M) g r s S T x

/-- Non-negativity of `tensorH1Inner` on the diagonal. -/
theorem tensorH1Inner_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    0 ≤ tensorH1Inner (I := I) (M := M) g r s S S := by
  unfold tensorH1Inner
  refine add_nonneg ?_ ?_
  · exact tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun
  · refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorCovDerivPointwiseInner_nonneg (I := I) (M := M) g r s S x

/-- Additivity of `tensorH1Inner` in the first argument. -/
theorem tensorH1Inner_add_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s (S₁ + S₂) T =
      tensorH1Inner (I := I) (M := M) g r s S₁ T +
        tensorH1Inner (I := I) (M := M) g r s S₂ T := by
  unfold tensorH1Inner
  have hL2 :
      tensorL2Inner (I := I) (M := M) g r s (S₁ + S₂).toFun T.toFun =
        tensorL2Inner (I := I) (M := M) g r s S₁.toFun T.toFun +
          tensorL2Inner (I := I) (M := M) g r s S₂.toFun T.toFun := by
    rw [SmoothCcTensor.toFun_add]
    exact tensorL2Inner_add_left (I := I) (M := M) g r s S₁.toFun S₂.toFun T.toFun
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₁ T)
      (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) S₂ T)
  have hGrad : (fun x : M => tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s (S₁ + S₂) T x) =
      (fun x : M => tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S₁ T x +
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s S₂ T x) := by
    funext x
    exact tensorCovDerivPointwiseInner_add_left
      (I := I) (M := M) g r s S₁ S₂ T x
  rw [hL2, hGrad]
  rw [MeasureTheory.integral_add
    (tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s S₁ T)
    (tensorCovDerivPointwiseInner_integrable (I := I) (M := M) g r s S₂ T)]
  ring

/-- Homogeneity of `tensorH1Inner` in the first argument. -/
theorem tensorH1Inner_smul_left (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S T : SmoothCcTensor g r s) :
    tensorH1Inner (I := I) (M := M) g r s (c • S) T =
      c * tensorH1Inner (I := I) (M := M) g r s S T := by
  unfold tensorH1Inner
  have hL2 :
      tensorL2Inner (I := I) (M := M) g r s (c • S).toFun T.toFun =
        c * tensorL2Inner (I := I) (M := M) g r s S.toFun T.toFun := by
    rw [SmoothCcTensor.toFun_smul]
    exact tensorL2Inner_smul_left (I := I) (M := M) g r s c S.toFun T.toFun
  have hGrad : (fun x : M => tensorCovDerivPointwiseInner
        (I := I) (M := M) g r s (c • S) T x) =
      (fun x : M => c * tensorCovDerivPointwiseInner
          (I := I) (M := M) g r s S T x) := by
    funext x
    exact tensorCovDerivPointwiseInner_smul_left
      (I := I) (M := M) g r s c S T x
  rw [hL2, hGrad]
  rw [MeasureTheory.integral_const_mul]
  ring

/-! ## Wrapper structure `SmoothCcTensorH1`

We package `SmoothCcTensor g r s` into a distinct Lean type so that the `H^1`
pre-Hilbert structure (to be installed in a follow-up commit, conditional on
integrability of the gradient term) does not clash with the existing `L^2`
pre-Hilbert structure on `SmoothCcTensor g r s`. -/

/-- Compactly-supported smooth `(r, s)`-tensor section wrapped to carry the
`H^1` pre-Hilbert structure, a distinct Lean type from `SmoothCcTensor`. -/
structure SmoothCcTensorH1 (g : SmoothRiemannianMetric I M) (r s : ℕ) where
  /-- The underlying `L^2`-wrapped compactly-supported smooth section. -/
  toCcTensor : SmoothCcTensor g r s

namespace SmoothCcTensorH1

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

/-- Two `SmoothCcTensorH1` are equal iff their underlying sections are equal. -/
@[ext] theorem ext {S T : SmoothCcTensorH1 g r s}
    (h : S.toCcTensor = T.toCcTensor) : S = T := by
  cases S; cases T; congr

/-- `toCcTensor` is injective. -/
lemma toCcTensor_injective :
    Function.Injective (fun S : SmoothCcTensorH1 g r s => S.toCcTensor) := by
  intro S T h
  exact ext h

instance : Zero (SmoothCcTensorH1 g r s) := ⟨⟨0⟩⟩
instance : Add (SmoothCcTensorH1 g r s) :=
  ⟨fun S T => ⟨S.toCcTensor + T.toCcTensor⟩⟩
instance : Neg (SmoothCcTensorH1 g r s) := ⟨fun S => ⟨-S.toCcTensor⟩⟩
instance : Sub (SmoothCcTensorH1 g r s) :=
  ⟨fun S T => ⟨S.toCcTensor - T.toCcTensor⟩⟩
instance : SMul ℝ (SmoothCcTensorH1 g r s) :=
  ⟨fun c S => ⟨c • S.toCcTensor⟩⟩

@[simp] lemma toCcTensor_zero :
    (0 : SmoothCcTensorH1 g r s).toCcTensor = 0 := rfl
@[simp] lemma toCcTensor_add (S T : SmoothCcTensorH1 g r s) :
    (S + T).toCcTensor = S.toCcTensor + T.toCcTensor := rfl
@[simp] lemma toCcTensor_neg (S : SmoothCcTensorH1 g r s) :
    (-S).toCcTensor = -S.toCcTensor := rfl
@[simp] lemma toCcTensor_sub (S T : SmoothCcTensorH1 g r s) :
    (S - T).toCcTensor = S.toCcTensor - T.toCcTensor := rfl
@[simp] lemma toCcTensor_smul (c : ℝ) (S : SmoothCcTensorH1 g r s) :
    (c • S).toCcTensor = c • S.toCcTensor := rfl

instance : SMul ℕ (SmoothCcTensorH1 g r s) := ⟨nsmulRec⟩
instance : SMul ℤ (SmoothCcTensorH1 g r s) := ⟨zsmulRec⟩

@[simp] lemma toCcTensor_nsmul (S : SmoothCcTensorH1 g r s) (n : ℕ) :
    (n • S).toCcTensor = n • S.toCcTensor := by
  induction n with
  | zero =>
      change (nsmulRec 0 S).toCcTensor = (0 : ℕ) • S.toCcTensor
      simp [nsmulRec]
  | succ n ih =>
      change (nsmulRec (n + 1) S).toCcTensor = (n + 1) • S.toCcTensor
      change (nsmulRec n S + S).toCcTensor = (n + 1) • S.toCcTensor
      have hn : (nsmulRec n S).toCcTensor = n • S.toCcTensor := ih
      rw [toCcTensor_add, hn, succ_nsmul]

@[simp] lemma toCcTensor_zsmul (S : SmoothCcTensorH1 g r s) (z : ℤ) :
    (z • S).toCcTensor = z • S.toCcTensor := by
  rcases z with n | n
  · change (n • S).toCcTensor = (Int.ofNat n) • S.toCcTensor
    rw [toCcTensor_nsmul]; simp
  · change (-((n + 1) • S)).toCcTensor = (Int.negSucc n) • S.toCcTensor
    rw [toCcTensor_neg, toCcTensor_nsmul]
    show -((n + 1) • S.toCcTensor) = Int.negSucc n • S.toCcTensor
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

instance : AddCommGroup (SmoothCcTensorH1 g r s) :=
  toCcTensor_injective.addCommGroup
    (fun S => S.toCcTensor)
    toCcTensor_zero
    toCcTensor_add
    toCcTensor_neg
    toCcTensor_sub
    toCcTensor_nsmul
    toCcTensor_zsmul

/-- Additive monoid hom from `SmoothCcTensorH1 g r s` to the underlying
compactly-supported smooth section. -/
def toCcTensorAddHom : SmoothCcTensorH1 g r s →+ SmoothCcTensor g r s where
  toFun := fun S => S.toCcTensor
  map_zero' := toCcTensor_zero
  map_add' := toCcTensor_add

instance : Module ℝ (SmoothCcTensorH1 g r s) :=
  toCcTensor_injective.module ℝ toCcTensorAddHom toCcTensor_smul

end SmoothCcTensorH1

/-! ## Step 5: Pre-inner-product core, induced norm and inner-product-space
structure on `SmoothCcTensorH1` -/

set_option linter.unusedSectionVars false in
/-- The pre-inner-product core on `SmoothCcTensorH1 g r s`, whose inner product
is the `H^1` pairing `tensorH1Inner g r s` of the underlying smooth
compactly-supported sections. -/
noncomputable instance instPreInnerProductSpaceCore
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    PreInnerProductSpace.Core ℝ (SmoothCcTensorH1 g r s) where
  inner S T := tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
  conj_inner_symm S T := by
    change (tensorH1Inner (I := I) (M := M) g r s T.toCcTensor S.toCcTensor : ℝ) =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
    exact tensorH1Inner_symm (I := I) (M := M) g r s T.toCcTensor S.toCcTensor
  re_inner_nonneg S := by
    change (0 : ℝ) ≤ tensorH1Inner (I := I) (M := M) g r s S.toCcTensor S.toCcTensor
    exact tensorH1Inner_nonneg (I := I) (M := M) g r s S.toCcTensor
  add_left S₁ S₂ T := by
    change tensorH1Inner (I := I) (M := M) g r s
        (S₁ + S₂).toCcTensor T.toCcTensor =
      tensorH1Inner (I := I) (M := M) g r s S₁.toCcTensor T.toCcTensor +
        tensorH1Inner (I := I) (M := M) g r s S₂.toCcTensor T.toCcTensor
    rw [SmoothCcTensorH1.toCcTensor_add]
    exact tensorH1Inner_add_left (I := I) (M := M) g r s
      S₁.toCcTensor S₂.toCcTensor T.toCcTensor
  smul_left S T c := by
    change tensorH1Inner (I := I) (M := M) g r s
        (c • S).toCcTensor T.toCcTensor =
      c * tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor
    rw [SmoothCcTensorH1.toCcTensor_smul]
    exact tensorH1Inner_smul_left (I := I) (M := M) g r s
      c S.toCcTensor T.toCcTensor

set_option linter.unusedSectionVars false in
/-- The seminormed structure on `SmoothCcTensorH1 g r s` derived from the
pre-inner-product core. -/
noncomputable instance instSeminormedAddCommGroup
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    SeminormedAddCommGroup (SmoothCcTensorH1 g r s) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

set_option linter.unusedSectionVars false in
/-- The inner-product-space structure on `SmoothCcTensorH1 g r s` derived from
the pre-inner-product core. -/
noncomputable instance instInnerProductSpace
    {g : SmoothRiemannianMetric I M} {r s : ℕ} :
    InnerProductSpace ℝ (SmoothCcTensorH1 g r s) :=
  InnerProductSpace.ofCore _

/-! ## Unfolding lemmas for the inner product and seminorm on `SmoothCcTensorH1` -/

set_option linter.unusedSectionVars false in
/-- The `H^1` inner product on `SmoothCcTensorH1 g r s` unfolds to the
`tensorH1Inner` pairing of the underlying smooth compactly-supported
sections. -/
@[simp] theorem SmoothCcTensorH1.inner_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S T : SmoothCcTensorH1 g r s) :
    ⟪S, T⟫_ℝ =
      tensorH1Inner (I := I) (M := M) g r s S.toCcTensor T.toCcTensor := rfl

set_option linter.unusedSectionVars false in
/-- The `H^1` seminorm on `SmoothCcTensorH1 g r s` is the square root of the
`tensorH1Inner` pairing of the underlying section with itself. -/
theorem SmoothCcTensorH1.norm_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensorH1 g r s) :
    ‖S‖ = Real.sqrt (tensorH1Inner
        (I := I) (M := M) g r s S.toCcTensor S.toCcTensor) := rfl

/-! ## Materialisation tests for the `H^1` instances -/

section InstanceTests

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SeminormedAddCommGroup (SmoothCcTensorH1 g r s) := inferInstance

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    InnerProductSpace ℝ (SmoothCcTensorH1 g r s) := inferInstance

end InstanceTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
