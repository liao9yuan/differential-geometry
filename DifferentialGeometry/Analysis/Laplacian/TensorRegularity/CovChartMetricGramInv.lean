import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivChartFormLowerOrder

/-!
# The chart-frame tensor-metric Gram matrix and its smooth inverse

For a smooth Riemannian metric `g` on a closed manifold `(M, g)`, a chart center
`α : M`, and tensor ranks `(r, s)`, the per-component-pair scalar
`covChartMetricGram g r s α P Q` (`CovDerivChartForm.lean`) is the chart-`α`-frame
`(r, s)`-inner product of the chart-frame basis elements indexed by the component
multi-index pairs `P, Q`. Collecting these scalars over all pairs assembles a
matrix indexed by component multi-indices.

This file packages that matrix, proves it is symmetric positive-definite on the
Euclidean chart target, and builds its inverse. The matrix is positive-definite
because the chart-frame `(r, s)`-inner product is positive-definite on non-zero
model tensors and the chart-frame basis family is linearly independent: a
quadratic form `vᵀ 𝓜 v` expands, by bilinearity, into the chart-frame inner
product of the tensor `∑ P, v P • basis P` with itself, which is strictly
positive whenever `v ≠ 0`. The inverse is therefore well-defined; its entries
are smooth on the chart target by the adjugate / determinant formula
`A⁻¹ i j = (det A)⁻¹ · adjugate A i j`, with `det A ≠ 0` from positive
definiteness.

## Main definitions

* `CompIdx r s` — the component multi-index type `(Fin r → Fin n) × (Fin s →
  Fin n)`, a `Fintype`.
* `covChartMetricGramMatrix g r s α y` — the chart-frame tensor-metric Gram
  matrix on `CompIdx r s`, at the chart-target point `y`.
* `covChartMetricGramInv g r s α y` — its matrix inverse.

## Main results

* `covChartMetricGramMatrix_isSymm` — the Gram matrix is symmetric.
* `covChartMetricGramMatrix_posDef` — on the Euclidean chart target the Gram
  matrix is positive-definite.
* `covChartMetricGramInv_mul`, `mul_covChartMetricGramInv` — on the Euclidean
  chart target the inverse multiplies the Gram matrix to the identity, on both
  sides.
* `covChartMetricGramInv_entry_contDiffOn` — each entry of the inverse Gram
  matrix is `C^∞` on the Euclidean chart target.
* `covChartMetricGramInv_symm` — the inverse Gram matrix is symmetric.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators Matrix
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## The component multi-index type

A `(r, s)`-tensor of the chart-frame basis is indexed by a pair of multi-indices:
an `r`-tuple of chart directions (the upper-index slots) and an `s`-tuple of
chart directions (the lower-index slots). The chart-frame tensor-metric Gram is a
matrix over this product type. -/

/-- The component multi-index type for a chart-frame `(r, s)`-tensor: an `r`-tuple
of chart directions paired with an `s`-tuple of chart directions. As a finite
product of finite types it is a `Fintype` and has decidable equality. -/
abbrev CompIdx (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (r s : ℕ) : Type _ :=
  (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E))

/-! ## The chart-frame tensor-metric Gram matrix

Assembling the per-component-pair scalar `covChartMetricGram g r s α P Q y` over
all pairs `(P, Q)` of component multi-indices yields a square matrix indexed by
`CompIdx r s`. Its entry at `(P, Q)` is the chart-`α`-frame `(r, s)`-inner
product of the chart-frame basis elements indexed by `P` and `Q`. -/

/-- The chart-frame tensor-metric Gram matrix at a chart-target point `y`: the
square matrix on `CompIdx r s` whose `(P, Q)`-entry is the chart-frame
tensor-metric Gram scalar `covChartMetricGram g r s α P Q y`. -/
noncomputable def covChartMetricGramMatrix
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    Matrix (CompIdx E r s) (CompIdx E r s) ℝ :=
  Matrix.of (fun P Q => covChartMetricGram (I := I) (M := M) g r s α P Q y)

/-- Entry-unfolding lemma for `covChartMetricGramMatrix`. -/
lemma covChartMetricGramMatrix_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (P Q : CompIdx E r s) :
    covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q =
      covChartMetricGram (I := I) (M := M) g r s α P Q y := rfl

/-! ## Symmetry of the Gram matrix

The `(P, Q)`- and `(Q, P)`-entries of the Gram matrix agree because the
chart-frame tensor-metric Gram scalar is symmetric under the `P, Q` swap
(`covChartMetricGram_symm`). -/

/-- **The chart-frame tensor-metric Gram matrix is symmetric.** Its transpose
equals itself, since each entry is symmetric under the component multi-index
swap. -/
theorem covChartMetricGramMatrix_isSymm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    (covChartMetricGramMatrix (I := I) (M := M) g r s α y).IsSymm := by
  refine Matrix.IsSymm.ext (fun P Q => ?_)
  rw [covChartMetricGramMatrix_apply, covChartMetricGramMatrix_apply]
  exact covChartMetricGram_symm (I := I) (M := M) g r s α Q P y

/-! ## Positive-definiteness of the Gram matrix

For a non-zero coefficient vector `v : CompIdx r s → ℝ`, the quadratic form
`vᵀ 𝓜 v = ∑ P ∑ Q, v P · 𝓜 P Q · v Q` expands, via the bilinearity of the
chart-frame `(r, s)`-inner product, into the chart-frame inner product of the
model tensor `Tv := ∑ P, v P • tensorChartBasisElement r s P.1 P.2` with itself.
The tensor `Tv` is non-zero because the chart-frame basis family is biorthogonal
to the chart-frame component projections: a non-zero coefficient `v P₀` is
recovered as `tensorChartComponentProjection r s P₀.1 P₀.2 Tv`. Strict
positivity of the chart-frame `(r, s)`-quadratic form at a non-zero tensor
(`chartTensorInnerPointwise_rs_model_pos_of_ne_zero`) then yields a strictly
positive quadratic form. -/

/-- The chart-frame `(r, s)`-inner product of two model tensors `X, Y` expands
as a finite component-coupled sum over the chart-frame tensor-metric Gram on the
basis, against the chart-frame component projections of `X` and `Y`. (A direct
restatement of the bilinearity expansion, specialised so that the Gram-on-basis
factor reads as the matrix entry.) -/
private lemma chartInner_eq_gramMatrix_quadratic
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (X Y : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) X Y =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q *
          (tensorChartComponentProjection (E := E) r s P.1 P.2 X *
            tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y) := by
  classical
  -- Expand both arguments in the chart-frame basis.
  have hX : X = ∑ P : CompIdx E r s,
      tensorChartComponentProjection (E := E) r s P.1 P.2 X •
        tensorChartBasisElement (E := E) r s P.1 P.2 := by
    rw [Fintype.sum_prod_type
      (f := fun P : CompIdx E r s =>
        tensorChartComponentProjection (E := E) r s P.1 P.2 X •
          tensorChartBasisElement (E := E) r s P.1 P.2)]
    exact tensorRSModel_eq_sum_basis (E := E) r s X
  have hY : Y = ∑ Q : CompIdx E r s,
      tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
        tensorChartBasisElement (E := E) r s Q.1 Q.2 := by
    rw [Fintype.sum_prod_type
      (f := fun Q : CompIdx E r s =>
        tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
          tensorChartBasisElement (E := E) r s Q.1 Q.2)]
    exact tensorRSModel_eq_sum_basis (E := E) r s Y
  -- Substitute the expansion of `X` into the first slot.
  conv_lhs => rw [hX]
  -- First-slot additivity / homogeneity over the finite sum.
  rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (∑ P : CompIdx E r s,
          tensorChartComponentProjection (E := E) r s P.1 P.2 X •
            tensorChartBasisElement (E := E) r s P.1 P.2) Y =
      ∑ P : CompIdx E r s,
        tensorChartComponentProjection (E := E) r s P.1 P.2 X *
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            (tensorChartBasisElement (E := E) r s P.1 P.2) Y from ?_]
  · -- Expand `Y` in the second slot of each summand.
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (tensorChartBasisElement (E := E) r s P.1 P.2) Y =
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (tensorChartBasisElement (E := E) r s P.1 P.2)
          (∑ Q : CompIdx E r s,
            tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
              tensorChartBasisElement (E := E) r s Q.1 Q.2) from by rw [← hY]]
    rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (tensorChartBasisElement (E := E) r s P.1 P.2)
          (∑ Q : CompIdx E r s,
            tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
              tensorChartBasisElement (E := E) r s Q.1 Q.2) =
        ∑ Q : CompIdx E r s,
          tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y *
            chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              (tensorChartBasisElement (E := E) r s P.1 P.2)
              (tensorChartBasisElement (E := E) r s Q.1 Q.2) from ?_]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      rw [covChartMetricGramMatrix_apply, covChartMetricGram_def]
      ring
    · -- Second-slot additivity / homogeneity over the finite sum.
      induction (Finset.univ : Finset (CompIdx E r s)) using Finset.induction with
      | empty =>
          rw [Finset.sum_empty, Finset.sum_empty]
          rw [show (0 : TensorRSModel r s ℝ E) =
              (0 : ℝ) • tensorChartBasisElement (E := E) r s P.1 P.2 from
            (zero_smul ℝ _).symm]
          rw [chartTensorInnerPointwise_rs_model_smul_right, zero_mul]
      | insert Q A hQ ih =>
          rw [Finset.sum_insert hQ, Finset.sum_insert hQ]
          rw [chartTensorInnerPointwise_rs_model_add_right,
            chartTensorInnerPointwise_rs_model_smul_right, ih]
  · -- First-slot additivity / homogeneity over the finite sum.
    induction (Finset.univ : Finset (CompIdx E r s)) using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : TensorRSModel r s ℝ E) =
            (0 : ℝ) • (0 : TensorRSModel r s ℝ E) from
          (smul_zero (0 : ℝ)).symm]
        rw [chartTensorInnerPointwise_rs_model_smul_left, zero_mul]
    | insert P A hP ih =>
        rw [Finset.sum_insert hP, Finset.sum_insert hP]
        rw [chartTensorInnerPointwise_rs_model_add_left,
          chartTensorInnerPointwise_rs_model_smul_left, ih]

/-- The chart-frame model tensor assembled from a coefficient vector `v` over
the component multi-indices: `∑ P, v P • tensorChartBasisElement r s P.1 P.2`. -/
private noncomputable def gramCoeffTensor (r s : ℕ) (v : CompIdx E r s → ℝ) :
    TensorRSModel r s ℝ E :=
  ∑ P : CompIdx E r s, v P • tensorChartBasisElement (E := E) r s P.1 P.2

/-- The chart-frame component projection of `gramCoeffTensor r s v` at a
multi-index `P₀` recovers the coefficient `v P₀`. The chart-frame basis family
is biorthogonal to the chart-frame component projections, so all off-diagonal
terms of the sum vanish. -/
private lemma tensorChartComponentProjection_gramCoeffTensor (r s : ℕ)
    (v : CompIdx E r s → ℝ) (P₀ : CompIdx E r s) :
    tensorChartComponentProjection (E := E) r s P₀.1 P₀.2
        (gramCoeffTensor (E := E) r s v) = v P₀ := by
  classical
  rw [gramCoeffTensor, map_sum]
  rw [Finset.sum_eq_single P₀]
  · rw [map_smul, smul_eq_mul,
      tensorChartComponentProjection_basisElement (E := E) r s P₀.1 P₀.1 P₀.2 P₀.2]
    simp
  · intro P _ hP
    rw [map_smul, smul_eq_mul,
      tensorChartComponentProjection_basisElement (E := E) r s P₀.1 P.1 P₀.2 P.2]
    -- `P ≠ P₀` forces at least one of the two index-tuple equalities to fail,
    -- so the biorthogonality product is zero.
    by_cases h1 : P₀.1 = P.1
    · by_cases h2 : P.2 = P₀.2
      · have hPP₀ : P = P₀ := Prod.ext h1.symm h2
        exact absurd hPP₀ hP
      · rw [if_neg h2, mul_zero, mul_zero]
    · rw [if_neg h1, zero_mul, mul_zero]
  · intro hP₀
    exact absurd (Finset.mem_univ P₀) hP₀

/-- If a coefficient vector `v` over the component multi-indices is non-zero,
the assembled chart-frame tensor `gramCoeffTensor r s v` is non-zero — a
component projection recovers a non-zero coordinate. -/
private lemma gramCoeffTensor_ne_zero (r s : ℕ) {v : CompIdx E r s → ℝ}
    (hv : v ≠ 0) :
    gramCoeffTensor (E := E) r s v ≠ 0 := by
  intro hzero
  apply hv
  funext P₀
  have hproj := tensorChartComponentProjection_gramCoeffTensor (E := E) r s v P₀
  rw [hzero, map_zero] at hproj
  exact hproj.symm

/-- The `*ᵥ` / `⬝ᵥ` quadratic form of the Gram matrix against a coefficient
vector `v` expands as the double sum `∑ P ∑ Q, v P · 𝓜 P Q · v Q`. -/
private lemma gramMatrix_star_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (v : CompIdx E r s → ℝ) :
    star v ⬝ᵥ (covChartMetricGramMatrix (I := I) (M := M) g r s α y *ᵥ v) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        v P * covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q *
          v Q := by
  classical
  -- Unfold `dotProduct` and `mulVec` to explicit finite sums.
  change (∑ P : CompIdx E r s,
      star v P * (covChartMetricGramMatrix (I := I) (M := M) g r s α y *ᵥ v) P) =
    ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
      v P * covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q * v Q
  refine Finset.sum_congr rfl (fun P _ => ?_)
  change star (v P) *
      (∑ Q : CompIdx E r s,
        covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q * v Q) =
    ∑ Q : CompIdx E r s,
      v P * covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q * v Q
  rw [Finset.mul_sum, star_trivial]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  ring

/-- **On the Euclidean chart target the chart-frame tensor-metric Gram matrix
is positive-definite.** Symmetry comes from `covChartMetricGramMatrix_isSymm`;
strict positivity of the quadratic form follows because, for `v ≠ 0`, the
quadratic form `vᵀ 𝓜 v` is the chart-frame `(r, s)`-inner product of the
non-zero tensor `∑ P, v P • basis P` with itself, which is `> 0` by strict
positivity of the chart-frame `(r, s)`-quadratic form at a non-zero tensor. -/
theorem covChartMetricGramMatrix_posDef
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (covChartMetricGramMatrix (I := I) (M := M) g r s α y).PosDef := by
  classical
  -- Notation: `b` is the chart-source preimage of `y`; it lies in the chart
  -- source, hence in the tangent trivialisation base set.
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart
  -- Symmetry, restated as a Hermitian-matrix property (over `ℝ`).
  have hSymm : (covChartMetricGramMatrix (I := I) (M := M) g r s α y).IsSymm :=
    covChartMetricGramMatrix_isSymm (I := I) (M := M) g r s α y
  have hHerm :
      (covChartMetricGramMatrix (I := I) (M := M) g r s α y).IsHermitian := by
    refine Matrix.IsHermitian.ext (fun P Q => ?_)
    rw [star_trivial]
    exact hSymm.apply P Q
  -- Positive-definiteness via the dot-product / matrix-vector characterisation.
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm (fun v hv => ?_)
  -- Expand the quadratic form as a double sum, then recognise it as the
  -- chart-frame inner product of the assembled tensor with itself.
  rw [gramMatrix_star_dotProduct_mulVec (I := I) (M := M) g r s α y v]
  -- The chart-frame inner product of `gramCoeffTensor v` with itself.
  have hquad := chartInner_eq_gramMatrix_quadratic (I := I) (M := M) g r s α
    (y := y) (gramCoeffTensor (E := E) r s v) (gramCoeffTensor (E := E) r s v)
  -- Each component projection of `gramCoeffTensor v` is the coefficient `v`.
  have hsum_eq :
      (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q *
            (tensorChartComponentProjection (E := E) r s P.1 P.2
                (gramCoeffTensor (E := E) r s v) *
              tensorChartComponentProjection (E := E) r s Q.1 Q.2
                (gramCoeffTensor (E := E) r s v))) =
        ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          v P * covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q *
            v Q := by
    refine Finset.sum_congr rfl (fun P _ => ?_)
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [tensorChartComponentProjection_gramCoeffTensor (E := E) r s v P,
      tensorChartComponentProjection_gramCoeffTensor (E := E) r s v Q]
    ring
  rw [hsum_eq] at hquad
  -- Thus the quadratic form equals the chart-frame diagonal value of
  -- `gramCoeffTensor v`, which is strictly positive since the tensor is
  -- non-zero (`v ≠ 0`).
  rw [← hquad, ← hb_def]
  exact chartTensorInnerPointwise_rs_model_pos_of_ne_zero (I := I) (M := M)
    g r s α hb_base (gramCoeffTensor_ne_zero (E := E) r s hv)

/-! ## The inverse Gram matrix

Positive-definiteness implies the Gram matrix has a non-zero determinant, so its
matrix inverse is well-defined. The inverse Gram matrix is the (right and left)
two-sided inverse on the Euclidean chart target. -/

/-- The inverse of the chart-frame tensor-metric Gram matrix at a chart-target
point `y`. -/
noncomputable def covChartMetricGramInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    Matrix (CompIdx E r s) (CompIdx E r s) ℝ :=
  (covChartMetricGramMatrix (I := I) (M := M) g r s α y)⁻¹

/-- The determinant of the chart-frame tensor-metric Gram matrix is positive on
the Euclidean chart target. -/
private lemma covChartMetricGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    0 < (covChartMetricGramMatrix (I := I) (M := M) g r s α y).det :=
  (covChartMetricGramMatrix_posDef (I := I) (M := M) g r s α hy).det_pos

/-- **The inverse Gram matrix is a left inverse of the Gram matrix** on the
Euclidean chart target. -/
theorem covChartMetricGramInv_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covChartMetricGramInv (I := I) (M := M) g r s α y *
        covChartMetricGramMatrix (I := I) (M := M) g r s α y = 1 := by
  rw [covChartMetricGramInv]
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr
      (ne_of_gt (covChartMetricGramMatrix_det_pos (I := I) (M := M) g r s α hy)))

/-- **The inverse Gram matrix is a right inverse of the Gram matrix** on the
Euclidean chart target. -/
theorem mul_covChartMetricGramInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covChartMetricGramMatrix (I := I) (M := M) g r s α y *
        covChartMetricGramInv (I := I) (M := M) g r s α y = 1 := by
  rw [covChartMetricGramInv]
  exact Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr
      (ne_of_gt (covChartMetricGramMatrix_det_pos (I := I) (M := M) g r s α hy)))

/-! ## Smoothness of the inverse Gram matrix entries

On the Euclidean chart target the determinant of the Gram matrix is positive,
hence non-zero, and Cramer's rule gives `A⁻¹ i j = (det A)⁻¹ · adjugate A i j`.
The adjugate entries are polynomials in the matrix entries, hence `C^∞`; the
determinant is `C^∞` and non-vanishing, so `(det ·)⁻¹` is `C^∞` by
`contDiffAt_inv`. -/

/-- Each entry of the Gram matrix is `C^∞` on the Euclidean chart target — a
direct restatement of `covChartMetricGram_contDiffOn`. -/
private lemma covChartMetricGramMatrix_entry_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P Q : CompIdx E r s) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        covChartMetricGramMatrix (I := I) (M := M) g r s α y P Q)
      (chartTargetEuclid (I := I) (M := M) α) :=
  covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q

/-- The determinant of the Gram matrix is `C^∞` on the Euclidean chart target.
The determinant is a polynomial — a finite signed sum over permutations of
products of matrix entries — and each entry is `C^∞`. -/
private lemma covChartMetricGramMatrix_det_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (covChartMetricGramMatrix (I := I) (M := M) g r s α y).det)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Expand the determinant via the Leibniz permutation formula.
  have hexp :
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (covChartMetricGramMatrix (I := I) (M := M) g r s α y).det)
        = fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ∑ σ : Equiv.Perm (CompIdx E r s),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ P : CompIdx E r s,
                  covChartMetricGramMatrix (I := I) (M := M) g r s α y (σ P) P := by
    funext y
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine ContDiffOn.sum (fun σ _ => ?_)
  refine ContDiffOn.mul contDiffOn_const ?_
  refine contDiffOn_prod (fun P _ => ?_)
  exact covChartMetricGramMatrix_entry_contDiffOn (I := I) (M := M) g r s α
    (σ P) P

/-- Each entry of the adjugate of the Gram matrix is `C^∞` on the Euclidean
chart target. The adjugate entry at `(P, Q)` is the determinant of the matrix
with the `Q`-th row replaced by a standard basis vector — again a polynomial in
the entries of the Gram matrix. -/
private lemma covChartMetricGramMatrix_adjugate_entry_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P Q : CompIdx E r s) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (covChartMetricGramMatrix (I := I) (M := M) g r s α y).adjugate P Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- `adjugate A P Q = det (A.updateRow Q (Pi.single P 1))`; expand via Leibniz.
  have hexp :
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (covChartMetricGramMatrix (I := I) (M := M) g r s α y).adjugate P Q)
        = fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ∑ σ : Equiv.Perm (CompIdx E r s),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ K : CompIdx E r s,
                  (covChartMetricGramMatrix (I := I) (M := M) g r s α y).updateRow Q
                    (Pi.single P (1 : ℝ)) (σ K) K := by
    funext y
    rw [Matrix.adjugate_apply, Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine ContDiffOn.sum (fun σ _ => ?_)
  refine ContDiffOn.mul contDiffOn_const ?_
  refine contDiffOn_prod (fun K _ => ?_)
  by_cases hσK : σ K = Q
  · -- The replaced row is the constant standard basis vector.
    have heq :
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            (covChartMetricGramMatrix (I := I) (M := M) g r s α y).updateRow Q
              (Pi.single P (1 : ℝ)) (σ K) K)
          = fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
              (Pi.single (M := fun _ : CompIdx E r s => ℝ) P (1 : ℝ)) K := by
      funext y
      rw [hσK, Matrix.updateRow_self]
    rw [heq]
    exact contDiffOn_const
  · -- An untouched row: a Gram matrix entry.
    have heq :
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            (covChartMetricGramMatrix (I := I) (M := M) g r s α y).updateRow Q
              (Pi.single P (1 : ℝ)) (σ K) K)
          = fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
              covChartMetricGramMatrix (I := I) (M := M) g r s α y (σ K) K := by
      funext y
      rw [Matrix.updateRow_ne hσK]
    rw [heq]
    exact covChartMetricGramMatrix_entry_contDiffOn (I := I) (M := M) g r s α
      (σ K) K

/-- **Each entry of the inverse Gram matrix is `C^∞` on the Euclidean chart
target.** On the chart target the determinant is positive (hence non-zero), so
Cramer's rule expresses the inverse entry as `(det A)⁻¹ · adjugate A P Q`; the
adjugate entry is `C^∞`, and `(det ·)⁻¹` is `C^∞` since the determinant is
`C^∞` and non-vanishing. -/
theorem covChartMetricGramInv_entry_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P Q : CompIdx E r s) :
    ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        covChartMetricGramInv (I := I) (M := M) g r s α y P Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- On the chart target, `A⁻¹ P Q = (det A)⁻¹ * adjugate A P Q`.
  have hcongr : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      covChartMetricGramInv (I := I) (M := M) g r s α y P Q =
        ((covChartMetricGramMatrix (I := I) (M := M) g r s α y).det)⁻¹ *
          (covChartMetricGramMatrix (I := I) (M := M) g r s α y).adjugate P Q := by
    intro y hy
    rw [covChartMetricGramInv, Matrix.inv_def]
    -- `A⁻¹ P Q = (det⁻¹ʳ • adjugate A) P Q`.
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    -- For `ℝ` (a field) `Ring.inverse a = a⁻¹`.
    exact Ring.inverse_eq_inv _
  refine ContDiffOn.congr ?_ hcongr
  refine ContDiffOn.mul ?_
    (covChartMetricGramMatrix_adjugate_entry_contDiffOn (I := I) (M := M)
      g r s α P Q)
  -- `(det · )⁻¹` is `C^∞` where the determinant is non-zero.
  intro y hy
  have hdet_pos := covChartMetricGramMatrix_det_pos (I := I) (M := M) g r s α hy
  have hdet_ne :
      (covChartMetricGramMatrix (I := I) (M := M) g r s α y).det ≠ 0 :=
    ne_of_gt hdet_pos
  have hsmooth_inv : ContDiffAt ℝ ∞ (fun u : ℝ => u⁻¹)
      (covChartMetricGramMatrix (I := I) (M := M) g r s α y).det :=
    contDiffAt_inv _ hdet_ne
  have h_at := covChartMetricGramMatrix_det_contDiffOn (I := I) (M := M)
    g r s α y hy
  exact hsmooth_inv.comp_contDiffWithinAt y h_at

/-! ## Symmetry of the inverse Gram matrix

The Gram matrix is symmetric at every chart-target point, and the matrix inverse
commutes with the transpose (`A⁻¹ᵀ = Aᵀ⁻¹`); hence the inverse Gram matrix is
symmetric — with no chart-target restriction, since entry-symmetry of the Gram
matrix is itself unconditional. -/

/-- **The inverse Gram matrix is symmetric.** Swapping the two component
multi-indices leaves an entry of the inverse Gram matrix unchanged, because the
Gram matrix is symmetric and matrix inversion commutes with transposition. -/
theorem covChartMetricGramInv_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (P Q : CompIdx E r s) :
    covChartMetricGramInv (I := I) (M := M) g r s α y P Q =
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P := by
  classical
  -- The inverse of the symmetric Gram matrix is symmetric: `(A⁻¹)ᵀ = (Aᵀ)⁻¹ =
  -- A⁻¹`.
  have hSymm : (covChartMetricGramMatrix (I := I) (M := M) g r s α y).IsSymm :=
    covChartMetricGramMatrix_isSymm (I := I) (M := M) g r s α y
  have hInvSymm : (covChartMetricGramInv (I := I) (M := M) g r s α y).IsSymm := by
    unfold Matrix.IsSymm
    rw [covChartMetricGramInv, Matrix.transpose_nonsing_inv, hSymm.eq]
  -- `IsSymm.apply` swaps the indices.
  exact hInvSymm.apply Q P

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
