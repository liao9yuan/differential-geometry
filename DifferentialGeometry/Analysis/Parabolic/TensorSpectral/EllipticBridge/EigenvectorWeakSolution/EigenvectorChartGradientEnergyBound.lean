import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorWeakPartials
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Spectrum
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.CovGradL2

/-!
# A chart-local gradient-energy estimate for an eigenvector chart component

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i : TensorEigenIdx g r s` with nonzero resolvent eigenvalue `μ := i.fst.val`,
a chart center `α : M`, a component multi-index `P₀`, and a chart-coordinate
direction `k`, the weak `k`-th chart partial `eigenvectorChartWeakPartial g r s
h_atlas i α P₀ k` of the eigenvector chart component is controlled in `L²` by a
`√(μ⁻¹)`-weighted multiple of the abstract `L²` norm of the eigenbasis vector
`tensorResolventEigenbasisVec h_atlas i`.

## Why an energy estimate is needed

A higher-order norm of a function cannot be bounded by a lower-order norm of the
same function in general. The bound below is genuine precisely because the
function is an *eigenvector*: it satisfies the resolvent eigen-equation
`tensorResolventL2 g r s φ = μ • φ`, and this equation supplies an *energy
identity* relating the squared `H¹` norm of the resolvent-applied eigenvector to
the squared `L²` norm of the eigenvector itself.

The constant `C` in the headline depends only on the geometric data
`g r s α P₀ k` — it is the operator norm of the canonical chart-partial
continuous linear map `eigenvectorChartPartialCLM g r s α P₀ k`. In particular
it is uniform over the eigenbasis index `i`: the headline quantifies `C` with
`∃` *before* the universal `∀ i`, and the only `i`-dependence of the right-hand
side is the explicit `√(μ⁻¹)` factor multiplying the abstract `L²` norm.

## The energy identity

Write `φ := tensorResolventEigenbasisVec h_atlas i ∈ TensorL2 r s g` for the
eigenbasis vector and `μ := i.fst.val` for the associated nonzero resolvent
eigenvalue. The defining variational identity of the resolvent
(`tensorResolvent_inner_eq_lpFunctional`), evaluated at `f := φ` and at the test
element `v := tensorResolvent g r s φ`, gives

`‖tensorResolvent g r s φ‖²_{H¹} = ⟪tensorResolventL2 g r s φ, φ⟫_{L²}`.

The eigen-equation `tensorResolventL2 g r s φ = μ • φ` then collapses the
right-hand side to `μ · ‖φ‖²_{L²}`. Since the eigenbasis vector is a unit
vector (`tensorResolventEigenbasisVec_orthonormal`), the eigenvalue is
non-negative, and taking square roots yields

`‖eigenvectorResolvent g r s h_atlas i‖_{H¹} = √μ · ‖φ‖_{L²}`.

## The chart projection

The covariant gradient extended to the `H¹` completion, `tensorCovGradL2Compl`,
has operator norm `≤ 1`; hence the abstract gradient of the eigenvector is
controlled by the `√μ`-weighted `L²` norm above. The chart-local statement is
obtained from the canonical chart-partial continuous linear map
`eigenvectorChartPartialCLM g r s α P₀ k`: the weak chart partial
`eigenvectorChartWeakPartial g r s h_atlas i α P₀ k` is the coercion-to-function
of `μ⁻¹` times the value of this map on the eigenvector resolvent, so its `L²`
norm is at most `μ⁻¹ · ‖eigenvectorChartPartialCLM …‖ · ‖eigenvectorResolvent
…‖_{H¹}`. Combining with the energy identity and `μ⁻¹ · √μ = √(μ⁻¹)` gives the
headline.

## Main results

* `eigenvectorResolvent_h1NormSq_eq` — the energy identity in squared form:
  `‖eigenvectorResolvent g r s h_atlas i‖² = μ · ‖tensorResolventEigenbasisVec
  h_atlas i‖²`.
* `eigenvectorResolvent_h1Norm_le` — the energy identity in `√`-form:
  `‖eigenvectorResolvent g r s h_atlas i‖ ≤ √μ · ‖tensorResolventEigenbasisVec
  h_atlas i‖`.
* `tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le` — the abstract
  gradient-energy bound: `‖tensorCovGradL2Compl g r s (eigenvectorResolvent …)‖
  ≤ √μ · ‖tensorResolventEigenbasisVec h_atlas i‖`.
* `eigenvectorChartWeakPartial_eLpNorm_le` — **the headline**: a chart-geometric
  constant `C ≥ 0`, uniform over the eigenbasis index `i`, such that the `L²`
  norm of `eigenvectorChartWeakPartial g r s h_atlas i α P₀ k` over the Euclidean
  chart target is at most `C · √(μ⁻¹)` times the abstract `L²` norm of
  `tensorResolventEigenbasisVec h_atlas i`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The eigen-equation for the eigenbasis vector

The eigenbasis vector `tensorResolventEigenbasisVec h_atlas i` lies, by
`tensorResolventEigenbasisVec_mem`, in the resolvent eigenspace at the nonzero
eigenvalue `μ := i.fst.val`; membership unfolds to the eigen-equation
`tensorResolventL2 g r s φ = μ • φ`. -/

/-- The eigenbasis vector satisfies the resolvent eigen-equation
`tensorResolventL2 g r s φ = μ • φ`, where `φ := tensorResolventEigenbasisVec
h_atlas i` and `μ := i.fst.val`. -/
private lemma tensorResolventL2_eigenbasisVec_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorResolventL2 (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) =
      i.fst.val • tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i :=
  (mem_tensorResolventEigenspace_iff (I := I) (M := M) g r s i.fst.val
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)).mp
    (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)

/-- The eigenbasis vector is a unit vector: it is, by construction, one of the
vectors of an orthonormal basis of its eigenspace. -/
private lemma norm_tensorResolventEigenbasisVec_eq_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ = 1 :=
  (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s) h_atlas).norm_eq_one i

/-! ### Chart-locality-free twins of the eigen-equation and unit-norm facts

The compactness witness `tensorResolventL2_isCompactOperator_intrinsic` selects
the eigenbasis vector `tensorResolventEigenbasisVec_ofCompact` with no chart-
selection hypothesis. Membership in the eigenspace unfolds, exactly as in the
`h_atlas` case, to the eigen-equation; orthonormality of the family supplies the
unit norm. `[CompleteSpace E]` is derived locally from finite-dimensionality. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Chart-locality-free eigen-equation.** The unconditional eigenbasis vector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic
g r s) i` satisfies the resolvent eigen-equation
`tensorResolventL2 g r s φ = μ • φ`, where `μ := i.fst.val`. No chart-selection
hypothesis. -/
private lemma tensorResolventL2_eigenbasisVec_eq_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorResolventL2 (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i) =
      i.fst.val • tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i :=
  (mem_tensorResolventEigenspace_iff (I := I) (M := M) g r s i.fst.val
      (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i)).mp
    (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **Chart-locality-free unit norm.** The unconditional eigenbasis vector is a
unit vector: it is one of the vectors of an orthonormal basis of its
eigenspace. -/
private lemma norm_tensorResolventEigenbasisVec_ofCompact_eq_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ = 1 :=
  (tensorResolventEigenbasisVec_ofCompact_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
      g r s)).norm_eq_one i

/-! ## The energy identity for the eigenvector

The defining variational identity of the resolvent, evaluated at the eigenbasis
vector and at the test element `tensorResolvent g r s φ`, exhibits the squared
`H¹` norm of `eigenvectorResolvent g r s h_atlas i` as `μ` times the squared
`L²` norm of the eigenbasis vector. -/

/-- **The energy identity in squared form.** For an eigenbasis index `i` with
nonzero resolvent eigenvalue `μ := i.fst.val`, the squared `H¹` norm of the
eigenvector resolvent `eigenvectorResolvent g r s h_atlas i` equals `μ` times
the squared `L²` norm of the eigenbasis vector `tensorResolventEigenbasisVec
h_atlas i`.

This is the energy identity supplied by the resolvent eigen-equation: it is the
mathematical content that makes the higher-order chart-partial bound below
genuine rather than vacuous. -/
theorem eigenvectorResolvent_h1NormSq_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖eigenvectorResolvent (I := I) (M := M) g r s h_atlas i‖ ^ 2 =
      i.fst.val *
        ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ ^ 2 := by
  -- Abbreviations: `φ` the eigenbasis vector, `Rφ` the resolvent applied to it.
  set φ := tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i with hφ
  set Rφ := tensorResolvent (I := I) (M := M) g r s φ with hRφ
  -- `eigenvectorResolvent … = Rφ` by definition.
  have h_eig : eigenvectorResolvent (I := I) (M := M) g r s h_atlas i = Rφ := by
    rw [eigenvectorResolvent, hRφ, hφ]
  rw [h_eig]
  -- The squared `H¹` norm is the `H¹` self-pairing.
  have h_self : ‖Rφ‖ ^ 2 = ⟪Rφ, Rφ⟫_ℝ := (real_inner_self_eq_norm_sq Rφ).symm
  -- The variational identity at `f := φ`, `v := Rφ`.
  have h_var : ⟪Rφ, Rφ⟫_ℝ =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s Rφ, φ⟫_ℝ := by
    rw [hRφ]
    exact tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s φ
      (tensorResolvent (I := I) (M := M) g r s φ)
  -- `TensorH1ComplToTensorL2 (tensorResolvent φ) = tensorResolventL2 φ = μ • φ`.
  have h_l2 : TensorH1ComplToTensorL2 (I := I) (M := M) g r s Rφ =
      i.fst.val • φ := by
    rw [hRφ, ← tensorResolventL2_apply (I := I) (M := M) g r s φ]
    exact tensorResolventL2_eigenbasisVec_eq (I := I) (M := M) g r s h_atlas i
  -- Assemble: `‖Rφ‖² = ⟪μ • φ, φ⟫ = μ · ‖φ‖²`.
  rw [h_self, h_var, h_l2, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- **The energy identity in `√`-form.** For an eigenbasis index `i` with
nonzero resolvent eigenvalue `μ := i.fst.val`, the `H¹` norm of the eigenvector
resolvent `eigenvectorResolvent g r s h_atlas i` is bounded by `√μ` times the
`L²` norm of the eigenbasis vector `tensorResolventEigenbasisVec h_atlas i`.

The eigenvalue is non-negative because the squared-form energy identity exhibits
`μ · ‖φ‖²` as a square, and the eigenbasis vector is a unit vector. -/
theorem eigenvectorResolvent_h1Norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖eigenvectorResolvent (I := I) (M := M) g r s h_atlas i‖ ≤
      Real.sqrt i.fst.val *
        ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  have h_sq := eigenvectorResolvent_h1NormSq_eq
    (I := I) (M := M) g r s h_atlas i
  -- `μ ≥ 0`: it is a resolvent eigenvalue of a unit eigenvector.
  have hμ_pos : 0 < i.fst.val :=
    (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
      (by
        intro h_zero
        have h_norm := norm_tensorResolventEigenbasisVec_eq_one
          (I := I) (M := M) g r s h_atlas i
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)).1
  have hμ_nn : 0 ≤ i.fst.val := le_of_lt hμ_pos
  -- The right-hand side is non-negative.
  have h_rhs_nn :
      0 ≤ Real.sqrt i.fst.val *
        ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  -- Compare squares: `‖Rφ‖² = μ · ‖φ‖² = (√μ · ‖φ‖)²`.
  have h_rhs_sq :
      (Real.sqrt i.fst.val *
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) ^ 2 =
        i.fst.val *
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hμ_nn]
  have h_le_sq :
      ‖eigenvectorResolvent (I := I) (M := M) g r s h_atlas i‖ ^ 2 ≤
        (Real.sqrt i.fst.val *
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) ^ 2 := by
    rw [h_rhs_sq]; exact le_of_eq h_sq
  -- From `a² ≤ b²` and `0 ≤ b` conclude `a ≤ b` (here `a = ‖·‖ ≥ 0`).
  exact (abs_le_of_sq_le_sq' h_le_sq h_rhs_nn).2

/-! ### Chart-locality-free twins of the energy identity

The same variational identity, eigen-equation, and unit-norm facts — now in
their `_ofCompact` / `_unconditional` forms — reproduce the energy identity for
the unconditional eigenvector resolvent `eigenvectorResolvent_unconditional`. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The energy identity in squared form (chart-locality-free).** Chart-
locality-free twin of `eigenvectorResolvent_h1NormSq_eq`: the squared `H¹` norm
of `eigenvectorResolvent_unconditional g r s i` equals `μ := i.fst.val` times
the squared `L²` norm of the unconditional eigenbasis vector. -/
theorem eigenvectorResolvent_h1NormSq_eq_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖eigenvectorResolvent_unconditional (I := I) (M := M) g r s i‖ ^ 2 =
      i.fst.val *
        ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i‖ ^ 2 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- Abbreviations: `φ` the unconditional eigenbasis vector, `Rφ` the resolvent
  -- applied to it.
  set φ := tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s) i
    with hφ
  set Rφ := tensorResolvent (I := I) (M := M) g r s φ with hRφ
  -- `eigenvectorResolvent_unconditional … = Rφ` by definition.
  have h_eig :
      eigenvectorResolvent_unconditional (I := I) (M := M) g r s i = Rφ := by
    rw [eigenvectorResolvent_unconditional, hRφ, hφ]
  rw [h_eig]
  -- The squared `H¹` norm is the `H¹` self-pairing.
  have h_self : ‖Rφ‖ ^ 2 = ⟪Rφ, Rφ⟫_ℝ := (real_inner_self_eq_norm_sq Rφ).symm
  -- The variational identity at `f := φ`, `v := Rφ`.
  have h_var : ⟪Rφ, Rφ⟫_ℝ =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s Rφ, φ⟫_ℝ := by
    rw [hRφ]
    exact tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s φ
      (tensorResolvent (I := I) (M := M) g r s φ)
  -- `TensorH1ComplToTensorL2 (tensorResolvent φ) = tensorResolventL2 φ = μ • φ`.
  have h_l2 : TensorH1ComplToTensorL2 (I := I) (M := M) g r s Rφ =
      i.fst.val • φ := by
    rw [hRφ, ← tensorResolventL2_apply (I := I) (M := M) g r s φ]
    exact tensorResolventL2_eigenbasisVec_eq_unconditional
      (I := I) (M := M) g r s i
  -- Assemble: `‖Rφ‖² = ⟪μ • φ, φ⟫ = μ · ‖φ‖²`.
  rw [h_self, h_var, h_l2, real_inner_smul_left, real_inner_self_eq_norm_sq]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The energy identity in `√`-form (chart-locality-free).** Chart-locality-
free twin of `eigenvectorResolvent_h1Norm_le`: the `H¹` norm of
`eigenvectorResolvent_unconditional g r s i` is bounded by `√μ` times the `L²`
norm of the unconditional eigenbasis vector. -/
theorem eigenvectorResolvent_h1Norm_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖eigenvectorResolvent_unconditional (I := I) (M := M) g r s i‖ ≤
      Real.sqrt i.fst.val *
        ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i‖ := by
  have h_sq := eigenvectorResolvent_h1NormSq_eq_unconditional
    (I := I) (M := M) g r s i
  -- `μ > 0`: it is a resolvent eigenvalue of a unit eigenvector.
  have hμ_pos : 0 < i.fst.val :=
    (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        have h_norm := norm_tensorResolventEigenbasisVec_ofCompact_eq_one
          (I := I) (M := M) g r s i
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)).1
  have hμ_nn : 0 ≤ i.fst.val := le_of_lt hμ_pos
  -- The right-hand side is non-negative.
  have h_rhs_nn :
      0 ≤ Real.sqrt i.fst.val *
        ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  -- Compare squares: `‖Rφ‖² = μ · ‖φ‖² = (√μ · ‖φ‖)²`.
  have h_rhs_sq :
      (Real.sqrt i.fst.val *
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖) ^ 2 =
        i.fst.val *
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hμ_nn]
  have h_le_sq :
      ‖eigenvectorResolvent_unconditional (I := I) (M := M) g r s i‖ ^ 2 ≤
        (Real.sqrt i.fst.val *
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖) ^ 2 := by
    rw [h_rhs_sq]; exact le_of_eq h_sq
  -- From `a² ≤ b²` and `0 ≤ b` conclude `a ≤ b` (here `a = ‖·‖ ≥ 0`).
  exact (abs_le_of_sq_le_sq' h_le_sq h_rhs_nn).2

/-! ## The abstract gradient-energy bound

The covariant gradient extended to the `H¹` completion, `tensorCovGradL2Compl`,
is a continuous linear map of operator norm `≤ 1`. Composing the operator-norm
bound with the energy identity controls the metric `L²` norm of the abstract
covariant gradient of the eigenvector resolvent by the `√μ`-weighted `L²` norm
of the eigenbasis vector. -/

/-- **The abstract gradient-energy bound.** For an eigenbasis index `i` with
nonzero resolvent eigenvalue `μ := i.fst.val`, the metric `L²` norm of the
completion-extended covariant gradient of the eigenvector resolvent
`eigenvectorResolvent g r s h_atlas i` is bounded by `√μ` times the `L²` norm of
the eigenbasis vector `tensorResolventEigenbasisVec h_atlas i`.

The covariant-gradient operator `tensorCovGradL2Compl g r s` has operator norm
`≤ 1`, so its value is bounded by the `H¹` norm of its argument; the energy
identity `eigenvectorResolvent_h1Norm_le` then supplies the `√μ`-weighted
bound. -/
theorem tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)‖ ≤
      Real.sqrt i.fst.val *
        ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  -- The pointwise bound for the completion-extended covariant gradient: its
  -- value at `eigenvectorResolvent …` is bounded by the `H¹` norm of that
  -- argument.
  have h_grad :
      ‖tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)‖ ≤
        ‖eigenvectorResolvent (I := I) (M := M) g r s h_atlas i‖ :=
    tensorCovGradL2Compl_apply_norm_le (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)
  -- Chain with the energy identity `‖eigenvectorResolvent …‖ ≤ √μ · ‖φ‖`.
  exact h_grad.trans
    (eigenvectorResolvent_h1Norm_le (I := I) (M := M) g r s h_atlas i)

/-! ### Chart-locality-free twin of the abstract gradient-energy bound

The covariant-gradient operator-norm bound `tensorCovGradL2Compl_apply_norm_le`
carries no chart-selection hypothesis, so the same chaining reproduces the
gradient-energy bound for the unconditional eigenvector resolvent
`eigenvectorResolvent_unconditional`, with the unconditional energy identity
`eigenvectorResolvent_h1Norm_le_unconditional`. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The abstract gradient-energy bound (chart-locality-free).** Chart-locality-
free twin of `tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le`: for an
eigenbasis index `i` with nonzero resolvent eigenvalue `μ := i.fst.val`, the
metric `L²` norm of the completion-extended covariant gradient of the
unconditional eigenvector resolvent `eigenvectorResolvent_unconditional g r s i`
is bounded by `√μ` times the `L²` norm of the unconditional eigenbasis vector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic
g r s) i`.

The covariant-gradient operator `tensorCovGradL2Compl g r s` has operator norm
`≤ 1` (`tensorCovGradL2Compl_apply_norm_le`, no chart-selection hypothesis), so
its value is bounded by the `H¹` norm of its argument; the unconditional energy
identity `eigenvectorResolvent_h1Norm_le_unconditional` then supplies the
`√μ`-weighted bound. No chart-selection hypothesis. -/
theorem tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)‖ ≤
      Real.sqrt i.fst.val *
        ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i‖ := by
  -- The pointwise bound for the completion-extended covariant gradient: its
  -- value at `eigenvectorResolvent_unconditional …` is bounded by the `H¹` norm
  -- of that argument. The bound carries no chart-selection hypothesis.
  have h_grad :
      ‖tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)‖ ≤
        ‖eigenvectorResolvent_unconditional (I := I) (M := M) g r s i‖ :=
    tensorCovGradL2Compl_apply_norm_le (I := I) (M := M) g r s
      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)
  -- Chain with the unconditional energy identity `‖eigenvectorResolvent …‖ ≤
  -- √μ · ‖φ‖`.
  exact h_grad.trans
    (eigenvectorResolvent_h1Norm_le_unconditional (I := I) (M := M) g r s i)

/-! ## The chart-partial operator-norm bound and the `μ`-power identity

The canonical chart-partial continuous linear map `eigenvectorChartPartialCLM
g r s α P₀ k` controls, by the elementary operator-norm bound `‖T x‖ ≤ ‖T‖ ·
‖x‖`, the chart-partial `L²` norm by the `H¹` norm of its argument. Its operator
norm depends only on the geometric data `g r s α P₀ k`; it is the constant of
the headline. The bound is combined with the energy identity through the scalar
identity `μ⁻¹ · √μ = √(μ⁻¹)`, valid for `μ > 0`. -/

/-- For a positive real `μ`, the rescaled square root satisfies
`μ⁻¹ · √μ = √(μ⁻¹)`. -/
private lemma inv_mul_sqrt_eq_sqrt_inv {μ : ℝ} (hμ : 0 < μ) :
    μ⁻¹ * Real.sqrt μ = Real.sqrt μ⁻¹ := by
  -- `√μ > 0`, hence `√μ ≠ 0` and `μ ≠ 0`.
  have h_sqrt_pos : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have h_sqrt_ne : Real.sqrt μ ≠ 0 := ne_of_gt h_sqrt_pos
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  -- `√μ * √μ = μ`.
  have h_mul_self : Real.sqrt μ * Real.sqrt μ = μ :=
    Real.mul_self_sqrt (le_of_lt hμ)
  -- Rewrite the right-hand side: `√(μ⁻¹) = (√μ)⁻¹`.
  rw [Real.sqrt_inv]
  -- Clear all denominators; the resulting polynomial identity is `√μ * √μ = μ`.
  field_simp
  linarith [h_mul_self]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 800000 in
/-- The chart-partial `L²` norm of the value of `eigenvectorChartPartialCLM
g r s α P₀ k` on an element of the `H¹` completion is bounded by the operator
norm of that map times the `H¹` norm of the argument.

The operator norm `‖eigenvectorChartPartialCLM g r s α P₀ k‖` is a chart-
geometric quantity: it depends only on `g r s α P₀ k`, not on any eigenbasis
index. -/
private lemma eigenvectorChartPartialCLM_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (x : TensorH1Compl g r s) :
    ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k x‖ ≤
      ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ * ‖x‖ :=
  (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k).le_opNorm x

/-! ## The headline chart-local gradient-energy estimate

The weak `k`-th chart partial `eigenvectorChartWeakPartial g r s h_atlas i α P₀
k` is the coercion-to-function of the `Lp` class `eigenvectorChartPartialLp g r s
h_atlas i α P₀ k`, itself `μ⁻¹` times the value of `eigenvectorChartPartialCLM`
on the eigenvector resolvent. The `eLpNorm` over the Euclidean chart target
therefore equals the `Lp` norm of that class; chaining the `Lp` norm-`smul`
identity, the chart-partial operator-norm bound, the energy identity, and the
`μ`-power identity produces the headline. -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
/-- **The chart-local gradient-energy estimate for an eigenvector chart
component.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart
center `α : M`, a component multi-index `P₀`, and a chart-coordinate direction
`k`, there is a chart-geometric constant `C ≥ 0` — uniform over the eigenbasis
index `i` — such that for every eigenbasis index `i` with nonzero resolvent
eigenvalue `μ := i.fst.val`, the `L²` norm over the Euclidean chart target of the
weak `k`-th chart partial `eigenvectorChartWeakPartial g r s h_atlas i α P₀ k` of
the eigenvector chart component is at most `C · √(μ⁻¹)` times the abstract `L²`
norm of the eigenbasis vector `tensorResolventEigenbasisVec h_atlas i`.

The constant `C` is the operator norm of the canonical chart-partial continuous
linear map `eigenvectorChartPartialCLM g r s α P₀ k`; it depends only on the
geometric data `g r s α P₀ k`. The bound is genuine — and not the vacuous
per-`i` ratio — because the universal quantifier `∀ i` lies *inside* the
existential `∃ C`: a single `C` controls the chart partial of *every*
eigenvector simultaneously. The `i`-dependence on the right-hand side is
confined to the explicit `√(μ⁻¹)` factor, which originates from the energy
identity `eigenvectorResolvent_h1Norm_le` (the eigen-equation), not from any
finiteness shortcut. -/
theorem eigenvectorChartWeakPartial_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm (eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i α P₀ k) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            (C * Real.sqrt ((i.fst.val)⁻¹)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- The constant: the operator norm of the canonical chart-partial CLM. It is a
  -- chart-geometric quantity, independent of the eigenbasis index `i`.
  refine ⟨‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖,
    norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k),
    fun i => ?_⟩
  -- `μ > 0`: it is a resolvent eigenvalue of the unit eigenbasis vector.
  have hμ_pos : 0 < i.fst.val :=
    (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
      (by
        intro h_zero
        have h_norm := norm_tensorResolventEigenbasisVec_eq_one
          (I := I) (M := M) g r s h_atlas i
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)).1
  -- `eigenvectorChartWeakPartial` is the coercion-to-function of the `Lp` class
  -- `eigenvectorChartPartialLp`; its `eLpNorm` over the chart target is the `Lp`
  -- norm of that class.
  have h_eLp_eq :
      eLpNorm (eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i α P₀ k) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) =
        eLpNorm ((eigenvectorChartPartialLp (I := I) (M := M)
            g r s h_atlas i α P₀ k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) α) := rfl
  -- The `eLpNorm` of the coercion is finite, so it equals `ENNReal.ofReal` of
  -- the `Lp` norm of the class (`Lp.norm_def`).
  have h_eLp_ne_top :
      eLpNorm ((eigenvectorChartPartialLp (I := I) (M := M)
            g r s h_atlas i α P₀ k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) α) ≠ ⊤ :=
    Lp.eLpNorm_ne_top _
  have h_eLp_ofReal :
      eLpNorm ((eigenvectorChartPartialLp (I := I) (M := M)
            g r s h_atlas i α P₀ k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) α) =
        ENNReal.ofReal
          ‖eigenvectorChartPartialLp (I := I) (M := M)
            g r s h_atlas i α P₀ k‖ := by
    rw [Lp.norm_def (eigenvectorChartPartialLp (I := I) (M := M)
      g r s h_atlas i α P₀ k), ENNReal.ofReal_toReal h_eLp_ne_top]
  -- The `Lp`-norm bound: `‖eigenvectorChartPartialLp‖ ≤ C · √(μ⁻¹) · ‖φ‖`.
  have h_lp_bound :
      ‖eigenvectorChartPartialLp (I := I) (M := M) g r s h_atlas i α P₀ k‖ ≤
        ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
            Real.sqrt (i.fst.val)⁻¹ *
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
    -- `eigenvectorChartPartialLp = μ⁻¹ • eigenvectorChartPartialCLM …
    --   (eigenvectorResolvent …)`.
    rw [eigenvectorChartPartialLp, norm_smul]
    -- `‖μ⁻¹‖ = μ⁻¹` since `μ > 0`.
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμ_pos)]
    -- Chain: the chart-partial operator-norm bound, then the energy identity,
    -- then the `μ`-power identity `μ⁻¹ · √μ = √(μ⁻¹)`.
    calc (i.fst.val)⁻¹ *
            ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)‖
          ≤ (i.fst.val)⁻¹ *
              (‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
                ‖eigenvectorResolvent (I := I) (M := M)
                  g r s h_atlas i‖) :=
            mul_le_mul_of_nonneg_left
              (eigenvectorChartPartialCLM_norm_le (I := I) (M := M)
                g r s α P₀ k
                (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
              (le_of_lt (inv_pos.mpr hμ_pos))
      _ ≤ (i.fst.val)⁻¹ *
            (‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
              (Real.sqrt i.fst.val *
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  h_atlas i‖)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (eigenvectorResolvent_h1Norm_le (I := I) (M := M)
                  g r s h_atlas i)
                (norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M)
                  g r s α P₀ k)))
              (le_of_lt (inv_pos.mpr hμ_pos))
      _ = ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
            ((i.fst.val)⁻¹ * Real.sqrt i.fst.val) *
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
            ring
      _ = ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
            Real.sqrt (i.fst.val)⁻¹ *
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
            rw [inv_mul_sqrt_eq_sqrt_inv hμ_pos]
  -- Lift the real bound to `ℝ≥0∞` and split the product factor.
  have h_factor_nn :
      0 ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
        Real.sqrt (i.fst.val)⁻¹ :=
    mul_nonneg
      (norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M)
        g r s α P₀ k))
      (Real.sqrt_nonneg _)
  calc eLpNorm (eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i α P₀ k) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        = ENNReal.ofReal
            ‖eigenvectorChartPartialLp (I := I) (M := M)
              g r s h_atlas i α P₀ k‖ := by
          rw [h_eLp_eq, h_eLp_ofReal]
    _ ≤ ENNReal.ofReal
          (‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
              Real.sqrt (i.fst.val)⁻¹ *
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :=
          ENNReal.ofReal_le_ofReal h_lp_bound
    _ = ENNReal.ofReal
          (‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
            Real.sqrt (i.fst.val)⁻¹) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
          rw [ENNReal.ofReal_mul h_factor_nn]

/-! ## The headline chart-local gradient-energy estimate (chart-locality-free)

The chart-locality-free twin of `eigenvectorChartWeakPartial_eLpNorm_le`. The
weak `k`-th chart partial `eigenvectorChartWeakPartial_unconditional g r s i α P₀
k` is the coercion-to-function of the `Lp` class
`eigenvectorChartPartialLp_unconditional`, itself `μ⁻¹` times the value of
`eigenvectorChartPartialCLM` on the unconditional eigenvector resolvent. The same
chain — `eLpNorm`–`Lp.norm_def`, the chart-partial operator-norm bound, the
unconditional energy identity, and the `μ`-power identity — produces the
headline. The constant `C` is again `‖eigenvectorChartPartialCLM g r s α P₀ k‖`,
a chart-geometric quantity uniform over `i`, and the only chart-selection
hypothesis is dropped. -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The chart-local gradient-energy estimate for an eigenvector chart
component (chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartWeakPartial_eLpNorm_le`. For a closed Riemannian manifold
`(M, g)`, ranks `(r, s)`, a chart center `α : M`, a component multi-index `P₀`,
and a chart-coordinate direction `k`, there is a chart-geometric constant
`C ≥ 0` — uniform over the eigenbasis index `i` — such that for every eigenbasis
index `i` with nonzero resolvent eigenvalue `μ := i.fst.val`, the `L²` norm over
the Euclidean chart target of the weak `k`-th chart partial
`eigenvectorChartWeakPartial_unconditional g r s i α P₀ k` is at most `C · √(μ⁻¹)`
times the abstract `L²` norm of the unconditional eigenbasis vector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic
g r s) i`. No chart-selection hypothesis. -/
theorem eigenvectorChartWeakPartial_eLpNorm_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      eLpNorm (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
            g r s i α P₀ k) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal
            (C * Real.sqrt ((i.fst.val)⁻¹)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- The constant: the operator norm of the canonical chart-partial CLM. It is a
  -- chart-geometric quantity, independent of the eigenbasis index `i`.
  refine ⟨‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖,
    norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k),
    fun i => ?_⟩
  -- `μ > 0`: it is a resolvent eigenvalue of the unit eigenbasis vector.
  have hμ_pos : 0 < i.fst.val :=
    (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i)
      (by
        intro h_zero
        have h_norm := norm_tensorResolventEigenbasisVec_ofCompact_eq_one
          (I := I) (M := M) g r s i
        rw [h_zero, norm_zero] at h_norm
        exact one_ne_zero h_norm.symm)).1
  -- `eigenvectorChartWeakPartial_unconditional` is the coercion-to-function of
  -- the `Lp` class `eigenvectorChartPartialLp_unconditional`; its `eLpNorm` over
  -- the chart target is the `Lp` norm of that class.
  have h_eLp_eq :
      eLpNorm (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
            g r s i α P₀ k) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) =
        eLpNorm ((eigenvectorChartPartialLp_unconditional (I := I) (M := M)
            g r s i α P₀ k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) α) := rfl
  -- The `eLpNorm` of the coercion is finite, so it equals `ENNReal.ofReal` of
  -- the `Lp` norm of the class (`Lp.norm_def`).
  have h_eLp_ne_top :
      eLpNorm ((eigenvectorChartPartialLp_unconditional (I := I) (M := M)
            g r s i α P₀ k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) α) ≠ ⊤ :=
    Lp.eLpNorm_ne_top _
  have h_eLp_ofReal :
      eLpNorm ((eigenvectorChartPartialLp_unconditional (I := I) (M := M)
            g r s i α P₀ k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) 2 (chartL2Measure (I := I) (M := M) α) =
        ENNReal.ofReal
          ‖eigenvectorChartPartialLp_unconditional (I := I) (M := M)
            g r s i α P₀ k‖ := by
    rw [Lp.norm_def (eigenvectorChartPartialLp_unconditional (I := I) (M := M)
      g r s i α P₀ k), ENNReal.ofReal_toReal h_eLp_ne_top]
  -- The `Lp`-norm bound: `‖eigenvectorChartPartialLp_unconditional‖ ≤
  --   C · √(μ⁻¹) · ‖φ‖`.
  have h_lp_bound :
      ‖eigenvectorChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P₀ k‖ ≤
        ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
            Real.sqrt (i.fst.val)⁻¹ *
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
    -- `eigenvectorChartPartialLp_unconditional = μ⁻¹ • eigenvectorChartPartialCLM
    --   … (eigenvectorResolvent_unconditional …)`.
    rw [eigenvectorChartPartialLp_unconditional, norm_smul]
    -- `‖μ⁻¹‖ = μ⁻¹` since `μ > 0`.
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hμ_pos)]
    -- Chain: the chart-partial operator-norm bound, then the unconditional
    -- energy identity, then the `μ`-power identity `μ⁻¹ · √μ = √(μ⁻¹)`.
    calc (i.fst.val)⁻¹ *
            ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k
              (eigenvectorResolvent_unconditional (I := I) (M := M)
                g r s i)‖
          ≤ (i.fst.val)⁻¹ *
              (‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
                ‖eigenvectorResolvent_unconditional (I := I) (M := M)
                  g r s i‖) :=
            mul_le_mul_of_nonneg_left
              (eigenvectorChartPartialCLM_norm_le (I := I) (M := M)
                g r s α P₀ k
                (eigenvectorResolvent_unconditional (I := I) (M := M)
                  g r s i))
              (le_of_lt (inv_pos.mpr hμ_pos))
      _ ≤ (i.fst.val)⁻¹ *
            (‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
              (Real.sqrt i.fst.val *
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic
                    (I := I) (M := M) g r s) i‖)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (eigenvectorResolvent_h1Norm_le_unconditional (I := I) (M := M)
                  g r s i)
                (norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M)
                  g r s α P₀ k)))
              (le_of_lt (inv_pos.mpr hμ_pos))
      _ = ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
            ((i.fst.val)⁻¹ * Real.sqrt i.fst.val) *
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ := by
            ring
      _ = ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
            Real.sqrt (i.fst.val)⁻¹ *
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ := by
            rw [inv_mul_sqrt_eq_sqrt_inv hμ_pos]
  -- Lift the real bound to `ℝ≥0∞` and split the product factor.
  have h_factor_nn :
      0 ≤ ‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
        Real.sqrt (i.fst.val)⁻¹ :=
    mul_nonneg
      (norm_nonneg (eigenvectorChartPartialCLM (I := I) (M := M)
        g r s α P₀ k))
      (Real.sqrt_nonneg _)
  calc eLpNorm (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
            g r s i α P₀ k) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        = ENNReal.ofReal
            ‖eigenvectorChartPartialLp_unconditional (I := I) (M := M)
              g r s i α P₀ k‖ := by
          rw [h_eLp_eq, h_eLp_ofReal]
    _ ≤ ENNReal.ofReal
          (‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
              Real.sqrt (i.fst.val)⁻¹ *
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖) :=
          ENNReal.ofReal_le_ofReal h_lp_bound
    _ = ENNReal.ofReal
          (‖eigenvectorChartPartialCLM (I := I) (M := M) g r s α P₀ k‖ *
            Real.sqrt (i.fst.val)⁻¹) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ := by
          rw [ENNReal.ofReal_mul h_factor_nn]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
