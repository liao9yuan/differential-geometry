import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl
import DifferentialGeometry.Geometry.LocalChartConsistency
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# `α`-uniform `L²` bound for chart-frame scalar components of tensor sections

For a closed Riemannian manifold `(M, g)` and a smooth compactly-supported
`H¹` tensor section `S : SmoothCcTensorH1 g r s`, this file delivers an
`α`-**uniform** `L²` bound on the chart-frame scalar component
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx`:

  `eLpNorm (tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx) 2 μ
      ≤ ENNReal.ofReal C₀ * ‖S‖₊`

with a single non-negative real constant `C₀` independent of the chart base
point `α : M`, the multi-index pair `(Idx, Jdx)`, and the section `S`.

## Strategy

The per-`α` headline `tensorChartComponentScalar_eLpNorm_le_uniform`
(`ComponentL2BoundUniform.lean`) supplies, for each `α : M`, a non-negative
constant `C(α)` such that the `L²` norm of the scalar component is bounded
by `ENNReal.ofReal C(α) · ENNReal.ofReal (tensorL2Norm g r s S.toFun)`,
uniformly in `(S, Idx, Jdx)`.

To upgrade to an `α`-uniform constant, we exploit two ingredients:

1. **Compactness + local finiteness**: the chart-atlas partition of unity
   `chartAtlasPOU I M : SmoothPartitionOfUnity M I M univ` is locally
   finite, so on a compact manifold only finitely many index points
   `α : M` have non-empty `support(POU_α)`. The set of "active" centres
   is a `Finset M`.

2. **Vanishing on inactive centres**: when `support(POU_α) = ∅`, the
   partition-of-unity weight `POU_α : M → ℝ` is identically zero, hence
   the POU-weighted scalar component
   `tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx = POU_α · raw`
   vanishes identically, and its `L²` norm is `0`.

Summing the per-`α` constants `C(α)` over the (finite) active set gives a
single non-negative constant `C_total` that dominates each `C(α)`. Using the
L²–H¹ comparison `SmoothCcTensorH1.l2Norm_le_h1Norm` to relate
`tensorL2Norm S.toCcTensor.toFun` to the H¹ norm `‖S‖`, we obtain the
desired `α`-uniform bound `ENNReal.ofReal C_total · ‖S‖₊`.

## Public theorem

* `tensorChartComponentScalar_eLpNorm_le` — the headline
  `α`-uniform `L²` bound on the chart-frame scalar component, for a
  smooth compactly-supported `H¹` tensor section, on a closed Riemannian
  manifold (assuming `[CompactSpace M]` for the finite-cover argument).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Finitely many `α : M` have non-empty `support(POU_α)`

Local finiteness of the chart-atlas partition of unity, combined with
compactness of `M`, ensures the set of "active" partition-of-unity centres
is finite. -/

/-- On a compact manifold, only finitely many partition-of-unity centres
have non-empty support. We package the set of such centres as a `Finset M`. -/
noncomputable def chartAtlasPOU_activeFinset
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] : Finset M :=
  ((chartAtlasPOU I M).locallyFinite.finite_nonempty_of_compact).toFinset

/-- An index `α : M` belongs to the active finset iff its partition-of-unity
support is non-empty. -/
lemma mem_chartAtlasPOU_activeFinset_iff (α : M) :
    α ∈ chartAtlasPOU_activeFinset I M ↔
      (Function.support (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).Nonempty := by
  classical
  unfold chartAtlasPOU_activeFinset
  exact Set.Finite.mem_toFinset _

/-- If `α : M` is NOT in the active finset, then `POU_α` is identically zero. -/
lemma chartAtlasPOU_eq_zero_of_notMem_activeFinset
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M) :
    ∀ x : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := by
  classical
  intro x
  -- Outside the active set, the support is empty.
  have h_empty :
      ¬ (Function.support (fun y : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y)).Nonempty := by
    intro h
    exact hα ((mem_chartAtlasPOU_activeFinset_iff (I := I) (M := M) α).mpr h)
  rw [Set.not_nonempty_iff_eq_empty, Function.support_eq_empty_iff] at h_empty
  have := congrFun h_empty x
  simpa using this

/-! ## The scalar component vanishes when `POU_α` vanishes

The POU-weighted scalar component is the product of `POU_α` and the raw
chart-frame scalar, so it vanishes pointwise as soon as `POU_α` does. -/

lemma tensorChartComponentScalar_eq_zero_of_pou_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (h_zero : ∀ x : M, ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentScalar (I := I) (M := M)
      g r s S α Idx Jdx = 0 := by
  classical
  funext x
  -- Unfold to `tensorChartComponentPou` = `POU_α(x) * raw(x)`.
  change (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x *
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x =
    (0 : M → ℝ) x
  rw [h_zero x, zero_mul]; rfl

/-- For an inactive centre `α`, the `eLpNorm` of the scalar component is `0`. -/
private lemma eLpNorm_tensorChartComponentScalar_eq_zero_of_inactive
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  rw [h_scalar_zero]
  exact eLpNorm_zero

/-! ## Per-`α` constants and their sum over the active finset

We package the per-`α` constants (one for each `α : M`) and sum them over
the (finite) active set, giving a single non-negative constant that
dominates each per-`α` constant on the active set. -/

/-- The per-`α` constant from the per-`α` headline, packaged as a function
`M → ℝ` via `Classical.choose`. -/
private noncomputable def perAlphaConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) : ℝ :=
  Classical.choose (tensorChartComponentScalar_eLpNorm_le_uniform
    (I := I) (M := M) g r s α)

/-- The per-`α` constant is non-negative. -/
private lemma perAlphaConstant_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    0 ≤ perAlphaConstant (I := I) (M := M) g r s α :=
  (Classical.choose_spec (tensorChartComponentScalar_eLpNorm_le_uniform
    (I := I) (M := M) g r s α)).1

/-- The per-`α` headline bound, expressed using `perAlphaConstant`. -/
private lemma perAlphaConstant_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) *
        ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toFun) :=
  (Classical.choose_spec (tensorChartComponentScalar_eLpNorm_le_uniform
    (I := I) (M := M) g r s α)).2 S Idx Jdx

/-- Sum of the per-`α` constants over the active finset. This is a single
non-negative real, independent of `α` (and of `(S, Idx, Jdx)`), that
dominates each per-`α` constant for `α` in the active finset. -/
private noncomputable def totalActiveConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  ∑ α ∈ chartAtlasPOU_activeFinset I M,
    perAlphaConstant (I := I) (M := M) g r s α

private lemma totalActiveConstant_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActiveConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveConstant
  exact Finset.sum_nonneg (fun α _ =>
    perAlphaConstant_nonneg (I := I) (M := M) g r s α)

/-- For each active centre `α`, its per-`α` constant is dominated by the
total sum over the active finset. -/
private lemma perAlphaConstant_le_totalActiveConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {α : M}
    (hα : α ∈ chartAtlasPOU_activeFinset I M) :
    perAlphaConstant (I := I) (M := M) g r s α ≤
      totalActiveConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveConstant
  have h_split :
      ∑ β ∈ chartAtlasPOU_activeFinset I M,
        perAlphaConstant (I := I) (M := M) g r s β =
        perAlphaConstant (I := I) (M := M) g r s α +
        ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
          perAlphaConstant (I := I) (M := M) g r s β := by
    rw [← Finset.sum_erase_add _ _ hα, add_comm]
  rw [h_split]
  have h_rest_nn :
      0 ≤ ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
            perAlphaConstant (I := I) (M := M) g r s β :=
    Finset.sum_nonneg (fun β _ =>
      perAlphaConstant_nonneg (I := I) (M := M) g r s β)
  linarith

/-! ## `α`-uniform bound on `SmoothCcTensor`

The intermediate `α`-uniform bound, stated for `SmoothCcTensor`, using
`tensorL2Norm` on the right-hand side. -/

private theorem tensorChartComponentScalar_eLpNorm_le_smoothCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (S : SmoothCcTensor g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C₀ *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  refine ⟨totalActiveConstant (I := I) (M := M) g r s,
    totalActiveConstant_nonneg (I := I) (M := M) g r s, ?_⟩
  intro S α Idx Jdx
  -- Split on whether `α` is active.
  by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
  · -- Active: chain through per-`α` bound and `perAlphaConstant ≤ totalActiveConstant`.
    have h_per :
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) :=
      perAlphaConstant_bound (I := I) (M := M) g r s α S Idx Jdx
    have h_const_le :
        ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) ≤
          ENNReal.ofReal (totalActiveConstant (I := I) (M := M) g r s) :=
      ENNReal.ofReal_le_ofReal
        (perAlphaConstant_le_totalActiveConstant
          (I := I) (M := M) g r s hα)
    have h_envelope_le :
        ENNReal.ofReal (perAlphaConstant (I := I) (M := M) g r s α) *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) ≤
          ENNReal.ofReal (totalActiveConstant (I := I) (M := M) g r s) *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) :=
      mul_le_mul_of_nonneg_right h_const_le (by exact zero_le _)
    exact h_per.trans h_envelope_le
  · -- Inactive: scalar component is identically zero, so eLpNorm = 0.
    rw [eLpNorm_tensorChartComponentScalar_eq_zero_of_inactive
      (I := I) (M := M) g r s hα S Idx Jdx]
    exact zero_le _

/-! ## Conversion of the right-hand side to `‖S‖₊` for `SmoothCcTensorH1`

For `S : SmoothCcTensorH1 g r s`, the L² norm `tensorL2Norm g r s S.toFun`
equals the L² seminorm `‖S.toCcTensor‖`, which is bounded by the H¹ norm
`‖S‖`. We use this to convert the bound to `ENNReal.ofReal C₀ * ‖S‖₊`. -/

private lemma tensorL2Norm_eq_norm_toCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
      ‖S.toCcTensor‖ := by
  -- Both sides equal `Real.sqrt (tensorL2Inner ...)`.
  have h_sq := SmoothCcTensor.norm_sq_eq_inner_self
    (I := I) (M := M) (g := g) (r := r) (s := s) S.toCcTensor
  -- `‖S.toCcTensor‖² = tensorL2Inner g r s S.toCcTensor.toFun S.toCcTensor.toFun`.
  have h_l2_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
        S.toCcTensor.toFun S.toCcTensor.toFun := by
    unfold tensorL2Inner
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have h_norm_nn : 0 ≤ ‖S.toCcTensor‖ := norm_nonneg _
  -- Compute `tensorL2Norm` and `‖S.toCcTensor‖`.
  have h_lhs :
      tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
        Real.sqrt (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := rfl
  rw [h_lhs]
  -- `‖S.toCcTensor‖ = Real.sqrt (tensorL2Inner ...)`.
  have h_rhs :
      ‖S.toCcTensor‖ = Real.sqrt
        (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := by
    rw [← Real.sqrt_sq h_norm_nn, h_sq]
  rw [h_rhs]

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

private lemma ofReal_tensorL2Norm_le_norm_ennreal
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ENNReal.ofReal
        (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
      (‖S‖₊ : ℝ≥0∞) := by
  rw [tensorL2Norm_eq_norm_toCcTensor (I := I) (M := M) g r s S]
  -- ‖S.toCcTensor‖ ≤ ‖S‖.
  have h_l2_le_h1 :
      ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  rw [coe_nnnorm_eq_ofReal_norm S]
  exact ENNReal.ofReal_le_ofReal h_l2_le_h1

/-! ## Headline `α`-uniform `L²` bound on `SmoothCcTensorH1` -/

/-- **Headline theorem (α-uniform L² bound for chart-frame scalar
components).** For a closed Riemannian manifold `(M, g)` with locally
constant chart selection and ranks `(r, s)`, there exists a single
non-negative real constant `C₀` such that for every smooth
compactly-supported `H¹` tensor section `S : SmoothCcTensorH1 g r s`,
every chart point `α : M`, and every multi-index pair `(Idx, Jdx)`, the
`L²` norm of the chart-frame scalar component
`tensorChartComponentScalar g r s S.toCcTensor α Idx Jdx` is bounded by
`ENNReal.ofReal C₀ · ‖S‖₊`.

The constant `C₀` is independent of `α`, `(Idx, Jdx)`, and `S`. -/
theorem tensorChartComponentScalar_eLpNorm_le
    (_h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C₀, hC₀_nn, h_smoothCc⟩ :=
    tensorChartComponentScalar_eLpNorm_le_smoothCcTensor
      (I := I) (M := M) g r s
  refine ⟨C₀, hC₀_nn, ?_⟩
  intro S α Idx Jdx
  have h_smoothCc' :
      eLpNorm (tensorChartComponentScalar (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C₀ *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s
              S.toCcTensor.toFun) :=
    h_smoothCc S.toCcTensor α Idx Jdx
  have h_rhs_le :
      ENNReal.ofReal C₀ *
        ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
        ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) :=
    mul_le_mul_of_nonneg_left
      (ofReal_tensorL2Norm_le_norm_ennreal (I := I) (M := M) g r s S)
      (by exact zero_le _)
  exact h_smoothCc'.trans h_rhs_le

/-! ## Functional packaging: `∀ S, ∃ C₀, ...` is implied by `∃ C₀, ∀ S, ...`. -/

/-- Functional packaging of the headline `α`-uniform bound. -/
theorem tensorChartComponentScalar_eLpNorm_le_forall
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) :=
  tensorChartComponentScalar_eLpNorm_le
    (I := I) (M := M) h_atlas g r s

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le_forall

end Sanity
