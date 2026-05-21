import DifferentialGeometry.Integral.Connection.RawTensorConnLapWtwokTwoZeroSquaredAggregate

/-!
# Linear chart-Sobolev-zero bound on the raw tensor connection Laplacian

For a closed smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, and a smooth
compactly-supported `(r, s)`-tensor section `T`, this file ships the **linear**
chart-Sobolev-zero bound

```
wtwokTwoNorm g 0 (rawTensorConnLapSmooth g r s T)
    ≤ ENNReal.ofReal C · wtwokTwoNorm g 1 T
```

with a non-negative constant `C` independent of `T`.

The proof composes the previously established squared aggregate bound for the
finset sum of `L²` chart-component norms of the raw tensor connection Laplacian,
collapses the tsum defining `wtwokTwoNorm g 0 (raw T)` to a finset sum over the
canonical chart-atlas partition-of-unity finset (the chart components vanish
identically outside this finset since the partition-of-unity weight does), and
takes a square root step through `ENNReal` `pow_le_pow_left_iff`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Vanishing of `tensorChartComp` outside `chartAtlasPOU_finset` -/

/-- For `α` outside the canonical chart-atlas partition-of-unity finset, every
chart component of any smooth compactly-supported `(r, s)`-tensor section
vanishes identically. The partition-of-unity weight is zero everywhere for such
`α`, so the POU-weighted scalar component is the zero function on `M`, whose
chart push-forward is the zero function on the Euclidean ambient space. -/
private lemma tensorChartComp_eq_zero_of_notMem_finset
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx = (fun _ => (0 : ℝ)) := by
  classical
  funext y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · -- On chart target: tensorChartComp = tensorChartComponentPou (...).
    rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy]
    unfold tensorChartComponentPou
    rw [chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα _]
    ring
  · -- Off chart target: tensorChartComp = 0.
    exact tensorChartComp_apply_of_notMem
      (I := I) (M := M) g r s S α Idx Jdx hy

/-! ## Collapse the chart-aggregating tsum to a finset sum -/

/-- The chart-aggregating `tsum` defining `wtwokTwoNorm g 0 (rawTensorConnLapSmooth
g r s T)` collapses to a finset sum over `chartAtlasPOU_finset`. The per-`α`
summand vanishes for `α` outside this finset because each chart component is the
zero function there (the partition-of-unity weight vanishes), and the
`wkpNorm 0 2` of the zero function on any open set is zero. -/
private lemma wtwokTwoNorm_zero_rawTensorConnLap_eq_finset_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g 0
        (rawTensorConnLapSmooth (I := I) g r s T) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) 0 2
              (tensorChartComp (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  rw [wtwokTwoNorm_eq_tsum (I := I) (M := M) g 0
    (rawTensorConnLapSmooth (I := I) g r s T)]
  -- Replace the `2 * 0` inside the `wkpNorm` with `0`.
  -- The chart-aggregating sum is the same as in the goal (definitionally
  -- `2 * 0 = 0`); we use `Nat.mul_zero` to convert.
  rw [show (2 * 0 : ℕ) = 0 from by norm_num]
  -- Apply `tsum_eq_sum` with finset `chartAtlasPOU_finset` and zero hypothesis.
  rw [tsum_eq_sum
    (s := chartAtlasPOU_finset (I := I) (M := M))
    (f := fun α : M =>
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) 0 2
            (tensorChartComp (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α))]
  -- Side condition: the summand vanishes for `α ∉ chartAtlasPOU_finset`.
  intro α hα
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [tensorChartComp_eq_zero_of_notMem_finset
    (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s T)
    hα Idx Jdx]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

/-! ## `wkpNorm 0 2` equals `eLpNorm 2 (volume.restrict ·)` -/

/-- The order-zero `wkpNorm` over an open set equals the corresponding restricted
`eLpNorm`. A specialisation of `wkpNorm_zero` recorded for direct use below. -/
private lemma wkpNorm_zero_eq_eLpNorm
    (u : EuclN → ℝ) (Ω : Set EuclN) :
    wkpNorm (d := Module.finrank ℝ E) 0 2 u Ω =
      eLpNorm u 2 ((volume : Measure EuclN).restrict Ω) :=
  wkpNorm_zero (d := Module.finrank ℝ E) 2 u Ω

/-! ## The linear headline -/

/-- **Linear chart-Sobolev-zero bound on the raw tensor connection Laplacian.**

For a closed smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, and a smooth
compactly-supported `(r, s)`-tensor section `T`, there is a non-negative
constant `C` such that

```
wtwokTwoNorm g 0 (rawTensorConnLapSmooth g r s T)
    ≤ ENNReal.ofReal C · wtwokTwoNorm g 1 T.
```

Strategy:

1. Re-express the LHS as a finset sum over `chartAtlasPOU_finset` of finite
   double sums of `L²` chart-component norms, using
   `wtwokTwoNorm_zero_rawTensorConnLap_eq_finset_sum`.

2. The squared aggregate
   `sq_finset_sum_eLpNorm_two_tensorChartComp_le_wtwokTwoNorm_sq` bounds the
   square of this finset sum by `ENNReal.ofReal C_sq · (wtwokTwoNorm g 1 T)²`
   for some `C_sq ≥ 0`.

3. Setting `C := √C_sq`, we have
   `ENNReal.ofReal C_sq = (ENNReal.ofReal C)²`, so the squared bound becomes
   `(LHS)² ≤ (ENNReal.ofReal C · wtwokTwoNorm g 1 T)²`. By
   `ENNReal.pow_le_pow_left_iff` this is equivalent to
   `LHS ≤ ENNReal.ofReal C · wtwokTwoNorm g 1 T`.
-/
theorem wtwokTwoNorm_zero_rawTensorConnLap_le_wtwokTwoNorm_one
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        wtwokTwoNorm (I := I) (M := M) g 0
            (rawTensorConnLapSmooth (I := I) g r s T) ≤
          ENNReal.ofReal C * wtwokTwoNorm (I := I) (M := M) g 1 T := by
  classical
  obtain ⟨C_sq, hC_sq_nn, hC_sq_bound⟩ :=
    sq_finset_sum_eLpNorm_two_tensorChartComp_le_wtwokTwoNorm_sq
      (I := I) (M := M) h_atlas h_atlas_strong g r s
  refine ⟨Real.sqrt C_sq, Real.sqrt_nonneg _, ?_⟩
  intro T
  -- Notation.
  set C : ℝ := Real.sqrt C_sq with hC_def
  set W₁ : ℝ≥0∞ := wtwokTwoNorm (I := I) (M := M) g 1 T with hW₁_def
  set LHS : ℝ≥0∞ := wtwokTwoNorm (I := I) (M := M) g 0
    (rawTensorConnLapSmooth (I := I) g r s T) with hLHS_def
  -- Step 1: re-express LHS as the finset sum used in the squared aggregate.
  set FS : ℝ≥0∞ :=
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          eLpNorm
            (tensorChartComp (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) with hFS_def
  -- LHS = FS via the tsum-to-finset-sum collapse and `wkpNorm_zero`.
  have hLHS_eq : LHS = FS := by
    rw [hLHS_def, hFS_def]
    rw [wtwokTwoNorm_zero_rawTensorConnLap_eq_finset_sum
      (I := I) (M := M) g r s T]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    refine Finset.sum_congr rfl (fun Idx _ => ?_)
    refine Finset.sum_congr rfl (fun Jdx _ => ?_)
    exact wkpNorm_zero_eq_eLpNorm
      (E := E)
      (tensorChartComp (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α)
  -- Step 2: squared aggregate gives FS² ≤ ofReal C_sq · W₁².
  have h_sq_bound : FS ^ 2 ≤ ENNReal.ofReal C_sq * W₁ ^ 2 := by
    rw [hFS_def, hW₁_def]
    exact hC_sq_bound T
  -- Step 3: rewrite `ofReal C_sq = (ofReal (sqrt C_sq))² = (ofReal C)²`.
  have h_C_sq_eq : C_sq = C ^ 2 := by
    rw [hC_def, sq, Real.mul_self_sqrt hC_sq_nn]
  have h_ofReal_eq : ENNReal.ofReal C_sq = (ENNReal.ofReal C) ^ 2 := by
    rw [h_C_sq_eq, ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
  rw [h_ofReal_eq] at h_sq_bound
  -- ofReal(C)² · W₁² = (ofReal C · W₁)².
  have h_mul_sq : (ENNReal.ofReal C) ^ 2 * W₁ ^ 2 =
      (ENNReal.ofReal C * W₁) ^ 2 := by
    rw [mul_pow]
  rw [h_mul_sq] at h_sq_bound
  -- Step 4: take square root via `ENNReal.pow_le_pow_left_iff`.
  rw [hLHS_eq]
  exact (ENNReal.pow_le_pow_left_iff (a := FS)
    (b := ENNReal.ofReal C * W₁) (n := 2) (by norm_num)).mp h_sq_bound

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.wtwokTwoNorm_zero_rawTensorConnLap_le_wtwokTwoNorm_one
end Sanity
