import DifferentialGeometry.Integral.Connection.RawTensorConnLapL2WtwokTwoBound

/-!
# Iterated raw tensor connection Laplacian and its L² bound at the first step

This file packages the iteration of the raw tensor connection Laplacian on
a smooth compactly-supported `(r, s)`-tensor section, together with the L²
bound for the single-step iterate (which is the bundled form of the
order-zero chart-Sobolev L² bound for `rawTensorConnLap`).

## Main definitions

* `rawTensorConnLapSmooth g r s T` — the bundled `SmoothCcTensor → SmoothCcTensor`
  packaging of `rawTensorConnLap`, using its unconditional smoothness.
* `rawTensorConnLapIter g r s k T` — the `k`-fold composition of
  `rawTensorConnLapSmooth` applied to `T`.

## Main results

* `rawTensorConnLapIter_zero` — the zero-th iterate is the input.
* `rawTensorConnLapIter_succ` — the `(k+1)`-th iterate equals the one-step
  bundled connection Laplacian of the `k`-th iterate.
* `rawTensorConnLapSmooth_toSection_apply` — the underlying section value at
  `x` agrees with `rawTensorConnLap`.
* `rawTensorConnLapIter_L2NormSq_le_wtwokTwoNorm_sq_one` — for `k = 1`, the
  `L²` norm squared of the iterate is bounded by a non-negative constant
  times `(wtwokTwoNorm g 1 T)²` (the bundled form of the chart-Sobolev L²
  bound).

The general-`k` headline `rawTensorConnLapIter_L2NormSq_le_wtwokTwoNorm_sq`
requires a higher-order chart-Sobolev bound asserting that, for each `m ≥ 0`,
`wtwokTwoNorm g m (rawTensorConnLapSmooth g r s T) ≤ K_m · wtwokTwoNorm g (m+1) T`.
That higher-order extension is not built in this file. The `k = 0` and
`k = 1` headlines below are unconditional. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

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

/-! ## Bundled `SmoothCcTensor → SmoothCcTensor` raw connection Laplacian -/

/-- **Bundled raw connection Laplacian on `SmoothCcTensor`.** Packages
`rawTensorConnLap` as a function `SmoothCcTensor g r s → SmoothCcTensor g r s`,
relying on the unconditional smoothness witness
`rawTensorConnLap_contMDiff`. -/
noncomputable def rawTensorConnLapSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor g r s :=
  tensorConnLaplacian_of_contMDiff (I := I) g r s T
    (rawTensorConnLap_contMDiff (I := I) g r s (fun z : M => T.toSection z)
      T.toSection.contMDiff_toFun)

/-- The underlying section of `rawTensorConnLapSmooth` agrees pointwise with
`rawTensorConnLap`. -/
@[simp] lemma rawTensorConnLapSmooth_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (x : M) :
    (rawTensorConnLapSmooth (I := I) g r s T).toSection x =
      rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := by
  unfold rawTensorConnLapSmooth
  exact tensorConnLaplacian_of_contMDiff_toFun (I := I) g r s T _ x

/-! ## The `k`-fold iterate of `rawTensorConnLapSmooth` -/

/-- **`k`-fold iterate of the bundled raw connection Laplacian.** Defined by
recursion on `k`: `0` ↦ identity; `(k+1)` ↦ apply `rawTensorConnLapSmooth`
once to the `k`-th iterate. -/
noncomputable def rawTensorConnLapIter
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ℕ → SmoothCcTensor g r s → SmoothCcTensor g r s
  | 0,     T => T
  | k + 1, T => rawTensorConnLapSmooth (I := I) g r s
                  (rawTensorConnLapIter g r s k T)

/-- The zero-th iterate is the input. -/
@[simp] theorem rawTensorConnLapIter_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s 0 T = T := rfl

/-- The `(k+1)`-th iterate equals the one-step bundled connection Laplacian
applied to the `k`-th iterate. -/
@[simp] theorem rawTensorConnLapIter_succ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s (k + 1) T =
      rawTensorConnLapSmooth (I := I) g r s
        (rawTensorConnLapIter (I := I) g r s k T) := rfl

/-- The first iterate is `rawTensorConnLapSmooth` applied to the input. -/
lemma rawTensorConnLapIter_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    rawTensorConnLapIter (I := I) g r s 1 T =
      rawTensorConnLapSmooth (I := I) g r s T := rfl

-- The k = 0 bound is non-trivial in general (it asserts that the L² norm of
-- `T` is controlled by `wtwokTwoNorm g 0 T`). We do not develop this lemma
-- here; the k = 1 case below is the one that follows directly from the
-- existing chart-Sobolev L² bound on `rawTensorConnLap`.

/-! ## Step case `k = 1`: direct application of the chart-Sobolev L² bound
on `rawTensorConnLap`. -/

/-- **L² bound on the first iterate.** For `k = 1`, the iterate is
`rawTensorConnLapSmooth g r s T`, whose underlying section value is
`rawTensorConnLap g r s T`. The chart-Sobolev L² bound
`rawTensorConnLap_L2NormSq_le_wtwokTwoNorm_sq` then gives the headline.

The constant `C` is non-negative; it depends on the metric `g`, the chart
atlas (via the locality hypotheses), and the ranks `(r, s)`. -/
theorem rawTensorConnLapIter_L2NormSq_le_wtwokTwoNorm_sq_one
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (h_atlas_strong :
        DifferentialGeometry.Geometry.HasChartSourceConsistentChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s),
        (letI : MeasurableSpace M := borel M
         haveI : BorelSpace M := ⟨rfl⟩
         Measurable (fun x : M =>
            ‖(rawTensorConnLapIter (I := I) g r s 1 T).toSection x‖ ^ 2)) →
        ∫⁻ x,
            (‖(rawTensorConnLapIter (I := I) g r s 1 T).toSection x‖ₑ
                : ℝ≥0∞) ^ 2
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            (wtwokTwoNorm (I := I) (M := M) g 1 T) ^ 2 := by
  classical
  -- Invoke the chart-Sobolev L² bound on `rawTensorConnLap`.
  obtain ⟨C, hC_nn, hbound⟩ :=
    rawTensorConnLap_L2NormSq_le_wtwokTwoNorm_sq (I := I) (M := M)
      h_atlas h_atlas_strong g r s
  refine ⟨C, hC_nn, ?_⟩
  intro T hmeas
  -- Rewrite the iterate as `rawTensorConnLapSmooth` and then unfold its
  -- underlying section to `rawTensorConnLap`.
  have h_iter_section : ∀ x : M,
      (rawTensorConnLapIter (I := I) g r s 1 T).toSection x =
        rawTensorConnLap (I := I) g r s
          (fun z : M => T.toSection z) x := by
    intro x
    rw [rawTensorConnLapIter_one]
    exact rawTensorConnLapSmooth_toSection_apply (I := I) g r s T x
  -- Equality of the squared-norm integrand functions on `M`.
  have h_fun_eq :
      (fun x : M => (‖(rawTensorConnLapIter (I := I) g r s 1 T).toSection x‖ₑ
            : ℝ≥0∞) ^ 2) =
      (fun x : M => (‖rawTensorConnLap (I := I) g r s
            (fun z : M => T.toSection z) x‖ₑ : ℝ≥0∞) ^ 2) := by
    funext x
    rw [h_iter_section x]
  -- Same for the squared `‖·‖` measurability hypothesis input.
  have h_meas_eq :
      (fun x : M =>
          ‖(rawTensorConnLapIter (I := I) g r s 1 T).toSection x‖ ^ 2) =
      (fun x : M =>
          ‖rawTensorConnLap (I := I) g r s
            (fun z : M => T.toSection z) x‖ ^ 2) := by
    funext x
    rw [h_iter_section x]
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  have hmeas' :
      Measurable (fun x : M =>
          ‖rawTensorConnLap (I := I) g r s
            (fun z : M => T.toSection z) x‖ ^ 2) := by
    rw [← h_meas_eq]; exact hmeas
  have h_integral_eq :
      ∫⁻ x,
          (‖(rawTensorConnLapIter (I := I) g r s 1 T).toSection x‖ₑ : ℝ≥0∞) ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ x,
          (‖rawTensorConnLap (I := I) g r s
              (fun z : M => T.toSection z) x‖ₑ : ℝ≥0∞) ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine lintegral_congr ?_
    intro x
    rw [h_iter_section x]
  rw [h_integral_eq]
  exact hbound T hmeas'

end Connection
end Integral
end DifferentialGeometry

end

section Sanity
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLapIter_zero
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLapIter_succ
#print axioms
  DifferentialGeometry.Integral.Connection.rawTensorConnLapIter_L2NormSq_le_wtwokTwoNorm_sq_one
end Sanity
