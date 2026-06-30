import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedAppCcLeibniz
import DifferentialGeometry.Geometry.Connection.TensorNabla.CometricRaiseSlot0CovariantParallelism
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCometricRaise
import DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open TensorRSNabla
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private theorem rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_convolution_recursion
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (A : ℝ) (B : ℕ → ℝ), 0 ≤ A ∧ (∀ m, 0 ≤ B m) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ y v w, g₁.inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (x : M),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 0) x
            ((iteratedCovGrad (I := I) g₀ 1 1 0
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤ A) ∧
        (∀ m : ℕ,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (m + 1)) x
              ((iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
            B m * ∑ k ∈ Finset.range (m + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + ((m - k) + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 ((m - k) + 1) T).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + k) x
                  ((iteratedCovGrad (I := I) g₀ 1 1 k
                    (slotInsertEndoCc (I := I) (M := M) g₀ 0
                      (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)) :=
  sorry

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private theorem rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ y v w, g₁.inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
          C i * ∑ n ∈ Finset.range (i + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  obtain ⟨A, B, hA, hB, hrec⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_convolution_recursion
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => (DifferentialGeometry.Combinatorics.recGridCS A B i).1,
    fun i => (DifferentialGeometry.Combinatorics.recGridCS_nonneg A B hA hB i).1, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  obtain ⟨hbase, hstep⟩ := hrec g₁ T htie hδ_le hδ0 hbound x
  have hmain := DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_convolution_bound
    (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x))
    (fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _)
    (fun i => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x))
    A hA B hB hbase hstep i
  rw [DifferentialGeometry.Combinatorics.antidiagonalTupleGrid] at hmain
  exact hmain

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_slotInsertEndoCc_gInvDiffRaisedEndoField_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ y v w, g₁.inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
          C i * ∑ n ∈ Finset.range (i + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  obtain ⟨C, hC, hbnd⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => (Module.finrank ℝ E : ℝ) * C i,
    fun i => mul_nonneg (Nat.cast_nonneg _) (hC i), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have h2862 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
    (gInvDiffRaisedEndoField (I := I) g₀ g₁) i x
  rw [pow_one] at h2862
  refine le_trans h2862 ?_
  have hchild := hbnd g₁ T htie hδ_le hδ0 hbound i x
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hchild (Nat.cast_nonneg _)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_gInvDiffSlotCoeff_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ y v w, g₁.inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
          C i * ∑ n ∈ Finset.range (i + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  obtain ⟨C, hC, hbnd⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨C, hC, fun g₁ T htie δ hδ_le hδ0 hbound i x => ?_⟩
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g₀ g₁]
  exact hbnd g₁ T htie hδ_le hδ0 hbound i x

end Connection
end Integral
end DifferentialGeometry

end
