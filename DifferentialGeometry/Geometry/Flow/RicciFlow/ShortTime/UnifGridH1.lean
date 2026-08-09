import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifGridH2

/-!
# Class-first uniform H1 grid summation

This module integrates a pointwise order-one tensor estimate whose order-`i`
window reaches perturbation derivatives through order `i + 1`.  In dimension
three, the resulting coefficient is chosen before the class metric varies and
uses only the metric's first two background-covariant jets.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem grid_h1_low
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (P : SmoothCcTensor g 0 2)
    (K C : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, k ≤ 2 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K k)
    (hC : ∀ i, 0 ≤ C i)
    (Φ : SmoothCcTensor g r s)
    (hΦ : ∀ (i : ℕ), i < 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 2),
          lowJetGrid (I := I) (M := M) g P k x) :
    (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤
      ∑ i ∈ Finset.range 2,
        C i * ∑ k ∈ Finset.range (i + 2), K k := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  have hi2 : i < 2 := Finset.mem_range.mp hi
  have hsumInt : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 2),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply MeasureTheory.integrable_finset_sum
    intro k hk
    exact (hgrid k (by have := Finset.mem_range.mp hk; omega)).1
  have hscaled : MeasureTheory.Integrable
      (fun x => C i * ∑ k ∈ Finset.range (i + 2),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hsumInt.const_mul (C i)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g r (s + i)
    (iteratedCovGrad (I := I) g r s i Φ)
    (fun x => C i * ∑ k ∈ Finset.range (i + 2),
      lowJetGrid (I := I) (M := M) g P k x)
    hscaled (hΦ i hi2)
  refine hnorm.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (hC i)
  rw [MeasureTheory.integral_finset_sum _
    (fun k hk => (hgrid k (by have := Finset.mem_range.mp hk; omega)).1)]
  exact Finset.sum_le_sum fun k hk =>
    (hgrid k (by have := Finset.mem_range.mp hk; omega)).2

/-- **Dimension-three class-first low-window `H1` estimate.**

For a pointwise order-one coefficient grid whose order-`i` window reaches
perturbation derivatives through order `i + 1`, one nonnegative coefficient is
chosen before the class metric and perturbation vary.  Only the class metric's
first two background-covariant jets enter the estimate. -/
theorem h1_low_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {r s : ℕ} (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (P : SmoothCcTensor g 0 2) (Φ : SmoothCcTensor g r s)
          (R : ℝ), 0 ≤ R →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          (∀ (i : ℕ), i < 2 → ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
                ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
              C i * ∑ k ∈ Finset.range (i + 2),
                lowJetGrid (I := I) (M := M) g P k x) →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤ (B R) ^ 2 := by
  classical
  let K : ℝ → ℕ → ℝ := fun R k ↦
    DifferentialGeometry.PDE.RicciFlow.h2GridC
      (E := E) (I := I) (M := M) gBase Λ R k
  let Q : ℝ → ℝ := fun R ↦ ∑ i ∈ Finset.range 2,
    C i * ∑ k ∈ Finset.range (i + 2), K R k
  let B : ℝ → ℝ := fun R ↦ Real.sqrt (Q R)
  have hK : ∀ R : ℝ, 0 ≤ R → ∀ k, 0 ≤ K R k := by
    intro R _ k
    simpa only [K] using
      (DifferentialGeometry.PDE.RicciFlow.h2_grid_nonneg
        (E := E) (I := I) (M := M) gBase Λ R k)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC i)
      (Finset.sum_nonneg fun k _ ↦ hK R hR k)
  refine ⟨B, fun R _ ↦ Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet1 hjet2 P Φ R hR hP hΦ
  have hgrid := DifferentialGeometry.PDE.RicciFlow.h2_grid_unif
    (E := E) (I := I) (M := M) hDim gBase hΛ
    g hEq hjet1 hjet2 P R hR hP
  have hgr : ∀ k : ℕ, k ≤ 2 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K R k := by
    intro k hk
    simpa only [lowJetGrid, K] using hgrid k hk
  have hle := grid_h1_low (I := I) (M := M) g P (K R) C
    hgr hC Φ hΦ
  change _ ≤ (B R) ^ 2
  rw [show (B R) ^ 2 = Q R by
    simp only [B, Real.sq_sqrt (hQ R hR)]]
  exact hle

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
