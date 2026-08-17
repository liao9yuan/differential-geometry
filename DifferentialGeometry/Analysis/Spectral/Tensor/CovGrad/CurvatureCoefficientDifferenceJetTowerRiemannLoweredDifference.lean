import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Lowered

noncomputable section

open Bundle Manifold MeasureTheory DifferentialGeometry.Analysis.Sobolev
  DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] in
theorem koszul_l2_succ
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ T)‖ ^ 2 ≤
      10 * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T‖ ^ 2 := by
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
        10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x) := by
    intro x
    exact CurvatureCoefficientDifferenceJetTower.rfns_iteratedCovGrad_koszulCovecCc_pointwise
      (I := I) (M := M) g₀ T n x
  have hF_int : MeasureTheory.Integrable
      (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g₀ 0 (2 + (n + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g₀ 0 (3 + n)
    (iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ T))
    (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
    hF_int hpt
  refine key.trans ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (I := I) (M := M) g₀ 0 (2 + (n + 1))
    (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)]
  rw [← SmoothCcTensor.norm_def]

end DifferentialGeometry.Analysis.Spectral

end
