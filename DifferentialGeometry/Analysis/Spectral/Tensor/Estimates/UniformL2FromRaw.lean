import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.TensorSectionL2BoundByComponents

/-!
# Uniform tensor L2 bounds from chart components

A family whose raw chart-frame components are uniformly bounded on every
active partition-of-unity support is uniformly bounded in the intrinsic
tensor `L2` norm.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Uniform bounds for all raw chart-frame components on the active POU
supports give a uniform intrinsic `L2` bound for a tensor family. -/
theorem l2_bdd_of_raw {ι : Type*}
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : ι → SmoothCcTensor g r s) (B : ℝ) (hB : 0 ≤ B)
    (hraw : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
            |tensorChartComponentRaw (I := I) (M := M)
              g r s (S k) α Idx Jdx b| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ι, ‖S k‖ ≤ C := by
  classical
  let μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let R : ℝ≥0∞ := μ Set.univ ^ ((2 : ℝ≥0∞).toReal⁻¹) * ENNReal.ofReal B
  let A : ℝ := R.toReal
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hR_ne : R ≠ (⊤ : ℝ≥0∞) := by
    dsimp [R]
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ Set.univ))
      ENNReal.ofReal_ne_top
  have hscalar : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι, ∀ b : M,
        ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
        ‖tensorChartComponentScalar (I := I) (M := M)
          g r s (S k) α Idx Jdx b‖ ≤ B := by
    intro α hα k b Idx Jdx
    rw [Real.norm_eq_abs]
    by_cases hb : b ∈ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    · rw [tensorChartComponentScalar_def]
      unfold tensorChartComponentPou
      rw [abs_mul, abs_of_nonneg ((chartAtlasPOU I M).nonneg α b)]
      calc
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b *
              |tensorChartComponentRaw (I := I) (M := M)
                g r s (S k) α Idx Jdx b|
            ≤ 1 * B := mul_le_mul ((chartAtlasPOU I M).le_one α b)
              (hraw α hα k b hb Idx Jdx) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    · have hρ : (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) b = 0 :=
        image_eq_zero_of_notMem_tsupport hb
      simp [tensorChartComponentScalar_def, tensorChartComponentPou, hρ, hB]
  have hcomponent : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ k : ι,
        ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ((eLpNorm (tensorChartComponentScalar (I := I) (M := M)
              g r s (S k) α Idx Jdx) 2 μ).toReal) ^ 2 ≤ A ^ 2 := by
    intro α hα k Idx Jdx
    have hpt : ∀ b : M,
        ‖tensorChartComponentScalar (I := I) (M := M)
          g r s (S k) α Idx Jdx b‖ ≤ B := by
      intro b
      exact hscalar α hα k b Idx Jdx
    have hlp : eLpNorm (tensorChartComponentScalar (I := I) (M := M)
          g r s (S k) α Idx Jdx) 2 μ ≤ R := by
      dsimp [R]
      exact MeasureTheory.eLpNorm_le_of_ae_bound
        (μ := μ) (p := 2) (Filter.Eventually.of_forall hpt)
    have hreal : (eLpNorm (tensorChartComponentScalar (I := I) (M := M)
          g r s (S k) α Idx Jdx) 2 μ).toReal ≤ A := by
      dsimp [A]
      exact ENNReal.toReal_mono hR_ne hlp
    exact (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).2 hreal
  obtain ⟨C₀, hC₀, hglobal⟩ :=
    tensorL2Norm_sq_le_const_mul_sum_componentL2Norm_sq
      (I := I) (M := M) g r s
  let Q : ℝ :=
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∑ _Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ _Jdx : Fin s → Fin (Module.finrank ℝ E), A ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg A
  refine ⟨Real.sqrt (C₀ * Q), Real.sqrt_nonneg _, fun k => ?_⟩
  rw [SmoothCcTensor.norm_def]
  have hnorm : 0 ≤ tensorL2Norm (I := I) (M := M) g r s (S k).toFun := by
    unfold tensorL2Norm
    exact Real.sqrt_nonneg _
  apply (Real.le_sqrt hnorm (mul_nonneg hC₀ hQ)).2
  refine (hglobal (S k)).trans (mul_le_mul_of_nonneg_left ?_ hC₀)
  dsimp [Q]
  refine Finset.sum_le_sum fun α hα => ?_
  refine Finset.sum_le_sum fun Idx _ => ?_
  exact Finset.sum_le_sum fun Jdx _ => hcomponent α hα k Idx Jdx

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
