import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChristoffelL2BoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SectionNormFromTensorInner
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotCorrectionUniformBound
import DifferentialGeometry.Integral.Measure.ChartDensity

/-!
# Unconditional `L^2` bound on the partition-of-unity-weighted Christoffel-atom sum

For a closed Riemannian manifold `(M, g)` admitting a locally constant chart
selection, a chart base point `α : M`, and tensor ranks `(r, s)`, this file
discharges the slot-substitution sup hypothesis `M_F` and the section-fibre
bound hypothesis `K_S` of the companion conditional `L^2` integration
`exists_eLpNorm_chartPou_mul_sqrt_chart_christoffel_correction_le_const_mul_h1Norm`,
specialised to the chart-`α` basis vector field
`X = chartBasisVecFiber α j` for `j : Fin (Module.finrank ℝ E)`. Summing over
the direction index `j` and taking the inner Euclidean square root then gives
the headline `L^2` estimate

```
eLpNorm (fun b => ρ_α(b) * √(∑ j, [(∑ k, ‖input_k j‖²) + (∑ l, ‖output_l j‖²)]))
   2 (riemannianVolumeMeasure g) ≤ ENNReal.ofReal C * ‖S‖₊
```

where the constant `C` depends only on `(g, r, s, α)` and on the locality
hypothesis. The slot-correction sum inside the square root is precisely the
"Christoffel atom" sum entering the gradient bound for chart-frame scalar
components, summed over both slot indices and chart-basis directions.

## Public theorem

* `exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq`
  — unconditional `L^2(volume)` bound on the chart-`α` partition-of-unity-
  weighted Euclidean norm of the direction-and-slot sum of squared
  Christoffel slot corrections.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

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

/-! ## Per-direction `L^2` bound from the conditional headline

We instantiate the conditional headline of `ChristoffelL2BoundFromH1` to the
chart-basis vector field `X = chartBasisVecFiber α j` for a fixed direction
`j`, discharging both `M_F` and `K_S` once and for all from the structural
γ2.5 lemmas. The result is a per-direction `L^2(volume)` bound on the
square root of the slot-correction norm sum, controlled by `‖S‖_{H^1}`. -/

private lemma exists_eLpNorm_chartPou_mul_sqrt_slotCorrection_per_direction
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  ((∑ k : Fin r,
                      ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
                    (∑ l : Fin s,
                      ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  -- Discharge `M_F` for the input slot (γ2.5.A.c).
  obtain ⟨M_F_in, hM_F_in_nn, hM_F_in_le⟩ :=
    chartTensorRSInputSlotCorrection_norm_le_const_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  -- Discharge `M_F` for the output slot (γ2.5.A.c — output side).
  obtain ⟨M_F_out, hM_F_out_nn, hM_F_out_le⟩ :=
    chartTensorRSOutputSlotCorrection_norm_le_const_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  -- Take a common `M_F := max M_F_in M_F_out`.
  set M_F : ℝ := max M_F_in M_F_out with hM_F_def
  have hM_F_nn : 0 ≤ M_F := le_max_of_le_left hM_F_in_nn
  have hM_F_in_le' : M_F_in ≤ M_F := le_max_left _ _
  have hM_F_out_le' : M_F_out ≤ M_F := le_max_right _ _
  -- Repackage the slot-correction bounds with the unified constant `M_F`.
  have hM_F_input :
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ≤
            M_F * ‖S.toSection b‖ := by
    intro S b hb k
    have h_orig :=
      hM_F_in_le (fun b' => S.toSection b') (b := b) hb j k
    have h_factor : M_F_in * ‖S.toSection b‖ ≤ M_F * ‖S.toSection b‖ :=
      mul_le_mul_of_nonneg_right hM_F_in_le' (norm_nonneg _)
    exact h_orig.trans h_factor
  have hM_F_output :
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ≤
            M_F * ‖S.toSection b‖ := by
    intro S b hb l
    have h_orig :=
      hM_F_out_le (fun b' => S.toSection b') (b := b) hb j l
    have h_factor : M_F_out * ‖S.toSection b‖ ≤ M_F * ‖S.toSection b‖ :=
      mul_le_mul_of_nonneg_right hM_F_out_le' (norm_nonneg _)
    exact h_orig.trans h_factor
  -- Discharge `K_S` (γ2.5.B).
  obtain ⟨K_S, hK_S_nn, hK_S_bound⟩ :=
    norm_section_sq_le_const_mul_tensorInnerPointwise_on_pouTsupport
      (I := I) (M := M) h_atlas g r s α
  -- Invoke the conditional headline with `X := chartBasisVecFiber α j`.
  exact
    exists_eLpNorm_chartPou_mul_sqrt_chart_christoffel_correction_le_const_mul_h1Norm
      (I := I) (M := M) g r s α (chartBasisVecFiber (I := I) α j)
      hM_F_nn hM_F_input hM_F_output hK_S_nn hK_S_bound

/-! ## Headline unconditional `L^2` bound on the Christoffel-atom sum

For each chart-basis direction `j : Fin (Module.finrank ℝ E)`, this is a
direct corollary of the per-direction lemma
`exists_eLpNorm_chartPou_mul_sqrt_slotCorrection_per_direction`, which itself
discharges the conditional headline of `ChristoffelL2BoundFromH1` via the
γ2.5.A.c and γ2.5.B uniform bounds. -/

/-- **Unconditional `L²` bound on the partition-of-unity-weighted Christoffel
slot-correction sum.** For a closed Riemannian manifold `(M, g)` admitting a
locally constant chart selection, ranks `(r, s)`, a chart base point `α : M`,
and a chart-basis direction index `j : Fin (Module.finrank ℝ E)`, there is a
non-negative constant `C` (depending only on `(g, r, s, α, j)` and the
locality hypothesis) such that for every smooth compactly-supported `H^1`
tensor section `S : SmoothCcTensorH1 g r s`,

```
eLpNorm
    (fun b => ρ_α(b) * √([∑_k ‖input_k j‖²] + [∑_l ‖output_l j‖²]))
    2 (riemannianVolumeMeasure g) ≤
  ENNReal.ofReal C * ‖S‖₊,
```

where the slot-corrections are evaluated at the chart-basis fibre
`chartBasisVecFiber α j`, the inner sums run over `k : Fin r` and `l : Fin s`,
and `ρ_α` is the chart-atlas partition-of-unity weight at `α`. -/
theorem exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq
    (h_atlas : HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  ((∑ k : Fin r,
                      ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
                    (∑ l : Fin s,
                      ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
  exists_eLpNorm_chartPou_mul_sqrt_slotCorrection_per_direction
    (I := I) (M := M) h_atlas g r s α j

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq

end Sanity
