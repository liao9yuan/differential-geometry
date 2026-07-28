import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H4Principal
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense

/-!
# Completed second-derivative tensor actions

This file completes the smooth-core action `U ↦ Φ(∇²U)` from spectral `H4`
to spectral `H2`.  In dimension three its operator norm is controlled by the
intrinsic `H2` jet of the mixed-tensor coefficient.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private noncomputable def appD2CcLin
    (g : SmoothRiemannianMetric I M) (s c : ℕ)
    (Φ : SmoothCcTensor g (s + 2) c) :
    SmoothCcTensor g 0 s →ₗ[ℝ] SmoothCcTensor g 0 c where
  toFun := fun U =>
    appCc (I := I) (M := M) g (s + 2) c Φ
      (iteratedCovGrad (I := I) g 0 s 2 U)
  map_add' := fun U V => by
    rw [iteratedCovGrad_add, appCc_add_right]
  map_smul' := fun a U => by
    simp only [RingHom.id_apply, iteratedCovGrad_smul, appCc_smul_right]

/-- A fixed smooth mixed-tensor coefficient acting on a second covariant
derivative, completed from spectral `H4` to spectral `H2`. -/
noncomputable def appD2Hs
    (g : SmoothRiemannianMetric I M) (s c : ℕ)
    (Φ : SmoothCcTensor g (s + 2) c) :
    tensorHs (I := I) (M := M) g 0 s (4 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 c (2 : ℝ) :=
  ((ccToHsLin (I := I) (M := M) g c (2 : ℝ)).comp
      (appD2CcLin (I := I) (M := M) g s c Φ)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g s (4 : ℝ))

/-- In dimension three, the norm of the completed second-derivative action is
linear in an intrinsic `H2` coefficient-jet envelope. -/
theorem appD2Hs_norm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g (s + 2) c) (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g (s + 2) c j Φ‖ ^ 2) ≤ A ^ 2 →
        ‖appD2Hs (I := I) (M := M) g s c Φ‖ ≤ C * A := by
  obtain ⟨C, hC, happ⟩ :=
    appCc_h2_h4_h2 (I := I) (M := M) hDim g s c
  refine ⟨C, hC, ?_⟩
  intro Φ A hA hΦ
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g s (4 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g s (by positivity)
  unfold appD2Hs
  apply LinearMap.opNorm_extendOfNorm_le hdense (mul_nonneg hC hA)
  intro U
  change
    ‖ccTensorToHs (I := I) (M := M) g c (2 : ℝ)
        (appCc (I := I) (M := M) g (s + 2) c Φ
          (iteratedCovGrad (I := I) g 0 s 2 U))‖ ≤
      (C * A) *
        ‖ccTensorToHs (I := I) (M := M) g s (4 : ℝ) U‖
  simpa only [mul_assoc] using happ Φ U A hA hΦ

/-- The completed second-derivative action agrees with its geometric
smooth-core formula. -/
theorem appD2Hs_core
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s c : ℕ)
    (Φ : SmoothCcTensor g (s + 2) c) (U : SmoothCcTensor g 0 s) :
    appD2Hs (I := I) (M := M) g s c Φ
        (ccTensorToHs (I := I) (M := M) g s (4 : ℝ) U) =
      ccTensorToHs (I := I) (M := M) g c (2 : ℝ)
        (appCc (I := I) (M := M) g (s + 2) c Φ
          (iteratedCovGrad (I := I) g 0 s 2 U)) := by
  let A : ℝ := Real.sqrt
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (s + 2) c j Φ‖ ^ 2)
  have hsum : 0 ≤
      ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 2) c j Φ‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hΦ :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 2) c j Φ‖ ^ 2) ≤ A ^ 2 := by
    rw [show A ^ 2 =
      ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 2) c j Φ‖ ^ 2 by
      simp only [A, Real.sq_sqrt hsum]]
  obtain ⟨C, _, happ⟩ :=
    appCc_h2_h4_h2 (I := I) (M := M) hDim g s c
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g s (4 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g s (by positivity)
  change
    (((ccToHsLin (I := I) (M := M) g c (2 : ℝ)).comp
        (appD2CcLin (I := I) (M := M) g s c Φ)).extendOfNorm
      (ccToHsLin (I := I) (M := M) g s (4 : ℝ)))
        ((ccToHsLin (I := I) (M := M) g s (4 : ℝ)) U) =
      ((ccToHsLin (I := I) (M := M) g c (2 : ℝ)).comp
        (appD2CcLin (I := I) (M := M) g s c Φ)) U
  apply LinearMap.extendOfNorm_eq hdense
  refine ⟨C * A, ?_⟩
  intro V
  change
    ‖ccTensorToHs (I := I) (M := M) g c (2 : ℝ)
        (appCc (I := I) (M := M) g (s + 2) c Φ
          (iteratedCovGrad (I := I) g 0 s 2 V))‖ ≤
      (C * A) *
        ‖ccTensorToHs (I := I) (M := M) g s (4 : ℝ) V‖
  simpa only [mul_assoc] using happ Φ V A hA hΦ

end Connection
end Integral
end DifferentialGeometry

end
