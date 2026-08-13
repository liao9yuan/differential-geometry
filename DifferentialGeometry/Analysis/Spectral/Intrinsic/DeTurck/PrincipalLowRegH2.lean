import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalNeumannH2
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.FractionalPower
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IterCovGradHs

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev rank2H4 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

private abbrev rank2H2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev rank4H2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 4 (2 : ℝ)

noncomputable def hessianH2
    (g : SmoothRiemannianMetric I M) :
    rank2H4 (I := I) (M := M) g →L[ℝ]
      rank4H2 (I := I) (M := M) g := by
  let J : rank2H4 (I := I) (M := M) g →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + (2 : ℝ)) :=
    (tensorHs.castEquiv (I := I) (M := M)
      (by norm_num : (4 : ℝ) = (2 : ℝ) + (2 : ℝ))).toContinuousLinearEquiv.toContinuousLinearMap
  exact (iterCovGradHs (I := I) (M := M) g 2 2 2).comp J

noncomputable def traceH2
    (g : SmoothRiemannianMetric I M) :
    rank4H2 (I := I) (M := M) g →L[ℝ]
      rank2H2 (I := I) (M := M) g :=
  appHs (I := I) (M := M) g 4 2 2
    (cometricDoubleTraceField (I := I) g 2)

theorem hessianH2_core
    (g : SmoothRiemannianMetric I M) (U : SmoothCcTensor g 0 2) :
    hessianH2 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
      ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ)
        (iteratedCovGrad (I := I) g 0 2 2 U) := by
  have hcast :
      (ContinuousLinearEquiv.toContinuousLinearMap
        (tensorHs.castEquiv (I := I) (M := M)
          (by norm_num : (4 : ℝ) = (2 : ℝ) + (2 : ℝ))).toContinuousLinearEquiv)
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
        ccTensorToHs (I := I) (M := M) g 2
          ((2 : ℝ) + (2 : ℝ)) U := by
    change
      tensorHs.castEquiv (I := I) (M := M)
          (by norm_num : (4 : ℝ) = (2 : ℝ) + (2 : ℝ))
          (ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) U) =
        ccTensorToHs (I := I) (M := M) g 2
          ((2 : ℝ) + (2 : ℝ)) U
    ext i
    simp only [tensorHs.castEquiv_coeff, ccTensorToHs_coeff]
  rw [hessianH2, ContinuousLinearMap.comp_apply, hcast]
  exact iterCovGradHs_core (I := I) (M := M) g 2 2 2 U

theorem traceH2_core
    (g : SmoothRiemannianMetric I M) (V : SmoothCcTensor g 0 4) :
    traceH2 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ) V) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (appCc (I := I) (M := M) g 4 2
          (cometricDoubleTraceField (I := I) g 2) V) := by
  exact appHs_core (I := I) (M := M) g 4 2 2
    (cometricDoubleTraceField (I := I) g 2) V

noncomputable def lowRegPrincipal
    (g : SmoothRiemannianMetric I M)
    (T : metricH2 (I := I) (M := M) g) :
    rank2H4 (I := I) (M := M) g →L[ℝ]
      rank2H2 (I := I) (M := M) g :=
  (traceH2 (I := I) (M := M) g).comp
    ((invPerturbH2 (I := I) (M := M) g T).comp
      (hessianH2 (I := I) (M := M) g))

theorem lowRegPrincipal_norm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ T : metricH2 (I := I) (M := M) g, ‖T‖ ≤ ρ →
        ‖lowRegPrincipal (I := I) (M := M) g T‖ ≤ C * ‖T‖ := by
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    invPerturbH2_norm (I := I) (M := M) hDim g
  let A := traceH2 (I := I) (M := M) g
  let D := hessianH2 (I := I) (M := M) g
  let C : ℝ := ‖A‖ * Cinv * ‖D‖
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T hT
  have hInv := (hinv T hT).2
  calc
    ‖lowRegPrincipal (I := I) (M := M) g T‖ ≤
        ‖A‖ *
          ‖(invPerturbH2 (I := I) (M := M) g T).comp D‖ := by
      simpa only [lowRegPrincipal, A, D] using
        (A.opNorm_comp_le
          ((invPerturbH2 (I := I) (M := M) g T).comp D))
    _ ≤ ‖A‖ *
          (‖invPerturbH2 (I := I) (M := M) g T‖ * ‖D‖) :=
      mul_le_mul_of_nonneg_left
        ((invPerturbH2 (I := I) (M := M) g T).opNorm_comp_le D)
        (norm_nonneg A)
    _ ≤ ‖A‖ * ((Cinv * ‖T‖) * ‖D‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hInv (norm_nonneg D))
        (norm_nonneg A)
    _ = C * ‖T‖ := by
      dsimp only [C]
      ring

theorem lowRegPrincipal_lip
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ T U : metricH2 (I := I) (M := M) g,
        ‖T‖ ≤ ρ → ‖U‖ ≤ ρ →
          ‖lowRegPrincipal (I := I) (M := M) g T -
              lowRegPrincipal (I := I) (M := M) g U‖ ≤
            C * ‖T - U‖ := by
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    invPerturbH2_lip (I := I) (M := M) hDim g
  let A := traceH2 (I := I) (M := M) g
  let D := hessianH2 (I := I) (M := M) g
  let C : ℝ := ‖A‖ * Cinv * ‖D‖
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro T U hT hU
  have hInv := hinv T U hT hU
  have hdiff :
      lowRegPrincipal (I := I) (M := M) g T -
          lowRegPrincipal (I := I) (M := M) g U =
        A.comp
          ((invPerturbH2 (I := I) (M := M) g T -
            invPerturbH2 (I := I) (M := M) g U).comp D) := by
    apply ContinuousLinearMap.ext
    intro V
    simp only [lowRegPrincipal, A, D, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply]
    rw [map_sub]
  rw [hdiff]
  calc
    _ ≤ ‖A‖ *
          ‖(invPerturbH2 (I := I) (M := M) g T -
            invPerturbH2 (I := I) (M := M) g U).comp D‖ :=
      A.opNorm_comp_le _
    _ ≤ ‖A‖ *
          (‖invPerturbH2 (I := I) (M := M) g T -
              invPerturbH2 (I := I) (M := M) g U‖ * ‖D‖) :=
      mul_le_mul_of_nonneg_left
        ((invPerturbH2 (I := I) (M := M) g T -
          invPerturbH2 (I := I) (M := M) g U).opNorm_comp_le D)
        (norm_nonneg A)
    _ ≤ ‖A‖ * ((Cinv * ‖T - U‖) * ‖D‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hInv (norm_nonneg D))
        (norm_nonneg A)
    _ = C * ‖T - U‖ := by
      dsimp only [C]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
