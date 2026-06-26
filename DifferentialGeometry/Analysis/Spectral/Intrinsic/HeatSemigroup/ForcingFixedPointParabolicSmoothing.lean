import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SmallTimeSmoothness
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ParabolicInteriorSmoothing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem deTurckForcing_solFieldMass_forcingMass_couple
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (d : ℝ)
    (hsol : Summable (solFieldMass (I := I) (M := M) (a := (a : ℝ)) hT.le gforce (d + 1))) :
    Summable (forcingMass (I := I) (M := M) (a := (a : ℝ)) gforce d) :=
  sorry

theorem deTurckForcing_ballForcing_admits_smoothDriver
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    (d' : ℝ) (hd'_pos : 0 < d') (hd'_le : d' ≤ T)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ : JetSpectralMassControl (I := I) (M := M) g₀ φ d')
    (hball : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d')),
      ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
        deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super)
    (hsolcoeff : ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d')] φ i) :
    ∃ d' : ℝ, 0 < d' ∧ d' ≤ T ∧
      ∃ c : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (c i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) d',
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (c i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d')] c i) := by
  classical
  obtain ⟨ψ, hψ_ctrl, hψ_ae⟩ :=
    deTurckSobolevNHa2_jetSpectralMass_preserving (I := I) (M := M)
      g₀ g_bg a ha_super hT hd'_pos hd'_le
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
      hball φ hφ hsolcoeff
  refine ⟨d', hd'_pos, hd'_le, ψ, hψ_ctrl.1, hψ_ctrl.2, fun i => ?_⟩
  have hsub : Set.Icc (0 : ℝ) d' ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hd'_le
  have htmc : (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
      =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d')]
        (fun t => (gforce t).coeff i) := by
    refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      hsub ?_
    exact timeModeCoeff_coeFn (I := I) (M := M) gforce i
  have hforce_coeff :
      (fun t => (gforce t).coeff i)
        =ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) d')]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) := by
    refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset (μ := MeasureTheory.volume)
      hsub ?_
    exact hforce.fun_comp (fun w => w.coeff i)
  exact (htmc.trans hforce_coeff).trans (hψ_ae i)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
