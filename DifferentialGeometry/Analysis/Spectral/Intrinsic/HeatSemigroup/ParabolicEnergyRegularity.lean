import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralMassUniformSup
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.ForcingFixedPointParabolicSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic

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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedVariables false in
theorem deTurckForcing_solField_uniformSpatialMass_allOrder
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)))
    {δ₀ : ℝ} (hδ₀_nn : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1)
    (C : ℝ) (hC_pos : 0 < C)
    (hCtame : ∀ (u v : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a u -
          deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a v‖ ≤
        C * ‖u - v‖)
    (hsmall : C * δ₀ < 1) :
    ∀ σ : ℝ, ∃ Cσ : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Summable (fun i => tensorSobolevWeight (I := I) (M := M) i σ *
          (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
            (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2) ∧
        ∑' i, tensorSobolevWeight (I := I) (M := M) i σ *
            (perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i)
              (fun u => (timeModeCoeff (I := I) (M := M) gforce i) u) t) ^ 2 ≤ Cσ := by
  have h_compact :
      IsCompactOperator (tensorResolventL2 (I := I) (M := M) g₀ 0 2) :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
  have hforcingBase :
      Summable (forcingMass (I := I) (M := M) (a := (a : ℝ)) gforce (a : ℝ)) :=
    summable_weight_mul_norm_timeModeCoeff_sq (I := I) (M := M) h_compact (f := gforce)
  have hbase :
      Summable (solFieldMass (I := I) (M := M) (a := (a : ℝ)) hT.le gforce ((a : ℝ) + 2)) :=
    solFieldMass_summable_of_forcingMass_summable (I := I) (M := M) (a := (a : ℝ))
      hT.le gforce (a : ℝ) hforcingBase
  have hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) (a := (a : ℝ)) hT.le gforce (d + 1)) →
        Summable (forcingMass (I := I) (M := M) (a := (a : ℝ)) gforce d) :=
    fun d hsol =>
      deTurckForcing_solFieldMass_forcingMass_couple (I := I) (M := M)
        g₀ g_bg a ha_super hT hT1 gforce hforce d hsol
  exact spectralMass_sup_le_of_timeL2_allHs (I := I) (M := M) (a := (a : ℝ))
    hT gforce hcouple hbase

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
