import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private def JetSpectralMassControl
    (g₀ : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ) (T : ℝ) : Prop :=
  (∀ i, ContDiff ℝ ∞ (φ i)) ∧
    (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i τ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)

private noncomputable def deTurckRealizabilityRadius
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ :=
  (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1

private theorem deTurckRealizabilityRadius_pos
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    0 < deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super :=
  (Classical.choose_spec
    (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1

private theorem deTurckForcing_solCoeff_jetSpectralMass
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ φ T ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          ‖maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t‖ ≤
            deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super) ∧
        ∀ i, (fun t => (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t).coeff i)
            =ᵐ[timeMeasure T] φ i :=
  sorry

private theorem deTurckSobolevNHa2_jetSpectralMass_preserving
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T)
    (w : ℝ → tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
    (hw_ball : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖w t‖ ≤ deTurckRealizabilityRadius (I := I) (M := M) g₀ a ha_super)
    (φ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ)
    (hφ : JetSpectralMassControl (I := I) (M := M) g₀ φ T)
    (hw : ∀ i, (fun t => (w t).coeff i) =ᵐ[timeMeasure T] φ i) :
    ∃ ψ : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      JetSpectralMassControl (I := I) (M := M) g₀ ψ T ∧
        ∀ i, (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a (w t)).coeff i)
            =ᵐ[timeMeasure T] ψ i :=
  sorry

theorem deTurckForcing_timeModeCoeff_smooth_allOrderJet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ g : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (g i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (g i) t) ^ 2 ≤ B i) ∧
      (∀ i, (timeModeCoeff (I := I) (M := M) gforce i : ℝ → ℝ)
          =ᵐ[timeMeasure T] g i) := by
  obtain ⟨φ, hφ_ctrl, hφ_ball, hφ_ae⟩ :=
    deTurckForcing_solCoeff_jetSpectralMass (I := I) (M := M)
      g₀ g_bg a ha_super ha_even hT hT1 gforce hforce
  obtain ⟨ψ, hψ_ctrl, hψ_ae⟩ :=
    deTurckSobolevNHa2_jetSpectralMass_preserving (I := I) (M := M)
      g₀ g_bg a ha_super ha_even hT
      (fun t => maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)
      hφ_ball φ hφ_ctrl hφ_ae
  refine ⟨ψ, hψ_ctrl.1, hψ_ctrl.2, fun i => ?_⟩
  have hforce_coeff :
      (fun t => (gforce t).coeff i) =ᵐ[timeMeasure T]
        (fun t => (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t)).coeff i) :=
    hforce.fun_comp (fun w => w.coeff i)
  exact ((timeModeCoeff_coeFn (I := I) (M := M) gforce i).trans hforce_coeff).trans (hψ_ae i)

theorem deTurckForcing_smoothCoordinate_aeTimeJet
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) (ha_even : Even a)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) gforce t))) :
    ∃ f : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ → ℝ,
      (∀ i, ContDiff ℝ ∞ (f i)) ∧
      (∀ (j : ℕ) (τ : ℝ), 0 ≤ τ →
        ∃ B : TensorEigenIdx (I := I) (M := M) g₀ 0 2 → ℝ, Summable B ∧
          ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i τ *
                (iteratedDeriv j (f i) t) ^ 2 ≤ B i) ∧
      (∀ i, (fun t => (gforce t).coeff i) =ᵐ[timeMeasure T] f i) := by
  obtain ⟨g, hg_smooth, hg_mass, hg_ae⟩ :=
    deTurckForcing_timeModeCoeff_smooth_allOrderJet (I := I) (M := M)
      g₀ g_bg a ha_super ha_even hT hT1 gforce hforce
  refine ⟨g, hg_smooth, hg_mass, fun i => ?_⟩
  exact (timeModeCoeff_coeFn (I := I) (M := M) gforce i).symm.trans (hg_ae i)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
