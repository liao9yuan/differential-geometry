import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRealizeTwo

/-!
# High-scale Ricci--DeTurck forcing identity

The adjacent-scale lift already identifies the high forcing after inclusion
into `H¹`, while `lowReg_force_smooth` identifies that lower forcing with the
genuine smooth Ricci--DeTurck nonlinearity.  Injectivity of the spectral
inclusion upgrades the equality back to `H²` along the realized smooth family.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The lifted `H²` forcing is the genuine smooth Ricci--DeTurck
nonlinearity along any smooth family realizing the lower solution field. -/
theorem force_hi_smooth
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ P : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) P‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (field : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2
      (((1 : ℕ) : ℝ) + 2)) T)
    (fHi : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ)) T)
    (fLo : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2
      ((1 : ℕ) : ℝ)) T)
    (hstate : ∀ᵐ t ∂timeMeasure T,
      field t ∈ lowerState (I := I) (M := M) g₀ 1 R)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t))
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t)
    (F : ℝ → SmoothCcTensor g₀ 0 2)
    (hpin : ∀ᵐ t ∂timeMeasure T,
      smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 2) (F t) = field t)
    (hball : ∀ t : ℝ,
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
        (smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 2) (F t))‖ ≤ R) :
    (fun t => fHi t) =ᵐ[timeMeasure T]
      fun t => deTurckSmoothN (I := I) (M := M) g₀ g_bg 2
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t))) := by
  have hlo := lowReg_force_smooth (I := I) (M := M) g₀ g_bg hR hδ
    hreal hcore field fLo hstate hforce F hpin hball
  filter_upwards [hincl, hlo] with t hi hlow
  apply tensorHsInclusion_injective (I := I) (M := M) (g := g₀)
    (r := 0) (s := 2) (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
  calc
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num) (fHi t) = fLo t := hi
    _ = deTurckSmoothN (I := I) (M := M) g₀ g_bg 1
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t))) := hlow
    _ = tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) ≤ (2 : ℝ) by norm_num)
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg 2
          (symmS (I := I) (M := M) g₀ (F t)) hδ
          (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t)))) :=
      (deTurckSmoothN_incl (I := I) (M := M) g₀ g_bg
        (a := 1) (b := 2) (by norm_num)
        (symmS (I := I) (M := M) g₀ (F t)) hδ
        (hreal _ (symm_h2_of_state (I := I) (M := M) g₀ (F t) (hball t)))).symm

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
