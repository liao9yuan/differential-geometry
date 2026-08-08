import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRungPack
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgRungFive

/-!
# Metricwise fixed-background gate package

This module selects the three fixed bottom-rung certificates and the generic
high-rung certificate for one pair `(g, g_bg)`.  The scalar envelopes are
metricwise bookkeeping only: no class-first uniformity is asserted here.

The scalar domination theorem `rungGate_le` is background-neutral and is reused
unchanged from `LowRegRungPack`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- A coherent pair of metricwise scalar envelopes for the three fixed
background bottom-rung gates and the generic background high-rung coefficient.
Each stored continuation retains the exact witnesses selected for `(g, g_bg)`.
-/
def IsLowGateOrdBg (g g_bg : SmoothRiemannianMetric I M) (A B : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧
    (∃ C2 Kr23 Kr13 K2 : ℝ,
      IsRung3OrdBg (I := I) (M := M) g g_bg C2 Kr23 Kr13 K2 ∧
        C2 * K2 ≤ A ∧ Kr23 + Kr13 ≤ B) ∧
    (∃ C3 Kr24 Kr14 K3 : ℝ,
      IsRung4OrdBg (I := I) (M := M) g g_bg C3 Kr24 Kr14 K3 ∧
        C3 * K3 ≤ A ∧ Kr24 + Kr14 ≤ B) ∧
    (∃ C4 Kr25 Kr15 K4 : ℝ,
      IsRung5OrdBg (I := I) (M := M) g g_bg C4 Kr25 Kr15 K4 ∧
        C4 * K4 ≤ A ∧ Kr25 + Kr15 ≤ B) ∧
    ∃ κ : ℝ, IsHmRungOrdBg (I := I) (M := M) g g_bg κ ∧ κ ≤ A

/-- Select one coherent metricwise gate package from the three fixed-background
rungs and the arbitrary-background all-rung producer. -/
theorem lowregGatePackBg (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ A B : ℝ, IsLowGateOrdBg (I := I) (M := M) g g_bg A B := by
  obtain ⟨C2, Kr23, Kr13, K2, h2⟩ :=
    lowregRung3PackBg (I := I) (M := M) hDim g g_bg
  obtain ⟨C3, Kr24, Kr14, K3, h3⟩ :=
    lowregRung4PackBg (I := I) (M := M) hDim g g_bg
  obtain ⟨C4, Kr25, Kr15, K4, h4⟩ :=
    lowregRung5PackBg (I := I) (M := M) hDim g g_bg
  obtain ⟨κ, hκ⟩ := lowregHmPackBg (I := I) (M := M) hDim g g_bg
  let A : ℝ := C2 * K2 + C3 * K3 + C4 * K4 + κ
  let B : ℝ := (Kr23 + Kr13) + (Kr24 + Kr14) + (Kr25 + Kr15)
  have hC2K2 : 0 ≤ C2 * K2 := mul_nonneg h2.1 h2.2.2.2.1
  have hC3K3 : 0 ≤ C3 * K3 := mul_nonneg h3.1 h3.2.2.2.1
  have hC4K4 : 0 ≤ C4 * K4 := mul_nonneg h4.1 h4.2.2.2.1
  have hB3 : 0 ≤ Kr23 + Kr13 := add_nonneg h2.2.1 h2.2.2.1
  have hB4 : 0 ≤ Kr24 + Kr14 := add_nonneg h3.2.1 h3.2.2.1
  have hB5 : 0 ≤ Kr25 + Kr15 := add_nonneg h4.2.1 h4.2.2.1
  have hκ0 : 0 ≤ κ := hκ.1
  have hAnn : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg (add_nonneg (add_nonneg hC2K2 hC3K3) hC4K4) hκ0
  have hBnn : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg (add_nonneg hB3 hB4) hB5
  have hA2le : C2 * K2 ≤ A := by dsimp only [A]; linarith
  have hA3le : C3 * K3 ≤ A := by dsimp only [A]; linarith
  have hA4le : C4 * K4 ≤ A := by dsimp only [A]; linarith
  have hκle : κ ≤ A := by dsimp only [A]; linarith
  have hB3le : Kr23 + Kr13 ≤ B := by dsimp only [B]; linarith
  have hB4le : Kr24 + Kr14 ≤ B := by dsimp only [B]; linarith
  have hB5le : Kr25 + Kr15 ≤ B := by dsimp only [B]; linarith
  exact ⟨A, B, hAnn, hBnn,
    ⟨C2, Kr23, Kr13, K2, h2, hA2le, hB3le⟩,
    ⟨C3, Kr24, Kr14, K3, h3, hA3le, hB4le⟩,
    ⟨C4, Kr25, Kr15, K4, h4, hA4le, hB5le⟩,
    ⟨κ, hκ, hκle⟩⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
