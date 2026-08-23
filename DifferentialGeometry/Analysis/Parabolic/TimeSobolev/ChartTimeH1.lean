import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M]

omit [CompleteSpace E] in
/-- The coordinate expression of a `C¹` manifold curve is `C¹` while the curve stays in
the source of the fixed chart. -/
theorem chartCoord_contDiff
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    (p : M) {T : ℝ} (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma (Icc (0 : ℝ) T))
    (hsrc : MapsTo gamma (Icc (0 : ℝ) T) (chartAt H p).source) :
    ContDiffOn ℝ 1 ((extChartAt I p) ∘ gamma) (Icc (0 : ℝ) T) := by
  apply contMDiffOn_iff_contDiffOn.mp
  exact (contMDiffOn_extChartAt (I := I) (n := 1) (x := p)).comp hgamma hsrc

/-- A `C¹` manifold curve contained in one fixed chart, realized as a coordinate-valued
time-`H¹` curve. -/
noncomputable def chartTimeH1
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T : ℝ} (hT : 0 ≤ T) (p : M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma (Icc (0 : ℝ) T))
    (hsrc : MapsTo gamma (Icc (0 : ℝ) T) (chartAt H p).source) : timeH1 E T :=
  timeH1.ofContDiffOn hT ((extChartAt I p) ∘ gamma)
    (chartCoord_contDiff I p gamma hgamma hsrc)

/-- The continuous representative of `chartTimeH1` is the fixed-chart coordinate curve. -/
theorem chartTimeH1_toFun
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T : ℝ} (hT : 0 ≤ T) (p : M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma (Icc (0 : ℝ) T))
    (hsrc : MapsTo gamma (Icc (0 : ℝ) T) (chartAt H p).source) :
    EqOn (chartTimeH1 I hT p gamma hgamma hsrc).toFun
      ((extChartAt I p) ∘ gamma) (Icc (0 : ℝ) T) := by
  exact timeH1.toFun_ofContDiffOn hT ((extChartAt I p) ∘ gamma)
    (chartCoord_contDiff I p gamma hgamma hsrc)

/-- The weak time derivative of `chartTimeH1` is represented almost everywhere by the
ordinary derivative of the fixed-chart coordinate curve. -/
theorem chartTimeH1_deriv
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I 1 M]
    {T : ℝ} (hT : 0 ≤ T) (p : M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 gamma (Icc (0 : ℝ) T))
    (hsrc : MapsTo gamma (Icc (0 : ℝ) T) (chartAt H p).source) :
    (chartTimeH1 I hT p gamma hgamma hsrc).deriv
      =ᵐ[timeMeasure T] _root_.deriv ((extChartAt I p) ∘ gamma) := by
  exact timeH1.deriv_ofContDiffOn hT ((extChartAt I p) ∘ gamma)
    (chartCoord_contDiff I p gamma hgamma hsrc)

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
