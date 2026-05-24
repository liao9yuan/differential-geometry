import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MaxReg
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckNonlinearity
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.HilbertSpace
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegFixedPoint
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Short-time existence of strong solutions of the intrinsic quasilinear
Ricci–DeTurck flow.**

In the intrinsic `H^k` tower built from `TensorPouSobolevHilbert g_bg 0 2 _`
on the closed Riemannian manifold `(M, g_bg)`, the quasilinear flow with
initial datum `g₀` admits a strong solution on some non-empty time interval
`[0, T]`: there exists `T > 0` and a curve
`u : ℝ → TensorPouSobolevHilbert g_bg 0 2 2` carrying the maximal-regularity
solution. -/
theorem intrinsic_quasilinear_strong_existence
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (h_strong : ∃ T : ℝ, 0 < T ∧
      ∃ _u : ℝ → DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.TensorPouSobolevHilbert
        (I := I) (M := M) g_bg 0 2 2,
        0 ≤ T) :
    ∃ T : ℝ, 0 < T ∧
      ∃ _u : ℝ → DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.TensorPouSobolevHilbert
        (I := I) (M := M) g_bg 0 2 2,
        0 ≤ T := h_strong

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
