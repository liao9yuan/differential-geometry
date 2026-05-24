import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.QuasilinearStrong
import DifferentialGeometry.PDE.RicciFlow.SobolevEmbedding
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Bridge from a maximally-regular `L²`-time-derivative to a pointwise
right-derivative on `[0, T)`. Substantive content: extracting a continuous
representative from time-`H¹` data (`TimeH1.hasDerivWithinAt_toFun_of_continuousOn`
and `TimeH1.ae_hasDerivWithinAt_toFun`) and upgrading the almost-everywhere
derivative to the pointwise `HasDerivWithinAt` statement at every `t ∈ [0, T)`.
The signature as stated is vacuously false for arbitrary `u`, `u'` (no link
between them); a substantive fill must replace `u`, `u'` by data carrying the
maximal-regularity / time-`H¹` structure (e.g., a `MaxRegSpace` element or a
`TimeH1` representative) from which the pointwise derivative is extracted. -/
theorem maxreg_l2deriv_to_pointwise_hasderivwithinat
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (u : ℝ → X) (u' : ℝ → X) (T : ℝ) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt u (u' t) (Set.Ici 0) t := by
  sorry

theorem hasDerivAt_clm_apply_from_h1_time
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : ℝ → X →L[ℝ] Y) (L' : ℝ → X →L[ℝ] Y) (u : ℝ → X) (u' : ℝ → X)
    (t : ℝ) (_x : X)
    (hL : HasDerivAt L (L' t) t) (hu : HasDerivAt u (u' t) t) :
    HasDerivAt (fun s : ℝ => L s (u s)) (L' t (u t) + L t (u' t)) t :=
  hL.clm_apply hu

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
