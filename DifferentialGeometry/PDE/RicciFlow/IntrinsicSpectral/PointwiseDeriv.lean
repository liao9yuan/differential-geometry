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

/-- Packaging lemma: given a pointwise right-derivative hypothesis at every
`t ∈ [0, T)`, extract the `HasDerivWithinAt` statement at each such point.
This is the honest, hypothesis-driven form of the abstract bridge from a
strong (maximally regular) `L²`-time-derivative to a pointwise statement.
The substantive content (extracting a continuous, hence pointwise-
differentiable, representative from time-`H¹` data) lives in
`TimeH1.hasDerivWithinAt_toFun_of_continuousOn` and
`TimeH1.ae_hasDerivWithinAt_toFun`; here we only repackage a supplied
pointwise hypothesis so that downstream consumers can chain it
into composite-derivative rules such as `clm_apply`. -/
theorem maxreg_l2deriv_to_pointwise_hasderivwithinat
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (u : ℝ → X) (u' : ℝ → X) (T : ℝ)
    (h_pointwise : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt u (u' t) (Set.Ici 0) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt u (u' t) (Set.Ici 0) t := by
  intro t ht
  exact h_pointwise t ht

theorem hasDerivAt_clm_apply_from_h1_time
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : ℝ → X →L[ℝ] Y) (L' : ℝ → X →L[ℝ] Y) (u : ℝ → X) (u' : ℝ → X)
    (t : ℝ) (_x : X)
    (hL : HasDerivAt L (L' t) t) (hu : HasDerivAt u (u' t) t) :
    HasDerivAt (fun s : ℝ => L s (u s)) (L' t (u t) + L t (u' t)) t :=
  hL.clm_apply hu

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
