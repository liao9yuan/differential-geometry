/-
The interior parabolic time-regularity gate: for `t > 0` the carrier-scale path
`timeH1.toFun u` is classically differentiable with the spectral value
`Δ_∇ u₂ + N(u₁)`. Skeleton stub for the short-time-existence blueprint (GAP 1,
interior spectral gate).
-/
import DifferentialGeometry.PDE.RicciFlow.ShortTimeExistence
import DifferentialGeometry.PDE.RicciFlow.ShortTimeParabolic.ForcingPerModeAssembly
import DifferentialGeometry.PDE.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.PDE.RicciFlow.Pullback.EvaluationFormChainRule
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartOverlapUniqueness
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatIdentity
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

-- `hu`, `hu₂sol`, `hforce` are genuine node-signature hypotheses retained for the
-- blueprint dependency contract (they pin the carrier to the Duhamel solution field
-- and the forcing to the continuous DeTurck nonlinearity). This proof discharges the
-- conclusion through the per-mode/Duhamel assembly sibling `permode_sum_hasderivat`,
-- threading those Duhamel hypotheses together with the two interior-smoothing inputs
-- `hderiv_ae` (a.e. identity of the L² time-derivative with the spectral RHS) and
-- `hRHS_cont` (interior continuity of the spectral RHS path) into the call site.
-- Some of the Duhamel hypotheses are subsumed by the two interior inputs at the call
-- site; the narrow linter suppression keeps the full signature intact and
-- warning-free.
set_option linter.unusedVariables false in
theorem deturck_interior_time_regularity
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (hu : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce)
    (hu₂sol : ∀ s, u₂ s =
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce s)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckGeometricN (I := I) g_bg a
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce t)))
    (hu₂ : ∀ s, tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) = timeH1.toFun u s)
    (hderiv_ae : (u.deriv : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
        =ᵐ[timeMeasure T]
      (fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
        deTurckGeometricN (I := I) g_bg a
          (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))))
    (hRHS_cont : ContinuousOn
      (fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
        deTurckGeometricN (I := I) g_bg a
          (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) (Set.Ioo (0 : ℝ) T)) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun r => (timeH1.toFun u r : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          deTurckGeometricN (I := I) g_bg a
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s := by
  -- Reduce to the per-mode/Duhamel assembly sibling `permode_sum_hasderivat` by
  -- instantiating its order-`(a+1)` carrier `u₁` as the canonical inclusion of the
  -- order-`(a+2)` lift `u₂`. With that choice the `hu₁` link is definitional (`rfl`),
  -- and the conclusion of `permode_sum_hasderivat` is syntactically the conclusion here.
  -- The Duhamel-structure hypotheses and the two interior-smoothing inputs are
  -- threaded through verbatim.
  exact permode_sum_hasderivat (I := I) (M := M) g_bg a u₀ gforce hT hT1 u u₂
    (fun s => tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
    hu hu₂sol hforce hu₂ (fun _ => rfl) hderiv_ae hRHS_cont

end DifferentialGeometry.PDE.RicciFlow
