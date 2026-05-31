/-
All-scale interior time-continuity of the maximal-regularity solution: on every
`[ε, T]` the carrier path lifts to a continuous `H^σ`-valued path for arbitrary
`σ ≥ a`, by analytic-semigroup decay. Skeleton stub for the short-time-existence
blueprint (GAP 1, spectral M1).
-/
import DifferentialGeometry.PDE.RicciFlow.ShortTimeExistence
import DifferentialGeometry.PDE.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.PDE.RicciFlow.Pullback.EvaluationFormChainRule
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.ParabolicInteriorSmoothing
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

/-- **All-scale interior time-continuity of the maximal-regularity solution.**

OPEN (honest gap, single `sorry`). The conclusion asks for a *pointwise-in-time,
`Hˢ`-valued continuous path* `uσ` on `[ε, T]` agreeing (after the spectral
inclusion) with the base-scale represented path `timeH1.toFun u`. The available
spectral infrastructure (`ParabolicInteriorSmoothing`, the `_ofCompact` readout
lemmas) provides only the **L²-in-time** order-`σ` field and a.e./coordinate
identities, NOT a pointwise-continuous `Hˢ`-valued path.

Precise reduction for the next worker (no fabrication shortcut is possible — the
existential witness must be constructed, so an "input path" hypothesis would be
hypothesis-packaging and is forbidden):
* synthesise `uσ t` mode-by-mode as the `Hˢ`-element with coordinates
  `i ↦ (timeH1.toFun u t).coeff i` (each coordinate is `u₀.coeff i · e^{-λᵢ t}`
  plus the Duhamel convolution, from `maxRegDuhamelSolField_coeff_ae` /
  `summable_solModeCoeff_ofCompact` under
  `tensorResolventL2_isCompactOperator_intrinsic`);
* prove `ContinuousOn uσ (Icc ε T)` via `continuousOn_tsum` (cf. the scalar
  template `CrossScaleField.continuousOn_normSq_repr`), applied to the
  `Hˢ`-valued per-mode functions `t ↦ (toFun u t).coeff i • basisVecσ i`,
  whose uniform-on-`[ε,T]` summability of `Hˢ`-norms reduces to the **interior
  heat-trace summability** `∑ᵢ (1 + λᵢ)^σ · e^{-2 λᵢ ε} < ∞` — a Weyl-type
  spectral-asymptotics input (finiteness of `tr(e^{2εΔ}(1−Δ)^σ)`), the allowed
  open gap. This is the sole remaining obligation. -/
theorem interior_allscale_time_continuity
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (hu : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce)
    (hcouple : ∀ d : ℝ,
      Summable (solFieldMass (I := I) (M := M) hT.le gforce (d + 1)) →
        Summable (forcingMass (I := I) (M := M) gforce d))
    (hbase : Summable (solFieldMass (I := I) (M := M) hT.le gforce (a : ℝ)))
    (σ : ℝ) (haσ : (a : ℝ) ≤ σ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ uσ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 σ,
        ContinuousOn uσ (Set.Icc ε T) ∧
          ∀ s ∈ Set.Icc ε T,
            tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2) haσ
              (uσ s) = timeH1.toFun u s := sorry

end DifferentialGeometry.PDE.RicciFlow
