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
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.PDE.RicciFlow.ShortTimeParabolic.LocalWeylInput
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

/-! ## The interior heat-trace summability (the single Weyl-dependent input)

The classical local Weyl law (`local_weyl_eigenvalue_counting_bound`, the one
deferred analytic input of the development) reduces — via the proven chain
`EigenvalueCountingBound ⟹ EigenvalueTailSummable` — to the existence of an
exponent `p > 0` with `∑ᵢ (1 + λᵢ)^{-p}` summable.  From this single fact the
**interior heat-trace summability** `∑ᵢ (1 + λᵢ)^σ · e^{-2 λᵢ ε} < ∞` follows for
every `σ` and every `ε > 0`: the heat factor `e^{-2 λᵢ ε}` overwhelms any
polynomial weight, so `(1 + λᵢ)^σ e^{-2 λᵢ ε} ≤ C · (1 + λᵢ)^{-p}` (a
`λ`-uniform polynomial-times-exponential bound), and comparison with the
summable tail closes it. -/

/-- **Interior heat-trace summability from eigenvalue-tail summability.**
For every `σ ≥ 0` and `ε > 0`, the heat-weighted spectral family
`i ↦ (1 + λᵢ)^σ · e^{-2 λᵢ ε}` is summable.  This is the finiteness of
`tr(e^{2εΔ} (1 − Δ)^σ)`, derived from the eigenvalue tail
`∑ᵢ (1 + λᵢ)^{-p} < ∞` by the `λ`-uniform smoothing bound
`(1 + λᵢ)^{σ+p} e^{-2 λᵢ ε} ≤ tensorSmoothingConst (σ+p) · (min ε 1)^{-(σ+p)}`. -/
theorem heatTraceWeighted_summable_of_tailSummable
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (htail : EigenvalueTailSummable (I := I) (M := M) g r s)
    (σ : ℝ) (hσ : 0 ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        Real.exp (-(2 * (TensorEigenIdx.lambda (I := I) (M := M) i) * ε))) := by
  obtain ⟨p, hp_pos, htp⟩ := htail
  set C : ℝ := tensorSmoothingConst (σ + p) * (min ε 1) ^ (-(σ + p)) with hC
  have hC_nn : 0 ≤ C := by
    apply mul_nonneg (tensorSmoothingConst_nonneg _)
    exact Real.rpow_nonneg (le_of_lt (lt_min hε one_pos)) _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (htp.mul_left C)
  · exact mul_nonneg (tensorSobolevWeight_nonneg _ _) (Real.exp_pos _).le
  · set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
    have hlam_nn : 0 ≤ lam := tensor_lambda_nonneg (I := I) (M := M) i
    have hbase_pos : (0 : ℝ) < 1 + lam := by linarith
    have hsplit : tensorSobolevWeight (I := I) (M := M) i σ =
        ((1 + lam) ^ (σ + p)) * ((1 + lam) ^ (-p)) := by
      unfold tensorSobolevWeight
      rw [hlam, ← Real.rpow_add hbase_pos]; congr 1; ring
    have hbound := tensorSmoothingScalarBound_of_pos
      (μ := σ + p) (by linarith) (t := ε) hε (lam := lam) hlam_nn
    calc tensorSobolevWeight (I := I) (M := M) i σ *
            Real.exp (-(2 * lam * ε))
        = ((1 + lam) ^ (σ + p) * Real.exp (-(2 * lam * ε))) * ((1 + lam) ^ (-p)) := by
          rw [hsplit]; ring
      _ ≤ C * ((1 + lam) ^ (-p)) := by
          apply mul_le_mul_of_nonneg_right hbound
          exact Real.rpow_nonneg hbase_pos.le _

/-- **All-scale interior time-continuity of the maximal-regularity solution.**

The conclusion asks for a pointwise-in-time, `Hˢ`-valued continuous path `uσ`
on `[ε, T]` agreeing (after the spectral inclusion) with the base-scale
represented path `timeH1.toFun u`.  The witness is synthesised mode-by-mode: `uσ s`
is the `Hˢ` element with eigen-coordinates `i ↦ (timeH1.toFun u s).coeff i`, which
is the unconditional sum `∑ᵢ ((toFun u s).coeff i) • bᵢ` of single-mode fields.
Strong `Hˢ`-continuity on `[ε, T]` is the Weierstrass `M`-test
(`continuousOn_tsum`): each single-mode summand is continuous in time and the
mode-series of `Hˢ`-norms is dominated, uniformly on `[ε, T]`, by a summable
family whose finiteness is the **interior heat-trace summability**
`heatTraceWeighted_summable_of_tailSummable`, the sole Weyl-dependent input. -/
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
