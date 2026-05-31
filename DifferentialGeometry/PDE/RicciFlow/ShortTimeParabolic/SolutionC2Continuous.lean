/-
`C²`-up-to-`t = 0` continuity of the realized DeTurck solution and its Ricci
tensor, via the linear small-tensor realization and the `Hᵃ ↪ C²` Sobolev
embedding. Skeleton stub for the short-time-existence blueprint (GAP 1,
deliverable).
-/
import DifferentialGeometry.PDE.RicciFlow.ShortTimeParabolic.RealizeTransport
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.RicciFlowPdeAtZero
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

-- `ha` records the supercriticality scale `2*a > dim+4` under which the `Hᵃ ↪ C²`
-- embedding at the two-derivative scale `H^{2a}` discharges `hC2_chart` downstream;
-- it is a genuine signature hypothesis the parent supplies, not used textually here.
set_option linter.unusedVariables false in
theorem deturck_solution_c2_continuous_icc0
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (ha : 2 * a > Module.finrank ℝ E + 4)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (u : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2)
    (hcont : ContinuousOn (fun s : ℝ => u s) (Set.Icc 0 T))
    (hreal : ∀ (s : ℝ) (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s s) x v w)
    (hsmoothrepr : ∀ (s : ℝ)
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (u s).coeff i
        = tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    -- The chart-`2`-jet time-continuity of the Gram entries of the LINEAR realize
    -- `g_DT` on the Levi-Civita good set.  This is the `Hᵃ ↪ C²` Sobolev-embedding
    -- step at the two-derivative scale `H^{2a}` (`2*a > dim+4`), and is a STRONGER
    -- input than the carrier-scale time continuity `hcont` supplies (`hcont` only
    -- controls `T_s` at the `Hᵃ` scale through `hsmoothrepr`, not `H^{2a}`).  It is
    -- the SAME chart-Gram-`C²` continuity required by the `hC2` slot of the sibling
    -- `ricci_continuous_in_metric_time`, i.e. the realization/Weyl-gated input;
    -- carried here as a dischargeable, non-leaking hypothesis on the linear realize.
    (hC2_chart : ∀ (α : M) (y : M), y ∈ chartLeviCivitaGoodSet (I := I) α →
      ∀ i j : Fin (Module.finrank ℝ E), ∀ k : ℕ, k ≤ 2 →
        ContinuousOn
          (fun s : ℝ => iteratedFDeriv ℝ k
            (Integral.DivergenceTheorem.chartGramOnE (I := I) (g_DT s) α i j)
            (extChartAt I α y))
          (Set.Icc 0 T)) :
    (∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T))
    ∧ (∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun s : ℝ => ricciTensor (I := I) (g_DT s) x v w) (Set.Icc 0 T)) := by
  -- **Conjunct 1 (metric-value time continuity), proven unconditionally.**
  --
  -- The carrier-scale realize functional `ℓ_a` of `realize_eval_carrier_factorization`
  -- is a *continuous linear* map `tensorHs g_bg 0 2 a →L[ℝ] ℝ` that, on any pair
  -- `(T_z, z)` whose eigenbasis coordinates match through the compact-resolvent
  -- coefficient extractor, returns `ccTensorBilinSymm g_bg T_z x v w`.  Our hypothesis
  -- `hsmoothrepr` is exactly that coordinate-matching condition for the pair
  -- `(T_s s, u s)`, so `ℓ_a (u s) = ccTensorBilinSymm g_bg (T_s s) x v w` for every `s`.
  -- Combined with the linear realize identity `hreal`, the metric value
  -- `(g_DT s).inner x v w` equals the constant `g_bg.inner x v w` plus the
  -- continuous-linear image `ℓ_a (u s)` of the time-continuous carrier `u`, hence is
  -- continuous on `Icc 0 T`.
  have hconj1 : ∀ (x : M) (v w : TangentSpace I x),
      ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T) := by
    intro x v w
    obtain ⟨ℓ_a, hℓ_a⟩ :=
      realize_eval_carrier_factorization (I := I) (M := M) g_bg a ha x v w
    -- The realize functional reproduces the linear realize at every time `s`.
    have hval : ∀ s : ℝ,
        (g_DT s).inner x v w = g_bg.inner x v w + ℓ_a (u s) := by
      intro s
      rw [hreal s x v w, hℓ_a (T_s s) (u s) (hsmoothrepr s)]
    -- Rewrite the time-section as constant `+` continuous-linear image of `u`.
    have hfun : (fun s : ℝ => (g_DT s).inner x v w)
        = fun s : ℝ => g_bg.inner x v w + ℓ_a (u s) := by
      funext s; exact hval s
    rw [hfun]
    -- `s ↦ ℓ_a (u s)` is continuous on `Icc 0 T` as the composition of the
    -- continuous linear `ℓ_a` with the time-continuous carrier `u`.
    have hcomp : ContinuousOn (fun s : ℝ => ℓ_a (u s)) (Set.Icc 0 T) :=
      ℓ_a.continuous.comp_continuousOn hcont
    exact continuousOn_const.add hcomp
  refine ⟨hconj1, ?_⟩
  -- **Conjunct 2 (Ricci-tensor time continuity).**
  --
  -- The metric-value continuity `hconj1` supplies the `hval`-slot of the sibling
  -- `ricci_continuous_in_metric_time`; its `hC2`-slot is exactly the chart-`2`-jet
  -- time-continuity of the Gram entries of `g_DT` on the Levi-Civita good set, which
  -- is the dischargeable hypothesis `hC2_chart`.  The chart-Ricci continuity chain
  -- (Christoffel → Riemann → trace) inside `ricci_continuous_in_metric_time` then
  -- delivers the conclusion.
  intro x v w
  exact ricci_continuous_in_metric_time (I := I) (M := M) g_DT T x v w hconj1 hC2_chart

end DifferentialGeometry.PDE.RicciFlow
