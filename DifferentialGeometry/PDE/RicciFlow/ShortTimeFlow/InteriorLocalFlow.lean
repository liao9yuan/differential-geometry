/-
The per-chart forward Picard local flow, the forward-uniqueness glue into one
interior flow carrying the bare velocity, and the chart-cover orbit linchpin.
Skeleton stubs for the short-time-existence blueprint (GAP 2, interior flow).
-/
import DifferentialGeometry.PDE.RicciFlow.ShortTimeExistence
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

theorem interior_local_flow_existence
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (α : M)
    (hCont : ContinuousOn (Function.uncurry (fun t x => X_DT t x))
      (Set.univ : Set (ℝ × M)))
    (hLip : ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X_DT t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r)) :
    ∃ T : ℝ, 0 < T ∧ ∃ r' : ℝ, 0 < r' ∧
      ∃ flow : E → ℝ → E,
        (∀ y ∈ Metric.closedBall (I ((chartAt H α) α)) r',
          flow y 0 = y ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            HasDerivWithinAt (flow y)
              ((X_DT t ((chartAt H α).symm (I.symm (flow y t)))) : E)
              (Set.Icc (0 : ℝ) T) t) :=
  -- Direct chart-Picard application: the chart-pushforward of `X_DT` is
  -- continuous on `ℝ × M` and chart-Lipschitz on a ball, so Mathlib's
  -- Picard–Lindelöf (packaged in `time_dependent_vf_chart_local_picard_with_lipschitz`)
  -- yields the chart-coordinate local flow.
  time_dependent_vf_chart_local_picard_with_lipschitz (I := I) X_DT α hCont hLip

theorem interior_flow_uniqueness_glue
    (X : ℝ → ∀ x : M, TangentSpace I x) (hX : AutonomizedFieldJointC1 (I := I) X)
    (T : ℝ) (hT : 0 < T)
    (hper : ∀ α : M, ChartLocalPicardData (I := I) X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (I := I) (fun t x => -(X t x)) α)
    (hTle : ∀ α : M, T ≤ (hper α).T)
    (hTleNeg : ∀ α : M, T ≤ (hperNeg α).T)
    (hSmoothX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E)))
    (hSmoothNegX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      ((-X t ((chartAt H α).symm (I.symm y))) : E))) :
    ∃ Φcc : ℝ → M → M, (∀ x : M, Φcc 0 x = x) ∧
      (∀ x : M, ∃ α : M, ∀ s : ℝ, Φcc s x =
        (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φcc t x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
        (∀ s : ℝ, Φcc s x =
          (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φcc s x)
          (Set.Icc (0 : ℝ) (hper α).T) t
          ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I)
              ((hper α).flow (I ((chartAt H α) x)) t)) ∘L
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φcc t x))))) := sorry

-- The chart-cover orbit linchpin uses the representation/confinement/target data
-- (`hrepr`, `hconf`, `htgt`) plus the chart-bridge infrastructure; the field
-- regularity `hX`, the horizon positivity `hT`, and the initial condition `hΦcc0`
-- are part of the on-disk signature but are not consumed by the transported-velocity
-- ODE bridge itself, so the unused-variable linter is silenced narrowly here.
set_option linter.unusedVariables false in
theorem chartcover_orbit_is_bare_integral_curve
    (X : ℝ → ∀ x : M, TangentSpace I x) (hX : AutonomizedFieldJointC1 (I := I) X)
    (T : ℝ) (hT : 0 < T) (Φcc : ℝ → M → M)
    (hΦcc0 : ∀ x : M, Φcc 0 x = x)
    (hper : ∀ α : M, ChartLocalPicardData (I := I) X α)
    (hTle : ∀ α : M, T ≤ (hper α).T)
    (hrepr : ∀ x : M, ∃ α : M, x ∈ (hper α).U ∧ ∀ s : ℝ, Φcc s x =
      (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s)))
    (hconf : ∀ x : M, ∀ α : M, x ∈ (hper α).U →
      ∀ t : ℝ, 0 < t → t < T →
        ((hper α).flow (I ((chartAt H α) x))) ⁻¹' (Set.range I) ∈
          𝓝[Set.Icc (0 : ℝ) (hper α).T] t)
    (htgt : ∀ x : M, ∀ α : M, x ∈ (hper α).U →
      ∀ t : ℝ, 0 < t → t < T →
        (hper α).flow (I ((chartAt H α) x)) t ∈ (extChartAt I α).target) :
    ∀ t : ℝ, 0 < t → t < T → ∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
      (∀ s : ℝ, Φcc s x =
        (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φcc s x)
        (Set.Icc (0 : ℝ) (hper α).T) t
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I)
            ((hper α).flow (I ((chartAt H α) x)) t)) ∘L
          ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φcc t x)))) := by
  intro t ht0 htT x
  -- Choose the representing chart `α` for `x`: it carries `x ∈ (hper α).U` and
  -- the chart-coordinate representation `Φcc s x = (chartAt H α).symm ...`.
  obtain ⟨α, hxU, hΦrepr⟩ := hrepr x
  refine ⟨α, hxU, hΦrepr, ?_⟩
  -- The chart-coordinate trajectory of `x`.
  set y : E := I ((chartAt H α) x) with hy
  -- `t ∈ [0, (hper α).T]`: from `0 < t` and `t < T ≤ (hper α).T`.
  have ht_Icc : t ∈ Set.Icc (0 : ℝ) (hper α).T :=
    ⟨ht0.le, (htT.le).trans (hTle α)⟩
  -- The confinement and target hypotheses for this `(x, α, t)`.
  have hconf_t : ((hper α).flow y) ⁻¹' (Set.range I) ∈
      𝓝[Set.Icc (0 : ℝ) (hper α).T] t := hconf x α hxU t ht0 htT
  have htgt_t : (hper α).flow y t ∈ (extChartAt I α).target := htgt x α hxU t ht0 htT
  -- The chart-bridge manifold ODE, in transported-velocity form.
  have hbridge :
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
        (fun s : ℝ => (chartAt H α).symm (I.symm ((hper α).flow y s)))
        (Set.Icc 0 (hper α).T) t
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I)
            ((hper α).flow y t)) ∘L
          ((ContinuousLinearMap.id ℝ ℝ).smulRight
            (X t ((chartAt H α).symm (I.symm ((hper α).flow y t)))))) :=
    manifoldFlow_hasMFDerivWithinAt_of_chartLocal (I := I) X α x (hper α)
      hxU t ht_Icc hconf_t htgt_t
  -- Identify the curve `s ↦ Φcc s x` with the chart-coordinate realisation.
  have hcurve : (fun s : ℝ => Φcc s x) =
      fun s : ℝ => (chartAt H α).symm (I.symm ((hper α).flow y s)) := by
    funext s; rw [hΦrepr s]
  -- Identify the velocity vector via the chart representation at `s = t`.
  have hvel : (X t (Φcc t x) : E) =
      (X t ((chartAt H α).symm (I.symm ((hper α).flow y t))) : E) := by
    rw [hΦrepr t]
  -- Assemble.
  rw [hcurve, hvel]
  exact hbridge

end DifferentialGeometry.PDE.RicciFlow
