/-
Continuity of the conjugating family's pushforward in time, the interior
identification of the diffeomorphism family with the chart-cover flow, and the
`t = 0` right-continuity of the moving pushforward. Skeleton stubs for the
short-time-existence blueprint (GAP 2, flow-continuity).
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

theorem flow_pushforward_continuous_in_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (T : ℝ) (hT : 0 < T)
    (hΦ0 : Φ_fam 0 = Diffeomorph.refl I M ∞)
    (hbare : ∀ s : ℝ, 0 < s → s ≤ T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ici (0 : ℝ)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) x))))
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ)) :
    (∀ (x : M) (v : TangentSpace I x), ContinuousOn
      (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E)) (Set.Ico 0 T))
    ∧ (∀ x : M, ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ici (0 : ℝ)) 0) := sorry

theorem flow_family_identification
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (Φ : ℝ → M → M)
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hΦfam_ode : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ioo (0 : ℝ) T) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) x))))
    (hΦ_ode : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Ioo (0 : ℝ) T) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ s x))))
    (hwin : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      ∃ (a b : ℝ) (Xt : ℝ → ∀ x : M, TangentSpace I x),
        s ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T ∧
          AutonomizedFieldJointC1 (I := I) Xt ∧
          (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x))
    (hstart : ∃ t₀ ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, (Φ_fam t₀ : M → M) x = Φ t₀ x) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, (Φ_fam s : M → M) x = Φ s x := sorry

theorem joint_smooth_moving_mfderiv_continuous
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (Φ : ℝ → M → M) (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X_DT q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X_DT q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hinterior : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x))))
    (hpicard : ∀ x : M, ∃ α : M, ∃ δ : ℝ, 0 < δ ∧ x ∈ (chartAt H α).source ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T), Φ s x ∈ (chartAt H α).source ∧
        extChartAt I α (Φ s x)
          = extChartAt I α x + ∫ r in (0 : ℝ)..s,
              chartRawRepr (I := I) α (X_DT r) (extChartAt I α (Φ r x))) :
    (∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) 0)
    ∧ (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E))
          (Set.Ici (0 : ℝ)) 0) := sorry

end DifferentialGeometry.PDE.RicciFlow
