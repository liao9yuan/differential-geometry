/-
The flat (Lie-route) variational data for the conjugating family: existence of the
raw flat variational identity, the Christoffel-correction equation relating its
factor values, and the flat value-jet identity at the chart level. Skeleton stubs
for the short-time-existence blueprint (GAP 2, flat variational data).
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

theorem flat_raw_variational_identity
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (hXauto : AutonomizedFieldJointC1 (I := I) X)
    (hΦfam_ode : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
        ∀ y ∈ W, ∀ s ∈ Set.Ioo (t - T₀) (t + T₀),
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) y)
            (Set.Ioo (t - T₀) (t + T₀)) s
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) y))))
    (horbit_cont : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      ContinuousAt (fun y : M => (Φ_fam t : M → M) y) x ∧
      ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    ∃ T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E),
      ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
        RawVariationalIdentityFlat (I := I) Φ_fam t x v (T' t x v) (P' t x v) := sorry

theorem flat_christoffel_correction_eqn
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (T' P' : ℝ → ∀ x : M, TangentSpace I x → (E →L[ℝ] E)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      (T' t x v) (mfderiv I I (Φ_fam t : M → M) x v) + (P' t x v) v
        = negCovariantSlotValue (I := I) (g_DT t)
            (deTurckVF (I := I) (g_DT t) g_bg) Φ_fam t x v
          + christoffelCorrection (I := I) (g_DT t) (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (deTurckVF (I := I) (g_DT t) g_bg) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v) := sorry

theorem flat_value_jet_identity
    (X : Cₛ^∞⟮I; E, (TangentSpace I)⟯)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (t : ℝ) (x : M) (v : TangentSpace I x)
    (T' P' : E →L[ℝ] E)
    (hflat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T' P')
    (hΦflow : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
      (Set.Ici (0 : ℝ)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (-((X : ∀ y : M, TangentSpace I y) ((Φ_fam t : M → M) x)))))
    (hΦnbhd : ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, ∀ s ∈ Set.Ioo (t - T₀) (t + T₀),
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) y)
          (Set.Ioo (t - T₀) (t + T₀)) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-((X : ∀ y : M, TangentSpace I y) ((Φ_fam s : M → M) y)))))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x))) :
    T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v
      = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x v)
          + movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x v)) := sorry

end DifferentialGeometry.PDE.RicciFlow
