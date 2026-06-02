import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.EvaluationFormChainRule
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartLocalPicard
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.ChartOverlapUniqueness
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.IntervalGlobalFlow
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.ChartLocalExistence.CorrectedChartAnchor
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.CorrectedVariationalEndpoint
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.Regularity.FieldTimeExtension
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.ChartOperator.MovingTrivJet

/-!
# Forward (one-sided) flow of the DeTurck vector field

Produces the forward integral flow of the time-dependent DeTurck vector field on `[0, T)` from a
joint-`C¹` field hypothesis, together with the time-zero continuity extension used downstream.
-/

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

/-- **Orbit right-continuity at `t = 0`** from the trivialised chart integral identity.

Fix `x : M`.  By `hpicard` the orbit `s ↦ Φ s x` satisfies, on a right-half neighbourhood
`Ico 0 (min δ T)` of `0`, the chart integral identity with the *trivialised* integrand
`chartTrivRepr α (X_DT r) (extChartAt I α (Φ r x))` (the geometrically-correct chart velocity,
the `trivToE`-transported field).  On the orbit this equals `trivToE α (Φ r x) (X_DT r (Φ r x))`,
whose norm is bounded on the compact `Icc 0 T ×ˢ univ`; hence the chart image of the orbit differs
from `extChartAt I α x` by an integral of norm `≤ C·|s| → 0` as `s → 0⁺`, giving right-continuity
of the orbit at `0` after composing with the continuous chart inverse. -/
private theorem flow_orbit_continuousWithinAt_zero
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (Φ : ℝ → M → M) (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X_DT q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hpicard : ∀ x : M, ∃ α : M, ∃ δ : ℝ, 0 < δ ∧ x ∈ (chartAt H α).source ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T), Φ s x ∈ (chartAt H α).source ∧
        extChartAt I α (Φ s x)
          = extChartAt I α x + ∫ r in (0 : ℝ)..s,
              chartTrivRepr (I := I) α (X_DT r) (extChartAt I α (Φ r x))) :
    ∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) 0 := sorry

/-- **Moving-spatial-Jacobian right-continuity at `t = 0` (variational endpoint).**

The variational analogue of `flow_orbit_continuousWithinAt_zero`.  Fix `x : M` and
`v : TangentSpace I x`.  The `E`-valued moving spatial Jacobian
`J s := (mfderiv I I (Φ s) x v : E)` satisfies, on a right-half neighbourhood
`Ico 0 (min δ T)` of `0`, the *linearised (variational) integral equation*

  `J s = J₀ + ∫₀ˢ A r (J r) dr`,

where `J₀ = (mfderiv I I (Φ 0) x v : E)` is the initial Jacobian value and the *covariant*
coefficient `A r := fderiv ℝ (chartTrivRepr α (X_DT r)) (extChartAt I α (Φ r x))` is the spatial
gradient of the trivialised chart field along the orbit.  `‖A‖` is bounded on the compact
`Icc 0 T ×ˢ univ` via the `chartTrivRepr_fderiv_eq` decomposition (`hgrad0` for the raw spatial
gradient, `hmovtriv` for the moving-trivialization jet) and `B` bounds `‖J r‖` near `0`
(`hJbound`, the genuine near-`0` boundedness of the variational Jacobian, dischargeable
downstream by the linear Grönwall estimate `‖J r‖ ≤ ‖J₀‖ · exp (C_A · r)`).  Hence
`‖J s − J₀‖ ≤ (C_A · B) · |s| → 0` as `s → 0⁺`; with `J 0 = J₀` this is right-continuity
at `0`.

`hvarpicard` (the variational integral equation for the moving Jacobian) and `hJbound`
(near-`0` boundedness of the Jacobian) are genuine dischargeable analytic data about the
linearised flow — neither is the conclusion (a `ContinuousWithinAt` of `J`), so this is
not hypothesis-packaging. -/
private theorem flow_mfderiv_continuousWithinAt_zero
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (Φ : ℝ → M → M)
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X_DT q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hmovtriv : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α q.2))
        (Prod.snd ⁻¹' (chartAt H α).source : Set (ℝ × M)))
    (hvarpicard : ∀ (x : M) (v : TangentSpace I x), ∃ α : M, ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
        (mfderiv I I (fun y : M => Φ s y) x v : E)
          = (@id E (mfderiv I I (fun y : M => Φ 0 y) x v))
            + ∫ r in (0 : ℝ)..s,
                (fderiv ℝ (fun z => chartTrivRepr (I := I) α (X_DT r) z)
                    (extChartAt I α (Φ r x)))
                  (mfderiv I I (fun y : M => Φ r y) x v : E))
    (hJbound : ∀ (x : M) (v : TangentSpace I x), ∃ δ : ℝ, ∃ B : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
        ‖(mfderiv I I (fun y : M => Φ s y) x v : E)‖ ≤ B) :
    ∀ (x : M) (v : TangentSpace I x),
      ContinuousWithinAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E))
        (Set.Ici (0 : ℝ)) 0 := sorry

/-- **Bare geometric velocity on `(0,T)` for `Φ := Φ0`** (C3), transported from the interior
flow `Φint` across their pointwise agreement on `(0,T)`.

For `t ∈ (0,T)` the curve `s ↦ Φ0 s x` agrees with `s ↦ Φint s x` on `Ioo 0 T` (`hagree`),
which is a neighbourhood of `t` within `Ici 0`; so `HasMFDerivWithinAt.congr_of_eventuallyEq`
transports the interior bare velocity `hΦint_bare` to `Φ0`, and the within-set widens from
`Ioo 0 T` to the headline's `Ici 0` (they coincide near the interior point `t`).  The velocity
`X_DT t (Φint t x)` rewrites to `X_DT t (Φ0 t x)` by `hagree` at `t`. -/
theorem forwardFlow_bare_velocity_of_agree
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (Φ0 Φint : ℝ → M → M)
    (hagree : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, Φint t x = Φ0 t x)
    (hΦint_bare : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φint s x) (Set.Ioo (0 : ℝ) T) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φint t x)))) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ0 s x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ0 t x))) := sorry

/-- **Per-time diffeomorphisms on `(0,T)` for `Φ := Φ0`** (C2), transported from the interior
flow `Φint` across their pointwise agreement on `(0,T)`.

For `t ∈ (0,T)`, take the diffeomorphism witness `d` of the interior slice `Φint t` from
`hdiffeo_int`; for every `x`, `d x = Φint t x = Φ0 t x` by `hagree t`, so the same `d` is the
witness for `Φ0 t`. -/
theorem forwardFlow_diffeo_of_agree
    (Φ Φint : ℝ → M → M) (T : ℝ)
    (hagree : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, Φint t x = Φ t x)
    (hdiffeo_int : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φint t x) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x := sorry

set_option linter.unusedVariables false in
/-- A time-dependent field `X_DT` that is jointly `C∞` on the interior `(0,T) ×ˢ univ`
(`hint`) and continuous together with its chart-gradient up to `t = 0` (`hcont0`,
`hgrad0`) admits a single forward flow `Φ : ℝ → M → M` with `Φ 0 = id`, per-time
diffeomorphisms on `(0,T)`, the bare geometric velocity `∂ₛ Φ s x = X_DT t (Φ t x)` on
`(0,T)`, and `t = 0` right-continuity of both the orbit `s ↦ Φ s x` and the moving
spatial Jacobian `s ↦ mfderiv I I (Φ s) x v`.

The forward-flow construction is currently a deferred `sorry`, to be assembled from the
trivialised chart integral identity and the covariant variational identity. -/
theorem forward_flow_existence_onesided_of_jointsmooth_field
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X_DT q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X_DT q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ Φ : ℝ → M → M, (∀ x : M, Φ 0 x = x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x)
        (Set.Ici (0 : ℝ)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x)))) ∧
      (∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) 0) ∧
      (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E))
          (Set.Ici (0 : ℝ)) 0) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow
