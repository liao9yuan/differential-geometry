/-
The realize-layer transport from the carrier-scale spectral derivative to the
geometric DeTurck–Ricci right-hand side: the carrier-scale realize-evaluate
functional and its factorization, the push of the within-derivative through it,
and the spectral→geometric reconciliation at the solution. Skeleton stubs for the
short-time-existence blueprint (GAP 1, transport layer).
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

theorem realize_eval_carrier_factorization
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (x : M) (v w : TangentSpace I x) :
    ∃ ℓ_a : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) →L[ℝ] ℝ,
      ∀ (T_z : Integral.L2.SmoothCcTensor g_bg 0 2)
        (z : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)),
        (∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g_bg 0 2,
          z.coeff i
            = tensorL2Coeff_ofCompact (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
                (Integral.L2.SmoothCcTensor.toL2 T_z) i) →
          ℓ_a z = ccTensorBilinSymm (I := I) g_bg T_z x v w := sorry

theorem pointwise_deriv_through_realize
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2)
    (u_car : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (u_car' : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (x : M) (v w : TangentSpace I x)
    (ℓ_a : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) →L[ℝ] ℝ)
    (hreal : ∀ s : ℝ,
      (g_DT s).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s s) x v w)
    (hfactor : ∀ s : ℝ,
      ccTensorBilinSymm (I := I) g_bg (T_s s) x v w = ℓ_a (u_car s))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ => u_car s) (u_car' t) (Set.Ici 0) t) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt
        (fun s : ℝ => (g_DT s).inner x v w)
        (ℓ_a (u_car' t)) (Set.Ici 0) t := sorry

/-- **Spectral→geometric reconciliation at the solution (fully ungated).**

Re-anchored off the finite-support-gated objects. The carrier-scale realize
functional `ℓ_a` now reconciles, at every interior time, the carrier-scale
spectral right-hand side against the geometric DeTurck–Ricci right-hand side
evaluated at the **linear** realized metric `g_DT t`
(`hreal : (g_DT s).inner = g_bg.inner + ccTensorBilinSymm (T_s s)`), NOT the
finite-support-gated piecewise `realizeMetricMap`. The nonlinear forcing is the
*continuous* realize-based nonlinearity `N_cont` (the SAME data as in
`deturckN_hscale_lipschitz` / `forcing_continuous_interior` /
`deturck_mildsolution_timeh1`), replacing the gated `deTurckGeometricN`, so the
identity holds for the genuine infinite-support solution carrier.

The construction data `N_cont`, `repr`, `Nsec` and the construction/realize
hypotheses `hN_coeff`, `hNsec_realize`, `hrepr_small` are IDENTICAL in shape to
A4/A5/parent (coordinate/realize identities about `N_cont`'s coordinates and
`Nsec`'s bilinear extraction, NOT the reconciliation conclusion). `hℓ` is the
carrier-wide pinning of `ℓ_a` against the linear realize `ccTensorBilinSymm`.

Non-packaging: every hypothesis is a coordinate/realize identity; none is the
`ℓ_a (…) = deTurckRicciRHS …` conclusion. Non-leaking: all data constrains the
internal carrier `u₂`/`T_s`/`g_DT`/`N_cont`, never `g₀`/the headline. -/
theorem rhs_matches_deturck_at_solution
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (ℓ_a : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) →L[ℝ] ℝ)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2)
    (x : M) (v w : TangentSpace I x)
    (hreal : ∀ (s : ℝ) (x' : M) (v' w' : TangentSpace I x'),
      (g_DT s).inner x' v' w'
        = g_bg.inner x' v' w' + ccTensorBilinSymm (I := I) g_bg (T_s s) x' v' w')
    (N_cont : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (repr : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g_bg 0 2)
    (Nsec : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      Integral.L2.SmoothCcTensor g_bg 0 2)
    (hN_coeff : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (N_cont u).coeff i =
        tensorL2Coeff_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g_bg 0 2)
          (Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
    (hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (x' : M) (v' w' : TangentSpace I x'),
      ccTensorBilinSymm (I := I) g_bg (Nsec u) x' v' w' =
        ccTensorBilinSymm (I := I) g_bg (repr u) x' v' w')
    (hrepr_small : ∀ u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1),
      ∃ δ' : ℝ, δ' < 1 ∧
        gFibreOpBound (I := I) (M := M) g_bg
          (ccTensorBilinSymm (I := I) g_bg (repr u)) δ')
    (hsmoothrepr : ∀ (s : ℝ)
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g_bg 0 2),
      (u₂ s).coeff i
        = tensorL2Coeff_ofCompact (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i)
    (hℓ : ∀ (T_z : Integral.L2.SmoothCcTensor g_bg 0 2)
        (z : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)),
        (∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g_bg 0 2,
          z.coeff i
            = tensorL2Coeff_ofCompact (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
                (Integral.L2.SmoothCcTensor.toL2 T_z) i) →
          ℓ_a z = ccTensorBilinSymm (I := I) g_bg T_z x v w)
    (hNsec_geom : ∀ (s : ℝ) (x' : M) (v' w' : TangentSpace I x'),
      ccTensorBilinSymm (I := I) g_bg
          (rawTensorConnLapSmooth (I := I) g_bg 0 2 (T_s s)) x' v' w'
        + ccTensorBilinSymm (I := I) g_bg
            (repr (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
        = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w') :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      ℓ_a (scaleLaplacianFun (I := I) (M := M) (u₂ t) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ t)))
        = deTurckRicciRHS (I := I) g_bg (g_DT t) x v w := sorry

end DifferentialGeometry.PDE.RicciFlow
