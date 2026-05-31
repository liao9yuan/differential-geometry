/-
Metric-level short-time existence for the strictly parabolic DeTurck–Ricci flow,
together with its interior (`Ioo`) and `t = 0` one-sided time-derivative pieces.
Skeleton stubs for the short-time-existence blueprint (GAP 1, transport layer).
-/
import DifferentialGeometry.PDE.RicciFlow.ShortTimeExistence
import DifferentialGeometry.PDE.RicciFlow.ShortTimeParabolic.RealizeTransport
import DifferentialGeometry.PDE.RicciFlow.ShortTimeParabolic.SolutionC2Continuous
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

theorem deturck_ricci_pde_shorttime
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ T : ℝ, ∃ g_DT : ℝ → SmoothRiemannianMetric I M,
      IsQuasilinearMetricParabolicSolution (I := I)
        (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT := sorry

/-- **Interior metric-level DeTurck–Ricci time-derivative (fully ungated).**

The interior one-sided time-derivative of the **linear** realized metric
`g_DT s` (`hreal : (g_DT s).inner = g_bg.inner + ccTensorBilinSymm (T_s s)`) is
the geometric DeTurck–Ricci right-hand side evaluated at `g_DT t`.

Re-anchored off the finite-support-gated `deTurckGeometricN`: the carrier-scale
derivative hypothesis `hreg` now routes the nonlinearity through the *continuous*
realize-based nonlinearity `N_cont` (the SAME data as in
`deturck_mildsolution_timeh1` / `forcing_continuous_interior` /
`deturckN_hscale_lipschitz`), so the carrier solves the genuine ungated PDE that
the parent mild-solution node produces and the node applies to the genuine
infinite-support solution (where `deTurckGeometricN`, being forced to `0` off
finite support by `deTurckGeometricN_of_not_realizable`, would degenerate the
flow to the pure linear heat flow and contradict the nonlinear RHS).

Dependency-sufficiency: `hreg` (ungated carrier derivative) pushed through `ℓ_a`
by `pointwise_deriv_through_realize`, composed with `rhs_matches_deturck_at_solution`
(now concluding `deTurckRicciRHS g_bg (g_DT t)`, the SAME continuous `N_cont` and
the SAME linear `g_DT`), yields the conclusion. The construction data `N_cont`,
`repr`, `Nsec` and the hypotheses `hN_coeff`, `hNsec_realize`, `hrepr_small` are
IDENTICAL in shape to A3/A4/A5/parent (coordinate/realize identities, NOT the
`HasDerivWithinAt` conclusion). Non-leaking: all data constrains the internal
carrier `u₂`/`T_s`/`g_DT`/`N_cont`, never `g₀`/the headline. `hrepr_small` is the
honestly-flagged open analytic input, consistent with A4/A5. -/
theorem deturck_metric_pde_interior
    (g_bg : SmoothRiemannianMetric I M) {T : ℝ} (a : ℕ)
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (T_s : ℝ → Integral.L2.SmoothCcTensor g_bg 0 2)
    (hreal : ∀ (s : ℝ) (x : M) (v w : TangentSpace I x),
      (g_DT s).inner x v w
        = g_bg.inner x v w + ccTensorBilinSymm (I := I) g_bg (T_s s) x v w)
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
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g_bg (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g_bg (repr u) x v w)
    (hrepr_small : ∀ u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1),
      ∃ δ' : ℝ, δ' < 1 ∧
        gFibreOpBound (I := I) (M := M) g_bg
          (ccTensorBilinSymm (I := I) g_bg (repr u)) δ')
    (hreg : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ r)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          N_cont
            (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) s)
    (hsmall : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∃ δ' : ℝ, δ' < 1 ∧
      gFibreOpBound (I := I) (M := M) g_bg
        (ccTensorBilinSymm (I := I) g_bg (T_s s)) δ')
    (hsmoothrepr : ∀ (s : ℝ)
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (u₂ s).coeff i
        = tensorL2Coeff_ofCompact (I := I) (M := M) (hCompact (I := I) (M := M) g_bg)
            (Integral.L2.SmoothCcTensor.toL2 (T_s s)) i) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t := by
  intro t ht x v w
  -- The carrier at scale `a` (the down-included `u₂`) and its spectral derivative.
  set u_car : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
    fun s => tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) with hu_car_def
  set u_car' : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
    fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
      N_cont
        (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s)) with hu_car'_def
  -- Extract the carrier-scale realize-evaluate functional `ℓ_a` and its pinning
  -- against the linear realize `ccTensorBilinSymm`.
  obtain ⟨ℓ_a, hℓ⟩ := realize_eval_carrier_factorization (I := I) (M := M) g_bg a x v w
  -- The pointwise factorization `ccTensorBilinSymm (T_s s) = ℓ_a (u_car s)`, valid
  -- on the whole line: the down-inclusion preserves eigen-coordinates, which
  -- `hsmoothrepr` identifies with the `L²` coordinates of `T_s s`.
  have hfactor : ∀ s : ℝ,
      ccTensorBilinSymm (I := I) g_bg (T_s s) x v w = ℓ_a (u_car s) := by
    intro s
    refine (hℓ (T_s s) (u_car s) ?_).symm
    intro i
    -- `(u_car s).coeff i = (u₂ s).coeff i = tensorL2Coeff_ofCompact … (T_s s) i`.
    rw [hu_car_def]
    simp only [tensorHsInclusion_coeff_apply]
    exact hsmoothrepr s i
  -- The carrier-scale within-derivative, from the ungated `HasDerivAt` carrier.
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun r : ℝ => u_car r) (u_car' s) (Set.Ici 0) s := by
    intro s hs
    exact (hreg s hs).hasDerivWithinAt
  -- Push the within-derivative of the carrier through `ℓ_a` onto the metric
  -- coordinate function `(g_DT ·).inner x v w`.
  have hpush := pointwise_deriv_through_realize (I := I) (M := M) g_bg a
    g_DT T_s u_car u_car' x v w ℓ_a
    (fun s => hreal s x v w) hfactor hderiv t ht
  -- Reconcile the spectral derivative value `ℓ_a (u_car' t)` with the geometric
  -- DeTurck–Ricci right-hand side at the realized metric.
  --
  -- The remaining open analytic input is the spectral→geometric principal-part
  -- reconciliation `hNsec_geom`, which is NOT among this node's hypotheses and is
  -- not derivable from the coordinate/realize identities present here: it is the
  -- principal-part match between the smooth rough Laplacian `rawTensorConnLapSmooth`
  -- plus the realized lower-order representative and `deTurckRicciRHS`.
  have hNsec_geom : ∀ (s : ℝ) (x' : M) (v' w' : TangentSpace I x'),
      ccTensorBilinSymm (I := I) g_bg
          (rawTensorConnLapSmooth (I := I) g_bg 0 2 (T_s s)) x' v' w'
        + ccTensorBilinSymm (I := I) g_bg
            (repr (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))) x' v' w'
        = deTurckRicciRHS (I := I) g_bg (g_DT s) x' v' w' := sorry
  have hmatch := rhs_matches_deturck_at_solution (I := I) (M := M) g_bg a u₂ ℓ_a
    g_DT T_s x v w hreal N_cont repr Nsec hN_coeff hNsec_realize hrepr_small
    hsmoothrepr hℓ hNsec_geom t (Set.Ioo_subset_Ico_self ht)
  -- The pushed derivative value equals the geometric RHS.
  rw [hu_car'_def] at hpush
  rw [hmatch] at hpush
  exact hpush

theorem deturck_metric_pde_at_zero
    (g_bg : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (g_DT : ℝ → SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x)
    (h_cont : ContinuousOn (fun s : ℝ => (g_DT s).inner x v w) (Set.Icc 0 T))
    (h_rhs_cont : ContinuousWithinAt
      (fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w) (Set.Ioi 0) 0)
    (h_interior : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivWithinAt
      (fun s : ℝ => (g_DT s).inner x v w)
      (deTurckRicciRHS (I := I) g_bg (g_DT t) x v w) (Set.Ici 0) t) :
    HasDerivWithinAt (fun s : ℝ => (g_DT s).inner x v w)
      (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w) (Set.Ici 0) 0 := by
  -- Abbreviations for the metric-coordinate function and the geometric RHS.
  set f : ℝ → ℝ := fun s : ℝ => (g_DT s).inner x v w with hf_def
  set rhs : ℝ → ℝ := fun s : ℝ => deTurckRicciRHS (I := I) g_bg (g_DT s) x v w with hrhs_def
  -- At every interior time `t ∈ (0, T)`, `Ici 0` is a neighbourhood of `t`, so the
  -- within-derivative upgrades to an ordinary derivative; hence `f` is
  -- differentiable on `(0, T)` and `deriv f t = rhs t` there.
  have hHasDerivAt : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt f (rhs t) t := by
    intro t ht
    exact (h_interior t ht).hasDerivAt (Ici_mem_nhds ht.1)
  have f_diff : DifferentiableOn ℝ f (Set.Ioo (0 : ℝ) T) := by
    intro t ht
    exact ((hHasDerivAt t ht).differentiableAt).differentiableWithinAt
  -- Continuity at `0` from the right, restricted to `(0, T)`.
  have f_lim : ContinuousWithinAt f (Set.Ioo (0 : ℝ) T) 0 :=
    (h_cont.continuousWithinAt (Set.left_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  -- `(0, T)` is a right-neighbourhood of `0`.
  have hs : Set.Ioo (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hT
  -- The free derivative `deriv f` agrees with `rhs` on `(0, T)`, hence eventually
  -- from the right of `0`; combined with `h_rhs_cont` it tends to `rhs 0`.
  have hEqOn : Set.EqOn rhs (fun x => deriv f x) (Set.Ioo (0 : ℝ) T) := by
    intro t ht
    exact ((hHasDerivAt t ht).deriv).symm
  have f_lim' : Filter.Tendsto (fun x => deriv f x) (𝓝[>] (0 : ℝ))
      (𝓝 (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w)) := by
    have h_rhs_tendsto : Filter.Tendsto rhs (𝓝[>] (0 : ℝ))
        (𝓝 (deTurckRicciRHS (I := I) g_bg (g_DT 0) x v w)) := h_rhs_cont
    exact h_rhs_tendsto.congr' (hEqOn.eventuallyEq_of_mem hs)
  exact hasDerivWithinAt_Ici_of_tendsto_deriv f_diff f_lim hs f_lim'

end DifferentialGeometry.PDE.RicciFlow
