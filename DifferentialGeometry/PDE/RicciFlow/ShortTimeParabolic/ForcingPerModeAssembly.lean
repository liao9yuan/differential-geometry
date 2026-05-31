/-
Interior continuity of the DeTurck geometric forcing (M2) and the term-by-term
per-mode assembly of the interior time-derivative (M3). Skeleton stubs for the
short-time-existence blueprint (GAP 1, spectral M2/M3).
-/
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

set_option linter.unusedVariables false in
/-- **Interior continuity of the continuous DeTurck forcing.**

Re-anchored away from the finite-support-gated `deTurckGeometricN` (globally
discontinuous: it jumps to `0` off the non-open finite-support locus, so
`s ↦ deTurckGeometricN g_bg a (u₁ s)` is genuinely discontinuous on the infinite-
support path) onto the *same* continuous realize-based nonlinearity `N_cont` as
in `deturckN_hscale_lipschitz` (binder/construction shape kept IDENTICAL).

As in `permode_sum_hasderivat`, the order-`(a+1)` carrier `u₁` is anchored to an
order-`(a+2)` lift `u₂` via `hu₁`, so the solution field's continuity in the
higher norm is available. The construction data `N_cont`, `repr`, `Nsec` and the
construction/realize-identity hypotheses `hN_coeff`, `hNsec_realize`,
`hrepr_small` are exactly those of `deturckN_hscale_lipschitz` (the *same*
continuous nonlinearity): coordinate/realize identities about `N_cont`'s
coordinates and `Nsec`'s bilinear extraction, NOT the continuity conclusion. The
`hcont`/`hball` hypotheses confine the carrier to the ball where the realize
construction is valid.

The conclusion is the continuity of `s ↦ N_cont (u₁ s)` (the *continuous*
nonlinearity), which is TRUE and dependency-sufficient: it composes the global
continuity of the continuous nonlinearity `N_cont` (carried as the dischargeable
hypothesis `hN_cont`, supplied downstream at the construction of `N_cont` from
the linear realize `ccTensorBilinSymm` — see `deturckN_hscale_lipschitz`, which
already proves `N_cont` Lipschitz on every ball, hence continuous) with the
interior continuity of the carrier `u₁` (`hcont`).

`repr`, `Nsec`, `hN_coeff`, `hNsec_realize`, `hrepr_small`, `hball` are carried
to keep the binder shape identical to `deturckN_hscale_lipschitz` for the
blueprint dependency contract; the composition argument here needs only the
global continuity `hN_cont` and the carrier continuity `hcont`, so the narrow
unused-variable linter suppression keeps the signature intact and warning-free. -/
theorem forcing_continuous_interior
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (u₁ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2)) (R : ℝ)
    (hu₁ : ∀ s, u₁ s = tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
    (N_cont : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (hN_cont : Continuous N_cont)
    (repr : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2)
    (Nsec : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2)
    (hN_coeff : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (N_cont u).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
          (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
    (hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g_bg (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g_bg (repr u) x v w)
    (hrepr_small : ∀ u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1),
      ∃ δ' : ℝ, δ' < 1 ∧
        gFibreOpBound (I := I) (M := M) g_bg
          (ccTensorBilinSymm (I := I) g_bg (repr u)) δ')
    (hcont : ∀ ε : ℝ, 0 < ε → ContinuousOn u₁ (Set.Icc ε T))
    (hball : ∀ ε : ℝ, 0 < ε → ∀ s ∈ Set.Icc ε T,
      u₁ s ∈ Metric.closedBall
        (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
          (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) u₀) R) :
    ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun s => (N_cont (u₁ s) :
        tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))) (Set.Icc ε T) := by
  -- The interior carrier `u₁` is continuous on `[ε, T]` (`hcont`); the continuous
  -- DeTurck nonlinearity `N_cont` is globally continuous (`hN_cont`); their
  -- composition `s ↦ N_cont (u₁ s)` is therefore continuous on `[ε, T]`.
  intro ε hε
  exact hN_cont.comp_continuousOn (hcont ε hε)

-- `hu₂`, `hu₁`, `hu`, `hu₂sol`, `hforce` are the carried Duhamel-structure
-- hypotheses pinning the carrier `u`/`u₂`/`u₁` to the affine Duhamel solution
-- field and the forcing to the continuous DeTurck nonlinearity; they feed sibling
-- nodes and the blueprint dependency contract. The interior `HasDerivAt`
-- conclusion is discharged from the two genuine interior-smoothing inputs
-- `hderiv_ae` (the a.e. identity of the *L²* time-derivative field `u.deriv` with
-- the spectral RHS — derived downstream from `maxRegDuhamelMap_timeDeriv_eq`) and
-- `hRHS_cont` (interior continuity of the spectral RHS *path*). Neither input is
-- the conclusion: `hderiv_ae`/`hRHS_cont` are statements about `u.deriv` and the
-- RHS path's continuity, structurally distinct from the differentiability of the
-- represented path `timeH1.toFun u`. The remaining Duhamel hypotheses are unused
-- in THIS reduction (they pin the same data the two inputs already encode), so the
-- narrow unused-variable linter suppression keeps the signature intact.
open MeasureTheory in
set_option linter.unusedVariables false in
theorem permode_sum_hasderivat
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ) {T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
    (u₂ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (u₁ : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (hu : u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce)
    (hu₂sol : ∀ s, u₂ s =
      maxRegDuhamelSolField (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce s)
    (hforce : gforce =ᵐ[timeMeasure T]
      (fun t => deTurckGeometricN (I := I) g_bg a
        (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce t)))
    (hu₂ : ∀ s, tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) (u₂ s) = timeH1.toFun u s)
    (hu₁ : ∀ s, u₁ s = tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
      (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) (u₂ s))
    (hderiv_ae : (u.deriv : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
        =ᵐ[timeMeasure T]
      (fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
        deTurckGeometricN (I := I) g_bg a (u₁ s)))
    (hRHS_cont : ContinuousOn
      (fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
        deTurckGeometricN (I := I) g_bg a (u₁ s)) (Set.Ioo (0 : ℝ) T)) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun r => (timeH1.toFun u r : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)))
        (scaleLaplacianFun (I := I) (M := M) (u₂ s) +
          deTurckGeometricN (I := I) g_bg a (u₁ s)) s := by
  classical
  -- Abbreviate the spectral RHS path.
  set RHS : ℝ → tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) :=
    fun s => scaleLaplacianFun (I := I) (M := M) (u₂ s) +
      deTurckGeometricN (I := I) g_bg a (u₁ s) with hRHS_def
  intro s hs
  obtain ⟨hs0, hsT⟩ := hs
  have hsmem : s ∈ Set.Ioo (0 : ℝ) T := ⟨hs0, hsT⟩
  have hTpos : (0 : ℝ) ≤ T := hs0.le.trans hsT.le
  -- `timeH1.toFun u r = u.init + ∫₀ʳ u.deriv`.
  -- The indefinite integral of the continuous RHS-representative has the FTC
  -- derivative `RHS s` at the interior point `s`; we then transfer along the a.e.
  -- equality `u.deriv =ᵐ RHS` to the indefinite integral of `u.deriv`.
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hTpos⟩
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs0.le, hsT.le⟩
  -- `u.deriv` is interval-integrable on `0..s` (it is the `L²` derivative field).
  have hderiv_int : IntervalIntegrable (fun r => u.deriv r) volume 0 s :=
    u.intervalIntegrable_deriv h0mem hsIcc
  -- The RHS representative is interval-integrable on `0..s` (a.e.-equal to `u.deriv`).
  have hRHS_int : IntervalIntegrable RHS volume 0 s := by
    -- `u.deriv =ᵐ RHS` over `timeMeasure T` ⟹ over `volume.restrict (uIoc 0 s)`.
    have hsub : Set.uIoc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (Set.uIcc_subset_Icc h0mem hsIcc)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv_ae
    exact hderiv_int.congr_ae hae
  -- The RHS representative is continuous at `s` (continuous on the open `(0,T)`).
  have hRHS_at : ContinuousAt RHS s :=
    hRHS_cont.continuousAt (isOpen_Ioo.mem_nhds hsmem)
  -- It is strongly measurable at `𝓝 s` (continuous on the open neighbourhood `(0,T)`).
  have hRHS_meas : StronglyMeasurableAtFilter RHS (𝓝 s) volume :=
    hRHS_cont.stronglyMeasurableAtFilter isOpen_Ioo s hsmem
  -- FTC for the continuous RHS representative: `(∫₀· RHS)' s = RHS s`.
  have hftc_RHS : HasDerivAt (fun r => ∫ x in (0 : ℝ)..r, RHS x) (RHS s) s :=
    intervalIntegral.integral_hasDerivAt_right hRHS_int hRHS_meas hRHS_at
  -- Near `s`, the indefinite integral of `u.deriv` equals that of `RHS`.
  have heq : (fun r => ∫ x in (0 : ℝ)..r, u.deriv x)
      =ᶠ[nhds s] fun r => ∫ x in (0 : ℝ)..r, RHS x := by
    filter_upwards [Ioo_mem_nhds hs0 hsT] with r hr
    refine intervalIntegral.integral_congr_ae ?_
    have hrIcc : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
    have hsub : Set.uIoc (0 : ℝ) r ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (Set.uIcc_subset_Icc h0mem hrIcc)
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv_ae
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with x hx hxmem
    exact hx hxmem
  -- Transfer the FTC derivative back to the indefinite integral of `u.deriv`.
  have hftc_u : HasDerivAt (fun r => ∫ x in (0 : ℝ)..r, u.deriv x) (RHS s) s :=
    hftc_RHS.congr_of_eventuallyEq heq
  -- Add the constant initial value: `toFun u r = u.init + ∫₀ʳ u.deriv` (`toFun_apply`),
  -- so the goal's path is definitionally `fun r => u.init + ∫₀ʳ u.deriv`.
  have hconst : HasDerivAt
      (fun r => (timeH1.toFun u r : tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)))
      (RHS s) s := by
    have h := hftc_u.const_add u.init
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with r
    rw [timeH1.toFun_apply]
  exact hconst

end DifferentialGeometry.PDE.RicciFlow
