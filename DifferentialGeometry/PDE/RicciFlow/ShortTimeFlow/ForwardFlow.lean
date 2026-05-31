/-
The forward (one-sided, from `t = 0`) jointly-smooth flow of the interior DeTurck
field, and the `t = 0` right-continuity extension of the flow and its pushforward.
Skeleton stubs for the short-time-existence blueprint (GAP 2, forward flow).
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

theorem forward_flow_jointsmooth_onesided
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
  -- ROUTE (cutoff multi-window glue → bare interior flow → diffeomorphism family →
  -- t=0 continuity extension), and the precise PARTIAL stop point.
  --
  -- Conjunct 3 (bare velocity for ALL `t ∈ (0,T)`) requires a SINGLE global flow `Φ`
  -- carrying `X_DT`'s geometric velocity on the whole open horizon `(0,T)`.  The field
  -- `X_DT` is only jointly `C∞` on `(0,T) ×ˢ univ` (`hint`), so no single time-cutoff
  -- field `Xt = cutoffEta a b δ • X_DT` (`interior_field_global_cutoff_extension`) can
  -- equal `X_DT` on all of `(0,T)`: a cutoff supported in `[a-2δ, b+2δ] ⊂ (0,T)` vanishes
  -- near both endpoints.  The honest construction is the per-interior-point cutoff glue:
  -- for each `t₀ ∈ (0,T)` a window `Ioo a b ∋ t₀` with `Xt = X_DT` there and
  -- `AutonomizedFieldJointC1 Xt`; the global bare flow of `Xt`
  -- (`h3_global_flow_jointContMDiffOn_on_closed_manifold` / cutoff route through
  -- `time_dependent_vf_globalflow_on_closed_mfd`) carries `X_DT`'s bare velocity on that
  -- window; the per-window flows are glued into one `Φ` on `(0,T)` by bare-flow
  -- uniqueness (`bare_integral_flow_eqOn_of_jointC1`), exactly the clopen/preconnected
  -- patching of the sibling `flow_family_identification` but at the level of CONSTRUCTING
  -- (not identifying) the flow.  The per-time diffeomorphism witnesses (conjunct 2) then
  -- come from `time_dependent_vf_diffeomorph_family_of_smooth_bijective`, and conjuncts
  -- 4/5 (t=0 right-continuity of the orbit and the moving mfderiv) from the sibling
  -- `flow_t0_continuity_extension` (whose conjunct-5 moving-mfderiv continuity is itself
  -- the open variational-flow endpoint, isolated below).
  --
  -- MISSING INFRA (no such producer on disk; existence search logged in the report):
  -- a "global bare flow on `(0,T)` of an interior-`C∞`-only time-dependent field" lemma
  --   `(hint : ContMDiffOn … (Ioo 0 T ×ˢ univ)) →
  --      ∃ Φ, (∀ x, Φ 0 x = x) ∧
  --        (∀ t ∈ Ioo 0 T, ∀ x, HasMFDerivWithinAt 𝓘(ℝ,ℝ) I (fun s => Φ s x) (Ici 0) t
  --          (𝟙.smulRight (X_DT t (Φ t x)))) ∧ (chart-Picard integral anchor `hpicard`)`.
  -- All existing global producers (`h3_global_flow_jointContMDiffOn_on_closed_manifold`,
  -- `time_dependent_vf_globalflow_on_closed_mfd`) require GLOBAL (`ℝ × M`) smoothness or
  -- chart-local Picard data for the genuine field, neither available from interior-only
  -- `hint`.  This multi-window construction is the remaining work; it is left here as a
  -- single labeled `sorry` (PARTIAL), pending that producer.
  sorry

/-- **Orbit right-continuity at `t = 0`.**

Self-contained helper for the first conjunct of `flow_t0_continuity_extension`.
Fix `x : M`.  By `hpicard` the orbit `s ↦ Φ s x` satisfies, on a right-half
neighbourhood `Ico 0 (min δ T)` of `0`, the chart-Picard integral identity
`extChartAt I α (Φ s x) = extChartAt I α x + ∫₀ˢ chartRawRepr α (X_DT r) (extChartAt I α (Φ r x))`.
The integrand equals `(X_DT r (Φ r x) : E)` (after rewriting through the chart
inverse on the orbit, which stays in the chart source), and is bounded by a constant
`C` near `0` because `(t, y) ↦ X_DT t y` is continuous on the compact set
`Icc 0 T ×ˢ univ` (compactness of `M`).  Hence the chart image of the orbit differs
from `extChartAt I α x` by an integral of norm `≤ C·|s|`, which tends to `0` as
`s → 0⁺`; composing with the continuous chart inverse and using `Φ 0 x = x` gives
right-continuity of the orbit at `0`. -/
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
              chartRawRepr (I := I) α (X_DT r) (extChartAt I α (Φ r x))) :
    ∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) 0 := by
  intro x
  obtain ⟨α, δ, hδ, hxsrc, hpic⟩ := hpicard x
  -- The model-space coordinate of the basepoint.
  set z₀ : E := extChartAt I α x with hz₀
  -- `x` lies in the extended-chart source.
  have hxsrc' : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hxsrc
  -- A uniform bound `C` on `‖X_DT t y‖` over the compact `Icc 0 T ×ˢ univ`.
  have hKcompact : IsCompact (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) :=
    (isCompact_Icc).prod isCompact_univ
  obtain ⟨C, hC⟩ :=
    hKcompact.exists_bound_of_continuousOn (f := fun q : ℝ × M =>
      (X_DT q.1 q.2 : TangentSpace I q.2)) hcont0
  -- `min δ T` is positive.
  have hδT : (0 : ℝ) < min δ T := lt_min hδ hT
  -- On `Ico 0 (min δ T)`, the chart image of the orbit equals `z₀` plus an
  -- integral of norm `≤ C·|s|`.
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
      ‖extChartAt I α (Φ s x) - z₀‖ ≤ C * |s| := by
    intro s hs
    obtain ⟨hΦsrc_s, hident⟩ := hpic s hs
    rw [hident, add_sub_cancel_left]
    -- `‖∫ r in 0..s, F r‖ ≤ C·|s - 0|` from a pointwise bound on `Ι 0 s`.
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := s) (C := C)
      (f := fun r : ℝ => chartRawRepr (I := I) α (X_DT r) (extChartAt I α (Φ r x)))
      (fun r hr => ?_)
    · simpa using hnorm
    -- Pointwise bound on `r ∈ Ι 0 s ⊆ Ico 0 (min δ T)`.
    · -- `r` lies in `Ioc 0 s`, hence in `Ico 0 (min δ T)`.
      rw [Set.uIoc_of_le hs.1] at hr
      have hr_mem : r ∈ Set.Ico (0 : ℝ) (min δ T) :=
        ⟨le_of_lt hr.1, lt_of_le_of_lt hr.2 hs.2⟩
      obtain ⟨hΦsrc_r, _⟩ := hpic r hr_mem
      -- `r ∈ Icc 0 T`.
      have hrT : r ∈ Set.Icc (0 : ℝ) T :=
        ⟨le_of_lt hr.1, le_of_lt (lt_of_lt_of_le hr_mem.2 (min_le_right _ _))⟩
      -- The integrand at `r` equals `(X_DT r (Φ r x) : E)`.
      have hΦsrc_r' : Φ r x ∈ (extChartAt I α).source := by
        rw [extChartAt_source]; exact hΦsrc_r
      have heq : chartRawRepr (I := I) α (X_DT r) (extChartAt I α (Φ r x))
          = (X_DT r (Φ r x) : E) := by
        unfold chartRawRepr
        rw [(extChartAt I α).left_inv hΦsrc_r']
      change ‖chartRawRepr (I := I) α (X_DT r) (extChartAt I α (Φ r x))‖ ≤ C
      rw [heq]
      have := hC (r, Φ r x) ⟨hrT, Set.mem_univ _⟩
      simpa using this
  -- The chart image of the orbit tends to `z₀` as `s → 0⁺`.
  have htendsto : Filter.Tendsto (fun s : ℝ => extChartAt I α (Φ s x))
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 z₀) := by
    -- Reduce to `Tendsto (· - z₀) → 𝓝 0` by the sandwich, then add back `z₀`.
    have htsub : Filter.Tendsto
        (fun s : ℝ => extChartAt I α (Φ s x) - z₀) (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun s : ℝ => C * |s|) ?_ ?_
      · -- Eventually on `Ici 0` (in fact on `Ico 0 (min δ T)`) the bound holds.
        have hmem : Set.Ico (0 : ℝ) (min δ T) ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := by
          refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
            (nhdsWithin_le_nhds (Iio_mem_nhds hδT))) (fun s hs => ?_)
          exact ⟨hs.1, hs.2⟩
        filter_upwards [hmem] with s hs using hbound s hs
      · -- `C·|s| → 0`.
        have hcontmul : Continuous (fun s : ℝ => C * |s|) := by fun_prop
        have := (hcontmul.tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ici (0 : ℝ)))
        simpa using this
    have := htsub.add (tendsto_const_nhds (x := z₀)
      (f := 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)))
    simpa using this
  have hchart_cont :
      ContinuousWithinAt (fun s : ℝ => extChartAt I α (Φ s x)) (Set.Ici (0 : ℝ)) 0 := by
    have hval : extChartAt I α (Φ 0 x) = z₀ := by rw [hΦ0, hz₀]
    rw [ContinuousWithinAt, hval]
    exact htendsto
  -- Compose with the continuous chart inverse and identify the orbit.
  have hmemtgt : z₀ ∈ (extChartAt I α).target := by
    rw [hz₀]; exact (extChartAt I α).map_source hxsrc'
  have hcont_symm : ContinuousAt (extChartAt I α).symm z₀ :=
    continuousAt_extChartAt_symm'' hmemtgt
  have hsymm_cont :
      ContinuousWithinAt
        (fun s : ℝ => (extChartAt I α).symm (extChartAt I α (Φ s x)))
        (Set.Ici (0 : ℝ)) 0 := by
    have hval0 : extChartAt I α (Φ 0 x) = z₀ := by rw [hΦ0, hz₀]
    exact hcont_symm.comp_continuousWithinAt_of_eq hchart_cont hval0
  -- Identify the composite with `Φ s x` on `Ici 0` near `0` and at `0`.
  have hmem' : Set.Ico (0 : ℝ) (min δ T) ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := by
    refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Iio_mem_nhds hδT))) (fun s hs => ?_)
    exact ⟨hs.1, hs.2⟩
  refine hsymm_cont.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hmem'] with s hs
    obtain ⟨hΦsrc_s, _⟩ := hpic s hs
    have hΦsrc_s' : Φ s x ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact hΦsrc_s
    exact ((extChartAt I α).left_inv hΦsrc_s').symm
  · -- At `0`: `Φ 0 x = x ∈ source`.
    simp only [hΦ0]
    exact ((extChartAt I α).left_inv hxsrc').symm

theorem flow_t0_continuity_extension
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
          (Set.Ici (0 : ℝ)) 0) := by
  refine ⟨flow_orbit_continuousWithinAt_zero X_DT T hT Φ hΦ0 hcont0 hpicard, ?_⟩
  -- ALLOWED GAP (variational-flow endpoint): moving-spatial-Jacobian right-continuity at
  -- `t = 0`, i.e. `ContinuousWithinAt (s ↦ mfderiv I I (Φ s) x v) (Ici 0) 0`.
  --
  -- This is the smooth-dependence-on-initial-conditions ENDPOINT statement.  The map
  -- `s ↦ mfderiv (Φ s) x v` solves the linearised (variational) flow whose coefficient is
  -- the spatial Jacobian `∇(chartRawRepr X_DT)` (the continuity of which up to `0` is
  -- exactly `hgrad0`); its right-limit at `0` is governed by that Jacobian being
  -- continuous up to `0`.  Deriving it needs the linearised-flow INTEGRAL equation up to
  -- `0`, for which the only in-signature anchor (`hpicard`) is for the ORBIT, not the
  -- spatial Jacobian.
  --
  -- MISSING INFRA (existence search logged in the report — not on disk):
  --   `variational_flow_mfderiv_continuousWithinAt_zero`
  --     (hΦ0 : ∀ x, Φ 0 x = x) (hinterior : … bare ODE on Ici 0)
  --     (hgrad0 : … spatial-Jacobian continuity up to 0)
  --     (hpicard-style variational integral anchor for `mfderivWithin`) :
  --     ∀ x v, ContinuousWithinAt (fun s => (mfderiv I I (Φ s) x v : E)) (Ici 0) 0
  -- The on-disk smooth-dependence stack (`SmoothDependence/VariationalEquation.lean`,
  -- `SmoothInSpace/VariationalODE.lean` — e.g. `IsLocalFlow.hasDerivAt_partial_spatial_fderiv`)
  -- supplies the INTERIOR variational `HasDerivAt`, never the `t→0⁺` endpoint right-limit.
  -- Per the WAVE-2 ADDENDUM this is the one allowed single labeled `sorry`.
  sorry

end DifferentialGeometry.PDE.RicciFlow
