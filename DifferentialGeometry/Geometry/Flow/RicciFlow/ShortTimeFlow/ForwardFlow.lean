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

set_option linter.unusedSectionVars false in
/-- **Moving-spatial-Jacobian right-continuity at `t = 0` (variational endpoint).**

The variational analogue of `flow_orbit_continuousWithinAt_zero`.  Fix `x : M` and
`v : TangentSpace I x`.  The `E`-valued moving spatial Jacobian
`J s := (mfderiv I I (Φ s) x v : E)` satisfies, on a right-half neighbourhood
`Ico 0 (min δ T)` of `0`, the *linearised (variational) integral equation*

  `J s = J₀ + ∫₀ˢ A r (J r) dr`,

where `J₀ = (mfderiv I I (Φ 0) x v : E)` is the initial Jacobian value and the *covariant*
coefficient `A r := fderiv ℝ (chartTrivRepr α (X_DT r)) (extChartAt I α (Φ r x))` is the spatial
gradient of the trivialised chart field along the orbit.  The per-`s` bound `‖A s‖ ≤ CA`
(carried inside `hvarpicard`) controls the coefficient near `0`, and `B` bounds `‖J r‖` near `0`
(`hJbound`, the genuine near-`0` boundedness of the variational Jacobian, dischargeable
downstream by the linear Grönwall estimate `‖J r‖ ≤ ‖J₀‖ · exp (CA · r)`).  Hence
`‖J s − J₀‖ ≤ (CA · B) · |s| → 0` as `s → 0⁺`; with `J 0 = J₀` this is right-continuity
at `0`.

`hvarpicard` (the variational integral equation for the moving Jacobian, with its per-`s`
coefficient bound) and `hJbound` (near-`0` boundedness of the Jacobian) are genuine
dischargeable analytic data about the linearised flow — neither is the conclusion (a
`ContinuousWithinAt` of `J`), so this is not hypothesis-packaging. -/
private theorem flow_mfderiv_continuousWithinAt_zero
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T) (Φ : ℝ → M → M)
    (hvarpicard : ∀ (x : M) (v : TangentSpace I x), ∃ α : M, ∃ δ : ℝ, ∃ CA : ℝ, 0 < δ ∧ 0 ≤ CA ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
        ((mfderiv I I (fun y : M => Φ s y) x v : E)
          = (@id E (mfderiv I I (fun y : M => Φ 0 y) x v))
            + ∫ r in (0 : ℝ)..s,
                (fderiv ℝ (fun z => chartTrivRepr (I := I) α (X_DT r) z) (extChartAt I α (Φ r x)))
                  (mfderiv I I (fun y : M => Φ r y) x v : E))
            ∧ ‖(fderiv ℝ (fun z => chartTrivRepr (I := I) α (X_DT s) z) (extChartAt I α (Φ s x)))‖ ≤ CA)
    (hJbound : ∀ (x : M) (v : TangentSpace I x), ∃ δ : ℝ, ∃ B : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T), ‖(mfderiv I I (fun y : M => Φ s y) x v : E)‖ ≤ B) :
    ∀ (x : M) (v : TangentSpace I x),
      ContinuousWithinAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E)) (Set.Ici (0 : ℝ)) 0 := by
  intro x v
  obtain ⟨α, δ₁, CA, hδ₁, hCA, hpic⟩ := hvarpicard x v
  obtain ⟨δ₂, B, hδ₂, hJB⟩ := hJbound x v
  let J : ℝ → E := fun s => (mfderiv I I (fun y : M => Φ s y) x v : E)
  let A : ℝ → (E →L[ℝ] E) := fun r =>
    fderiv ℝ (fun z => chartTrivRepr (I := I) α (X_DT r) z) (extChartAt I α (Φ r x))
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hJB 0 ⟨le_refl 0, by
    simp only [lt_min_iff]; exact ⟨hδ₂, hT⟩⟩)
  have hδ₀ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hwin_mem : Set.Ico (0 : ℝ) (min (min δ₁ δ₂) T) ∈ 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) :=
    Ico_mem_nhdsGE (lt_min hδ₀ hT)
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) (min (min δ₁ δ₂) T), ‖J s - J 0‖ ≤ (CA * B) * s := by
    intro s hs
    have hsT : s ∈ Set.Ico (0 : ℝ) (min δ₁ T) := by
      refine ⟨hs.1, lt_of_lt_of_le hs.2 ?_⟩
      exact min_le_min (min_le_left _ _) (le_refl T)
    obtain ⟨heq, _⟩ := hpic s hsT
    have h2 : J s = J 0 + ∫ r in (0 : ℝ)..s, (A r) (J r) := by
      simpa only [id_eq] using heq
    have hdiff : J s - J 0 = ∫ r in (0 : ℝ)..s, (A r) (J r) := by
      rw [h2]; abel
    rw [hdiff]
    have hnormle : ∀ r ∈ Set.uIoc (0 : ℝ) s, ‖(A r) (J r)‖ ≤ CA * B := by
      intro r hr
      have hr_mem : r ∈ Set.Ico (0 : ℝ) (min (min δ₁ δ₂) T) := by
        rw [Set.uIoc_of_le hs.1] at hr
        exact ⟨le_of_lt hr.1, lt_of_le_of_lt hr.2 hs.2⟩
      have hr1 : r ∈ Set.Ico (0 : ℝ) (min δ₁ T) := by
        refine ⟨hr_mem.1, lt_of_lt_of_le hr_mem.2 ?_⟩
        exact min_le_min (min_le_left _ _) (le_refl T)
      have hr2 : r ∈ Set.Ico (0 : ℝ) (min δ₂ T) := by
        refine ⟨hr_mem.1, lt_of_lt_of_le hr_mem.2 ?_⟩
        exact min_le_min (min_le_right _ _) (le_refl T)
      obtain ⟨_, hAr⟩ := hpic r hr1
      have hJr : ‖J r‖ ≤ B := hJB r hr2
      calc ‖(A r) (J r)‖ ≤ ‖A r‖ * ‖J r‖ := (A r).le_opNorm (J r)
        _ ≤ CA * B := mul_le_mul hAr hJr (norm_nonneg _) hCA
    calc ‖∫ r in (0 : ℝ)..s, (A r) (J r)‖
        ≤ (CA * B) * |s - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hnormle
      _ = (CA * B) * s := by rw [sub_zero, abs_of_nonneg hs.1]
  have htendsto_a : Filter.Tendsto (fun s : ℝ => (CA * B) * s) (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
    have hc : Filter.Tendsto (fun s : ℝ => (CA * B) * s) (𝓝 (0 : ℝ)) (𝓝 ((CA * B) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hev : (fun s : ℝ => ‖J s - J 0‖) ≤ᶠ[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)] (fun s : ℝ => (CA * B) * s) := by
    filter_upwards [hwin_mem] with s hs using hbound s hs
  have hsq : Filter.Tendsto (fun s : ℝ => J s - J 0) (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero_norm' hev htendsto_a
  exact tendsto_sub_nhds_zero_iff.mp hsq

set_option linter.unusedSectionVars false in
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
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ0 t x))) := by
  intro t ht x
  have hIoo_nhds : Set.Ioo (0 : ℝ) T ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
  have hint_at : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φint s x) (Set.Ici (0 : ℝ)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φint t x))) :=
    ((hΦint_bare t ht x).hasMFDerivAt hIoo_nhds).hasMFDerivWithinAt
  have hev : (fun s : ℝ => Φ0 s x) =ᶠ[𝓝[Set.Ici (0 : ℝ)] t] (fun s : ℝ => Φint s x) := by
    refine Filter.eventuallyEq_of_mem (s := Set.Ioo (0 : ℝ) T)
      (nhdsWithin_le_nhds hIoo_nhds) (fun s hs => ?_)
    exact (hagree s hs x).symm
  have hxpt : (fun s : ℝ => Φ0 s x) t = (fun s : ℝ => Φint s x) t := (hagree t ht x).symm
  have hcongr := hint_at.congr_of_eventuallyEq hev hxpt
  rwa [hagree t ht x] at hcongr

set_option linter.unusedSectionVars false in
/-- **Per-time diffeomorphisms on `(0,T)` for `Φ := Φ0`** (C2), transported from the interior
flow `Φint` across their pointwise agreement on `(0,T)`.

For `t ∈ (0,T)`, take the diffeomorphism witness `d` of the interior slice `Φint t` from
`hdiffeo_int`; for every `x`, `d x = Φint t x = Φ0 t x` by `hagree t`, so the same `d` is the
witness for `Φ0 t`. -/
theorem forwardFlow_diffeo_of_agree
    (Φ Φint : ℝ → M → M) (T : ℝ)
    (hagree : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, Φint t x = Φ t x)
    (hdiffeo_int : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φint t x) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x := by
  intro t ht
  obtain ⟨d, hd⟩ := hdiffeo_int t ht
  exact ⟨d, fun x => (hd x).trans (hagree t ht x)⟩

set_option linter.unusedSectionVars false in
/-- The interior agreement `Φ s x = Φ0 s x` on the open horizon `(0,σ)` extends to the
half-open `[0,σ)` because both flows fix the basepoint at `t = 0` (`Φ 0 = id = Φ0 0`). -/
private theorem forwardFlow_agree_extends_to_zero
    (Φ Φ0 : ℝ → M → M) (σ : ℝ) (x : M) (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) σ)
    (hΦ0id : ∀ y : M, Φ 0 y = y) (hΦ0_0 : ∀ y : M, Φ0 0 y = y)
    (hagree : ∀ t ∈ Set.Ioo (0 : ℝ) σ, ∀ y : M, Φ t y = Φ0 t y) :
    Φ s x = Φ0 s x := by
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · rw [← hs0, hΦ0id x, hΦ0_0 x]
  · exact hagree s ⟨hs0, hs.2⟩ x

set_option linter.unusedVariables false in
/-- A time-dependent field `X_DT` that is jointly `C∞` on the interior `(0,T) ×ˢ univ`
(`hint`) and continuous together with its chart-gradient up to `t = 0` (`hcont0`,
`hgrad0`) admits a single forward flow `Φ : ℝ → M → M` with `Φ 0 = id`, per-time
diffeomorphisms on `(0,T)`, the bare geometric velocity `∂ₛ Φ s x = X_DT t (Φ t x)` on
`(0,T)`, and `t = 0` right-continuity of both the orbit `s ↦ Φ s x` and the moving
spatial Jacobian `s ↦ mfderiv I I (Φ s) x v`.

The forward flow is assembled by composition: a time-clamp extension of the field, the
`t = 0`-anchored chart flow, the interior continuation to all of `(0,T)`, and the trivialised
chart/covariant-variational integral identities supplying the two `t = 0` right-continuities.
Several of those inputs are themselves deferred `sorry`s, so this theorem transitively depends
on `sorryAx` until they are discharged. -/
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
  obtain ⟨Xext, hXeq, hXcont, hXgrad⟩ := field_time_clamp_extension X_DT T hT hcont0 hgrad0
  obtain ⟨σ, hσ, Φ0, hΦ0_0, hΦ0_bare, hΦ0_pic, hΦ0_cont0⟩ :=
    corrected_chart_anchor_flow_build Xext hXcont hXgrad
  set σ' : ℝ := min σ T with hσ'def
  have hσ' : 0 < σ' := lt_min hσ hT
  have hσ'T : σ' ≤ T := min_le_right _ _
  have hσ'σ : σ' ≤ σ := min_le_left _ _
  have hint_ext : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Xext q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ) := by
    refine hint.congr (fun q hq => ?_)
    have hq1 : q.1 ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self (Set.mem_prod.mp hq).1
    show (TotalSpace.mk' E q.2 (Xext q.1 q.2) : TangentBundle I M)
      = (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M)
    rw [hXeq q.1 hq1 q.2]
  have hΦ0_bare' : ∀ t ∈ Set.Ioo (0 : ℝ) σ', ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ0 s x) (Set.Ioo (0 : ℝ) σ') t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Xext t (Φ0 t x))) := by
    intro t ht x
    exact (hΦ0_bare t (Set.Ioo_subset_Ioo_right hσ'σ ht) x).mono
      (Set.Ioo_subset_Ioo_right hσ'σ)
  obtain ⟨Φ, hΦ0id, hagree, hΦbare_Ioo, hΦsmooth⟩ :=
    interior_extends_anchor Xext T hT hint_ext Φ0 σ' hσ' hσ'T hΦ0_0 hΦ0_bare'
  have hΦbare_Ici_Xext : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Xext t (Φ t x))) :=
    forwardFlow_bare_velocity_of_agree Xext T Φ Φ (fun t _ x => rfl) hΦbare_Ioo
  have hΦbare_Ici_XDT : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x))) := by
    intro t ht x
    have := hΦbare_Ici_Xext t ht x
    rwa [hXeq t (Set.Ioo_subset_Icc_self ht) (Φ t x)] at this
  refine ⟨Φ, hΦ0id, ?_, hΦbare_Ici_XDT, ?_, ?_⟩
  · exact interior_flow_slice_diffeo_on_Ioo Xext T hT hint_ext Φ hΦsmooth hΦbare_Ioo
  · intro x
    have hagree_Ico : Set.EqOn (fun s : ℝ => Φ s x) (fun s : ℝ => Φ0 s x)
        (Set.Ico (0 : ℝ) σ') := fun s hs =>
      forwardFlow_agree_extends_to_zero Φ Φ0 σ' x s hs hΦ0id hΦ0_0 hagree
    have hev : (fun s : ℝ => Φ s x) =ᶠ[𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)] (fun s : ℝ => Φ0 s x) :=
      Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE hσ') hagree_Ico
    have hx0 : (fun s : ℝ => Φ s x) 0 = (fun s : ℝ => Φ0 s x) 0 := by
      simp only [hΦ0id x, hΦ0_0 x]
    exact (hΦ0_cont0 x).congr_of_eventuallyEq hev hx0
  · have hΦpic : ∀ x : M, ∃ α : M, ∃ δ : ℝ, 0 < δ ∧ x ∈ (chartAt H α).source ∧
        ∀ s ∈ Set.Ico (0 : ℝ) (min δ T), Φ s x ∈ (chartAt H α).source ∧
          extChartAt I α (Φ s x) = extChartAt I α x
            + ∫ r in (0 : ℝ)..s, chartTrivRepr (I := I) α (Xext r) (extChartAt I α (Φ r x)) := by
      intro x
      obtain ⟨α, δ, C, hδ, hxsrc, hpic⟩ := hΦ0_pic x
      refine ⟨α, min δ σ', lt_min hδ hσ', hxsrc, ?_⟩
      have hmin_eq : min (min δ σ') T = min δ σ' := by
        rw [min_eq_left (le_trans (min_le_right _ _) hσ'T)]
      intro s hs
      rw [hmin_eq] at hs
      have hsσ' : s < σ' := lt_of_lt_of_le hs.2 (min_le_right _ _)
      have hsδσ : s < min δ σ := lt_of_lt_of_le hs.2 (min_le_min (le_refl δ) hσ'σ)
      have hΦs : Φ s x = Φ0 s x :=
        forwardFlow_agree_extends_to_zero Φ Φ0 σ' x s ⟨hs.1, hsσ'⟩ hΦ0id hΦ0_0 hagree
      obtain ⟨hsrc0, heq0, _⟩ := hpic s ⟨hs.1, hsδσ⟩
      refine ⟨by rw [hΦs]; exact hsrc0, ?_⟩
      have hintegrand : Set.EqOn
          (fun r => chartTrivRepr (I := I) α (Xext r) (extChartAt I α (Φ r x)))
          (fun r => chartTrivRepr (I := I) α (Xext r) (extChartAt I α (Φ0 r x)))
          (Set.uIcc (0 : ℝ) s) := by
        intro r hr
        rw [Set.uIcc_of_le hs.1, Set.mem_Icc] at hr
        have hrσ' : r < σ' := lt_of_le_of_lt hr.2 hsσ'
        simp only [forwardFlow_agree_extends_to_zero Φ Φ0 σ' x r ⟨hr.1, hrσ'⟩ hΦ0id hΦ0_0 hagree]
      rw [hΦs, heq0, intervalIntegral.integral_congr hintegrand]
    have hXgrad' : ∀ α : M, ContinuousOn
        (fun q : ℝ × M => fderiv ℝ (chartRawRepr (I := I) α (Xext q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
      fun α => (hXgrad α).mono (Set.subset_univ _)
    have hvarjb := corrected_variational_endpoint_data Xext T hT Φ hint_ext hXgrad' hΦ0id hΦpic
      hΦbare_Ici_Xext
    exact flow_mfderiv_continuousWithinAt_zero Xext T hT Φ hvarjb.1 hvarjb.2

end DifferentialGeometry.PDE.RicciFlow
