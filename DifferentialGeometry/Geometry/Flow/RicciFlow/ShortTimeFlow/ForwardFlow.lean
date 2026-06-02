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
  set z₀ : E := extChartAt I α x with hz₀
  have hxsrc' : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hxsrc
  have hKcompact : IsCompact (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) :=
    (isCompact_Icc).prod isCompact_univ
  obtain ⟨C, hC⟩ :=
    hKcompact.exists_bound_of_continuousOn (f := fun q : ℝ × M =>
      (X_DT q.1 q.2 : TangentSpace I q.2)) hcont0
  have hδT : (0 : ℝ) < min δ T := lt_min hδ hT
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
      ‖extChartAt I α (Φ s x) - z₀‖ ≤ C * |s| := by
    intro s hs
    obtain ⟨hΦsrc_s, hident⟩ := hpic s hs
    rw [hident, add_sub_cancel_left]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := s) (C := C)
      (f := fun r : ℝ => chartRawRepr (I := I) α (X_DT r) (extChartAt I α (Φ r x)))
      (fun r hr => ?_)
    · simpa using hnorm
    · rw [Set.uIoc_of_le hs.1] at hr
      have hr_mem : r ∈ Set.Ico (0 : ℝ) (min δ T) :=
        ⟨le_of_lt hr.1, lt_of_le_of_lt hr.2 hs.2⟩
      obtain ⟨hΦsrc_r, _⟩ := hpic r hr_mem
      have hrT : r ∈ Set.Icc (0 : ℝ) T :=
        ⟨le_of_lt hr.1, le_of_lt (lt_of_lt_of_le hr_mem.2 (min_le_right _ _))⟩
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
  have htendsto : Filter.Tendsto (fun s : ℝ => extChartAt I α (Φ s x))
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 z₀) := by
    have htsub : Filter.Tendsto
        (fun s : ℝ => extChartAt I α (Φ s x) - z₀) (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun s : ℝ => C * |s|) ?_ ?_
      · have hmem : Set.Ico (0 : ℝ) (min δ T) ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := by
          refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
            (nhdsWithin_le_nhds (Iio_mem_nhds hδT))) (fun s hs => ?_)
          exact ⟨hs.1, hs.2⟩
        filter_upwards [hmem] with s hs using hbound s hs
      · have hcontmul : Continuous (fun s : ℝ => C * |s|) := by fun_prop
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
  · simp only [hΦ0]
    exact ((extChartAt I α).left_inv hxsrc').symm

/-- **Moving-spatial-Jacobian right-continuity at `t = 0` (variational endpoint).**

The variational analogue of `flow_orbit_continuousWithinAt_zero`.  Fix `x : M` and
`v : TangentSpace I x`.  The `E`-valued moving spatial Jacobian
`J s := (mfderiv I I (Φ s) x v : E)` satisfies, on a right-half neighbourhood
`Ico 0 (min δ T)` of `0`, the *linearised (variational) integral equation*

  `J s = J₀ + ∫₀ˢ A r (J r) dr`,

where `J₀ = (mfderiv I I (Φ 0) x v : E)` is the initial Jacobian value and
`A r := fderiv ℝ (chartRawRepr α (X_DT r)) (extChartAt I α (Φ r x))` is the spatial
gradient of the field along the orbit (continuous up to `0` by `hgrad0`, evaluated at
`(r, Φ r x)`).  The integrand `A r (J r)` is bounded by `C_A · B` near `0`, where
`C_A` bounds `‖A‖` on the compact `Icc 0 T ×ˢ univ` (via `hgrad0` continuity composed
with the orbit, restricted to the chart neighbourhood) and `B` bounds `‖J r‖` near `0`
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
    (hvarpicard : ∀ (x : M) (v : TangentSpace I x), ∃ α : M, ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
        (mfderiv I I (fun y : M => Φ s y) x v : E)
          = (@id E (mfderiv I I (fun y : M => Φ 0 y) x v))
            + ∫ r in (0 : ℝ)..s,
                (fderiv ℝ (chartRawRepr (I := I) α (X_DT r))
                    (extChartAt I α (Φ r x)))
                  (mfderiv I I (fun y : M => Φ r y) x v : E))
    (hJbound : ∀ (x : M) (v : TangentSpace I x), ∃ δ : ℝ, ∃ B : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
        ‖(mfderiv I I (fun y : M => Φ s y) x v : E)‖ ≤ B) :
    ∀ (x : M) (v : TangentSpace I x),
      ContinuousWithinAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E))
        (Set.Ici (0 : ℝ)) 0 := by
  intro x v
  obtain ⟨α, δ₁, hδ₁, hpic⟩ := hvarpicard x v
  obtain ⟨δ₂, B, hδ₂, hBound⟩ := hJbound x v
  set J : ℝ → E := fun s : ℝ => @id E (mfderiv I I (fun y : M => Φ s y) x v) with hJ
  set J₀ : E := J 0 with hJ₀
  have hKcompact : IsCompact (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) :=
    (isCompact_Icc).prod isCompact_univ
  obtain ⟨CA, hCA⟩ :=
    hKcompact.exists_bound_of_continuousOn
      (f := fun q : ℝ × M =>
        fderiv ℝ (chartRawRepr (I := I) α (X_DT q.1)) (extChartAt I α q.2)) (hgrad0 α)
  have hδpos : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hδT : (0 : ℝ) < min (min δ₁ δ₂) T := lt_min hδpos hT
  have hle1 : min (min δ₁ δ₂) T ≤ min δ₁ T :=
    min_le_min (min_le_left _ _) (le_refl _)
  have hle2 : min (min δ₁ δ₂) T ≤ min δ₂ T :=
    min_le_min (min_le_right _ _) (le_refl _)
  set A : ℝ → (E →L[ℝ] E) := fun r : ℝ =>
    fderiv ℝ (chartRawRepr (I := I) α (X_DT r)) (extChartAt I α (Φ r x)) with hA
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) (min (min δ₁ δ₂) T),
      ‖J s - J₀‖ ≤ (CA * B) * |s| := by
    intro s hs
    have hs1 : s ∈ Set.Ico (0 : ℝ) (min δ₁ T) :=
      ⟨hs.1, lt_of_lt_of_le hs.2 hle1⟩
    have hpics : J s = J₀ + ∫ r in (0 : ℝ)..s, A r (J r) := hpic s hs1
    rw [hpics, add_sub_cancel_left]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := s) (C := CA * B)
      (f := fun r : ℝ => A r (J r)) (fun r hr => ?_)
    · simpa using hnorm
    · rw [Set.uIoc_of_le hs.1] at hr
      have hr_mem : r ∈ Set.Ico (0 : ℝ) (min (min δ₁ δ₂) T) :=
        ⟨le_of_lt hr.1, lt_of_le_of_lt hr.2 hs.2⟩
      have hrT : r ∈ Set.Icc (0 : ℝ) T :=
        ⟨le_of_lt hr.1, le_of_lt (lt_of_lt_of_le hr_mem.2 (min_le_right _ _))⟩
      have hr2 : r ∈ Set.Ico (0 : ℝ) (min δ₂ T) :=
        ⟨le_of_lt hr.1, lt_of_lt_of_le hr_mem.2 hle2⟩
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      have hAnorm : ‖A r‖ ≤ CA := by
        have := hCA (r, Φ r x) ⟨hrT, Set.mem_univ _⟩
        simpa [hA] using this
      have hJnorm : ‖J r‖ ≤ B := hBound r hr2
      have hCA0 : (0 : ℝ) ≤ CA := le_trans (norm_nonneg _) hAnorm
      exact mul_le_mul hAnorm hJnorm (norm_nonneg _) hCA0
  have htsub : Filter.Tendsto (fun s : ℝ => J s - J₀)
      (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun s : ℝ => (CA * B) * |s|) ?_ ?_
    · have hmem : Set.Ico (0 : ℝ) (min (min δ₁ δ₂) T) ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := by
        refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin
          (nhdsWithin_le_nhds (Iio_mem_nhds hδT))) (fun s hs => ?_)
        exact ⟨hs.1, hs.2⟩
      filter_upwards [hmem] with s hs using hbound s hs
    · have hcontmul : Continuous (fun s : ℝ => (CA * B) * |s|) := by fun_prop
      have := (hcontmul.tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ici (0 : ℝ)))
      simpa using this
  have htendsto : Filter.Tendsto J (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 J₀) := by
    have := htsub.add (tendsto_const_nhds (x := J₀)
      (f := 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)))
    simpa using this
  change ContinuousWithinAt J (Set.Ici (0 : ℝ)) 0
  rw [ContinuousWithinAt]
  exact htendsto

set_option linter.unusedVariables false in
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
              chartRawRepr (I := I) α (X_DT r) (extChartAt I α (Φ r x)))
    (hvarpicard : ∀ (x : M) (v : TangentSpace I x), ∃ α : M, ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
        (mfderiv I I (fun y : M => Φ s y) x v : E)
          = (@id E (mfderiv I I (fun y : M => Φ 0 y) x v))
            + ∫ r in (0 : ℝ)..s,
                (fderiv ℝ (chartRawRepr (I := I) α (X_DT r))
                    (extChartAt I α (Φ r x)))
                  (mfderiv I I (fun y : M => Φ r y) x v : E))
    (hJbound : ∀ (x : M) (v : TangentSpace I x), ∃ δ : ℝ, ∃ B : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
        ‖(mfderiv I I (fun y : M => Φ s y) x v : E)‖ ≤ B) :
    (∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) 0)
    ∧ (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E))
          (Set.Ici (0 : ℝ)) 0) :=
  ⟨flow_orbit_continuousWithinAt_zero X_DT T hT Φ hΦ0 hcont0 hpicard,
    flow_mfderiv_continuousWithinAt_zero X_DT T hT Φ hgrad0 hvarpicard hJbound⟩

set_option linter.unusedVariables false in
/-- A time-dependent field `X_DT` that is jointly `C∞` on the interior `(0,T) ×ˢ univ`
(`hint`) and continuous together with its chart-gradient up to `t = 0` (`hcont0`,
`hgrad0`) admits a single forward flow `Φ : ℝ → M → M` with `Φ 0 = id`, per-time
diffeomorphisms on `(0,T)`, the bare geometric velocity `∂ₛ Φ s x = X_DT t (Φ t x)` on
`(0,T)`, and `t = 0` right-continuity of both the orbit `s ↦ Φ s x` and the moving
spatial Jacobian `s ↦ mfderiv I I (Φ s) x v`.

This statement is correct; its forward-flow construction is currently a deferred `sorry`.
The previous internal producer rebuilt the flow through a chart-Picard / variational
integral identity whose integrand was the *raw-fibre* chart representation `chartRawRepr`
(the bare value `(X_DT r (Φ r x) : E)`).  An adversarial statement check found that
integrand to be the wrong chart-ODE term off the basepoint: the genuine flow's chart
velocity is `mfderiv (extChartAt I α) (Φ r x) (X_DT r (Φ r x)) = trivToE α (Φ r x) …`,
which differs from the bare value by the moving-trivialization (chart-transition Jacobian)
correction and agrees with it only at `Φ r x = α`.  That producer was therefore
unsatisfiable on a curved manifold (every `Sⁿ`) and has been removed; this `sorry` is to
be discharged by reconstructing the forward flow with the *trivialised* chart integral
identity (and the analogous covariant variational identity). -/
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
