import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.LowerAllUpperIndices
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.JinvContinuity
import DifferentialGeometry.Analysis.Laplacian.MetricBounds
import DifferentialGeometry.Geometry.LocalChartConsistency
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Integral.Measure.Invariance
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Uniform upper bound on the metric quadratic form over a compact base set

For a smooth manifold `M` modelled on `(E, H)` carrying a smooth Riemannian
metric `g : SmoothRiemannianMetric I M`, this file proves a uniform
pointwise upper bound on the metric quadratic form `g.inner b v v` for `b`
ranging over a compact subset of `M` and `v` ranging over the model fibre
`E`, under the locality hypothesis `HasLocallyConstantChartAt H M` on the
chart-selection function.

## Strategy

The bundle metric `g.inner b v v` (for `v : E ≡ TangentSpace I b`) is, by
itself, not jointly continuous in `(b, v)` because the chart trivialisation
of the tangent bundle jumps between chart sources. The locality hypothesis
remedies this: on a neighbourhood `U_{b₀}` of any base point `b₀` where
`chartAt H b = chartAt H b₀`, the inverse chart-Jacobian `chartJinv b₀ b`
is the identity (because `achart H b = achart H b₀`, and the core-
coordinate change with equal endpoints is the identity). The identity
`chartGramBilin g α b u w = g.inner b (chartJinv α b u) (chartJinv α b w)`
therefore reduces to `chartGramBilin g b₀ b v v = g.inner b v v` on
`U_{b₀}`. The function `b ↦ chartGramBilin g b₀ b` is continuous on the
chart base set (a finite sum of `(b ↦ chartGramMatrix g b₀ b j k)` times
constant CLMs, each entry being smooth on the chart base set by
`chartGramMatrix_entry_contMDiffOn`). Consequently
`b ↦ ‖chartGramBilin g b₀ b‖` is continuous on `U_{b₀}` and, on any
compact subset of `U_{b₀}`, bounded above.

To convert a compact-in-open inclusion into bounds on compact pieces, we
use `IsCompact.finite_compact_cover` (available because `M` is `T2`, hence
`R1`): from an open cover of `K_base` by locality neighbourhoods we
extract finitely many compact `K_i ⊆ U_{b₀_i}` whose union is `K_base`.
On each `K_i`, the function `b ↦ ‖chartGramBilin g b₀_i b‖` is bounded by
some `C_i`. The maximum `C := max_i C_i` gives `g.inner b v v ≤ C · ‖v‖²`
on `K_base × E`. Taking `K := √(C + 1) + 1` (strictly positive) yields the
bound `√(g.inner b v v) ≤ K · ‖v‖`.

## Main result

* `g_inner_sqrt_uniform_upper_bound_on_compact` — for any compact
  `K_base : Set M`, there is `K > 0` with
  `√(g.inner b v v) ≤ K · ‖v‖` for all `b ∈ K_base` and all `v : E`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-! ## Step 1: equality of trivialisation symm CLMs on the locality neighbourhood

If `chartAt H b = chartAt H b₀`, then the `achart` values at `b` and at
`b₀` are equal as subtypes of the atlas (proof irrelevance on the second
component), and consequently the inverse chart-Jacobian centred at `b₀`
evaluated at `b` equals the coordinate change `coordChange (achart H b₀)
(achart H b₀) b`, which is the identity by `coordChange_self`. -/

private lemma achart_eq_of_chartAt_eq {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀) :
    achart H b = achart H b₀ := by
  apply Subtype.ext
  exact h_chart

/-- Under the locality hypothesis, on the open neighbourhood produced by
`HasLocallyConstantChartAt.exists_isOpen_nhds b₀`, the inverse chart-Jacobian
`chartJinv b₀ b : E →L[ℝ] E` is the identity. -/
private lemma chartJinv_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    chartJinv (I := I) (M := M) b₀ b = (1 : E →L[ℝ] E) := by
  unfold chartJinv
  rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (I := I)
    (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

/-! ## Step 2: rewriting `g.inner b v v` as `chartGramBilin g b₀ b v v`

On the locality neighbourhood `U_{b₀}`, the inverse chart-Jacobian is the
identity, so `chartGramBilin g b₀ b v v = g.inner b v v` for all `v : E`. -/

/-- On the locality neighbourhood, the bundle metric quadratic form coincides
with the chart-Gram bilinear quadratic form centred at `b₀`. -/
private lemma g_inner_eq_chartGramBilin_of_chartAt_eq
    (g : SmoothRiemannianMetric I M) {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) (v : E) :
    g.inner b v v =
      chartGramBilin (I := I) (M := M) g b₀ b v v := by
  rw [chartGramBilin_eq_innerJinv (I := I) (M := M) g b₀ b v v]
  rw [chartJinv_eq_id_of_chartAt_eq (I := I) (M := M) h_chart hb]
  rfl

/-! ## Step 3: continuity of `b ↦ chartGramBilin g b₀ b` on the chart base set

The chart-Gram bilinear form is, as a function of `b`, a finite sum of
matrix-entry-times-constant-CLM terms. Each matrix entry is smooth in `b`
on the chart base set, and finite sums and scalar-CLM products preserve
continuity, so the resulting CLM-valued function is continuous on the
chart base set. -/

private lemma chartGramBilin_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (b₀ : M) :
    ContinuousOn (fun b : M => chartGramBilin (I := I) (M := M) g b₀ b)
      (chartAt H b₀).source := by
  classical
  have h_eq : ∀ b : M,
      chartGramBilin (I := I) (M := M) g b₀ b =
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartGramMatrix g b₀ b j k •
              (chartCoordCLM E j).smulRight (chartCoordCLM E k) := by
    intro b; rfl
  refine ContinuousOn.congr ?_ (fun b _ => (h_eq b).symm)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine continuousOn_finset_sum _ (fun k _ => ?_)
  have h_entry : ContinuousOn (fun b : M => chartGramMatrix g b₀ b j k)
      (chartAt H b₀).source := by
    have hsmooth := chartGramMatrix_entry_contMDiffOn (I := I) g b₀ j k
    have h_set_eq : ((trivializationAt E (TangentSpace I) b₀).baseSet
        : Set M) = (chartAt H b₀).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M) b₀
    rw [h_set_eq] at hsmooth
    exact hsmooth.continuousOn
  exact h_entry.smul continuousOn_const

/-! ## Step 4: operator-norm continuity of `b ↦ ‖chartGramBilin g b₀ b‖` -/

private lemma chartGramBilin_norm_continuousOn
    (g : SmoothRiemannianMetric I M) (b₀ : M) :
    ContinuousOn (fun b : M => ‖chartGramBilin (I := I) (M := M) g b₀ b‖)
      (chartAt H b₀).source :=
  continuous_norm.comp_continuousOn
    (chartGramBilin_continuousOn_chartSource (I := I) (M := M) g b₀)

/-! ## Step 5: pointwise upper bound on the locality neighbourhood -/

private lemma g_inner_le_chartGramBilin_norm_sq
    (g : SmoothRiemannianMetric I M) {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) (v : E) :
    g.inner b v v ≤ ‖chartGramBilin (I := I) (M := M) g b₀ b‖ * ‖v‖ ^ 2 := by
  have h_eq : g.inner b v v =
      chartGramBilin (I := I) (M := M) g b₀ b v v :=
    g_inner_eq_chartGramBilin_of_chartAt_eq (I := I) (M := M) g h_chart hb v
  rw [h_eq]
  have h_abs_le :
      |chartGramBilin (I := I) (M := M) g b₀ b v v| ≤
        ‖chartGramBilin (I := I) (M := M) g b₀ b‖ * ‖v‖ * ‖v‖ := by
    have h := (chartGramBilin (I := I) (M := M) g b₀ b).le_opNorm₂ v v
    simpa [Real.norm_eq_abs] using h
  calc chartGramBilin (I := I) (M := M) g b₀ b v v
      ≤ |chartGramBilin (I := I) (M := M) g b₀ b v v| := le_abs_self _
    _ ≤ ‖chartGramBilin (I := I) (M := M) g b₀ b‖ * ‖v‖ * ‖v‖ := h_abs_le
    _ = ‖chartGramBilin (I := I) (M := M) g b₀ b‖ * ‖v‖ ^ 2 := by ring

/-! ## Step 6: uniform pointwise bound on a compact subset of the chart source -/

private lemma exists_norm_bound_on_compact_subset_of_chartSource
    (g : SmoothRiemannianMetric I M) (b₀ : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H b₀).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K,
      ‖chartGramBilin (I := I) (M := M) g b₀ b‖ ≤ C := by
  by_cases h_empty : K = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    rw [h_empty] at hb
    exact absurd hb (Set.notMem_empty _)
  have h_cont : ContinuousOn
      (fun b : M => ‖chartGramBilin (I := I) (M := M) g b₀ b‖) K :=
    (chartGramBilin_norm_continuousOn (I := I) (M := M) g b₀).mono hKsub
  have h_bdd : BddAbove
      ((fun b : M => ‖chartGramBilin (I := I) (M := M) g b₀ b‖) '' K) :=
    hK.bddAbove_image h_cont
  rcases h_bdd with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have h1 : ‖chartGramBilin (I := I) (M := M) g b₀ b‖ ≤ C :=
    hC ⟨b, hb, rfl⟩
  exact h1.trans (le_max_left _ _)

/-! ## Step 7: refining the locality neighbourhood to inside the chart source -/

private lemma exists_open_chart_loc
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (b₀ : M) :
    ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧
      U ⊆ (chartAt H b₀).source ∧
      ∀ b ∈ U, chartAt H b = chartAt H b₀ := by
  rcases h_atlas.exists_isOpen_nhds b₀ with ⟨U, hU_open, hU_mem, hU_const⟩
  refine ⟨U, hU_open, hU_mem, ?_, hU_const⟩
  intro b hb
  have h_eq : chartAt H b = chartAt H b₀ := hU_const b hb
  have h_mem_b : b ∈ (chartAt H b).source := mem_chart_source H b
  rw [h_eq] at h_mem_b
  exact h_mem_b

/-! ## Step 8: uniform `g.inner` upper bound on the compact base set -/

private lemma exists_uniform_g_inner_upper_bound_on_compact
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M)
    {K_base : Set M} (hK_base : IsCompact K_base) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K_base, ∀ v : E,
      g.inner b v v ≤ C * ‖v‖ ^ 2 := by
  classical
  -- For each `b₀ : M`, choose a locality neighbourhood `loc b₀ ⊆ (chartAt H b₀).source`.
  let loc : M → Set M := fun b₀ =>
    (exists_open_chart_loc (H := H) (M := M) h_atlas b₀).choose
  have h_loc_open : ∀ b₀ : M, IsOpen (loc b₀) :=
    fun b₀ => (exists_open_chart_loc (H := H) (M := M) h_atlas b₀).choose_spec.1
  have h_loc_mem : ∀ b₀ : M, b₀ ∈ loc b₀ :=
    fun b₀ => (exists_open_chart_loc (H := H) (M := M) h_atlas b₀).choose_spec.2.1
  have h_loc_sub : ∀ b₀ : M, loc b₀ ⊆ (chartAt H b₀).source :=
    fun b₀ => (exists_open_chart_loc (H := H) (M := M) h_atlas b₀).choose_spec.2.2.1
  have h_loc_const : ∀ b₀ : M, ∀ b ∈ loc b₀, chartAt H b = chartAt H b₀ :=
    fun b₀ => (exists_open_chart_loc (H := H) (M := M) h_atlas b₀).choose_spec.2.2.2
  -- Cover `K_base` by `loc b₀` for `b₀ ∈ K_base`.
  have h_cover : K_base ⊆ ⋃ b₀ ∈ K_base, loc b₀ := by
    intro b hb
    exact Set.mem_iUnion₂.mpr ⟨b, hb, h_loc_mem b⟩
  -- Finite subcover.
  rcases hK_base.elim_finite_subcover_image (b := K_base) (c := loc)
    (fun b₀ _ => h_loc_open b₀) h_cover with ⟨S, hS_sub, hS_finite, hS_cover⟩
  -- Recast as a `Finset M` cover.
  set S' : Finset M := hS_finite.toFinset with hS'_def
  have hS_cover' : K_base ⊆ ⋃ b₀ ∈ S', loc b₀ := by
    intro b hb
    have h := hS_cover hb
    rcases Set.mem_iUnion.mp h with ⟨b₀, hb₀⟩
    rcases Set.mem_iUnion.mp hb₀ with ⟨hb₀_S, hb_in⟩
    refine Set.mem_iUnion.mpr ⟨b₀, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, hb_in⟩
    rw [hS'_def]
    exact hS_finite.mem_toFinset.mpr hb₀_S
  -- Compact subcover by `IsCompact.finite_compact_cover` (requires `R1Space`,
  -- which follows from `T2Space M`).
  rcases hK_base.finite_compact_cover (t := S') (U := loc)
    (fun b₀ _ => h_loc_open b₀) hS_cover'
    with ⟨KK, hKK_compact, hKK_sub, hKK_eq⟩
  -- For each `b₀ ∈ S'`, get a bound on `KK b₀ ⊆ loc b₀ ⊆ (chartAt H b₀).source`.
  have h_each_bound : ∀ b₀ : M,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ KK b₀,
        ‖chartGramBilin (I := I) (M := M) g b₀ b‖ ≤ C := by
    intro b₀
    exact exists_norm_bound_on_compact_subset_of_chartSource
      (I := I) (M := M) g b₀ (hKK_compact b₀)
      ((hKK_sub b₀).trans (h_loc_sub b₀))
  -- Extract `C : M → ℝ` from the existence statement (non-finset version).
  choose C h_C_nn h_C_bound using h_each_bound
  -- Take the maximum of the bounds over the finset `S'`. If `S' = ∅`, then
  -- `K_base = ⋃ ∅ = ∅` and the conclusion is vacuous.
  by_cases hS_empty : S' = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb v
    -- K_base = ⋃ b₀ ∈ ∅, KK b₀ = ∅, so hb is impossible.
    rw [hKK_eq, hS_empty] at hb
    simp at hb
  have hS_nonempty : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  set C_max : ℝ := S'.sup' hS_nonempty C with hCmax_def
  -- The maximum is non-negative: each `C b₀ ≥ 0`.
  have h_C_max_nn : 0 ≤ C_max := by
    rcases hS_nonempty with ⟨b₀, hb₀⟩
    have h_le : C b₀ ≤ C_max := Finset.le_sup' (f := C) hb₀
    exact (h_C_nn b₀).trans h_le
  refine ⟨C_max, h_C_max_nn, ?_⟩
  intro b hb v
  -- Pick `b₀ ∈ S'` with `b ∈ KK b₀`.
  rw [hKK_eq] at hb
  rcases Set.mem_iUnion.mp hb with ⟨b₀, hb₀⟩
  rcases Set.mem_iUnion.mp hb₀ with ⟨hb₀_S, hb_in⟩
  -- Bound at `b`: use Step 5 with `b₀` as the centre.
  have h_b_in_loc : b ∈ loc b₀ := hKK_sub b₀ hb_in
  have h_chart : chartAt H b = chartAt H b₀ := h_loc_const b₀ b h_b_in_loc
  have h_b_in_source : b ∈ (chartAt H b₀).source := h_loc_sub b₀ h_b_in_loc
  have h_b_in_KK : b ∈ KK b₀ := hb_in
  have h_norm_le : ‖chartGramBilin (I := I) (M := M) g b₀ b‖ ≤ C b₀ :=
    h_C_bound b₀ b h_b_in_KK
  have h_inner_le :
      g.inner b v v ≤ ‖chartGramBilin (I := I) (M := M) g b₀ b‖ * ‖v‖ ^ 2 :=
    g_inner_le_chartGramBilin_norm_sq (I := I) (M := M) g h_chart h_b_in_source v
  have h_C_le : C b₀ ≤ C_max := Finset.le_sup' (f := C) hb₀_S
  have h_norm_sq_nn : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  calc g.inner b v v
      ≤ ‖chartGramBilin (I := I) (M := M) g b₀ b‖ * ‖v‖ ^ 2 := h_inner_le
    _ ≤ C b₀ * ‖v‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right h_norm_le h_norm_sq_nn
    _ ≤ C_max * ‖v‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right h_C_le h_norm_sq_nn

/-! ## Step 9: the headline -/

/-- Headline: a uniform upper bound on `√(g.inner b v v)` for `(b, v)`
ranging over `K_base × E`, under the locality hypothesis on the chart
selection. -/
theorem g_inner_sqrt_uniform_upper_bound_on_compact
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (g : SmoothRiemannianMetric I M)
    {K_base : Set M} (hK_base : IsCompact K_base) :
    ∃ K : ℝ, 0 < K ∧ ∀ b ∈ K_base, ∀ v : E,
      Real.sqrt (g.inner b v v) ≤ K * ‖v‖ := by
  rcases exists_uniform_g_inner_upper_bound_on_compact (I := I) (M := M)
    h_atlas g hK_base with ⟨C, hC_nn, h_bound⟩
  -- Take `K := √C + 1`; this is strictly positive and majorises `√(g.inner b v v)`.
  refine ⟨Real.sqrt C + 1, ?_, ?_⟩
  · have h_sqrt_nn : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
    linarith
  intro b hb v
  -- The metric quadratic form is non-negative.
  have h_inner_nn : 0 ≤ g.inner b v v :=
    metric_inner_self_nonneg (I := I) (M := M) g b v
  have h_sq_bound : g.inner b v v ≤ C * ‖v‖ ^ 2 := h_bound b hb v
  -- Take square roots on both sides.
  have h_norm_nn : 0 ≤ ‖v‖ := norm_nonneg _
  have h_C_nn := hC_nn
  -- `√(g.inner b v v) ≤ √(C * ‖v‖²) = √C * ‖v‖`.
  have h_sqrt_le : Real.sqrt (g.inner b v v) ≤ Real.sqrt (C * ‖v‖ ^ 2) :=
    Real.sqrt_le_sqrt h_sq_bound
  have h_sqrt_prod : Real.sqrt (C * ‖v‖ ^ 2) = Real.sqrt C * ‖v‖ := by
    have h1 : Real.sqrt (C * ‖v‖ ^ 2) = Real.sqrt C * Real.sqrt (‖v‖ ^ 2) :=
      Real.sqrt_mul h_C_nn _
    have h2 : Real.sqrt (‖v‖ ^ 2) = ‖v‖ := Real.sqrt_sq h_norm_nn
    rw [h1, h2]
  rw [h_sqrt_prod] at h_sqrt_le
  -- `√C * ‖v‖ ≤ (√C + 1) * ‖v‖`.
  have h_step : Real.sqrt C * ‖v‖ ≤ (Real.sqrt C + 1) * ‖v‖ := by
    have h_sqrt_nn : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
    nlinarith [h_norm_nn]
  linarith

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
