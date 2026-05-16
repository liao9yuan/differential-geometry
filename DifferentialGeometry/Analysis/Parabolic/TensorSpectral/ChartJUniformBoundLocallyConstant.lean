import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian
import DifferentialGeometry.Geometry.LocalChartConsistency
import DifferentialGeometry.Integral.Measure.Invariance
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic

/-!
# Uniform operator-norm bounds on `chartJ α` and `chartJinv α` over a compact base set

For a smooth manifold `M` modelled on `(E, H)` with model `I`, and a fixed base
point `α : M`, this file proves uniform operator-norm bounds on the chart
Jacobian `chartJ α b` and its inverse `chartJinv α b` for `b` ranging over an
arbitrary compact subset `K ⊆ (chartAt H α).source`, under the locality
hypothesis `HasLocallyConstantChartAt H M` on the chart-selection function.

## Strategy

The chart-Jacobian `chartJ α b = (trivializationAt E (TangentSpace I) α)
.continuousLinearMapAt ℝ b` and its inverse
`chartJinv α b = (trivializationAt E (TangentSpace I) α).symmL ℝ b` are not, by
themselves, continuous in `b` because the chart-selection function jumps
between chart sources. The locality hypothesis remedies this: on a
neighbourhood `U_{b₀}` of any base point `b₀` where `chartAt H b = chartAt H b₀`
(equivalently `achart H b = achart H b₀`), the trivialisation at `b₀`
satisfies `(triv b₀).symmL b = id` and `(triv b₀).clmAt b = id`. Combining
this with Mathlib's identity
`(triv α).coordChangeL ℝ (triv β) b v = (triv β).clmAt b ((triv α).symmL b v)`
(coming from the bundle's smooth coord-change structure) yields:

* For `chartJ`, taking `α'` = `α`, `β` = `b₀` (and reading off the identity in
  reverse direction): `(triv b₀).coordChangeL ℝ (triv α) b = (triv α).clmAt b
  ∘L (triv b₀).symmL b = (triv α).clmAt b = chartJ α b` on the locality nbd.

* For `chartJinv`, taking `α'` = `α`, `β` = `b₀`: `(triv α).coordChangeL ℝ
  (triv b₀) b = (triv b₀).clmAt b ∘L (triv α).symmL b = (triv α).symmL b
  = chartJinv α b` on the locality nbd.

The `coordChangeL` CLM family is `ContMDiffOn` — hence continuous — on the
intersection of base sets, by the `ContMDiffVectorBundle ∞ E (TangentSpace I)`
Mathlib instance applied via `contMDiffOn_coordChangeL`.

A compact subset `K ⊆ (chartAt H α).source` is covered by finitely many
locality neighbourhoods, refined to lie inside `(chartAt H α).source`. The
finite-compact-cover lemma `IsCompact.finite_compact_cover` (available because
`M` is `T2`, hence `R1`) extracts compact pieces `K_i` on which the
operator-norm function is continuous and therefore bounded. The maximum of
these bounds plus `1` is a strictly positive uniform bound.

## Main results

* `chartJ_opNorm_isBounded_on_compact` — uniform op-norm bound on `chartJ α`
  over any compact `K ⊆ (chartAt H α).source`.
* `chartJinv_opNorm_isBounded_on_compact` — uniform op-norm bound on
  `chartJinv α` over any compact `K ⊆ (chartAt H α).source`.

Both headlines carry the locality hypothesis `HasLocallyConstantChartAt H M`
on the chart selection of `M` and require no Riemannian-metric structure.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-! ## Step 1: identifying `(triv b₀).symmL b` and `(triv b₀).clmAt b` with the
identity on the locality neighbourhood of `b₀` -/

/-- If `chartAt H b = chartAt H b₀`, the corresponding `achart` values agree
as subtypes. -/
private lemma achart_eq_of_chartAt_eq {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀) :
    achart H b = achart H b₀ :=
  Subtype.ext h_chart

/-- On the locality neighbourhood of `b₀`, the inverse trivialisation centred
at `b₀` evaluated at `b` is the identity. -/
private lemma trivb₀_symmL_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).symmL ℝ b = (1 : E →L[ℝ] E) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (I := I)
    (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

/-- On the locality neighbourhood of `b₀`, the forward trivialisation centred
at `b₀` evaluated at `b` is the identity. -/
private lemma trivb₀_clmAt_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b =
      (1 : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (𝕜 := ℝ) (I := I) (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

/-! ## Step 2: continuity of the `coordChangeL` CLM family on chart-source
intersections -/

/-- The map `b ↦ (triv b₀).coordChangeL ℝ (triv α) b` is `ContMDiffOn` on
`(chartAt H b₀).source ∩ (chartAt H α).source`, hence continuous. -/
private lemma continuousOn_coordChangeL_b₀_α (b₀ α : M) :
    ContinuousOn
      (fun b : M => ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E))
      ((chartAt H b₀).source ∩ (chartAt H α).source) := by
  have h_smooth :
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun b : M => ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E))
        ((trivializationAt E (TangentSpace I) b₀).baseSet ∩
          (trivializationAt E (TangentSpace I) α).baseSet) :=
    contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I) (F := E)
      (E := (TangentSpace I : M → Type _))
      (trivializationAt E (TangentSpace I) b₀)
      (trivializationAt E (TangentSpace I) α)
  have h_base_b₀ : (trivializationAt E (TangentSpace I) b₀).baseSet =
      (chartAt H b₀).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀
  have h_base_α : (trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α
  rw [h_base_b₀, h_base_α] at h_smooth
  exact h_smooth.continuousOn

/-! ## Step 3: identifying `coordChangeL` action with the bare CLM expressions on
the locality neighbourhood -/

/-- On the locality neighbourhood `U` of `b₀` (inside `(chart α).source`), the
`coordChangeL` CLM `(triv b₀).coordChangeL ℝ (triv α) b` equals
`chartJ α b`. -/
private lemma coordChangeL_eq_chartJ_of_locality
    (α : M) {b b₀ : M}
    (hb_α : b ∈ (chartAt H α).source)
    (hb_b₀ : b ∈ (chartAt H b₀).source)
    (h_chart : chartAt H b = chartAt H b₀) :
    ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E) =
      chartJ (I := I) (M := M) α b := by
  ext v
  have hb_b₀' : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact hb_b₀
  have hb_α' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hb_α
  -- Use Mathlib's `coordChangeL_apply`: maps to `(triv α).clmAt b ((triv b₀).symmL b v)`.
  have h_apply :
      ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E) v =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) b₀).symmL ℝ b v) := by
    change ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b) v =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) b₀).symmL ℝ b v)
    rw [Trivialization.coordChangeL_apply _ _ ⟨hb_b₀', hb_α'⟩]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_α',
        Bundle.Trivialization.symmL_apply]
  rw [h_apply]
  -- Now use `(triv b₀).symmL b = id` on the locality nbd.
  have h_symmL_id := trivb₀_symmL_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart hb_b₀
  have h_eq : (trivializationAt E (TangentSpace I) b₀).symmL ℝ b v = v := by
    have := congrArg (fun (f : E →L[ℝ] E) => f v) h_symmL_id
    simpa using this
  rw [h_eq]
  rfl

/-- On the locality neighbourhood `U` of `b₀` (inside `(chart α).source`), the
`coordChangeL` CLM `(triv α).coordChangeL ℝ (triv b₀) b` equals
`chartJinv α b`. -/
private lemma coordChangeL_eq_chartJinv_of_locality
    (α : M) {b b₀ : M}
    (hb_α : b ∈ (chartAt H α).source)
    (hb_b₀ : b ∈ (chartAt H b₀).source)
    (h_chart : chartAt H b = chartAt H b₀) :
    ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E) =
      chartJinv (I := I) (M := M) α b := by
  ext v
  have hb_b₀' : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
    exact hb_b₀
  have hb_α' : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
    exact hb_α
  have h_apply :
      ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E) v =
      (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) := by
    change ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b₀) b) v =
      (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v)
    rw [Trivialization.coordChangeL_apply _ _ ⟨hb_α', hb_b₀'⟩]
    rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_b₀',
        Bundle.Trivialization.symmL_apply]
  rw [h_apply]
  have h_clmAt_id := trivb₀_clmAt_eq_id_of_chartAt_eq (I := I) (M := M)
    h_chart hb_b₀
  have h_eq :
      (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt ℝ b
        ((trivializationAt E (TangentSpace I) α).symmL ℝ b v) =
        (trivializationAt E (TangentSpace I) α).symmL ℝ b v := by
    have := congrArg
      (fun (f : E →L[ℝ] E) =>
        f ((trivializationAt E (TangentSpace I) α).symmL ℝ b v)) h_clmAt_id
    simpa using this
  rw [h_eq]
  rfl

/-! ## Step 4: refining the locality neighbourhood to lie inside `(chartAt H α).source` -/

/-- Given the locality hypothesis, every `b₀ ∈ (chartAt H α).source` admits an
open neighbourhood `U` with `U ⊆ (chartAt H b₀).source` and `U ⊆ (chartAt H α).source`,
on which `chartAt H` is constant. -/
private lemma exists_loc_nhds_in_chart_source
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α b₀ : M) (hb₀_α : b₀ ∈ (chartAt H α).source) :
    ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧
      U ⊆ (chartAt H b₀).source ∧
      U ⊆ (chartAt H α).source ∧
      ∀ b ∈ U, chartAt H b = chartAt H b₀ := by
  rcases h_atlas.exists_isOpen_nhds b₀ with ⟨U₀, hU₀_open, hU₀_mem, hU₀_const⟩
  refine ⟨U₀ ∩ (chartAt H α).source,
    hU₀_open.inter (chartAt H α).open_source,
    ⟨hU₀_mem, hb₀_α⟩, ?_, ?_, ?_⟩
  · intro b hb
    have h_eq : chartAt H b = chartAt H b₀ := hU₀_const b hb.1
    have h_mem_b : b ∈ (chartAt H b).source := mem_chart_source H b
    rw [h_eq] at h_mem_b
    exact h_mem_b
  · intro b hb; exact hb.2
  · intro b hb; exact hU₀_const b hb.1

/-! ## Step 5: continuity of `b ↦ chartJ α b` and `b ↦ chartJinv α b` on the
refined locality neighbourhood -/

private lemma chartJ_continuousOn_loc
    (α b₀ : M)
    {U : Set M}
    (hU_sub_b₀ : U ⊆ (chartAt H b₀).source)
    (hU_sub_α : U ⊆ (chartAt H α).source)
    (hU_const : ∀ b ∈ U, chartAt H b = chartAt H b₀) :
    ContinuousOn (fun b : M => chartJ (I := I) (M := M) α b) U := by
  have h_coord_cont :
      ContinuousOn
        (fun b : M => ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E)) U := by
    refine (continuousOn_coordChangeL_b₀_α (I := I) b₀ α).mono ?_
    intro b hb
    exact ⟨hU_sub_b₀ hb, hU_sub_α hb⟩
  have h_eq : EqOn
      (fun b : M => chartJ (I := I) (M := M) α b)
      (fun b : M => ((trivializationAt E (TangentSpace I) b₀).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) α) b : E →L[ℝ] E)) U := by
    intro b hb
    exact (coordChangeL_eq_chartJ_of_locality (I := I) (M := M) α
      (hU_sub_α hb) (hU_sub_b₀ hb) (hU_const b hb)).symm
  exact h_coord_cont.congr h_eq

private lemma chartJinv_continuousOn_loc
    (α b₀ : M)
    {U : Set M}
    (hU_sub_b₀ : U ⊆ (chartAt H b₀).source)
    (hU_sub_α : U ⊆ (chartAt H α).source)
    (hU_const : ∀ b ∈ U, chartAt H b = chartAt H b₀) :
    ContinuousOn (fun b : M => chartJinv (I := I) (M := M) α b) U := by
  have h_coord_cont :
      ContinuousOn
        (fun b : M => ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
          (trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E)) U := by
    have h := continuousOn_coordChangeL_b₀_α (I := I) α b₀
    refine h.mono ?_
    intro b hb
    exact ⟨hU_sub_α hb, hU_sub_b₀ hb⟩
  have h_eq : EqOn
      (fun b : M => chartJinv (I := I) (M := M) α b)
      (fun b : M => ((trivializationAt E (TangentSpace I) α).coordChangeL ℝ
        (trivializationAt E (TangentSpace I) b₀) b : E →L[ℝ] E)) U := by
    intro b hb
    exact (coordChangeL_eq_chartJinv_of_locality (I := I) (M := M) α
      (hU_sub_α hb) (hU_sub_b₀ hb) (hU_const b hb)).symm
  exact h_coord_cont.congr h_eq

/-! ## Step 6: bound on a compact set from continuity -/

private lemma exists_opNorm_bound_on_compact_of_continuousOn
    (f : M → E →L[ℝ] E)
    {K : Set M} (hK : IsCompact K) (h_cont : ContinuousOn f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ‖f b‖ ≤ C := by
  by_cases h_empty : K = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    rw [h_empty] at hb
    exact absurd hb (Set.notMem_empty _)
  have h_norm_cont : ContinuousOn (fun b : M => ‖f b‖) K :=
    continuous_norm.comp_continuousOn h_cont
  have h_bdd : BddAbove ((fun b : M => ‖f b‖) '' K) :=
    hK.bddAbove_image h_norm_cont
  rcases h_bdd with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  exact (hC ⟨b, hb, rfl⟩).trans (le_max_left _ _)

/-! ## Step 7: the generic compact-cover assembly -/

/-- Under the locality hypothesis, any function `f : M → E →L[ℝ] E` that is
continuous on every refined locality neighbourhood admits a uniform
operator-norm bound on any compact `K ⊆ (chartAt H α).source`. -/
private lemma exists_uniform_opNorm_bound_via_locality
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (f : M → E →L[ℝ] E)
    (h_cont_loc :
      ∀ b₀ : M, b₀ ∈ (chartAt H α).source →
        ∀ U : Set M, b₀ ∈ U →
          U ⊆ (chartAt H b₀).source → U ⊆ (chartAt H α).source →
          (∀ b ∈ U, chartAt H b = chartAt H b₀) →
          ContinuousOn f U)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ‖f b‖ ≤ C := by
  classical
  -- Choose, for each `b₀ : M`, a refined locality neighbourhood when
  -- `b₀ ∈ (chartAt H α).source`, and the empty set otherwise.
  let loc : M → Set M := fun b₀ =>
    if hb₀ : b₀ ∈ (chartAt H α).source then
      (exists_loc_nhds_in_chart_source (H := H) (M := M) h_atlas α b₀ hb₀).choose
    else ∅
  have h_loc_open : ∀ b₀ : M, IsOpen (loc b₀) := by
    intro b₀
    simp only [loc]
    split_ifs with hb₀
    · exact (exists_loc_nhds_in_chart_source (H := H) (M := M)
        h_atlas α b₀ hb₀).choose_spec.1
    · exact isOpen_empty
  have h_loc_mem : ∀ b₀ ∈ K, b₀ ∈ loc b₀ := by
    intro b₀ hb₀
    have hb₀_α : b₀ ∈ (chartAt H α).source := hKsub hb₀
    simp only [loc, dif_pos hb₀_α]
    exact (exists_loc_nhds_in_chart_source (H := H) (M := M)
      h_atlas α b₀ hb₀_α).choose_spec.2.1
  have h_loc_sub_b₀ : ∀ b₀ ∈ K, loc b₀ ⊆ (chartAt H b₀).source := by
    intro b₀ hb₀
    have hb₀_α : b₀ ∈ (chartAt H α).source := hKsub hb₀
    simp only [loc, dif_pos hb₀_α]
    exact (exists_loc_nhds_in_chart_source (H := H) (M := M)
      h_atlas α b₀ hb₀_α).choose_spec.2.2.1
  have h_loc_sub_α : ∀ b₀ ∈ K, loc b₀ ⊆ (chartAt H α).source := by
    intro b₀ hb₀
    have hb₀_α : b₀ ∈ (chartAt H α).source := hKsub hb₀
    simp only [loc, dif_pos hb₀_α]
    exact (exists_loc_nhds_in_chart_source (H := H) (M := M)
      h_atlas α b₀ hb₀_α).choose_spec.2.2.2.1
  have h_loc_const : ∀ b₀ ∈ K, ∀ b ∈ loc b₀, chartAt H b = chartAt H b₀ := by
    intro b₀ hb₀
    have hb₀_α : b₀ ∈ (chartAt H α).source := hKsub hb₀
    simp only [loc, dif_pos hb₀_α]
    exact (exists_loc_nhds_in_chart_source (H := H) (M := M)
      h_atlas α b₀ hb₀_α).choose_spec.2.2.2.2
  -- Open cover of `K` by `loc b₀` for `b₀ ∈ K`.
  have h_cover : K ⊆ ⋃ b₀ ∈ K, loc b₀ := by
    intro b hb
    exact Set.mem_iUnion₂.mpr ⟨b, hb, h_loc_mem b hb⟩
  -- Finite subcover.
  rcases hK.elim_finite_subcover_image (b := K) (c := loc)
    (fun b₀ _ => h_loc_open b₀) h_cover with
    ⟨S, hS_sub, hS_finite, hS_cover⟩
  set S' : Finset M := hS_finite.toFinset with hS'_def
  have hS_cover' : K ⊆ ⋃ b₀ ∈ S', loc b₀ := by
    intro b hb
    rcases Set.mem_iUnion.mp (hS_cover hb) with ⟨b₀, hb₀⟩
    rcases Set.mem_iUnion.mp hb₀ with ⟨hb₀_S, hb_in⟩
    refine Set.mem_iUnion.mpr ⟨b₀, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, hb_in⟩
    rw [hS'_def]
    exact hS_finite.mem_toFinset.mpr hb₀_S
  have hS_sub_K : ∀ b₀ ∈ S', b₀ ∈ K := by
    intro b₀ hb₀
    rw [hS'_def] at hb₀
    exact hS_sub (hS_finite.mem_toFinset.mp hb₀)
  -- Compact cover.
  rcases hK.finite_compact_cover (t := S') (U := loc)
    (fun b₀ _ => h_loc_open b₀) hS_cover' with
    ⟨KK, hKK_compact, hKK_sub, hKK_eq⟩
  -- For each `b₀ ∈ S'`, get a bound on `KK b₀`.
  have h_each_bound : ∀ b₀ ∈ S',
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ KK b₀, ‖f b‖ ≤ C := by
    intro b₀ hb₀_S
    have hb₀_K : b₀ ∈ K := hS_sub_K b₀ hb₀_S
    have hb₀_α : b₀ ∈ (chartAt H α).source := hKsub hb₀_K
    have h_mem : b₀ ∈ loc b₀ := h_loc_mem b₀ hb₀_K
    have h_sub_b₀ : loc b₀ ⊆ (chartAt H b₀).source := h_loc_sub_b₀ b₀ hb₀_K
    have h_sub_α : loc b₀ ⊆ (chartAt H α).source := h_loc_sub_α b₀ hb₀_K
    have h_const : ∀ b ∈ loc b₀, chartAt H b = chartAt H b₀ :=
      h_loc_const b₀ hb₀_K
    have h_cont : ContinuousOn f (loc b₀) :=
      h_cont_loc b₀ hb₀_α (loc b₀) h_mem h_sub_b₀ h_sub_α h_const
    have h_cont_KK : ContinuousOn f (KK b₀) := h_cont.mono (hKK_sub b₀)
    exact exists_opNorm_bound_on_compact_of_continuousOn
      (f := f) (hK := hKK_compact b₀) (h_cont := h_cont_KK)
  -- Take maximum of bounds.
  by_cases hS_empty : S' = ∅
  · -- `S' = ∅` ⟹ `K = ∅`; take `C = 1`.
    refine ⟨1, one_pos, ?_⟩
    intro b hb
    rw [hKK_eq, hS_empty] at hb
    simp at hb
  have hS_nonempty : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  let C : M → ℝ := fun b₀ =>
    if hb₀ : b₀ ∈ S' then (h_each_bound b₀ hb₀).choose else 0
  have h_C_nn : ∀ b₀ ∈ S', 0 ≤ C b₀ := by
    intro b₀ hb₀
    simp only [C, dif_pos hb₀]
    exact (h_each_bound b₀ hb₀).choose_spec.1
  have h_C_bound : ∀ b₀ ∈ S', ∀ b ∈ KK b₀, ‖f b‖ ≤ C b₀ := by
    intro b₀ hb₀
    simp only [C, dif_pos hb₀]
    exact (h_each_bound b₀ hb₀).choose_spec.2
  set C_max : ℝ := S'.sup' hS_nonempty C with hCmax_def
  have h_C_max_nn : 0 ≤ C_max := by
    rcases hS_nonempty with ⟨b₀, hb₀⟩
    have h_le : C b₀ ≤ C_max := Finset.le_sup' (f := C) hb₀
    exact (h_C_nn b₀ hb₀).trans h_le
  refine ⟨C_max + 1, by linarith, ?_⟩
  intro b hb
  rw [hKK_eq] at hb
  rcases Set.mem_iUnion.mp hb with ⟨b₀, hb₀⟩
  rcases Set.mem_iUnion.mp hb₀ with ⟨hb₀_S, hb_in⟩
  have h_bound : ‖f b‖ ≤ C b₀ := h_C_bound b₀ hb₀_S b hb_in
  have h_le : C b₀ ≤ C_max := Finset.le_sup' (f := C) hb₀_S
  linarith

/-! ## Step 8: the two headlines -/

/-- Uniform operator-norm bound on `chartJ α b` over any compact subset of
`(chartAt H α).source`. -/
theorem chartJ_opNorm_isBounded_on_compact
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ‖chartJ (I := I) (M := M) α b‖ ≤ C :=
  exists_uniform_opNorm_bound_via_locality
    h_atlas α (fun b : M => chartJ (I := I) (M := M) α b)
    (fun b₀ _hb₀_α _U _hU_mem hU_sub_b₀ hU_sub_α hU_const =>
      chartJ_continuousOn_loc (I := I) α b₀ hU_sub_b₀ hU_sub_α hU_const)
    hK hKsub

/-- Uniform operator-norm bound on `chartJinv α b` over any compact subset of
`(chartAt H α).source`. -/
theorem chartJinv_opNorm_isBounded_on_compact
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ‖chartJinv (I := I) (M := M) α b‖ ≤ C :=
  exists_uniform_opNorm_bound_via_locality
    h_atlas α (fun b : M => chartJinv (I := I) (M := M) α b)
    (fun b₀ _hb₀_α _U _hU_mem hU_sub_b₀ hU_sub_α hU_const =>
      chartJinv_continuousOn_loc (I := I) α b₀ hU_sub_b₀ hU_sub_α hU_const)
    hK hKsub

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
