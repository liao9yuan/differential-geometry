import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivative
import DifferentialGeometry.Tensor.RSTensor.TensorRSBundleLocalityIdentities
import DifferentialGeometry.Geometry.LocalChartConsistency
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic

/-!
# Uniform op-norm bound on the chart-`(r, s)` fibre forward map over compact base sets

Forward analogue of `tensorRSChartFiberFromModel_opNorm_isBounded_on_compact`:
the family
`(triv α).continuousLinearMapAt ℝ b : TensorRSSpace r s I b →L[ℝ] TensorRSModel r s ℝ E`
admits a uniform pointwise op-norm bound on any compact `K ⊆ (chartAt H α).source`.

Strategy: on the locality neighbourhood of `b₀ ∈ K`, the forward locality
identity gives `(triv b₀).clmAt ℝ b` equal to the canonical
`TensorRSSpace b ≃L TensorRSModel` CLM, so `‖(triv b₀).clmAt ℝ b T‖ = ‖T‖`. The
`coordChangeL` formula then expresses `(triv α).clmAt ℝ b T` as
`coordChangeL b₀ α b ((triv b₀).clmAt ℝ b T)`, yielding
`‖(triv α).clmAt ℝ b T‖ ≤ ‖coordChangeL b₀ α b‖ · ‖T‖`. A finite compact cover
plus operator-norm continuity of `coordChangeL` yields the uniform constant.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Norm pullback identity. -/
private lemma tensorRSSpace_norm_eq_fwd (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    ‖T‖ = ‖tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s b T‖ :=
  rfl

/-- CLM-level locality identity for the forward direction at `b₀`. -/
private lemma tensorRS_trivAt_clmAt_eq_CLE_on_locality_fwd
    (r s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source) :
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b :
        TensorRSSpace r s I b →L[ℝ] TensorRSModel r s ℝ E) =
      ((tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s
        b).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro T
  apply ContinuousLinearMap.ext
  intro D_α
  have h_subB := tensorRS_trivAt_continuousLinearMapAt_apply_eq_self_on_locality
    (I := I) (M := M) (r := r) (s := s) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src) (T := T) (D_α := D_α)
  change (((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T)
        D_α : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
      (tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s b T) D_α
  rw [h_subB]
  rfl

/-- Norm of forward trivialisation equals fibre norm on locality. -/
private lemma trivAt_clmAt_norm_eq_on_locality
    (r s : ℕ) (b₀ : M) {b : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (h_src : b ∈ (chartAt H b₀).source)
    (T : TensorRSSpace r s I b) :
    ‖((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T :
        TensorRSModel r s ℝ E)‖ = ‖T‖ := by
  have h_clm := tensorRS_trivAt_clmAt_eq_CLE_on_locality_fwd
    (I := I) (M := M) (r := r) (s := s) (b₀ := b₀) (b := b)
    (h_chart := h_chart) (h_src := h_src)
  have h_apply :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T :
          TensorRSModel r s ℝ E) =
        ((tensorRSSpace_continuousLinearEquiv (𝕜 := ℝ) (M := M) (I := I) r s b)
          T : TensorRSModel r s ℝ E) := by
    have := congrArg
      (fun (f : TensorRSSpace r s I b →L[ℝ] TensorRSModel r s ℝ E) => f T) h_clm
    simpa using this
  rw [h_apply]
  exact (tensorRSSpace_norm_eq_fwd (I := I) (M := M) r s b T).symm

/-- Forward CLM norm bound by `coordChangeL` op-norm times fibre norm. -/
private lemma chartFiberToModel_norm_le_coordChangeL_norm_on_locality
    (r s : ℕ) (α : M) {b₀ b : M}
    (hb_α : b ∈ (chartAt H α).source)
    (hb_b₀ : b ∈ (chartAt H b₀).source)
    (h_chart : chartAt H b = chartAt H b₀)
    (T : TensorRSSpace r s I b) :
    ‖((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T :
        TensorRSModel r s ℝ E)‖ ≤
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) b
            : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)‖ * ‖T‖ := by
  have hb_tan_α : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]; exact hb_α
  have hb_tan_b₀ : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]; exact hb_b₀
  have hb_α' : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := ⟨hb_tan_α, hb_tan_α⟩
  have hb_b₀' : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀).baseSet := ⟨hb_tan_b₀, hb_tan_b₀⟩
  have h_eq :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T :
          TensorRSModel r s ℝ E) =
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
          (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α) b
              : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T) := by
    set eα := trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α with heα
    set eb₀ := trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) b₀ with heb₀
    have h_cc :
        (eb₀.coordChangeL ℝ eα b
            : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
          (eb₀.continuousLinearMapAt ℝ b T) =
        eα.continuousLinearMapAt ℝ b
          (eb₀.symmL ℝ b (eb₀.continuousLinearMapAt ℝ b T)) := by
      change (eb₀.coordChangeL ℝ eα b)
          (eb₀.continuousLinearMapAt ℝ b T) = _
      rw [Trivialization.coordChangeL_apply _ _ ⟨hb_b₀', hb_α'⟩]
      simp only [Bundle.Trivialization.continuousLinearMapAt_apply,
          Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_α',
          Bundle.Trivialization.coe_linearMapAt_of_mem _ hb_b₀',
          Bundle.Trivialization.symmL_apply]
    have h_inv : eb₀.symmL ℝ b (eb₀.continuousLinearMapAt ℝ b T) = T :=
      Trivialization.symmL_continuousLinearMapAt (R := ℝ) eb₀ hb_b₀' T
    rw [h_cc, h_inv]
  have h_norm_T :
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T :
          TensorRSModel r s ℝ E)‖ = ‖T‖ :=
    trivAt_clmAt_norm_eq_on_locality (I := I) (M := M) (r := r) (s := s)
      (b₀ := b₀) (b := b) (h_chart := h_chart) (h_src := hb_b₀) T
  rw [h_eq]
  have h_le_op := ContinuousLinearMap.le_opNorm
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α) b
          : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).continuousLinearMapAt ℝ b T)
  rw [h_norm_T] at h_le_op
  exact h_le_op

/-- Continuity of `b ↦ coordChangeL b₀ α b` on the chart-source intersection. -/
private lemma continuousOn_RS_coordChangeL_b₀_α (r s : ℕ) (α b₀ : M) :
    ContinuousOn
      (fun b : M => ((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
          (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α) b
              : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E))
      ((chartAt H b₀).source ∩ (chartAt H α).source) := by
  have h_smooth :
      ContMDiffOn I 𝓘(ℝ, TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E) ∞
        (fun b : M => ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
            (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α) b
                : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E))
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).baseSet ∩
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet) :=
    contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I)
      (F := TensorRSModel r s ℝ E)
      (E := fun y : M => TensorRSSpace r s I y)
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀)
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α)
  have h_base_α : (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (chartAt H α).source := by
    change (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
    rw [inter_self, TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) α]
  have h_base_b₀ : (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).baseSet =
      (chartAt H b₀).source := by
    change (trivializationAt E (TangentSpace I) b₀).baseSet ∩
        (trivializationAt E (TangentSpace I) b₀).baseSet = (chartAt H b₀).source
    rw [inter_self, TangentBundle.trivializationAt_baseSet (𝕜 := ℝ) (I := I) b₀]
  rw [h_base_α, h_base_b₀] at h_smooth
  exact h_smooth.continuousOn

/-- Locality neighbourhood of `b₀` inside `(chartAt H α).source`. -/
private lemma exists_loc_nhds_in_chart_source_fwd
    (h_atlas : HasLocallyConstantChartAt H M)
    (α b₀ : M) (hb₀_α : b₀ ∈ (chartAt H α).source) :
    ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧
      U ⊆ (chartAt H b₀).source ∧ U ⊆ (chartAt H α).source ∧
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

/-- Op-norm bound on a compact from op-norm continuity. -/
private lemma exists_opNorm_bound_on_compact_of_continuousOn_fwd
    {r s : ℕ} (f : M → TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
    {K : Set M} (hK : IsCompact K) (h_cont : ContinuousOn f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K, ‖f b‖ ≤ C := by
  by_cases h_empty : K = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb; rw [h_empty] at hb; exact absurd hb (Set.notMem_empty _)
  have h_norm_cont : ContinuousOn (fun b : M => ‖f b‖) K :=
    continuous_norm.comp_continuousOn h_cont
  have h_bdd : BddAbove ((fun b : M => ‖f b‖) '' K) :=
    hK.bddAbove_image h_norm_cont
  rcases h_bdd with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  exact (hC ⟨b, hb, rfl⟩).trans (le_max_left _ _)

/-- Uniform pointwise op-norm bound on the chart-`(r, s)` fibre forward
trivialisation over any compact subset of the chart-`α` source. -/
theorem tensorRSChartFiberToModel_opNorm_isBounded_on_compact
    (h_atlas : HasLocallyConstantChartAt H M)
    (r s : ℕ) (α : M) {K : Set M} (hK : IsCompact K)
    (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ T : TensorRSSpace r s I b,
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T :
          TensorRSModel r s ℝ E)‖ ≤ C * ‖T‖ := by
  classical
  let loc : M → Set M := fun b₀ =>
    if hb₀ : b₀ ∈ (chartAt H α).source then
      (exists_loc_nhds_in_chart_source_fwd (H := H) (M := M)
        h_atlas α b₀ hb₀).choose
    else ∅
  have h_loc_open : ∀ b₀ : M, IsOpen (loc b₀) := by
    intro b₀; simp only [loc]
    split_ifs with hb₀
    · exact (exists_loc_nhds_in_chart_source_fwd (H := H) (M := M)
        h_atlas α b₀ hb₀).choose_spec.1
    · exact isOpen_empty
  have h_loc_mem : ∀ b₀ ∈ K, b₀ ∈ loc b₀ := by
    intro b₀ hb₀
    have hb₀_α : b₀ ∈ (chartAt H α).source := hKsub hb₀
    simp only [loc, dif_pos hb₀_α]
    exact (exists_loc_nhds_in_chart_source_fwd (H := H) (M := M)
      h_atlas α b₀ hb₀_α).choose_spec.2.1
  have h_loc_sub_b₀ : ∀ b₀ ∈ K, loc b₀ ⊆ (chartAt H b₀).source := by
    intro b₀ hb₀
    have hb₀_α : b₀ ∈ (chartAt H α).source := hKsub hb₀
    simp only [loc, dif_pos hb₀_α]
    exact (exists_loc_nhds_in_chart_source_fwd (H := H) (M := M)
      h_atlas α b₀ hb₀_α).choose_spec.2.2.1
  have h_loc_sub_α : ∀ b₀ ∈ K, loc b₀ ⊆ (chartAt H α).source := by
    intro b₀ hb₀
    have hb₀_α : b₀ ∈ (chartAt H α).source := hKsub hb₀
    simp only [loc, dif_pos hb₀_α]
    exact (exists_loc_nhds_in_chart_source_fwd (H := H) (M := M)
      h_atlas α b₀ hb₀_α).choose_spec.2.2.2.1
  have h_loc_const : ∀ b₀ ∈ K, ∀ b ∈ loc b₀, chartAt H b = chartAt H b₀ := by
    intro b₀ hb₀
    have hb₀_α : b₀ ∈ (chartAt H α).source := hKsub hb₀
    simp only [loc, dif_pos hb₀_α]
    exact (exists_loc_nhds_in_chart_source_fwd (H := H) (M := M)
      h_atlas α b₀ hb₀_α).choose_spec.2.2.2.2
  have h_cover : K ⊆ ⋃ b₀ ∈ K, loc b₀ := fun b hb =>
    Set.mem_iUnion₂.mpr ⟨b, hb, h_loc_mem b hb⟩
  rcases hK.elim_finite_subcover_image (b := K) (c := loc)
    (fun b₀ _ => h_loc_open b₀) h_cover with ⟨S, hS_sub, hS_finite, hS_cover⟩
  set S' : Finset M := hS_finite.toFinset with hS'_def
  have hS_cover' : K ⊆ ⋃ b₀ ∈ S', loc b₀ := by
    intro b hb
    rcases Set.mem_iUnion.mp (hS_cover hb) with ⟨b₀, hb₀⟩
    rcases Set.mem_iUnion.mp hb₀ with ⟨hb₀_S, hb_in⟩
    refine Set.mem_iUnion.mpr ⟨b₀, ?_⟩
    refine Set.mem_iUnion.mpr ⟨?_, hb_in⟩
    rw [hS'_def]; exact hS_finite.mem_toFinset.mpr hb₀_S
  have hS_sub_K : ∀ b₀ ∈ S', b₀ ∈ K := by
    intro b₀ hb₀; rw [hS'_def] at hb₀
    exact hS_sub (hS_finite.mem_toFinset.mp hb₀)
  rcases hK.finite_compact_cover (t := S') (U := loc)
    (fun b₀ _ => h_loc_open b₀) hS_cover' with
    ⟨KK, hKK_compact, hKK_sub, hKK_eq⟩
  have h_each_bound : ∀ b₀ ∈ S',
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ KK b₀,
        ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
          (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α) b
              : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)‖ ≤ C := by
    intro b₀ hb₀_S
    have hb₀_K : b₀ ∈ K := hS_sub_K b₀ hb₀_S
    have h_sub_b₀ : loc b₀ ⊆ (chartAt H b₀).source := h_loc_sub_b₀ b₀ hb₀_K
    have h_sub_α : loc b₀ ⊆ (chartAt H α).source := h_loc_sub_α b₀ hb₀_K
    have h_cc_cont :
        ContinuousOn
          (fun b : M => ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
              (trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α) b
                  : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E))
          (loc b₀) := by
      refine (continuousOn_RS_coordChangeL_b₀_α (I := I) (M := M)
        (r := r) (s := s) α b₀).mono ?_
      intro b hb; exact ⟨h_sub_b₀ hb, h_sub_α hb⟩
    exact exists_opNorm_bound_on_compact_of_continuousOn_fwd (M := M) (E := E)
      (r := r) (s := s) (f := fun b : M =>
        ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
            (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α) b))
      (hK := hKK_compact b₀) (h_cont := h_cc_cont.mono (hKK_sub b₀))
  by_cases hS_empty : S' = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro b hb _
    rw [hKK_eq, hS_empty] at hb; simp at hb
  have hS_nonempty : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  let C : M → ℝ := fun b₀ =>
    if hb₀ : b₀ ∈ S' then (h_each_bound b₀ hb₀).choose else 0
  have h_C_nn : ∀ b₀ ∈ S', 0 ≤ C b₀ := by
    intro b₀ hb₀; simp only [C, dif_pos hb₀]
    exact (h_each_bound b₀ hb₀).choose_spec.1
  have h_C_bound : ∀ b₀ ∈ S', ∀ b ∈ KK b₀,
      ‖((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
        (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α) b
            : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)‖ ≤ C b₀ := by
    intro b₀ hb₀; simp only [C, dif_pos hb₀]
    exact (h_each_bound b₀ hb₀).choose_spec.2
  set C_max : ℝ := S'.sup' hS_nonempty C with hCmax_def
  have h_C_max_nn : 0 ≤ C_max := by
    rcases hS_nonempty with ⟨b₀, hb₀⟩
    exact (h_C_nn b₀ hb₀).trans (Finset.le_sup' (f := C) hb₀)
  refine ⟨C_max + 1, by linarith, ?_⟩
  intro b hb T
  rw [hKK_eq] at hb
  rcases Set.mem_iUnion.mp hb with ⟨b₀, hb₀⟩
  rcases Set.mem_iUnion.mp hb₀ with ⟨hb₀_S, hb_in⟩
  have hb₀_K : b₀ ∈ K := hS_sub_K b₀ hb₀_S
  have hb_loc : b ∈ loc b₀ := hKK_sub b₀ hb_in
  have hb_α : b ∈ (chartAt H α).source := h_loc_sub_α b₀ hb₀_K hb_loc
  have hb_b₀ : b ∈ (chartAt H b₀).source := h_loc_sub_b₀ b₀ hb₀_K hb_loc
  have h_chart : chartAt H b = chartAt H b₀ := h_loc_const b₀ hb₀_K b hb_loc
  have h_le_norm := chartFiberToModel_norm_le_coordChangeL_norm_on_locality
    (I := I) (M := M) (r := r) (s := s) (α := α) (b₀ := b₀) (b := b)
    hb_α hb_b₀ h_chart T
  have h_cc_bound : ‖((trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) b₀).coordChangeL ℝ
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α) b
          : TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)‖ ≤ C b₀ :=
    h_C_bound b₀ hb₀_S b hb_in
  have h_norm_nn : 0 ≤ ‖T‖ := norm_nonneg _
  have h_le_Cmax : C b₀ ≤ C_max := Finset.le_sup' (f := C) hb₀_S
  calc ‖((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b T :
            TensorRSModel r s ℝ E)‖
      ≤ _ := h_le_norm
    _ ≤ C b₀ * ‖T‖ := mul_le_mul_of_nonneg_right h_cc_bound h_norm_nn
    _ ≤ C_max * ‖T‖ := mul_le_mul_of_nonneg_right h_le_Cmax h_norm_nn
    _ ≤ (C_max + 1) * ‖T‖ := mul_le_mul_of_nonneg_right (by linarith) h_norm_nn

end DifferentialGeometry.Integral.Connection

end
