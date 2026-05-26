import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.TensorChartTransition
import DifferentialGeometry.Analysis.Laplacian.MetricExtension

namespace DifferentialGeometry.PDE.RicciFlow.HebeyBlock

open Bundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Chart-Euclidean pull-back of the tensor-component transition coefficient

For two chart base points `α, β : M`, the scalar transition coefficient
`transitionCoeff r s α β P₀ Q : M → ℝ` of the `(r, s)`-tensor bundle is
`C^∞` on the chart overlap `(chartAt H α).source ∩ (chartAt H β).source`
(see `contMDiffOn_transitionCoeff`). Pulling back through the chart at `α`
and the linear identification `toEuclidean`, we obtain a function defined
on `chartTargetEuclid α ⊆ EuclideanSpace ℝ (Fin n)` that is `ContDiffOn ℝ ∞`
on the open subset where the chart-α point also lies in the chart at `β`.

The pull-back is the natural object that downstream chart-Sobolev consumers
estimate, since their Sobolev norms are formulated on `EuclideanSpace`.
-/

/-- The chart-α Euclidean pull-back of the tensor-component transition
coefficient `transitionCoeff r s α β P₀ Q`. -/
noncomputable def transitionCoeffOnEuclid
    (r s : ℕ) (α β : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (y : EuclN) : ℝ :=
  transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

@[simp] lemma transitionCoeffOnEuclid_def
    (r s : ℕ) (α β : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (y : EuclN) :
    transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q y =
      transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

/-! ## The Euclidean overlap set

The natural smoothness domain of `transitionCoeffOnEuclid` is the subset of
`chartTargetEuclid α` whose chart-α image lies in `(chartAt H β).source`,
i.e. the chart overlap viewed through chart-α Euclidean coordinates.
We do not need to identify this set as `chartTargetEuclid α ∩ …` in a closed
form; we use it only via its (compact) subsets `K_E` carried by the user.
-/

/-- The set of `y ∈ EuclN` such that the corresponding manifold point
`(extChartAt I α).symm ((toEuclidean).symm y)` lies in
`(chartAt H α).source ∩ (chartAt H β).source`. This is the natural
chart-α Euclidean domain on which `transitionCoeffOnEuclid r s α β P₀ Q`
is `ContDiffOn ℝ ∞`. -/
noncomputable def chartTransitionEuclidOverlap (α β : M) : Set EuclN :=
  {y | y ∈ chartTargetEuclid (I := I) (M := M) α ∧
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H β).source}

/-- Membership in `chartTransitionEuclidOverlap α β` unfolded. -/
@[simp] lemma mem_chartTransitionEuclidOverlap {α β : M} {y : EuclN} :
    y ∈ chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β ↔
      y ∈ chartTargetEuclid (I := I) (M := M) α ∧
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H β).source :=
  Iff.rfl

/-! ## The Euclidean overlap set is open

`chartTargetEuclid α` is open under `[I.Boundaryless]`, and the second
condition `(extChartAt I α).symm (…) ∈ (chartAt H β).source` is the
preimage under a `ContinuousOn` map of an open set. The intersection is
open in `EuclN`.
-/

private lemma isOpen_chartTransitionEuclidOverlap (α β : M) :
    IsOpen (chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β) := by
  classical
  -- The overlap is `U ∩ V` where `U = chartTargetEuclid α` and
  -- `V = preimage of (chartAt H β).source` under `(extChartAt I α).symm ∘
  -- (toEuclidean).symm`, intersected with `U`.
  set U : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hU_def
  have hU_open : IsOpen U := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The composition `(extChartAt I α).symm ∘ (toEuclidean).symm` is
  -- continuous on `U` (image goes to chart source on `M`).
  -- We show the overlap equals the preimage `U ∩ f ⁻¹' (chartAt H β).source`,
  -- and that this preimage is open in `EuclN`.
  -- The function:
  let f : EuclN → M := fun y => (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
  -- Continuity of `f` on `U`: factor through `EuclN → E → M`.
  have h_toE_cont : Continuous (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (toEuclidean (E := E)).symm.continuous
  -- `(extChartAt I α).symm` is continuous on `(extChartAt I α).target`, and
  -- `toEuclidean.symm` maps `U` into the target.
  have h_chart_symm_contOn : ContinuousOn (extChartAt I α).symm
      ((extChartAt I α).target) := by
    have h := continuousOn_extChartAt_symm (I := I) α
    exact h
  have h_maps : Set.MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y) U
      ((extChartAt I α).target) := by
    intro y hy
    exact toEuclidean_symm_mem_target (I := I) hy
  have hf_contOn : ContinuousOn f U :=
    h_chart_symm_contOn.comp h_toE_cont.continuousOn h_maps
  -- Pre-image of an open set under a `ContinuousOn` function on an open set
  -- intersected with that open set is open.
  have h_pre_open : IsOpen (U ∩ f ⁻¹' (chartAt H β).source) := by
    have h_β_open : IsOpen ((chartAt H β).source) :=
      (chartAt H β).open_source
    -- `f` is `ContinuousOn U`, `U` open, target open ⇒
    -- preimage relative to `U` is open.
    have h_preU : IsOpen (U ∩ f ⁻¹' (chartAt H β).source) := by
      rw [show U ∩ f ⁻¹' (chartAt H β).source =
          f ⁻¹' (chartAt H β).source ∩ U from Set.inter_comm _ _]
      have h_continuousOn_open :=
        hf_contOn.isOpen_inter_preimage hU_open h_β_open
      simpa [Set.inter_comm] using h_continuousOn_open
    exact h_preU
  -- Rewrite the overlap as `U ∩ f ⁻¹' (chartAt H β).source`.
  have h_eq : chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β =
      U ∩ f ⁻¹' (chartAt H β).source := by
    ext y
    constructor
    · rintro ⟨hyU, hyβ⟩
      exact ⟨hyU, hyβ⟩
    · rintro ⟨hyU, hyβ⟩
      exact ⟨hyU, hyβ⟩
  rw [h_eq]
  exact h_pre_open

/-! ## `transitionCoeffOnEuclid` is `ContDiffOn ℝ ∞` on the Euclidean overlap

The proof composes:

* `contMDiffOn_transitionCoeff` (smoothness on the manifold chart overlap),
* `contMDiffOn_chart_symm` (smoothness of `(extChartAt I α).symm ∘
  (toEuclidean).symm` as a manifold map on `chartTargetEuclid α`),
* `contMDiffOn_iff_contDiffOn` (transfer between scalar-valued
  `ContMDiffOn` on Euclidean domains and `ContDiffOn ℝ`).
-/

/-- `transitionCoeffOnEuclid r s α β P₀ Q` is `ContDiffOn ℝ ∞` on the
chart-α Euclidean overlap set. -/
lemma transitionCoeffOnEuclid_contDiffOn
    (r s : ℕ) (α β : M)
    (P₀ Q : TensorCompIdx (E := E) r s) :
    ContDiffOn ℝ ∞ (transitionCoeffOnEuclid (E := E) (I := I) (M := M)
        r s α β P₀ Q)
      (chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β) := by
  classical
  -- The chart-α symm composition is smooth on `chartTargetEuclid α`.
  have h_chart_symm : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    contMDiffOn_chart_symm (I := I) α
  -- The transition coefficient is `C^∞` on the manifold chart overlap.
  have h_tc : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q)
      ((chartAt H α).source ∩ (chartAt H β).source) :=
    contMDiffOn_transitionCoeff (E := E) (I := I) (M := M) r s α β P₀ Q
  -- The chart-symm composition maps the Euclidean overlap into the manifold
  -- chart overlap. Membership in `chartTransitionEuclidOverlap α β` carries
  -- both pieces of information directly.
  have h_maps : Set.MapsTo
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β)
      ((chartAt H α).source ∩ (chartAt H β).source) := by
    intro y hy
    refine ⟨?_, hy.2⟩
    -- chart-α membership: chart-symm of a chart-target point is in chart source.
    have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
      toEuclidean_symm_mem_target (I := I) hy.1
    have h_src : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
        (extChartAt I α).source :=
      (extChartAt I α).map_target h_tgt
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at h_src
  -- Restrict `h_chart_symm` to the (open subset) chart-transition overlap.
  have h_overlap_subset_target :
      chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β ⊆
        chartTargetEuclid (I := I) (M := M) α := fun y hy => hy.1
  have h_chart_symm_sub : ContMDiffOn 𝓘(ℝ, EuclN) I ∞
      (fun y : EuclN => (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β) :=
    h_chart_symm.mono h_overlap_subset_target
  -- Compose to get manifold-level smoothness of the scalar pull-back.
  have h_comp : ContMDiffOn 𝓘(ℝ, EuclN) 𝓘(ℝ, ℝ) ∞
      (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q)
      (chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β) :=
    h_tc.comp h_chart_symm_sub h_maps
  -- Transfer to `ContDiffOn ℝ`.
  exact (contMDiffOn_iff_contDiffOn).mp h_comp

/-! ## Chart-`C^k` operator-norm bound for the tensor-component transition matrix

The headline theorem. For two chart base points `α, β : M` and a compact subset
`K_E ⊆ chartTargetEuclid α` whose chart-α image lies inside `(chartAt H β).source`,
there is a non-negative constant `C(g, r, s, k, α, β, K_E) ≥ 0` such that for every
iterated Fréchet-derivative order `j ∈ Finset.range k`, every component multi-index
pair `(P₀, Q) : TensorCompIdx r s × TensorCompIdx r s`, and every `y ∈ K_E`,
the iterated Fréchet derivative operator norm of
`transitionCoeffOnEuclid r s α β P₀ Q` is bounded by `C`.

The constant depends only on the data above; it is uniform over the (finite)
component multi-index pair domain and over the chart-α Euclidean point.

# Proof outline

1. By `transitionCoeffOnEuclid_contDiffOn`, the pull-back is `ContDiffOn ℝ ∞`
   on the (open) Euclidean overlap `U`.
2. `K_E ⊆ U` is compact, so for each fixed order `j` and each fixed
   `(P₀, Q)` the continuous function `y ↦ ‖iteratedFDerivWithin ℝ j … y‖`
   attains a maximum on `K_E`, giving a per-`(j, P₀, Q)` bound.
3. On the open `U` (which equals its interior), `iteratedFDerivWithin ℝ j … U y`
   agrees with `iteratedFDeriv ℝ j … y` (the chart pull-back is defined on all
   of `EuclN`, but the iterated Fréchet derivatives only agree on the open
   subset `U`).
4. The maximum of the per-`(j, P₀, Q)` bounds over the finite product
   `Finset.range k ×ˢ Finset.univ ×ˢ Finset.univ` is a single non-negative
   real constant.

# Why a compact subset, not the whole chart-target

The Euclidean overlap `chartTransitionEuclidOverlap α β` is open but not
precompact in general (the chart-α image of `(chartAt H β).source ∩
(chartAt H α).source` may be unbounded; e.g. the chart-α image of a generic
geodesic ball under a non-radial chart can be all of Euclidean space).
A uniform iterated-Fréchet bound on the full open set is therefore false in
general; the correct formulation restricts to a precompact set `K_E`
contained in the overlap.

Downstream tensor chart-Sobolev consumers only need bounds on the chart-α
image of a partition-of-unity support, which is compact and contained in
the chart overlap by `pouTsupport_inter_image_extChartAt_isCompact`. -/
set_option maxHeartbeats 800000 in
theorem tensorChartTransition_Ck_bound_on_compact
    (r s k : ℕ) (α β : M)
    {K_E : Set EuclN} (hK_compact : IsCompact K_E)
    (hK_sub : K_E ⊆ chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j ∈ Finset.range k,
      ∀ P₀ Q : TensorCompIdx (E := E) r s,
      ∀ y ∈ K_E,
        ‖iteratedFDeriv ℝ j
            (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q)
            y‖ ≤ C := by
  classical
  -- Local abbreviation for the open Euclidean overlap.
  set U : Set EuclN := chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β
    with hU_def
  have hU_open : IsOpen U :=
    isOpen_chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β
  have hU_uniqueDiff : UniqueDiffOn ℝ U := hU_open.uniqueDiffOn
  -- For each `(P₀, Q)`, `transitionCoeffOnEuclid r s α β P₀ Q` is `ContDiffOn ℝ ∞` on `U`.
  have h_pull_contDiffOn : ∀ P₀ Q : TensorCompIdx (E := E) r s,
      ContDiffOn ℝ ∞
        (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U :=
    fun P₀ Q => transitionCoeffOnEuclid_contDiffOn
      (E := E) (I := I) (M := M) r s α β P₀ Q
  -- On the open set `U`, `iteratedFDerivWithin ℝ j … U y = iteratedFDeriv ℝ j … y`.
  have h_iteratedFDerivWithin_eq : ∀ (j : ℕ) (P₀ Q : TensorCompIdx (E := E) r s)
      (y : EuclN), y ∈ U →
      iteratedFDerivWithin ℝ j
        (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y =
      iteratedFDeriv ℝ j
        (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) y :=
    fun j P₀ Q y hy => iteratedFDerivWithin_of_isOpen j hU_open hy
  -- Continuity of `iteratedFDerivWithin ℝ j … U` on `U` for each `j`.
  have h_iter_contOn : ∀ (j : ℕ) (P₀ Q : TensorCompIdx (E := E) r s),
      ContinuousOn (fun y => iteratedFDerivWithin ℝ j
        (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y) U :=
    fun j P₀ Q =>
      (h_pull_contDiffOn P₀ Q).continuousOn_iteratedFDerivWithin
        (by exact_mod_cast le_top) hU_uniqueDiff
  -- Per-`(j, P₀, Q)` bound on the compact set `K_E`.
  have h_per_triple : ∀ (j : ℕ) (P₀ Q : TensorCompIdx (E := E) r s),
      ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ y ∈ K_E,
        ‖iteratedFDeriv ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) y‖ ≤ Cj := by
    intro j P₀ Q
    by_cases hKne : K_E.Nonempty
    · -- Continuous norm of `iteratedFDerivWithin` on `K_E ⊆ U`.
      have h_iter_K : ContinuousOn (fun y => iteratedFDerivWithin ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y) K_E :=
        (h_iter_contOn j P₀ Q).mono hK_sub
      have h_cont_norm : ContinuousOn (fun y => ‖iteratedFDerivWithin ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y‖) K_E :=
        continuous_norm.comp_continuousOn h_iter_K
      obtain ⟨y₀, _hy₀_K, hy₀_max⟩ :=
        hK_compact.exists_isMaxOn hKne h_cont_norm
      refine ⟨‖iteratedFDerivWithin ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y₀‖,
        norm_nonneg _, ?_⟩
      intro y hy
      have hy_U : y ∈ U := hK_sub hy
      have h₁ : ‖iteratedFDerivWithin ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y‖ ≤
          ‖iteratedFDerivWithin ℝ j
            (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y₀‖ :=
        hy₀_max hy
      have h₂ : iteratedFDerivWithin ℝ j
          (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) U y =
          iteratedFDeriv ℝ j
            (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q) y :=
        h_iteratedFDerivWithin_eq j P₀ Q y hy_U
      rw [h₂] at h₁
      exact h₁
    · -- Empty `K_E`: trivial.
      refine ⟨0, le_refl _, ?_⟩
      intro y hy
      exact absurd ⟨y, hy⟩ hKne
  -- Aggregate over the finite set `Finset.range k × Finset.univ × Finset.univ`.
  -- Extract a per-triple witness via `Classical.choice`.
  choose Cj hCj_nn hCj_bd using h_per_triple
  -- Case split on whether the index domain is empty (`k = 0`).
  by_cases hk : k = 0
  · refine ⟨0, le_refl _, ?_⟩
    intro j hj _ _ _ _
    subst hk
    simp at hj
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    -- The non-empty finset of triples.
    let T : Finset (ℕ × TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s) :=
      (Finset.range k) ×ˢ ((Finset.univ : Finset (TensorCompIdx (E := E) r s)) ×ˢ
        (Finset.univ : Finset (TensorCompIdx (E := E) r s)))
    -- Show `T` is non-empty.
    -- Pick a witness: `j = 0` (since `0 < k`) and any `(P₀, Q)`.
    have hT_ne : T.Nonempty := by
      classical
      -- Pick `j = 0` and use any element of `TensorCompIdx r s`.
      let P₀_witness : TensorCompIdx (E := E) r s :=
        (fun _ : Fin r => ⟨0, (NeZero.pos _)⟩,
          fun _ : Fin s => ⟨0, (NeZero.pos _)⟩)
      refine ⟨(0, P₀_witness, P₀_witness), ?_⟩
      simp [T, Finset.mem_product, Finset.mem_range, hk_pos]
    -- Take the max of `Cj j P₀ Q` over `T`.
    let C : ℝ := T.sup' hT_ne (fun t => Cj t.1 t.2.1 t.2.2)
    have hC_ge : ∀ j P₀ Q, (j, P₀, Q) ∈ T → Cj j P₀ Q ≤ C := by
      intro j P₀ Q ht
      have := Finset.le_sup' (f := fun t : ℕ × TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s => Cj t.1 t.2.1 t.2.2) ht
      exact this
    -- Non-negativity from the chosen witness.
    obtain ⟨t₀, ht₀⟩ := hT_ne
    have hC_nn : 0 ≤ C :=
      le_trans (hCj_nn t₀.1 t₀.2.1 t₀.2.2) (hC_ge t₀.1 t₀.2.1 t₀.2.2 ht₀)
    refine ⟨C, hC_nn, ?_⟩
    intro j hj P₀ Q y hy
    have hmem : (j, P₀, Q) ∈ T := by
      refine Finset.mem_product.mpr ⟨hj, ?_⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    exact (hCj_bd j P₀ Q y hy).trans (hC_ge j P₀ Q hmem)

/-! ## Downstream-friendly variant

The headline theorem on a manifold-side compact `K_M` carried inside the chart
overlap. The proof passes through the chart-α Euclidean image of `K_M`. -/

set_option maxHeartbeats 800000 in
/-- **Tensor-component chart-transition `C^k` operator-norm bound, manifold form.**

For two chart base points `α, β : M` and a compact subset
`K_M ⊆ (chartAt H α).source ∩ (chartAt H β).source` of the chart overlap,
there is a non-negative constant
`C(g, r, s, k, α, β, K_M) ≥ 0` such that for every order
`j ∈ Finset.range k`, every component multi-index pair `(P₀, Q)`,
and every chart-α Euclidean image point of `K_M`, the iterated Fréchet
derivative operator norm of `transitionCoeffOnEuclid r s α β P₀ Q` is
bounded by `C`. -/
theorem tensorChartTransition_Ck_bound_on_compact_manifold
    (r s k : ℕ) (α β : M)
    {K_M : Set M} (hK_compact : IsCompact K_M)
    (hK_α : K_M ⊆ (chartAt H α).source)
    (hK_β : K_M ⊆ (chartAt H β).source) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j ∈ Finset.range k,
      ∀ P₀ Q : TensorCompIdx (E := E) r s,
      ∀ x ∈ K_M,
        ‖iteratedFDeriv ℝ j
            (transitionCoeffOnEuclid (E := E) (I := I) (M := M) r s α β P₀ Q)
            ((toEuclidean (E := E)) ((extChartAt I α) x))‖ ≤ C := by
  classical
  -- Push `K_M` through chart-α `extChartAt` and then `toEuclidean`.
  let f : M → EuclN := fun x => (toEuclidean (E := E)) ((extChartAt I α) x)
  -- Continuity of `f` on `(chartAt H α).source`.
  have h_ext_cont : ContinuousOn (extChartAt I α) (chartAt H α).source := by
    have h := continuousOn_extChartAt (I := I) α
    rw [extChartAt_source (I := I)] at h
    exact h
  have h_toE_cont : Continuous (toEuclidean (E := E)) :=
    (toEuclidean (E := E)).continuous
  have hf_cont : ContinuousOn f (chartAt H α).source :=
    h_toE_cont.continuousOn.comp h_ext_cont (fun _ hx => Set.mem_univ _)
  -- The image `K_E := f '' K_M` is compact.
  have h_KM_sub : K_M ⊆ (chartAt H α).source := hK_α
  have hK_E_compact : IsCompact (f '' K_M) :=
    hK_compact.image_of_continuousOn (hf_cont.mono h_KM_sub)
  -- Show `f '' K_M ⊆ chartTransitionEuclidOverlap α β`.
  have h_KE_sub : f '' K_M ⊆
      chartTransitionEuclidOverlap (E := E) (I := I) (M := M) α β := by
    rintro y ⟨x, hx, hfx⟩
    -- Reformat `y = f x = toEuclidean (extChartAt I α x)`.
    have hx_src : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hK_α hx
    have hx_tgt : (extChartAt I α) x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx_src
    -- First piece: `y ∈ chartTargetEuclid α`.
    have h_first : y ∈ chartTargetEuclid (I := I) (M := M) α := by
      refine ⟨(extChartAt I α) x, hx_tgt, ?_⟩
      change (toEuclidean (E := E)) ((extChartAt I α) x) = y
      exact hfx
    -- Second piece: chart-symm composition gives back `x ∈ (chartAt H β).source`.
    have h_toE_symm : (toEuclidean (E := E)).symm y = (extChartAt I α) x := by
      have : (toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) ((extChartAt I α) x)) = (extChartAt I α) x := by simp
      rw [← hfx]; exact this
    have h_chart_symm : (extChartAt I α).symm
        ((toEuclidean (E := E)).symm y) = x := by
      rw [h_toE_symm]
      exact (extChartAt I α).left_inv hx_src
    have h_second : (extChartAt I α).symm
        ((toEuclidean (E := E)).symm y) ∈ (chartAt H β).source := by
      rw [h_chart_symm]; exact hK_β hx
    exact ⟨h_first, h_second⟩
  -- Apply the Euclidean theorem.
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    tensorChartTransition_Ck_bound_on_compact (E := E) (I := I) (M := M)
      r s k α β hK_E_compact h_KE_sub
  refine ⟨C, hC_nn, ?_⟩
  intro j hj P₀ Q x hx
  -- `f x ∈ f '' K_M` provides the Euclidean-side membership.
  have hf_mem : f x ∈ f '' K_M := ⟨x, hx, rfl⟩
  exact hC_bd j hj P₀ Q (f x) hf_mem

end DifferentialGeometry.PDE.RicciFlow.HebeyBlock

/-! ## Axiom audit -/

#print axioms
  DifferentialGeometry.PDE.RicciFlow.HebeyBlock.tensorChartTransition_Ck_bound_on_compact

#print axioms
  DifferentialGeometry.PDE.RicciFlow.HebeyBlock.tensorChartTransition_Ck_bound_on_compact_manifold

