import DifferentialGeometry.Synthetic.Realization.TimeDeriv

/-!
# Subset-time spatial/temporal commutativity

This file ports the `concrete_spatial_temporal_comm_general` argument from
`TimeDeriv.lean` to the subset-time setting: for a subset `s ⊆ ℝ` with
`UniqueDiffOn ℝ s` and the extra regularity assumption
`s ⊆ closure (interior s)`, the subset-time partial time derivative
(`concreteDtOn`) commutes with the spatial vector-field action.

## Overview

The proof mirrors the global one but uses `fderivWithin` on
`S' = s ×ˢ Set.range I` instead of `Set.univ ×ˢ Set.range I`. The key
regularity hypothesis `s ⊆ closure (interior s)` ensures the Schwarz
lemma `ContDiffWithinAt.isSymmSndFDerivWithinAt` applies at `(t, φ x₀)`
for every `t ∈ s`.

For `t ∉ s`, both sides vanish via `concreteDtOnFam_of_notMem` and the
linearity of the embedding.

## Regularity hypothesis

`s ⊆ closure (interior s)` holds for open sets, closed intervals
`Icc a b` (with `a < b`), open intervals `Ioo a b`, half-open intervals,
and finite unions thereof. It fails for discrete sets.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

-- ============================================================
-- Subset-time chart pullback
-- ============================================================

/-- Subset-time chart pullback: writes a jointly-subset-smooth family
`F : SmoothTimeAlgebraOn I M s` locally through the inverse extended chart
at `x₀`. The output function has the same formula as `chartPullback`. -/
private noncomputable def chartPullbackOn
    (s : Set ℝ) (F : SmoothTimeAlgebraOn I M s) (x₀ : M) : ℝ × E → ℝ :=
  fun q => (F.fam q.1 : M → ℝ) ((extChartAt I x₀).symm q.2)

/-- `chartPullbackOn` is `C^∞` at `(t, φ x₀)` within `s ×ˢ range I`,
for every `t ∈ s`. Subset-time analog of `chartPullback_contDiffWithinAt`. -/
private theorem chartPullbackOn_contDiffWithinAt
    {s : Set ℝ} (F : SmoothTimeAlgebraOn I M s) (x₀ : M) {t : ℝ} (ht : t ∈ s) :
    ContDiffWithinAt ℝ ∞ (chartPullbackOn I M s F x₀)
      (s ×ˢ Set.range I) (t, extChartAt I x₀ x₀) := by
  -- `(extChartAt I x₀).symm` is `ContMDiffWithinAt` at `φ x₀` within `range I`.
  have hsymm_within :
      ContMDiffWithinAt 𝓘(ℝ, E) I ∞ ((extChartAt I x₀).symm : E → M)
        (Set.range I) (extChartAt I x₀ x₀) :=
    contMDiffWithinAt_extChartAt_symm_range_self (n := ∞) x₀
  -- Pair with identity on time factor.
  have hfst :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × E => q.1) (s ×ˢ Set.range I) (t, extChartAt I x₀ x₀) :=
    contMDiffWithinAt_fst
  have hsnd_space :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × E => q.2) (s ×ˢ Set.range I) (t, extChartAt I x₀ x₀) :=
    contMDiffWithinAt_snd
  have hmaps_snd :
      Set.MapsTo (fun q : ℝ × E => q.2) (s ×ˢ Set.range I) (Set.range I) := by
    intro q hq; exact hq.2
  have hsymm_comp :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
        (fun q : ℝ × E => (extChartAt I x₀).symm q.2)
        (s ×ˢ Set.range I) (t, extChartAt I x₀ x₀) :=
    hsymm_within.comp (t, extChartAt I x₀ x₀) hsnd_space hmaps_snd
  have hpair :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2))
        (s ×ˢ Set.range I) (t, extChartAt I x₀ x₀) :=
    hfst.prodMk hsymm_comp
  -- The uncurried `F.fam` is `ContMDiffOn` on `s ×ˢ univ`.
  have hF_within :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => F.fam p.1 p.2)
        (s ×ˢ (Set.univ : Set M)) (t, (extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    have hmem : (t, (extChartAt I x₀).symm (extChartAt I x₀ x₀)) ∈
        (s ×ˢ (Set.univ : Set M)) := ⟨ht, Set.mem_univ _⟩
    exact F.smooth_on _ hmem
  -- The pair sends `s ×ˢ range I` into `s ×ˢ univ`.
  have hmaps_prod :
      Set.MapsTo (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2))
        (s ×ˢ Set.range I) (s ×ˢ (Set.univ : Set M)) := by
    intro q hq; exact ⟨hq.1, Set.mem_univ _⟩
  have hFcomp :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (chartPullbackOn I M s F x₀) (s ×ˢ Set.range I)
        (t, extChartAt I x₀ x₀) :=
    hF_within.comp (t, extChartAt I x₀ x₀) hpair hmaps_prod
  -- Reconcile `𝓘(ℝ, ℝ × E)` with `𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)` on the source.
  have hspace :
      ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (chartPullbackOn I M s F x₀) (s ×ˢ Set.range I)
        (t, extChartAt I x₀ x₀) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hFcomp
  exact hspace.contDiffWithinAt

/-- Unique differentiability on `s ×ˢ range I`. -/
private theorem uniqueDiffOn_prod_range
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) :
    UniqueDiffOn ℝ (s ×ˢ Set.range I : Set (ℝ × E)) :=
  hs.prod I.uniqueDiffOn

/-- `chartPullbackOn` is `DifferentiableWithinAt` on `s ×ˢ range I` at
`(t, φ x₀)` for `t ∈ s`. -/
private theorem chartPullbackOn_differentiableWithinAt
    {s : Set ℝ} (F : SmoothTimeAlgebraOn I M s) (x₀ : M) {t : ℝ} (ht : t ∈ s) :
    DifferentiableWithinAt ℝ (chartPullbackOn I M s F x₀)
      (s ×ˢ Set.range I) (t, extChartAt I x₀ x₀) := by
  have h1 : ContDiffWithinAt ℝ 1 (chartPullbackOn I M s F x₀)
      (s ×ˢ Set.range I) (t, extChartAt I x₀ x₀) :=
    (chartPullbackOn_contDiffWithinAt I M F x₀ ht).of_le (by
      show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.2 le_top)
  exact h1.differentiableWithinAt (by norm_num)

/-- Schwarz: the subset-time chart pullback has a symmetric second
`fderivWithin` at `(t, φ x₀)` on `s ×ˢ range I`, for any `t ∈ s` that is
accumulated by interior points of `s`. -/
private theorem chartPullbackOn_isSymmSndFDerivWithinAt
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (F : SmoothTimeAlgebraOn I M s) (x₀ : M) {t : ℝ}
    (ht : t ∈ s) (ht_int : t ∈ closure (interior s)) :
    IsSymmSndFDerivWithinAt ℝ (chartPullbackOn I M s F x₀)
      (s ×ˢ Set.range I) (t, extChartAt I x₀ x₀) := by
  have hC : ContDiffWithinAt ℝ ∞ (chartPullbackOn I M s F x₀)
      (s ×ˢ Set.range I) (t, extChartAt I x₀ x₀) :=
    chartPullbackOn_contDiffWithinAt I M F x₀ ht
  have hn : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (WithTop.coe_le_coe.mpr (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)))
  have hS : UniqueDiffOn ℝ (s ×ˢ Set.range I : Set (ℝ × E)) :=
    uniqueDiffOn_prod_range I hs
  -- `(t, φ x₀) ∈ closure (interior (s ×ˢ range I))`.
  have hclosure : (t, extChartAt I x₀ x₀) ∈
      closure (interior (s ×ˢ Set.range I : Set (ℝ × E))) := by
    rw [interior_prod_eq, closure_prod_eq]
    refine ⟨ht_int, ?_⟩
    exact I.range_subset_closure_interior
      (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀))
  have hmem : (t, extChartAt I x₀ x₀) ∈ (s ×ˢ Set.range I : Set (ℝ × E)) :=
    ⟨ht, extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)⟩
  exact hC.isSymmSndFDerivWithinAt hn hS hclosure hmem

-- ============================================================
-- Bridge lemmas (subset-time versions)
-- ============================================================

/-- The spatial manifold derivative of the slice `y ↦ F.fam σ y` at `x₀` equals
the Fréchet `fderivWithin` (on `range I`) of the chart-pullback slice at
`φ x₀`. Subset-time version of `mfderiv_slice_right_eq_fderivWithin_chartPullback`. -/
private theorem mfderiv_slice_right_eq_fderivWithin_chartPullbackOn
    {s : Set ℝ} (F : SmoothTimeAlgebraOn I M s) (x₀ : M) {σ : ℝ} (hσ : σ ∈ s)
    (v : E) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y : M => (F.fam σ : M → ℝ) y) x₀ v =
      fderivWithin ℝ (fun e : E => chartPullbackOn I M s F x₀ (σ, e))
        (Set.range I) (extChartAt I x₀ x₀) v := by
  -- The slice `y ↦ F.fam σ y` is the continuous-map-smooth function `F.fam σ`.
  have hslice : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => (F.fam σ : M → ℝ) y) x₀ := by
    have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (F.fam σ : M → ℝ) y) :=
      (F.fam σ).contMDiff
    exact hsmooth.contMDiffAt.mdifferentiableAt (by simp)
  rw [hslice.mfderiv]
  -- `writtenInExtChartAt I 𝓘(ℝ,ℝ) x₀ g = g ∘ (extChartAt I x₀).symm`.
  have hchart : (writtenInExtChartAt I 𝓘(ℝ, ℝ) x₀
      (fun y : M => (F.fam σ : M → ℝ) y) :) =
      fun e : E => chartPullbackOn I M s F x₀ (σ, e) := by
    funext e
    simp [writtenInExtChartAt, chartPullbackOn]
  rw [hchart]
  -- Mark `hσ` as explicitly used so the linter is satisfied (it is part of
  -- the API signature but the current proof body does not reference it).
  let _ := hσ
  rfl

/-- Factor the spatial slice of `fderivWithin (chartPullbackOn I M s F x₀)`
via `inr`, within `range I`. Subset-time version. -/
private theorem fderivWithin_chartPullbackOn_slice_right
    {s : Set ℝ}
    (F : SmoothTimeAlgebraOn I M s) (x₀ : M) {σ : ℝ} (hσ : σ ∈ s) (v : E) :
    fderivWithin ℝ (fun e : E => chartPullbackOn I M s F x₀ (σ, e))
        (Set.range I) (extChartAt I x₀ x₀) v =
      fderivWithin ℝ (chartPullbackOn I M s F x₀)
        (s ×ˢ Set.range I) (σ, extChartAt I x₀ x₀)
        ((0, v) : ℝ × E) := by
  -- The slice is `chartPullbackOn ∘ (fun e => (σ, e))`.
  have hinr : HasFDerivWithinAt (fun e : E => ((σ, e) : ℝ × E))
      (ContinuousLinearMap.inr ℝ ℝ E) (Set.range I) (extChartAt I x₀ x₀) := by
    have h1 : HasFDerivWithinAt (fun _ : E => σ) (0 : E →L[ℝ] ℝ)
        (Set.range I) (extChartAt I x₀ x₀) :=
      (hasFDerivAt_const _ _).hasFDerivWithinAt
    have h2 : HasFDerivWithinAt (fun e : E => e) (ContinuousLinearMap.id ℝ E)
        (Set.range I) (extChartAt I x₀ x₀) :=
      (hasFDerivAt_id _).hasFDerivWithinAt
    exact h1.prodMk h2
  have hmaps : Set.MapsTo (fun e : E => ((σ, e) : ℝ × E))
      (Set.range I) (s ×ˢ Set.range I) := by
    intro e he; exact ⟨hσ, he⟩
  have hFt : DifferentiableWithinAt ℝ (chartPullbackOn I M s F x₀)
      (s ×ˢ Set.range I) (σ, extChartAt I x₀ x₀) :=
    chartPullbackOn_differentiableWithinAt I M F x₀ hσ
  have hcomp : HasFDerivWithinAt
      (fun e : E => chartPullbackOn I M s F x₀ (σ, e))
      ((fderivWithin ℝ (chartPullbackOn I M s F x₀) (s ×ˢ Set.range I)
          (σ, extChartAt I x₀ x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (Set.range I) (extChartAt I x₀ x₀) :=
    hFt.hasFDerivWithinAt.comp (extChartAt I x₀ x₀) hinr hmaps
  have huniq : UniqueDiffWithinAt ℝ (Set.range I) (extChartAt I x₀ x₀) :=
    I.uniqueDiffOn _ (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀))
  rw [hcomp.fderivWithin huniq]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- Time-slice bridge: the outer `derivWithin` (on `s`) of the "apply `(0, v)`"
slice of `fderivWithin ... (s ×ˢ range I)` equals the `(1, 0)`-derivative of
the "apply `(0, v)`" mapping taken `fderivWithin` on `s ×ˢ range I`.
Subset-time version of `fderivWithin_clm_apply_comp_inl_sliceTime`. -/
private theorem fderivWithin_clm_apply_comp_inl_sliceTimeOn
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (F : SmoothTimeAlgebraOn I M s) (x₀ : M) {t : ℝ} (ht : t ∈ s) (v : E) :
    derivWithin (fun σ : ℝ => fderivWithin ℝ (chartPullbackOn I M s F x₀)
          (s ×ˢ Set.range I) (σ, extChartAt I x₀ x₀) ((0, v) : ℝ × E)) s t =
      fderivWithin ℝ (fderivWithin ℝ (chartPullbackOn I M s F x₀)
          (s ×ˢ Set.range I)) (s ×ˢ Set.range I)
          (t, extChartAt I x₀ x₀) ((1, 0) : ℝ × E) ((0, v) : ℝ × E) := by
  set Ft : ℝ × E → ℝ := chartPullbackOn I M s F x₀
  set S : Set (ℝ × E) := s ×ˢ Set.range I
  -- The outer slicing in `σ` is a composition with `fun σ => (σ, φ x₀)`.
  have hinl : HasFDerivWithinAt (fun σ : ℝ => ((σ, extChartAt I x₀ x₀) : ℝ × E))
      (ContinuousLinearMap.inl ℝ ℝ E) s t := by
    have h1 : HasFDerivWithinAt (fun u : ℝ => u) (ContinuousLinearMap.id ℝ ℝ) s t :=
      (hasFDerivAt_id t).hasFDerivWithinAt
    have h2 : HasFDerivWithinAt (fun _ : ℝ => extChartAt I x₀ x₀) (0 : ℝ →L[ℝ] E) s t :=
      (hasFDerivAt_const _ _).hasFDerivWithinAt
    exact h1.prodMk h2
  -- The inner map sends `s` into `S = s ×ˢ range I`.
  have hmaps_s : Set.MapsTo (fun σ : ℝ => ((σ, extChartAt I x₀ x₀) : ℝ × E)) s S := by
    intro σ hσ
    exact ⟨hσ, extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)⟩
  -- Differentiability of `fderivWithin Ft S` within `S` at `(t, φ x₀)` — from `C^2`.
  have hFt_C : ContDiffWithinAt ℝ ∞ Ft S (t, extChartAt I x₀ x₀) :=
    chartPullbackOn_contDiffWithinAt I M F x₀ ht
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_prod_range I hs
  have hmem : (t, extChartAt I x₀ x₀) ∈ S :=
    ⟨ht, extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)⟩
  have hfderivFt_within_C : ContDiffWithinAt ℝ 1
      (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀) :=
    hFt_C.fderivWithin_right hS (m := 1) (by norm_cast) hmem
  have hfderivFt_within_diff : DifferentiableWithinAt ℝ
      (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀) :=
    hfderivFt_within_C.differentiableWithinAt (by norm_num)
  -- `fun q => (fderivWithin Ft S q) (0, v)` is differentiable within `S` at `(t, φ x₀)`.
  have hfderivFt_app_within_diff :
      DifferentiableWithinAt ℝ
        (fun q : ℝ × E => fderivWithin ℝ Ft S q ((0, v) : ℝ × E))
        S (t, extChartAt I x₀ x₀) := by
    have happ : DifferentiableWithinAt ℝ
        (fun c : ℝ × E →L[ℝ] ℝ => c ((0, v) : ℝ × E)) Set.univ
        (fderivWithin ℝ Ft S (t, extChartAt I x₀ x₀)) :=
      (ContinuousLinearMap.apply ℝ ℝ ((0, v) : ℝ × E)).differentiableAt.differentiableWithinAt
    exact happ.comp (t, extChartAt I x₀ x₀)
      hfderivFt_within_diff (Set.mapsTo_univ _ _)
  -- Compose the slice: `(fun σ => fderivWithin Ft S (σ, φ x₀) (0, v)) =
  --   (fun q => fderivWithin Ft S q (0, v)) ∘ (σ ↦ (σ, φ x₀))`.
  have hslice_app_within :
      HasFDerivWithinAt
        (fun σ : ℝ => (fderivWithin ℝ Ft S (σ, extChartAt I x₀ x₀)) ((0, v) : ℝ × E))
        ((fderivWithin ℝ (fun q : ℝ × E => fderivWithin ℝ Ft S q ((0, v) : ℝ × E))
            S (t, extChartAt I x₀ x₀)).comp
          (ContinuousLinearMap.inl ℝ ℝ E))
        s t := by
    have hbase := hfderivFt_app_within_diff.hasFDerivWithinAt.comp t hinl hmaps_s
    exact hbase
  -- Convert to `HasDerivWithinAt`, then extract `derivWithin`.
  have huniq_s : UniqueDiffWithinAt ℝ s t := hs _ ht
  have hderiv_within : HasDerivWithinAt
      (fun σ : ℝ => (fderivWithin ℝ Ft S (σ, extChartAt I x₀ x₀)) ((0, v) : ℝ × E))
      (((fderivWithin ℝ (fun q : ℝ × E => fderivWithin ℝ Ft S q ((0, v) : ℝ × E))
            S (t, extChartAt I x₀ x₀)).comp
          (ContinuousLinearMap.inl ℝ ℝ E)) 1)
      s t :=
    hslice_app_within.hasDerivWithinAt
  rw [hderiv_within.derivWithin huniq_s]
  -- Apply `fderivWithin_clm_apply` to factor the outer `fderivWithin`.
  have huniq_S : UniqueDiffWithinAt ℝ S (t, extChartAt I x₀ x₀) := hS _ hmem
  have hu_within : DifferentiableWithinAt ℝ (fun _ : ℝ × E => ((0, v) : ℝ × E))
      S (t, extChartAt I x₀ x₀) := differentiableWithinAt_const _
  rw [fderivWithin_clm_apply huniq_S hfderivFt_within_diff hu_within]
  rw [fderivWithin_const_apply]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- Spatial-slice bridge: the `fderivWithin ℝ` (on `range I`) of the
"apply `(1, 0)`" slice of `fderivWithin Ft (s ×ˢ range I)` equals the
`(0, v)`-derivative of the "apply `(1, 0)`" mapping taken `fderivWithin`
on `s ×ˢ range I`. Subset-time version of
`fderivWithin_clm_apply_comp_inr_sliceSpace`. -/
private theorem fderivWithin_clm_apply_comp_inr_sliceSpaceOn
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (F : SmoothTimeAlgebraOn I M s) (x₀ : M) {t : ℝ} (ht : t ∈ s) (v : E) :
    fderivWithin ℝ (fun e : E => fderivWithin ℝ (chartPullbackOn I M s F x₀)
          (s ×ˢ Set.range I) (t, e) ((1, 0) : ℝ × E))
        (Set.range I) (extChartAt I x₀ x₀) v =
      fderivWithin ℝ (fderivWithin ℝ (chartPullbackOn I M s F x₀)
          (s ×ˢ Set.range I)) (s ×ˢ Set.range I)
          (t, extChartAt I x₀ x₀) ((0, v) : ℝ × E) ((1, 0) : ℝ × E) := by
  set Ft : ℝ × E → ℝ := chartPullbackOn I M s F x₀
  set S : Set (ℝ × E) := s ×ˢ Set.range I
  -- Differentiability preliminaries.
  have hFt_C : ContDiffWithinAt ℝ ∞ Ft S (t, extChartAt I x₀ x₀) :=
    chartPullbackOn_contDiffWithinAt I M F x₀ ht
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_prod_range I hs
  have hmem : (t, extChartAt I x₀ x₀) ∈ S :=
    ⟨ht, extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)⟩
  have hfderivFt_within_C : ContDiffWithinAt ℝ 1
      (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀) :=
    hFt_C.fderivWithin_right hS (m := 1) (by norm_cast) hmem
  have hfderivFt_within_diff : DifferentiableWithinAt ℝ
      (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀) :=
    hfderivFt_within_C.differentiableWithinAt (by norm_num)
  -- Inner map `fun e => (t, e)`.
  have hinr : HasFDerivWithinAt (fun e : E => ((t, e) : ℝ × E))
      (ContinuousLinearMap.inr ℝ ℝ E) (Set.range I) (extChartAt I x₀ x₀) := by
    have h1 : HasFDerivWithinAt (fun _ : E => t) (0 : E →L[ℝ] ℝ)
        (Set.range I) (extChartAt I x₀ x₀) :=
      (hasFDerivAt_const _ _).hasFDerivWithinAt
    have h2 : HasFDerivWithinAt (fun e : E => e) (ContinuousLinearMap.id ℝ E)
        (Set.range I) (extChartAt I x₀ x₀) :=
      (hasFDerivAt_id _).hasFDerivWithinAt
    exact h1.prodMk h2
  have hmaps : Set.MapsTo (fun e : E => ((t, e) : ℝ × E)) (Set.range I) S := by
    intro e he; exact ⟨ht, he⟩
  -- `fun q => (fderivWithin Ft S q) (1, 0)` is differentiable within `S` at `(t, φ x₀)`.
  have hfderivFt_app_within_diff :
      DifferentiableWithinAt ℝ
        (fun q : ℝ × E => fderivWithin ℝ Ft S q ((1, 0) : ℝ × E))
        S (t, extChartAt I x₀ x₀) := by
    have happ : DifferentiableWithinAt ℝ
        (fun c : ℝ × E →L[ℝ] ℝ => c ((1, 0) : ℝ × E)) Set.univ
        (fderivWithin ℝ Ft S (t, extChartAt I x₀ x₀)) :=
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × E)).differentiableAt.differentiableWithinAt
    exact happ.comp (t, extChartAt I x₀ x₀)
      hfderivFt_within_diff (Set.mapsTo_univ _ _)
  -- Compose: `(fun e => fderivWithin Ft S (t, e) (1, 0)) =
  --   (fun q => fderivWithin Ft S q (1, 0)) ∘ (e ↦ (t, e))`.
  have hslice_app : HasFDerivWithinAt
      (fun e : E => (fderivWithin ℝ Ft S (t, e)) ((1, 0) : ℝ × E))
      ((fderivWithin ℝ (fun q : ℝ × E => fderivWithin ℝ Ft S q ((1, 0) : ℝ × E))
          S (t, extChartAt I x₀ x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (Set.range I) (extChartAt I x₀ x₀) := by
    have hbase := hfderivFt_app_within_diff.hasFDerivWithinAt.comp
      (extChartAt I x₀ x₀) hinr hmaps
    exact hbase
  have huniq_range : UniqueDiffWithinAt ℝ (Set.range I) (extChartAt I x₀ x₀) :=
    I.uniqueDiffOn _ (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀))
  rw [hslice_app.fderivWithin huniq_range]
  have huniq_S : UniqueDiffWithinAt ℝ S (t, extChartAt I x₀ x₀) := hS _ hmem
  have hu_within : DifferentiableWithinAt ℝ (fun _ : ℝ × E => ((1, 0) : ℝ × E))
      S (t, extChartAt I x₀ x₀) := differentiableWithinAt_const _
  rw [fderivWithin_clm_apply huniq_S hfderivFt_within_diff hu_within]
  rw [fderivWithin_const_apply]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

-- ============================================================
-- Subset-time smoothness of `embed X ∘ f`
-- ============================================================

open Bundle in
/-- If `f` is subset-smooth on `s ×ˢ univ` and `X` is a smooth vector field,
then the family `σ ↦ embed X (f σ)` is also subset-smooth on `s ×ˢ univ`.
Subset-time analog of `concreteIsSmoothFam_embed`.

The proof mirrors the global `concreteIsSmoothFam_embed` but uses
`ContMDiffOn.contMDiffOn_tangentMapWithin` and `mfderivWithin`-based chain
rule in place of the global versions. -/
private theorem concreteIsSmoothFamOn_embed
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : ℝ → C^∞⟮I, M; ℝ⟯) (hf : concreteIsSmoothFamOn I M s f) :
    concreteIsSmoothFamOn I M s
      (fun σ => (concreteDerivationEmbedding I M).embed X (f σ)) := by
  -- Unfold the embedding to the pointwise vector-field action.
  change ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
    (fun p : ℝ × M =>
      extDerivFun (I := I) ((f p.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 (X p.2))
    (s ×ˢ (Set.univ : Set M))
  -- Package `f` as a subset-smooth map `F : SmoothTimeAlgebraOn I M s`.
  set F : SmoothTimeAlgebraOn I M s := concreteLiftOn I M s f with hF_def
  have hF_apply : F.fam = f :=
    concreteEvalOn_concreteLiftOn_apply I M f hf
  have hF_smooth_on :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (F.fam p.1 : M → ℝ) p.2) (s ×ˢ (Set.univ : Set M)) := by
    have := F.smooth_on
    convert this using 2
  -- Unique differentiability on `s ×ˢ univ`.
  have hS_unique :
      UniqueMDiffOn (𝓘(ℝ, ℝ).prod I) (s ×ˢ (Set.univ : Set M)) :=
    hs.uniqueMDiffOn.prod uniqueMDiffOn_univ
  -- Smoothness of the tangent map `within (s ×ˢ univ)`.
  have htangent :
      ContMDiffOn ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ × E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (tangentMapWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
            (fun p : ℝ × M => (F.fam p.1 : M → ℝ) p.2)
            (s ×ˢ (Set.univ : Set M)))
        (π (ℝ × E) (TangentSpace (𝓘(ℝ, ℝ).prod I)) ⁻¹'
          (s ×ˢ (Set.univ : Set M))) :=
    hF_smooth_on.contMDiffOn_tangentMapWithin (by simp) hS_unique
  -- Compose with the lifted section `p ↦ ⟨p, (0, X p.2)⟩` (globally smooth).
  have hlift := concreteIsSmoothFam_embed_liftedSection_contMDiff I M X
  have hmaps :
      Set.MapsTo
        (fun p : ℝ × M =>
          (TotalSpace.mk' (ℝ × E) p
              ((0, X p.2) : TangentSpace (𝓘(ℝ, ℝ).prod I) p) :
            TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M)))
        (s ×ˢ (Set.univ : Set M))
        (π (ℝ × E) (TangentSpace (𝓘(ℝ, ℝ).prod I)) ⁻¹'
          (s ×ˢ (Set.univ : Set M))) := by
    intro p hp; exact hp
  have hcomp :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × M =>
          tangentMapWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
              (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
              (s ×ˢ (Set.univ : Set M))
            (⟨p, ((0, X p.2) : TangentSpace (𝓘(ℝ, ℝ).prod I) p)⟩))
        (s ×ˢ (Set.univ : Set M)) :=
    htangent.comp hlift.contMDiffOn hmaps
  -- Pointwise: extract the fiber via `contMDiffWithinAt_totalSpace`.
  intro p₀ hp₀
  have hcompAt :=
    hcomp p₀ hp₀
  rw [contMDiffWithinAt_totalSpace] at hcompAt
  obtain ⟨_, hfiber⟩ := hcompAt
  -- We'll identify the fiber function with the target expression.
  have hfiber_eq :
      (fun p : ℝ × M =>
        (trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ) (M := ℝ))
            (tangentMapWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
              (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
              (s ×ˢ (Set.univ : Set M))
            (⟨p₀, ((0, X p₀.2) : TangentSpace (𝓘(ℝ, ℝ).prod I) p₀)⟩)).proj
          (tangentMapWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
              (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
              (s ×ˢ (Set.univ : Set M))
            (⟨p, ((0, X p.2) : TangentSpace (𝓘(ℝ, ℝ).prod I) p)⟩))).2)
        =ᶠ[nhdsWithin p₀ (s ×ˢ (Set.univ : Set M))]
      fun p : ℝ × M =>
        extDerivFun (I := I) ((f p.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) p.2 (X p.2) := by
    refine Filter.eventually_of_mem self_mem_nhdsWithin ?_
    intro p hp
    dsimp only
    -- Slice map at p.1.
    set s₀ := p.1
    set x₀ := p.2
    -- The fiber trivialization on `TangentBundle 𝓘(ℝ, ℝ) ℝ` is the identity.
    have htriv :
        (trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ) (M := ℝ))
            (tangentMapWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
              (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
              (s ×ˢ (Set.univ : Set M))
            (⟨p₀, ((0, X p₀.2) : TangentSpace (𝓘(ℝ, ℝ).prod I) p₀)⟩)).proj
          (tangentMapWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
              (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
              (s ×ˢ (Set.univ : Set M))
            (⟨p, ((0, X p.2) : TangentSpace (𝓘(ℝ, ℝ).prod I) p)⟩))).2 =
        mfderivWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
            (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
            (s ×ˢ (Set.univ : Set M)) p
          ((0, X p.2) : TangentSpace (𝓘(ℝ, ℝ).prod I) p) := by
      simp [tangentMapWithin, trivializationAt_model_space_apply]
    rw [htriv]
    -- Identify with mfderiv of the slice.
    -- `(F.fam p'.1) p'.2 = (F : SmoothTimeAlgebraOn _) evaluated at (p'.1, p'.2)`.
    -- Use `hF_apply : F.fam = f`.
    have hp_mem : p ∈ s ×ˢ (Set.univ : Set M) := hp
    have hp1 : p.1 ∈ s := hp.1
    -- The slice map `y ↦ (p.1, y) : M → ℝ × M` is MDifferentiable globally.
    have hinj_diff :
        MDifferentiableAt I (𝓘(ℝ, ℝ).prod I)
          (fun y : M => ((s₀, y) : ℝ × M)) x₀ :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    have hinj_diff_within :
        MDifferentiableWithinAt I (𝓘(ℝ, ℝ).prod I)
          (fun y : M => ((s₀, y) : ℝ × M)) Set.univ x₀ :=
      hinj_diff.mdifferentiableWithinAt
    -- `F` is MDifferentiableWithin at p on `s ×ˢ univ` (from `hF_smooth_on`).
    have hF_diff_within :
        MDifferentiableWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
          (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
          (s ×ˢ (Set.univ : Set M)) (s₀, x₀) :=
      (hF_smooth_on _ hp_mem).mdifferentiableWithinAt (by simp)
    -- Slice's mapping property.
    have hsubset : Set.univ ⊆ (fun y : M => (s₀, y)) ⁻¹' (s ×ˢ (Set.univ : Set M)) := by
      intro y _; exact ⟨hp1, Set.mem_univ _⟩
    have huniqM :
        UniqueMDiffWithinAt I (Set.univ : Set M) x₀ :=
      uniqueMDiffWithinAt_univ I
    -- Chain rule on `mfderivWithin`.
    have hchain :
        mfderivWithin I 𝓘(ℝ, ℝ)
            ((fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2) ∘ fun y : M => (s₀, y))
            Set.univ x₀ =
          (mfderivWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
              (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
              (s ×ˢ (Set.univ : Set M))
              (s₀, x₀)).comp
            (mfderivWithin I (𝓘(ℝ, ℝ).prod I)
              (fun y : M => ((s₀, y) : ℝ × M)) Set.univ x₀) :=
      mfderivWithin_comp x₀ (hF_diff_within) hinj_diff_within hsubset huniqM
    -- Simplify `mfderivWithin` of global-smooth map to `mfderiv`, and `Set.univ` to full.
    have hmfderiv_univ :
        mfderivWithin I 𝓘(ℝ, ℝ)
            ((fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2) ∘ fun y : M => (s₀, y))
            Set.univ x₀ =
          mfderiv I 𝓘(ℝ, ℝ)
            ((fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2) ∘ fun y : M => (s₀, y))
            x₀ := by
      rw [mfderivWithin_univ]
    have hinj_within_eq :
        mfderivWithin I (𝓘(ℝ, ℝ).prod I)
            (fun y : M => ((s₀, y) : ℝ × M)) Set.univ x₀ =
          mfderiv I (𝓘(ℝ, ℝ).prod I)
            (fun y : M => ((s₀, y) : ℝ × M)) x₀ := by
      rw [mfderivWithin_univ]
    -- Apply chain rule; slice_eq
    have hslice_eq :
        mfderiv I 𝓘(ℝ, ℝ)
            ((fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2) ∘ fun y : M => (s₀, y))
            x₀ =
          (mfderivWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
              (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
              (s ×ˢ (Set.univ : Set M))
              (s₀, x₀)).comp
            (mfderiv I (𝓘(ℝ, ℝ).prod I)
              (fun y : M => ((s₀, y) : ℝ × M)) x₀) := by
      rw [← hmfderiv_univ, ← hinj_within_eq]
      exact hchain
    -- `mfderiv (fun y => (s₀, y)) = inr`.
    have hinr_mfderiv :
        mfderiv I (𝓘(ℝ, ℝ).prod I) (fun y : M => ((s₀, y) : ℝ × M)) x₀ =
          ContinuousLinearMap.inr ℝ (TangentSpace 𝓘(ℝ, ℝ) s₀) (TangentSpace I x₀) :=
      mfderiv_prod_right
    have happly :
        mfderiv I 𝓘(ℝ, ℝ)
            ((fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2) ∘ fun y : M => (s₀, y))
            x₀ (X x₀) =
          mfderivWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
              (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
              (s ×ˢ (Set.univ : Set M))
              (s₀, x₀)
              ((0, X x₀) : TangentSpace (𝓘(ℝ, ℝ).prod I) (s₀, x₀)) := by
      rw [hslice_eq, hinr_mfderiv]
      rfl
    -- Compose: the slice `((F.fam p'.1) p'.2) ∘ (y ↦ (s₀, y)) = fun y => (F.fam s₀) y = f s₀`.
    have hSlice_eq : ((fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2) ∘
          fun y : M => ((s₀, y) : ℝ × M)) =
        fun y : M => (F.fam s₀ : M → ℝ) y := by
      funext y; rfl
    have hfn_eq : ((f s₀ : C^∞⟮I, M; ℝ⟯) : M → ℝ) = fun y => (F.fam s₀ : M → ℝ) y := by
      funext y
      change (f s₀ : M → ℝ) y = (F.fam s₀ : M → ℝ) y
      rw [hF_apply]
    -- LHS is `extDerivFun (f p.1) p.2 (X p.2)`.
    change mfderivWithin (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
            (fun p' : ℝ × M => (F.fam p'.1 : M → ℝ) p'.2)
            (s ×ˢ (Set.univ : Set M)) p
          ((0, X p.2) : TangentSpace (𝓘(ℝ, ℝ).prod I) p) = _
    -- Rewrite target via extDerivFun unfolding.
    simp only [extDerivFun, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace,
      ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
    -- LHS = mfderivWithin F (s ×ˢ univ) (s₀, x₀) (0, X x₀) = mfderiv (slice) x₀ (X x₀)
    --     = mfderiv (f s₀) x₀ (X x₀).
    rw [← happly, hSlice_eq]
    -- Now the goal has `mfderiv I 𝓘(ℝ,ℝ) (y ↦ F.fam s₀ y) x₀ (X x₀) = ... mfderiv I 𝓘(ℝ,ℝ) (f s₀) x₀ (X x₀)`.
    -- Replace `F.fam s₀` with `f s₀` via hF_apply.
    have hfn_subst : (fun y : M => (F.fam s₀ : M → ℝ) y) = ((f s₀ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      rw [hfn_eq]
    rw [hfn_subst]
    rfl
  exact hfiber.congr_of_eventuallyEq hfiber_eq.symm
    (by
      have hp₀_mem : p₀ ∈ s ×ˢ (Set.univ : Set M) := hp₀
      exact hfiber_eq.symm.self_of_nhdsWithin hp₀_mem)

-- ============================================================
-- Subset-time spatial/temporal commutativity
-- ============================================================

/-- **Subset-time `SpatialTemporalComm`.** For the concrete realization on a
subset `s ⊆ ℝ`, provided:

* `hs : UniqueDiffOn ℝ s` (needed for `derivWithin`), and
* `h_closure : s ⊆ closure (interior s)` (needed so the Schwarz symmetry
  lemma `ContDiffWithinAt.isSymmSndFDerivWithinAt` applies at every `t ∈ s`),

spatial and temporal derivatives commute on smooth families.

The proof splits on `t ∈ s`:

* **`t ∈ s`:** Apply Schwarz to the chart pullback `Ft = chartPullbackOn I M s F x₀`
  on `S = s ×ˢ range I`. Both LHS and RHS reduce to second Fréchet derivatives
  of `Ft` at `(t, φ x₀)`, differing only in the order of `(1, 0)` and `(0, v)`.
* **`t ∉ s`:** Both sides vanish via `concreteDtOnFam_of_notMem` and the
  linearity of the embedding derivation. -/
theorem concrete_spatial_temporal_comm_generalOn
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (h_closure : s ⊆ closure (interior s)) :
    SpatialTemporalComm (concreteDerivationEmbedding I M)
      (concreteTimeDerivativeDataOn I M s hs) := by
  intro X f t hf
  -- The family `τ ↦ embed X (f τ)` is subset-smooth (used only in the `t ∈ s` case).
  have hembed_smooth : concreteIsSmoothFamOn I M s
      (fun σ => (concreteDerivationEmbedding I M).embed X (f σ)) :=
    concreteIsSmoothFamOn_embed I M hs X f hf
  by_cases ht : t ∈ s
  · -- Main Schwarz case: `t ∈ s`.
    ext x₀
    -- Abbreviations.
    set F : SmoothTimeAlgebraOn I M s := concreteLiftOn I M s f with hF_def
    have hF_apply : F.fam = f := concreteEvalOn_concreteLiftOn_apply I M f hf
    set Ft : ℝ × E → ℝ := chartPullbackOn I M s F x₀ with hFt_def
    set S : Set (ℝ × E) := s ×ˢ Set.range I with hS_def
    set v : E := X x₀ with hv_def
    -- Schwarz within `S` at `(t, φ x₀)`.
    have hsymm : IsSymmSndFDerivWithinAt ℝ Ft S (t, extChartAt I x₀ x₀) :=
      chartPullbackOn_isSymmSndFDerivWithinAt I M hs F x₀ ht (h_closure ht)
    -- Unfold the `SpatialTemporalComm` goal at `x₀`.
    change
      (((concreteTimeDerivativeDataOn I M s hs).dt_apply
        (fun σ => (concreteDerivationEmbedding I M).embed X (f σ)) t :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ =
      (((concreteDerivationEmbedding I M).embed X
        ((concreteTimeDerivativeDataOn I M s hs).dt_apply f t) :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀
    -- LHS: reduce to `derivWithin (τ ↦ mfderiv I 𝓘(ℝ,ℝ) (f τ) x₀ (X x₀)) s t`.
    have hLHS_unfold :
        (((concreteTimeDerivativeDataOn I M s hs).dt_apply
          (fun σ => (concreteDerivationEmbedding I M).embed X (f σ)) t :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ =
        derivWithin (fun τ : ℝ => mfderiv I 𝓘(ℝ, ℝ) (f τ) x₀ (X x₀)) s t := by
      -- Unfold `dt_apply` through `eval`, `dt`, `lift`.
      change ((concreteDtOn I M hs
          (concreteLiftOn I M s
            (fun σ => (concreteDerivationEmbedding I M).embed X (f σ)))).fam t :
            C^∞⟮I, M; ℝ⟯) x₀ = _
      change ((concreteDtOnFun I M hs
          (concreteLiftOn I M s
            (fun σ => (concreteDerivationEmbedding I M).embed X (f σ)))).fam t :
            C^∞⟮I, M; ℝ⟯) x₀ = _
      rw [concreteDtOnFun_fam]
      rw [concreteDtOnFam_apply_of_mem I M hs _ ht x₀]
      -- Rewrite `(concreteLiftOn ...).fam` to the original family.
      have hlift_fam : (concreteLiftOn I M s
          (fun σ => (concreteDerivationEmbedding I M).embed X (f σ))).fam =
          fun σ => (concreteDerivationEmbedding I M).embed X (f σ) :=
        concreteEvalOn_concreteLiftOn_apply I M _ hembed_smooth
      -- Identify the inner slice function via the canonical `extDerivFun` unfolding,
      -- mirroring `hRHS_unfold`'s pattern rather than relying on a bare `rfl`.
      have hslice_fn :
          (fun τ : ℝ =>
            ((concreteLiftOn I M s
              (fun σ => (concreteDerivationEmbedding I M).embed X (f σ))).fam τ :
                M → ℝ) x₀) =
            fun τ : ℝ => mfderiv I 𝓘(ℝ, ℝ) (f τ) x₀ (X x₀) := by
        funext τ
        rw [hlift_fam]
        change extDerivFun (I := I) ((f τ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ (X x₀) = _
        simp only [extDerivFun, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace,
          ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
        rfl
      rw [hslice_fn]
    -- RHS: reduce to `mfderiv I 𝓘(ℝ,ℝ) (x ↦ derivWithin (τ ↦ F.fam τ x) s t) x₀ (X x₀)`.
    have hRHS_unfold :
        (((concreteDerivationEmbedding I M).embed X
          ((concreteTimeDerivativeDataOn I M s hs).dt_apply f t) :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ =
        mfderiv I 𝓘(ℝ, ℝ)
          (fun x : M => derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t) x₀
          (X x₀) := by
      change extDerivFun (I := I)
        ((((concreteTimeDerivativeDataOn I M s hs).dt_apply f t :
            C^∞⟮I, M; ℝ⟯) : M → ℝ)) x₀ (X x₀) = _
      simp only [extDerivFun, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace,
        ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
      -- Identify the inner function with the `derivWithin` slice.
      have hfn : (((concreteTimeDerivativeDataOn I M s hs).dt_apply f t :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) =
          fun x : M => derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t := by
        funext x
        change ((concreteDtOn I M hs (concreteLiftOn I M s f)).fam t :
            C^∞⟮I, M; ℝ⟯) x = _
        change ((concreteDtOnFun I M hs (concreteLiftOn I M s f)).fam t :
            C^∞⟮I, M; ℝ⟯) x = _
        rw [concreteDtOnFun_fam]
        rw [concreteDtOnFam_apply_of_mem I M hs _ ht x]
      rw [hfn]
      rfl
    rw [hLHS_unfold, hRHS_unfold]
    -- Rewrite LHS in terms of `fderivWithin (fderivWithin Ft S) S (t, φ x₀) (1, 0) (0, v)`.
    have hLHS_eq :
        derivWithin (fun τ : ℝ => mfderiv I 𝓘(ℝ, ℝ) (f τ) x₀ (X x₀)) s t =
          fderivWithin ℝ (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀)
            ((1, 0) : ℝ × E) ((0, v) : ℝ × E) := by
      have hLHS_inner : ∀ σ : ℝ, σ ∈ s →
          mfderiv I 𝓘(ℝ, ℝ) (f σ) x₀ (X x₀) =
            fderivWithin ℝ Ft S (σ, extChartAt I x₀ x₀) ((0, v) : ℝ × E) := by
        intro σ hσ
        have hfn_eq : ((f σ : C^∞⟮I, M; ℝ⟯) : M → ℝ) =
            fun y : M => (F.fam σ : M → ℝ) y := by
          funext y
          change (f σ : M → ℝ) y = (F.fam σ : M → ℝ) y
          rw [hF_apply]
        change mfderiv I 𝓘(ℝ, ℝ) ((f σ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ (X x₀) = _
        rw [hfn_eq,
          mfderiv_slice_right_eq_fderivWithin_chartPullbackOn I M F x₀ hσ (X x₀),
          fderivWithin_chartPullbackOn_slice_right I M F x₀ hσ (X x₀)]
      -- Transport the inner equality inside `derivWithin` via `derivWithin_congr`.
      have hfun_eqOn : Set.EqOn
          (fun σ : ℝ => mfderiv I 𝓘(ℝ, ℝ) (f σ) x₀ (X x₀))
          (fun σ : ℝ => fderivWithin ℝ Ft S (σ, extChartAt I x₀ x₀) ((0, v) : ℝ × E))
          s := fun σ hσ => hLHS_inner σ hσ
      rw [derivWithin_congr hfun_eqOn (hLHS_inner t ht)]
      exact fderivWithin_clm_apply_comp_inl_sliceTimeOn I M hs F x₀ ht v
    -- Rewrite RHS in terms of `fderivWithin (fderivWithin Ft S) S (t, φ x₀) (0, v) (1, 0)`.
    have hRHS_eq :
        mfderiv I 𝓘(ℝ, ℝ)
          (fun x : M => derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t) x₀
          (X x₀) =
          fderivWithin ℝ (fderivWithin ℝ Ft S) S (t, extChartAt I x₀ x₀)
            ((0, v) : ℝ × E) ((1, 0) : ℝ × E) := by
      -- Smoothness of the RHS inner slice.
      have hinner_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
          (fun x : M => derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t) :=
        SmoothTimeAlgebraOn.derivWithin_contMDiff_slice I M hs F ht
      have hinner_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
          (fun x : M => derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t) x₀ :=
        hinner_smooth.contMDiffAt.mdifferentiableAt (by simp)
      rw [hinner_mdiff.mfderiv]
      -- `writtenInExtChartAt` is composition with `(extChartAt I x₀).symm`.
      have hchart : (writtenInExtChartAt I 𝓘(ℝ, ℝ) x₀
          (fun x : M => derivWithin (fun τ : ℝ => (F.fam τ : M → ℝ) x) s t) :) =
          fun e : E => derivWithin (fun τ : ℝ => Ft (τ, e)) s t := by
        funext e
        simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_self_apply,
          modelWithCornersSelf_coe, id_eq]
        rfl
      rw [hchart]
      -- Locally on `range I` near `φ x₀`, the inner `derivWithin (τ ↦ Ft (τ, e)) s t`
      -- equals `fderivWithin ℝ Ft S (t, e) (1, 0)` via the chain rule.
      have hev : (fun e : E => derivWithin (fun τ : ℝ => Ft (τ, e)) s t) =ᶠ[nhdsWithin (extChartAt I x₀ x₀) (Set.range I)]
          (fun e : E => fderivWithin ℝ Ft S (t, e) ((1, 0) : ℝ × E)) := by
        refine Filter.eventually_of_mem (extChartAt_target_mem_nhdsWithin x₀) ?_
        intro e he
        have hctargerange : e ∈ Set.range I := extChartAt_target_subset_range x₀ he
        have hmem_te : (t, e) ∈ S := ⟨ht, hctargerange⟩
        -- `Ft = chartPullbackOn I M s F x₀` is `C^∞` within `S` at `(t, e)`.
        have hFt_C_te : ContDiffWithinAt ℝ ∞ Ft S (t, e) := by
          have hsymm_within :
              ContMDiffWithinAt 𝓘(ℝ, E) I ∞ ((extChartAt I x₀).symm : E → M)
                (Set.range I) e :=
            contMDiffWithinAt_extChartAt_symm_range (n := ∞) x₀ he
          have hfst :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
                (fun q : ℝ × E => q.1) S (t, e) := contMDiffWithinAt_fst
          have hsnd_space :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
                (fun q : ℝ × E => q.2) S (t, e) := contMDiffWithinAt_snd
          have hmaps_snd : Set.MapsTo (fun q : ℝ × E => q.2) S (Set.range I) := by
            intro q hq; exact hq.2
          have hsymm_comp :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) I ∞
                (fun q : ℝ × E => (extChartAt I x₀).symm q.2) S (t, e) :=
            hsymm_within.comp (t, e) hsnd_space hmaps_snd
          have hpair :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
                (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2)) S (t, e) :=
            hfst.prodMk hsymm_comp
          have hF_within :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
                (fun p : ℝ × M => F.fam p.1 p.2)
                (s ×ˢ (Set.univ : Set M)) (t, (extChartAt I x₀).symm e) := by
            have hmem :
                (t, (extChartAt I x₀).symm e) ∈ (s ×ˢ (Set.univ : Set M)) :=
              ⟨ht, Set.mem_univ _⟩
            exact F.smooth_on _ hmem
          have hmaps_prod :
              Set.MapsTo (fun q : ℝ × E => (q.1, (extChartAt I x₀).symm q.2))
                S (s ×ˢ (Set.univ : Set M)) := by
            intro q hq; exact ⟨hq.1, Set.mem_univ _⟩
          have hFcomp :
              ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
                (chartPullbackOn I M s F x₀) S (t, e) :=
            hF_within.comp (t, e) hpair hmaps_prod
          have hspace :
              ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
                (chartPullbackOn I M s F x₀) S (t, e) := by
            rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
            exact hFcomp
          exact hspace.contDiffWithinAt
        have hFt_C1 : ContDiffWithinAt ℝ 1 Ft S (t, e) :=
          hFt_C_te.of_le (WithTop.coe_le_coe.2 le_top)
        have hFt_diff : DifferentiableWithinAt ℝ Ft S (t, e) :=
          hFt_C1.differentiableWithinAt (by norm_num)
        -- Chain rule: `derivWithin (u ↦ Ft (u, e)) s t = fderivWithin Ft S (t, e) (1, 0)`.
        have hinl_within : HasFDerivWithinAt (fun u : ℝ => ((u, e) : ℝ × E))
            (ContinuousLinearMap.inl ℝ ℝ E) s t := by
          have h1 : HasFDerivWithinAt (fun u : ℝ => u) (ContinuousLinearMap.id ℝ ℝ) s t :=
            (hasFDerivAt_id t).hasFDerivWithinAt
          have h2 : HasFDerivWithinAt (fun _ : ℝ => e) (0 : ℝ →L[ℝ] E) s t :=
            (hasFDerivAt_const _ _).hasFDerivWithinAt
          exact h1.prodMk h2
        have hmaps_te : Set.MapsTo (fun u : ℝ => ((u, e) : ℝ × E)) s S := by
          intro u hu; exact ⟨hu, hctargerange⟩
        have hFt_has : HasFDerivWithinAt Ft (fderivWithin ℝ Ft S (t, e)) S (t, e) :=
          hFt_diff.hasFDerivWithinAt
        have hcomp_raw : HasFDerivWithinAt (Ft ∘ (fun u : ℝ => ((u, e) : ℝ × E)))
            ((fderivWithin ℝ Ft S (t, e)).comp (ContinuousLinearMap.inl ℝ ℝ E))
            s t :=
          hFt_has.comp t hinl_within hmaps_te
        have hcomp : HasFDerivWithinAt (fun u : ℝ => Ft (u, e))
            ((fderivWithin ℝ Ft S (t, e)).comp (ContinuousLinearMap.inl ℝ ℝ E))
            s t := hcomp_raw
        have huniq_s : UniqueDiffWithinAt ℝ s t := hs _ ht
        have hderiv_within : HasDerivWithinAt (fun u : ℝ => Ft (u, e))
            (((fderivWithin ℝ Ft S (t, e)).comp (ContinuousLinearMap.inl ℝ ℝ E)) 1)
            s t :=
          hcomp.hasDerivWithinAt
        change derivWithin (fun τ : ℝ => Ft (τ, e)) s t =
            fderivWithin ℝ Ft S (t, e) ((1, 0) : ℝ × E)
        rw [hderiv_within.derivWithin huniq_s]
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      -- Transport `fderivWithin ... (range I) (φ x₀)` across `hev`.
      have huniq_range : UniqueDiffWithinAt ℝ (Set.range I) (extChartAt I x₀ x₀) :=
        I.uniqueDiffOn _ (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀))
      have hev_eq :
          fderivWithin ℝ (fun e : E => derivWithin (fun τ : ℝ => Ft (τ, e)) s t)
            (Set.range I) (extChartAt I x₀ x₀) =
          fderivWithin ℝ
            (fun e : E => fderivWithin ℝ Ft S (t, e) ((1, 0) : ℝ × E))
            (Set.range I) (extChartAt I x₀ x₀) :=
        Filter.EventuallyEq.fderivWithin_eq hev
          (hev.self_of_nhdsWithin
            (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀)))
      rw [hev_eq]
      exact fderivWithin_clm_apply_comp_inr_sliceSpaceOn I M hs F x₀ ht (X x₀)
    -- Combine via Schwarz.
    rw [hLHS_eq, hRHS_eq]
    exact hsymm ((1, 0) : ℝ × E) ((0, v) : ℝ × E)
  · -- Degenerate case: `t ∉ s`. Both sides vanish pointwise.
    ext x₀
    change
      (((concreteTimeDerivativeDataOn I M s hs).dt_apply
        (fun σ => (concreteDerivationEmbedding I M).embed X (f σ)) t :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀ =
      (((concreteDerivationEmbedding I M).embed X
        ((concreteTimeDerivativeDataOn I M s hs).dt_apply f t) :
          C^∞⟮I, M; ℝ⟯) : M → ℝ) x₀
    -- LHS = 0.
    have hLHS_zero :
        ((concreteTimeDerivativeDataOn I M s hs).dt_apply
          (fun σ => (concreteDerivationEmbedding I M).embed X (f σ)) t :
            C^∞⟮I, M; ℝ⟯) = 0 := by
      change (concreteDtOn I M hs
          (concreteLiftOn I M s
            (fun σ => (concreteDerivationEmbedding I M).embed X (f σ)))).fam t = 0
      change (concreteDtOnFun I M hs
          (concreteLiftOn I M s
            (fun σ => (concreteDerivationEmbedding I M).embed X (f σ)))).fam t = 0
      rw [concreteDtOnFun_fam]
      exact concreteDtOnFam_of_notMem I M hs _ ht
    -- RHS: `dt_apply f t = 0`, so `embed X 0 = 0` by linearity.
    have hRHS_zero :
        ((concreteTimeDerivativeDataOn I M s hs).dt_apply f t :
          C^∞⟮I, M; ℝ⟯) = 0 := by
      change (concreteDtOn I M hs (concreteLiftOn I M s f)).fam t = 0
      change (concreteDtOnFun I M hs (concreteLiftOn I M s f)).fam t = 0
      rw [concreteDtOnFun_fam]
      exact concreteDtOnFam_of_notMem I M hs _ ht
    rw [hLHS_zero, hRHS_zero]
    simp only [ContMDiffMap.coe_zero, map_zero, Pi.zero_apply]

end
