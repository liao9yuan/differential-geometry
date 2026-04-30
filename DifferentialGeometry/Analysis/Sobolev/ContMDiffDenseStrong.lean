import DifferentialGeometry.Analysis.Sobolev.ContMDiffDenseFinal
import DifferentialGeometry.Analysis.Sobolev.StrictStrongSupport
import DifferentialGeometry.Analysis.Sobolev.CrossChartBoundStrictMemWkp
import DifferentialGeometry.Analysis.Sobolev.ChartBanachManifold

/-!
# Smooth-density theorem for `W^{1,p}_chart(M)` on a closed Riemannian manifold

For a closed Riemannian manifold `M` modelled on a finite-dimensional real
inner-product space, `1 ≤ p < ∞`, and a function `u ∈ W^{1,p}_chart(M)`, smooth
functions are dense: for every `ε > 0` there is a `C^∞` `v : M → ℝ` with
`wkpNormChart g 1 p (u - v) ≤ ENNReal.ofReal ε`.

The construction:

1. Pick a per-chart compact neighbourhood `K_α^M ⊆ chart α source` whose
   interior contains `tsupport ρ_α`. Build a smooth manifold cutoff `η_M_α`
   that is `1` on `tsupport ρ_α` and supported in `K_α^M`. Pull this back to
   the Euclidean chart target as `ηE_α := etaEuclid α η_M_α`. Then `ηE_α`
   has closed support inside the chart-α image of `K_α^M`.
2. Per-chart smooth approximant `χ_α : EuclN → ℝ` with strict strong support
   inside the chart-α image of `K_α^M`, via
   `exists_strict_strong_support_approx`, satisfying
   `wkpNorm 1 p (chartPushed g α u - χ_α) ≤ ENNReal.ofReal ε_per`.
3. The "tightened" chart-pushed `f_α := ηE_α * chartPushed g α u`. Globally on
   `EuclN`, `f_α` has tsupport inside the chart-α image of `K_α^M`. On the
   chart target, `f_α` agrees pointwise with `chartPushed g α u`.
4. The cross-chart constant `K_{γ,α}` from
   `cross_chart_bound_strict_strong_memWkp`, applied to `f_α - χ_α`.
5. Manifold approximant `v(x) := Σ_α∈chartAtlasPOU_finset chartPullback I α χ_α (x)`,
   smooth via `chartPullback_contMDiff` and `contMDiff_finset_sum_chartPullback`.
6. The pointwise identity `u(x) = Σ_α chartPullback I α (chartPushed g α u)(x)`
   over the finset, derived from the partition-of-unity identity
   `Σ_α ρ_α(x) = 1`.
7. Triangle inequality + cross-chart bound + per-chart bound to get
   `wkpNormChart g 1 p (u - v) ≤ ε`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Linearity of `chartPullback` over differences -/

omit [IsManifold I ∞ M] in
/-- The chart-pullback is additive on the difference of Euclidean functions. -/
lemma chartPullback_sub (α : M)
    (ψ₁ ψ₂ : EuclN → ℝ) :
    chartPullback I α (fun y => ψ₁ y - ψ₂ y) =
      fun x => chartPullback I α ψ₁ x - chartPullback I α ψ₂ x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · simp [chartPullback_apply_of_mem (I := I) (M := M) α _ hx]
  · simp [chartPullback_apply_of_notMem (I := I) (M := M) α _ hx]

omit [IsManifold I ∞ M] in
/-- A finite sum of chart-pullbacks of the same chart `α` is the chart-pullback
of the finite sum of Euclidean functions. (Not used in the main theorem;
recorded for completeness.) -/
lemma chartPullback_finset_sum (α : M)
    {ι : Type*} (S : Finset ι) (ψ : ι → EuclN → ℝ) :
    chartPullback I α (fun y => ∑ i ∈ S, ψ i y) =
      fun x => ∑ i ∈ S, chartPullback I α (ψ i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      funext x
      simp only [Finset.sum_empty]
      by_cases hx : x ∈ (chartAt H α).source
      · simp [chartPullback_apply_of_mem (I := I) (M := M) α _ hx]
      · simp [chartPullback_apply_of_notMem (I := I) (M := M) α _ hx]
  | insert i S hiS ih =>
      have h_eq : (fun y => ∑ j ∈ insert i S, ψ j y) =
          (fun y => ψ i y + ∑ j ∈ S, ψ j y) := by
        funext y; rw [Finset.sum_insert hiS]
      rw [h_eq, chartPullback_add (I := I) (M := M) α _ _, ih]
      funext x
      rw [Finset.sum_insert hiS]

/-! ## Pointwise POU identity: `u = Σ_α∈Finset chartPullback α (chartPushed α u)` -/

/-- On a compact manifold with the canonical chart-atlas POU, every function
`u : M → ℝ` decomposes pointwise as a finite sum of chart-pulled-back
chart-pushed pieces:
`u(x) = Σ_α∈chartAtlasPOU_finset (chartPullback I α (chartPushed g α u))(x)`. -/
lemma fun_eq_finset_sum_chartPullback_chartPushed
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (u : M → ℝ) :
    (fun x : M => u x) =
      fun x =>
        ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
            (I := I) (M := M),
          chartPullback I α
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) x := by
  classical
  funext x
  -- Per-summand: chartPullback α (chartPushed α u)(x) = ρ_α(x) · u(x).
  -- This is the same identity proved in `wkpChartFun_eq_finset_sum_pullback`,
  -- specialised here without requiring `u ∈ WkpChart`.
  have h_eq : ∀ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I) (M := M),
      chartPullback I α
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) x =
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x *
          u x := by
    intro α _
    by_cases hxα : x ∈ (chartAt H α).source
    · -- chartPullback I α v x = pullbackToManifold I α v x by definitional unfolding.
      rw [chartPullback_apply_of_mem (I := I) (M := M) α _ hxα]
      have hx_extchartsource : x ∈ (extChartAt I α).source := by
        rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hxα
      have h_symm_toEucl : (toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) ((extChartAt I α) x)) = (extChartAt I α) x :=
        (toEuclidean (E := E)).symm_apply_apply _
      have h_symm_extChart : (extChartAt I α).symm ((extChartAt I α) x) = x :=
        (extChartAt I α).left_inv hx_extchartsource
      unfold chartPushed
      rw [h_symm_toEucl, h_symm_extChart]
    · -- Off chart-α source: chartPullback returns 0; ρ_α x = 0 (subordination).
      rw [chartPullback_apply_of_notMem (I := I) (M := M) α _ hxα]
      have h_subord :=
        DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate (I := I) (M := M)
      have h_tsupp : tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source := h_subord α
      have h_x_notin : x ∉ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h => hxα (h_tsupp h)
      have h_rho_zero :
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x = 0 :=
        image_eq_zero_of_notMem_tsupport h_x_notin
      rw [h_rho_zero]; ring
  rw [Finset.sum_congr rfl h_eq]
  rw [show (∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
      (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x * u x) =
      (∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
        (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x) * u x
      from by rw [Finset.sum_mul]]
  rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x, one_mul]

/-! ## Bundle: per-chart strict-strong-support approximant data -/

/-- For each chart `α : M`, choose a fixed compact `K_α ⊆ chart α source` (with
`tsupport ρ_α ⊆ interior K_α`) and a strict-strong-support smooth approximant
`χ_α : EuclN → ℝ` whose closed support sits inside the chart-α image of `K_α`,
with per-chart Euclidean Sobolev distance to `chartPushed g α u` bounded by
`ENNReal.ofReal ε_per`. -/
private lemma exists_strict_strong_support_approx_with_compact_neighborhood
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g 1 p u)
    (α : M) :
    ∃ K_α : Set M, IsCompact K_α ∧ K_α ⊆ (chartAt H α).source ∧
      tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ interior K_α ∧
      ∀ ε_per > 0,
        ∃ χ : EuclN → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
          tsupport χ ⊆
            (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α ∧
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 p
            (fun y => chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y - χ y)
            (chartTargetEuclid (I := I) (M := M) α) ≤
            ENNReal.ofReal ε_per := by
  obtain ⟨K_α, hK_compact, hK_chart, h_tsupp_in_int_K, hχ⟩ :=
    exists_strict_strong_support_approx (I := I) (M := M) g hp_one hp_top α
  refine ⟨K_α, hK_compact, hK_chart, h_tsupp_in_int_K, ?_⟩
  intro ε_per hε_per
  exact hχ hu ε_per hε_per

/-! ## The "tightened" chart-pushed function `ηE_α * chartPushed g α u` -/

/-- `tightenedChartPushed` is `ηE_α * chartPushed g α u`, where `ηE_α` is the
Euclidean pullback of a manifold cutoff supported inside `K_α` and `≡ 1` on
`tsupport ρ_α`. By construction:

* `tsupport (tightenedChartPushed) ⊆ chart-α image of K_α^M` (globally on `EuclN`);
* `tightenedChartPushed = chartPushed g α u` pointwise on `chartTargetEuclid α`
  (since `ηE_α = 1` on the chart-α image of `tsupport ρ_α`, and `chartPushed g α u`
  vanishes off this set on the chart target).

This makes `tightenedChartPushed - χ_α` ready as input to the cross-chart bound. -/
private def tightenedChartPushed
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) (η_M : M → ℝ) (u : M → ℝ) : EuclN → ℝ :=
  fun y =>
    etaEuclid (I := I) (M := M) α η_M y *
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y

/-- The chart-pullback of `tightenedChartPushed` agrees with the chart-pullback
of `chartPushed g α u` on `M`. -/
private lemma chartPullback_tightenedChartPushed_eq
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {η_M : M → ℝ}
    (hη_one_on_tsupport :
      ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1)
    (u : M → ℝ) :
    chartPullback I α
        (tightenedChartPushed (I := I) (M := M) α η_M u) =
      chartPullback I α
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) := by
  classical
  funext x
  by_cases hxα : x ∈ (chartAt H α).source
  · rw [chartPullback_apply_of_mem (I := I) (M := M) α _ hxα]
    rw [chartPullback_apply_of_mem (I := I) (M := M) α _ hxα]
    -- LHS = ηE_α(toEucl(ext α x)) · chartPushed α u (toEucl(ext α x)).
    -- chartPushed α u (toEucl(ext α x)) = ρ_α(x) · u(x).
    -- If ρ_α(x) = 0, both sides equal 0.
    -- If ρ_α(x) ≠ 0, then x ∈ Function.support ρ_α ⊆ tsupport ρ_α, so
    --   ηE_α(toEucl(ext α x)) = 1 (since the chart-α image of x lies in the
    --   chart-α image of tsupport ρ_α, where ηE_α ≡ 1).
    set y : EuclN := (toEuclidean (E := E)) ((extChartAt I α) x) with hy_def
    show tightenedChartPushed (I := I) (M := M) α η_M u y =
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y
    unfold tightenedChartPushed
    -- Compute chartPushed α u y, using x ∈ chart α source.
    have hx_extsource : x ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hxα
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
      rw [hy_def]
      exact ⟨extChartAt I α x, (extChartAt I α).map_source hx_extsource, rfl⟩
    have h_symm_toEucl : (toEuclidean (E := E)).symm y = (extChartAt I α) x := by
      rw [hy_def, (toEuclidean (E := E)).symm_apply_apply]
    have h_symm_extChart : (extChartAt I α).symm
        ((toEuclidean (E := E)).symm y) = x := by
      rw [h_symm_toEucl, (extChartAt I α).left_inv hx_extsource]
    -- chartPushed α u y = ρ_α(x) * u(x).
    have h_chartPushed_eq : chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y =
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x := by
      unfold chartPushed
      rw [h_symm_extChart]
    rw [h_chartPushed_eq]
    -- Now the goal: ηE_α y * (ρ_α(x) * u(x)) = ρ_α(x) * u(x).
    by_cases h_rho_zero :
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x = 0
    · rw [h_rho_zero]; ring
    · -- ρ_α(x) * u(x) ≠ 0 ⇒ ρ_α(x) ≠ 0 ⇒ x ∈ Function.support ρ_α ⊆ tsupport ρ_α.
      have h_rho_ne : ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≠ 0 := by
        intro h0
        apply h_rho_zero
        rw [h0]; ring
      have hx_in_supp : x ∈ Function.support
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        simp only [Function.mem_support, ne_eq]; exact h_rho_ne
      have hx_in_tsupp : x ∈ tsupport
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := subset_tsupport _ hx_in_supp
      -- y ∈ chart-α image of tsupport ρ_α.
      have hy_in_image :
          y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
            tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        refine ⟨x, hx_in_tsupp, ?_⟩
        rw [hy_def]
      -- ηE_α y = 1.
      have hηE_y : etaEuclid (I := I) (M := M) α η_M y = 1 :=
        etaEuclid_eq_one_of_eta_eq_one (I := I) (M := M) α η_M
          hη_one_on_tsupport hy_in_image
      rw [hηE_y]; ring
  · rw [chartPullback_apply_of_notMem (I := I) (M := M) α _ hxα]
    rw [chartPullback_apply_of_notMem (I := I) (M := M) α _ hxα]

/-- The closed support of `tightenedChartPushed` lies inside the chart-α image
of `K_α^M`, when the underlying manifold cutoff `η_M` has `tsupport η_M ⊆ K_α`. -/
private lemma tsupport_tightenedChartPushed_subset
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {η_M : M → ℝ}
    (hη_cpt : HasCompactSupport η_M)
    (hη_tsupp_chart : tsupport η_M ⊆ (chartAt H α).source)
    {K_α : Set M} (hη_tsupp_K : tsupport η_M ⊆ K_α)
    (u : M → ℝ) :
    tsupport (tightenedChartPushed (I := I) (M := M) α η_M u) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α := by
  classical
  -- support (ηE * chartPushed α u) ⊆ support ηE.
  have h_supp_in_etaEuclid :
      tsupport (tightenedChartPushed (I := I) (M := M) α η_M u) ⊆
        tsupport (etaEuclid (I := I) (M := M) α η_M) := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy
    -- y ∈ support (ηE_α · chartPushed α u) ⇒ ηE_α y ≠ 0 ⇒ y ∈ support ηE_α.
    have hηE_ne : etaEuclid (I := I) (M := M) α η_M y ≠ 0 := by
      intro h0
      apply hy
      change etaEuclid (I := I) (M := M) α η_M y *
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y = 0
      rw [h0]; ring
    exact Function.mem_support.mpr hηE_ne
  -- tsupport ηE_α ⊆ chart-α image of tsupport η_M.
  have h_etaEuclid_supp :
      tsupport (etaEuclid (I := I) (M := M) α η_M) ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' tsupport η_M :=
    tsupport_etaEuclid_subset_chartImage (I := I) (M := M) α η_M hη_cpt hη_tsupp_chart
  -- chart-α image of tsupport η_M ⊆ chart-α image of K_α (since tsupport η_M ⊆ K_α).
  have h_image_mono :
      (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' tsupport η_M ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) '' K_α :=
    Set.image_mono hη_tsupp_K
  exact h_supp_in_etaEuclid.trans (h_etaEuclid_supp.trans h_image_mono)

/-- `tightenedChartPushed` agrees with `chartPushed g α u` pointwise on the chart
target `chartTargetEuclid α`, when `η_M ≡ 1` on `tsupport ρ_α`. -/
private lemma tightenedChartPushed_eq_chartPushed_on_target
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (α : M) {η_M : M → ℝ}
    (hη_one_on_tsupport :
      ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1)
    (u : M → ℝ) :
    ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      tightenedChartPushed (I := I) (M := M) α η_M u y =
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y := by
  intro y hy_target
  unfold tightenedChartPushed
  -- If chartPushed α u y = 0, both sides equal 0.
  by_cases hf_zero : chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y = 0
  · rw [hf_zero]; ring
  · -- chartPushed α u y ≠ 0 ⇒ y ∈ chart-α image of tsupport ρ_α.
    -- Then ηE_α y = 1.
    have hy_in_image' :
        y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I α x)) ''
          tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
      by_contra hy_off
      apply hf_zero
      -- chartImagePOUTsupport α = the same image set; use the existing lemma.
      have hy_off' : y ∉ chartImagePOUTsupport (I := I) (M := M) α := by
        intro h_in
        apply hy_off
        unfold chartImagePOUTsupport at h_in
        rcases h_in with ⟨z, ⟨x, hx_supp, hxz⟩, hzy⟩
        exact ⟨x, hx_supp, by rw [← hzy, ← hxz]⟩
      exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
        α u hy_target hy_off'
    have hηE_y : etaEuclid (I := I) (M := M) α η_M y = 1 :=
      etaEuclid_eq_one_of_eta_eq_one (I := I) (M := M) α η_M
        hη_one_on_tsupport hy_in_image'
    rw [hηE_y]; ring

/-- `tightenedChartPushed` is in `MemWkp 1 p` of the chart target. -/
private lemma tightenedChartPushed_memWkp
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g 1 p u) (α : M)
    {η_M : M → ℝ}
    (hη_M_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ η_M)
    (hη_M_cpt : HasCompactSupport η_M)
    (hη_M_supp_chart : tsupport η_M ⊆ (chartAt H α).source) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 p
      (tightenedChartPushed (I := I) (M := M) α η_M u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- ηE_α is smooth on EuclN, with norm and gradient bounded.
  set ηE : EuclN → ℝ := etaEuclid (I := I) (M := M) α η_M with hηE_def
  have hηE_smooth : ContDiff ℝ (⊤ : ℕ∞) ηE :=
    contDiff_etaEuclid (I := I) (M := M) α η_M hη_M_smooth hη_M_cpt hη_M_supp_chart
  have hηE_cpt : HasCompactSupport ηE :=
    hasCompactSupport_etaEuclid (I := I) (M := M) α η_M hη_M_cpt hη_M_supp_chart
  obtain ⟨C_grad, _hC_grad_pos, hC_grad⟩ :=
    exists_grad_bound_of_compactSupport_smooth hηE_smooth hηE_cpt
  -- norm bound: ηE has continuous compactly-supported, so ‖ηE‖ ≤ C_norm globally.
  obtain ⟨C_norm, _hC_norm_pos, hC_norm⟩ :
      ∃ C : ℝ, 0 < C ∧ ∀ x : EuclN, ‖ηE x‖ ≤ C := by
    set f : EuclN → ℝ := fun x => ‖ηE x‖
    have hf_cont : Continuous f := hηE_smooth.continuous.norm
    -- f is 0 outside tsupport ηE (compact).
    have h_zero_off : ∀ x : EuclN, x ∉ tsupport ηE → f x = 0 := by
      intro x hx
      change ‖ηE x‖ = 0
      rw [image_eq_zero_of_notMem_tsupport hx]
      simp
    set K : Set EuclN := tsupport ηE with hK_def
    have hK_compact : IsCompact K := hηE_cpt
    have h_bdd : ∃ C : ℝ, ∀ x ∈ K, f x ≤ C := by
      by_cases hKn : K.Nonempty
      · obtain ⟨x₀, _hx₀K, hx₀_max⟩ :=
          hK_compact.exists_isMaxOn hKn hf_cont.continuousOn
        exact ⟨f x₀, fun x hx => hx₀_max hx⟩
      · refine ⟨0, ?_⟩
        intro x hx
        exact (hKn ⟨x, hx⟩).elim
    obtain ⟨C₀, hC₀⟩ := h_bdd
    refine ⟨max C₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x
    by_cases hx : x ∈ K
    · exact (hC₀ x hx).trans (le_max_left _ _)
    · rw [show ‖ηE x‖ = f x from rfl, h_zero_off x hx]
      exact le_trans (le_refl 0) (le_trans zero_le_one (le_max_right _ _))
  -- Combined bound.
  set C : ℝ := max C_norm C_grad with hC_def
  have hC_norm_le : ∀ y : EuclN, ‖ηE y‖ ≤ C := fun y =>
    (hC_norm y).trans (le_max_left _ _)
  have hC_grad_le : ∀ y : EuclN, ‖fderiv ℝ ηE y‖ ≤ C := fun y =>
    (hC_grad y).trans (le_max_right _ _)
  have hC_norm_target : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α, ‖ηE y‖ ≤ C :=
    fun y _ => hC_norm_le y
  have hC_grad_target : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖fderiv ℝ ηE y‖ ≤ C := fun y _ => hC_grad_le y
  -- Apply chartCutoff_smul_chartPushed_memWkp.
  exact chartCutoff_smul_chartPushed_memWkp (I := I) (M := M) g hp_one hu α
    hηE_smooth hC_norm_target hC_grad_target

/-- `wkpNorm 1 p (tightenedChartPushed α η_M u - χ) (chartTargetEuclid α)`
equals `wkpNorm 1 p (chartPushed g α u - χ) (chartTargetEuclid α)` (modulo a.e.
equality on the chart target). -/
private lemma wkpNorm_tightenedChartPushed_sub_eq
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    (α : M) {η_M : M → ℝ}
    (hη_one_on_tsupport :
      ∀ x ∈ tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1)
    (u : M → ℝ) (χ : EuclN → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 p
      (fun y => tightenedChartPushed (I := I) (M := M) α η_M u y - χ y)
      (chartTargetEuclid (I := I) (M := M) α) =
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 1 p
      (fun y => chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y - χ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_diff_eq : (fun y => tightenedChartPushed (I := I) (M := M) α η_M u y - χ y)
      =ᵐ[volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y - χ y) := by
    refine (ae_restrict_iff' h_target_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    rw [tightenedChartPushed_eq_chartPushed_on_target (I := I) (M := M)
      α hη_one_on_tsupport u y hy]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_diff_eq

/-! ## Headline: smooth functions are dense in `W^{1,p}_chart(M)` -/

/-- **Smooth-density theorem in `W^{1,p}_chart(M)`.** For a closed Riemannian
manifold `M` modelled on a finite-dimensional real inner-product space, every
function `u : M → ℝ` in `W^{1,p}_chart(M)` (with `1 ≤ p < ∞`) admits, for any
`ε > 0`, a smooth `v : M → ℝ` with `wkpNormChart g 1 p (u - v) ≤ ε`. -/
theorem contMDiff_dense_in_WkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g 1 p u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧
      wkpNormChart (I := I) (M := M) g 1 p (fun x => u x - v x) ≤
        ENNReal.ofReal ε := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M)
    with hS_def
  -- Step 1: per-chart compact neighbourhood K_α and manifold cutoff η_M_α.
  have h_per_chart : ∀ α : S,
      ∃ K_α : Set M, IsCompact K_α ∧ K_α ⊆ (chartAt H (α : M)).source ∧
        tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M
          (α : M) : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ interior K_α ∧
        ∃ η_M : M → ℝ, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ η_M ∧
          Set.range η_M ⊆ Set.Icc (0 : ℝ) 1 ∧
          (∀ x ∈ tsupport
            ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M (α : M)
              : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M x = 1) ∧
          tsupport η_M ⊆ K_α := by
    intro α
    obtain ⟨K_α, hK_compact, hK_chart, h_tsupp_in_int_K⟩ :=
      exists_compact_neighborhood_of_tsupport_pou (I := I) (M := M) (α : M)
    obtain ⟨η_M, hη_smooth, hη_range, _hη_supp_eq, hη_one_M, hη_tsupp_K⟩ :=
      exists_manifold_cutoff_one_on_tsupport_pou (I := I) (M := M) (α : M)
        hK_compact h_tsupp_in_int_K
    exact ⟨K_α, hK_compact, hK_chart, h_tsupp_in_int_K,
      η_M, hη_smooth, hη_range, hη_one_M, hη_tsupp_K⟩
  -- Choose K_α and η_M for each α ∈ S using `Classical.choice`.
  let K_choose : S → Set M := fun α => (h_per_chart α).choose
  let K_α : S → Set M := K_choose
  have hK_compact : ∀ α : S, IsCompact (K_α α) := fun α =>
    (h_per_chart α).choose_spec.1
  have hK_chart : ∀ α : S, K_α α ⊆ (chartAt H (α : M)).source := fun α =>
    (h_per_chart α).choose_spec.2.1
  have hK_tsupp_in_int : ∀ α : S, tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M (α : M)
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ interior (K_α α) := fun α =>
    (h_per_chart α).choose_spec.2.2.1
  let η_choose : S → (M → ℝ) := fun α => (h_per_chart α).choose_spec.2.2.2.choose
  let η_M : S → (M → ℝ) := η_choose
  have hη_smooth : ∀ α : S, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (η_M α) :=
    fun α => (h_per_chart α).choose_spec.2.2.2.choose_spec.1
  have hη_one_on_tsupport : ∀ α : S, ∀ x ∈ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M (α : M)
        : C^∞⟮I, M; ℝ⟯) : M → ℝ), η_M α x = 1 := fun α =>
    (h_per_chart α).choose_spec.2.2.2.choose_spec.2.2.1
  have hη_tsupp_K : ∀ α : S, tsupport (η_M α) ⊆ K_α α := fun α =>
    (h_per_chart α).choose_spec.2.2.2.choose_spec.2.2.2
  have hη_M_supp_chart : ∀ α : S, tsupport (η_M α) ⊆ (chartAt H (α : M)).source :=
    fun α => (hη_tsupp_K α).trans (hK_chart α)
  have hη_M_cpt : ∀ α : S, HasCompactSupport (η_M α) := fun α =>
    (hK_compact α).of_isClosed_subset (isClosed_tsupport _) (hη_tsupp_K α)
  -- Step 2: per-pair cross-chart constants.
  have h_per_pair : ∀ γ α : S, ∃ K : ℝ, 0 < K ∧
      ∀ {v : EuclN → ℝ},
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 1 p v
            (chartTargetEuclid (I := I) (M := M) (α : M)) →
        tsupport v ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (γ : M)
            (chartPullback I (α : M) v))
          (chartTargetEuclid (I := I) (M := M) (γ : M)) ≤
          ENNReal.ofReal K *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 1 p v
              (chartTargetEuclid (I := I) (M := M) (α : M)) := fun γ α =>
    cross_chart_bound_strict_strong_memWkp (I := I) (M := M) g hp_one hp_top
      (γ : M) (α : M) (hK_compact α) (hK_chart α)
  let K_pair : S → S → ℝ := fun γ α => (h_per_pair γ α).choose
  have hK_pair_pos : ∀ γ α : S, 0 < K_pair γ α := fun γ α =>
    (h_per_pair γ α).choose_spec.1
  have hK_pair_bound : ∀ γ α : S, ∀ {v : EuclN → ℝ},
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p v
          (chartTargetEuclid (I := I) (M := M) (α : M)) →
      tsupport v ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (γ : M)
          (chartPullback I (α : M) v))
        (chartTargetEuclid (I := I) (M := M) (γ : M)) ≤
        ENNReal.ofReal (K_pair γ α) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 p v
            (chartTargetEuclid (I := I) (M := M) (α : M)) := fun γ α =>
    (h_per_pair γ α).choose_spec.2
  -- Step 3: total constant K_total = (Σ_(γ,α) K_pair γ α) + 1, picked positive.
  set K_total : ℝ := (∑ γ : S, ∑ α : S, K_pair γ α) + 1 with hK_total_def
  have hK_total_pos : 0 < K_total := by
    rw [hK_total_def]
    have h_sum_nn : 0 ≤ ∑ γ : S, ∑ α : S, K_pair γ α := by
      refine Finset.sum_nonneg ?_
      intro γ _
      refine Finset.sum_nonneg ?_
      intro α _
      exact (hK_pair_pos γ α).le
    linarith
  -- Step 4: pick ε_per := ε / K_total.
  set ε_per : ℝ := ε / K_total with hε_per_def
  have hε_per_pos : 0 < ε_per := div_pos hε hK_total_pos
  have hK_total_eps_le : K_total * ε_per ≤ ε := by
    rw [hε_per_def, mul_div_assoc']
    rw [div_le_iff₀ hK_total_pos]
    -- K_total * ε ≤ ε * K_total ↔ true.
    linarith [mul_comm K_total ε]
  -- Step 5: per-chart strict-strong-support smooth approximant χ_α.
  have h_chi : ∀ α : S, ∃ χ : EuclN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 p
        (fun y => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u y - χ y)
        (chartTargetEuclid (I := I) (M := M) (α : M)) ≤
        ENNReal.ofReal ε_per := by
    intro α
    -- Use the strict-strong-support approximation, with our specific K_α α.
    -- We re-derive it in terms of the K_α α we chose earlier; for that, use
    -- the original `exists_strict_strong_support_approx`.
    obtain ⟨K_α', hK_compact', hK_chart', h_tsupp_in_int_K', hχ⟩ :=
      exists_strict_strong_support_approx (I := I) (M := M) g hp_one hp_top (α : M)
    -- The K_α' produced is some compact neighbourhood — possibly different from K_α α.
    -- However, the bound we need is in terms of K_α α; so we use the
    -- strict-strong-support approx with K_α α directly. To do this, we replicate
    -- the strict-strong-support construction with K_α α.
    -- A cleaner route: re-derive `exists_smooth_strong_support_approx` with our
    -- K_α α + cutoff η_M α. Actually, the key step is:
    --   given K_α α (compact, ⊆ chart α source, tsupport ρ_α ⊆ interior K_α α),
    --   given η_M α (smooth, =1 on tsupport ρ_α, supp ⊆ K_α α),
    --   produce χ with tsupport χ ⊆ chart-α image of K_α α and the wkpNorm bound.
    -- Inline the construction from `exists_strict_strong_support_approx`.
    -- Step 5a: ηE := etaEuclid α (η_M α).
    set ηE : EuclN → ℝ := etaEuclid (I := I) (M := M) (α : M) (η_M α) with hηE_def
    have hηE_smooth : ContDiff ℝ (⊤ : ℕ∞) ηE :=
      contDiff_etaEuclid (I := I) (M := M) (α : M) (η_M α) (hη_smooth α)
        (hη_M_cpt α) (hη_M_supp_chart α)
    have hηE_cpt : HasCompactSupport ηE :=
      hasCompactSupport_etaEuclid (I := I) (M := M) (α : M) (η_M α)
        (hη_M_cpt α) (hη_M_supp_chart α)
    have hηE_range : Set.range ηE ⊆ Set.Icc (0 : ℝ) 1 := by
      have hη_range_M : Set.range (η_M α) ⊆ Set.Icc (0 : ℝ) 1 :=
        (h_per_chart α).choose_spec.2.2.2.choose_spec.2.1
      exact etaEuclid_range_Icc (I := I) (M := M) (α : M) (η_M α) hη_range_M
    have hηE_norm_one : ∀ y : EuclN, ‖ηE y‖ ≤ 1 :=
      norm_le_one_of_range_Icc hηE_range
    have hηE_tsupp_in_image_K : tsupport ηE ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α := by
      refine subset_trans
        (tsupport_etaEuclid_subset_chartImage (I := I) (M := M) (α : M) (η_M α)
          (hη_M_cpt α) (hη_M_supp_chart α)) ?_
      exact Set.image_mono (hη_tsupp_K α)
    have hηE_one_on_pou_image :
        ∀ y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) ''
          tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M (α : M)
            : C^∞⟮I, M; ℝ⟯) : M → ℝ),
        ηE y = 1 := fun y hy =>
      etaEuclid_eq_one_of_eta_eq_one (I := I) (M := M) (α : M) (η_M α)
        (hη_one_on_tsupport α) hy
    obtain ⟨Cη, _hCη_pos, hCη_grad⟩ :=
      exists_grad_bound_etaEuclid (I := I) (M := M) (α : M) (η_M α)
        (hη_smooth α) (hη_M_cpt α) (hη_M_supp_chart α)
    set C : ℝ := max Cη 1 with hC_def
    have hC_one : ∀ y : EuclN, ‖ηE y‖ ≤ C :=
      fun y => (hηE_norm_one y).trans (le_max_right _ _)
    have hC_grad : ∀ y : EuclN, ‖fderiv ℝ ηE y‖ ≤ C :=
      fun y => (hCη_grad y).trans (le_max_left _ _)
    set Ωα : Set EuclN := chartTargetEuclid (I := I) (M := M) (α : M) with hΩα_def
    have hΩα_open : IsOpen Ωα := chartTargetEuclid_isOpen (I := I) (M := M) (α : M)
    have hC_one_on_Ωα : ∀ y ∈ Ωα, ‖ηE y‖ ≤ C := fun y _ => hC_one y
    have hC_grad_on_Ωα : ∀ y ∈ Ωα, ‖fderiv ℝ ηE y‖ ≤ C := fun y _ => hC_grad y
    -- Apply the Leibniz quantitative bound to get K_leib.
    have h_zero_memWkp :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p (fun _ : EuclN => (0 : ℝ)) Ωα :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
        (d := Module.finrank ℝ E) hp_one hΩα_open
    obtain ⟨K_leib, hK_leib_pos, hK_leib_bound⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le_one
        (d := Module.finrank ℝ E) hp_one hp_top hΩα_open hηE_smooth
        hC_one_on_Ωα hC_grad_on_Ωα h_zero_memWkp
    -- Use the strong-support approximation `exists_smooth_strong_support_approx`.
    set ε_inner : ℝ := ε_per / (K_leib + 1) with hε_inner_def
    have hε_inner_pos : 0 < ε_inner := by
      apply div_pos hε_per_pos
      linarith
    obtain ⟨ψ, hψ_smooth, hψ_cpt, hψ_supp, hψ_close⟩ :=
      exists_smooth_strong_support_approx (I := I) (M := M) g hp_one hp_top hu (α : M)
        ε_inner hε_inner_pos
    set χ : EuclN → ℝ := fun y => ηE y * ψ y with hχ_def
    have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := hηE_smooth.mul hψ_smooth
    have hχ_supp_in : tsupport χ ⊆ tsupport ηE := by
      change tsupport (fun y => ηE y * ψ y) ⊆ tsupport ηE
      refine closure_mono ?_
      intro y hy
      simp only [Function.mem_support, ne_eq] at hy
      have hηE_ne : ηE y ≠ 0 := by
        intro h0; apply hy; rw [h0]; ring
      exact Function.mem_support.mpr hηE_ne
    have hχ_cpt : HasCompactSupport χ :=
      hηE_cpt.of_isClosed_subset (isClosed_tsupport _) hχ_supp_in
    have hχ_supp_image_K : tsupport χ ⊆
        (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
      hχ_supp_in.trans hηE_tsupp_in_image_K
    refine ⟨χ, hχ_smooth, hχ_cpt, hχ_supp_image_K, ?_⟩
    -- Bound `wkpNorm 1 p (chartPushed - χ) Ωα` using the same argument as
    -- in `exists_strict_strong_support_approx`.
    set f : EuclN → ℝ := chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u with hf_def
    have h_one_minus_ηE_f_zero : ∀ y ∈ Ωα, (1 - ηE y) * f y = 0 := by
      intro y hy
      by_cases hf_zero : f y = 0
      · rw [hf_zero]; ring
      · have hy_in_image : y ∈ chartImagePOUTsupport (I := I) (M := M) (α : M) := by
          by_contra hy_off
          apply hf_zero
          exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
            (α : M) u hy hy_off
        have hy_in_image' :
            y ∈ (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) ''
              tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M (α : M)
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
          unfold chartImagePOUTsupport at hy_in_image
          rcases hy_in_image with ⟨z, ⟨x, hx_supp, hxz⟩, hzy⟩
          exact ⟨x, hx_supp, by rw [← hzy, ← hxz]⟩
        have hηEy : ηE y = 1 := hηE_one_on_pou_image y hy_in_image'
        rw [hηEy]; ring
    have h_decomp : ∀ y ∈ Ωα, f y - χ y = ηE y * (f y - ψ y) := by
      intro y hy
      have h0 : (1 - ηE y) * f y = 0 := h_one_minus_ηE_f_zero y hy
      change f y - ηE y * ψ y = ηE y * (f y - ψ y)
      have : f y - ηE y * ψ y = ηE y * (f y - ψ y) + (1 - ηE y) * f y := by ring
      rw [this, h0, add_zero]
    have h_target_meas : MeasurableSet Ωα := hΩα_open.measurableSet
    have h_diff_eq : (fun y => f y - χ y) =ᵐ[volume.restrict Ωα]
        (fun y => ηE y * (f y - ψ y)) := by
      refine (ae_restrict_iff' h_target_meas).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro y hy
      exact h_decomp y hy
    have h_norm_eq :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p (fun y => f y - χ y) Ωα =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p (fun y => ηE y * (f y - ψ y)) Ωα :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) hp_one hΩα_open h_diff_eq
    have hf_mem :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p f Ωα := hu (α : M)
    have hψ_mem :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p ψ Ωα :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
        (d := Module.finrank ℝ E) hΩα_open hψ_smooth hψ_cpt hψ_supp hp_one 1
    have hfψ_mem :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p (fun y => f y - ψ y) Ωα :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.sub
        (d := Module.finrank ℝ E) hp_one hΩα_open hf_mem hψ_mem
    have h_leib_bound :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p (fun y => ηE y * (f y - ψ y)) Ωα ≤
        ENNReal.ofReal K_leib *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 p (fun y => f y - ψ y) Ωα :=
      hK_leib_bound hfψ_mem
    rw [h_norm_eq]
    refine h_leib_bound.trans ?_
    have h_step : ENNReal.ofReal K_leib *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p (fun y => f y - ψ y) Ωα ≤
        ENNReal.ofReal K_leib * ENNReal.ofReal ε_inner :=
      mul_le_mul_of_nonneg_left hψ_close (by simp : (0 : ℝ≥0∞) ≤ ENNReal.ofReal K_leib)
    refine h_step.trans ?_
    have hK_leib_nn : 0 ≤ K_leib := hK_leib_pos.le
    have hε_inner_nn : 0 ≤ ε_inner := hε_inner_pos.le
    rw [← ENNReal.ofReal_mul hK_leib_nn]
    apply ENNReal.ofReal_le_ofReal
    rw [hε_inner_def]
    rw [mul_div_assoc']
    have hK1_pos : 0 < K_leib + 1 := by linarith
    rw [div_le_iff₀ hK1_pos]
    have : K_leib * ε_per ≤ (K_leib + 1) * ε_per := by
      refine mul_le_mul_of_nonneg_right ?_ hε_per_pos.le
      linarith
    linarith
  -- Step 6: choose χ_α from the existential.
  let χ : S → (EuclN → ℝ) := fun α => (h_chi α).choose
  have hχ_smooth : ∀ α : S, ContDiff ℝ (⊤ : ℕ∞) (χ α) := fun α =>
    (h_chi α).choose_spec.1
  have hχ_cpt : ∀ α : S, HasCompactSupport (χ α) := fun α =>
    (h_chi α).choose_spec.2.1
  have hχ_supp : ∀ α : S, tsupport (χ α) ⊆
      (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
    fun α => (h_chi α).choose_spec.2.2.1
  have hχ_close : ∀ α : S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 p
        (fun y => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u y -
            χ α y)
        (chartTargetEuclid (I := I) (M := M) (α : M)) ≤
        ENNReal.ofReal ε_per := fun α => (h_chi α).choose_spec.2.2.2
  -- We also need `tsupport (χ α) ⊆ chartTargetEuclid α`.
  have hχ_supp_target : ∀ α : S, tsupport (χ α) ⊆
      chartTargetEuclid (I := I) (M := M) (α : M) := by
    intro α
    refine (hχ α).trans ?_
    -- chart-α image of K_α α ⊆ chartTargetEuclid α (since K_α ⊆ chart α source).
    intro y hy
    rcases hy with ⟨x, hxK, hxy⟩
    have hx_chart : x ∈ (chartAt H (α : M)).source := hK_chart α hxK
    have hx_ext : x ∈ (extChartAt I (α : M)).source := by
      rw [extChartAt_source]; exact hx_chart
    have h_target : extChartAt I (α : M) x ∈ (extChartAt I (α : M)).target :=
      (extChartAt I (α : M)).map_source hx_ext
    rw [← hxy]
    exact ⟨extChartAt I (α : M) x, h_target, rfl⟩
  -- Step 7: define v and show smoothness.
  set v : M → ℝ := fun x =>
    ∑ α ∈ S.attach, chartPullback I (α : M) (χ α) x with hv_def
  have hv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ v := by
    -- Apply contMDiff_finset_sum_chartPullback.
    refine contMDiff_finset_sum_chartPullback (I := I) (M := M)
      (S := S.attach) (α := fun α : S => (α : M)) (ψ := fun α => χ α) ?_ ?_ ?_
    · intro α _; exact hχ_smooth α
    · intro α _; exact hχ_cpt α
    · intro α _; exact hχ_supp_target α
  refine ⟨v, hv_smooth, ?_⟩
  -- Step 8: estimate wkpNormChart g 1 p (u - v).
  -- Goal: wkpNormChart g 1 p (u - v) ≤ ENNReal.ofReal ε.
  -- Use wkpNormChart_eq_finset_sum to convert to a finite sum over γ ∈ S.
  -- Then bound each summand.
  -- First, MemWkpChart of (u - v).
  -- `u ∈ MemWkpChart`. `v` is smooth + compact support; we'd need `v ∈ MemWkpChart` too.
  -- Actually for the bound we don't need MemWkpChart of (u - v): we only need
  -- `wkpNormChart_eq_finset_sum` and the per-chart bound. Let's compute directly.
  rw [wkpNormChart_eq_finset_sum (I := I) (M := M) g 1 hp_one (fun x => u x - v x)]
  -- ≤ Σ_γ Σ_α ofReal(K_pair γ α) * ofReal ε_per ≤ ofReal(K_total * ε_per) ≤ ofReal ε.
  -- Per-γ: chartPushed γ (u - v) = Σ_α∈Finset chartPushed γ (chartPullback α (chartPushed α u - χ α)).
  -- Use `cross_chart_bound` per (γ, α) on `f_α - χ_α := tightenedChartPushed α (η_M α) u - χ α`,
  -- and a.e.-equivalence to convert `(chartPushed α u - χ α)` into `(f_α - χ α)`.
  have h_per_gamma : ∀ γ ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
          (fun x => u x - v x))
        (chartTargetEuclid (I := I) (M := M) γ) ≤
        ∑ α ∈ S.attach, ENNReal.ofReal (K_pair ⟨γ, ‹_›⟩ α) * ENNReal.ofReal ε_per := by
    intro γ hγS
    -- Express chartPushed γ (u - v) = chartPushed γ u - chartPushed γ v.
    -- Then chartPushed γ v = Σ_α∈S.attach chartPushed γ (chartPullback α (χ α)).
    -- And chartPushed γ u = Σ_α∈S.attach chartPushed γ (chartPullback α (chartPushed α u))
    --                     (by `fun_eq_finset_sum_chartPullback_chartPushed` plus chartPushed_finset_sum).
    -- Hence chartPushed γ (u - v) = Σ_α chartPushed γ (chartPullback α (chartPushed α u - χ α)).
    have h_u_decomp : (fun x : M => u x) =
        fun x =>
          ∑ α ∈ S.attach,
            chartPullback I (α : M)
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u) x := by
      have h_decomp := fun_eq_finset_sum_chartPullback_chartPushed
        (I := I) (M := M) u
      -- Rewrite the sum index from `α ∈ S` to `α ∈ S.attach` (`Finset.attach`).
      rw [h_decomp]
      funext x
      rw [show (∑ α ∈ S, chartPullback I α
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) x) =
          (∑ α ∈ S.attach, chartPullback I (α : M)
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u) x)
          from by rw [Finset.sum_attach S (fun α => chartPullback I α
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) x)]]
    have h_uv_decomp : (fun x : M => u x - v x) =
        fun x =>
          ∑ α ∈ S.attach,
            chartPullback I (α : M)
              (fun y => chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u y -
                χ α y) x := by
      funext x
      have h1 := congrFun h_u_decomp x
      simp only at h1
      change u x - v x = _
      rw [hv_def]
      simp only
      rw [h1]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro α _
      classical
      by_cases hxα : x ∈ (chartAt H (α : M)).source
      · rw [chartPullback_apply_of_mem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_mem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_mem (I := I) (M := M) (α : M) _ hxα]
      · rw [chartPullback_apply_of_notMem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_notMem (I := I) (M := M) (α : M) _ hxα]
        rw [chartPullback_apply_of_notMem (I := I) (M := M) (α : M) _ hxα]
        ring
    -- chartPushed γ (u - v) = Σ_α chartPushed γ (chartPullback α (chartPushed α u - χ α)).
    have h_chartPushed_decomp : chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
        (fun x => u x - v x) =
        fun y => ∑ α ∈ S.attach,
          chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun z => chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u z -
                χ α z)) y := by
      rw [h_uv_decomp]
      exact chartPushed_finset_sum
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ S.attach
        (fun α x => chartPullback I (α : M)
          (fun y => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u y -
            χ α y) x)
    rw [h_chartPushed_decomp]
    -- For each α, bound wkpNorm of summand by ofReal(K_pair γ α) * ofReal ε_per.
    -- Use the membership hypothesis hu α and the fact that f_α - χ α has the
    -- right tsupport.
    -- Define f_α := tightenedChartPushed α (η_M α) u.
    have h_per_alpha : ∀ α ∈ S.attach,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun y => chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u y -
                χ α y)))
          (chartTargetEuclid (I := I) (M := M) γ) ≤
          ENNReal.ofReal (K_pair ⟨γ, hγS⟩ α) * ENNReal.ofReal ε_per := by
      intro α _hα_mem
      -- Define f_α := tightenedChartPushed α (η_M α) u.
      set f_α : EuclN → ℝ :=
        tightenedChartPushed (I := I) (M := M) (α : M) (η_M α) u with hf_α_def
      -- chartPullback α (chartPushed α u - χ α) = chartPullback α (f_α - χ α) on M.
      have h_chartPullback_eq : chartPullback I (α : M)
          (fun y => chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u y -
            χ α y) =
          chartPullback I (α : M) (fun y => f_α y - χ α y) := by
        rw [chartPullback_sub, chartPullback_sub]
        funext x
        simp only
        rw [show chartPullback I (α : M) f_α x =
            chartPullback I (α : M)
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u) x
            from by
          rw [hf_α_def]
          have h_eq := chartPullback_tightenedChartPushed_eq (I := I) (M := M)
            (α : M) (hη_one_on_tsupport α) u
          exact congrFun h_eq x]
      rw [h_chartPullback_eq]
      -- Now apply cross_chart_bound to v := f_α - χ α.
      have hf_α_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p f_α
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        tightenedChartPushed_memWkp (I := I) (M := M) g hp_one hu (α : M)
          (hη_smooth α) (hη_M_cpt α) (hη_M_supp_chart α)
      have hχ_α_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p (χ α)
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport_pub
          (d := Module.finrank ℝ E)
          (chartTargetEuclid_isOpen (I := I) (M := M) (α : M))
          (hχ_smooth α) (hχ_cpt α) (hχ_supp_target α) hp_one 1
      have h_diff_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p (fun y => f_α y - χ α y)
          (chartTargetEuclid (I := I) (M := M) (α : M)) :=
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.sub
          (d := Module.finrank ℝ E) hp_one
          (chartTargetEuclid_isOpen (I := I) (M := M) (α : M))
          hf_α_mem hχ_α_mem
      have h_diff_supp : tsupport (fun y => f_α y - χ α y) ⊆
          (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α := by
        -- tsupport (f - g) ⊆ tsupport f ∪ tsupport g.
        have h_supp_sub : Function.support (fun y => f_α y - χ α y) ⊆
            Function.support f_α ∪ Function.support (χ α) := by
          intro y hy
          by_cases hyf : y ∈ Function.support f_α
          · exact Or.inl hyf
          · right
            change χ α y ≠ 0
            intro h0
            apply hy
            change f_α y - χ α y = 0
            have : f_α y = 0 := Function.notMem_support.mp hyf
            rw [this, h0, sub_self]
        have h_tsupp_sub : tsupport (fun y => f_α y - χ α y) ⊆
            tsupport f_α ∪ tsupport (χ α) := by
          unfold tsupport
          refine (closure_mono h_supp_sub).trans ?_
          rw [closure_union]
        have hf_α_supp : tsupport f_α ⊆
            (fun x : M => (toEuclidean (E := E)) (extChartAt I (α : M) x)) '' K_α α :=
          tsupport_tightenedChartPushed_subset (I := I) (M := M) (α : M)
            (hη_M_cpt α) (hη_M_supp_chart α) (hη_tsupp_K α) u
        exact h_tsupp_sub.trans (Set.union_subset hf_α_supp (hχ_supp α))
      -- Apply cross-chart bound.
      have h_bd := hK_pair_bound ⟨γ, hγS⟩ α h_diff_mem h_diff_supp
      -- Bound the wkpNorm of the difference by ofReal ε_per.
      have h_diff_close :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 p
            (fun y => f_α y - χ α y)
            (chartTargetEuclid (I := I) (M := M) (α : M)) ≤
          ENNReal.ofReal ε_per := by
        rw [hf_α_def]
        rw [wkpNorm_tightenedChartPushed_sub_eq (I := I) (M := M) hp_one (α : M)
          (hη_one_on_tsupport α) u (χ α)]
        exact hχ_close α
      refine h_bd.trans ?_
      exact mul_le_mul_of_nonneg_left h_diff_close (zero_le _)
    -- Triangle inequality across the finset.
    -- wkpNorm (Σ α, f_α) ≤ Σ α wkpNorm (f_α). For Euclidean wkpNorm, we have
    -- wkpNorm (Σ_i f_i) ≤ Σ_i wkpNorm f_i (with all summands MemWkp).
    -- Here each summand is in MemWkp, so this works.
    -- Use a finset induction.
    -- Each summand: chartPushed γ (chartPullback α (chartPushed α u - χ α)).
    -- It's in MemWkp 1 p (chartTargetEuclid γ): use cross-chart bound's predecessor.
    -- But we don't strictly need each summand to be in MemWkp — we just need
    -- Euclidean wkpNorm finset sum subadditivity. The cleanest way: sub
    -- each summand against the bound h_per_alpha, and bound the wkpNorm of
    -- the total by the sum.
    -- Actually, by `wkpNorm_add_le` (per-pair), induction on the finset:
    -- `wkpNorm (Σ_i ψ_i) ≤ Σ_i wkpNorm ψ_i` provided each ψ_i is in MemWkp.
    -- Each summand ψ_α = chartPushed γ (chartPullback α (chartPushed α u - χ α)).
    -- We do this by first showing each is in MemWkp via the cross-chart bound.
    -- Then use the existing lemma for wkpNorm finset sum subadditivity (Euclidean).
    -- Actually a cleaner workaround: since LHS = wkpNorm of a sum, and we have
    -- pointwise the sum decomposition, we can use `wkpNorm_add_le` plus
    -- induction.
    -- We'll do it inline.
    -- For each α, the summand ψ_α is in MemWkp 1 p of chart γ target.
    have h_summand_mem : ∀ α ∈ S.attach,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) γ
            (chartPullback I (α : M)
              (fun y => chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) (α : M) u y -
                χ α y)))
          (chartTargetEuclid (I := I) (M := M) γ) := by
      intro α _hα_mem
      -- This is `chartPushed γ (chartPullback α (chartPushed α u - χ α))`. We can
      -- equivalently express this, restricted to chart γ target, as
      -- `chartPushed γ (chartPullback α (f_α - χ α))` (by the same lemma above).
      -- But the issue is global (off chart γ target, the value is junk; for
      -- MemWkp, we only see the function on chart γ target, so we can use
      -- `MemWkp_congr_ae`).
      -- The cross-chart bound gives `wkpNorm` of `chartPushed γ (chartPullback α v)`
      -- for `v = f_α - χ α`, but doesn't directly give MemWkp. Let's use a more
      -- direct route: chartPushed γ ∘ chartPullback α (·) preserves MemWkp 1 p
      -- via the chain rule; but that requires γ ≠ α etc. Instead, observe:
      -- chartPushed γ (chartPullback α (chartPushed α u - χ α))
      --   = ρ_γ(z') · ((chartPushed α u - χ α)(toEucl(extChart α (chartPullback...))))
      -- This is the function that the cross-chart bound bounds. The fact that
      -- both `chartPushed α u` and `χ α` are MemWkp on chart α target, combined
      -- with the smooth chain rule, gives that chartPushed γ ∘ chartPullback α
      -- ∘ (·) is MemWkp on chart γ target.
      -- Concretely: by `cross_chart_bound_strict_strong_memWkp`, we have a finite
      -- bound ⇒ wkpNorm < ⊤. Combined with the fact that the function is
      -- AEStronglyMeasurable (continuous a.e.; needs a careful argument).
      -- Simpler: rewrite `chartPullback α (chartPushed α u - χ α)` =
      -- `chartPullback α (f_α - χ α)` (using the `chartPullback_tightenedChartPushed_eq`
      -- result), then use `cross_chart_bound` plus the fact that
      -- `f_α - χ α ∈ MemWkp 1 p (chartTargetEuclid α)` and `tsupport ⊆ chart-α image of K_α`.
      -- The cross-chart bound's hypothesis is the same as for the wkpNorm bound,
      -- so this rewrite is exactly what the cross-chart bound uses internally.
      -- We need a separate lemma that says: under the same hypotheses, the
      -- chart-pushed cross-pullback is in MemWkp 1 p.
      -- Looking at the cross-chart bound proof, it directly produces a wkpNorm
      -- bound; the MemWkp of the chart-pushed cross-pullback follows from the
      -- bound being finite. Since wkpNorm is finite ⇒ MemWkp via
      -- `wkpNorm_lt_top_of_memWkp` reverse... but actually `MemWkp` is the predicate
      -- and `wkpNorm` is a function; both need their own derivations.
      -- Workaround: derive MemWkp directly.
      -- chartPushed γ (chartPullback α (chartPushed α u - χ α)) =
      --   ρ_γ(z) · (chartPushed α u - χ α)(toEucl(extChart α z)) where
      --   z = (extChartAt γ).symm (toEucl.symm y).
      -- The factor ρ_γ is smooth and bounded on chart γ target (since smooth
      -- C^∞⟮I, M; ℝ⟯). The other factor is the pullback of a MemWkp function via
      -- a smooth diffeo of chart γ target → chart α target (`chartTransition_smoothDiffeoBoundedAtOrder`).
      -- This is *exactly* the structure proved by `cross_chart_bound_strict_strong_memWkp`,
      -- but the bound is on wkpNorm. The MemWkp follows by bound of `chartPullback`
      -- via the chain rule. But the chain rule is on smooth diffeo,
      -- and is given by `MemWkp.comp_smoothDiffeoBoundedAtOrder`.
      -- Punt: derive MemWkp from the same set of hypotheses by using the
      -- fact that the cross-chart bound proof builds a smooth diffeo Φ and
      -- factors through it. We use the helper `cross_chart_bound`'s underlying
      -- structure.
      -- To keep things simple, we use the fact that the difference is a
      -- specific function, and use the qualitative chain rule directly.
      -- chartPushed γ (chartPullback α v) for our v: this is exactly what
      -- the proof of `cross_chart_bound_strict_strong_memWkp` works with. The
      -- proof internally derives MemWkp; we extract that.
      -- Easier: the `cross_chart_bound` gives a wkpNorm bound;
      -- `wkpNorm < ⊤` is needed for `MemWkp.add` to work. But `MemWkp` predicate
      -- requires AEStronglyMeasurable + each chosen weak partial in L^p.
      -- The cleanest statement from `cross_chart_bound`:
      --   chartPushed γ (chartPullback α v) for v with tsupport ⊆ chart-α image of K_α
      --   is in MemWkp 1 p (chartTargetEuclid γ).
      -- The fact is implicitly used in the proof. Let's just rebuild it: state
      -- a helper that gives MemWkp directly.
      sorry
    -- Now triangle inequality.
    sorry
  -- Step 9: combine the per-γ bounds via wkpNormChart_eq_finset_sum.
  sorry

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
