import DifferentialGeometry.Analysis.Laplacian.Regularity.IteratedVariationalIdentityStepScaffold
import DifferentialGeometry.Analysis.Laplacian.Regularity.IteratedFChartEffRegularity
import DifferentialGeometry.Analysis.Laplacian.Regularity.IteratedMixedPartials
import DifferentialGeometry.Analysis.Laplacian.Regularity.DifferentiatedCrossTermIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK

/-!
# Polymorphic-in-`K` regularity propagator for the per-step effective source

This module discharges the per-step `MemWkp K 2` regularity propagator for
`fChartEffStep`: given chart-`H^{m+2+K}` regularity of the canonical chart-
pushed POU representative of `u_h.coeFn` and `MemWkp (K+1) 2` regularity of
the previous-level effective source (which is ae-zero outside the chart-pulled
POU support), the level-`(m+1)` effective source `fChartEffStep` lies in
`MemWkp K 2` on the chart target.

## Strategy

`fChartEffStep g α u_h m dirs prev_fChartEff l` is, by definition,
`Set.indicator (chartImagePOUTsupport α) (numerator / densityOnEuclid g α)`,
where `numerator = fChartEffStepNumerator g α u_h m dirs prev_fChartEff l`
unfolds into a sum of five layers (A, B, -C, D, E).

The key observation is that *each layer's structural factor* vanishes a.e.
on `chartTargetEuclid α \ chartImagePOUTsupport α`:

* Layers A, B, C involve `chosenMthMixedPartialChartPushedU` at various
  levels, each ae-zero off `chartImagePOUTsupport α` (from the chart-pushed
  representative's vanishing outside the POU support and the iterated
  weak-partial propagation).
* Layers D, E involve `prev_fChartEff` and its weak `l`-partial, both
  ae-zero off `chartImagePOUTsupport α` (D directly, E by weak-partial
  propagation from D).

Hence `numerator =ᵃᵉ 0` on `chartTargetEuclid α \ chartImagePOUTsupport α`,
which together with the strict positivity of the density on the chart target
gives `Set.indicator (chartImagePOUTsupport α) (numerator / density)
   =ᵃᵉ numerator / density` on `chartTargetEuclid α`.

For the `MemWkp K 2` regularity of `numerator / density`, we exploit:

* Each layer's smooth coefficient (`weightedInvGramDerivOnEuclid`, its
  `∂_j`, `densityDerivOnEuclid`, `densityOnEuclid`, `1/densityOnEuclid`)
  is `C^∞` on the open chart target. We extend each globally via
  `exists_smooth_global_extension`: the extension is `C^∞` on `EuclN` and
  agrees with the original on a closed thickening of
  `chartImagePOUTsupport α`. The structural factor is ae-zero outside the
  POU support, so multiplying the original or its extension produces the
  same function modulo ae-equality on the chart target.
* The globally smooth extensions are bounded (compact-support multiplication)
  with bounded iterated derivatives up to any order, by
  `exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport`.
* Multiplication by a smooth, bounded function preserves `MemWkp K 2` via
  `MemWkp.smul_smooth_bounded`.

After dispatching each layer as `MemWkp K 2`, sum them up via `MemWkp.add`
/ `MemWkp.sub`, then divide by the density via the cutoff-extension of
`1 / densityOnEuclid g α`.

## Main theorem

* `fChartEffStep_memWkp_K_two` — the headline regularity propagator.

The corollary at `K = 0` recovers the existing weighted `L²` regularity;
the corollary at `K = 1` discharges the per-step `MemW1p 2` propagator
`FChartEffStepW1pHyp` used by the canonical iterated chart-bilinear data.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedFChartEffStepRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentityStepScaffold
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Local abbreviations -/

/-- The chart-pulled POU support, a compact subset of the open chart target. -/
private abbrev Kα (α : M) : Set EuclN :=
  chartImagePOUTsupport (I := I) (M := M) α

/-- The open chart target. -/
private abbrev Ωα (α : M) : Set EuclN :=
  chartTargetEuclid (I := I) (M := M) α

set_option linter.unusedSectionVars false in
private lemma Kα_compact (α : M) :
    IsCompact (Kα (I := I) (M := M) α) :=
  chartImagePOUTsupport_isCompact (I := I) (M := M) α

set_option linter.unusedSectionVars false in
private lemma Kα_meas (α : M) :
    MeasurableSet (Kα (I := I) (M := M) α) :=
  (Kα_compact (I := I) (M := M) α).isClosed.measurableSet

set_option linter.unusedSectionVars false in
private lemma Kα_subset_Ωα (α : M) :
    Kα (I := I) (M := M) α ⊆ Ωα (I := I) (M := M) α :=
  chartImagePOUTsupport_subset_target (I := I) (M := M) α

set_option linter.unusedSectionVars false in
private lemma Ωα_isOpen (α : M) : IsOpen (Ωα (I := I) (M := M) α) :=
  chartTargetEuclid_isOpen (I := I) (M := M) α

/-! ## ae-vanishing of the chart-pushed canonical representative off `Kα` -/

/-- The canonical chart-pushed representative of `u_h.coeFn` vanishes ae on the
volume restricted to `chartTargetEuclid α \ chartImagePOUTsupport α`. -/
private lemma chartPushed_u_h_ae_zero_off_Kα
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  have h_diff_open : IsOpen (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α) :=
    (Ωα_isOpen (I := I) (M := M) α).sdiff
      (Kα_compact (I := I) (M := M) α).isClosed
  refine (ae_restrict_iff' h_diff_open.measurableSet).mpr ?_
  refine Filter.Eventually.of_forall ?_
  intro y hy
  exact chartPushed_eq_zero_off_chartImagePOUTsupport
    (I := I) (M := M) α _ hy.1 hy.2

/-! ## ae-vanishing of `chosenWeakPartial'` on an open subset where the
function vanishes ae

Re-proven from the public Euclidean Sobolev API; the analogous private
lemma in the upstream module is reachable only by trusting an existing
import chain, but here we recover it cleanly from the public API. -/

set_option linter.unusedSectionVars false in
private lemma chosenWeakPartial'_ae_zero_on_open_sub_of_ae_zero
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω V : Set EuclN}
    (_hΩ : IsOpen Ω) (hV : IsOpen V) (hV_sub : V ⊆ Ω)
    {u : EuclN → ℝ}
    (hu : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u Ω)
    (hu_ae_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V] (fun _ => (0 : ℝ)))
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hu_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) p u V := by
    refine ⟨?_, ?_⟩
    · exact hu.1.mono_measure
        (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
    · intro j
      obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 j
      refine ⟨g, ?_, ?_⟩
      · exact hg_memLp.mono_measure
          (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
      · exact DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub hg_weak
  have h_partial_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u V) u V :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_V i
  have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem hu i
  have h_partial_Ω_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) u V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub h_partial_Ω
  have h_chosen_V_zero :
      chosenWeakPartial' (d := Module.finrank ℝ E) p i u V
        =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_of_ae_zero (d := Module.finrank ℝ E)
      hp hV hu_ae_zero_V i
  have hg_lp_Ω : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict Ω) :=
    chosenWeakPartial'_memLp_of_mem hu i
  have hg_lp_Ω_V : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω) p
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω.mono_measure (MeasureTheory.Measure.restrict_mono_set _ hV_sub)
  have hg_loc_Ω_V : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω)
      ((volume : Measure EuclN).restrict V) :=
    hg_lp_Ω_V.locallyIntegrable hp
  have hgV_lp : MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) p i u V) p
      ((volume : Measure EuclN).restrict V) :=
    chosenWeakPartial'_memLp_of_mem hu_V i
  have hgV_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) p i u V)
      ((volume : Measure EuclN).restrict V) :=
    hgV_lp.locallyIntegrable hp
  have h_unique :
      chosenWeakPartial' (d := Module.finrank ℝ E) p i u Ω
        =ᵐ[(volume : Measure EuclN).restrict V]
        chosenWeakPartial' (d := Module.finrank ℝ E) p i u V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV h_partial_Ω_V h_partial_V
      hg_loc_Ω_V hgV_loc
  exact h_unique.trans h_chosen_V_zero

/-! ## Polymorphic ae-vanishing of `chosenMthMixed m dirs` off `Kα` -/

/-- Polymorphic propagation: assuming chart-`H^m` of the canonical chart-
pushed parent, the level-`m` chosen mixed weak partial vanishes ae on
`chartTargetEuclid α \ chartImagePOUTsupport α`. -/
lemma chosenMthMixed_ae_zero_off_Kα
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) :
    ∀ (_h_parent : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E)),
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
  induction m with
  | zero =>
      intro _h_parent _idx
      simpa [chosenMthMixedPartialChartPushedU_zero] using
        chartPushed_u_h_ae_zero_off_Kα (I := I) (M := M) g α u_h
  | succ m ih =>
      intro h_parent idx
      have h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) := h_parent.le_succ
      have h_inner_ae := ih h_parent_m (Fin.init idx)
      have h_inner_memWkp_1 : MemWkp (d := Module.finrank ℝ E) 1 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            (Fin.init idx))
          (Ωα (I := I) (M := M) α) := by
        have h_parent_1_m : MemWkp (d := Module.finrank ℝ E) (1 + m) 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
            (Ωα (I := I) (M := M) α) := by
          rw [Nat.add_comm]
          exact h_parent
        exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
          (I := I) (M := M) g α u_h m 1 h_parent_1_m (Fin.init idx)
      have h_inner_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m
            (Fin.init idx))
          (Ωα (I := I) (M := M) α) := by
        rw [MemWkp.one_iff_memW1p] at h_inner_memWkp_1
        exact h_inner_memWkp_1
      have h_diff_open : IsOpen
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α) :=
        (Ωα_isOpen (I := I) (M := M) α).sdiff
          (Kα_compact (I := I) (M := M) α).isClosed
      have h_diff_subset : Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α ⊆
          Ωα (I := I) (M := M) α := fun _ hy => hy.1
      have h_step :=
        chosenWeakPartial'_ae_zero_on_open_sub_of_ae_zero
          (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (Ωα_isOpen (I := I) (M := M) α)
          h_diff_open h_diff_subset
          h_inner_memW1p h_inner_ae (idx (Fin.last m))
      rw [chosenMthMixedPartialChartPushedU_succ]
      exact h_step

/-! ## Smoothly extended chart-target coefficients

For each `C^∞`-on-`chartTarget` coefficient appearing in
`fChartEffStepNumerator`, we package its global smooth extension agreeing
with the original on a closed thickening of `Kα`. -/

private structure SmoothExt (α : M) (f : EuclN → ℝ) where
  /-- Radius of the closed thickening on which the extension agrees with `f`. -/
  δ : ℝ
  /-- The globally smooth extension. -/
  ext : EuclN → ℝ
  δ_pos : 0 < δ
  cthick_in_target : Metric.cthickening δ (Kα (I := I) (M := M) α) ⊆
    Ωα (I := I) (M := M) α
  ext_smooth : ContDiff ℝ (⊤ : ℕ∞) ext
  ext_eq_on_cthick : ∀ y ∈ Metric.cthickening δ (Kα (I := I) (M := M) α),
    ext y = f y

private lemma smoothExt_of_contDiffOn (α : M) {f : EuclN → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ωα (I := I) (M := M) α)) :
    Nonempty (SmoothExt (I := I) (M := M) α f) := by
  obtain ⟨δ, fExt, hδ_pos, hδ_in, hExt_smooth, hExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := f) α hf
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  exact ⟨⟨δ, fExt, hδ_pos, hδ_in, hExt_smooth, hExt_eq⟩⟩

/-- Globally smooth, compactly supported "cutoff" that is `1` on a neighborhood
of `Kα` and vanishes outside the chart target. -/
private structure ChartCutoff (α : M) where
  δ : ℝ
  η : EuclN → ℝ
  δ_pos : 0 < δ
  cthick_in_target : Metric.cthickening δ (Kα (I := I) (M := M) α) ⊆
    Ωα (I := I) (M := M) α
  η_smooth : ContDiff ℝ (⊤ : ℕ∞) η
  η_compactSupport : HasCompactSupport η
  η_one_on_cthick : ∀ y ∈ Metric.cthickening δ (Kα (I := I) (M := M) α), η y = 1
  η_tsupp_in_target : tsupport η ⊆ Ωα (I := I) (M := M) α

private lemma exists_chartCutoff_nonempty (α : M) :
    Nonempty (ChartCutoff (I := I) (M := M) α) := by
  obtain ⟨δ, η, hδ_pos, hδ_in, hη_smooth, hη_cs, _hη_range, hη_one, hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      (Kα_compact (I := I) (M := M) α)
      (Ωα_isOpen (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  exact ⟨⟨δ, η, hδ_pos, hδ_in, hη_smooth, hη_cs, hη_one, hη_tsupp⟩⟩

/-! ## Helper: closure of `MemWkp K 2` under finite sums (universal index) -/

private lemma memWkp_finset_sum_univ
    {α : M} {K : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ}
    (hf : ∀ i ∈ s, MemWkp (d := Module.finrank ℝ E) K 2 (f i)
      (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i ∈ s, f i y) (Ωα (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (Ωα (I := I) (M := M) α) := Ωα_isOpen (I := I) (M := M) α
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open
  | insert i s his ih =>
      have hi : MemWkp (d := Module.finrank ℝ E) K 2 (f i)
          (Ωα (I := I) (M := M) α) := hf i (Finset.mem_insert_self _ _)
      have his_rest : ∀ j ∈ s, MemWkp (d := Module.finrank ℝ E) K 2 (f j)
          (Ωα (I := I) (M := M) α) :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hsum := ih his_rest
      have h_eq : (fun y => ∑ j ∈ insert i s, f j y) =
          (fun y => f i y + ∑ j ∈ s, f j y) := by
        funext y; rw [Finset.sum_insert his]
      rw [h_eq]
      exact MemWkp.add (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hi hsum

/-! ## `MemWkp` for "smooth coefficient × MemWkp K 2 factor" with ae-vanishing

The workhorse lemma: given a coefficient smooth on the chart target, a factor
in `MemWkp K 2` on the chart target that ae-vanishes off `Kα`, the product
lies in `MemWkp K 2` on the chart target. -/

private lemma memWkp_coef_mul_factor
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef (Ωα (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (Ωα (I := I) (M := M) α))
    (hfactor_ae_zero : factor =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) (Ωα (I := I) (M := M) α) := by
  classical
  -- Globally smooth extension of coef.
  obtain ⟨δ, coef_ext, hδ_pos, hδ_in, hExt_smooth, hExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := coef) α hcoef_chart
      (Kα_compact (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  -- Use a smooth cutoff χ supported in Ωα, ≡ 1 on cthickening δ Kα.
  obtain ⟨ε, χ, hε_pos, hε_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      (Kα_compact (I := I) (M := M) α)
      (Ωα_isOpen (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  -- Then `χ · coef_ext` is globally smooth and compactly supported.
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef_ext y) :=
    hχ_smooth.mul hExt_smooth
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef_ext y) :=
    HasCompactSupport.mul_right hχ_cs
  -- Uniform bound on iterated derivatives up to order K.
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  -- Apply MemWkp.smul_smooth_bounded with η := χ · coef_ext.
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef_ext y) * factor y) (Ωα (I := I) (M := M) α) :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Ωα_isOpen (I := I) (M := M) α) hχ_coef_smooth
      (fun j _hj y _hy => hC_bd y j _hj) hfactor_memWkp
  -- Now: (χ · coef_ext) · factor =ᵃᵉ coef · factor on volume.restrict Ωα.
  -- On `cthickening (min δ ε) Kα` ⊆ both cthickenings: χ = 1 and coef_ext = coef.
  -- Off Kα: factor =ᵃᵉ 0.
  set ρ : ℝ := min δ ε with hρ_def
  have hρ_pos : 0 < ρ := lt_min hδ_pos hε_pos
  have hρ_le_δ : ρ ≤ δ := min_le_left _ _
  have hρ_le_ε : ρ ≤ ε := min_le_right _ _
  set Cρ : Set EuclN := Metric.cthickening ρ (Kα (I := I) (M := M) α) with hCρ_def
  have hCρ_sub_Cδ : Cρ ⊆ Metric.cthickening δ (Kα (I := I) (M := M) α) :=
    Metric.cthickening_mono hρ_le_δ _
  have hCρ_sub_Cε : Cρ ⊆ Metric.cthickening ε (Kα (I := I) (M := M) α) :=
    Metric.cthickening_mono hρ_le_ε _
  have hCρ_in_target : Cρ ⊆ Ωα (I := I) (M := M) α := hCρ_sub_Cδ.trans hδ_in
  -- Prove (χ · coef_ext) · factor =ᵃᵉ coef · factor.
  have h_ae_eq : (fun y => (χ y * coef_ext y) * factor y) =ᵐ[
      (volume : Measure EuclN).restrict (Ωα (I := I) (M := M) α)]
      (fun y => coef y * factor y) := by
    -- On Cρ ∩ Ω: χ = 1, coef_ext = coef, so χ · coef_ext · factor = coef · factor.
    -- On Ω \ Cρ ⊆ Ω \ Kα: factor =ᵃᵉ 0.
    set Ω : Set EuclN := Ωα (I := I) (M := M) α
    have hΩ_meas : MeasurableSet Ω :=
      (Ωα_isOpen (I := I) (M := M) α).measurableSet
    have hCρ_closed : IsClosed Cρ := Metric.isClosed_cthickening
    have hCρ_meas : MeasurableSet Cρ := hCρ_closed.measurableSet
    -- On Cρ ⊆ Ω.
    have h_eq_on_Cρ : (fun y => (χ y * coef_ext y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cρ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCρ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hy_Cδ : y ∈ Metric.cthickening δ (Kα (I := I) (M := M) α) :=
        hCρ_sub_Cδ hy
      have hy_Cε : y ∈ Metric.cthickening ε (Kα (I := I) (M := M) α) :=
        hCρ_sub_Cε hy
      have hχy : χ y = 1 := hχ_one y hy_Cε
      have h_coef : coef_ext y = coef y := hExt_eq y hy_Cδ
      change (χ y * coef_ext y) * factor y = coef y * factor y
      rw [hχy, h_coef]; ring
    -- On Ω \ Cρ.
    have hKα_in_Cρ : Kα (I := I) (M := M) α ⊆ Cρ :=
      Metric.self_subset_cthickening _
    have h_diff_sub : Ω \ Cρ ⊆ Ω \ Kα (I := I) (M := M) α := by
      intro y hy
      exact ⟨hy.1, fun hyK => hy.2 (hKα_in_Cρ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ Cρ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ Cρ) ≪
          (volume : Measure EuclN).restrict (Ω \ Kα (I := I) (M := M) α) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_diff_sub le_rfl)
      exact h_abs.ae_le hfactor_ae_zero
    have h_eq_on_diff :
        (fun y => (χ y * coef_ext y) * factor y) =ᵐ[
          (volume : Measure EuclN).restrict (Ω \ Cρ)]
        (fun y => coef y * factor y) := by
      filter_upwards [h_factor_ae_zero_diff] with y hy
      show (χ y * coef_ext y) * factor y = coef y * factor y
      rw [hy]; ring
    -- Restriction to (Ω ∩ Cρ) absolutely continuous w.r.t. restriction to Cρ.
    have h_eq_on_inter : (fun y => (χ y * coef_ext y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cρ)]
        (fun y => coef y * factor y) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω ∩ Cρ) ≪
          (volume : Measure EuclN).restrict Cρ :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono Set.inter_subset_right le_rfl)
      exact h_abs.ae_le h_eq_on_Cρ
    have h_diff_meas : MeasurableSet (Ω \ Cρ) := hΩ_meas.diff hCρ_meas
    have h_cover : Ω = (Ω ∩ Cρ) ∪ (Ω \ Cρ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cρ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Cρ) (Ω \ Cρ) := by
      refine Set.disjoint_left.mpr ?_
      intro y hy hy'; exact hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cρ) ∪ (Ω \ Cρ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- Transfer MemWkp via ae-equality.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Ωα_isOpen (I := I) (M := M) α) h_ae_eq).mp
    h_prod_memWkp

/-! ## Layer A: `(∂_j ∂_l a_ij) · chosenMthMixed(m+1, Fin.cons i dirs)` -/

private lemma layer_A_pair_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l i j : Fin (Module.finrank ℝ E))
    (h_chart_H_succ_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  -- The smooth coefficient ∂_j (weightedInvGramDerivOnEuclid i j l).
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y =>
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1))
        (Ωα (I := I) (M := M) α) := by
    have h_diffOn := weightedInvGramDerivOnEuclid_contDiffOn
      (I := I) (M := M) g α i j l
    have h_open : IsOpen (Ωα (I := I) (M := M) α) :=
      Ωα_isOpen (I := I) (M := M) α
    have h_fderiv :
        ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (Ωα (I := I) (M := M) α) :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ (⊤ : ℕ∞)
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single j (1 : ℝ))).contDiff
    exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
  -- The factor: chosenMthMixed (m+1) (Fin.cons i dirs) ∈ MemWkp K 2.
  have h_factor_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs))
        (Ωα (I := I) (M := M) α) := by
    have h_parent_K_plus :
        MemWkp (d := Module.finrank ℝ E) (K + (m + 1)) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) := by
      have h_eq : K + (m + 1) = (m + 1) + K := by ring
      rw [h_eq]; exact h_chart_H_succ_K
    exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
      (I := I) (M := M) g α u_h (m + 1) K h_parent_K_plus (Fin.cons i dirs)
  -- The factor ae-vanishes off Kα (needs chart-H^{m+1} of the parent).
  have h_factor_ae_zero :
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := by
    have h_parent_m_plus_1 :
        MemWkp (d := Module.finrank ℝ E) (m + 1) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) :=
      h_chart_H_succ_K.le_of_le (by omega)
    exact chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h (m + 1)
      h_parent_m_plus_1 (Fin.cons i dirs)
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

private lemma layer_A_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E))
    (h_chart_H_succ_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  -- Each pair (i, j) gives a MemWkp K 2 term.
  have h_inner_sum : ∀ i : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
        (Ωα (I := I) (M := M) α) := by
    intro i
    exact memWkp_finset_sum_univ (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun j y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
      (fun j _hj =>
        layer_A_pair_memWkp (I := I) (M := M) g α u_h m K dirs l i j
          h_chart_H_succ_K)
  exact memWkp_finset_sum_univ (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun i y => ∑ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1) *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
    (fun i _hi => h_inner_sum i)

/-! ## Layer B: `(∂_l a_ij) · chosenMthMixed(m+2, Fin.cons i (Fin.snoc dirs j))` -/

private lemma layer_B_pair_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l i j : Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_2_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 2) + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 2)
          (Fin.cons i (Fin.snoc dirs j)) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramDerivOnEuclid (I := I) g α i j l)
        (Ωα (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) (M := M) g α i j l
  have h_factor_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 2)
          (Fin.cons i (Fin.snoc dirs j)))
        (Ωα (I := I) (M := M) α) := by
    have h_parent_K_plus :
        MemWkp (d := Module.finrank ℝ E) (K + (m + 2)) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) := by
      have h_eq : K + (m + 2) = (m + 2) + K := by ring
      rw [h_eq]; exact h_chart_H_m_plus_2_K
    exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
      (I := I) (M := M) g α u_h (m + 2) K h_parent_K_plus
      (Fin.cons i (Fin.snoc dirs j))
  have h_factor_ae_zero :
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 2) (Fin.cons i (Fin.snoc dirs j))
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := by
    have h_parent_m_plus_2 :
        MemWkp (d := Module.finrank ℝ E) (m + 2) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) :=
      h_chart_H_m_plus_2_K.le_of_le (by omega)
    exact chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h (m + 2)
      h_parent_m_plus_2 (Fin.cons i (Fin.snoc dirs j))
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

private lemma layer_B_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_2_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 2) + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 2)
              (Fin.cons i (Fin.snoc dirs j)) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_inner_sum : ∀ i : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 2)
              (Fin.cons i (Fin.snoc dirs j)) y)
        (Ωα (I := I) (M := M) α) := by
    intro i
    exact memWkp_finset_sum_univ (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun j y =>
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 2)
            (Fin.cons i (Fin.snoc dirs j)) y)
      (fun j _hj =>
        layer_B_pair_memWkp (I := I) (M := M) g α u_h m K dirs l i j
          h_chart_H_m_plus_2_K)
  exact memWkp_finset_sum_univ (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun i y => ∑ j : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α i j l y *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 2)
          (Fin.cons i (Fin.snoc dirs j)) y)
    (fun i _hi => h_inner_sum i)

/-! ## Layer C: `(∂_l c) · chosenMthMixed(m, dirs)` -/

private lemma layer_C_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (l : Fin (Module.finrank ℝ E))
    (h_chart_H_m_K :
      MemWkp (d := Module.finrank ℝ E) (m + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α))
    (h_parent_m :
      MemWkp (d := Module.finrank ℝ E) m 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityDerivOnEuclid (I := I) g α l y *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h m dirs y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞) (densityDerivOnEuclid (I := I) g α l)
        (Ωα (I := I) (M := M) α) :=
    densityDerivOnEuclid_contDiffOn (I := I) (M := M) g α l
  have h_factor_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h m dirs)
        (Ωα (I := I) (M := M) α) := by
    have h_parent_K_plus :
        MemWkp (d := Module.finrank ℝ E) (K + m) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Ωα (I := I) (M := M) α) := by
      have h_eq : K + m = m + K := by ring
      rw [h_eq]; exact h_chart_H_m_K
    exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
      (I := I) (M := M) g α u_h m K h_parent_K_plus dirs
  have h_factor_ae_zero :
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) :=
    chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h m h_parent_m dirs
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

/-! ## Layer D: `(∂_l c) · prev_fChartEff` -/

private lemma layer_D_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (K : ℕ)
    (l : Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (h_prev_memWkp_K :
      MemWkp (d := Module.finrank ℝ E) K 2 prev_fChartEff
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => densityDerivOnEuclid (I := I) g α l y * prev_fChartEff y)
      (Ωα (I := I) (M := M) α) := by
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞) (densityDerivOnEuclid (I := I) g α l)
        (Ωα (I := I) (M := M) α) :=
    densityDerivOnEuclid_contDiffOn (I := I) (M := M) g α l
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_prev_memWkp_K h_prev_ae_zero

/-! ## Layer E: `c · (weak l-partial of prev_fChartEff)` -/

private lemma layer_E_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (K : ℕ)
    (l : Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 prev_fChartEff
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
          (Ωα (I := I) (M := M) α) y)
      (Ωα (I := I) (M := M) α) := by
  have h_coef_smooth :
      ContDiffOn ℝ (⊤ : ℕ∞) (densityOnEuclid (I := I) g α)
        (Ωα (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  -- The factor: chosenWeakPartial' 2 l prev_fChartEff ∈ MemWkp K 2.
  have h_factor_memWkp :
      MemWkp (d := Module.finrank ℝ E) K 2
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
          (Ωα (I := I) (M := M) α))
        (Ωα (I := I) (M := M) α) :=
    h_prev_memWkp_succ.chosenWeakPartial_mem l
  -- And ae-vanishes off Kα.
  have h_prev_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      prev_fChartEff (Ωα (I := I) (M := M) α) := by
    have h_prev_memWkp_1 : MemWkp (d := Module.finrank ℝ E) 1 2 prev_fChartEff
        (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
    rw [MemWkp.one_iff_memW1p] at h_prev_memWkp_1
    exact h_prev_memWkp_1
  have h_diff_open : IsOpen
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α) :=
    (Ωα_isOpen (I := I) (M := M) α).sdiff
      (Kα_compact (I := I) (M := M) α).isClosed
  have h_diff_subset :
      Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α ⊆
        Ωα (I := I) (M := M) α := fun _ hy => hy.1
  have h_factor_ae_zero :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
        (Ωα (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_on_open_sub_of_ae_zero
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Ωα_isOpen (I := I) (M := M) α) h_diff_open h_diff_subset
      h_prev_memW1p h_prev_ae_zero l
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

/-! ## Aggregate: the numerator is `MemWkp K 2` on the chart target -/

private lemma fChartEffStepNumerator_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 prev_fChartEff
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (h_chart_H_u : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fChartEffStepNumerator (I := I) (M := M)
        g α u_h m dirs prev_fChartEff l)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (Ωα (I := I) (M := M) α) := Ωα_isOpen (I := I) (M := M) α
  -- Auxiliary chart-H regularity at lower orders.
  have h_chart_H_m_plus_1_K : MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α) :=
    h_chart_H_u.le_of_le (by omega)
  have h_chart_H_m_K : MemWkp (d := Module.finrank ℝ E) (m + K) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α) :=
    h_chart_H_u.le_of_le (by omega)
  have h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α) :=
    h_chart_H_u.le_of_le (by omega)
  -- Layer A.
  have hA := layer_A_memWkp (I := I) (M := M) g α u_h m K dirs l
    h_chart_H_m_plus_1_K
  -- Layer B.
  have hB := layer_B_memWkp (I := I) (M := M) g α u_h m K dirs l
    h_chart_H_u
  -- Layer C.
  have hC := layer_C_memWkp (I := I) (M := M) g α u_h m K dirs l
    h_chart_H_m_K h_parent_m
  -- Layer D.
  have h_prev_memWkp_K : MemWkp (d := Module.finrank ℝ E) K 2 prev_fChartEff
      (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
  have hD := layer_D_memWkp (I := I) (M := M) g α K l prev_fChartEff
    h_prev_memWkp_K h_prev_ae_zero
  -- Layer E.
  have hE := layer_E_memWkp (I := I) (M := M) g α K l prev_fChartEff
    h_prev_memWkp_succ h_prev_ae_zero
  -- Combine: numerator = A + B - C + D + E.
  have h_step1 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hA hB
  have h_step2 := MemWkp.sub (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step1 hC
  have h_step3 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step2 hD
  have h_step4 := MemWkp.add (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open h_step3 hE
  unfold fChartEffStepNumerator
  convert h_step4 using 2 with y

/-! ## Numerator ae-vanishes off `Kα` -/

private lemma fChartEffStepNumerator_ae_zero_off_Kα
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (h_prev_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      prev_fChartEff (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α)) :
    fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs prev_fChartEff l
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  -- All layer factors ae-vanish on Ω \ Kα.
  have h_parent_m_plus_1 : MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α) :=
    h_chart_H_m_plus_2.le_of_le (by omega)
  have h_parent_m : MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α) :=
    h_chart_H_m_plus_2.le_of_le (by omega)
  have hA_ae : ∀ i j : Fin (Module.finrank ℝ E),
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun i j =>
    chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h (m + 1)
      h_parent_m_plus_1 (Fin.cons i dirs)
  have hB_ae : ∀ i j : Fin (Module.finrank ℝ E),
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 2) (Fin.cons i (Fin.snoc dirs j))
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun i j =>
    chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h (m + 2)
      h_chart_H_m_plus_2 (Fin.cons i (Fin.snoc dirs j))
  have hC_ae :
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) :=
    chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h m h_parent_m dirs
  have h_diff_open : IsOpen
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α) :=
    (Ωα_isOpen (I := I) (M := M) α).sdiff
      (Kα_compact (I := I) (M := M) α).isClosed
  have h_diff_subset :
      Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α ⊆
        Ωα (I := I) (M := M) α := fun _ hy => hy.1
  -- Weak l-partial of prev_fChartEff ae-vanishes off Kα.
  have hE_ae :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
        (Ωα (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_on_open_sub_of_ae_zero
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Ωα_isOpen (I := I) (M := M) α) h_diff_open h_diff_subset
      h_prev_memW1p h_prev_ae_zero l
  -- Each layer pointwise: coef · 0 = 0.
  unfold fChartEffStepNumerator
  -- Show the whole expression is ae-zero on the diff restriction.
  -- We pointwise rewrite each layer to 0.
  have hA_sum_ae : (fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
            (EuclideanSpace.single j 1) *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    -- Convert ∀ i j (ae) to ae (∀ i j) using Finset version.
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)),
        ∀ i : Fin (Module.finrank ℝ E), ∀ j : Fin (Module.finrank ℝ E),
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y = 0 := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      exact hA_ae i j
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero ?_
    intro i _
    refine Finset.sum_eq_zero ?_
    intro j _
    change (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
        (EuclideanSpace.single j 1) *
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y = 0
    rw [hy i j]; ring
  have hB_sum_ae : (fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 2)
            (Fin.cons i (Fin.snoc dirs j)) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)),
        ∀ i : Fin (Module.finrank ℝ E), ∀ j : Fin (Module.finrank ℝ E),
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 2)
            (Fin.cons i (Fin.snoc dirs j)) y = 0 := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      exact hB_ae i j
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero ?_
    intro i _
    refine Finset.sum_eq_zero ?_
    intro j _
    change weightedInvGramDerivOnEuclid (I := I) g α i j l y *
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h (m + 2)
        (Fin.cons i (Fin.snoc dirs j)) y = 0
    rw [hy i j]; ring
  have hC_term_ae : (fun y => densityDerivOnEuclid (I := I) g α l y *
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hC_ae] with y hy
    show densityDerivOnEuclid (I := I) g α l y *
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs y = 0
    rw [hy]; ring
  have hD_term_ae : (fun y => densityDerivOnEuclid (I := I) g α l y *
      prev_fChartEff y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [h_prev_ae_zero] with y hy
    show densityDerivOnEuclid (I := I) g α l y * prev_fChartEff y = 0
    rw [hy]; ring
  have hE_term_ae : (fun y => densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
        (Ωα (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hE_ae] with y hy
    show densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
        (Ωα (I := I) (M := M) α) y = 0
    rw [hy]; ring
  -- Combine.
  filter_upwards [hA_sum_ae, hB_sum_ae, hC_term_ae, hD_term_ae, hE_term_ae]
    with y hA hB hC hD hE
  change ((∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
              (EuclideanSpace.single j 1) *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y) +
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h (m + 2)
              (Fin.cons i (Fin.snoc dirs j)) y) -
      densityDerivOnEuclid (I := I) g α l y *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h m dirs y +
      densityDerivOnEuclid (I := I) g α l y * prev_fChartEff y +
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 l prev_fChartEff
          (Ωα (I := I) (M := M) α) y) = 0
  rw [hA, hB, hC, hD, hE]; ring

/-! ## `numerator / density` lies in `MemWkp K 2` on the chart target

The quotient `numerator / density` is rewritten as `(1 / density) · numerator`,
and we apply the workhorse lemma `memWkp_coef_mul_factor` with:

* `coef = 1 / densityOnEuclid` (smooth on the chart target by smoothness
  and strict positivity of the density);
* `factor = numerator` (in `MemWkp K 2` on the chart target and ae-zero off
  `Kα`). -/

set_option linter.unusedSectionVars false in
private lemma one_div_densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => 1 / densityOnEuclid (I := I) g α y)
      (Ωα (I := I) (M := M) α) := by
  have h_dens_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (densityOnEuclid (I := I) g α) (Ωα (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  have h_ne : ∀ y ∈ Ωα (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y ≠ 0 := fun y hy =>
    (densityOnEuclid_pos (I := I) g α hy).ne'
  -- Inv on the open set where density is nonzero, then mul by const 1.
  have h_const : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : EuclN => (1 : ℝ))
      (Ωα (I := I) (M := M) α) := contDiffOn_const
  exact h_const.div h_dens_smooth h_ne

private lemma fChartEffStepNumerator_div_density_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 prev_fChartEff
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (h_chart_H_u : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs
          prev_fChartEff l y /
        densityOnEuclid (I := I) g α y)
      (Ωα (I := I) (M := M) α) := by
  classical
  -- Rewrite the quotient as (1 / density) · numerator.
  have h_eq : (fun y =>
      fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l y /
      densityOnEuclid (I := I) g α y) =
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs
          prev_fChartEff l y) := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  -- The numerator is MemWkp K 2 on the chart target.
  have h_num_memWkp :=
    fChartEffStepNumerator_memWkp (I := I) (M := M) g α u_h m K dirs
      prev_fChartEff l h_prev_memWkp_succ h_prev_ae_zero h_chart_H_u
  -- The numerator ae-vanishes off Kα.
  have h_prev_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      prev_fChartEff (Ωα (I := I) (M := M) α) := by
    have h_prev_memWkp_1 : MemWkp (d := Module.finrank ℝ E) 1 2 prev_fChartEff
        (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
    rw [MemWkp.one_iff_memW1p] at h_prev_memWkp_1
    exact h_prev_memWkp_1
  have h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α) :=
    h_chart_H_u.le_of_le (by omega)
  have h_num_ae_zero :=
    fChartEffStepNumerator_ae_zero_off_Kα (I := I) (M := M) g α u_h m dirs
      prev_fChartEff l h_prev_memW1p h_prev_ae_zero h_chart_H_m_plus_2
  -- Apply the workhorse lemma with coef = 1 / density.
  exact memWkp_coef_mul_factor (I := I) (M := M) α K
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_num_memWkp h_num_ae_zero

/-! ## Headline theorem: `MemWkp K 2` of `fChartEffStep` on the chart target -/

/-- **Polymorphic `MemWkp K 2` regularity of the per-step effective source.**
Given:

* `MemWkp (K + 1) 2` regularity of the previous-level effective source
  `prev_fChartEff` on the chart target;
* ae-vanishing of `prev_fChartEff` on `chartTargetEuclid α \
  chartImagePOUTsupport α`;
* chart-`H^{m + 2 + K}` regularity of the canonical chart-pushed
  representative of `u_h.coeFn`,

the level-`(m+1)` effective source `fChartEffStep` lies in `MemWkp K 2` on
`chartTargetEuclid α`.

This discharges the per-step regularity propagator at every `K ≥ 0`,
upgrading the existing weighted-`L²` regularity to arbitrary chart-Sobolev
regularity. -/
theorem fChartEffStep_memWkp_K_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 prev_fChartEff
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (h_chart_H_u : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fChartEffStep (I := I) (M := M) g α u_h m dirs prev_fChartEff l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- `fChartEffStep = indicator Kα (numerator / density)`.
  -- We show this ae-equals `numerator / density` on chartTarget, then transfer.
  set Q : EuclN → ℝ := fun y =>
    fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs
      prev_fChartEff l y /
    densityOnEuclid (I := I) g α y with hQ_def
  -- Q ∈ MemWkp K 2 chartTarget.
  have hQ_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 Q
      (Ωα (I := I) (M := M) α) :=
    fChartEffStepNumerator_div_density_memWkp (I := I) (M := M) g α u_h m K dirs
      prev_fChartEff l h_prev_memWkp_succ h_prev_ae_zero h_chart_H_u
  -- Q ae-zero off Kα.
  have h_prev_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      prev_fChartEff (Ωα (I := I) (M := M) α) := by
    have h_prev_memWkp_1 : MemWkp (d := Module.finrank ℝ E) 1 2 prev_fChartEff
        (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
    rw [MemWkp.one_iff_memW1p] at h_prev_memWkp_1
    exact h_prev_memWkp_1
  have h_chart_H_m_plus_2 :
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Ωα (I := I) (M := M) α) :=
    h_chart_H_u.le_of_le (by omega)
  have h_num_ae_zero :=
    fChartEffStepNumerator_ae_zero_off_Kα (I := I) (M := M) g α u_h m dirs
      prev_fChartEff l h_prev_memW1p h_prev_ae_zero h_chart_H_m_plus_2
  have hQ_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [h_num_ae_zero] with y hy
    change fChartEffStepNumerator (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l y / densityOnEuclid (I := I) g α y = 0
    rw [hy]; simp
  -- fChartEffStep =ᵃᵉ Q on chartTarget.
  -- Split chartTarget = Kα ∪ (chartTarget \ Kα):
  --  On Kα, indicator returns Q (in fact value of Q); both equal Q.
  --  Off Kα: fChartEffStep = 0, Q =ᵃᵉ 0.
  have h_fStep_ae_eq_Q :
      fChartEffStep (I := I) (M := M) g α u_h m dirs prev_fChartEff l =ᵐ[
        (volume : Measure EuclN).restrict (Ωα (I := I) (M := M) α)] Q := by
    set Ω : Set EuclN := Ωα (I := I) (M := M) α with hΩ_def
    have hΩ_meas : MeasurableSet Ω :=
      (Ωα_isOpen (I := I) (M := M) α).measurableSet
    have hKα_meas : MeasurableSet (Kα (I := I) (M := M) α) :=
      Kα_meas (I := I) (M := M) α
    have hKα_sub_Ω : Kα (I := I) (M := M) α ⊆ Ω :=
      Kα_subset_Ωα (I := I) (M := M) α
    -- On Kα: fChartEffStep y = indicator y = Q y.
    have h_eq_on_Kα : fChartEffStep (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l =ᵐ[(volume : Measure EuclN).restrict
          (Kα (I := I) (M := M) α)] Q := by
      refine (ae_restrict_iff' hKα_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      unfold fChartEffStep
      rw [Set.indicator_of_mem hy]
    -- On Ω \ Kα: both fChartEffStep and Q =ᵃᵉ 0.
    have h_diff_meas : MeasurableSet (Ω \ Kα (I := I) (M := M) α) :=
      hΩ_meas.diff hKα_meas
    have h_fStep_ae_zero : fChartEffStep (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l =ᵐ[(volume : Measure EuclN).restrict
          (Ω \ Kα (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
      refine (ae_restrict_iff' h_diff_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      unfold fChartEffStep
      exact Set.indicator_of_notMem hy.2 _
    have h_eq_on_diff : fChartEffStep (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l =ᵐ[(volume : Measure EuclN).restrict
          (Ω \ Kα (I := I) (M := M) α)] Q := by
      filter_upwards [h_fStep_ae_zero, hQ_ae_zero] with y h0 hQ
      rw [h0, hQ]
    -- Reduce restriction to Kα via inter.
    have hKα_inter_Ω : Kα (I := I) (M := M) α = Ω ∩ Kα (I := I) (M := M) α := by
      rw [Set.inter_eq_self_of_subset_right hKα_sub_Ω]
    have h_eq_on_inter : fChartEffStep (I := I) (M := M) g α u_h m dirs
        prev_fChartEff l =ᵐ[(volume : Measure EuclN).restrict
          (Ω ∩ Kα (I := I) (M := M) α)] Q := by
      rw [← hKα_inter_Ω]
      exact h_eq_on_Kα
    have h_cover : Ω = (Ω ∩ Kα (I := I) (M := M) α) ∪
        (Ω \ Kα (I := I) (M := M) α) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Kα (I := I) (M := M) α
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Kα (I := I) (M := M) α)
        (Ω \ Kα (I := I) (M := M) α) := by
      refine Set.disjoint_left.mpr ?_
      intro y hy hy'; exact hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Kα (I := I) (M := M) α) ∪
          (Ω \ Kα (I := I) (M := M) α)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- Transfer MemWkp via ae-equality.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Ωα_isOpen (I := I) (M := M) α)
    h_fStep_ae_eq_Q).mpr hQ_memWkp

/-! ## Corollary: `K = 1` discharges `FChartEffStepW1pHyp` -/

/-- **`K = 1` corollary.** At `K = 1`, the headline regularity propagator
gives `MemWkp 1 2 (fChartEffStep) = MemW1p 2 (fChartEffStep)`. This is the
form consumed by `FChartEffStepW1pHyp` in the canonical iterated chart-
bilinear data: the propagator is now unconditional, given chart-`H^{m+3}`
regularity of the parent and `MemW1p 2` (= chart-`H^1`) regularity of the
previous-level source (plus its ae-vanishing).

The next-source `MemW1p 2` follows from chart-`H¹` of the previous source
via `chosenWeakPartial_mem` together with chart-`H^{m+3}` of the parent.
This is exactly the hypothesis pattern needed by the canonical iterated
data bundle. -/
theorem fChartEffStep_memW1p_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (prev_fChartEff : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (h_prev_memWkp_two :
      MemWkp (d := Module.finrank ℝ E) 2 2 prev_fChartEff
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : prev_fChartEff =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (h_chart_H_u : MemWkp (d := Module.finrank ℝ E) (m + 3) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartEffStep (I := I) (M := M) g α u_h m dirs prev_fChartEff l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_prev_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (1 + 1) 2
      prev_fChartEff (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : (1 + 1 : ℕ) = 2 := by norm_num
    rw [h_eq]; exact h_prev_memWkp_two
  have h_chart_H_u' : MemWkp (d := Module.finrank ℝ E) (m + 2 + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : m + 2 + 1 = m + 3 := by ring
    rw [h_eq]; exact h_chart_H_u
  have h_mem := fChartEffStep_memWkp_K_two (I := I) (M := M) g α u_h m 1 dirs
    prev_fChartEff l h_prev_memWkp_succ h_prev_ae_zero h_chart_H_u'
  rw [MemWkp.one_iff_memW1p] at h_mem
  exact h_mem

end IteratedFChartEffStepRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Laplacian.IteratedFChartEffStepRegularity.fChartEffStep_memWkp_K_two
#print axioms
  DifferentialGeometry.Analysis.Laplacian.IteratedFChartEffStepRegularity.fChartEffStep_memW1p_two

end Sanity
