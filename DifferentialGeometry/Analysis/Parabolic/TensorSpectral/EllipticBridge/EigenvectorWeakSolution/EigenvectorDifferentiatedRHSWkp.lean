import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedScaffold
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK

/-!
# Polymorphic-in-`K` `W^{k,2}` regularity of the differentiated numerator

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the level-`m`
differentiated numerator `eigenvectorChartRHSDiffNumerator` of the eigenvector
chart variational identity is the explicit five-layer Leibniz combination
`A + B − C + D + E` (built in `EigenvectorDifferentiatedRHS`). This module
discharges its polymorphic `W^{k,2}` regularity: for each `K : ℕ`, given

* `MemWkp` of sufficiently high order of the eigenvector chart component, and
* `MemWkp (K + 1) 2` of the level-`m` differentiated right-hand side
  `fChartEffPrev` (which is ae-zero off the partition-of-unity kernel
  `chartPouKernel α`),

the numerator lies in `MemWkp K 2` on the open chart target, and so does the
chart-density-divided numerator `numerator / densityOnEuclid g α`.

## Strategy

`eigenvectorChartRHSDiffNumerator g r s h_uniform i α P₀ m l fChartEffPrev`
unfolds into five layers:

* layers A, B, C carry the recursive `m`-fold mixed weak partials
  `eigenvectorChartIteratedPartial` at levels `m + 1` / `m`, each `MemWkp K 2`
  by the polymorphic regularity bridge
  `eigenvectorChartIteratedPartial_memWkp_of_memWkp` and ae-zero off
  `chartPouKernel α` by `eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel`;
* layers D, E carry `fChartEffPrev` and its chosen weak `lₙ`-partial — `D`
  directly, `E` via the inductive-hypothesis `MemWkp (K + 1) 2` and
  `MemWkp.chosenWeakPartial_mem` — both ae-zero off `chartPouKernel α`.

Each layer is one such `MemWkp K 2` factor (ae-zero off `chartPouKernel α`)
multiplied by a smooth chart-target coefficient (`∂_b weightedInvGramDerivOnEuclid`,
`weightedInvGramDerivOnEuclid`, `densityDerivOnEuclid`, `densityOnEuclid`, and
the reciprocal `1 / densityOnEuclid`). The workhorse `memWkp_coef_mul_factor`
glues a smooth coefficient to such a factor: it cuts the coefficient off into a
globally smooth, compactly supported representative agreeing with it on a
neighbourhood of the kernel, uniformly bounds its iterated derivatives via
`exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport`, multiplies via
`MemWkp.smul_smooth_bounded`, and transfers the result back through the
ae-vanishing of the factor outside the kernel.

Summing the five layers with `MemWkp.add` / `MemWkp.sub` gives the numerator;
rewriting `numerator / density` as `(1 / density) · numerator` and applying the
workhorse once more gives the divided numerator.

## Main results

* `eigenvectorChartRHSDiffNumerator_memWkp` — the differentiated numerator is
  `MemWkp K 2` on the chart target.
* `eigenvectorChartRHSDiffNumerator_div_density_memWkp` — the chart-density-
  divided differentiated numerator is `MemWkp K 2` on the chart target.

These are intermediate campaign lemmas: the iterated-regularity bootstrap of the
level-`(m+1)` differentiated right-hand side consumes them.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Local abbreviations for the chart target and the partition-of-unity kernel

`Ωα α` is the open Euclidean chart target; `Kα α` is the compact
partition-of-unity kernel `chartPouKernel α`, a closed subset of `Ωα α`. The
factors of the differentiated numerator are `MemWkp K 2` on `Ωα α` and ae-zero
on `Ωα α \ Kα α`. -/

/-- The compact partition-of-unity kernel `chartPouKernel α`, a closed subset of
the open chart target. -/
private abbrev Kα (α : M) : Set EuclN :=
  chartPouKernel (I := I) (M := M) α

/-- The open Euclidean chart target. -/
private abbrev Ωα (α : M) : Set EuclN :=
  chartTargetEuclid (I := I) (M := M) α

set_option linter.unusedSectionVars false in
private lemma Kα_compact (α : M) : IsCompact (Kα (I := I) (M := M) α) :=
  chartPouKernel_isCompact (I := I) (M := M) α

set_option linter.unusedSectionVars false in
private lemma Kα_meas (α : M) : MeasurableSet (Kα (I := I) (M := M) α) :=
  chartPouKernel_measurableSet (I := I) (M := M) α

set_option linter.unusedSectionVars false in
private lemma Kα_subset_Ωα (α : M) :
    Kα (I := I) (M := M) α ⊆ Ωα (I := I) (M := M) α :=
  chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α

set_option linter.unusedSectionVars false in
private lemma Ωα_isOpen (α : M) : IsOpen (Ωα (I := I) (M := M) α) :=
  chartTargetEuclid_isOpen (I := I) (M := M) α

/-! ## `MemWkp` for "smooth coefficient × `MemWkp K 2` factor" with ae-vanishing

The workhorse lemma. Given a coefficient smooth on the open chart target, a
factor in `MemWkp K 2` on the chart target that ae-vanishes off the compact
partition-of-unity kernel `Kα`, the product lies in `MemWkp K 2` on the chart
target.

The proof cuts the coefficient off to a globally smooth, compactly supported
representative `χ · coef`: a smooth cutoff `χ` equal to `1` on a closed
thickening of `Kα` and supported in the chart target. The product `χ · coef` is
globally smooth (smooth on `tsupport χ ⊆ Ωα`, identically zero off `tsupport χ`)
and compactly supported. Its iterated derivatives up to order `K` are uniformly
bounded, so `MemWkp.smul_smooth_bounded` keeps `MemWkp K 2`. Finally
`(χ · coef) · factor =ᵐ coef · factor` on `volume.restrict Ωα`: on the thickening
`χ = 1`; off `Kα` the factor ae-vanishes. -/

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
  -- A smooth cutoff `χ` equal to `1` on `cthickening δ Kα`, supported in `Ωα`.
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      (Kα_compact (I := I) (M := M) α)
      (Ωα_isOpen (I := I) (M := M) α)
      (Kα_subset_Ωα (I := I) (M := M) α)
  -- `χ · coef` is globally smooth: smooth on `tsupport χ ⊆ Ωα`, identically zero
  -- (hence smooth) on the open complement of `tsupport χ`.
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_chart : IsOpen (Ωα (I := I) (M := M) α) :=
      Ωα_isOpen (I := I) (M := M) α
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ Ωα (I := I) (M := M) α := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (h_open_chart.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  -- Uniform bound on the iterated derivatives of `χ · coef` up to order `K`.
  obtain ⟨C, _hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  -- `(χ · coef) · factor ∈ MemWkp K 2` via `MemWkp.smul_smooth_bounded`.
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) (Ωα (I := I) (M := M) α) :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Ωα_isOpen (I := I) (M := M) α) hχ_coef_smooth
      (fun j _hj y _hy => hC_bd y j _hj) hfactor_memWkp
  -- `(χ · coef) · factor =ᵃᵉ coef · factor` on `volume.restrict Ωα`.
  set Cδ : Set EuclN := Metric.cthickening δ (Kα (I := I) (M := M) α)
    with hCδ_def
  have hCδ_in_target : Cδ ⊆ Ωα (I := I) (M := M) α := hδ_in
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ωα (I := I) (M := M) α)]
      (fun y => coef y * factor y) := by
    set Ω : Set EuclN := Ωα (I := I) (M := M) α with hΩ_def
    have hΩ_meas : MeasurableSet Ω :=
      (Ωα_isOpen (I := I) (M := M) α).measurableSet
    have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
    have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
    -- On `Cδ ⊆ Ω`: `χ = 1`, so `(χ · coef) · factor = coef · factor`.
    have h_eq_on_Cδ : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict Cδ]
        (fun y => coef y * factor y) := by
      refine (ae_restrict_iff' hCδ_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hχy : χ y = 1 := hχ_one y hy
      change (χ y * coef y) * factor y = coef y * factor y
      rw [hχy]; ring
    -- On `Ω \ Cδ ⊆ Ω \ Kα`: `factor` ae-vanishes.
    have hKα_in_Cδ : Kα (I := I) (M := M) α ⊆ Cδ :=
      Metric.self_subset_cthickening _
    have h_diff_sub : Ω \ Cδ ⊆ Ω \ Kα (I := I) (M := M) α := fun y hy =>
      ⟨hy.1, fun hyK => hy.2 (hKα_in_Cδ hyK)⟩
    have h_factor_ae_zero_diff : factor =ᵐ[(volume : Measure EuclN).restrict
        (Ω \ Cδ)] (fun _ => (0 : ℝ)) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω \ Cδ) ≪
          (volume : Measure EuclN).restrict (Ω \ Kα (I := I) (M := M) α) :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono h_diff_sub le_rfl)
      exact h_abs.ae_le hfactor_ae_zero
    have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
        (fun y => coef y * factor y) := by
      filter_upwards [h_factor_ae_zero_diff] with y hy
      show (χ y * coef y) * factor y = coef y * factor y
      rw [hy]; ring
    have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
        =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
        (fun y => coef y * factor y) := by
      have h_abs : (volume : Measure EuclN).restrict (Ω ∩ Cδ) ≪
          (volume : Measure EuclN).restrict Cδ :=
        MeasureTheory.Measure.absolutelyContinuous_of_le
          (MeasureTheory.Measure.restrict_mono Set.inter_subset_right le_rfl)
      exact h_abs.ae_le h_eq_on_Cδ
    have h_diff_meas : MeasurableSet (Ω \ Cδ) := hΩ_meas.diff hCδ_meas
    have h_cover : Ω = (Ω ∩ Cδ) ∪ (Ω \ Cδ) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Cδ
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Cδ) (Ω \ Cδ) :=
      Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- Transfer `MemWkp K 2` through the ae-equality.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Ωα_isOpen (I := I) (M := M) α) h_ae_eq).mp
    h_prod_memWkp

/-! ## Helper: closure of `MemWkp K 2` under finite sums (universal index)

The differentiated numerator's layers A and B are finite double sums. The helper
below propagates `MemWkp K 2` through a finite sum indexed by an arbitrary
`Finset`. -/

private lemma memWkp_finset_sum
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
      have hsum := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have h_eq : (fun y => ∑ j ∈ insert i s, f j y) =
          (fun y => f i y + ∑ j ∈ s, f j y) := by
        funext y; rw [Finset.sum_insert his]
      rw [h_eq]
      exact MemWkp.add (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open hi hsum

/-! ## ae-vanishing of the iterated mixed partials off the kernel, restated

The iterated mixed weak partials of the eigenvector chart component are ae-zero
on `Ωα α \ Kα α`; the lemma `eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel`
already establishes this, restated here against the local abbreviations. -/

omit [CompleteSpace E] in
private lemma iteratedPartial_ae_zero_off_Kα
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_uniform i α P₀ m l
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) :=
  eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s h_uniform i α P₀ m l

/-! ## Layer A: `(∂_b ∂_{lₙ} a_ab) · ((m+1)-fold mixed partial, `Fin.cons a (Fin.init l)`)`

Layer A is the `∂_b`-partial of the Leibniz cross-coefficient against the
level-`(m+1)` mixed weak partial of the chart component. The coefficient is
`C^∞` on the chart target; the factor is `MemWkp K 2` (from chart-`H^{(m+1)+K}`
regularity of the component) and ae-zero off the kernel. -/

private lemma layer_A_pair_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (a b : Fin (Module.finrank ℝ E))
    (h_comp_succ_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_uniform i α P₀
          (m + 1) (Fin.cons a (Fin.init l)) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  -- The smooth coefficient `∂_b (weightedInvGramDerivOnEuclid · · ·)`.
  have h_coef_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1))
      (Ωα (I := I) (M := M) α) := by
    have h_open : IsOpen (Ωα (I := I) (M := M) α) :=
      Ωα_isOpen (I := I) (M := M) α
    have h_diffOn : ContDiffOn ℝ (⊤ : ℕ∞)
        (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
        (Ωα (I := I) (M := M) α) :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
    have h_fderiv : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
        (Ωα (I := I) (M := M) α) :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ (⊤ : ℕ∞)
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
    exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
  -- The factor `iteratedPartial (m+1) (Fin.cons a (Fin.init l)) ∈ MemWkp K 2`.
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
      (Ωα (I := I) (M := M) α) := by
    have h_comp_K_plus : MemWkp (d := Module.finrank ℝ E) (K + (m + 1)) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
        (Ωα (I := I) (M := M) α) := by
      have h_eq : K + (m + 1) = (m + 1) + K := by ring
      rw [h_eq]; exact h_comp_succ_K
    exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s h_uniform i α P₀ (m + 1) K h_comp_K_plus
      (Fin.cons a (Fin.init l))
  -- The factor ae-vanishes off `Kα`.
  have h_factor_ae_zero := iteratedPartial_ae_zero_off_Kα
    (I := I) (M := M) g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

private lemma layer_A_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (h_comp_succ_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
        (Ωα (I := I) (M := M) α) := by
    intro a
    exact memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      (fun b _hb => layer_A_pair_memWkp (I := I) (M := M)
        g r s h_uniform i α P₀ m K l a b h_comp_succ_K)
  exact memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
    (fun a _ha => h_inner a)

/-! ## Layer B: `(∂_{lₙ} a_ab) · (∂_b-weak-partial of the `(m+1)`-fold mixed partial)`

Layer B carries the highest derivative. The factor `∂_b-weak-partial of the
`(m+1)`-fold mixed partial` is the chosen weak `b`-partial of the level-`(m+1)`
mixed partial: by `MemWkp.chosenWeakPartial_mem` it is `MemWkp K 2` once the
level-`(m+1)` mixed partial is `MemWkp (K + 1) 2`, which holds from
chart-`H^{(m+2)+K}` regularity of the component. The chosen weak partial
ae-vanishes off the kernel because the level-`(m+1)` mixed partial does, by
`chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero`. -/

private lemma layer_B_pair_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (a b : Fin (Module.finrank ℝ E))
    (h_comp_m_plus_2_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 2) + K) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (Ωα (I := I) (M := M) α) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_coef_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
      (Ωα (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
  -- The level-`(m+1)` mixed partial lies in `MemWkp (K + 1) 2`.
  have h_inner_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
      (Ωα (I := I) (M := M) α) := by
    have h_comp_K_plus : MemWkp (d := Module.finrank ℝ E) ((K + 1) + (m + 1)) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
        (Ωα (I := I) (M := M) α) := by
      have h_eq : (K + 1) + (m + 1) = (m + 2) + K := by ring
      rw [h_eq]; exact h_comp_m_plus_2_K
    exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s h_uniform i α P₀ (m + 1) (K + 1) h_comp_K_plus
      (Fin.cons a (Fin.init l))
  -- The chosen weak `b`-partial of it is `MemWkp K 2`.
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (Ωα (I := I) (M := M) α))
      (Ωα (I := I) (M := M) α) :=
    h_inner_memWkp_succ.chosenWeakPartial_mem b
  -- The chosen weak `b`-partial ae-vanishes off `Kα`.
  have h_inner_ae := iteratedPartial_ae_zero_off_Kα
    (I := I) (M := M) g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  have h_factor_ae_zero :=
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α h_inner_ae b
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

private lemma layer_B_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (h_comp_m_plus_2_K :
      MemWkp (d := Module.finrank ℝ E) ((m + 2) + K) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (Ωα (I := I) (M := M) α) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_inner : ∀ a : Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ∑ b : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
            chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (Ωα (I := I) (M := M) α) y)
        (Ωα (I := I) (M := M) α) := by
    intro a
    exact memWkp_finset_sum (I := I) (M := M)
      (α := α) (K := K) (s := Finset.univ)
      (f := fun b y =>
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (Ωα (I := I) (M := M) α) y)
      (fun b _hb => layer_B_pair_memWkp (I := I) (M := M)
        g r s h_uniform i α P₀ m K l a b h_comp_m_plus_2_K)
  exact memWkp_finset_sum (I := I) (M := M)
    (α := α) (K := K) (s := Finset.univ)
    (f := fun a y => ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (Ωα (I := I) (M := M) α) y)
    (fun a _ha => h_inner a)

/-! ## Layer C: `(∂_{lₙ} c) · (m-fold mixed partial in `Fin.init l`)`

Layer C is the zeroth-order Leibniz term. The coefficient `densityDerivOnEuclid`
is `C^∞`; the factor is the level-`m` mixed weak partial, `MemWkp K 2` from
chart-`H^{m+K}` regularity of the component, ae-zero off the kernel. -/

private lemma layer_C_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (h_comp_m_K :
      MemWkp (d := Module.finrank ℝ E) (m + K) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
        (Ωα (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        eigenvectorChartIteratedPartial (I := I) (M := M) g r s h_uniform i α P₀
          m (Fin.init l) y)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_coef_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (densityDerivOnEuclid (I := I) g α (l (Fin.last m)))
      (Ωα (I := I) (M := M) α) :=
    densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m))
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_uniform i α P₀ m (Fin.init l))
      (Ωα (I := I) (M := M) α) := by
    have h_comp_K_plus : MemWkp (d := Module.finrank ℝ E) (K + m) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
        (Ωα (I := I) (M := M) α) := by
      have h_eq : K + m = m + K := by ring
      rw [h_eq]; exact h_comp_m_K
    exact eigenvectorChartIteratedPartial_memWkp_of_memWkp
      (I := I) (M := M) g r s h_uniform i α P₀ m K h_comp_K_plus (Fin.init l)
  have h_factor_ae_zero := iteratedPartial_ae_zero_off_Kα
    (I := I) (M := M) g r s h_uniform i α P₀ m (Fin.init l)
  exact memWkp_coef_mul_factor (I := I) (M := M) α K h_coef_smooth
    h_factor_memWkp h_factor_ae_zero

/-! ## Layer D: `(∂_{lₙ} c) · fChartEffPrev`

Layer D multiplies the smooth `densityDerivOnEuclid` coefficient by the
level-`m` differentiated right-hand side `fChartEffPrev`, which is `MemWkp K 2`
(by inductive hypothesis) and ae-zero off the kernel. -/

private lemma layer_D_memWkp
    (g : SmoothRiemannianMetric I M) (α : M) (K : ℕ)
    (lₙ : Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_memWkp_K :
      MemWkp (d := Module.finrank ℝ E) K 2 fChartEffPrev
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => densityDerivOnEuclid (I := I) g α lₙ y * fChartEffPrev y)
      (Ωα (I := I) (M := M) α) :=
  memWkp_coef_mul_factor (I := I) (M := M) α K
    (densityDerivOnEuclid_contDiffOn (I := I) g α lₙ)
    h_prev_memWkp_K h_prev_ae_zero

/-! ## Layer E: `c · (∂_{lₙ}-weak-partial of fChartEffPrev)`

Layer E multiplies the smooth `densityOnEuclid` coefficient by the chosen weak
`lₙ`-partial of `fChartEffPrev`. The factor is `MemWkp K 2` by
`MemWkp.chosenWeakPartial_mem` (from `MemWkp (K + 1) 2` of `fChartEffPrev`) and
ae-zero off the kernel by `chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero`. -/

private lemma layer_E_memWkp
    (g : SmoothRiemannianMetric I M) (α : M) (K : ℕ)
    (lₙ : Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 lₙ
          fChartEffPrev (Ωα (I := I) (M := M) α) y)
      (Ωα (I := I) (M := M) α) := by
  -- The chosen weak `lₙ`-partial of `fChartEffPrev` is `MemWkp K 2`.
  have h_factor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 lₙ
        fChartEffPrev (Ωα (I := I) (M := M) α))
      (Ωα (I := I) (M := M) α) :=
    h_prev_memWkp_succ.chosenWeakPartial_mem lₙ
  -- The chosen weak `lₙ`-partial ae-vanishes off `Kα`.
  have h_factor_ae_zero :=
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α h_prev_ae_zero lₙ
  exact memWkp_coef_mul_factor (I := I) (M := M) α K
    (densityOnEuclid_contDiffOn (I := I) g α)
    h_factor_memWkp h_factor_ae_zero

/-! ## Aggregate: the differentiated numerator is `MemWkp K 2` on the chart target

Summing the five layers via `MemWkp.add` / `MemWkp.sub` gives the differentiated
numerator. The hypothesis index arithmetic mirrors the scalar campaign exactly:
the component is required in `MemWkp (m + 2 + K) 2` — layer A consumes
`(m + 1) + K`, layer B consumes `(m + 2) + K`, layer C consumes `m + K`, all
extracted by `MemWkp.le_of_le`. -/

/-- **The level-`m` differentiated numerator is `MemWkp K 2` on the chart
target.** Given `MemWkp (m + 2 + K) 2` of the eigenvector chart component,
`MemWkp (K + 1) 2` of the level-`m` differentiated right-hand side
`fChartEffPrev` (ae-zero off `chartPouKernel α`), each of the five layers of
`eigenvectorChartRHSDiffNumerator` lies in `MemWkp K 2` on the chart target, so
the assembled numerator does.

This is an intermediate campaign lemma — the eigenvector/tensor analogue of the
scalar campaign's `fChartEffStepNumerator_memWkp`. -/
lemma eigenvectorChartRHSDiffNumerator_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
      (Ωα (I := I) (M := M) α))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s h_uniform i α P₀ m l fChartEffPrev)
      (Ωα (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (Ωα (I := I) (M := M) α) := Ωα_isOpen (I := I) (M := M) α
  -- Lower-order chart-`H` regularity of the component.
  have h_comp_succ_K : MemWkp (d := Module.finrank ℝ E) ((m + 1) + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
      (Ωα (I := I) (M := M) α) :=
    h_comp.le_of_le (by omega)
  have h_comp_m_K : MemWkp (d := Module.finrank ℝ E) (m + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
      (Ωα (I := I) (M := M) α) :=
    h_comp.le_of_le (by omega)
  have h_comp_m_plus_2_K : MemWkp (d := Module.finrank ℝ E) ((m + 2) + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
      (Ωα (I := I) (M := M) α) :=
    h_comp.le_of_le (by omega)
  -- Layer A.
  have hA := layer_A_memWkp (I := I) (M := M) g r s h_uniform i α P₀ m K l
    h_comp_succ_K
  -- Layer B.
  have hB := layer_B_memWkp (I := I) (M := M) g r s h_uniform i α P₀ m K l
    h_comp_m_plus_2_K
  -- Layer C.
  have hC := layer_C_memWkp (I := I) (M := M) g r s h_uniform i α P₀ m K l
    h_comp_m_K
  -- Layer D.
  have h_prev_memWkp_K : MemWkp (d := Module.finrank ℝ E) K 2 fChartEffPrev
      (Ωα (I := I) (M := M) α) := h_prev_memWkp_succ.le_of_le (by omega)
  have hD := layer_D_memWkp (I := I) (M := M) g α K (l (Fin.last m))
    h_prev_memWkp_K h_prev_ae_zero
  -- Layer E.
  have hE := layer_E_memWkp (I := I) (M := M) g α K (l (Fin.last m))
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
  -- The assembled sum is definitionally the numerator.
  have h_eq : (fun y =>
      ((((∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
                (l (Fin.last m))) y)
              (EuclideanSpace.single b 1) *
            eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) +
        (∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
            weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
              chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (Ωα (I := I) (M := M) α) y)) -
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_uniform i α P₀ m (Fin.init l) y) +
        densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
          fChartEffPrev y) +
        densityOnEuclid (I := I) g α y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            fChartEffPrev (Ωα (I := I) (M := M) α) y) =
      eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s h_uniform i α P₀ m l fChartEffPrev := by
    funext y
    rfl
  rw [← h_eq]
  exact h_step4

/-! ## `numerator / density` lies in `MemWkp K 2` on the chart target

The chart-density-divided numerator `numerator / densityOnEuclid g α` is
rewritten as `(1 / densityOnEuclid g α) · numerator` and handed to the workhorse
`memWkp_coef_mul_factor`: the reciprocal `1 / densityOnEuclid g α` is `C^∞` on
the chart target (smoothness and strict positivity of the density), and the
numerator is `MemWkp K 2` and ae-zero off the kernel. -/

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The reciprocal `1 / densityOnEuclid g α` of the chart density is `C^∞` on the
open chart target: the chart density is `C^∞` (`densityOnEuclid_contDiffOn`) and
strictly positive (`densityOnEuclid_pos`) there. -/
private lemma one_div_densityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => 1 / densityOnEuclid (I := I) g α y)
      (Ωα (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

/-- The differentiated numerator ae-vanishes off the partition-of-unity kernel.

Every layer factor — the iterated mixed weak partials of the chart component and
`fChartEffPrev` with its chosen weak `lₙ`-partial — ae-vanishes on `Ωα α \ Kα α`,
so each layer (a coefficient times such a factor) does, and so does their sum. -/
private lemma eigenvectorChartRHSDiffNumerator_ae_zero_off_Kα
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s h_uniform i α P₀ m l fChartEffPrev
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  -- Layer-A factors: every level-`(m+1)` mixed partial `Fin.cons a (Fin.init l)`.
  have hA_ae : ∀ a : Fin (Module.finrank ℝ E),
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l))
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun a =>
    iteratedPartial_ae_zero_off_Kα (I := I) (M := M)
      g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l))
  -- Layer-B factors: the chosen weak `b`-partials of those.
  have hB_ae : ∀ a b : Fin (Module.finrank ℝ E),
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (Ωα (I := I) (M := M) α)
        =ᵐ[(volume : Measure EuclN).restrict
          (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun a b =>
    chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
      (I := I) (M := M) α (hA_ae a) b
  -- Layer-C factor: the level-`m` mixed partial in `Fin.init l`.
  have hC_ae := iteratedPartial_ae_zero_off_Kα
    (I := I) (M := M) g r s h_uniform i α P₀ m (Fin.init l)
  -- Layer-E factor: the chosen weak `lₙ`-partial of `fChartEffPrev`.
  have hE_ae := chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
    (I := I) (M := M) α h_prev_ae_zero (l (Fin.last m))
  -- Each layer is ae-zero on the diff.
  have hA_sum_ae : (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)),
        ∀ a : Fin (Module.finrank ℝ E),
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y = 0 := by
      rw [Filter.eventually_all]
      intro a
      exact hA_ae a
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    change (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
          (l (Fin.last m))) y)
        (EuclideanSpace.single b 1) *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y = 0
    rw [hy a]; ring
  have hB_sum_ae : (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (Ωα (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    have h_all : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)),
        ∀ a : Fin (Module.finrank ℝ E), ∀ b : Fin (Module.finrank ℝ E),
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (Ωα (I := I) (M := M) α) y = 0 := by
      rw [Filter.eventually_all]
      intro a
      rw [Filter.eventually_all]
      intro b
      exact hB_ae a b
    filter_upwards [h_all] with y hy
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    change weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_uniform i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
        (Ωα (I := I) (M := M) α) y = 0
    rw [hy a b]; ring
  have hC_term_ae : (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_uniform i α P₀ m (Fin.init l) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hC_ae] with y hy
    show densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_uniform i α P₀ m (Fin.init l) y = 0
    rw [hy]; ring
  have hD_term_ae : (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y * fChartEffPrev y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [h_prev_ae_zero] with y hy
    show densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev y = 0
    rw [hy]; ring
  have hE_term_ae : (fun y =>
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          fChartEffPrev (Ωα (I := I) (M := M) α) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hE_ae] with y hy
    show densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (Ωα (I := I) (M := M) α) y = 0
    rw [hy]; ring
  -- Combine.
  filter_upwards [hA_sum_ae, hB_sum_ae, hC_term_ae, hD_term_ae, hE_term_ae]
    with y hA hB hC hD hE
  show eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s h_uniform i α P₀ m l fChartEffPrev y = 0
  unfold eigenvectorChartRHSDiffNumerator
  rw [hA, hB, hC, hD, hE]; ring

/-- **The chart-density-divided differentiated numerator is `MemWkp K 2` on the
chart target.** Rewriting `numerator / densityOnEuclid g α` as
`(1 / densityOnEuclid g α) · numerator`, the workhorse `memWkp_coef_mul_factor`
applies with `coef = 1 / densityOnEuclid g α` (smooth on the chart target) and
`factor = numerator` (`MemWkp K 2` on the chart target and ae-zero off the
partition-of-unity kernel).

This is an intermediate campaign lemma — the eigenvector/tensor analogue of the
scalar campaign's `fChartEffStepNumerator_div_density_memWkp`. -/
lemma eigenvectorChartRHSDiffNumerator_div_density_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
      (Ωα (I := I) (M := M) α))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s h_uniform i α P₀ m l fChartEffPrev y /
        densityOnEuclid (I := I) g α y)
      (Ωα (I := I) (M := M) α) := by
  classical
  -- Rewrite the quotient as `(1 / density) · numerator`.
  have h_eq : (fun y =>
      eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s h_uniform i α P₀ m l fChartEffPrev y /
      densityOnEuclid (I := I) g α y) =
      (fun y => (1 / densityOnEuclid (I := I) g α y) *
        eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s h_uniform i α P₀ m l fChartEffPrev y) := by
    funext y
    rw [one_div, mul_comm, ← div_eq_mul_inv]
  rw [h_eq]
  -- The numerator is `MemWkp K 2` on the chart target.
  have h_num_memWkp := eigenvectorChartRHSDiffNumerator_memWkp
    (I := I) (M := M) g r s h_uniform i α P₀ m K l
    h_comp h_prev_memWkp_succ h_prev_ae_zero
  -- The numerator ae-vanishes off the kernel.
  have h_num_ae_zero := eigenvectorChartRHSDiffNumerator_ae_zero_off_Kα
    (I := I) (M := M) g r s h_uniform i α P₀ m l h_prev_ae_zero
  -- Apply the workhorse with `coef = 1 / density`.
  exact memWkp_coef_mul_factor (I := I) (M := M) α K
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_num_memWkp h_num_ae_zero

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_uniform : uniformTensorChartSobolevBound g r s)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
      (Ωα (I := I) (M := M) α))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (Ωα (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (Ωα (I := I) (M := M) α \ Kα (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s h_uniform i α P₀ m l fChartEffPrev)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiffNumerator_memWkp (I := I) (M := M)
    g r s h_uniform i α P₀ m K l h_comp h_prev_memWkp_succ h_prev_ae_zero

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_uniform i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s h_uniform i α P₀ m l fChartEffPrev y /
        densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiffNumerator_div_density_memWkp (I := I) (M := M)
    g r s h_uniform i α P₀ m K l h_comp h_prev_memWkp_succ h_prev_ae_zero

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
