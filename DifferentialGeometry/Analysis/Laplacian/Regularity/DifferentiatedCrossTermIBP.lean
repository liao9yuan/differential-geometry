import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChartBilinearH1ComplH3
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChartBilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SmoothCoefWeakPartialIBP
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density

/-!
# Integration by parts for the Leibniz cross-term in the differentiated
# chart-bilinear identity

For `u_h ∈ laplacianDomainPow g 2` on a closed Riemannian manifold `(M, g)`,
the differentiated chart-bilinear identity packaged in
`DiffChartBilinearH1ComplData g α` contains, on its right-hand side, the
Leibniz cross-term

```
∫_{chartTarget} ∑_{i,j} weightedInvGramDerivOnEuclid g α i j direction y *
                       base.weak_partial i y *
                       (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂vol.
```

This module rewrites this cross-term, via integration by parts in direction
`j`, into the sum of two integrals against `ψ` (no test-function derivative
remaining). The integration by parts uses two ingredients:

* the smooth chart-target coefficient
  `weightedInvGramDerivOnEuclid g α i j direction` (only smooth on
  `chartTargetEuclid α`, with junk values elsewhere), which is *extended* to
  a globally smooth representative agreeing with the original on a
  neighborhood of `tsupport ψ`;
* the canonical second chosen weak partial
  `chosenSecondPartialChartPushedU g α u_h i j`, which is a weak `j`-partial
  of the chart-pushed first weak partial
  `(chartPushedWeakPartialLp g α i _ u_h).coeFn` on the whole chart target.

## Main results

* `chosenSecondPartialChartPushedU_isWeakPartial_of_chartPushedWeakPartialLp`
  — the canonical chosen second weak partial is a weak `j`-partial of
  `D.base.weak_partial i = (chartPushedWeakPartialLp g α i _ u_h).coeFn` on
  the chart target. This is a public re-export of the corresponding internal
  bridge from `DiffChartBilinearH1ComplFromDomainPow`.

* `cross_derivative_term_ibp` — the headline IBP identity for the Leibniz
  cross-term, expressed as a single integrated identity over the chart
  target.

## Strategy

1. Apply the smooth-coefficient integration-by-parts primitive
   `Sobolev.Euclidean.integral_smul_weak_partial_eq` to each pair `(i, j)`,
   with weak coefficient `v := (chartPushedWeakPartialLp g α i _ u_h).coeFn`
   and weak partials `w j' := chosenSecondPartialChartPushedU g α u_h i j'`.
   The smooth scalar coefficient is supplied via a smooth global extension
   of `weightedInvGramDerivOnEuclid g α i j direction`, obtained from a
   smooth cutoff function which equals `1` on a neighborhood of
   `tsupport ψ`.
2. Equality between the integrals against the global extension and the
   original chart-target restriction is a `setIntegral_congr_fun` step.
3. The doubly-summed identity is assembled via finite-sum manipulation of
   the per-pair identities.

-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DifferentiatedCrossTermIBP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-! ## Public re-export of the weak-partial identification -/

/-- The canonical chosen second weak partial
`chosenSecondPartialChartPushedU g α u_h i l` is a weak `l`-partial of
`(chartPushedWeakPartialLp g α i _ u_h).coeFn` on `chartTargetEuclid α`,
for `u_h ∈ laplacianDomainPow g 2`. This is a public alias for the internal
bridge in `DiffChartBilinearH1ComplFromDomainPow`. -/
theorem chosenSecondPartialChartPushedU_isWeakPartial_of_chartPushedWeakPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i l : Fin (Module.finrank ℝ E)) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) l
      (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l)
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  hasWeakPartialDeriv_chosenSecond_of_chartPushedWeakPartialLp
    (I := I) (M := M) g α hu_h i l

/-! ## Smooth global extension of a chart-target smooth coefficient -/

/-- Smooth global extension of a function `φ` that is `ContDiffOn` of any
order on the open chart target, agreeing with `φ` on a neighborhood of a
prescribed compact `K ⊆ chartTargetEuclid α`. Concretely we multiply `φ`
extended by zero off the chart target by a smooth cutoff `η` that is `1` on
a neighborhood of `K` and has `tsupport η ⊆ chartTargetEuclid α`.

The output is `(δ, η, φExt)` where `φExt := fun y => η y * φ y` is globally
smooth, with `φExt = φ` pointwise on `cthickening δ K` (a neighborhood of
`K`). -/
lemma exists_smooth_global_extension
    {φ : EuclN → ℝ} (α : M)
    (hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ (δ : ℝ) (φExt : EuclN → ℝ),
      0 < δ ∧
      Metric.cthickening δ K ⊆ chartTargetEuclid (I := I) (M := M) α ∧
      ContDiff ℝ (⊤ : ℕ∞) φExt ∧
      (∀ y ∈ Metric.cthickening δ K, φExt y = φ y) := by
  classical
  -- A smooth cutoff η equal to 1 on a neighborhood (cthickening δ K) of K,
  -- with tsupport η ⊆ chartTargetEuclid α.
  obtain ⟨δ, η, hδ_pos, hδ_subset, hη_smooth, hη_cs, _hη_range, hη_one, hη_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_compact
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hK_in
  -- The product η · φ is globally smooth (φ is only smooth on the chart
  -- target, but η = 0 outside the chart target, so η · φ is defined to be
  -- 0 there in the standard junk-value sense).
  let φExt : EuclN → ℝ := fun y => η y * φ y
  refine ⟨δ, φExt, hδ_pos, hδ_subset, ?_, ?_⟩
  · -- η is globally smooth; φ is smooth on the open chart target. On the open
    -- complement of tsupport η, η ≡ 0 in a neighborhood of every point, so
    -- η · φ ≡ 0 there.
    -- Hence η · φ is smooth at every point.
    -- We use the partition lemma `contDiff_iff_forall_localExpr` directly.
    have h_open_chart : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h_open_compl : IsOpen ((tsupport η)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    -- We rewrite φExt = η * φExt' where φExt' coincides with φ on chartTarget
    -- but is replaced by η * 0 = 0 outside via the η = 0 condition.
    -- Concretely we use `ContDiff.contDiffAt` at each point and split cases.
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport η
    · -- Inside `tsupport η ⊆ chartTargetEuclid α`: both η and φ are smooth.
      have hy_chart : y ∈ chartTargetEuclid (I := I) (M := M) α := hη_tsupp hy_supp
      have hη_at : ContDiffAt ℝ (⊤ : ℕ∞) η y := hη_smooth.contDiffAt
      have hφ_at : ContDiffAt ℝ (⊤ : ℕ∞) φ y :=
        (hφ_chart y hy_chart).contDiffAt (h_open_chart.mem_nhds hy_chart)
      exact hη_at.mul hφ_at
    · -- Outside `tsupport η`: η ≡ 0 in a neighborhood, hence φExt ≡ 0 there.
      have h_nbhd : (tsupport η)ᶜ ∈ 𝓝 y := h_open_compl.mem_nhds hy_supp
      have h_eq_zero : φExt =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_nbhd] with z hz
        have hηz : η z = 0 := image_eq_zero_of_notMem_tsupport hz
        change η z * φ z = 0
        rw [hηz, zero_mul]
      have h_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : EuclN => (0 : ℝ)) y :=
        contDiffAt_const
      -- `congr_of_eventuallyEq`: from `ContDiffAt f x` and `f₁ =ᶠ[𝓝 x] f`,
      -- conclude `ContDiffAt f₁ x`. Here `f := const 0`, `f₁ := φExt`.
      exact h_const.congr_of_eventuallyEq h_eq_zero
  · -- φExt y = η y * φ y = 1 * φ y = φ y on cthickening δ K.
    intro y hy
    change η y * φ y = φ y
    rw [hη_one y hy]
    ring

/-! ## Smoothness of `weightedInvGramDerivOnEuclid` on the chart target -/

/-- The `l`-partial Frechet derivative of `weightedInvGramOnEuclid` is smooth
on the chart target. (Public alias for `weightedInvGramDerivOnEuclid_contDiffOn`,
re-stated in the namespace of this file for ergonomics.) -/
private lemma weightedInvGramDerivOnEuclid_contDiffOn_chart
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (weightedInvGramDerivOnEuclid (I := I) g α i j l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  -- The `(⊤ : ℕ∞)` smoothness is the `∞` case of `ContDiffOn ℝ ∞`.
  have h := weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
  exact h

/-! ## Per-pair IBP identity for a single `(i, j)` -/

/-- For fixed indices `i, j, direction`, the per-pair IBP identity for the
Leibniz cross-term coefficient, applied against a smooth compactly supported
test function `ψ` with `tsupport ψ ⊆ chartTargetEuclid α`. -/
private lemma cross_derivative_term_ibp_single
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (i j : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
        (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
         ) : EuclN → ℝ)) y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j direction) y)
            (EuclideanSpace.single j 1) *
          (((chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
           ) : EuclN → ℝ)) y * ψ y
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h i j y * ψ y
          ∂(volume : Measure EuclN))) := by
  classical
  -- Abbreviate the open chart target.
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- The smooth coefficient on the chart target.
  set φ : EuclN → ℝ := weightedInvGramDerivOnEuclid (I := I) g α i j direction
    with hφ_def
  have hφ_chart : ContDiffOn ℝ (⊤ : ℕ∞) φ Ω :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j direction
  -- The weakly differentiable factor `v` (the chart-pushed weak partial Lp).
  set v : EuclN → ℝ :=
    (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ)) with hv_def
  -- The weak partials of `v` in each direction `j'`:
  set w : Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun j' => chosenSecondPartialChartPushedU
      (I := I) (M := M) g α u_h i j' with hw_def
  -- `w j'` is a weak `j'`-partial of `v` on `Ω`.
  have hw_isWeakPartial : ∀ j' : Fin (Module.finrank ℝ E),
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j' (w j') v Ω :=
    fun j' =>
      chosenSecondPartialChartPushedU_isWeakPartial_of_chartPushedWeakPartialLp
        (I := I) (M := M) g α hu_h i j'
  -- The compact set `K := tsupport ψ`, contained in `Ω`.
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  -- Smooth global extension of `φ` on a neighborhood of `K`.
  obtain ⟨δ, φExt, hδ_pos, hδ_subset, hφExt_smooth, hφExt_eq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := φ) α
      hφ_chart hK_compact hK_in
  -- Local-`L²` regularity of `v` on every compact subset of `Ω`.
  have hv_locMemLp : ∀ K' : Set EuclN, IsCompact K' → K' ⊆ Ω →
      MemLp v 2 ((volume : Measure EuclN).restrict K') := by
    intro K' hK'_compact hK'_in
    have h := chartPushedWeakPartialLp_locally_memLp
      (I := I) (M := M) g α i u_h hK'_compact hK'_in
    exact h
  -- Local-`L²` regularity of `w j'` on every compact subset of `Ω`.
  have hw_locMemLp : ∀ (j' : Fin (Module.finrank ℝ E)) (K' : Set EuclN),
      IsCompact K' → K' ⊆ Ω →
      MemLp (w j') 2 ((volume : Measure EuclN).restrict K') := by
    intro j' K' hK'_compact hK'_in
    have h := chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i j' hK'_compact hK'_in
    exact h
  -- Apply the generic IBP primitive to `(φExt, v, w)` in direction `j`.
  have h_ibp_ext :=
    Sobolev.Euclidean.integral_smul_weak_partial_eq
      (d := Module.finrank ℝ E) (Ω := Ω) hΩ_open
      (φ := φExt) hφExt_smooth (v := v) (w := w)
      hv_locMemLp hw_locMemLp hw_isWeakPartial j
      (ψ := ψ) hψ_smooth hψ_cs hψ_supp
  -- Now: replace `φExt` by `φ` everywhere on `Ω` in the integrals (only `tsupport ψ`
  -- matters, and on a neighborhood of `tsupport ψ`, `φExt = φ` AND
  -- `fderiv φExt = fderiv φ`).
  -- LHS replacement:
  --   ∫_Ω φExt · v · ∂_jψ = ∫_Ω φ · v · ∂_jψ
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hcthick_subset : Metric.cthickening δ K ⊆ Ω := hδ_subset
  have hK_in_thickening : K ⊆ Metric.cthickening δ K :=
    Metric.self_subset_cthickening _
  -- The fderiv of ψ vanishes outside tsupport ψ.
  have h_fderiv_zero_outside_K : ∀ x ∉ K, fderiv ℝ ψ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ Kᶜ := hx
    have hψ_zero_nbhd : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψ_const_zero : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hψ_zero_nbhd] with y hy
      rw [hy]
    rw [hψ_const_zero]; simp
  -- (i) LHS replacement.
  have hLHS_eq :
      ∫ y in Ω, φExt y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * v y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · -- On `K`, `φExt y = φ y` (since `K ⊆ cthickening δ K`).
      rw [hφExt_eq y (hK_in_thickening hy_K)]
    · -- Outside `K`, `fderiv ψ y = 0`, so both sides are zero.
      rw [h_fderiv_zero_outside_K y hy_K]
      simp
  -- (ii) First Leibniz-term replacement.
  -- `fderiv φExt y = fderiv φ y` on a neighborhood of K (since
  -- φExt =ᶠ[𝓝 y] φ inside cthickening δ K).
  have h_fderiv_φExt_eq_φ_on_K : ∀ y ∈ K, ∀ j' : Fin (Module.finrank ℝ E),
      (fderiv ℝ φExt y) (EuclideanSpace.single j' 1) =
      (fderiv ℝ φ y) (EuclideanSpace.single j' 1) := by
    intro y hy_K j'
    -- Find a small open ball around `y` inside `cthickening δ K` ∩ `chartTarget`.
    have hy_thick : y ∈ Metric.cthickening δ K := hK_in_thickening hy_K
    -- Use that interior of cthickening contains a neighborhood: actually we
    -- show φExt =ᶠ[𝓝 y] φ via a ball inside `interior (cthickening δ K)`.
    -- A simpler argument: pick a small ball around y in
    -- `Metric.thickening δ K`, which is open and contained in cthickening.
    have hy_thick_open : y ∈ Metric.thickening δ K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨y, hy_K, ?_⟩
      simp [hδ_pos]
    have h_thick_open : IsOpen (Metric.thickening δ K) := Metric.isOpen_thickening
    have h_nbhd : Metric.thickening δ K ∈ 𝓝 y := h_thick_open.mem_nhds hy_thick_open
    have h_thick_sub : Metric.thickening δ K ⊆ Metric.cthickening δ K :=
      Metric.thickening_subset_cthickening _ _
    have h_eq_nbhd : φExt =ᶠ[𝓝 y] φ := by
      filter_upwards [h_nbhd] with z hz
      exact hφExt_eq z (h_thick_sub hz)
    have h_fderiv_eq : fderiv ℝ φExt y = fderiv ℝ φ y :=
      Filter.EventuallyEq.fderiv_eq h_eq_nbhd
    rw [h_fderiv_eq]
  have hLeibniz1_eq :
      ∫ y in Ω, (fderiv ℝ φExt y) (EuclideanSpace.single j 1) * v y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in Ω, (fderiv ℝ φ y) (EuclideanSpace.single j 1) * v y * ψ y
        ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [h_fderiv_φExt_eq_φ_on_K y hy_K j]
    · -- Outside `K`, `ψ y = 0`, so both sides are zero.
      have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  -- (iii) Second Leibniz-term replacement: `φExt` to `φ` in the `(w j)`-term.
  have hLeibniz2_eq :
      ∫ y in Ω, φExt y * w j y * ψ y ∂(volume : Measure EuclN) =
      ∫ y in Ω, φ y * w j y * ψ y ∂(volume : Measure EuclN) := by
    refine setIntegral_congr_fun hΩ_meas (fun y hy => ?_)
    by_cases hy_K : y ∈ K
    · rw [hφExt_eq y (hK_in_thickening hy_K)]
    · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_K
      rw [hψy]; ring
  -- Combine.
  -- h_ibp_ext: ∫ φExt · v · ∂_jψ = -((∫ ∂_jφExt · v · ψ) + (∫ φExt · w j · ψ)).
  -- We rewrite LHS by hLHS_eq, and RHS pieces by hLeibniz1_eq / hLeibniz2_eq.
  -- Conclude.
  rw [← hLHS_eq, ← hLeibniz1_eq, ← hLeibniz2_eq]
  -- Goal is now exactly `h_ibp_ext` with `j` unfolded.
  exact h_ibp_ext

/-! ## Headline: doubly-summed IBP identity for the differentiated cross-term

The headline result states that the cross-derivative term in the Leibniz
expansion of the differentiated chart-bilinear identity equals its IBP'd
form summed over both `i` and `j`. -/

/-- **Doubly-summed IBP identity for the Leibniz cross-derivative term in
the differentiated chart-bilinear identity.**

For `u_h ∈ laplacianDomainPow g 2`, chart point `α`, direction
`l : Fin (Module.finrank ℝ E)`, and a smooth compactly supported test
function `ψ` with `tsupport ψ ⊆ chartTargetEuclid α`, the cross-derivative
term obtained by formally differentiating the chart-bilinear identity
admits the integration-by-parts identity

```
∫ ∑_{i,j} weightedInvGramDerivOnEuclid g α i j l y *
           (chartPushedWeakPartialLp g α i _ u_h) y *
           (fderiv ψ y)(eⱼ) ∂vol
  = -[ ∫ ∑_{i,j} (fderiv (weightedInvGramDerivOnEuclid g α i j l) y)(eⱼ) *
           (chartPushedWeakPartialLp g α i _ u_h) y * ψ y ∂vol
     + ∫ ∑_{i,j} weightedInvGramDerivOnEuclid g α i j l y *
           (chosenSecondPartialChartPushedU g α u_h i j) y * ψ y ∂vol ].
``` -/
theorem cross_derivative_term_ibp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l : Fin (Module.finrank ℝ E))
    {ψ : EuclN → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramDerivOnEuclid (I := I) g α i j l y *
            (((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
             ) : EuclN → ℝ)) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN))
    = -((∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
                (EuclideanSpace.single j 1) *
              (((chartPushedWeakPartialLp (I := I) (M := M) g α i
                (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
               ) : EuclN → ℝ)) y * ψ y)
          ∂(volume : Measure EuclN))
      + (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l y *
              chosenSecondPartialChartPushedU
                (I := I) (M := M) g α u_h i j y * ψ y)
          ∂(volume : Measure EuclN))) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  -- Abbreviations.
  set v : Fin (Module.finrank ℝ E) → EuclN → ℝ := fun i =>
    (((chartPushedWeakPartialLp (I := I) (M := M) g α i
      (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
     ) : EuclN → ℝ)) with hv_def
  set A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j => weightedInvGramDerivOnEuclid (I := I) g α i j l with hA_def
  set dA : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j j' y => (fderiv ℝ (A i j) y) (EuclideanSpace.single j' 1) with hdA_def
  set u₂ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → EuclN → ℝ :=
    fun i j' => chosenSecondPartialChartPushedU
      (I := I) (M := M) g α u_h i j' with hu₂_def
  -- LHS: ∫_Ω ∑_{i,j} A i j · v i · ∂_jψ
  --     = ∑_{i,j} ∫_Ω A i j · v i · ∂_jψ
  -- by `integral_finset_sum` over the doubled sum. We pull out the sums one by
  -- one.
  -- Per-pair IBP identity.
  have h_pair : ∀ (i j : Fin (Module.finrank ℝ E)),
      ∫ y in Ω, A i j y * v i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1) ∂(volume : Measure EuclN) =
      -((∫ y in Ω, dA i j j y * v i y * ψ y ∂(volume : Measure EuclN))
        + (∫ y in Ω, A i j y * u₂ i j y * ψ y ∂(volume : Measure EuclN))) :=
    fun i j =>
      cross_derivative_term_ibp_single
        (I := I) (M := M) g α hu_h l i j hψ_smooth hψ_cs hψ_supp
  -- Reduce ∫_Ω ∑_{i,j} _ = ∑_{i,j} ∫_Ω _.
  -- Integrability of per-pair integrands.
  set K : Set EuclN := tsupport ψ with hK_def
  have hK_compact : IsCompact K := hψ_cs
  have hK_in : K ⊆ Ω := hψ_supp
  have hK_meas : MeasurableSet K := (isClosed_tsupport ψ).measurableSet
  have hvolK_finite : (volume : Measure EuclN) K < (⊤ : ℝ≥0∞) :=
    hK_compact.measure_lt_top
  have hvolK_finite' : (volume.restrict K : Measure EuclN) Set.univ < (⊤ : ℝ≥0∞) := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hvolK_finite
  haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict K) := ⟨hvolK_finite'⟩
  -- Continuity / boundedness data.
  have hψ_cont : Continuous ψ := hψ_smooth.continuous
  have hψ_fderiv_j_cont : ∀ j : Fin (Module.finrank ℝ E),
      Continuous (fun y : EuclN => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    fun j => (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  -- The fderiv of ψ vanishes outside `K = tsupport ψ`.
  have h_fderiv_zero_outside_K : ∀ x ∉ K, fderiv ℝ ψ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ Kᶜ := hx
    have hψ_zero_nbhd : ∀ᶠ y in 𝓝 x, ψ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hψ_const_zero : fderiv ℝ ψ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hψ_zero_nbhd] with y hy
      rw [hy]
    rw [hψ_const_zero]; simp
  -- The fderiv of ψ has tsupport inside K, hence has compact support.
  have hψ_fderiv_supp : ∀ j : Fin (Module.finrank ℝ E),
      tsupport (fun y => (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) ⊆ K := by
    intro j
    refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
    by_contra hy_notin
    have : (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
      rw [h_fderiv_zero_outside_K y hy_notin]; simp
    exact hy this
  -- Build the integrability witnesses for the doubly-summed integrand.
  -- Continuity helpers for the coefficients.
  have h_A_cont_on : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (A i j) Ω := fun i j =>
    weightedInvGramDerivOnEuclid_continuousOn (I := I) g α i j l
  have h_A_cont_K : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (A i j) K := fun i j => (h_A_cont_on i j).mono hK_in
  -- Local-L² for v i on K.
  have hv_locMemLp_K : ∀ i : Fin (Module.finrank ℝ E),
      MemLp (v i) 2 ((volume : Measure EuclN).restrict K) :=
    fun i => chartPushedWeakPartialLp_locally_memLp
      (I := I) (M := M) g α i u_h hK_compact hK_in
  have hv_int_K : ∀ i : Fin (Module.finrank ℝ E),
      IntegrableOn (v i) K (volume : Measure EuclN) :=
    fun i => (hv_locMemLp_K i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- Continuity helper for the derivative coefficients dA i j j'.
  have h_dA_cont_on : ∀ i j j' : Fin (Module.finrank ℝ E),
      ContinuousOn (dA i j j') Ω := by
    intro i j j'
    have h_diffOn :=
      weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α i j l
    have h_fderiv_diff : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y) Ω :=
      ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ_open).1 h_diffOn).2
    have h_eval : ContDiff ℝ (⊤ : ℕ∞)
        (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single j' 1)) :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j' (1 : ℝ))).contDiff
    have h := h_eval.contDiffOn.comp h_fderiv_diff (mapsTo_univ _ _)
    exact h.continuousOn
  have h_dA_cont_K : ∀ i j j' : Fin (Module.finrank ℝ E),
      ContinuousOn (dA i j j') K := fun i j j' => (h_dA_cont_on i j j').mono hK_in
  -- Local-L² for u₂ i j' on K.
  have hu₂_locMemLp_K : ∀ (i j' : Fin (Module.finrank ℝ E)),
      MemLp (u₂ i j') 2 ((volume : Measure EuclN).restrict K) := fun i j' =>
    chosenSecondPartialChartPushedU_locally_memLp
      (I := I) (M := M) g α hu_h i j' hK_compact hK_in
  have hu₂_int_K : ∀ (i j' : Fin (Module.finrank ℝ E)),
      IntegrableOn (u₂ i j') K (volume : Measure EuclN) := fun i j' =>
    (hu₂_locMemLp_K i j').integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- Integrability of the per-pair LHS integrand on `volume.restrict Ω`.
  -- General helper: for continuous bounded `h₁ : EuclN → ℝ` with tsupport ⊆ K,
  -- and integrable `f` on K, the product f · h₁ is integrable on volume.restrict Ω.
  have integrable_mul_compact_v :
      ∀ {i : Fin (Module.finrank ℝ E)} {h₁ : EuclN → ℝ},
        Continuous h₁ → tsupport h₁ ⊆ K →
        Integrable (fun y => v i y * h₁ y)
          ((volume : Measure EuclN).restrict Ω) := by
    intro i h₁ hh₁_cont hh₁_supp
    have hh₁_contOn : ContinuousOn h₁ K := hh₁_cont.continuousOn
    have step_K : IntegrableOn (fun y => v i y * h₁ y) K (volume : Measure EuclN) :=
      (hv_int_K i).mul_continuousOn hh₁_contOn hK_compact
    have h_vanish : ∀ y, y ∉ K → v i y * h₁ y = 0 := by
      intro y hy
      have : h₁ y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hy_supp => hy (hh₁_supp hy_supp))
      simp [this]
    have h_eq_ind :
        (fun y => v i y * h₁ y) = K.indicator (fun y => v i y * h₁ y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, h_vanish y hy]
    have ind_int : Integrable (K.indicator (fun y => v i y * h₁ y))
        (volume : Measure EuclN) :=
      (integrable_indicator_iff hK_meas).mpr step_K
    have full_int : Integrable (fun y => v i y * h₁ y) (volume : Measure EuclN) := by
      rw [h_eq_ind]; exact ind_int
    exact full_int.restrict
  have integrable_mul_compact_u₂ :
      ∀ {i j' : Fin (Module.finrank ℝ E)} {h₁ : EuclN → ℝ},
        Continuous h₁ → tsupport h₁ ⊆ K →
        Integrable (fun y => u₂ i j' y * h₁ y)
          ((volume : Measure EuclN).restrict Ω) := by
    intro i j' h₁ hh₁_cont hh₁_supp
    have hh₁_contOn : ContinuousOn h₁ K := hh₁_cont.continuousOn
    have step_K : IntegrableOn (fun y => u₂ i j' y * h₁ y) K (volume : Measure EuclN) :=
      (hu₂_int_K i j').mul_continuousOn hh₁_contOn hK_compact
    have h_vanish : ∀ y, y ∉ K → u₂ i j' y * h₁ y = 0 := by
      intro y hy
      have : h₁ y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hy_supp => hy (hh₁_supp hy_supp))
      simp [this]
    have h_eq_ind :
        (fun y => u₂ i j' y * h₁ y) = K.indicator (fun y => u₂ i j' y * h₁ y) := by
      funext y
      by_cases hy : y ∈ K
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy, h_vanish y hy]
    have ind_int : Integrable (K.indicator (fun y => u₂ i j' y * h₁ y))
        (volume : Measure EuclN) :=
      (integrable_indicator_iff hK_meas).mpr step_K
    have full_int : Integrable (fun y => u₂ i j' y * h₁ y) (volume : Measure EuclN) := by
      rw [h_eq_ind]; exact ind_int
    exact full_int.restrict
  -- Per-pair integrability witnesses.
  -- LHS per-pair integrand: y ↦ A i j y * v i y * ∂_jψ y.
  have h_int_LHS_pair : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => A i j y * v i y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Ω) := by
    intro i j
    -- y ↦ A i j y * ∂_jψ y is continuous on K with tsupport ⊆ K.
    set h₁ : EuclN → ℝ := fun y => A i j y *
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1) with hh₁_def
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have hψ_y : (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
        rw [h_fderiv_zero_outside_K y hy_notin]; simp
      have : A i j y * (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
        rw [hψ_y, mul_zero]
      exact hy this
    -- Since `h₁ = 0` outside `K`, and `A i j` is continuous on K, `h₁` is
    -- continuous on EuclN.
    have h_h₁_cont : Continuous h₁ := by
      -- Continuity via continuity of A·∂_jψ on K and zero outside.
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ K
      · -- On the open interior of K? Not generally open. But on tsupport ψ
        -- (= K), continuity follows by noting `A i j` is continuous on the
        -- open chart target containing K, and ∂_jψ is globally continuous.
        have h_A_cont_at : ContinuousAt (A i j) y :=
          ((h_A_cont_on i j).continuousAt (hΩ_open.mem_nhds (hK_in hy)))
        exact h_A_cont_at.mul (hψ_fderiv_j_cont j).continuousAt
      · -- Outside K: h₁ vanishes in a neighborhood (Kᶜ is open;
        -- (∂_jψ) y = 0 in a neighborhood).
        have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
        have h_eq_zero : ∀ᶠ z in 𝓝 y, h₁ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds hy] with z hz
          have : (fderiv ℝ ψ z) (EuclideanSpace.single j 1) = 0 := by
            rw [h_fderiv_zero_outside_K z hz]; simp
          change A i j z * (fderiv ℝ ψ z) (EuclideanSpace.single j 1) = 0
          rw [this, mul_zero]
        have h_y_eq : h₁ y = 0 := by
          have : (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
            rw [h_fderiv_zero_outside_K y hy]; simp
          change A i j y * (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0
          rw [this, mul_zero]
        rw [continuousAt_congr h_eq_zero]
        exact continuousAt_const
    -- Apply the integrability helper.
    have h_int := integrable_mul_compact_v
      (i := i) (h₁ := h₁) h_h₁_cont hh₁_supp
    -- Now rewrite the product `v i · h₁` as `A i j · v i · ∂_jψ`.
    have h_eq : (fun y => v i y * h₁ y) =
        (fun y => A i j y * v i y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) := by
      funext y
      change v i y * (A i j y * (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =
        A i j y * v i y * (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
      ring
    rw [← h_eq]
    exact h_int
  -- RHS pair 1: dA i j j · v i · ψ.
  have h_int_RHS1_pair : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => dA i j j y * v i y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := by
    intro i j
    set h₁ : EuclN → ℝ := fun y => dA i j j y * ψ y with hh₁_def
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_notin
      have : dA i j j y * ψ y = 0 := by rw [hψ_y, mul_zero]
      exact hy this
    have h_h₁_cont : Continuous h₁ := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ K
      · have h_dA_cont_at : ContinuousAt (dA i j j) y :=
          ((h_dA_cont_on i j j).continuousAt (hΩ_open.mem_nhds (hK_in hy)))
        exact h_dA_cont_at.mul hψ_cont.continuousAt
      · have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
        have h_eq_zero : ∀ᶠ z in 𝓝 y, h₁ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds hy] with z hz
          have : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
          change dA i j j z * ψ z = 0
          rw [this, mul_zero]
        have h_y_eq : h₁ y = 0 := by
          have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
          change dA i j j y * ψ y = 0
          rw [this, mul_zero]
        rw [continuousAt_congr h_eq_zero]
        exact continuousAt_const
    have h_int := integrable_mul_compact_v
      (i := i) (h₁ := h₁) h_h₁_cont hh₁_supp
    have h_eq : (fun y => v i y * h₁ y) =
        (fun y => dA i j j y * v i y * ψ y) := by
      funext y
      change v i y * (dA i j j y * ψ y) = dA i j j y * v i y * ψ y
      ring
    rw [← h_eq]
    exact h_int
  -- RHS pair 2: A i j · u₂ i j · ψ.
  have h_int_RHS2_pair : ∀ i j : Fin (Module.finrank ℝ E),
      Integrable (fun y => A i j y * u₂ i j y * ψ y)
        ((volume : Measure EuclN).restrict Ω) := by
    intro i j
    set h₁ : EuclN → ℝ := fun y => A i j y * ψ y with hh₁_def
    have hh₁_supp : tsupport h₁ ⊆ K := by
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport ψ)
      by_contra hy_notin
      have hψ_y : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy_notin
      have : A i j y * ψ y = 0 := by rw [hψ_y, mul_zero]
      exact hy this
    have h_h₁_cont : Continuous h₁ := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ K
      · have h_A_cont_at : ContinuousAt (A i j) y :=
          ((h_A_cont_on i j).continuousAt (hΩ_open.mem_nhds (hK_in hy)))
        exact h_A_cont_at.mul hψ_cont.continuousAt
      · have h_compl_open : IsOpen (Kᶜ) := (isClosed_tsupport _).isOpen_compl
        have h_eq_zero : ∀ᶠ z in 𝓝 y, h₁ z = 0 := by
          filter_upwards [h_compl_open.mem_nhds hy] with z hz
          have : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
          change A i j z * ψ z = 0
          rw [this, mul_zero]
        have h_y_eq : h₁ y = 0 := by
          have : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
          change A i j y * ψ y = 0
          rw [this, mul_zero]
        rw [continuousAt_congr h_eq_zero]
        exact continuousAt_const
    have h_int := integrable_mul_compact_u₂
      (i := i) (j' := j) (h₁ := h₁) h_h₁_cont hh₁_supp
    have h_eq : (fun y => u₂ i j y * h₁ y) =
        (fun y => A i j y * u₂ i j y * ψ y) := by
      funext y
      change u₂ i j y * (A i j y * ψ y) = A i j y * u₂ i j y * ψ y
      ring
    rw [← h_eq]
    exact h_int
  -- Now expand the sums.
  -- LHS: ∫_Ω ∑_i ∑_j (A i j · v i · ∂_jψ) = ∑_i ∑_j ∫_Ω (A i j · v i · ∂_jψ).
  have hLHS_sum_swap :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            A i j y * v i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, A i j y * v i y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
              ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_LHS_pair i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_LHS_pair i j)]
  have hRHS1_sum_swap :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            dA i j j y * v i y * ψ y)
        ∂(volume : Measure EuclN)
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, dA i j j y * v i y * ψ y
              ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_RHS1_pair i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_RHS1_pair i j)]
  have hRHS2_sum_swap :
      ∫ y in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            A i j y * u₂ i j y * ψ y)
        ∂(volume : Measure EuclN)
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ y in Ω, A i j y * u₂ i j y * ψ y
              ∂(volume : Measure EuclN) := by
    rw [integral_finset_sum _ (fun i _ =>
      (integrable_finset_sum _ (fun j _ => h_int_RHS2_pair i j)))]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [integral_finset_sum _ (fun j _ => h_int_RHS2_pair i j)]
  -- Now use the per-pair identity to assemble.
  -- Sum over (i, j) the per-pair identity: ∑_{i,j} h_pair i j = ∑_{i,j} (- ...).
  rw [hLHS_sum_swap, hRHS1_sum_swap, hRHS2_sum_swap]
  -- Now: ∑_{i,j} ∫ A · v · ∂_jψ = ∑_{i,j} (-((∫ dA · v · ψ) + (∫ A · u₂ · ψ))).
  -- Apply h_pair pointwise.
  -- We compute step-by-step.
  -- Step 1: rewrite the LHS double-sum into the pointwise-negated form.
  have hLHS_neg :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ y in Ω, A i j y * v i y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)
            ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((∫ y in Ω, dA i j j y * v i y * ψ y
              ∂(volume : Measure EuclN))
            + (∫ y in Ω, A i j y * u₂ i j y * ψ y
              ∂(volume : Measure EuclN)))) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    exact h_pair i j
  -- Step 2: distribute the negation out of the double sums.
  -- Abbreviate the per-pair integrals.
  set X : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => ∫ y in Ω, dA i j j y * v i y * ψ y ∂(volume : Measure EuclN)
    with hX_def
  set Y : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => ∫ y in Ω, A i j y * u₂ i j y * ψ y ∂(volume : Measure EuclN)
    with hY_def
  -- Goal is now: ∑_{i} ∑_{j} (A i j · v i · ∂_j ψ integral) = -((∑_{i,j} X i j) + (∑_{i,j} Y i j))
  -- And hLHS_neg gives: LHS = ∑_{i,j} -(X i j + Y i j).
  have h_distribute :
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (-((X i j) + (Y i j))) =
      -((∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), X i j)
        + (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), Y i j)) := by
    -- Inner step: ∑_j -(X i j + Y i j) = -((∑_j X i j) + (∑_j Y i j))
    have h_inner : ∀ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E), (-((X i j) + (Y i j))) =
        -((∑ j : Fin (Module.finrank ℝ E), X i j)
          + (∑ j : Fin (Module.finrank ℝ E), Y i j)) := by
      intro i
      -- Rewrite -(X i j + Y i j) = -X i j + -Y i j.
      simp_rw [neg_add]
      -- ∑ j, (-X i j + -Y i j) = (∑ j, -X i j) + (∑ j, -Y i j)
      rw [Finset.sum_add_distrib]
      -- ∑ j, -X i j = -∑ j, X i j; ∑ j, -Y i j = -∑ j, Y i j.
      rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    rw [Finset.sum_congr rfl (fun i _ => h_inner i)]
    -- Outer step: ∑_i (-(P i + Q i)) = -((∑_i P i) + (∑_i Q i))
    -- where P i := ∑ j, X i j, Q i := ∑ j, Y i j.
    -- Rewrite -(P i + Q i) = -P i + -Q i.
    have h_outer : ∀ i : Fin (Module.finrank ℝ E),
        -((∑ j : Fin (Module.finrank ℝ E), X i j)
          + (∑ j : Fin (Module.finrank ℝ E), Y i j)) =
        (-(∑ j : Fin (Module.finrank ℝ E), X i j))
          + (-(∑ j : Fin (Module.finrank ℝ E), Y i j)) := by
      intro i; rw [neg_add]
    rw [Finset.sum_congr rfl (fun i _ => h_outer i)]
    -- Now: ∑_i (-(∑_j X i j) + (-(∑_j Y i j))) = (∑_i -(∑_j X i j)) + (∑_i -(∑_j Y i j))
    -- by sum-add-distrib.
    rw [Finset.sum_add_distrib]
    -- ∑_i -(∑_j X i j) = -(∑_i ∑_j X i j) by sum-neg-distrib (forward direction).
    rw [Finset.sum_neg_distrib (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (f := fun i => ∑ j, X i j)]
    rw [Finset.sum_neg_distrib (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (f := fun i => ∑ j, Y i j)]
    rw [← neg_add]
  rw [hLHS_neg]
  -- Now LHS = ∑_{i,j} -(X i j + Y i j) by unfolding X, Y.
  exact h_distribute

end DifferentiatedCrossTermIBP
end Laplacian
end Analysis
end DifferentialGeometry

end

/-! ## Axiom audit -/

section Sanity

#print axioms
  DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP.chosenSecondPartialChartPushedU_isWeakPartial_of_chartPushedWeakPartialLp
#print axioms
  DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP.cross_derivative_term_ibp

end Sanity
