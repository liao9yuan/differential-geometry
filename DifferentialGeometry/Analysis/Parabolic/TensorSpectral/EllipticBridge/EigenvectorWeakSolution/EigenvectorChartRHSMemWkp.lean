import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHS
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorCovGradComponent

/-!
# Iterated Sobolev regularity of the chart right-hand side: certain summands

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`
and a component multi-index `P₀`, the chart-Euclidean right-hand side
`eigenvectorChartRHS g r s h_uniform i α P₀` of the limiting per-component
variational identity is the `μ⁻¹`-rescaled seven-summand bracket

```
(1) − (2) + (3) − (4) − (5) + (6) − (7).
```

`eigenvectorChartRHS_memLp_weighted` (in `EigenvectorChartRHS.lean`) established
its weighted-`L²` membership — i.e. `MemWkp 0 2` — by splitting the bracket and
proving each summand `MemLp 2`. This module upgrades the **first three
summands** to iterated Euclidean Sobolev regularity `MemWkp K 2` for an
arbitrary order `K`, given the genuine bootstrap input

* `h_pou` — every partition-of-unity Euclidean chart component of the
  `L²`-coercion `TensorH1ComplToTensorL2 g r s (eigenvectorResolvent …)` of the
  eigenvector resolvent is `W^{K+1,2}` on its chart target, at every chart
  centre and for every component multi-index.

## The three summands

* **Summand 1** — the canonical eigenvector chart component
  `tensorL2ChartComponent g r s (tensorResolventEigenbasisVec h_uniform i) α P₀`.
  It is `μ⁻¹` times the chart component of `TensorH1ComplToTensorL2 g r s
  (eigenvectorResolvent …)` (`eigenvector_chartComponent_eq`); `MemWkp` is
  scalar-invariant, so `h_pou α P₀` and `MemWkp.le_of_le` give `MemWkp K 2`.
* **Summand 2** — the cross-left double sum: a finite `C^∞`-coefficient-weighted
  sum of the cross-left limit object `crossLeftLimitComponent`, which is the
  cutoff Euclidean chart component of the section-level covariant gradient
  `tensorCovGradL2Compl g r s (eigenvectorResolvent …)`. The cutoff ↔
  partition-of-unity bridge `tensorL2ChartComponentCutoff_memWkp_of_pou`, fed the
  covariant-gradient chart-component regularity `eigenvectorCovGrad_pou_memWkp`,
  makes it `W^{K,2}`; `MemWkp.smul_smooth_bounded` carries the smooth coefficient.
* **Summand 3** — the cross-right double sum: a finite `C^∞`-coefficient-weighted
  sum of the cross-right limit object `crossRightLimitComponent`, which is the
  cutoff Euclidean chart component of the `L²`-coercion `TensorH1ComplToTensorL2
  g r s (eigenvectorResolvent …)`. The cutoff ↔ partition-of-unity bridge, fed
  `h_pou` directly (after a `MemWkp.le_of_le` from `K + 1` to `K`), makes it
  `W^{K,2}`; `MemWkp.smul_smooth_bounded` carries the smooth coefficient.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

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
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Finite-sum closure of iterated Sobolev membership

`MemWkp k p` is closed under addition and contains the zero function, hence is
closed under arbitrary finite sums. -/

/-- **`MemWkp` is closed under finite sums.** If every member of a family of
functions indexed by a finite set is `W^{k,p}`-regular on an open set, then the
pointwise finite sum is `W^{k,p}`-regular. -/
private lemma memWkp_finsetSum
    {d : ℕ} [NeZero d] {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {ι : Type*} (T : Finset ι)
    (F : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ i ∈ T, MemWkp (d := d) k p (F i) Ω) :
    MemWkp (d := d) k p (fun y => ∑ i ∈ T, F i y) Ω := by
  classical
  induction T using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := d) (k := k) (p := p) hp hΩ
  | insert a s ha ih =>
      have hF_a : MemWkp (d := d) k p (F a) Ω :=
        hF a (Finset.mem_insert_self a s)
      have hF_s : ∀ i ∈ s, MemWkp (d := d) k p (F i) Ω :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have h_sum_s : MemWkp (d := d) k p (fun y => ∑ i ∈ s, F i y) Ω := ih hF_s
      have h_add : MemWkp (d := d) k p
          (fun y => F a y + ∑ i ∈ s, F i y) Ω :=
        MemWkp.add (d := d) hp hΩ hF_a h_sum_s
      have h_eq : (fun y => ∑ i ∈ insert a s, F i y) =
          fun y => F a y + ∑ i ∈ s, F i y := by
        funext y
        rw [Finset.sum_insert ha]
      rw [h_eq]
      exact h_add

/-! ## `MemWkp` for a chart-target-smooth coefficient times an ae-kernel-vanishing
factor

The workhorse for the cross-left and cross-right double sums. Given a coefficient
`C^∞` on the open chart target and a factor that is `MemWkp K 2` on the chart
target and vanishes almost everywhere off a fixed compact kernel inside the chart
target, the product lies in `MemWkp K 2` on the chart target.

The coefficient is cut off to a globally smooth, compactly supported
representative `χ · coef` by a smooth cutoff `χ` equal to `1` on a closed
thickening of the kernel and supported in the chart target. The product
`χ · coef` is globally smooth and compactly supported, so
`MemWkp.smul_smooth_bounded` keeps `MemWkp K 2`; finally
`(χ · coef) · factor =ᵐ coef · factor` because `χ = 1` on the thickening while
the factor ae-vanishes off the kernel. -/

/-- **`MemWkp` closure for a chart-target-smooth coefficient times an
ae-kernel-vanishing `MemWkp K 2` factor.** For a coefficient `coef` that is `C^∞`
on the open Euclidean chart target, a compact kernel `Kkern` inside the chart
target, and a factor that is `MemWkp K 2` on the chart target and vanishes almost
everywhere off `Kkern`, the pointwise product lies in `MemWkp K 2` on the chart
target. -/
private lemma memWkp_smoothCoef_mul_aeZeroFactor
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ Kkern → factor y = 0) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  -- A smooth cutoff `χ` equal to `1` on a closed thickening of `Kkern`, supported
  -- in the chart target `Ω`.
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKkern_compact hΩ_open hKkern_in
  -- `χ · coef` is globally smooth: smooth on `tsupport χ ⊆ Ω`, identically zero
  -- (hence smooth) on the open complement of `tsupport χ`.
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ Ω := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  -- A uniform bound on the iterated derivatives of `χ · coef` up to order `K`.
  obtain ⟨C, _hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  -- `(χ · coef) · factor ∈ MemWkp K 2` via `MemWkp.smul_smooth_bounded`.
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC_bd y j _hj) hfactor_memWkp
  -- `(χ · coef) · factor =ᵐ coef · factor` on `volume.restrict Ω`.
  set Cδ : Set EuclN := Metric.cthickening δ Kkern with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  -- The factor ae-vanishes off `Kkern` against `volume.restrict Ω` (the chart
  -- `L²` measure is, definitionally, `volume.restrict Ω`).
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kkern → factor y = 0 := by
    have h := hfactor_ae_zero
    rw [chartL2Measure] at h
    exact h
  -- On `Cδ ∩ Ω`: `χ = 1`, so `(χ · coef) · factor = coef · factor`.
  have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
      (fun y => coef y * factor y) := by
    refine (ae_restrict_iff' (hΩ_meas.inter hCδ_meas)).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hχy : χ y = 1 := hχ_one y hy.2
    change (χ y * coef y) * factor y = coef y * factor y
    rw [hχy]; ring
  -- On `Ω \ Cδ ⊆ Ω \ Kkern`: the factor ae-vanishes, so both products ae-vanish.
  have hKkern_in_Cδ : Kkern ⊆ Cδ := Metric.self_subset_cthickening _
  have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
      (fun y => coef y * factor y) := by
    have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
        (volume : Measure EuclN).restrict Ω :=
      Measure.restrict_mono Set.diff_subset le_rfl
    have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
        factor y = 0 := by
      have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          y ∉ Kkern → factor y = 0 :=
        (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
      have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
      filter_upwards [h_lift, h_off] with y hy hy_mem
      exact hy (fun hyK => hy_mem.2 (hKkern_in_Cδ hyK))
    filter_upwards [h_factor_diff] with y hy
    show (χ y * coef y) * factor y = coef y * factor y
    rw [hy]; ring
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
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, Measure.restrict_union h_disj h_diff_meas]
    exact (ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  -- Transfer `MemWkp K 2` through the almost-everywhere equality.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp

/-! ## The eigenvector chart component as a rescaled resolvent chart component

The regularity input `h_pou` is phrased for the `L²`-coercion
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s h_uniform i)` of the
`H¹`-completion resolvent. The canonical eigenvector chart component, however,
references the eigenvector vector `tensorResolventEigenbasisVec h_uniform i`
itself. The two differ by the nonzero scalar `μ⁻¹` (`eigenvector_chartComponent_eq`),
and `MemWkp` is scalar-invariant. -/

/-- The partition-of-unity Euclidean chart components of the eigenvector vector
`tensorResolventEigenbasisVec h_uniform i` are `MemWkp N 2` on every chart
target, given that those of the `L²`-coercion of the eigenvector resolvent are
`MemWkp N 2`. The two chart components differ by the nonzero scalar `μ⁻¹`, and
`MemWkp` is scalar-invariant; the iteration order is preserved. -/
private lemma eigenvectorVec_pou_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- `MemWkp N 2` of the resolvent-coercion chart component.
  have h_res : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    h_pou β Q
  -- The eigenvector chart component is `μ⁻¹` times the resolvent-coercion chart
  -- component (`eigenvector_chartComponent_eq`). Pass to `coeFn` and rescale.
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s h_uniform i β Q
  have h_ae : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i) β Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i)) β Q)
    have h_smul' : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
      rw [h_chart_eq]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  -- `MemWkp N 2` is scalar-invariant.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

/-! ## Summand 1 — the canonical eigenvector chart component

The first bracketed summand of `eigenvectorChartRHS` is the canonical eigenvector
chart component. Its `W^{K,2}` regularity is immediate from `eigenvectorVec_pou_memWkp`
(transferring the resolvent-coercion regularity to the eigenvector vector) and the
order-monotonicity `MemWkp.le_of_le`, since `K ≤ K + 1`. -/

/-- **Summand 1 is `W^{K,2}`.** The canonical eigenvector chart component
`tensorL2ChartComponent g r s (tensorResolventEigenbasisVec h_uniform i) α P₀` is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)` partition-of-unity
regularity input `h_pou`. -/
theorem eigenvectorChartRHS_summand1_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_uniform i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (eigenvectorVec_pou_memWkp (I := I) (M := M) g r s h_uniform i (K + 1)
    h_pou α P₀).le_of_le (Nat.le_succ K)

/-! ## Summand 2 — the cross-left limit contribution

The second bracketed summand of `eigenvectorChartRHS` is the finite double sum,
over `(r, s + 1)`-component multi-indices `(P, Q)`, of the `C^∞` coefficient
`covChartMetricGram · crossLeftTestCoeff` times the cross-left limit object
`crossLeftLimitComponent g r s h_uniform i α P`.

`crossLeftLimitComponent` is, by definition, the cutoff Euclidean chart component
`tensorL2ChartComponentCutoff g r (s + 1) (tensorCovGradL2Compl g r s
(eigenvectorResolvent …)) α P`. The cutoff ↔ partition-of-unity bridge
`tensorL2ChartComponentCutoff_memWkp_of_pou`, fed the covariant-gradient
chart-component regularity `eigenvectorCovGrad_pou_memWkp`, makes it `W^{K,2}`;
`MemWkp.smul_smooth_bounded` then carries the smooth coefficient. -/

/-- **The cross-left limit object is `W^{K,2}`.** The cross-left limit object
`crossLeftLimitComponent g r s h_uniform i α P` — the cutoff Euclidean chart
component of the section-level covariant gradient `tensorCovGradL2Compl g r s
(eigenvectorResolvent …)` — is `MemWkp K 2` on the chart-`α` target, given the
order-`(K + 1)` partition-of-unity regularity input `h_pou`.

The cutoff ↔ partition-of-unity bridge `tensorL2ChartComponentCutoff_memWkp_of_pou`
is fed the order-`K` covariant-gradient chart-component regularity
`eigenvectorCovGrad_pou_memWkp` (which itself consumes `h_pou`). -/
theorem crossLeftLimitComponent_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((crossLeftLimitComponent (I := I) (M := M) g r s h_uniform i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- `crossLeftLimitComponent` is the cutoff chart component of the section-level
  -- covariant gradient `tensorCovGradL2Compl g r s (eigenvectorResolvent …)`.
  rw [crossLeftLimitComponent]
  -- The bridge: feed it the covariant-gradient chart-component regularity, which
  -- itself consumes `h_pou`.
  exact tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r (s + 1)
    (tensorCovGradL2Compl (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i)) α P K
    (fun β Q => eigenvectorCovGrad_pou_memWkp (I := I) (M := M)
      g r s h_uniform i K h_pou β Q)

/-- **Summand 2 is `W^{K,2}`.** The cross-left double sum of `eigenvectorChartRHS`
— a finite `C^∞`-coefficient-weighted sum of the cross-left limit object — is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)` partition-of-unity
regularity input `h_pou`.

Each summand is the `C^∞` coefficient `covChartMetricGram · crossLeftTestCoeff`
times the `W^{K,2}` cross-left limit object; `MemWkp.smul_smooth_bounded` carries
the coefficient and `memWkp_finsetSum` assembles the double sum. -/
theorem eigenvectorChartRHS_summand2_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent (I := I) (M := M) g r s h_uniform i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Each `(P, Q)`-leaf is the smooth coefficient `covChartMetricGram ·
  -- crossLeftTestCoeff` times the `W^{K,2}` cross-left limit object.
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossLeftLimitComponent (I := I) (M := M) g r s h_uniform i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q
    -- The cross-left limit object is `W^{K,2}`.
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s h_uniform i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossLeftLimitComponent_memWkp (I := I) (M := M)
        g r s h_uniform i α P K h_pou
    -- The coefficient `covChartMetricGram · crossLeftTestCoeff` is `C^∞` on the
    -- chart target.
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q)
    -- The cross-left limit object is a cutoff chart component, hence ae-vanishes
    -- off the compact cutoff chart kernel.
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent (I := I) (M := M) g r s h_uniform i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i)) α P
    exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart h_factor h_factor_ae_zero
  -- The double sum of `W^{K,2}` leaves is `W^{K,2}`.
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r (s + 1),
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s h_uniform i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun Q y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s h_uniform i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => h_leaf P Q))

/-! ## Summand 3 — the cross-right limit contribution

The third bracketed summand of `eigenvectorChartRHS` is the finite double sum,
over `(r, s)`-component multi-indices `(P, Q)`, of the `C^∞` coefficient
`covChartMetricGram · crossRightTestValueCoeff` times the cross-right limit
object `crossRightLimitComponent g r s h_uniform i α P`.

`crossRightLimitComponent` is, by definition, the cutoff Euclidean chart component
`tensorL2ChartComponentCutoff g r s (TensorH1ComplToTensorL2 g r s
(eigenvectorResolvent …)) α P`. The cutoff ↔ partition-of-unity bridge
`tensorL2ChartComponentCutoff_memWkp_of_pou`, fed `h_pou` directly (after the
order monotonicity `K + 1 ≥ K`), makes it `W^{K,2}`; `MemWkp.smul_smooth_bounded`
then carries the smooth coefficient. -/

/-- **The cross-right limit object is `W^{K,2}`.** The cross-right limit object
`crossRightLimitComponent g r s h_uniform i α P` — the cutoff Euclidean chart
component of the `L²`-coercion `TensorH1ComplToTensorL2 g r s (eigenvectorResolvent
…)` — is `MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)`
partition-of-unity regularity input `h_pou`.

The cutoff ↔ partition-of-unity bridge `tensorL2ChartComponentCutoff_memWkp_of_pou`
is fed `h_pou` directly, after the order monotonicity `MemWkp.le_of_le` from
`K + 1` to `K`. -/
theorem crossRightLimitComponent_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((crossRightLimitComponent (I := I) (M := M) g r s h_uniform i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- `crossRightLimitComponent` is the cutoff chart component of the `L²`-coercion
  -- `TensorH1ComplToTensorL2 g r s (eigenvectorResolvent …)`.
  rw [crossRightLimitComponent]
  -- The bridge: feed it `h_pou` directly, after the order monotonicity.
  exact tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i)) α P K
    (fun β Q => (h_pou β Q).le_of_le (Nat.le_succ K))

/-- **Summand 3 is `W^{K,2}`.** The cross-right double sum of `eigenvectorChartRHS`
— a finite `C^∞`-coefficient-weighted sum of the cross-right limit object — is
`MemWkp K 2` on the chart-`α` target, given the order-`(K + 1)` partition-of-unity
regularity input `h_pou`.

Each summand is the `C^∞` coefficient `covChartMetricGram · crossRightTestValueCoeff`
times the `W^{K,2}` cross-right limit object; `MemWkp.smul_smooth_bounded` carries
the coefficient and `memWkp_finsetSum` assembles the double sum. -/
theorem eigenvectorChartRHS_summand3_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent (I := I) (M := M) g r s h_uniform i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- Each `(P, Q)`-leaf is the smooth coefficient `covChartMetricGram ·
  -- crossRightTestValueCoeff` times the `W^{K,2}` cross-right limit object.
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossRightLimitComponent (I := I) (M := M) g r s h_uniform i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q
    -- The cross-right limit object is `W^{K,2}`.
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossRightLimitComponent (I := I) (M := M)
            g r s h_uniform i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossRightLimitComponent_memWkp (I := I) (M := M)
        g r s h_uniform i α P K h_pou
    -- The coefficient `covChartMetricGram · crossRightTestValueCoeff` is `C^∞` on
    -- the chart target.
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q)
    -- The cross-right limit object is a cutoff chart component, hence ae-vanishes
    -- off the compact cutoff chart kernel.
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent (I := I) (M := M) g r s h_uniform i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i)) α P
    exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart h_factor h_factor_ae_zero
  -- The double sum of `W^{K,2}` leaves is `W^{K,2}`.
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s h_uniform i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s h_uniform i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => h_leaf P Q))

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
