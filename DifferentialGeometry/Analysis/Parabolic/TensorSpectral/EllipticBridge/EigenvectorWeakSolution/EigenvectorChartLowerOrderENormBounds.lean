import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.WeightedCoeffMulENormBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedData

/-!
# Explicit-norm `eLpNorm` bounds for two lower-order eigenvector chart limits

The chart-Euclidean right-hand side of the connection-Laplacian eigenvector's
weak-solution assembly is, summand by summand, a finite sum of
`C^∞`-coefficient-weighted lower-order limit objects. Two of those objects are

* `covLowerOrderRotationValueCoeffLimit g r s h_atlas i α P₀` — a four-fold sum
  of the kernel-cut `C^∞` factor `valuePartialFactor` against the chart-partial
  atom `partialLpLimit`, plus a five-fold sum of the kernel-cut `C^∞` factor
  `valueComponentFactor` against the chart-component atom `componentLpLimit`;
* `weightedGradCoeffDivLimit g r s h_atlas i α P₀ l` — a four-fold sum of the
  kernel-cut chart-Euclidean partial of the `C^∞` factor `weightedGradFactor`
  against `componentLpLimit`, plus a four-fold sum of the kernel-cut
  `weightedGradFactor` against `partialLpLimit`.

This file records, for each of these two objects, an explicit-constant
`eLpNorm` bound for the chart-pulled weighted measure: the `eLpNorm` of the
limit object is bounded by a nonnegative constant times the sum, over the
*distinct* chart-component / chart-partial atoms, of the atoms' `eLpNorm`.

The proof is the same for both objects. Each summand carries an
`indicator (chartPouKernel α)` cut of a `C^∞`-on-the-chart-target factor; the
accompanying atom vanishes almost everywhere — for the weighted measure — off
the compact partition-of-unity kernel `chartPouKernel α`, so the indicator-cut
summand agrees almost everywhere with the *uncut* `C^∞`-factor product. The
explicit-norm bound `eLpNorm_weighted_contDiffOn_mul_le` of the foundational
file then controls that product's `eLpNorm` by an explicit constant — the
`C^∞` factor's sup over the compact kernel — times the atom's `eLpNorm`. The
triangle inequality `eLpNorm_sum_le` over the nested finite sums and the two
groups assembles the per-summand bounds; every summation multiplicity and every
per-coefficient sup constant is folded into the single headline constant.

## Main results

* `eLpNorm_covLowerOrderRotationValueCoeffLimit_le`
* `eLpNorm_weightedGradCoeffDivLimit_le`

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
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
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

section LowerOrderENormBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-! ## Weighted almost-everywhere vanishing of the two atoms

Both atoms — the chart-component atom `componentLpLimit` and the chart-partial
atom `partialLpLimit` — vanish almost everywhere, for the chart-pulled weighted
measure restricted to the chart target, off the compact partition-of-unity
kernel `chartPouKernel α`.

For the chart-component atom this is the `i.fst.val`-rescaling of the weighted
off-kernel vanishing of the canonical Euclidean chart component
(`tensorL2ChartComponent_ae_zero_off_chartPouKernel_weighted`). For the
chart-partial atom it is the `i.fst.val`-rescaling of the weighted transfer of
the unconditional off-kernel vanishing of the eigenvector weak chart partial
(`eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel`). -/

/-- The chart-component atom `componentLpLimit g r s h_atlas i α P` vanishes
almost everywhere — for the chart-pulled weighted measure restricted to the
chart target — off the compact partition-of-unity kernel `chartPouKernel α`. -/
private lemma componentLpLimit_ae_zero_off_chartPouKernel_weighted
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((componentLpLimit (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  -- `componentLpLimit = i.fst.val • tensorL2ChartComponent (eigenvector)`.
  have h_smul : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [componentLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  -- Transfer the `=ᵐ` from the plain chart `L²` measure to the weighted one.
  have h_smul_w : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) :=
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α).ae_le h_smul
  -- The canonical chart component vanishes a.e. (weighted) off the kernel.
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel_weighted
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P
  filter_upwards [h_smul_w, h_comp_zero] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

/-- The chart-partial atom `partialLpLimit g r s h_atlas i α P k` vanishes almost
everywhere — for the chart-pulled weighted measure restricted to the chart
target — off the compact partition-of-unity kernel `chartPouKernel α`. -/
private lemma partialLpLimit_ae_zero_off_chartPouKernel_weighted
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  -- `partialLpLimit = i.fst.val • eigenvectorChartWeakPartial`.
  have h_smul : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y) := by
    rw [partialLpLimit, eigenvectorChartWeakPartial]
    exact Lp.coeFn_smul i.fst.val _
  -- The eigenvector weak chart partial vanishes a.e. on the open complement of
  -- the kernel inside the chart target.
  have h_weak_sdiff := eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s h_atlas i α P k
  have hKc_meas : MeasurableSet
      (chartPouKernel (I := I) (M := M) α)ᶜ :=
    (chartPouKernel_measurableSet (I := I) (M := M) α).compl
  -- Recast that `=ᵐ` on `Ω \ kernel` as an a.e. implication on `Ω`.
  have h_weak_impl : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y = 0 := by
    refine (ae_restrict_iff' hKc_meas).mp ?_
    rw [Measure.restrict_restrict hKc_meas]
    have h_inter : (chartPouKernel (I := I) (M := M) α)ᶜ ∩
        chartTargetEuclid (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α := by
      rw [Set.diff_eq, Set.inter_comm]
    rw [h_inter]
    filter_upwards [h_weak_sdiff] with y hy using hy
  -- Transfer from the plain restricted volume to the weighted measure.
  have h_weak_w : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y = 0 :=
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α).ae_le h_weak_impl
  -- Transfer the `i.fst.val`-rescaling identity to the weighted measure.
  have h_smul_w : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y) :=
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α).ae_le h_smul
  filter_upwards [h_smul_w, h_weak_w] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

/-! ## Weighted-`L²` membership of the two atoms

Each atom is `MemLp 2` for the chart-pulled weighted measure restricted to the
chart target: it is an `Lp ℝ 2 (chartL2Measure α)` element (hence `MemLp 2` of
the plain restricted volume) that vanishes almost everywhere off the compact
partition-of-unity kernel, so the general weighted upgrade
`memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact`
applies. -/

/-- The chart-component atom `componentLpLimit g r s h_atlas i α P` is `MemLp 2`
for the chart-pulled weighted measure restricted to the chart target. -/
private lemma componentLpLimit_memLp_weighted
    (α : M) (P : TensorCompIdx (E := E) r s) :
    MemLp (fun y => ((componentLpLimit (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- The atom is `MemLp 2` of the plain chart `L²` reference measure.
  have h_plain : MemLp (fun y => ((componentLpLimit (I := I) (M := M)
      g r s h_atlas i α P :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      (chartL2Measure (I := I) (M := M) α) := Lp.memLp _
  -- The atom vanishes a.e. off the kernel for the plain chart `L²` measure.
  have h_smul : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [componentLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P
  have h_atom_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((componentLpLimit (I := I) (M := M) g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    filter_upwards [h_smul, h_comp_zero] with y hy hy_zero hyK
    rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    h_atom_zero h_plain

/-- The chart-partial atom `partialLpLimit g r s h_atlas i α P k` is `MemLp 2`
for the chart-pulled weighted measure restricted to the chart target. -/
private lemma partialLpLimit_memLp_weighted
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (fun y => ((partialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- The atom is `MemLp 2` of the plain chart `L²` reference measure.
  have h_plain : MemLp (fun y => ((partialLpLimit (I := I) (M := M)
      g r s h_atlas i α P k :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      (chartL2Measure (I := I) (M := M) α) := Lp.memLp _
  -- `partialLpLimit = i.fst.val • eigenvectorChartWeakPartial`.
  have h_smul : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y) := by
    rw [partialLpLimit, eigenvectorChartWeakPartial]
    exact Lp.coeFn_smul i.fst.val _
  -- The eigenvector weak chart partial vanishes a.e. off the kernel.
  have h_weak_sdiff := eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s h_atlas i α P k
  have hKc_meas : MeasurableSet
      (chartPouKernel (I := I) (M := M) α)ᶜ :=
    (chartPouKernel_measurableSet (I := I) (M := M) α).compl
  have h_weak_impl : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y = 0 := by
    refine (ae_restrict_iff' hKc_meas).mp ?_
    rw [Measure.restrict_restrict hKc_meas]
    have h_inter : (chartPouKernel (I := I) (M := M) α)ᶜ ∩
        chartTargetEuclid (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α := by
      rw [Set.diff_eq, Set.inter_comm]
    rw [h_inter]
    filter_upwards [h_weak_sdiff] with y hy using hy
  -- The atom vanishes a.e. off the kernel for the plain chart `L²` measure.
  have h_atom_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    filter_upwards [h_smul, h_weak_impl] with y hy hy_zero hyK
    rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    h_atom_zero h_plain

/-! ## The per-summand explicit-norm bound

Each summand of either limit object is the `chartPouKernel α`-indicator cut of a
`C^∞`-on-the-chart-target coefficient, times an `Lp ℝ 2 (chartL2Measure α)`
atom. The lemma below records, for any such pair, the explicit-norm `eLpNorm`
estimate against the weighted measure, together with the summand's weighted-`L²`
membership (needed to feed the triangle inequality). -/

/-- For a `C^∞`-on-the-chart-target coefficient `c` and a function `G` that is
weighted-`MemLp` and vanishes almost everywhere — for the chart-pulled weighted
measure restricted to the chart target — off the compact partition-of-unity
kernel, the indicator-cut summand `(chartPouKernel α).indicator c · G` is
weighted-`MemLp` and its `eLpNorm` is bounded by an explicit nonnegative
constant times the `eLpNorm` of `G`. -/
private lemma eLpNorm_indicatorFactor_mul_atom_le
    (g : SmoothRiemannianMetric I M) (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    (G : EuclN → ℝ)
    (hG : MemLp G 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)))
    (hG_zero : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) :
    MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
        G y) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        eLpNorm (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
            G y) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eLpNorm G 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- Off the kernel `G` vanishes a.e., so the indicator-cut coefficient agrees
  -- a.e. (weighted) with the uncut `C^∞` coefficient.
  have h_prod_eq : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        c y * G y) =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)] (fun y => c y * G y) := by
    filter_upwards [hG_zero] with y hy
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK, mul_zero, mul_zero]
  -- The uncut product is weighted-`MemLp` and explicitly `eLpNorm`-bounded.
  have h_mul_memLp : MemLp (fun y => c y * G y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    memLp_weighted_contDiffOn_mul (I := I) (M := M) g α hc
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      hG hG_zero
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le
    (I := I) (M := M) g α hc
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    hG hG_zero
  refine ⟨h_mul_memLp.ae_eq h_prod_eq.symm, C, hC_nn, ?_⟩
  rw [eLpNorm_congr_ae h_prod_eq]
  exact hC_bd

/-! ## The aggregation lemmas

The triangle inequality over a finite sum bounds the `eLpNorm` of the sum by the
sum of the `eLpNorm`s of the summands. The lemmas below package, once, the steps
shared by the two headlines. The completeness / non-degeneracy / closedness
instances enter only through the *type* of the chart-pulled weighted measure and
play no role in these purely measure-theoretic estimates. -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- Triangle inequality for `eLpNorm` over a finite sum, with each summand
weighted-`MemLp`. -/
private lemma eLpNorm_finsetSum_le
    {ι : Type*} (g : SmoothRiemannianMetric I M) (α : M)
    (s : Finset ι) (F : ι → EuclN → ℝ)
    (hF : ∀ j ∈ s, MemLp (F j) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))) :
    eLpNorm (fun y => ∑ j ∈ s, F j y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ∑ j ∈ s, eLpNorm (F j) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_fun : (fun y => ∑ j ∈ s, F j y) = ∑ j ∈ s, F j := by
    funext y
    exact (Finset.sum_apply y s F).symm
  rw [h_fun]
  exact eLpNorm_sum_le (fun j hj => (hF j hj).1) (by norm_num)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- A finite indexed family of summands, each weighted-`MemLp` and each
`eLpNorm`-bounded by `ENNReal.ofReal C` times the `eLpNorm` of an atom selected
by a projection `proj`, has its summed `eLpNorm` bounded by `ENNReal.ofReal` of
an explicit constant times the sum, over the distinct atoms, of the atoms'
`eLpNorm`. -/
private lemma eLpNorm_finsetSum_le_const_mul_atomSum
    {ι κ : Type*} (g : SmoothRiemannianMetric I M) (α : M)
    (s : Finset ι) (t : Finset κ) (F : ι → EuclN → ℝ) (atom : κ → EuclN → ℝ)
    (proj : ι → κ) (hproj : ∀ j ∈ s, proj j ∈ t)
    (C : ℝ) (_hC_nn : 0 ≤ C)
    (hF : ∀ j ∈ s, MemLp (F j) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    (h_bd : ∀ j ∈ s, eLpNorm (F j) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal C * eLpNorm (atom (proj j)) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) :
    eLpNorm (fun y => ∑ j ∈ s, F j y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal (C * s.card)
        * ∑ p ∈ t, eLpNorm (atom p) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- Triangle inequality, then the per-summand bound, then bound each projected
  -- atom `eLpNorm` by the whole nonnegative atom-sum.
  have h_tri := eLpNorm_finsetSum_le (I := I) (M := M) g α s F hF
  have h_step : ∑ j ∈ s, eLpNorm (F j) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ∑ _j ∈ s, ENNReal.ofReal C
        * ∑ p ∈ t, eLpNorm (atom p) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    refine (h_bd j hj).trans ?_
    refine mul_le_mul_right ?_ _
    exact Finset.single_le_sum
      (f := fun p => eLpNorm (atom p) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      (fun p _ => zero_le _) (hproj j hj)
  have h_const : ∑ _j ∈ s, ENNReal.ofReal C
        * ∑ p ∈ t, eLpNorm (atom p) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
      = (s.card : ℝ≥0∞) * (ENNReal.ofReal C
        * ∑ p ∈ t, eLpNorm (atom p) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  -- Reassociate the constant `s.card * ENNReal.ofReal C` into `ENNReal.ofReal`.
  have h_cast : (s.card : ℝ≥0∞) * ENNReal.ofReal C
      = ENNReal.ofReal (C * s.card) := by
    rw [mul_comm C, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  calc
    eLpNorm (fun y => ∑ j ∈ s, F j y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))
        ≤ ∑ j ∈ s, eLpNorm (F j) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := h_tri
    _ ≤ ∑ _j ∈ s, ENNReal.ofReal C
          * ∑ p ∈ t, eLpNorm (atom p) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := h_step
    _ = (s.card : ℝ≥0∞) * (ENNReal.ofReal C
          * ∑ p ∈ t, eLpNorm (atom p) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) := h_const
    _ = ((s.card : ℝ≥0∞) * ENNReal.ofReal C)
          * ∑ p ∈ t, eLpNorm (atom p) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by rw [mul_assoc]
    _ = ENNReal.ofReal (C * s.card)
          * ∑ p ∈ t, eLpNorm (atom p) 2
              ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by rw [h_cast]

/-! ## Headline 1 — the lower-order rotation value coefficient limit

`covLowerOrderRotationValueCoeffLimit g r s h_atlas i α P₀` is the sum of two
groups: a four-fold sum over `(P, Q, k, l)` of the kernel-cut `C^∞` factor
`valuePartialFactor` against the chart-partial atom `partialLpLimit P k`, and a
five-fold sum over `(P, Q, k, l, p)` of the kernel-cut `C^∞` factor
`valueComponentFactor` against the chart-component atom `componentLpLimit p`. -/

/-- **Explicit-norm `eLpNorm` bound for the lower-order rotation value
coefficient limit.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`,
an eigenbasis index `i`, a chart center `α : M`, and a component multi-index
`P₀`, there is a nonnegative constant `C` with

```
eLpNorm (covLowerOrderRotationValueCoeffLimit g r s h_atlas i α P₀) 2 μw
  ≤ ENNReal.ofReal C * ((∑ P, ∑ k, eLpNorm (partialLpLimit … P k) 2 μw)
      + (∑ p, eLpNorm (componentLpLimit … p) 2 μw)),
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)` and
the sums on the right range over the distinct chart-partial / chart-component
atoms.

Each of the two groups defining the limit object is a finite sum whose summands
carry an `indicator (chartPouKernel α)` cut of a `C^∞` factor; the accompanying
atom vanishes almost everywhere (weighted) off the compact partition-of-unity
kernel, so the indicator-cut summand agrees almost everywhere with the uncut
`C^∞`-factor product, and `eLpNorm_weighted_contDiffOn_mul_le` controls its
`eLpNorm`. The triangle inequality assembles the per-summand bounds; every
summation multiplicity and every per-coefficient sup constant is folded into the
single constant `C`. -/
theorem eLpNorm_covLowerOrderRotationValueCoeffLimit_le
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
          g r s h_atlas i α P₀ : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          ((∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit (I := I) (M := M)
                    g r s h_atlas i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ p : TensorCompIdx (E := E) r s,
                eLpNorm ((componentLpLimit (I := I) (M := M)
                    g r s h_atlas i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- Abbreviations for the two distinct atom families.
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pk y =>
    ((partialLpLimit (I := I) (M := M) g r s h_atlas i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set compAtom : TensorCompIdx (E := E) r s → EuclN → ℝ := fun p y =>
    ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  -- The chart-partial group, as a single sum over `(P, Q, k, l)`.
  set Fpart : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s h_atlas i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  -- The chart-component group, as a single sum over `(P, Q, k, l, p)`.
  set Fcomp : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y *
        ((componentLpLimit (I := I) (M := M) g r s h_atlas i α x.2.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  -- The per-summand membership / bound for the chart-partial group.
  have h_part_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))),
      MemLp (Fpart x) 2 μw ∧
        ∃ C : ℝ, 0 ≤ C ∧
          eLpNorm (Fpart x) 2 μw
            ≤ ENNReal.ofReal C * eLpNorm (partAtom (x.1, x.2.2.1)) 2 μw := by
    intro x _
    rw [hμw_def]
    exact eLpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) g α
      (valuePartialFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)
      _
      (partialLpLimit_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.1 x.2.2.1)
      (partialLpLimit_ae_zero_off_chartPouKernel_weighted (I := I) (M := M)
        g r s h_atlas i α x.1 x.2.2.1)
  -- The per-summand membership / bound for the chart-component group.
  have h_comp_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s)),
      MemLp (Fcomp x) 2 μw ∧
        ∃ C : ℝ, 0 ≤ C ∧
          eLpNorm (Fcomp x) 2 μw
            ≤ ENNReal.ofReal C * eLpNorm (compAtom x.2.2.2.2) 2 μw := by
    intro x _
    rw [hμw_def]
    exact eLpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) g α
      (valueComponentFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      _
      (componentLpLimit_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2.2)
      (componentLpLimit_ae_zero_off_chartPouKernel_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2.2)
  -- A single nonnegative constant dominating every chart-partial-summand
  -- constant: the sum of all of them.
  obtain ⟨Cpart, hCpart_nn, hCpart_bd⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))),
        eLpNorm (Fpart x) 2 μw
          ≤ ENNReal.ofReal C * eLpNorm (partAtom (x.1, x.2.2.1)) 2 μw := by
    refine ⟨∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        (h_part_data x (Finset.mem_univ x)).2.choose, ?_, ?_⟩
    · exact Finset.sum_nonneg
        (fun x _ => (h_part_data x (Finset.mem_univ x)).2.choose_spec.1)
    · intro x _
      refine (h_part_data x (Finset.mem_univ x)).2.choose_spec.2.trans ?_
      refine mul_le_mul_left ?_ _
      refine ENNReal.ofReal_le_ofReal ?_
      exact Finset.single_le_sum
        (f := fun x => (h_part_data x (Finset.mem_univ x)).2.choose)
        (fun x _ => (h_part_data x (Finset.mem_univ x)).2.choose_spec.1)
        (Finset.mem_univ x)
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)),
        eLpNorm (Fcomp x) 2 μw
          ≤ ENNReal.ofReal C * eLpNorm (compAtom x.2.2.2.2) 2 μw := by
    refine ⟨∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s,
        (h_comp_data x (Finset.mem_univ x)).2.choose, ?_, ?_⟩
    · exact Finset.sum_nonneg
        (fun x _ => (h_comp_data x (Finset.mem_univ x)).2.choose_spec.1)
    · intro x _
      refine (h_comp_data x (Finset.mem_univ x)).2.choose_spec.2.trans ?_
      refine mul_le_mul_left ?_ _
      refine ENNReal.ofReal_le_ofReal ?_
      exact Finset.single_le_sum
        (f := fun x => (h_comp_data x (Finset.mem_univ x)).2.choose)
        (fun x _ => (h_comp_data x (Finset.mem_univ x)).2.choose_spec.1)
        (Finset.mem_univ x)
  -- Bound on the chart-partial group `eLpNorm`.
  have h_part_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), Fpart x y) 2 μw
        ≤ ENNReal.ofReal (Cpart * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              eLpNorm (partAtom pk) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fpart partAtom
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      Cpart hCpart_nn
      (fun x hx => by rw [← hμw_def]; exact (h_part_data x hx).1)
      (fun x hx => by rw [← hμw_def]; exact hCpart_bd x hx)
  -- Bound on the chart-component group `eLpNorm`.
  have h_comp_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          Fcomp x y) 2 μw
        ≤ ENNReal.ofReal (Ccomp * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              eLpNorm (compAtom p) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fcomp compAtom
      (fun x => x.2.2.2.2) (fun x _ => Finset.mem_univ _)
      Ccomp hCcomp_nn
      (fun x hx => by rw [← hμw_def]; exact (h_comp_data x hx).1)
      (fun x hx => by rw [← hμw_def]; exact hCcomp_bd x hx)
  -- Identify the two single-product sums with the two nested-sum groups.
  have h_part_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), Fpart x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_comp_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, Fcomp x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                      EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  -- The chart-partial index sum on the right is the chart-partial atom family.
  have h_part_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), eLpNorm (partAtom pk) 2 μw
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [Fintype.sum_prod_type]
  -- Headline constant: the larger of the two group constants.
  refine ⟨max
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card),
    le_trans (by positivity) (le_max_left _ _), ?_⟩
  -- Abbreviations for the headline constant and the two atom-sums.
  set Cmax : ℝ := max
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card) with hCmax_def
  -- Bound on the chart-partial group, in the distinct-atom-sum form.
  have hpart : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E), Fpart x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  -- Bound on the chart-component group, in the distinct-atom-sum form.
  have hcomp : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
        Fcomp x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          eLpNorm ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            μw := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _
  -- Weighted-`L²` membership of the two groups, for the triangle inequality.
  have h_part_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), Fpart x y) 2 μw :=
    memLp_finset_sum _ (fun x hx => (h_part_data x hx).1)
  have h_comp_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      Fcomp x y) 2 μw :=
    memLp_finset_sum _ (fun x hx => (h_comp_data x hx).1)
  -- Unfold the limit object into its two groups, bridge to single-product sums.
  unfold covLowerOrderRotationValueCoeffLimit
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (valueComponentFactor (I := I) (M := M)
                          g r s α P₀ P Q k l p) y *
                      (componentLpLimit (I := I) (M := M)
                        g r s h_atlas i α p : EuclN → ℝ) y)
      = (fun y => (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), Fpart x y)
          + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fcomp x y) := by
    funext y
    rw [← congrFun h_part_eq y, ← congrFun h_comp_eq y]
  rw [h_bridge]
  -- Triangle inequality, then the two group bounds, then distribute.
  calc
    eLpNorm (fun y => (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), Fpart x y)
        + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
            × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
        ≤ eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × Fin (Module.finrank ℝ E), Fpart x y) 2 μw
          + eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
              Fcomp x y) 2 μw :=
        eLpNorm_add_le h_part_memLp.1 h_comp_memLp.1 (by norm_num)
    _ ≤ ENNReal.ofReal Cmax *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                μw)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw) :=
        add_le_add hpart hcomp
    _ = ENNReal.ofReal Cmax *
          ((∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit (I := I) (M := M)
                    g r s h_atlas i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  μw)
            + (∑ p : TensorCompIdx (E := E) r s,
                eLpNorm ((componentLpLimit (I := I) (M := M)
                    g r s h_atlas i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  μw)) := by
      rw [mul_add]

/-! ## Headline 2 — the chart-density-weighted lower-order gradient divergence

`weightedGradCoeffDivLimit g r s h_atlas i α P₀ l` is the sum of two four-fold
sums over `(P, Q, k, p)`: the kernel-cut chart-Euclidean partial of the `C^∞`
factor `weightedGradFactor` against the chart-component atom `componentLpLimit p`,
and the kernel-cut `weightedGradFactor` against the chart-partial atom
`partialLpLimit p l`. -/

/-- **Explicit-norm `eLpNorm` bound for the chart-density-weighted lower-order
gradient divergence coefficient limit.** For a closed Riemannian manifold
`(M, g)`, ranks `(r, s)`, an eigenbasis index `i`, a chart center `α : M`, a
component multi-index `P₀`, and a chart direction `l`, there is a nonnegative
constant `C` with

```
eLpNorm (weightedGradCoeffDivLimit g r s h_atlas i α P₀ l) 2 μw
  ≤ ENNReal.ofReal C * ((∑ p, eLpNorm (componentLpLimit … p) 2 μw)
      + (∑ p, ∑ l, eLpNorm (partialLpLimit … p l) 2 μw)),
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)` and
the sums on the right range over the distinct chart-component / chart-partial
atoms.

Each of the two four-fold sums defining the limit object has summands carrying
an `indicator (chartPouKernel α)` cut of a `C^∞` factor — the chart-Euclidean
partial of `weightedGradFactor`, respectively `weightedGradFactor` itself; the
accompanying atom vanishes almost everywhere (weighted) off the compact
partition-of-unity kernel, so the indicator-cut summand agrees almost everywhere
with the uncut `C^∞`-factor product, controlled by
`eLpNorm_weighted_contDiffOn_mul_le`. The triangle inequality assembles the
per-summand bounds; every summation multiplicity and per-coefficient sup
constant is folded into the single constant `C`. -/
theorem eLpNorm_weightedGradCoeffDivLimit_le
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (weightedGradCoeffDivLimit (I := I) (M := M)
          g r s h_atlas i α P₀ l : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          ((∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α)))
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit (I := I) (M := M)
                      g r s h_atlas i α p l' :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- Abbreviations for the two distinct atom families.
  set compAtom : TensorCompIdx (E := E) r s → EuclN → ℝ := fun p y =>
    ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pl y =>
    ((partialLpLimit (I := I) (M := M) g r s h_atlas i α pl.1 pl.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  -- The chart-component group, as a single sum over `(P, Q, k, p)`.
  set Fcomp : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y *
        ((componentLpLimit (I := I) (M := M) g r s h_atlas i α x.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  -- The chart-partial group, as a single sum over `(P, Q, k, p)`.
  set Fpart : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M)
            g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s h_atlas i α x.2.2.2 l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  -- The per-summand membership / bound for the chart-component group.
  have h_comp_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)),
      MemLp (Fcomp x) 2 μw ∧
        ∃ C : ℝ, 0 ≤ C ∧
          eLpNorm (Fcomp x) 2 μw
            ≤ ENNReal.ofReal C * eLpNorm (compAtom x.2.2.2) 2 μw := by
    intro x _
    rw [hμw_def]
    exact eLpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) g α
      (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)
      _
      (componentLpLimit_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2)
      (componentLpLimit_ae_zero_off_chartPouKernel_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2)
  -- The per-summand membership / bound for the chart-partial group.
  have h_part_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)),
      MemLp (Fpart x) 2 μw ∧
        ∃ C : ℝ, 0 ≤ C ∧
          eLpNorm (Fpart x) 2 μw
            ≤ ENNReal.ofReal C * eLpNorm (partAtom (x.2.2.2, l)) 2 μw := by
    intro x _
    rw [hμw_def]
    exact eLpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) g α
      (weightedGradFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)
      _
      (partialLpLimit_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2 l)
      (partialLpLimit_ae_zero_off_chartPouKernel_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2 l)
  -- A single nonnegative constant dominating every chart-component-summand
  -- constant: the sum of all of them.
  obtain ⟨Ccomp, hCcomp_nn, hCcomp_bd⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)),
        eLpNorm (Fcomp x) 2 μw
          ≤ ENNReal.ofReal C * eLpNorm (compAtom x.2.2.2) 2 μw := by
    refine ⟨∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
        (h_comp_data x (Finset.mem_univ x)).2.choose, ?_, ?_⟩
    · exact Finset.sum_nonneg
        (fun x _ => (h_comp_data x (Finset.mem_univ x)).2.choose_spec.1)
    · intro x _
      refine (h_comp_data x (Finset.mem_univ x)).2.choose_spec.2.trans ?_
      refine mul_le_mul_left ?_ _
      refine ENNReal.ofReal_le_ofReal ?_
      exact Finset.single_le_sum
        (f := fun x => (h_comp_data x (Finset.mem_univ x)).2.choose)
        (fun x _ => (h_comp_data x (Finset.mem_univ x)).2.choose_spec.1)
        (Finset.mem_univ x)
  obtain ⟨Cpart, hCpart_nn, hCpart_bd⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)),
        eLpNorm (Fpart x) 2 μw
          ≤ ENNReal.ofReal C * eLpNorm (partAtom (x.2.2.2, l)) 2 μw := by
    refine ⟨∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
        (h_part_data x (Finset.mem_univ x)).2.choose, ?_, ?_⟩
    · exact Finset.sum_nonneg
        (fun x _ => (h_part_data x (Finset.mem_univ x)).2.choose_spec.1)
    · intro x _
      refine (h_part_data x (Finset.mem_univ x)).2.choose_spec.2.trans ?_
      refine mul_le_mul_left ?_ _
      refine ENNReal.ofReal_le_ofReal ?_
      exact Finset.single_le_sum
        (f := fun x => (h_part_data x (Finset.mem_univ x)).2.choose)
        (fun x _ => (h_part_data x (Finset.mem_univ x)).2.choose_spec.1)
        (Finset.mem_univ x)
  -- Bound on the chart-component group `eLpNorm`.
  have h_comp_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
        ≤ ENNReal.ofReal (Ccomp * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              eLpNorm (compAtom p) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fcomp compAtom
      (fun x => x.2.2.2) (fun x _ => Finset.mem_univ _)
      Ccomp hCcomp_nn
      (fun x hx => by rw [← hμw_def]; exact (h_comp_data x hx).1)
      (fun x hx => by rw [← hμw_def]; exact hCcomp_bd x hx)
  -- Bound on the chart-partial group `eLpNorm`.
  have h_part_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fpart x y) 2 μw
        ≤ ENNReal.ofReal (Cpart * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ pl : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              eLpNorm (partAtom pl) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fpart partAtom
      (fun x => (x.2.2.2, l)) (fun x _ => Finset.mem_univ _)
      Cpart hCpart_nn
      (fun x hx => by rw [← hμw_def]; exact (h_part_data x hx).1)
      (fun x hx => by rw [← hμw_def]; exact hCpart_bd x hx)
  -- Identify the two single-product sums with the two nested-sum groups.
  have h_comp_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fcomp x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fpart x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M)
                      g r s α P₀ l P Q k p) y *
                  (partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  -- The chart-partial index sum on the right is the chart-partial atom family.
  have h_part_atom_eq : ∑ pl : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), eLpNorm (partAtom pl) 2 μw
      = ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α p l' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [Fintype.sum_prod_type]
  -- Headline constant: the larger of the two group constants.
  refine ⟨max
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card),
    le_trans (by positivity) (le_max_left _ _), ?_⟩
  -- Abbreviation for the headline constant.
  set Cmax : ℝ := max
      (Ccomp * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
      (Cpart * (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
    with hCmax_def
  -- Bound on the chart-component group, in the distinct-atom-sum form.
  have hcomp : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          eLpNorm ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            μw := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  -- Bound on the chart-partial group, in the distinct-atom-sum form.
  have hpart : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, Fpart x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M) g r s h_atlas i α p l' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _
  -- Weighted-`L²` membership of the two groups, for the triangle inequality.
  have h_comp_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw :=
    memLp_finset_sum _ (fun x hx => (h_comp_data x hx).1)
  have h_part_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fpart x y) 2 μw :=
    memLp_finset_sum _ (fun x hx => (h_part_data x hx).1)
  -- Unfold the limit object into its two groups, bridge to single-product sums.
  unfold weightedGradCoeffDivLimit
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p) y *
                    (partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
                      EuclN → ℝ) y)
      = (fun y => (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y)
          + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
              Fpart x y) := by
    funext y
    rw [← congrFun h_comp_eq y, ← congrFun h_part_eq y]
  rw [h_bridge]
  -- Triangle inequality, then the two group bounds, then distribute.
  calc
    eLpNorm (fun y => (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fcomp x y)
        + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
            Fpart x y) 2 μw
        ≤ eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
          + eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fpart x y) 2 μw :=
        eLpNorm_add_le h_comp_memLp.1 h_part_memLp.1 (by norm_num)
    _ ≤ ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            ∑ l' : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                μw) :=
        add_le_add hcomp hpart
    _ = ENNReal.ofReal Cmax *
          ((∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                μw)
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit (I := I) (M := M)
                      g r s h_atlas i α p l' :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) 2 μw)) := by
      rw [mul_add]

end LowerOrderENormBounds

/-! ## Uniform-constant restatements

The two headline bounds above produce, per eigenbasis index `i`, a nonnegative
constant `C`. A downstream bounded-operator argument over the whole eigenbasis
needs the constant *uniform* — one `C` serving every `i`. The constants are
finite sums / maxima of per-summand sup constants of the `i`-free `C^∞` factors
over the compact partition-of-unity kernel, so the uniform restatement is
provable: the witness construction is hoisted before the `∀ i`.

The eigenvector index `i` is **not** a section variable here, so each restatement
carries its own `∀ i`. -/

section LowerOrderENormBoundsUniform

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)

/-- A constant-uniform form of the per-summand bound: for a `C^∞`-on-the-chart-
target coefficient `c`, a single nonnegative constant `C` controls the `eLpNorm`
of the indicator-cut product `(chartPouKernel α).indicator c · G` for *every*
weighted-`MemLp` function `G` that vanishes almost everywhere (weighted) off the
compact partition-of-unity kernel. The constant is the coefficient's sup over
the kernel, independent of `G`. -/
private lemma eLpNorm_indicatorFactor_mul_atom_le_uniform
    (g : SmoothRiemannianMetric I M) (α : M) {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ G : EuclN → ℝ,
        MemLp G 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) →
        (∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)),
          y ∉ chartPouKernel (I := I) (M := M) α → G y = 0) →
        MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α) c y *
            G y) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ∧
          eLpNorm (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              c y * G y) 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
            ≤ ENNReal.ofReal C *
              eLpNorm G 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_weighted_contDiffOn_mul_le_uniform
    (I := I) (M := M) g α hc
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  refine ⟨C, hC_nn, fun G hG hG_zero => ?_⟩
  have h_prod_eq : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
        c y * G y) =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)] (fun y => c y * G y) := by
    filter_upwards [hG_zero] with y hy
    by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK, mul_zero, mul_zero]
  have h_mul_memLp : MemLp (fun y => c y * G y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    memLp_weighted_contDiffOn_mul (I := I) (M := M) g α hc
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_measurableSet (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      hG hG_zero
  refine ⟨h_mul_memLp.ae_eq h_prod_eq.symm, ?_⟩
  rw [eLpNorm_congr_ae h_prod_eq]
  exact hC_bd G hG hG_zero

/-- **Uniform-constant `eLpNorm` bound for the lower-order rotation value
coefficient limit.** The constant-uniform form of
`eLpNorm_covLowerOrderRotationValueCoeffLimit_le`: a single nonnegative constant
`C` serves every eigenbasis index `i`. The per-`i` bound's constant is the larger
of two finite sums of the per-summand sup constants of the `i`-free `C^∞` factors
`valuePartialFactor` / `valueComponentFactor` over the compact partition-of-unity
kernel; that constant does not depend on `i` and is hoisted before the `∀ i`. -/
theorem eLpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
            g r s h_atlas i α P₀ : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ((∑ P : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit (I := I) (M := M)
                      g r s h_atlas i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ p : TensorCompIdx (E := E) r s,
                  eLpNorm ((componentLpLimit (I := I) (M := M)
                      g r s h_atlas i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- Per-summand uniform constants — `i`-free.
  choose CpartF hCpartF_nn hCpartF using
    (fun x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
      eLpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) g α
        (valuePartialFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2))
  choose CcompF hCcompF_nn hCcompF using
    (fun x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s =>
      eLpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) g α
        (valueComponentFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))
  -- The uniform headline constant — the larger of the two group constants.
  refine ⟨max
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), CpartF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E))).card)
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, CcompF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card),
    le_trans (mul_nonneg (Finset.sum_nonneg (fun x _ => hCpartF_nn x))
      (by positivity)) (le_max_left _ _), fun i => ?_⟩
  -- Abbreviations for the two distinct atom families.
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pk y =>
    ((partialLpLimit (I := I) (M := M) g r s h_atlas i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set compAtom : TensorCompIdx (E := E) r s → EuclN → ℝ := fun p y =>
    ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  -- The chart-partial group, as a single sum over `(P, Q, k, l)`.
  set Fpart : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s h_atlas i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  -- The chart-component group, as a single sum over `(P, Q, k, l, p)`.
  set Fcomp : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y *
        ((componentLpLimit (I := I) (M := M) g r s h_atlas i α x.2.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  -- The per-summand membership / bound for the chart-partial group, this `i`.
  have h_part_data : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      MemLp (Fpart x) 2 μw ∧
        eLpNorm (Fpart x) 2 μw
          ≤ ENNReal.ofReal (CpartF x) * eLpNorm (partAtom (x.1, x.2.2.1)) 2 μw :=
    fun x => hCpartF x _
      (partialLpLimit_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.1 x.2.2.1)
      (partialLpLimit_ae_zero_off_chartPouKernel_weighted (I := I) (M := M)
        g r s h_atlas i α x.1 x.2.2.1)
  -- The per-summand membership / bound for the chart-component group, this `i`.
  have h_comp_data : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s,
      MemLp (Fcomp x) 2 μw ∧
        eLpNorm (Fcomp x) 2 μw
          ≤ ENNReal.ofReal (CcompF x) * eLpNorm (compAtom x.2.2.2.2) 2 μw :=
    fun x => hCcompF x _
      (componentLpLimit_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2.2)
      (componentLpLimit_ae_zero_off_chartPouKernel_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2.2)
  -- Each per-summand constant is dominated by the corresponding sum.
  have hCpart_bd : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      eLpNorm (Fpart x) 2 μw
        ≤ ENNReal.ofReal (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), CpartF x) *
          eLpNorm (partAtom (x.1, x.2.2.1)) 2 μw := by
    intro x
    refine (h_part_data x).2.trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCpartF_nn k) (Finset.mem_univ x)
  have hCcomp_bd : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s,
      eLpNorm (Fcomp x) 2 μw
        ≤ ENNReal.ofReal (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CcompF x) *
          eLpNorm (compAtom x.2.2.2.2) 2 μw := by
    intro x
    refine (h_comp_data x).2.trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCcompF_nn k) (Finset.mem_univ x)
  -- Bound on the chart-partial group `eLpNorm`.
  have h_part_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), Fpart x y) 2 μw
        ≤ ENNReal.ofReal ((∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), CpartF x) * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              eLpNorm (partAtom pk) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fpart partAtom
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      (∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), CpartF x)
      (Finset.sum_nonneg (fun x _ => hCpartF_nn x))
      (fun x _ => by rw [← hμw_def]; exact (h_part_data x).1)
      (fun x _ => by rw [← hμw_def]; exact hCpart_bd x)
  -- Bound on the chart-component group `eLpNorm`.
  have h_comp_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          Fcomp x y) 2 μw
        ≤ ENNReal.ofReal ((∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CcompF x)
            * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              eLpNorm (compAtom p) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fcomp compAtom
      (fun x => x.2.2.2.2) (fun x _ => Finset.mem_univ _)
      (∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, CcompF x)
      (Finset.sum_nonneg (fun x _ => hCcompF_nn x))
      (fun x _ => by rw [← hμw_def]; exact (h_comp_data x).1)
      (fun x _ => by rw [← hμw_def]; exact hCcomp_bd x)
  -- Identify the two single-product sums with the two nested-sum groups.
  have h_part_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), Fpart x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_comp_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, Fcomp x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                      EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  -- The chart-partial index sum is the chart-partial atom family.
  have h_part_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), eLpNorm (partAtom pk) 2 μw
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [Fintype.sum_prod_type]
  -- Abbreviation for the headline constant.
  set Cmax : ℝ := max
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), CpartF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E))).card)
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, CcompF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
    with hCmax_def
  -- Bound on the chart-partial group, in the distinct-atom-sum form.
  have hpart : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E), Fpart x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  -- Bound on the chart-component group, in the distinct-atom-sum form.
  have hcomp : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
        Fcomp x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          eLpNorm ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            μw := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _
  -- Weighted-`L²` membership of the two groups, for the triangle inequality.
  have h_part_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), Fpart x y) 2 μw :=
    memLp_finset_sum _ (fun x _ => (h_part_data x).1)
  have h_comp_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      Fcomp x y) 2 μw :=
    memLp_finset_sum _ (fun x _ => (h_comp_data x).1)
  -- Unfold the limit object into its two groups, bridge to single-product sums.
  unfold covLowerOrderRotationValueCoeffLimit
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (valueComponentFactor (I := I) (M := M)
                          g r s α P₀ P Q k l p) y *
                      (componentLpLimit (I := I) (M := M)
                        g r s h_atlas i α p : EuclN → ℝ) y)
      = (fun y => (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), Fpart x y)
          + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fcomp x y) := by
    funext y
    rw [← congrFun h_part_eq y, ← congrFun h_comp_eq y]
  rw [h_bridge]
  -- Triangle inequality, then the two group bounds, then distribute.
  calc
    eLpNorm (fun y => (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), Fpart x y)
        + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
            × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
        ≤ eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × Fin (Module.finrank ℝ E), Fpart x y) 2 μw
          + eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
              Fcomp x y) 2 μw :=
        eLpNorm_add_le h_part_memLp.1 h_comp_memLp.1 (by norm_num)
    _ ≤ ENNReal.ofReal Cmax *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                μw)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw) :=
        add_le_add hpart hcomp
    _ = ENNReal.ofReal Cmax *
          ((∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit (I := I) (M := M)
                    g r s h_atlas i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  μw)
            + (∑ p : TensorCompIdx (E := E) r s,
                eLpNorm ((componentLpLimit (I := I) (M := M)
                    g r s h_atlas i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  μw)) := by
      rw [mul_add]

/-- **Uniform-constant `eLpNorm` bound for the chart-density-weighted lower-order
gradient divergence coefficient limit.** The constant-uniform form of
`eLpNorm_weightedGradCoeffDivLimit_le`: a single nonnegative constant `C` serves
every eigenbasis index `i`. The per-`i` bound's constant is the larger of two
finite sums of the per-summand sup constants of the `i`-free `C^∞` factor
`weightedGradFactor` (or its chart-Euclidean partial) over the compact
partition-of-unity kernel; that constant does not depend on `i` and is hoisted
before the `∀ i`. -/
theorem eLpNorm_weightedGradCoeffDivLimit_le_uniform
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (weightedGradCoeffDivLimit (I := I) (M := M)
            g r s h_atlas i α P₀ l : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ((∑ p : TensorCompIdx (E := E) r s,
                eLpNorm ((componentLpLimit (I := I) (M := M)
                    g r s h_atlas i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ p : TensorCompIdx (E := E) r s,
                  ∑ l' : Fin (Module.finrank ℝ E),
                    eLpNorm ((partialLpLimit (I := I) (M := M)
                        g r s h_atlas i α p l' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- Per-summand uniform constants — `i`-free.
  choose CcompF hCcompF_nn hCcompF using
    (fun x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s =>
      eLpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) g α
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2))
  choose CpartF hCpartF_nn hCpartF using
    (fun x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s =>
      eLpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) g α
        (weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2))
  -- The uniform headline constant — the larger of the two group constants.
  refine ⟨max
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CcompF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card)
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CpartF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card),
    le_trans (mul_nonneg (Finset.sum_nonneg (fun x _ => hCcompF_nn x))
      (by positivity)) (le_max_left _ _), fun i => ?_⟩
  -- Abbreviations for the two distinct atom families.
  set compAtom : TensorCompIdx (E := E) r s → EuclN → ℝ := fun p y =>
    ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pl y =>
    ((partialLpLimit (I := I) (M := M) g r s h_atlas i α pl.1 pl.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  -- The chart-component group, as a single sum over `(P, Q, k, p)`.
  set Fcomp : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y *
        ((componentLpLimit (I := I) (M := M) g r s h_atlas i α x.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  -- The chart-partial group, as a single sum over `(P, Q, k, p)`.
  set Fpart : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M)
            g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s h_atlas i α x.2.2.2 l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  -- The per-summand membership / bound for the chart-component group, this `i`.
  have h_comp_data : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      MemLp (Fcomp x) 2 μw ∧
        eLpNorm (Fcomp x) 2 μw
          ≤ ENNReal.ofReal (CcompF x) * eLpNorm (compAtom x.2.2.2) 2 μw :=
    fun x => hCcompF x _
      (componentLpLimit_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2)
      (componentLpLimit_ae_zero_off_chartPouKernel_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2)
  -- The per-summand membership / bound for the chart-partial group, this `i`.
  have h_part_data : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      MemLp (Fpart x) 2 μw ∧
        eLpNorm (Fpart x) 2 μw
          ≤ ENNReal.ofReal (CpartF x) * eLpNorm (partAtom (x.2.2.2, l)) 2 μw :=
    fun x => hCpartF x _
      (partialLpLimit_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2 l)
      (partialLpLimit_ae_zero_off_chartPouKernel_weighted (I := I) (M := M)
        g r s h_atlas i α x.2.2.2 l)
  -- Each per-summand constant is dominated by the corresponding sum.
  have hCcomp_bd : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      eLpNorm (Fcomp x) 2 μw
        ≤ ENNReal.ofReal (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, CcompF x) *
          eLpNorm (compAtom x.2.2.2) 2 μw := by
    intro x
    refine (h_comp_data x).2.trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCcompF_nn k) (Finset.mem_univ x)
  have hCpart_bd : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      eLpNorm (Fpart x) 2 μw
        ≤ ENNReal.ofReal (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, CpartF x) *
          eLpNorm (partAtom (x.2.2.2, l)) 2 μw := by
    intro x
    refine (h_part_data x).2.trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCpartF_nn k) (Finset.mem_univ x)
  -- Bound on the chart-component group `eLpNorm`.
  have h_comp_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
        ≤ ENNReal.ofReal ((∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, CcompF x) * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              eLpNorm (compAtom p) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fcomp compAtom
      (fun x => x.2.2.2) (fun x _ => Finset.mem_univ _)
      (∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CcompF x)
      (Finset.sum_nonneg (fun x _ => hCcompF_nn x))
      (fun x _ => by rw [← hμw_def]; exact (h_comp_data x).1)
      (fun x _ => by rw [← hμw_def]; exact hCcomp_bd x)
  -- Bound on the chart-partial group `eLpNorm`.
  have h_part_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fpart x y) 2 μw
        ≤ ENNReal.ofReal ((∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, CpartF x) * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ pl : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              eLpNorm (partAtom pl) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fpart partAtom
      (fun x => (x.2.2.2, l)) (fun x _ => Finset.mem_univ _)
      (∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CpartF x)
      (Finset.sum_nonneg (fun x _ => hCpartF_nn x))
      (fun x _ => by rw [← hμw_def]; exact (h_part_data x).1)
      (fun x _ => by rw [← hμw_def]; exact hCpart_bd x)
  -- Identify the two single-product sums with the two nested-sum groups.
  have h_comp_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fcomp x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fpart x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M)
                      g r s α P₀ l P Q k p) y *
                  (partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
                    EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  -- The chart-partial index sum is the chart-partial atom family.
  have h_part_atom_eq : ∑ pl : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), eLpNorm (partAtom pl) 2 μw
      = ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α p l' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [Fintype.sum_prod_type]
  -- Abbreviation for the headline constant.
  set Cmax : ℝ := max
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CcompF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card)
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CpartF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card)
    with hCmax_def
  -- Bound on the chart-component group, in the distinct-atom-sum form.
  have hcomp : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          eLpNorm ((componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            μw := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  -- Bound on the chart-partial group, in the distinct-atom-sum form.
  have hpart : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, Fpart x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M) g r s h_atlas i α p l' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _
  -- Weighted-`L²` membership of the two groups, for the triangle inequality.
  have h_comp_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw :=
    memLp_finset_sum _ (fun x _ => (h_comp_data x).1)
  have h_part_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fpart x y) 2 μw :=
    memLp_finset_sum _ (fun x _ => (h_part_data x).1)
  -- Unfold the limit object into its two groups, bridge to single-product sums.
  unfold weightedGradCoeffDivLimit
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit (I := I) (M := M) g r s h_atlas i α p :
                    EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p) y *
                    (partialLpLimit (I := I) (M := M) g r s h_atlas i α p l :
                      EuclN → ℝ) y)
      = (fun y => (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y)
          + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
              Fpart x y) := by
    funext y
    rw [← congrFun h_comp_eq y, ← congrFun h_part_eq y]
  rw [h_bridge]
  -- Triangle inequality, then the two group bounds, then distribute.
  calc
    eLpNorm (fun y => (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fcomp x y)
        + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
            Fpart x y) 2 μw
        ≤ eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
          + eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fpart x y) 2 μw :=
        eLpNorm_add_le h_comp_memLp.1 h_part_memLp.1 (by norm_num)
    _ ≤ ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            ∑ l' : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                μw) :=
        add_le_add hcomp hpart
    _ = ENNReal.ofReal Cmax *
          ((∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                  g r s h_atlas i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                μw)
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit (I := I) (M := M)
                      g r s h_atlas i α p l' :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) 2 μw)) := by
      rw [mul_add]

end LowerOrderENormBoundsUniform

/-! ## Chart-locality-free uniform restatements

The two uniform bounds above carry the chart-locality predicate `h_atlas`. The
chart-locality-free twins below re-key every chart-partial / chart-component atom
onto the intrinsic-compactness eigenvector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic g r s) i`,
through the `_unconditional` limit objects
`covLowerOrderRotationValueCoeffLimit_unconditional` and
`weightedGradCoeffDivLimit_unconditional`. Both objects have the same two-group,
finite-nested-sum shape as their `h_atlas` counterparts, with the two atom
families replaced by the chart-locality-free atoms
`partialLpLimit_unconditional` and `componentLpLimit_unconditional`.

The two chart-component atom facts (weighted-`L²` membership and weighted
off-kernel vanishing) are the chart-locality-free atom twins
`componentLpLimit_memLp_weighted_unconditional` /
`componentLpLimit_ae_zero_off_chartPouKernel_weighted_unconditional` recorded
alongside the underlying weighted-measure infrastructure. The two chart-partial
atom facts are recorded here, mirroring the `h_atlas` atom twins: the
chart-partial atom `partialLpLimit_unconditional` is the `i.fst.val`-rescaling of
the chart-locality-free weak chart partial `eigenvectorChartWeakPartial_unconditional`,
whose weighted off-kernel vanishing comes from the chart-locality-free
`eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel_unconditional`.

The proofs are otherwise verbatim copies of the `h_atlas` uniform proofs, with
the four atom citations swapped for their chart-locality-free twins. -/

section LowerOrderENormBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

/-! ### Chart-locality-free chart-partial atom facts

The chart-partial atom `partialLpLimit_unconditional g r s i α P k` is the
`i.fst.val`-rescaling of the chart-locality-free weak chart partial
`eigenvectorChartWeakPartial_unconditional`. -/

/-- **Chart-locality-free weighted off-kernel vanishing of the chart-partial atom.**
Chart-locality-free twin of `partialLpLimit_ae_zero_off_chartPouKernel_weighted`:
the chart-partial atom `partialLpLimit_unconditional g r s i α P k` vanishes
almost everywhere — for the chart-pulled weighted measure restricted to the chart
target — off the compact partition-of-unity kernel `chartPouKernel α`. The atom is
`i.fst.val` times the chart-locality-free weak chart partial
`eigenvectorChartWeakPartial_unconditional`, which is a.e. zero on the open
complement of the kernel inside the chart target
(`eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel_unconditional`). -/
lemma partialLpLimit_ae_zero_off_chartPouKernel_weighted_unconditional
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  -- `partialLpLimit_unconditional = i.fst.val • eigenvectorChartWeakPartial_unconditional`.
  have h_smul : (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y) := by
    rw [partialLpLimit_unconditional, eigenvectorChartWeakPartial_unconditional]
    exact Lp.coeFn_smul i.fst.val _
  -- The chart-locality-free weak chart partial vanishes a.e. on the open
  -- complement of the kernel inside the chart target.
  have h_weak_sdiff := eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel_unconditional
    (I := I) (M := M) g r s i α P k
  have hKc_meas : MeasurableSet
      (chartPouKernel (I := I) (M := M) α)ᶜ :=
    (chartPouKernel_measurableSet (I := I) (M := M) α).compl
  -- Recast that `=ᵐ` on `Ω \ kernel` as an a.e. implication on `Ω`.
  have h_weak_impl : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y = 0 := by
    refine (ae_restrict_iff' hKc_meas).mp ?_
    rw [Measure.restrict_restrict hKc_meas]
    have h_inter : (chartPouKernel (I := I) (M := M) α)ᶜ ∩
        chartTargetEuclid (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α := by
      rw [Set.diff_eq, Set.inter_comm]
    rw [h_inter]
    filter_upwards [h_weak_sdiff] with y hy using hy
  -- Transfer from the plain restricted volume to the weighted measure.
  have h_weak_w : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y = 0 :=
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α).ae_le h_weak_impl
  -- Transfer the `i.fst.val`-rescaling identity to the weighted measure.
  have h_smul_w : (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y) :=
    (chartPulledWeightedMeasure_restrict_absolutelyContinuous (I := I) (M := M)
      g α).ae_le h_smul
  filter_upwards [h_smul_w, h_weak_w] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

/-- **Chart-locality-free weighted-`L²` membership of the chart-partial atom.**
Chart-locality-free twin of `partialLpLimit_memLp_weighted`: the chart-partial
atom `partialLpLimit_unconditional g r s i α P k` is `MemLp 2` for the chart-pulled
weighted measure restricted to the chart target. It is an
`Lp ℝ 2 (chartL2Measure α)` element (hence `MemLp 2` of the plain restricted
volume) that vanishes almost everywhere off the compact partition-of-unity kernel,
so `memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact`
applies. -/
lemma partialLpLimit_memLp_weighted_unconditional
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- The atom is `MemLp 2` of the plain chart `L²` reference measure.
  have h_plain : MemLp (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
      g r s i α P k :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) 2
      (chartL2Measure (I := I) (M := M) α) := Lp.memLp _
  -- `partialLpLimit_unconditional = i.fst.val • eigenvectorChartWeakPartial_unconditional`.
  have h_smul : (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y) := by
    rw [partialLpLimit_unconditional, eigenvectorChartWeakPartial_unconditional]
    exact Lp.coeFn_smul i.fst.val _
  -- The chart-locality-free weak chart partial vanishes a.e. off the kernel.
  have h_weak_sdiff := eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel_unconditional
    (I := I) (M := M) g r s i α P k
  have hKc_meas : MeasurableSet
      (chartPouKernel (I := I) (M := M) α)ᶜ :=
    (chartPouKernel_measurableSet (I := I) (M := M) α).compl
  have h_weak_impl : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y = 0 := by
    refine (ae_restrict_iff' hKc_meas).mp ?_
    rw [Measure.restrict_restrict hKc_meas]
    have h_inter : (chartPouKernel (I := I) (M := M) α)ᶜ ∩
        chartTargetEuclid (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α := by
      rw [Set.diff_eq, Set.inter_comm]
    rw [h_inter]
    filter_upwards [h_weak_sdiff] with y hy using hy
  -- The atom vanishes a.e. off the kernel for the plain chart `L²` measure.
  have h_atom_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit_unconditional (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    filter_upwards [h_smul, h_weak_impl] with y hy hy_zero hyK
    rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    h_atom_zero h_plain

/-! ### The two uniform bounds, chart-locality-free -/

/-- **Chart-locality-free uniform-constant `eLpNorm` bound for the lower-order
rotation value coefficient limit.** Chart-locality-free twin of
`eLpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform`: a single nonnegative
constant `C` serves every eigenbasis index `i`, with every chart-partial /
chart-component atom re-keyed onto the intrinsic-compactness eigenvector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic g r s) i`,
through the `_unconditional` limit object
`covLowerOrderRotationValueCoeffLimit_unconditional`. The per-`i` bound's constant
is the larger of two finite sums of the per-summand sup constants of the `i`-free
`C^∞` factors `valuePartialFactor` / `valueComponentFactor` over the compact
partition-of-unity kernel; that constant does not depend on `i` and is hoisted
before the `∀ i`. -/
theorem eLpNorm_covLowerOrderRotationValueCoeffLimit_le_uniform_unconditional
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (covLowerOrderRotationValueCoeffLimit_unconditional (I := I) (M := M)
            g r s i α P₀ : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ((∑ P : TensorCompIdx (E := E) r s,
                ∑ k : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                      g r s i α P k :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ p : TensorCompIdx (E := E) r s,
                  eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
                      g r s i α p :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                    ((chartPulledWeightedMeasure (I := I) g α).restrict
                      (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- Per-summand uniform constants — `i`-free.
  choose CpartF hCpartF_nn hCpartF using
    (fun x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
      eLpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) g α
        (valuePartialFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2))
  choose CcompF hCcompF_nn hCcompF using
    (fun x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s =>
      eLpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) g α
        (valueComponentFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))
  -- The uniform headline constant — the larger of the two group constants.
  refine ⟨max
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), CpartF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E))).card)
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, CcompF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card),
    le_trans (mul_nonneg (Finset.sum_nonneg (fun x _ => hCpartF_nn x))
      (by positivity)) (le_max_left _ _), fun i => ?_⟩
  -- Abbreviations for the two distinct atom families.
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pk y =>
    ((partialLpLimit_unconditional (I := I) (M := M) g r s i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  set compAtom : TensorCompIdx (E := E) r s → EuclN → ℝ := fun p y =>
    ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  -- The chart-partial group, as a single sum over `(P, Q, k, l)`.
  set Fpart : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valuePartialFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit_unconditional (I := I) (M := M) g r s i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  -- The chart-component group, as a single sum over `(P, Q, k, l, p)`.
  set Fcomp : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (valueComponentFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) y *
        ((componentLpLimit_unconditional (I := I) (M := M)
            g r s i α x.2.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  -- The per-summand membership / bound for the chart-partial group, this `i`.
  have h_part_data : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      MemLp (Fpart x) 2 μw ∧
        eLpNorm (Fpart x) 2 μw
          ≤ ENNReal.ofReal (CpartF x) * eLpNorm (partAtom (x.1, x.2.2.1)) 2 μw :=
    fun x => hCpartF x _
      (partialLpLimit_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α x.1 x.2.2.1)
      (partialLpLimit_ae_zero_off_chartPouKernel_weighted_unconditional
        (I := I) (M := M) g r s i α x.1 x.2.2.1)
  -- The per-summand membership / bound for the chart-component group, this `i`.
  have h_comp_data : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s,
      MemLp (Fcomp x) 2 μw ∧
        eLpNorm (Fcomp x) 2 μw
          ≤ ENNReal.ofReal (CcompF x) * eLpNorm (compAtom x.2.2.2.2) 2 μw :=
    fun x => hCcompF x _
      (componentLpLimit_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α x.2.2.2.2)
      (componentLpLimit_ae_zero_off_chartPouKernel_weighted_unconditional
        (I := I) (M := M) g r s i α x.2.2.2.2)
  -- Each per-summand constant is dominated by the corresponding sum.
  have hCpart_bd : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      eLpNorm (Fpart x) 2 μw
        ≤ ENNReal.ofReal (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), CpartF x) *
          eLpNorm (partAtom (x.1, x.2.2.1)) 2 μw := by
    intro x
    refine (h_part_data x).2.trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCpartF_nn k) (Finset.mem_univ x)
  have hCcomp_bd : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s,
      eLpNorm (Fcomp x) 2 μw
        ≤ ENNReal.ofReal (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CcompF x) *
          eLpNorm (compAtom x.2.2.2.2) 2 μw := by
    intro x
    refine (h_comp_data x).2.trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCcompF_nn k) (Finset.mem_univ x)
  -- Bound on the chart-partial group `eLpNorm`.
  have h_part_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), Fpart x y) 2 μw
        ≤ ENNReal.ofReal ((∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), CpartF x) * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              eLpNorm (partAtom pk) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fpart partAtom
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      (∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), CpartF x)
      (Finset.sum_nonneg (fun x _ => hCpartF_nn x))
      (fun x _ => by rw [← hμw_def]; exact (h_part_data x).1)
      (fun x _ => by rw [← hμw_def]; exact hCpart_bd x)
  -- Bound on the chart-component group `eLpNorm`.
  have h_comp_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
          Fcomp x y) 2 μw
        ≤ ENNReal.ofReal ((∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CcompF x)
            * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              eLpNorm (compAtom p) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fcomp compAtom
      (fun x => x.2.2.2.2) (fun x _ => Finset.mem_univ _)
      (∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, CcompF x)
      (Finset.sum_nonneg (fun x _ => hCcompF_nn x))
      (fun x _ => by rw [← hμw_def]; exact (h_comp_data x).1)
      (fun x _ => by rw [← hμw_def]; exact hCcomp_bd x)
  -- Identify the two single-product sums with the two nested-sum groups.
  have h_part_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), Fpart x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit_unconditional (I := I) (M := M)
                    g r s i α P k : EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  have h_comp_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, Fcomp x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (valueComponentFactor (I := I) (M := M)
                        g r s α P₀ P Q k l p) y *
                    (componentLpLimit_unconditional (I := I) (M := M)
                      g r s i α p : EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  -- The chart-partial index sum is the chart-partial atom family.
  have h_part_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), eLpNorm (partAtom pk) 2 μw
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [Fintype.sum_prod_type]
  -- Abbreviation for the headline constant.
  set Cmax : ℝ := max
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), CpartF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E))).card)
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, CcompF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
    with hCmax_def
  -- Bound on the chart-partial group, in the distinct-atom-sum form.
  have hpart : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E), Fpart x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  -- Bound on the chart-component group, in the distinct-atom-sum form.
  have hcomp : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
        Fcomp x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            μw := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _
  -- Weighted-`L²` membership of the two groups, for the triangle inequality.
  have h_part_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), Fpart x y) 2 μw :=
    memLp_finset_sum _ (fun x _ => (h_part_data x).1)
  have h_comp_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      Fcomp x y) 2 μw :=
    memLp_finset_sum _ (fun x _ => (h_comp_data x).1)
  -- Unfold the limit object into its two groups, bridge to single-product sums.
  unfold covLowerOrderRotationValueCoeffLimit_unconditional
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (valuePartialFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit_unconditional (I := I) (M := M)
                    g r s i α P k : EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ p : TensorCompIdx (E := E) r s,
                    Set.indicator (chartPouKernel (I := I) (M := M) α)
                        (valueComponentFactor (I := I) (M := M)
                          g r s α P₀ P Q k l p) y *
                      (componentLpLimit_unconditional (I := I) (M := M)
                        g r s i α p : EuclN → ℝ) y)
      = (fun y => (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E), Fpart x y)
          + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fcomp x y) := by
    funext y
    rw [← congrFun h_part_eq y, ← congrFun h_comp_eq y]
  rw [h_bridge]
  -- Triangle inequality, then the two group bounds, then distribute.
  calc
    eLpNorm (fun y => (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), Fpart x y)
        + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
            × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
        ≤ eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × Fin (Module.finrank ℝ E), Fpart x y) 2 μw
          + eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
              Fcomp x y) 2 μw :=
        eLpNorm_add_le h_part_memLp.1 h_comp_memLp.1 (by norm_num)
    _ ≤ ENNReal.ofReal Cmax *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                μw)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw) :=
        add_le_add hpart hcomp
    _ = ENNReal.ofReal Cmax *
          ((∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                    g r s i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  μw)
            + (∑ p : TensorCompIdx (E := E) r s,
                eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
                    g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  μw)) := by
      rw [mul_add]

/-- **Chart-locality-free uniform-constant `eLpNorm` bound for the
chart-density-weighted lower-order gradient divergence coefficient limit.**
Chart-locality-free twin of `eLpNorm_weightedGradCoeffDivLimit_le_uniform`: a
single nonnegative constant `C` serves every eigenbasis index `i`, with every
chart-component / chart-partial atom re-keyed onto the intrinsic-compactness
eigenvector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic g r s) i`,
through the `_unconditional` limit object `weightedGradCoeffDivLimit_unconditional`.
The per-`i` bound's constant is the larger of two finite sums of the per-summand
sup constants of the `i`-free `C^∞` factor `weightedGradFactor` (or its
chart-Euclidean partial) over the compact partition-of-unity kernel; that constant
does not depend on `i` and is hoisted before the `∀ i`. -/
theorem eLpNorm_weightedGradCoeffDivLimit_le_uniform_unconditional
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (weightedGradCoeffDivLimit_unconditional (I := I) (M := M)
            g r s i α P₀ l : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ((∑ p : TensorCompIdx (E := E) r s,
                eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
                    g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                  ((chartPulledWeightedMeasure (I := I) g α).restrict
                    (chartTargetEuclid (I := I) (M := M) α)))
              + (∑ p : TensorCompIdx (E := E) r s,
                  ∑ l' : Fin (Module.finrank ℝ E),
                    eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                        g r s i α p l' :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                      EuclN → ℝ) 2
                      ((chartPulledWeightedMeasure (I := I) g α).restrict
                        (chartTargetEuclid (I := I) (M := M) α)))) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- Per-summand uniform constants — `i`-free.
  choose CcompF hCcompF_nn hCcompF using
    (fun x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s =>
      eLpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) g α
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2))
  choose CpartF hCpartF_nn hCpartF using
    (fun x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s =>
      eLpNorm_indicatorFactor_mul_atom_le_uniform (I := I) (M := M) g α
        (weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2))
  -- The uniform headline constant — the larger of the two group constants.
  refine ⟨max
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CcompF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card)
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CpartF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card),
    le_trans (mul_nonneg (Finset.sum_nonneg (fun x _ => hCcompF_nn x))
      (by positivity)) (le_max_left _ _), fun i => ?_⟩
  -- Abbreviations for the two distinct atom families.
  set compAtom : TensorCompIdx (E := E) r s → EuclN → ℝ := fun p y =>
    ((componentLpLimit_unconditional (I := I) (M := M) g r s i α p :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hcompAtom_def
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pl y =>
    ((partialLpLimit_unconditional (I := I) (M := M) g r s i α pl.1 pl.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  -- The chart-component group, as a single sum over `(P, Q, k, p)`.
  set Fcomp : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (euclidPartial (E := E) l
            (weightedGradFactor (I := I) (M := M)
              g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2)) y *
        ((componentLpLimit_unconditional (I := I) (M := M)
            g r s i α x.2.2.2 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFcomp_def
  -- The chart-partial group, as a single sum over `(P, Q, k, p)`.
  set Fpart : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (weightedGradFactor (I := I) (M := M)
            g r s α P₀ l x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit_unconditional (I := I) (M := M)
            g r s i α x.2.2.2 l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hFpart_def
  -- The per-summand membership / bound for the chart-component group, this `i`.
  have h_comp_data : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      MemLp (Fcomp x) 2 μw ∧
        eLpNorm (Fcomp x) 2 μw
          ≤ ENNReal.ofReal (CcompF x) * eLpNorm (compAtom x.2.2.2) 2 μw :=
    fun x => hCcompF x _
      (componentLpLimit_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α x.2.2.2)
      (componentLpLimit_ae_zero_off_chartPouKernel_weighted_unconditional
        (I := I) (M := M) g r s i α x.2.2.2)
  -- The per-summand membership / bound for the chart-partial group, this `i`.
  have h_part_data : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      MemLp (Fpart x) 2 μw ∧
        eLpNorm (Fpart x) 2 μw
          ≤ ENNReal.ofReal (CpartF x) * eLpNorm (partAtom (x.2.2.2, l)) 2 μw :=
    fun x => hCpartF x _
      (partialLpLimit_memLp_weighted_unconditional (I := I) (M := M)
        g r s i α x.2.2.2 l)
      (partialLpLimit_ae_zero_off_chartPouKernel_weighted_unconditional
        (I := I) (M := M) g r s i α x.2.2.2 l)
  -- Each per-summand constant is dominated by the corresponding sum.
  have hCcomp_bd : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      eLpNorm (Fcomp x) 2 μw
        ≤ ENNReal.ofReal (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, CcompF x) *
          eLpNorm (compAtom x.2.2.2) 2 μw := by
    intro x
    refine (h_comp_data x).2.trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCcompF_nn k) (Finset.mem_univ x)
  have hCpart_bd : ∀ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
      eLpNorm (Fpart x) 2 μw
        ≤ ENNReal.ofReal (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, CpartF x) *
          eLpNorm (partAtom (x.2.2.2, l)) 2 μw := by
    intro x
    refine (h_part_data x).2.trans ?_
    gcongr
    exact Finset.single_le_sum (fun k _ => hCpartF_nn k) (Finset.mem_univ x)
  -- Bound on the chart-component group `eLpNorm`.
  have h_comp_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
        ≤ ENNReal.ofReal ((∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, CcompF x) * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ p : TensorCompIdx (E := E) r s,
              eLpNorm (compAtom p) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fcomp compAtom
      (fun x => x.2.2.2) (fun x _ => Finset.mem_univ _)
      (∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CcompF x)
      (Finset.sum_nonneg (fun x _ => hCcompF_nn x))
      (fun x _ => by rw [← hμw_def]; exact (h_comp_data x).1)
      (fun x _ => by rw [← hμw_def]; exact hCcomp_bd x)
  -- Bound on the chart-partial group `eLpNorm`.
  have h_part_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fpart x y) 2 μw
        ≤ ENNReal.ofReal ((∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, CpartF x) * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s)).card)
          * ∑ pl : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              eLpNorm (partAtom pl) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ Fpart partAtom
      (fun x => (x.2.2.2, l)) (fun x _ => Finset.mem_univ _)
      (∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CpartF x)
      (Finset.sum_nonneg (fun x _ => hCpartF_nn x))
      (fun x _ => by rw [← hμw_def]; exact (h_part_data x).1)
      (fun x _ => by rw [← hμw_def]; exact hCpart_bd x)
  -- Identify the two single-product sums with the two nested-sum groups.
  have h_comp_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fcomp x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit_unconditional (I := I) (M := M)
                    g r s i α p : EuclN → ℝ) y) := by
    funext y
    rw [hFcomp_def]
    simp only [Fintype.sum_prod_type]
  have h_part_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fpart x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (weightedGradFactor (I := I) (M := M)
                      g r s α P₀ l P Q k p) y *
                  (partialLpLimit_unconditional (I := I) (M := M)
                    g r s i α p l : EuclN → ℝ) y) := by
    funext y
    rw [hFpart_def]
    simp only [Fintype.sum_prod_type]
  -- The chart-partial index sum is the chart-partial atom family.
  have h_part_atom_eq : ∑ pl : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), eLpNorm (partAtom pl) 2 μw
      = ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α p l' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [Fintype.sum_prod_type]
  -- Abbreviation for the headline constant.
  set Cmax : ℝ := max
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CcompF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card)
      ((∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s, CpartF x)
        * (Finset.univ : Finset (TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s)).card)
    with hCmax_def
  -- Bound on the chart-component group, in the distinct-atom-sum form.
  have hcomp : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            μw := by
    refine h_comp_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  -- Bound on the chart-partial group, in the distinct-atom-sum form.
  have hpart : eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
        × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
        × TensorCompIdx (E := E) r s, Fpart x y) 2 μw
      ≤ ENNReal.ofReal Cmax *
        ∑ p : TensorCompIdx (E := E) r s,
          ∑ l' : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                g r s i α p l' :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [← h_part_atom_eq]
    refine h_part_bound.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _
  -- Weighted-`L²` membership of the two groups, for the triangle inequality.
  have h_comp_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw :=
    memLp_finset_sum _ (fun x _ => (h_comp_data x).1)
  have h_part_memLp : MemLp (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × TensorCompIdx (E := E) r s, Fpart x y) 2 μw :=
    memLp_finset_sum _ (fun x _ => (h_part_data x).1)
  -- Unfold the limit object into its two groups, bridge to single-product sums.
  unfold weightedGradCoeffDivLimit_unconditional
  have h_bridge : (fun y => (∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ p : TensorCompIdx (E := E) r s,
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (euclidPartial (E := E) l
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p)) y *
                  (componentLpLimit_unconditional (I := I) (M := M)
                    g r s i α p : EuclN → ℝ) y)
        + ∑ P : TensorCompIdx (E := E) r s,
            ∑ Q : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ p : TensorCompIdx (E := E) r s,
                  Set.indicator (chartPouKernel (I := I) (M := M) α)
                      (weightedGradFactor (I := I) (M := M)
                        g r s α P₀ l P Q k p) y *
                    (partialLpLimit_unconditional (I := I) (M := M)
                      g r s i α p l : EuclN → ℝ) y)
      = (fun y => (∑ x : TensorCompIdx (E := E) r s
            × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
            × TensorCompIdx (E := E) r s, Fcomp x y)
          + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
              Fpart x y) := by
    funext y
    rw [← congrFun h_comp_eq y, ← congrFun h_part_eq y]
  rw [h_bridge]
  -- Triangle inequality, then the two group bounds, then distribute.
  calc
    eLpNorm (fun y => (∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × TensorCompIdx (E := E) r s, Fcomp x y)
        + ∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
            × Fin (Module.finrank ℝ E) × TensorCompIdx (E := E) r s,
            Fpart x y) 2 μw
        ≤ eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fcomp x y) 2 μw
          + eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
              × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
              × TensorCompIdx (E := E) r s, Fpart x y) 2 μw :=
        eLpNorm_add_le h_comp_memLp.1 h_part_memLp.1 (by norm_num)
    _ ≤ ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw)
        + ENNReal.ofReal Cmax *
          (∑ p : TensorCompIdx (E := E) r s,
            ∑ l' : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                  g r s i α p l' :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                μw) :=
        add_le_add hcomp hpart
    _ = ENNReal.ofReal Cmax *
          ((∑ p : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
                  g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                μw)
            + (∑ p : TensorCompIdx (E := E) r s,
                ∑ l' : Fin (Module.finrank ℝ E),
                  eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                      g r s i α p l' :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                    EuclN → ℝ) 2 μw)) := by
      rw [mul_add]

end LowerOrderENormBoundsUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
