import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.WeightedCoeffMulENormBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedData
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.ChartComponentCutoffENormBound

/-!
# Explicit-norm `eLpNorm` bounds for three eigenvector chart limit objects

The chart-Euclidean right-hand side of the connection-Laplacian eigenvector's
weak-solution assembly is built from `C^∞`-coefficient-weighted limit objects.
Three of them are treated here:

* `crossLeftLimitComponent g r s h_atlas i α P` — the cutoff Euclidean chart
  component, at `(α, P)`, of the completion-extended covariant gradient
  `tensorCovGradL2Compl g r s` applied to the eigenvector resolvent;
* `crossRightLimitComponent g r s h_atlas i α P` — the cutoff Euclidean chart
  component, at `(α, P)`, of the `L²`-coercion `TensorH1ComplToTensorL2 g r s`
  of the eigenvector resolvent;
* `covPrincipalRotationCoeffLimit g r s h_atlas i α P₀` — a four-fold finite sum,
  over component multi-index pairs and chart directions, of the
  `chartPouKernel α`-indicator-cut `C^∞` factor `principalRotationFactor`
  against the chart-partial atom `partialLpLimit`.

This file records, for each, an explicit-constant `eLpNorm` bound for the
chart-pulled weighted measure
`μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

## Strategy

The two cross-Leibniz limits are, by definition, single cutoff Euclidean chart
components of abstract `L²` elements; their weighted `eLpNorm` bound is the
corresponding instance of the foundational
`eLpNorm_tensorL2ChartComponentCutoff_le` — the cutoff confines the component to
a compact kernel, on which the chart-density is bounded above, so the weighted
`eLpNorm` is controlled by a constant times the abstract element's norm `‖u‖`.

The principal rotation coefficient limit is a four-fold finite sum whose
summands carry an `indicator (chartPouKernel α)` cut of the `C^∞`-on-the-chart-
target factor `principalRotationFactor`; the accompanying chart-partial atom
`partialLpLimit` vanishes almost everywhere — for the weighted measure — off the
compact partition-of-unity kernel `chartPouKernel α`, so the indicator-cut
summand agrees almost everywhere with the uncut `C^∞`-factor product. The
explicit-norm bound `eLpNorm_weighted_contDiffOn_mul_le` controls that product's
`eLpNorm` by an explicit constant — the `C^∞` factor's sup over the compact
kernel — times the atom's `eLpNorm`. The triangle inequality `eLpNorm_sum_le`
over the four-fold finite sum assembles the per-summand bounds; every summation
multiplicity and every per-coefficient sup constant is folded into a single
headline constant.

## Main results

* `eLpNorm_crossLeftLimitComponent_le`
* `eLpNorm_crossRightLimitComponent_le`
* `eLpNorm_covPrincipalRotationCoeffLimit_le`

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

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section CrossRotationENormBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-! ## Headline 1 — the cross-left limit object

`crossLeftLimitComponent g r s h_atlas i α P` is, by definition, the cutoff
Euclidean chart component of the abstract `L²` element
`tensorCovGradL2Compl g r s (eigenvectorResolvent g r s h_atlas i)`. Its weighted
`eLpNorm` bound is the corresponding instance of the foundational
`eLpNorm_tensorL2ChartComponentCutoff_le`. -/

/-- **Explicit-norm `eLpNorm` bound for the cross-left limit object.** For a
closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index `i`, a
chart center `α : M`, and a component multi-index `P : CompIdx E r (s + 1)`,
there is a nonnegative constant `C` with

```
eLpNorm (crossLeftLimitComponent g r s h_atlas i α P) 2 μw
  ≤ ENNReal.ofReal C
      * ENNReal.ofReal ‖tensorCovGradL2Compl g r s (eigenvectorResolvent …)‖,
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

By definition `crossLeftLimitComponent` is the cutoff Euclidean chart component
of the abstract `L²` element `tensorCovGradL2Compl g r s
(eigenvectorResolvent g r s h_atlas i)`; the foundational
`eLpNorm_tensorL2ChartComponentCutoff_le` controls the weighted `eLpNorm` of any
cutoff chart component by an explicit constant times the abstract element's
norm. -/
theorem eLpNorm_crossLeftLimitComponent_le
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          ENNReal.ofReal ‖tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)‖ := by
  -- Unfold the limit object into a cutoff Euclidean chart component, then apply
  -- the foundational weighted `eLpNorm` bound for cutoff chart components.
  rw [crossLeftLimitComponent]
  exact eLpNorm_tensorL2ChartComponentCutoff_le (I := I) (M := M) g r (s + 1) α P
    (tensorCovGradL2Compl (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))

/-! ## Headline 2 — the cross-right limit object

`crossRightLimitComponent g r s h_atlas i α P` is, by definition, the cutoff
Euclidean chart component of the abstract `L²` element
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent g r s h_atlas i)`. Its
weighted `eLpNorm` bound is the corresponding instance of the foundational
`eLpNorm_tensorL2ChartComponentCutoff_le`. -/

/-- **Explicit-norm `eLpNorm` bound for the cross-right limit object.** For a
closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index `i`, a
chart center `α : M`, and a component multi-index `P : CompIdx E r s`, there is a
nonnegative constant `C` with

```
eLpNorm (crossRightLimitComponent g r s h_atlas i α P) 2 μw
  ≤ ENNReal.ofReal C
      * ENNReal.ofReal ‖TensorH1ComplToTensorL2 g r s (eigenvectorResolvent …)‖,
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

By definition `crossRightLimitComponent` is the cutoff Euclidean chart component
of the abstract `L²` element `TensorH1ComplToTensorL2 g r s
(eigenvectorResolvent g r s h_atlas i)`; the foundational
`eLpNorm_tensorL2ChartComponentCutoff_le` controls the weighted `eLpNorm` of any
cutoff chart component by an explicit constant times the abstract element's
norm. -/
theorem eLpNorm_crossRightLimitComponent_le
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm ((crossRightLimitComponent (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          ENNReal.ofReal ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)‖ := by
  -- Unfold the limit object into a cutoff Euclidean chart component, then apply
  -- the foundational weighted `eLpNorm` bound for cutoff chart components.
  rw [crossRightLimitComponent]
  exact eLpNorm_tensorL2ChartComponentCutoff_le (I := I) (M := M) g r s α P
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))

/-! ## Headline 3 — the principal rotation coefficient limit

`covPrincipalRotationCoeffLimit g r s h_atlas i α P₀` is a four-fold finite sum
over `(P, Q, k, l)` of the `chartPouKernel α`-indicator cut of the `C^∞` factor
`principalRotationFactor` against the chart-partial atom `partialLpLimit P k`.
Note the atom depends only on `(P, k)`, not on `(Q, l)`. -/

/-! ### Weighted almost-everywhere vanishing of the chart-partial atom

The chart-partial atom `partialLpLimit g r s h_atlas i α P k` vanishes almost
everywhere — for the chart-pulled weighted measure restricted to the chart
target — off the compact partition-of-unity kernel `chartPouKernel α`. It is the
`i.fst.val`-rescaling of the eigenvector weak chart partial, which vanishes
almost everywhere off the kernel on the open complement inside the chart
target. -/

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
  -- The eigenvector weak chart partial vanishes a.e. off the kernel.
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

/-! ### Weighted-`L²` membership of the chart-partial atom

The chart-partial atom is `MemLp 2` for the chart-pulled weighted measure
restricted to the chart target: it is an `Lp ℝ 2 (chartL2Measure α)` element
(hence `MemLp 2` of the plain restricted volume) that vanishes almost everywhere
off the compact partition-of-unity kernel, so the general weighted upgrade
`memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact`
applies. -/

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
  -- The atom vanishes a.e. off the kernel for the plain chart `L²` measure
  -- (`chartL2Measure α` is, definitionally, `volume.restrict (chartTargetEuclid α)`).
  have h_atom_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
    filter_upwards [h_smul, h_weak_impl] with y hy hy_zero hyK
    · rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    h_atom_zero h_plain

/-! ### The per-summand explicit-norm bound

Each summand of `covPrincipalRotationCoeffLimit` is the `chartPouKernel α`-
indicator cut of the `C^∞`-on-the-chart-target factor `principalRotationFactor`,
times the chart-partial atom `partialLpLimit`. The lemma below records, for any
`C^∞`-coefficient / weighted-`L²`-atom pair, the explicit-norm `eLpNorm` estimate
against the weighted measure, together with the summand's weighted-`L²`
membership (needed to feed the triangle inequality). -/

/-- For a `C^∞`-on-the-chart-target coefficient `c` and a function `G` that is
weighted-`MemLp` and vanishes almost everywhere — for the chart-pulled weighted
measure restricted to the chart target — off the compact partition-of-unity
kernel, the indicator-cut summand `(chartPouKernel α).indicator c · G` is
weighted-`MemLp` and its `eLpNorm` is bounded by an explicit nonnegative constant
times the `eLpNorm` of `G`. -/
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

/-! ### The aggregation lemmas

The triangle inequality over a finite sum bounds the `eLpNorm` of the sum by the
sum of the `eLpNorm`s of the summands. The lemmas below package, once, the steps
shared between the per-summand bound and the headline. -/

-- The triangle inequality over a finite sum is established purely by
-- monotone-subadditivity of `eLpNorm`; the manifold-completeness and
-- closed-manifold instances enter only through the type of the chart-pulled
-- weighted measure and play no role in the proof term.
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

-- The aggregation step is established purely from the triangle inequality and
-- arithmetic of `ℝ≥0∞`; the manifold-completeness and closed-manifold instances
-- enter only through the type of the chart-pulled weighted measure.
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
    (C : ℝ)
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
    gcongr
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

/-- **Explicit-norm `eLpNorm` bound for the principal rotation coefficient
limit.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis
index `i`, a chart center `α : M`, and a component multi-index `P₀`, there is a
nonnegative constant `C` with

```
eLpNorm (covPrincipalRotationCoeffLimit g r s h_atlas i α P₀) 2 μw
  ≤ ENNReal.ofReal C * (∑ P, ∑ k, eLpNorm (partialLpLimit … P k) 2 μw),
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)` and
the sum on the right ranges over the distinct chart-partial atoms (each atom
depends only on the component multi-index `P` and the chart direction `k`).

`covPrincipalRotationCoeffLimit` is a four-fold finite sum over `(P, Q, k, l)`
whose summands carry an `indicator (chartPouKernel α)` cut of the `C^∞` factor
`principalRotationFactor`; the chart-partial atom `partialLpLimit P k` vanishes
almost everywhere (weighted) off the compact partition-of-unity kernel, so the
indicator-cut summand agrees almost everywhere with the uncut `C^∞`-factor
product, and `eLpNorm_weighted_contDiffOn_mul_le` controls its `eLpNorm`. The
triangle inequality assembles the per-summand bounds; the `(Q, l)`-summation
multiplicity and every per-coefficient sup constant are folded into the single
constant `C`. -/
theorem eLpNorm_covPrincipalRotationCoeffLimit_le
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (covPrincipalRotationCoeffLimit (I := I) (M := M)
          g r s h_atlas i α P₀ : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))) := by
  classical
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  -- Abbreviation for the chart-partial atom family, indexed by `(P, k)`.
  set partAtom : (TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E))
      → EuclN → ℝ := fun pk y =>
    ((partialLpLimit (I := I) (M := M) g r s h_atlas i α pk.1 pk.2 :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hpartAtom_def
  -- The four-fold sum, as a single sum over `(P, Q, k, l)`.
  set F : (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → EuclN → ℝ :=
    fun x y =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (principalRotationFactor (I := I) (M := M)
            g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2) y *
        ((partialLpLimit (I := I) (M := M) g r s h_atlas i α x.1 x.2.2.1 :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y
    with hF_def
  -- The per-summand weighted-`MemLp` membership and explicit-norm bound.
  have h_data : ∀ x ∈ (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))),
      MemLp (F x) 2 μw ∧
        ∃ C : ℝ, 0 ≤ C ∧
          eLpNorm (F x) 2 μw
            ≤ ENNReal.ofReal C * eLpNorm (partAtom (x.1, x.2.2.1)) 2 μw := by
    intro x _
    rw [hμw_def]
    exact eLpNorm_indicatorFactor_mul_atom_le (I := I) (M := M) g α
      (principalRotationFactor_contDiffOn (I := I) (M := M)
        g r s α P₀ x.1 x.2.1 x.2.2.1 x.2.2.2)
      _
      (partialLpLimit_memLp_weighted (I := I) (M := M)
        g r s h_atlas i α x.1 x.2.2.1)
      (partialLpLimit_ae_zero_off_chartPouKernel_weighted (I := I) (M := M)
        g r s h_atlas i α x.1 x.2.2.1)
  -- A single nonnegative constant dominating every per-summand constant: the
  -- sum of all of them.
  obtain ⟨Csum, hCsum_nn, hCsum_bd⟩ :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ (Finset.univ :
        Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
          × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))),
        eLpNorm (F x) 2 μw
          ≤ ENNReal.ofReal C * eLpNorm (partAtom (x.1, x.2.2.1)) 2 μw := by
    refine ⟨∑ x : TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        (h_data x (Finset.mem_univ x)).2.choose, ?_, ?_⟩
    · exact Finset.sum_nonneg
        (fun x _ => (h_data x (Finset.mem_univ x)).2.choose_spec.1)
    · intro x _
      refine (h_data x (Finset.mem_univ x)).2.choose_spec.2.trans ?_
      gcongr
      exact Finset.single_le_sum
        (f := fun x => (h_data x (Finset.mem_univ x)).2.choose)
        (fun x _ => (h_data x (Finset.mem_univ x)).2.choose_spec.1)
        (Finset.mem_univ x)
  -- Bound on the four-fold-sum `eLpNorm`, via the aggregation lemma.
  have h_bound :
      eLpNorm (fun y => ∑ x : TensorCompIdx (E := E) r s
          × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
          × Fin (Module.finrank ℝ E), F x y) 2 μw
        ≤ ENNReal.ofReal (Csum * (Finset.univ :
            Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card)
          * ∑ pk : TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E),
              eLpNorm (partAtom pk) 2 μw := by
    rw [hμw_def]
    exact eLpNorm_finsetSum_le_const_mul_atomSum (I := I) (M := M) g α
      Finset.univ Finset.univ F partAtom
      (fun x => (x.1, x.2.2.1)) (fun x _ => Finset.mem_univ _)
      Csum
      (fun x hx => by rw [← hμw_def]; exact (h_data x hx).1)
      (fun x hx => by rw [← hμw_def]; exact hCsum_bd x hx)
  -- Identify the single-product sum with the nested four-fold sum.
  have h_eq : (fun y => ∑ x : TensorCompIdx (E := E) r s
      × TensorCompIdx (E := E) r s × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E), F x y)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                    EuclN → ℝ) y) := by
    funext y
    rw [hF_def]
    simp only [Fintype.sum_prod_type]
  -- The chart-partial index sum on the right is the chart-partial atom family.
  have h_atom_eq : ∑ pk : TensorCompIdx (E := E) r s
      × Fin (Module.finrank ℝ E), eLpNorm (partAtom pk) 2 μw
      = ∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            eLpNorm ((partialLpLimit (I := I) (M := M)
                g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
              μw := by
    rw [Fintype.sum_prod_type]
  -- Headline constant: the per-summand sum constant times the four-fold-index
  -- cardinality.
  refine ⟨Csum * (Finset.univ :
      Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).card,
    by positivity, ?_⟩
  -- Unfold the limit object and assemble the bound.
  rw [show (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s h_atlas i α P₀ : EuclN → ℝ)
      = (fun y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                Set.indicator (chartPouKernel (I := I) (M := M) α)
                    (principalRotationFactor (I := I) (M := M)
                      g r s α P₀ P Q k l) y *
                  (partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
                    EuclN → ℝ) y) from rfl]
  rw [← h_eq, hμw_def, ← h_atom_eq]
  exact h_bound

end CrossRotationENormBounds

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          ENNReal.ofReal ‖tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)‖ :=
  eLpNorm_crossLeftLimitComponent_le (I := I) (M := M) g r s h_atlas i α P

example (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm ((crossRightLimitComponent (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          ENNReal.ofReal ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)‖ :=
  eLpNorm_crossRightLimitComponent_le (I := I) (M := M) g r s h_atlas i α P

example (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (covPrincipalRotationCoeffLimit (I := I) (M := M)
          g r s h_atlas i α P₀ : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C *
          (∑ P : TensorCompIdx (E := E) r s,
            ∑ k : Fin (Module.finrank ℝ E),
              eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
                ((chartPulledWeightedMeasure (I := I) g α).restrict
                  (chartTargetEuclid (I := I) (M := M) α))) :=
  eLpNorm_covPrincipalRotationCoeffLimit_le (I := I) (M := M)
    g r s h_atlas i α P₀

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
