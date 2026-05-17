import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightLimit
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLowerOrderLimits
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.TensorChartBilinearData

/-!
# Weighted-`L²` membership of the eigenvector chart-component limit objects

The chart-bilinear divergence-form data structure `ChartBilinearH1ComplData`
(and its tensor wrapper `TensorChartBilinearH1ComplData`) records the chart
component `u_chart` and the right-hand side `f_chart` as `MemLp 2` of the
chart-pulled **weighted** measure

```
(chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)
  = (volume.withDensity densityOnEuclid g α).restrict (chartTargetEuclid α).
```

The Euclidean chart-component limit objects that build `u_chart` and `f_chart`
for an eigenvector — produced by the companion files of this campaign — are, by
construction, only known to lie in `MemLp 2 (chartL2Measure α)`, where
`chartL2Measure α = volume.restrict (chartTargetEuclid α)` is the *plain*
Lebesgue measure restricted to the Euclidean chart target.

The naive implication

```
MemLp w 2 (volume.restrict (chartTargetEuclid α))
  → MemLp w 2 ((chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α))
```

is **false** for a general `w`: `densityOnEuclid g α` need not be bounded above
on `chartTargetEuclid α` (the chart target is open, not precompact). It holds,
however, for `w` that is (almost everywhere) supported in a *compact* subset of
the chart target: on a compact subset `densityOnEuclid g α` is bounded above, so
the chart-pulled weighted measure restricted there is dominated by a scalar
multiple of `volume`.

Every eigenvector chart-component limit object treated here is supported (a.e.)
in such a compact subset:

* the three lower-order coefficient limits `covPrincipalRotationCoeffLimit`,
  `covLowerOrderRotationValueCoeffLimit`, `weightedGradCoeffDivLimit` are
  *explicit finite sums* in which every summand carries an
  `indicator (chartPouKernel α)` factor — hence each vanishes **pointwise**
  off the compact partition-of-unity kernel `chartPouKernel α`;
* the cross-Leibniz limits `crossLeftLimitComponent`, `crossRightLimitComponent`
  and the canonical eigenvector chart component
  `tensorL2ChartComponent g r s u α P₀` are continuous-linear-map images of
  abstract `L²` elements; they are `L²`-limits of concrete chart components of
  smooth sections, each supported in a compact chart kernel. An `L²`-convergent
  sequence has an almost-everywhere-convergent subsequence, and the
  almost-everywhere limit of functions vanishing off a closed set vanishes off
  it almost everywhere — so these objects are a.e. supported in the relevant
  compact kernel.

## Main results

* `memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact` —
  the general upgrade: plain `L²` plus a.e.-vanishing off a compact subset of
  the chart target implies weighted `L²`.
* `tensorL2ChartComponent_memLp_weighted`,
  `tensorL2ChartComponentCutoff_memLp_weighted` — weighted `L²` of the canonical
  / cutoff Euclidean chart component of *any* abstract `L²` element.
* `covPrincipalRotationCoeffLimit_memLp_weighted`,
  `covLowerOrderRotationValueCoeffLimit_memLp_weighted`,
  `weightedGradCoeffDivLimit_memLp_weighted` — weighted `L²` of the three
  lower-order coefficient limits.
* `crossLeftLimitComponent_memLp_weighted`,
  `crossRightLimitComponent_memLp_weighted` — weighted `L²` of the two
  cross-Leibniz limits.

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

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Almost-everywhere support of an `L²`-limit

An `L²`-convergent sequence converges in measure, hence has a subsequence
converging almost everywhere; if every term of the sequence vanishes almost
everywhere off a closed set `K`, the almost-everywhere limit vanishes off `K`
almost everywhere too. This is the propagation principle used to control the
support of the continuous-linear-map-extended chart components, which are
`L²`-limits of concrete chart components supported in a compact chart kernel. -/

/-- **Almost-everywhere support of an `L²`-limit.** If `F n → glim` in
`Lp ℝ 2 μ` and each `F n` vanishes almost everywhere off a closed set `K`, then
`glim` vanishes almost everywhere off `K`. -/
private lemma ae_eq_zero_off_of_tendsto_Lp
    {μ : Measure EuclN} {K : Set EuclN} {F : ℕ → Lp ℝ 2 μ} {glim : Lp ℝ 2 μ}
    (hF : ∀ n, ∀ᵐ y ∂μ, y ∉ K → (F n : EuclN → ℝ) y = 0)
    (h_tendsto : Filter.Tendsto F atTop (𝓝 glim)) :
    ∀ᵐ y ∂μ, y ∉ K → (glim : EuclN → ℝ) y = 0 := by
  classical
  -- `L²`-convergence implies convergence in measure.
  have h_inMeasure : TendstoInMeasure μ (fun n => (F n : EuclN → ℝ)) atTop
      (glim : EuclN → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp (p := 2) h_tendsto
  -- Hence an almost-everywhere-convergent subsequence.
  obtain ⟨ns, _hns_mono, h_ae⟩ := h_inMeasure.exists_seq_tendsto_ae
  -- Each term of the subsequence vanishes a.e. off `K`; intersect over `i`.
  have hF_sub : ∀ᵐ y ∂μ, ∀ i : ℕ, y ∉ K → (F (ns i) : EuclN → ℝ) y = 0 :=
    ae_all_iff.mpr (fun i => hF (ns i))
  -- Combine the a.e.-convergence with the a.e.-vanishing of the subsequence.
  filter_upwards [h_ae, hF_sub] with y h_lim h_zero hy
  -- The subsequence at `y` is identically zero, so its limit `glim y` is zero.
  have h_const : Filter.Tendsto (fun i => (F (ns i) : EuclN → ℝ) y) atTop (𝓝 0) := by
    refine Filter.Tendsto.congr (fun i => (h_zero i hy).symm) tendsto_const_nhds
  exact tendsto_nhds_unique h_lim h_const

/-! ## The chart-pulled weighted measure dominated on a compact subset

On any compact subset `K ⊆ chartTargetEuclid α` the density `densityOnEuclid g α`
is bounded above by a positive constant, so the chart-pulled weighted measure
restricted to `K` is dominated by that constant times `volume` restricted to
`K`. -/

/-- On a compact subset `K ⊆ chartTargetEuclid α`, the chart-pulled weighted
measure restricted to `K` is dominated by a positive scalar multiple of `volume`
restricted to `K`. -/
private lemma chartPulledWeightedMeasure_restrict_le_volume_of_compact
    {g : SmoothRiemannianMetric I M} (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict K ≤
        ENNReal.ofReal c • ((volume : Measure EuclN).restrict K) := by
  classical
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  refine ⟨c_max, lt_of_lt_of_le hc_min_pos hc_le, ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter hK_meas)]
  -- The density is bounded above by `c_max` on `A ∩ K`.
  have h_pointwise_bd :
      ∫⁻ y in A ∩ K,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(volume : Measure EuclN) ≤
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setLIntegral_mono_ae' (hA.inter hK_meas) ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    exact ENNReal.ofReal_le_ofReal (h_bd y hy.2).2
  have h_const_eval :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) =
      ENNReal.ofReal c_max * (volume : Measure EuclN) (A ∩ K) :=
    MeasureTheory.setLIntegral_const _ _
  rw [smul_eq_mul]
  exact h_pointwise_bd.trans (le_of_eq h_const_eval)

/-! ## The general weighted-`L²` upgrade

The headline upgrade lemma: an `L²` function with respect to the plain Lebesgue
measure on `chartTargetEuclid α`, vanishing almost everywhere off a compact
subset `K` of the chart target, is `L²` with respect to the chart-pulled
weighted measure restricted to `chartTargetEuclid α`. -/

/-- **Weighted-`L²` upgrade from compact a.e.-support.** Let `w : EuclN → ℝ` be
`MemLp 2` with respect to the plain Lebesgue volume restricted to
`chartTargetEuclid α`. If `w` vanishes almost everywhere (with respect to that
plain restricted volume) off a compact subset `K ⊆ chartTargetEuclid α`, then
`w` is `MemLp 2` with respect to the chart-pulled weighted measure
`(chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

On the compact set `K` the density `densityOnEuclid g α` is bounded above, so
the chart-pulled weighted measure restricted to `K` is dominated by a scalar
multiple of `volume`; off `K` the function `w` vanishes almost everywhere, and
the weighted restricted measure is absolutely continuous with respect to the
plain restricted volume, so the a.e.-vanishing transfers. -/
theorem memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (g : SmoothRiemannianMetric I M) (α : M) {w : EuclN → ℝ}
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hwK : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ K → w y = 0)
    (hw : MemLp w 2 ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α))) :
    MemLp w 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  -- The weighted restricted measure is absolutely continuous w.r.t. the plain
  -- restricted volume.
  have h_abs : (chartPulledWeightedMeasure (I := I) g α).restrict Ω ≪
      (volume : Measure EuclN).restrict Ω := by
    unfold chartPulledWeightedMeasure
    exact (withDensity_absolutelyContinuous (volume : Measure EuclN) _).restrict Ω
  -- `w` vanishes a.e. off `K` w.r.t. the weighted restricted measure.
  have hwK' : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict Ω),
      y ∉ K → w y = 0 :=
    h_abs.ae_le hwK
  -- Hence `w` agrees a.e. with `K.indicator w` w.r.t. the weighted measure.
  have h_ind : w =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict Ω]
      K.indicator w := by
    filter_upwards [hwK'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  -- It therefore suffices to show `MemLp (K.indicator w)` w.r.t. the weighted
  -- restricted measure.
  refine MemLp.ae_eq h_ind.symm ?_
  -- `MemLp (K.indicator w)` is `MemLp w` w.r.t. the weighted measure restricted
  -- to `K`.
  rw [memLp_indicator_iff_restrict hK_meas]
  -- The weighted measure restricted to `Ω` then to `K` is the weighted measure
  -- restricted to `K` (because `K ⊆ Ω`).
  rw [Measure.restrict_restrict hK_meas, Set.inter_eq_self_of_subset_left hK_in]
  -- Dominate the weighted measure on `K` by a multiple of `volume`.
  obtain ⟨c, _hc_pos, h_le⟩ :=
    chartPulledWeightedMeasure_restrict_le_volume_of_compact (I := I) (M := M)
      α hK_compact hK_meas hK_in
  -- `MemLp w` w.r.t. `volume` restricted to `K` (subset of `Ω`).
  have hw_K : MemLp w 2 ((volume : Measure EuclN).restrict K) := by
    refine hw.mono_measure ?_
    rw [hΩ_def]
    exact Measure.restrict_mono hK_in le_rfl
  exact hw_K.of_measure_le_smul (c := ENNReal.ofReal c) ENNReal.ofReal_ne_top h_le

/-! ## The canonical Euclidean chart component is a.e. kernel-supported

The canonical Euclidean chart component `tensorL2ChartComponent g r s u α P₀` of
an abstract `L²` element `u` is the continuous linear extension, along the dense
embedding of smooth sections, of the chart-component `L²` map. On a smooth
section it recovers the concrete chart component `tensorChartComponent`, which
vanishes off the compact partition-of-unity kernel `chartPouKernel α`. Picking a
smooth sequence converging to `u` and propagating the support through the
`L²`-limit shows the canonical chart component of *any* `u` is a.e. supported in
`chartPouKernel α`. -/

/-- For any abstract `L²` element `u`, the canonical Euclidean chart component
`tensorL2ChartComponent g r s u α P₀` vanishes almost everywhere off the compact
partition-of-unity kernel `chartPouKernel α`. -/
private lemma tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
          EuclN → ℝ) y = 0 := by
  classical
  -- Smooth sections are dense in the `L²` Hilbert space: pick a sequence whose
  -- `L²`-images converge to `u`.
  have h_dense : DenseRange
      (fun S : SmoothCcTensor g r s => (S : TensorL2 r s g)) := by
    have h := UniformSpace.Completion.denseRange_coe
      (α := SmoothCcTensor g r s)
    exact h
  have h_mem : u ∈ closure (Set.range
      (fun S : SmoothCcTensor g r s => (S : TensorL2 r s g))) := h_dense u
  obtain ⟨x, hx_range, hx_tendsto⟩ :=
    mem_closure_iff_seq_limit.mp h_mem
  -- Choose smooth-section preimages of the approximating sequence.
  choose S hS using hx_range
  -- The chart components of the approximants converge to that of `u`.
  have h_comp_tendsto : Filter.Tendsto
      (fun n => tensorL2ChartComponent (I := I) (M := M) g r s
        ((S n : TensorL2 r s g)) α P₀)
      atTop
      (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀)) := by
    have h_clm := ((continuous_tensorL2ChartComponent (I := I) (M := M)
      g r s α P₀).tendsto u).comp hx_tendsto
    refine Filter.Tendsto.congr (fun n => ?_) h_clm
    simp only [Function.comp_apply, hS n]
  -- Each approximant chart component vanishes a.e. off the kernel.
  have h_term : ∀ n : ℕ,
      ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ chartPouKernel (I := I) (M := M) α →
          (tensorL2ChartComponent (I := I) (M := M) g r s
            ((S n : TensorL2 r s g)) α P₀ : EuclN → ℝ) y = 0 := by
    intro n
    -- The canonical chart component of a smooth section agrees a.e. with the
    -- concrete `tensorChartComponent`, which vanishes off the kernel.
    have h_ae := tensorL2ChartComponent_smoothToTensorL2_coeFn
      (I := I) (M := M) g r s (S n) α P₀
    filter_upwards [h_ae] with y hy hyK
    rw [hy]
    exact tensorChartComponent_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s (S n) α P₀.1 P₀.2 hyK
  -- Propagate the support through the `L²`-limit.
  exact ae_eq_zero_off_of_tendsto_Lp h_term h_comp_tendsto

/-- For any abstract `L²` element `u`, the canonical Euclidean chart component
`tensorL2ChartComponent g r s u α P₀` is `MemLp 2` with respect to the
chart-pulled weighted measure restricted to `chartTargetEuclid α`.

This is the weighted-`L²` membership of the eigenvector chart component
`u_chart` in `ChartBilinearH1ComplData` / `TensorChartBilinearH1ComplData`: the
chart component is a.e. supported in the compact partition-of-unity kernel, so
the general upgrade
`memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact`
applies. -/
theorem tensorL2ChartComponent_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (fun y => (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
        EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- The canonical chart component is `MemLp 2` of the plain `L²` reference
  -- measure of the chart (it is an `Lp` element).
  have h_plain : MemLp (fun y => (tensorL2ChartComponent (I := I) (M := M)
      g r s u α P₀ : EuclN → ℝ) y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    Lp.memLp (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀)
  -- It is a.e. supported in the compact partition-of-unity kernel.
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (tensorL2ChartComponent_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s u α P₀)
    h_plain

/-! ## The cutoff Euclidean chart component is a.e. kernel-supported

The cutoff Euclidean chart component `tensorL2ChartComponentCutoff g r s u α P₀`
is the continuous linear extension of the cutoff chart-component `L²` map. On a
smooth section it recovers the concrete `cutoffComponentEuclid`, which is the
chart push-forward of the chart-kernel-cutoff-weighted scalar component. The
latter vanishes off the closed support of the chart-kernel cutoff, whose chart
image is the compact kernel `cutoffChartKernel α`; the chart push-forward
therefore vanishes off the `toEuclidean`-image of that kernel. -/

/-- The `toEuclidean`-image of the compact chart-kernel-cutoff kernel: the
compact subset of the Euclidean chart target in which every cutoff Euclidean
chart component is supported. -/
private def cutoffChartKernelEuclid (α : M) : Set EuclN :=
  toEuclidean '' (cutoffChartKernel (I := I) (M := M) α)

private lemma cutoffChartKernelEuclid_isCompact (α : M) :
    IsCompact (cutoffChartKernelEuclid (I := I) (M := M) α) :=
  (cutoffChartKernel_isCompact (I := I) (M := M) α).image
    (toEuclidean (E := E)).continuous

private lemma cutoffChartKernelEuclid_measurableSet (α : M) :
    MeasurableSet (cutoffChartKernelEuclid (I := I) (M := M) α) :=
  (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α).isClosed.measurableSet

private lemma cutoffChartKernelEuclid_subset_chartTargetEuclid (α : M) :
    cutoffChartKernelEuclid (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  unfold cutoffChartKernelEuclid chartTargetEuclid
  exact Set.image_mono (cutoffChartKernel_subset_target (I := I) (M := M) α)

/-- The concrete cutoff Euclidean chart component of a smooth section vanishes
outside the compact cutoff kernel `cutoffChartKernelEuclid α`. -/
private lemma cutoffComponentEuclid_eq_zero_off_cutoffChartKernelEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ cutoffChartKernelEuclid (I := I) (M := M) α) :
    cutoffComponentEuclid (I := I) (M := M) g r s S α Idx Jdx y = 0 := by
  classical
  by_cases htar : y ∈ chartTargetEuclid (I := I) (M := M) α
  · -- On the chart target the cutoff component reads the cutoff scalar at the
    -- chart-source preimage; that scalar vanishes off the cutoff support.
    rw [cutoffComponentEuclid_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx
      htar]
    -- The chart-source preimage of `y`.
    set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
    -- `b` is not in the closed support of the cutoff scalar component.
    have hb_notin : b ∉ tsupport (cutoffComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx) := by
      intro hb_supp
      -- Otherwise its chart image lands in `cutoffChartKernel α`, hence `y` in
      -- `cutoffChartKernelEuclid α` — a contradiction.
      apply hy
      refine ⟨extChartAt I α b, ?_, ?_⟩
      · exact cutoffComponentScalar_chartImage_subset_kernel
          (I := I) (M := M) g r s S α Idx Jdx ⟨b, hb_supp, rfl⟩
      · -- `toEuclidean (extChartAt I α b) = y`.
        have hmem : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
          DifferentialGeometry.Analysis.Laplacian.MetricExtension.toEuclidean_symm_mem_target
            (I := I) (M := M) htar
        rw [hb_def, (extChartAt I α).right_inv hmem, toEuclidean.apply_symm_apply]
    exact image_eq_zero_of_notMem_tsupport hb_notin
  · -- Off the chart target the cutoff component vanishes outright.
    exact cutoffComponentEuclid_apply_of_notMem (I := I) (M := M) g r s S α
      Idx Jdx htar

/-- For any abstract `L²` element `u`, the cutoff Euclidean chart component
`tensorL2ChartComponentCutoff g r s u α P₀` vanishes almost everywhere off the
compact cutoff kernel `cutoffChartKernelEuclid α`. -/
private lemma tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
        (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀ :
          EuclN → ℝ) y = 0 := by
  classical
  -- Smooth sections are dense in the `L²` Hilbert space.
  have h_dense : DenseRange
      (fun S : SmoothCcTensor g r s => (S : TensorL2 r s g)) :=
    UniformSpace.Completion.denseRange_coe (α := SmoothCcTensor g r s)
  obtain ⟨x, hx_range, hx_tendsto⟩ :=
    mem_closure_iff_seq_limit.mp (h_dense u)
  choose S hS using hx_range
  -- The cutoff chart components of the approximants converge to that of `u`.
  have h_comp_tendsto : Filter.Tendsto
      (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        ((S n : TensorL2 r s g)) α P₀)
      atTop
      (𝓝 (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀)) := by
    have h_clm :=
      ((tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s α
        P₀).continuous.tendsto u).comp hx_tendsto
    refine Filter.Tendsto.congr (fun n => ?_) h_clm
    simp only [Function.comp_apply, hS n, tensorL2ChartComponentCutoffCLM_apply]
  -- Each approximant cutoff chart component vanishes a.e. off the kernel.
  have h_term : ∀ n : ℕ,
      ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          (tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            ((S n : TensorL2 r s g)) α P₀ : EuclN → ℝ) y = 0 := by
    intro n
    have h_ae := tensorL2ChartComponentCutoff_smoothToTensorL2_coeFn
      (I := I) (M := M) g r s (S n) α P₀
    filter_upwards [h_ae] with y hy hyK
    rw [hy]
    exact cutoffComponentEuclid_eq_zero_off_cutoffChartKernelEuclid
      (I := I) (M := M) g r s (S n) α P₀.1 P₀.2 hyK
  exact ae_eq_zero_off_of_tendsto_Lp h_term h_comp_tendsto

/-- For any abstract `L²` element `u`, the cutoff Euclidean chart component
`tensorL2ChartComponentCutoff g r s u α P₀` is `MemLp 2` with respect to the
chart-pulled weighted measure restricted to `chartTargetEuclid α`.

This is the weighted-`L²` membership backing the cross-Leibniz limit objects:
the cutoff chart component is a.e. supported in the compact cutoff kernel, so the
general upgrade
`memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact`
applies. -/
theorem tensorL2ChartComponentCutoff_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (fun y => (tensorL2ChartComponentCutoff (I := I) (M := M)
        g r s u α P₀ : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : MemLp (fun y => (tensorL2ChartComponentCutoff (I := I) (M := M)
      g r s u α P₀ : EuclN → ℝ) y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    Lp.memLp (tensorL2ChartComponentCutoff (I := I) (M := M) g r s u α P₀)
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
    (cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α)
    (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
    (tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
      (I := I) (M := M) g r s u α P₀)
    h_plain

/-! ## Weighted-`L²` membership of the cross-Leibniz limit objects

The cross-left and cross-right limit objects are, by definition, cutoff
Euclidean chart components of abstract `L²` elements; their weighted-`L²`
membership is the corresponding instance of
`tensorL2ChartComponentCutoff_memLp_weighted`. -/

/-- **Weighted-`L²` membership of the cross-left limit object.** The cross-left
limit `crossLeftLimitComponent g r s h_uniform i α P` is `MemLp 2` with respect
to the chart-pulled weighted measure restricted to `chartTargetEuclid α`. -/
theorem crossLeftLimitComponent_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    MemLp (fun y => (crossLeftLimitComponent (I := I) (M := M)
        g r s h_uniform i α P : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [crossLeftLimitComponent]
  exact tensorL2ChartComponentCutoff_memLp_weighted (I := I) (M := M)
    g r (s + 1)
    (tensorCovGradL2Compl (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
    α P

/-- **Weighted-`L²` membership of the cross-right limit object.** The cross-right
limit `crossRightLimitComponent g r s h_uniform i α P` is `MemLp 2` with respect
to the chart-pulled weighted measure restricted to `chartTargetEuclid α`. -/
theorem crossRightLimitComponent_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    MemLp (fun y => (crossRightLimitComponent (I := I) (M := M)
        g r s h_uniform i α P : EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [crossRightLimitComponent]
  exact tensorL2ChartComponentCutoff_memLp_weighted (I := I) (M := M) g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_uniform i))
    α P

/-! ## Weighted-`L²` membership of the three lower-order coefficient limits

The lower-order coefficient limit objects are explicit finite sums in which
every summand carries an `indicator (chartPouKernel α)` factor; each therefore
vanishes **pointwise** off the compact partition-of-unity kernel
`chartPouKernel α`. Combined with their `MemLp 2 (chartL2Measure α)` membership,
the general upgrade lemma yields weighted-`L²` membership. -/

/-- The principal rotation coefficient limit vanishes pointwise off the compact
partition-of-unity kernel `chartPouKernel α`: every summand carries an
`indicator (chartPouKernel α)` factor. -/
private lemma covPrincipalRotationCoeffLimit_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s h_uniform i α P₀ y = 0 := by
  classical
  rw [covPrincipalRotationCoeffLimit]
  refine Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ =>
    Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))))
  rw [Set.indicator_of_notMem hy, zero_mul]

/-- The lower-order rotation value coefficient limit vanishes pointwise off the
compact partition-of-unity kernel `chartPouKernel α`. -/
private lemma covLowerOrderRotationValueCoeffLimit_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s h_uniform i α P₀ y = 0 := by
  classical
  -- `covLowerOrderRotationValueCoeffLimit` is a sum of two finite multiple sums;
  -- each summand carries an `indicator (chartPouKernel α)` factor that vanishes
  -- at `y ∉ chartPouKernel α`. Both finite sums are therefore zero.
  rw [covLowerOrderRotationValueCoeffLimit,
    Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ =>
      Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => by
        rw [Set.indicator_of_notMem hy, zero_mul])))),
    Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ =>
      Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ =>
        Finset.sum_eq_zero (fun p _ => by
          rw [Set.indicator_of_notMem hy, zero_mul]))))),
    add_zero]

/-- The chart-density-weighted lower-order gradient divergence coefficient limit
vanishes pointwise off the compact partition-of-unity kernel
`chartPouKernel α`. -/
private lemma weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    weightedGradCoeffDivLimit (I := I) (M := M)
        g r s h_uniform i α P₀ l y = 0 := by
  classical
  -- `weightedGradCoeffDivLimit` is a sum of two finite multiple sums; each
  -- summand carries an `indicator (chartPouKernel α)` factor that vanishes at
  -- `y ∉ chartPouKernel α`. Both finite sums are therefore zero.
  rw [weightedGradCoeffDivLimit,
    Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ =>
      Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun p _ => by
        rw [Set.indicator_of_notMem hy, zero_mul])))),
    Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ =>
      Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun p _ => by
        rw [Set.indicator_of_notMem hy, zero_mul])))),
    add_zero]

/-- **Weighted-`L²` membership of the principal rotation coefficient limit.**
`covPrincipalRotationCoeffLimit g r s h_uniform i α P₀` is `MemLp 2` with respect
to the chart-pulled weighted measure restricted to `chartTargetEuclid α`. -/
theorem covPrincipalRotationCoeffLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s h_uniform i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  -- The limit is `MemLp 2 (chartL2Measure α) = MemLp 2 (volume.restrict Ω)`.
  have h_plain : MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
      g r s h_uniform i α P₀) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    covPrincipalRotationCoeffLimit_memLp (I := I) (M := M) g r s h_uniform i α P₀
  -- It vanishes pointwise — hence a.e. — off the compact kernel.
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      covPrincipalRotationCoeffLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_uniform i α P₀ hy))
    h_plain

/-- **Weighted-`L²` membership of the lower-order rotation value coefficient
limit.** `covLowerOrderRotationValueCoeffLimit g r s h_uniform i α P₀` is
`MemLp 2` with respect to the chart-pulled weighted measure restricted to
`chartTargetEuclid α`. -/
theorem covLowerOrderRotationValueCoeffLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s h_uniform i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : MemLp (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
      g r s h_uniform i α P₀) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    covLowerOrderRotationValueCoeffLimit_memLp (I := I) (M := M)
      g r s h_uniform i α P₀
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      covLowerOrderRotationValueCoeffLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_uniform i α P₀ hy))
    h_plain

/-- **Weighted-`L²` membership of the chart-density-weighted lower-order gradient
divergence coefficient limit.** `weightedGradCoeffDivLimit g r s h_uniform i α P₀
l` is `MemLp 2` with respect to the chart-pulled weighted measure restricted to
`chartTargetEuclid α`. -/
theorem weightedGradCoeffDivLimit_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) :
    MemLp (weightedGradCoeffDivLimit (I := I) (M := M)
        g r s h_uniform i α P₀ l) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_plain : MemLp (weightedGradCoeffDivLimit (I := I) (M := M)
      g r s h_uniform i α P₀ l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    weightedGradCoeffDivLimit_memLp (I := I) (M := M) g r s h_uniform i α P₀ l
  exact memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
    (I := I) (M := M) g α
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_measurableSet (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (Filter.Eventually.of_forall (fun y hy =>
      weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_uniform i α P₀ l hy))
    h_plain

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (fun y => (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
        EuclN → ℝ) y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  tensorL2ChartComponent_memLp_weighted (I := I) (M := M) g r s u α P₀

example (h_uniform : uniformTensorChartSobolevBound g r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s h_uniform i α P₀) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  covPrincipalRotationCoeffLimit_memLp_weighted (I := I) (M := M)
    g r s h_uniform i α P₀

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
