import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSEpNorm
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLimitEnergyBounds
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSMemWkp

/-!
# A uniform energy bound for the eigenvector chart right-hand side

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, and a component multi-index `P₀`, the chart-Euclidean right-hand side
`eigenvectorChartRHS g r s h_atlas i α P₀` of the connection-Laplacian
eigenvector weak-solution assembly has, by `eigenvectorChartRHS_eLpNorm_le_uniform`,
a weighted-`eLpNorm` bound whose right-hand side is `ENNReal.ofReal (μ⁻¹ · C)`
times a six-summand source aggregate, where `μ := i.fst.val ∈ (0, 1]` is the
resolvent eigenvalue attached to the eigenbasis index `i`.

This file collapses that six-summand aggregate down to the abstract `L²` norm of
the eigenbasis vector `tensorResolventEigenbasisVec h_atlas i`. The headline is

```
∃ C ≥ 0, ∀ i,
  eLpNorm (eigenvectorChartRHS g r s h_atlas i α P₀) 2 μw
    ≤ ENNReal.ofReal (C · μ⁻¹) · ENNReal.ofReal ‖tensorResolventEigenbasisVec …‖,
```

with `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)` and
`C` a chart-geometric constant — depending only on `g r s h_atlas α P₀`, never
on the eigenbasis index `i`.

## Why an energy bound is needed

A higher-order norm of a function cannot be bounded by a lower-order norm of the
same function in general. The bound below is genuine precisely because the
function is an *eigenvector*: the resolvent eigen-equation supplies the energy
identity `eigenvectorResolvent_h1Norm_le` and its gradient corollary
`tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le`. The universal quantifier
`∀ i` lies *inside* the existential `∃ C`, so a single geometric constant `C`
controls the chart right-hand side of *every* eigenvector simultaneously; the
`i`-dependence of the right-hand side is confined to the explicit `μ⁻¹` factor.

## Strategy

Each of the six aggregate atoms is bounded by `C_atom · μ^p · ‖φ‖`
(`φ := tensorResolventEigenbasisVec h_atlas i`) where the per-atom `μ`-power `p`
is `1/2` for the two gradient-order chart-partial atoms and the cross-left
gradient atom, `1` for the cross-right and chart-component atoms, and `0` for the
bare chart component:

* atoms `crossLeftLimitComponent` / `crossRightLimitComponent` — the committed
  uniform lemmas `eLpNorm_crossLeftLimitComponent_le_uniform` /
  `eLpNorm_crossRightLimitComponent_le_uniform` bound them by an abstract norm,
  collapsed via `tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le`
  respectively the eigen-equation `TensorH1ComplToTensorL2 (eigenvectorResolvent
  …) = μ • φ`;
* atoms `partialLpLimit` / `cutoffPartialLpLimit` — the committed lemmas
  `partialLpLimit_eLpNorm_le` / `cutoffPartialLpLimit_eLpNorm_le` bound them on
  plain Lebesgue volume; a weighted-versus-volume `eLpNorm` comparison
  (`eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact`) transfers the bound
  to the chart-pulled weighted measure, since each atom vanishes almost
  everywhere off a compact kernel;
* atoms `eigenvectorChartComponentFun` / `componentLpLimit` — order-`0`; the
  uniform weighted bound `eLpNorm_tensorL2ChartComponent_le_uniform` for the
  canonical chart component controls them.

Since `μ ∈ (0, 1]`, every `μ`-power is `≤ 1`, so the six-summand aggregate is
bounded by `C' · ‖φ‖`; multiplying by the `μ⁻¹` prefactor of
`eigenvectorChartRHS_eLpNorm_le_uniform` produces the single explicit `μ⁻¹`
power of the headline.

## Main result

* `eigenvectorChartRHS_eLpNorm_le_energy` — the uniform energy bound for the
  eigenvector chart right-hand side.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

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

/-! ## Positivity of the resolvent eigenvalue

The eigenbasis vector `tensorResolventEigenbasisVec h_atlas i` is a unit vector
of the orthonormal eigenbasis of the resolvent eigenspace at `μ := i.fst.val`;
since it is non-zero, `μ` lies in the resolvent's unit interval `(0, 1]`, hence
is strictly positive and bounded above by `1`. -/

/-- The eigenbasis vector is a unit vector: it is, by construction, one of the
vectors of an orthonormal basis of its eigenspace. -/
private lemma norm_eigenbasisVec_eq_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ = 1 :=
  (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s) h_atlas).norm_eq_one i

/-- The resolvent eigenvalue `μ := i.fst.val` attached to an eigenbasis index
lies in the unit interval `(0, 1]`: the eigenbasis vector is a non-zero element
of the resolvent eigenspace at `μ`, and the resolvent eigenvalues lie in the
unit interval. -/
private lemma eigenvalue_mem_Ioc
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val ∧ i.fst.val ≤ 1 :=
  tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
    (by
      intro h_zero
      have h_norm := norm_eigenbasisVec_eq_one (I := I) (M := M) g r s h_atlas i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The resolvent eigenvalue `μ := i.fst.val` lies in the unit interval `(0, 1]`
(chart-locality-free). Chart-locality-free twin of `eigenvalue_mem_Ioc`, re-keyed
onto the unconditional eigenbasis vector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic
g r s) i`: this vector is a unit element of the resolvent eigenspace at `μ`, and
the resolvent eigenvalues lie in the unit interval. No chart-selection
hypothesis. -/
private lemma eigenvalue_mem_Ioc_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val ∧ i.fst.val ≤ 1 :=
  tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s) i)
    (by
      intro h_zero
      have h_norm :
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ = 1 :=
        (tensorResolventEigenbasisVec_ofCompact_orthonormal (I := I) (M := M)
          (g := g) (r := r) (s := s)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s)).norm_eq_one i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)

/-! ## The weighted-versus-volume `eLpNorm` comparison on a compact kernel

For a function vanishing almost everywhere — with respect to the plain Lebesgue
volume restricted to the off-kernel set `chartTargetEuclid α \ K` — off a
compact subset `K ⊆ chartTargetEuclid α`, the weighted `L²`-norm against the
chart-pulled weighted measure restricted to the chart target is bounded by a
single nonnegative constant — depending only on `g, α, K` — times the
plain-volume `L²`-norm restricted to the chart target. On the compact kernel the
chart density `densityOnEuclid g α` is bounded above. -/

omit [CompleteSpace E] in
/-- **Weighted-versus-volume `eLpNorm` comparison on a compact kernel.** For a
compact subset `K` of the Euclidean chart target `chartTargetEuclid α`, there is
a nonnegative constant `C` — depending only on `g, α, K` — such that *every*
function `f` vanishing almost everywhere off `K` (with respect to the plain
Lebesgue volume restricted to `chartTargetEuclid α \ K`) satisfies

```
eLpNorm f 2 μw ≤ ENNReal.ofReal C · eLpNorm f 2 (volume.restrict (chartTargetEuclid α)),
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

On the compact kernel the chart density is bounded above, so the weighted
measure restricted there is dominated by a multiple of `volume`; off the kernel
`f` vanishes almost everywhere, and the weighted restricted measure is
absolutely continuous with respect to the plain restricted volume, so the
a.e.-vanishing transfers. The constant `C` does not depend on `f` — it is the
square root of an upper bound for the chart density on `K`. -/
private lemma eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : EuclN → ℝ,
        f =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \ K)]
            (fun _ : EuclN => (0 : ℝ)) →
        eLpNorm f 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            eLpNorm f 2
              ((volume : Measure EuclN).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hΩ_open : IsOpen Ω :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hV_meas : MeasurableSet (Ω \ K) := hΩ_open.measurableSet.diff hK_meas
  -- On the compact kernel the density is bounded above by a positive constant.
  obtain ⟨_c_min, c_max, hc_min_pos, hc_le, h_dens_bd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hK_compact hK_in
  have hc_max_pos : 0 < c_max := lt_of_lt_of_le hc_min_pos hc_le
  -- The weighted measure restricted to `K` is dominated by `c_max • volume`.
  have hc_le_meas : (chartPulledWeightedMeasure (I := I) g α).restrict K ≤
      ENNReal.ofReal c_max • ((volume : Measure EuclN).restrict K) := by
    refine Measure.le_iff.2 ?_
    intro A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.restrict_apply hA]
    unfold chartPulledWeightedMeasure
    rw [withDensity_apply _ (hA.inter hK_meas)]
    have h_pointwise_bd :
        ∫⁻ y in A ∩ K,
            ENNReal.ofReal (densityOnEuclid (I := I) g α y)
              ∂(volume : Measure EuclN) ≤
        ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) := by
      refine MeasureTheory.setLIntegral_mono_ae' (hA.inter hK_meas) ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact ENNReal.ofReal_le_ofReal (h_dens_bd y hy.2).2
    have h_const_eval :
        ∫⁻ _y in A ∩ K, ENNReal.ofReal c_max ∂(volume : Measure EuclN) =
        ENNReal.ofReal c_max * (volume : Measure EuclN) (A ∩ K) :=
      MeasureTheory.setLIntegral_const _ _
    rw [smul_eq_mul]
    exact h_pointwise_bd.trans (le_of_eq h_const_eval)
  -- The headline constant: `√c_max`, independent of `f`.
  refine ⟨Real.sqrt c_max, Real.sqrt_nonneg _, fun f hf => ?_⟩
  -- Recast the off-kernel a.e.-vanishing as a pointwise implication on `Ω`.
  have hf' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω), y ∉ K → f y = 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas] at hf
    rw [ae_restrict_iff' hΩ_open.measurableSet]
    filter_upwards [hf] with y hy hy_Ω hy_K
    exact hy ⟨hy_Ω, hy_K⟩
  -- The weighted measure restricted to `Ω` is absolutely continuous w.r.t. the
  -- plain volume restricted to `Ω`.
  have h_abs : (chartPulledWeightedMeasure (I := I) g α).restrict Ω ≪
      (volume : Measure EuclN).restrict Ω := by
    unfold chartPulledWeightedMeasure
    exact (withDensity_absolutelyContinuous (volume : Measure EuclN) _).restrict Ω
  -- `f` vanishes a.e. off `K` for the weighted restricted measure too.
  have hf_w : ∀ᵐ y ∂((chartPulledWeightedMeasure (I := I) g α).restrict Ω),
      y ∉ K → f y = 0 := h_abs.ae_le hf'
  -- `f` agrees a.e. with `K.indicator f` for both measures.
  have h_ind_w : f =ᵐ[(chartPulledWeightedMeasure (I := I) g α).restrict Ω]
      K.indicator f := by
    filter_upwards [hf_w] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  have h_ind_v : f =ᵐ[(volume : Measure EuclN).restrict Ω] K.indicator f := by
    filter_upwards [hf'] with y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, hy hyK]
  -- Rewrite both `eLpNorm`s through the indicator and restrict to `K`.
  rw [eLpNorm_congr_ae h_ind_w, eLpNorm_congr_ae h_ind_v,
    eLpNorm_indicator_eq_eLpNorm_restrict hK_meas,
    eLpNorm_indicator_eq_eLpNorm_restrict hK_meas,
    Measure.restrict_restrict_of_subset hK_in,
    Measure.restrict_restrict_of_subset hK_in]
  -- Dominate the weighted measure on `K`, then split the scalar.
  have h_mono :
      eLpNorm f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K)
        ≤ eLpNorm f 2
            (ENNReal.ofReal c_max • ((volume : Measure EuclN).restrict K)) :=
    eLpNorm_mono_measure f hc_le_meas
  refine h_mono.trans ?_
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have h_toReal : ((1 / 2 : ℝ≥0∞).toReal : ℝ) = (1 : ℝ) / 2 := by
    rw [show (1 / 2 : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 from rfl]; simp
  rw [h_toReal]
  have h_pow_eq : ENNReal.ofReal c_max ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.sqrt c_max) := by
    rw [Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_rpow_of_nonneg hc_max_pos.le (by positivity)]
  rw [h_pow_eq, smul_eq_mul]

/-! ## A uniform weighted bound for the canonical Euclidean chart component

The canonical Euclidean chart component `tensorL2ChartComponent g r s u α P₀` of
an abstract `L²` element `u` vanishes almost everywhere off the compact
partition-of-unity kernel `chartPouKernel α`; on that kernel the chart density is
bounded above. Composing the operator-norm bound for the chart-component
continuous linear map `tensorL2ChartComponentCLM g r s α P₀` with the
weighted-versus-volume comparison yields a single chart-geometric constant
controlling the weighted `eLpNorm` of the chart component for every `u`. -/

omit [CompleteSpace E] in
/-- The canonical Euclidean chart component vanishes almost everywhere — for the
plain Lebesgue volume restricted to the off-kernel set — off the compact
partition-of-unity kernel `chartPouKernel α`. This recasts the
`chartL2Measure`-a.e. vanishing `tensorL2ChartComponent_ae_zero_off_chartPouKernel`
as an `=ᵐ` on the off-kernel set. -/
private lemma tensorL2ChartComponent_aeEq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    (fun y => (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
        EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) α) :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
      chartPouKernel (I := I) (M := M) α) := hΩ_meas.diff hK_meas
  -- The `chartL2Measure`-a.e. vanishing off the kernel. `chartL2Measure α` is
  -- definitionally `volume.restrict (chartTargetEuclid α)`.
  have h_ae := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s u α P₀
  -- Unfold `chartL2Measure` to the plain restricted volume and recast as a
  -- `volume`-a.e. implication on the open chart target.
  have h_ae_v : ∀ᵐ y ∂(volume : Measure EuclN), y ∈
        chartTargetEuclid (I := I) (M := M) α →
      y ∉ chartPouKernel (I := I) (M := M) α →
        (tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
          EuclN → ℝ) y = 0 :=
    (ae_restrict_iff' hΩ_meas).mp h_ae
  -- Restrict the implication to the off-kernel set.
  rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
  filter_upwards [h_ae_v] with y hy hy_mem
  exact hy hy_mem.1 hy_mem.2

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 800000 in
/-- **Uniform-constant weighted-`eLpNorm` bound for the canonical Euclidean chart
component.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart
center `α : M`, and a component multi-index `P₀`, there is a single nonnegative
constant `C` — depending only on `g, r, s, α, P₀` — such that for every abstract
`L²` element `u : TensorL2 r s g`,

```
eLpNorm (tensorL2ChartComponent g r s u α P₀) 2 μw ≤ ENNReal.ofReal C · ENNReal.ofReal ‖u‖,
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

The canonical chart component is the value of the continuous linear map
`tensorL2ChartComponentCLM g r s α P₀`, so its chart `L²` norm is bounded by the
operator norm of that map times `‖u‖`. The chart component vanishes almost
everywhere off the compact partition-of-unity kernel, so the
weighted-versus-volume comparison upgrades the plain-volume `L²` norm — the chart
`L²` norm — to the weighted `eLpNorm`. -/
theorem eLpNorm_tensorL2ChartComponent_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : TensorL2 r s g,
        eLpNorm ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C * ENNReal.ofReal ‖u‖ := by
  classical
  -- The weighted-versus-volume comparison constant on the partition-of-unity
  -- kernel — independent of the abstract element.
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact (I := I) (M := M) g α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  -- The operator norm of the chart-component continuous linear map.
  set Cop : ℝ := ‖tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀‖
    with hCop_def
  have hCop_nn : 0 ≤ Cop :=
    norm_nonneg (tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀)
  refine ⟨Ccmp * Cop, mul_nonneg hCcmp_nn hCop_nn, fun u => ?_⟩
  -- The chart component vanishes a.e. off the compact kernel.
  have h_off := tensorL2ChartComponent_aeEq_zero_off_chartPouKernel
    (I := I) (M := M) g r s u α P₀
  -- The plain-volume `eLpNorm` of the chart component is `ofReal` of its chart
  -- `L²` norm; the operator-norm bound gives `‖·‖ ≤ Cop · ‖u‖`.
  have h_eLp_eq :
      eLpNorm ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) =
        ENNReal.ofReal ‖tensorL2ChartComponent (I := I) (M := M) g r s u α P₀‖ := by
    rw [show (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        chartL2Measure (I := I) (M := M) α from rfl,
      Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  have h_op : ‖tensorL2ChartComponent (I := I) (M := M) g r s u α P₀‖ ≤
      Cop * ‖u‖ := by
    rw [hCop_def,
      ← tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s α P₀ u]
    exact (tensorL2ChartComponentCLM (I := I) (M := M) g r s α P₀).le_opNorm u
  -- Assemble: weighted-versus-volume comparison, then the operator-norm bound.
  calc eLpNorm ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccmp *
          eLpNorm ((tensorL2ChartComponent (I := I) (M := M) g r s u α P₀ :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) :=
        hCcmp_bd _ h_off
    _ = ENNReal.ofReal Ccmp *
          ENNReal.ofReal
            ‖tensorL2ChartComponent (I := I) (M := M) g r s u α P₀‖ := by
        rw [h_eLp_eq]
    _ ≤ ENNReal.ofReal Ccmp * ENNReal.ofReal (Cop * ‖u‖) := by
        gcongr
    _ = ENNReal.ofReal (Ccmp * Cop) * ENNReal.ofReal ‖u‖ := by
        rw [ENNReal.ofReal_mul hCop_nn, ENNReal.ofReal_mul hCcmp_nn, mul_assoc]

/-! ## The six per-atom weighted-`eLpNorm` energy bounds

Each of the six source atoms of `eigenvectorChartRHS_eLpNorm_le_uniform` is
bounded — with a chart-geometric, eigenbasis-index-uniform constant — by a
`μ`-power times the abstract `L²` norm of the eigenbasis vector. The `μ`-power is
`1/2` for the gradient-order atoms, `1` for the cross-right and chart-component
atoms, and `0` for the bare chart component. -/

section AtomBounds

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)

/-- **Atom 1 — the bare eigenvector chart component.** A chart-geometric
constant, uniform over `i`, bounds the weighted `eLpNorm` of
`eigenvectorChartComponentFun g r s h_atlas i α P₀` by the constant times the
abstract `L²` norm of the eigenbasis vector. The chart component is, by
definition, the canonical Euclidean chart component of the eigenbasis vector;
the uniform bound `eLpNorm_tensorL2ChartComponent_le_uniform` applies. -/
private lemma eigenvectorChartComponentFun_eLpNorm_le_energy
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_tensorL2ChartComponent_le_uniform
    (I := I) (M := M) g r s α P₀
  exact ⟨C, hC_nn, fun i => hC_bd
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)⟩

/-- **Atom 2 — the cross-left limit object.** A chart-geometric constant, uniform
over `i`, bounds the weighted `eLpNorm` of `crossLeftLimitComponent g r s h_atlas
i α P` by the constant times `√μ` times the abstract `L²` norm of the eigenbasis
vector. The committed `eLpNorm_crossLeftLimitComponent_le_uniform` bounds the
atom by an abstract gradient norm; the gradient-energy identity
`tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le` collapses that norm to
`√μ · ‖φ‖`. -/
private lemma crossLeftLimitComponent_eLpNorm_le_energy
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * Real.sqrt i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_crossLeftLimitComponent_le_uniform
    (I := I) (M := M) g r s h_atlas α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  refine (hC_bd i).trans ?_
  -- Collapse `‖tensorCovGradL2Compl (eigenvectorResolvent …)‖ ≤ √μ · ‖φ‖`.
  rw [ENNReal.ofReal_mul hC_nn]
  refine le_trans (mul_le_mul' (le_refl _)
    (ENNReal.ofReal_le_ofReal
      (tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le
        (I := I) (M := M) g r s h_atlas i))) ?_
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← mul_assoc]

/-- **Atom 3 — the cross-right limit object.** A chart-geometric constant,
uniform over `i`, bounds the weighted `eLpNorm` of `crossRightLimitComponent g r
s h_atlas i α P` by the constant times `μ` times the abstract `L²` norm of the
eigenbasis vector. The committed `eLpNorm_crossRightLimitComponent_le_uniform`
bounds the atom by `‖TensorH1ComplToTensorL2 (eigenvectorResolvent …)‖`; the
eigen-equation exhibits `TensorH1ComplToTensorL2 (eigenvectorResolvent …) = μ • φ`,
so that norm is `μ · ‖φ‖`. -/
private lemma crossRightLimitComponent_eLpNorm_le_energy
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((crossRightLimitComponent (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_crossRightLimitComponent_le_uniform
    (I := I) (M := M) g r s h_atlas α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  have hμ_nn : 0 ≤ i.fst.val :=
    le_of_lt (eigenvalue_mem_Ioc (I := I) (M := M) g r s h_atlas i).1
  -- The eigen-equation: `TensorH1ComplToTensorL2 (eigenvectorResolvent …) = μ • φ`.
  have h_l2 : TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i) =
      i.fst.val • tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i := by
    rw [eigenvectorResolvent, ← tensorResolventL2_apply (I := I) (M := M) g r s]
    exact (mem_tensorResolventEigenspace_iff (I := I) (M := M) g r s i.fst.val
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)).mp
      (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
  have h_norm : ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)‖ =
      i.fst.val *
        ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
    rw [h_l2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ_nn]
  refine (hC_bd i).trans ?_
  rw [h_norm, ENNReal.ofReal_mul hC_nn, ENNReal.ofReal_mul hμ_nn, mul_assoc]

/-- **Atom 4 — the chart-partial limit object.** A chart-geometric constant,
uniform over `i`, bounds the weighted `eLpNorm` of `partialLpLimit g r s h_atlas
i α P k` by the constant times `√μ` times the abstract `L²` norm of the
eigenbasis vector. The committed `partialLpLimit_eLpNorm_le` supplies the bound
on plain Lebesgue volume; the chart-partial atom vanishes almost everywhere off
the compact partition-of-unity kernel (it is the `μ`-rescaling of the eigenvector
weak chart partial, which does), so the weighted-versus-volume comparison
transfers the bound to the chart-pulled weighted measure. -/
private lemma partialLpLimit_eLpNorm_le_energy
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((partialLpLimit (I := I) (M := M)
            g r s h_atlas i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * Real.sqrt i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- The weighted-versus-volume comparison constant on the partition-of-unity
  -- kernel.
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact (I := I) (M := M) g α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  -- The plain-volume energy bound for the chart-partial atom.
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    partialLpLimit_eLpNorm_le (I := I) (M := M) g r s h_atlas α P k
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, fun i => ?_⟩
  -- The chart-partial atom vanishes a.e. off the compact kernel: it is the
  -- `μ`-rescaling of the eigenvector weak chart partial.
  have h_off : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
    -- `partialLpLimit = μ • eigenvectorChartWeakPartial`.
    have h_smul : (fun y => ((partialLpLimit (I := I) (M := M)
          g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
        (fun y => i.fst.val •
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s h_atlas i α P k y) := by
      have h_ac : (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α) ≪
          chartL2Measure (I := I) (M := M) α := by
        rw [show chartL2Measure (I := I) (M := M) α =
            (volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α) from rfl]
        exact Measure.absolutelyContinuous_of_le
          (Measure.restrict_mono Set.diff_subset le_rfl)
      refine h_ac.ae_eq ?_
      rw [partialLpLimit, eigenvectorChartWeakPartial]
      exact Lp.coeFn_smul i.fst.val _
    -- The eigenvector weak chart partial vanishes a.e. off the kernel.
    have h_weak := eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s h_atlas i α P k
    filter_upwards [h_smul, h_weak] with y hy hy_zero
    rw [hy, hy_zero, smul_zero]
  -- Assemble: weighted-versus-volume comparison, then the plain-volume bound.
  refine le_trans (hCcmp_bd _ h_off) ?_
  refine le_trans (mul_le_mul' (le_refl _) (hCvol_bd i)) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn,
    show Ccmp * (Cvol * Real.sqrt i.fst.val) =
      Ccmp * Cvol * Real.sqrt i.fst.val from (mul_assoc _ _ _).symm]

/-- **Atom 5 — the chart-component limit object.** A chart-geometric constant,
uniform over `i`, bounds the weighted `eLpNorm` of `componentLpLimit g r s
h_atlas i α P` by the constant times `μ` times the abstract `L²` norm of the
eigenbasis vector. The atom is, by definition, `μ` times the canonical Euclidean
chart component of the eigenbasis vector; the homogeneity of `eLpNorm` extracts
the `μ` factor and the uniform bound `eLpNorm_tensorL2ChartComponent_le_uniform`
controls the remaining chart component. -/
private lemma componentLpLimit_eLpNorm_le_energy
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((componentLpLimit (I := I) (M := M)
            g r s h_atlas i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_tensorL2ChartComponent_le_uniform
    (I := I) (M := M) g r s α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hμ_nn : 0 ≤ i.fst.val :=
    le_of_lt (eigenvalue_mem_Ioc (I := I) (M := M) g r s h_atlas i).1
  -- `componentLpLimit = μ • tensorL2ChartComponent (φ) α P`; the coercion is
  -- a.e. `μ • (chart component coercion)`, so the `eLpNorm` factors out `μ`.
  have h_smul : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[μw]
      i.fst.val •
        (((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)) := by
    have h_ac : μw ≪ chartL2Measure (I := I) (M := M) α := by
      rw [hμw_def]
      exact chartPulledWeightedMeasure_restrict_absolutelyContinuous
        (I := I) (M := M) g α
    refine h_ac.ae_eq ?_
    rw [componentLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  rw [eLpNorm_congr_ae h_smul]
  -- `eLpNorm (μ • h) = ‖μ‖ₑ • eLpNorm h = ofReal μ · eLpNorm h`.
  rw [eLpNorm_const_smul (μ := μw) (p := 2) i.fst.val
    (((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)),
    Real.enorm_of_nonneg hμ_nn]
  -- Bound the chart component, then collect the `μ` factor.
  refine le_trans (mul_le_mul' (le_refl _) (hC_bd
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i))) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_nn, mul_comm i.fst.val C]

/-- **Atom 6 — the cutoff chart-partial limit object.** A chart-geometric
constant, uniform over `i`, bounds the weighted `eLpNorm` of
`cutoffPartialLpLimit g r s h_atlas i α P k` by the constant times `√μ` times the
abstract `L²` norm of the eigenbasis vector. The committed
`cutoffPartialLpLimit_eLpNorm_le` supplies the bound on plain Lebesgue volume;
the cutoff chart-partial atom vanishes almost everywhere off the compact cutoff
kernel (`cutoffPartialLpLimit_ae_zero_off_cutoffChartKernelEuclid`), so the
weighted-versus-volume comparison transfers the bound to the chart-pulled
weighted measure. -/
private lemma cutoffPartialLpLimit_eLpNorm_le_energy
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
            g r s h_atlas i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * Real.sqrt i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- The weighted-versus-volume comparison constant on the cutoff kernel.
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact (I := I) (M := M) g α
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
  -- The plain-volume energy bound for the cutoff chart-partial atom.
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    cutoffPartialLpLimit_eLpNorm_le (I := I) (M := M) g r s h_atlas α P k
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, fun i => ?_⟩
  -- The cutoff chart-partial atom vanishes a.e. off the compact cutoff kernel.
  have h_off : (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          cutoffChartKernelEuclid (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
    have hKc_meas : MeasurableSet (cutoffChartKernelEuclid (I := I) (M := M) α) :=
      cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α
    have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α).measurableSet
    have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
        cutoffChartKernelEuclid (I := I) (M := M) α) := hΩ_meas.diff hKc_meas
    -- The committed off-cutoff-kernel a.e.-vanishing on `volume.restrict Ω`,
    -- recast as a `volume`-a.e. implication.
    have h_ae := cutoffPartialLpLimit_ae_zero_off_cutoffChartKernelEuclid
      (I := I) (M := M) g r s h_atlas i α P k
    have h_ae_v : ∀ᵐ y ∂(volume : Measure EuclN), y ∈
          chartTargetEuclid (I := I) (M := M) α →
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((cutoffPartialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 :=
      (ae_restrict_iff' hΩ_meas).mp h_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
    filter_upwards [h_ae_v] with y hy hy_mem
    exact hy hy_mem.1 hy_mem.2
  -- Assemble: weighted-versus-volume comparison, then the plain-volume bound.
  refine le_trans (hCcmp_bd _ h_off) ?_
  refine le_trans (mul_le_mul' (le_refl _) (hCvol_bd i)) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn,
    show Ccmp * (Cvol * Real.sqrt i.fst.val) =
      Ccmp * Cvol * Real.sqrt i.fst.val from (mul_assoc _ _ _).symm]

end AtomBounds

/-! ## The six per-atom weighted-`eLpNorm` energy bounds (chart-locality-free)

Chart-locality-free twins of the six per-atom energy bounds, re-keyed onto the
`_unconditional` source-quantity families and the unconditional eigenbasis vector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic
g r s) i`. The proofs transfer verbatim from the `h_atlas`-keyed originals via
the committed `_unconditional` upstream twins; no chart-selection hypothesis
appears. -/

section AtomBoundsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

/-- **Atom 1 — the bare eigenvector chart component (chart-locality-free).**
Chart-locality-free twin of `eigenvectorChartComponentFun_eLpNorm_le_energy`. The
unconditional chart component `eigenvectorChartComponentFun_unconditional` is, by
definition, the canonical Euclidean chart component of the unconditional
eigenbasis vector; the uniform bound `eLpNorm_tensorL2ChartComponent_le_uniform`
applies. -/
private lemma eigenvectorChartComponentFun_eLpNorm_le_energy_unconditional
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal C *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_tensorL2ChartComponent_le_uniform
    (I := I) (M := M) g r s α P₀
  exact ⟨C, hC_nn, fun i => hC_bd
    (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s) i)⟩

/-- **Atom 2 — the cross-left limit object (chart-locality-free).**
Chart-locality-free twin of `crossLeftLimitComponent_eLpNorm_le_energy`. The
committed `eLpNorm_crossLeftLimitComponent_le_uniform_unconditional` bounds the
atom by an abstract gradient norm; the gradient-energy identity
`tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le_unconditional` collapses that
norm to `√μ · ‖φ‖`. -/
private lemma crossLeftLimitComponent_eLpNorm_le_energy_unconditional
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((crossLeftLimitComponent_unconditional (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * Real.sqrt i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_crossLeftLimitComponent_le_uniform_unconditional
    (I := I) (M := M) g r s α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  refine (hC_bd i).trans ?_
  -- Collapse `‖tensorCovGradL2Compl (eigenvectorResolvent_unconditional …)‖ ≤ √μ · ‖φ‖`.
  rw [ENNReal.ofReal_mul hC_nn]
  refine le_trans (mul_le_mul' (le_refl _)
    (ENNReal.ofReal_le_ofReal
      (tensorCovGradL2Compl_eigenvectorResolvent_l2Norm_le_unconditional
        (I := I) (M := M) g r s i))) ?_
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← mul_assoc]

/-- **Atom 3 — the cross-right limit object (chart-locality-free).**
Chart-locality-free twin of `crossRightLimitComponent_eLpNorm_le_energy`. The
committed `eLpNorm_crossRightLimitComponent_le_uniform_unconditional` bounds the
atom by `‖TensorH1ComplToTensorL2 (eigenvectorResolvent_unconditional …)‖`; the
eigen-equation exhibits `TensorH1ComplToTensorL2 (eigenvectorResolvent_unconditional
…) = μ • φ`, so that norm is `μ · ‖φ‖`. -/
private lemma crossRightLimitComponent_eLpNorm_le_energy_unconditional
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((crossRightLimitComponent_unconditional (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_crossRightLimitComponent_le_uniform_unconditional
    (I := I) (M := M) g r s α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  have hμ_nn : 0 ≤ i.fst.val :=
    le_of_lt (eigenvalue_mem_Ioc_unconditional (I := I) (M := M) g r s i).1
  -- The eigen-equation: `TensorH1ComplToTensorL2 (eigenvectorResolvent_unconditional
  -- …) = μ • φ`.
  have h_l2 : TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i) =
      i.fst.val •
        tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i := by
    rw [eigenvectorResolvent_unconditional,
      ← tensorResolventL2_apply (I := I) (M := M) g r s]
    exact (mem_tensorResolventEigenspace_iff (I := I) (M := M) g r s i.fst.val
        (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i)).mp
      (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i)
  have h_norm : ‖TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)‖ =
      i.fst.val *
        ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i‖ := by
    rw [h_l2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ_nn]
  refine (hC_bd i).trans ?_
  rw [h_norm, ENNReal.ofReal_mul hC_nn, ENNReal.ofReal_mul hμ_nn, mul_assoc]

/-- **Atom 4 — the chart-partial limit object (chart-locality-free).**
Chart-locality-free twin of `partialLpLimit_eLpNorm_le_energy`. The committed
`partialLpLimit_eLpNorm_le_unconditional` supplies the bound on plain Lebesgue
volume; the chart-partial atom vanishes almost everywhere off the compact
partition-of-unity kernel (it is the `μ`-rescaling of the eigenvector weak chart
partial, which does), so the weighted-versus-volume comparison transfers the
bound to the chart-pulled weighted measure. -/
private lemma partialLpLimit_eLpNorm_le_energy_unconditional
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
            g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * Real.sqrt i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  -- The weighted-versus-volume comparison constant on the partition-of-unity
  -- kernel.
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact (I := I) (M := M) g α
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
  -- The plain-volume energy bound for the chart-partial atom.
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    partialLpLimit_eLpNorm_le_unconditional (I := I) (M := M) g r s α P k
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, fun i => ?_⟩
  -- The chart-partial atom vanishes a.e. off the compact kernel: it is the
  -- `μ`-rescaling of the eigenvector weak chart partial.
  have h_off : (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
    -- `partialLpLimit_unconditional = μ • eigenvectorChartWeakPartial_unconditional`.
    have h_smul : (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
        (fun y => i.fst.val •
          eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
            g r s i α P k y) := by
      have h_ac : (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α) ≪
          chartL2Measure (I := I) (M := M) α := by
        rw [show chartL2Measure (I := I) (M := M) α =
            (volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α) from rfl]
        exact Measure.absolutelyContinuous_of_le
          (Measure.restrict_mono Set.diff_subset le_rfl)
      refine h_ac.ae_eq ?_
      rw [partialLpLimit_unconditional, eigenvectorChartWeakPartial_unconditional]
      exact Lp.coeFn_smul i.fst.val _
    -- The eigenvector weak chart partial vanishes a.e. off the kernel.
    have h_weak := eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel_unconditional
      (I := I) (M := M) g r s i α P k
    filter_upwards [h_smul, h_weak] with y hy hy_zero
    rw [hy, hy_zero, smul_zero]
  -- Assemble: weighted-versus-volume comparison, then the plain-volume bound.
  refine le_trans (hCcmp_bd _ h_off) ?_
  refine le_trans (mul_le_mul' (le_refl _) (hCvol_bd i)) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn,
    show Ccmp * (Cvol * Real.sqrt i.fst.val) =
      Ccmp * Cvol * Real.sqrt i.fst.val from (mul_assoc _ _ _).symm]

/-- **Atom 5 — the chart-component limit object (chart-locality-free).**
Chart-locality-free twin of `componentLpLimit_eLpNorm_le_energy`. The atom is, by
definition, `μ` times the canonical Euclidean chart component of the unconditional
eigenbasis vector; the homogeneity of `eLpNorm` extracts the `μ` factor and the
uniform bound `eLpNorm_tensorL2ChartComponent_le_uniform` controls the remaining
chart component. -/
private lemma componentLpLimit_eLpNorm_le_energy_unconditional
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
            g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ := eLpNorm_tensorL2ChartComponent_le_uniform
    (I := I) (M := M) g r s α P
  refine ⟨C, hC_nn, fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  have hμ_nn : 0 ≤ i.fst.val :=
    le_of_lt (eigenvalue_mem_Ioc_unconditional (I := I) (M := M) g r s i).1
  -- `componentLpLimit_unconditional = μ • tensorL2ChartComponent (φ) α P`; the
  -- coercion is a.e. `μ • (chart component coercion)`, so the `eLpNorm` factors
  -- out `μ`.
  have h_smul : (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[μw]
      i.fst.val •
        (((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)) := by
    have h_ac : μw ≪ chartL2Measure (I := I) (M := M) α := by
      rw [hμw_def]
      exact chartPulledWeightedMeasure_restrict_absolutelyContinuous
        (I := I) (M := M) g α
    refine h_ac.ae_eq ?_
    rw [componentLpLimit_unconditional]
    exact Lp.coeFn_smul i.fst.val _
  rw [eLpNorm_congr_ae h_smul]
  -- `eLpNorm (μ • h) = ‖μ‖ₑ • eLpNorm h = ofReal μ · eLpNorm h`.
  rw [eLpNorm_const_smul (μ := μw) (p := 2) i.fst.val
    (((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i) α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)),
    Real.enorm_of_nonneg hμ_nn]
  -- Bound the chart component, then collect the `μ` factor.
  refine le_trans (mul_le_mul' (le_refl _) (hC_bd
    (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i))) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_nn, mul_comm i.fst.val C]

/-- **Atom 6 — the cutoff chart-partial limit object (chart-locality-free).**
Chart-locality-free twin of `cutoffPartialLpLimit_eLpNorm_le_energy`. The
committed `cutoffPartialLpLimit_eLpNorm_le_unconditional` supplies the bound on
plain Lebesgue volume; the cutoff chart-partial atom vanishes almost everywhere
off the compact cutoff kernel
(`cutoffPartialLpLimit_ae_zero_off_cutoffChartKernelEuclid_unconditional`), so the
weighted-versus-volume comparison transfers the bound to the chart-pulled
weighted measure. -/
private lemma cutoffPartialLpLimit_eLpNorm_le_energy_unconditional
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
            g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * Real.sqrt i.fst.val) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  -- The weighted-versus-volume comparison constant on the cutoff kernel.
  obtain ⟨Ccmp, hCcmp_nn, hCcmp_bd⟩ :=
    eLpNorm_chartPulledWeighted_le_of_ae_zero_off_compact (I := I) (M := M) g α
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
  -- The plain-volume energy bound for the cutoff chart-partial atom.
  obtain ⟨Cvol, hCvol_nn, hCvol_bd⟩ :=
    cutoffPartialLpLimit_eLpNorm_le_unconditional (I := I) (M := M) g r s α P k
  refine ⟨Ccmp * Cvol, mul_nonneg hCcmp_nn hCvol_nn, fun i => ?_⟩
  -- The cutoff chart-partial atom vanishes a.e. off the compact cutoff kernel.
  have h_off : (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          cutoffChartKernelEuclid (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
    have hKc_meas : MeasurableSet (cutoffChartKernelEuclid (I := I) (M := M) α) :=
      cutoffChartKernelEuclid_measurableSet (I := I) (M := M) α
    have hΩ_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α).measurableSet
    have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
        cutoffChartKernelEuclid (I := I) (M := M) α) := hΩ_meas.diff hKc_meas
    -- The committed off-cutoff-kernel a.e.-vanishing on `volume.restrict Ω`,
    -- recast as a `volume`-a.e. implication.
    have h_ae := cutoffPartialLpLimit_ae_zero_off_cutoffChartKernelEuclid_unconditional
      (I := I) (M := M) g r s i α P k
    have h_ae_v : ∀ᵐ y ∂(volume : Measure EuclN), y ∈
          chartTargetEuclid (I := I) (M := M) α →
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
              g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 :=
      (ae_restrict_iff' hΩ_meas).mp h_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
    filter_upwards [h_ae_v] with y hy hy_mem
    exact hy hy_mem.1 hy_mem.2
  -- Assemble: weighted-versus-volume comparison, then the plain-volume bound.
  refine le_trans (hCcmp_bd _ h_off) ?_
  refine le_trans (mul_le_mul' (le_refl _) (hCvol_bd i)) (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hCcmp_nn,
    show Ccmp * (Cvol * Real.sqrt i.fst.val) =
      Ccmp * Cvol * Real.sqrt i.fst.val from (mul_assoc _ _ _).symm]

end AtomBoundsUnconditional

/-! ## A `μ`-power collapse helper

Each per-atom bound carries a `μ`-power factor — `√μ`, `μ`, or `1`. Since the
resolvent eigenvalue `μ` lies in `(0, 1]`, every such power is at most `1`, so
each per-atom right-hand side is bounded by the same constant times `‖φ‖`. -/

/-- For `μ ≤ 1` and `0 ≤ C`, both `ENNReal.ofReal (C · √μ)` and
`ENNReal.ofReal (C · μ)` are bounded above by `ENNReal.ofReal C`: the `μ`-power
is at most `1`. -/
private lemma ofReal_mul_muPow_le_ofReal {C μ : ℝ} (hC : 0 ≤ C)
    (hμ_le : μ ≤ 1) :
    ENNReal.ofReal (C * Real.sqrt μ) ≤ ENNReal.ofReal C ∧
      ENNReal.ofReal (C * μ) ≤ ENNReal.ofReal C := by
  have h_sqrt_le : Real.sqrt μ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hμ_le
  refine ⟨ENNReal.ofReal_le_ofReal ?_, ENNReal.ofReal_le_ofReal ?_⟩
  · calc C * Real.sqrt μ ≤ C * 1 :=
          mul_le_mul_of_nonneg_left h_sqrt_le hC
      _ = C := mul_one C
  · calc C * μ ≤ C * 1 := mul_le_mul_of_nonneg_left hμ_le hC
      _ = C := mul_one C

/-! ## The headline uniform energy bound

Starting from `eigenvectorChartRHS_eLpNorm_le_uniform`, the six-summand source
aggregate is bounded — atom by atom — by a single chart-geometric constant times
the abstract `L²` norm of the eigenbasis vector. The `μ⁻¹` prefactor of
`eigenvectorChartRHS_eLpNorm_le_uniform` then produces the single explicit `μ⁻¹`
power of the headline. -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
/-- **The uniform energy bound for the eigenvector chart right-hand side.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, and a component multi-index `P₀`, there is a single nonnegative
constant `C` — geometric (chart-transition / density / dimension / operator-norm
data), independent of the eigenbasis index — such that for *every* eigenbasis
index `i`, with resolvent eigenvalue `μ := i.fst.val`, the weighted `eLpNorm` of
the chart-Euclidean right-hand side `eigenvectorChartRHS g r s h_atlas i α P₀` is
bounded by `ENNReal.ofReal (C · μ⁻¹)` times the abstract `L²` norm of the
eigenbasis vector `tensorResolventEigenbasisVec h_atlas i`:

```
eLpNorm (eigenvectorChartRHS g r s h_atlas i α P₀) 2 μw
  ≤ ENNReal.ofReal (C · μ⁻¹) · ENNReal.ofReal ‖tensorResolventEigenbasisVec …‖,
```

where `μw = (chartPulledWeightedMeasure g α).restrict (chartTargetEuclid α)`.

The explicit eigenvalue factor `μ⁻¹` stays *inside* the `∀ i` — it is a genuine
per-`i` quantity — while only the geometric constant `C` is hoisted before the
`∀ i`. The bound is genuine and not the vacuous per-`i` ratio: a single `C`
controls the chart right-hand side of *every* eigenvector simultaneously.

The proof exhibits the uniform witness of `eigenvectorChartRHS_eLpNorm_le_uniform`,
whose six-summand source aggregate is bounded — atom by atom, by the six
companion energy lemmas — by `C' · ‖φ‖`: each gradient-order atom carries a `√μ`
factor and each order-`0` atom a `μ` or `1` factor, all `≤ 1` because the
resolvent eigenvalue lies in `(0, 1]`. The `μ⁻¹` prefactor of
`eigenvectorChartRHS_eLpNorm_le_uniform` then yields the headline. -/
theorem eigenvectorChartRHS_eLpNorm_le_energy
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  -- The uniform `μ⁻¹`-prefactor bound: the six-summand source aggregate.
  obtain ⟨Crhs, hCrhs_nn, hCrhs_bd⟩ :=
    eigenvectorChartRHS_eLpNorm_le_uniform (I := I) (M := M) g r s h_atlas α P₀
  -- The six per-atom energy bounds.
  obtain ⟨C1, hC1_nn, hC1_bd⟩ := eigenvectorChartComponentFun_eLpNorm_le_energy
    (I := I) (M := M) g r s h_atlas α P₀
  -- Atoms 2 and 4 are summed over `TensorCompIdx r (s + 1)` / direction `k`;
  -- atom 6 over `TensorCompIdx r s` / direction `l`; choose uniform constants.
  choose C2 hC2_nn hC2_bd using fun P : TensorCompIdx (E := E) r (s + 1) =>
    crossLeftLimitComponent_eLpNorm_le_energy (I := I) (M := M)
      g r s h_atlas α P
  choose C3 hC3_nn hC3_bd using fun P : TensorCompIdx (E := E) r s =>
    crossRightLimitComponent_eLpNorm_le_energy (I := I) (M := M)
      g r s h_atlas α P
  choose C4 hC4_nn hC4_bd using
    fun (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) =>
      partialLpLimit_eLpNorm_le_energy (I := I) (M := M) g r s h_atlas α P k
  choose C5 hC5_nn hC5_bd using fun P : TensorCompIdx (E := E) r s =>
    componentLpLimit_eLpNorm_le_energy (I := I) (M := M) g r s h_atlas α P
  choose C6 hC6_nn hC6_bd using
    fun (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) =>
      cutoffPartialLpLimit_eLpNorm_le_energy (I := I) (M := M)
        g r s h_atlas α P l
  -- The aggregate-collapse constant: the sum of all per-atom constants over
  -- their summation indices — a finite chart-geometric quantity.
  set Cagg : ℝ :=
    C1
      + ∑ P : TensorCompIdx (E := E) r (s + 1), C2 P
      + ∑ P : TensorCompIdx (E := E) r s, C3 P
      + ∑ P : TensorCompIdx (E := E) r s, ∑ k : Fin (Module.finrank ℝ E), C4 P k
      + ∑ P : TensorCompIdx (E := E) r s, C5 P
      + ∑ P : TensorCompIdx (E := E) r s, ∑ l : Fin (Module.finrank ℝ E), C6 P l
    with hCagg_def
  have hCagg_nn : 0 ≤ Cagg := by
    rw [hCagg_def]
    have h2 : 0 ≤ ∑ P : TensorCompIdx (E := E) r (s + 1), C2 P :=
      Finset.sum_nonneg (fun P _ => hC2_nn P)
    have h3 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C3 P :=
      Finset.sum_nonneg (fun P _ => hC3_nn P)
    have h4 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), C4 P k :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun k _ => hC4_nn P k))
    have h5 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C5 P :=
      Finset.sum_nonneg (fun P _ => hC5_nn P)
    have h6 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E), C6 P l :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun l _ => hC6_nn P l))
    positivity
  -- The headline constant: the `μ⁻¹`-prefactor constant times the
  -- aggregate-collapse constant.
  refine ⟨Crhs * Cagg, mul_nonneg hCrhs_nn hCagg_nn, fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  obtain ⟨hμ_pos, hμ_le⟩ := eigenvalue_mem_Ioc (I := I) (M := M) g r s h_atlas i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  set φnorm : ℝ :=
    ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ with hφnorm_def
  have hφnorm_nn : 0 ≤ φnorm := norm_nonneg _
  -- Abbreviation for the abstract-norm right-hand side factor.
  set Rhs : ℝ≥0∞ := ENNReal.ofReal φnorm with hRhs_def
  -- Each of the six atoms is `≤ ENNReal.ofReal C_atom · Rhs` (`μ`-powers folded).
  -- Atom 1.
  have hA1 :
      eLpNorm (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P₀) 2 μw
        ≤ ENNReal.ofReal C1 * Rhs := hC1_bd i
  -- Atoms 2–6 fold their `μ`-power via `ofReal_mul_muPow_le_ofReal`.
  have hfold := fun {C : ℝ} (hC : 0 ≤ C) =>
    ofReal_mul_muPow_le_ofReal (C := C) (μ := i.fst.val) hC hμ_le
  have hA2 : ∀ P : TensorCompIdx (E := E) r (s + 1),
      eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C2 P) * Rhs := fun P =>
    le_trans (hC2_bd P i)
      (mul_le_mul' (hfold (hC2_nn P)).1 (le_refl _))
  have hA3 : ∀ P : TensorCompIdx (E := E) r s,
      eLpNorm ((crossRightLimitComponent (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C3 P) * Rhs := fun P =>
    le_trans (hC3_bd P i)
      (mul_le_mul' (hfold (hC3_nn P)).2 (le_refl _))
  have hA4 : ∀ (P : TensorCompIdx (E := E) r s)
      (k : Fin (Module.finrank ℝ E)),
      eLpNorm ((partialLpLimit (I := I) (M := M)
          g r s h_atlas i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C4 P k) * Rhs := fun P k =>
    le_trans (hC4_bd P k i)
      (mul_le_mul' (hfold (hC4_nn P k)).1 (le_refl _))
  have hA5 : ∀ P : TensorCompIdx (E := E) r s,
      eLpNorm ((componentLpLimit (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C5 P) * Rhs := fun P =>
    le_trans (hC5_bd P i)
      (mul_le_mul' (hfold (hC5_nn P)).2 (le_refl _))
  have hA6 : ∀ (P : TensorCompIdx (E := E) r s)
      (l : Fin (Module.finrank ℝ E)),
      eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
          g r s h_atlas i α P l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C6 P l) * Rhs := fun P l =>
    le_trans (hC6_bd P l i)
      (mul_le_mul' (hfold (hC6_nn P l)).1 (le_refl _))
  -- The six-summand aggregate is bounded by `ofReal Cagg · Rhs`.
  -- First sum the finite-index families: each `∑ ofReal C_atom · Rhs`
  -- equals `ofReal (∑ C_atom) · Rhs`.
  have h_sum2 : (∑ P : TensorCompIdx (E := E) r (s + 1),
        eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r (s + 1), C2 P) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => hC2_nn P), Finset.sum_mul]
    exact Finset.sum_le_sum (fun P _ => hA2 P)
  have h_sum3 : (∑ P : TensorCompIdx (E := E) r s,
        eLpNorm ((crossRightLimitComponent (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s, C3 P) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => hC3_nn P), Finset.sum_mul]
    exact Finset.sum_le_sum (fun P _ => hA3 P)
  have h_sum4 : (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          eLpNorm ((partialLpLimit (I := I) (M := M)
            g r s h_atlas i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E), C4 P k) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg
        (fun P _ => Finset.sum_nonneg (fun k _ => hC4_nn P k)), Finset.sum_mul]
    refine Finset.sum_le_sum (fun P _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hC4_nn P k), Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _ => hA4 P k)
  have h_sum5 : (∑ P : TensorCompIdx (E := E) r s,
        eLpNorm ((componentLpLimit (I := I) (M := M)
          g r s h_atlas i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s, C5 P) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => hC5_nn P), Finset.sum_mul]
    exact Finset.sum_le_sum (fun P _ => hA5 P)
  have h_sum6 : (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
            g r s h_atlas i α P l :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s,
          ∑ l : Fin (Module.finrank ℝ E), C6 P l) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg
        (fun P _ => Finset.sum_nonneg (fun l _ => hC6_nn P l)), Finset.sum_mul]
    refine Finset.sum_le_sum (fun P _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => hC6_nn P l), Finset.sum_mul]
    exact Finset.sum_le_sum (fun l _ => hA6 P l)
  -- The full six-summand aggregate is bounded by `ofReal Cagg · Rhs`.
  have h_aggr :
      eLpNorm (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀) 2 μw
          + (∑ P : TensorCompIdx (E := E) r (s + 1),
              eLpNorm ((crossLeftLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              eLpNorm ((crossRightLimitComponent (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit (I := I) (M := M)
                g r s h_atlas i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              ∑ l : Fin (Module.finrank ℝ E),
                eLpNorm ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s h_atlas i α P l :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) 2 μw)
        ≤ ENNReal.ofReal Cagg * Rhs := by
    -- The per-sum nonnegativity facts.
    have hS2 : 0 ≤ ∑ P : TensorCompIdx (E := E) r (s + 1), C2 P :=
      Finset.sum_nonneg (fun P _ => hC2_nn P)
    have hS3 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C3 P :=
      Finset.sum_nonneg (fun P _ => hC3_nn P)
    have hS4 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), C4 P k :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun k _ => hC4_nn P k))
    have hS5 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C5 P :=
      Finset.sum_nonneg (fun P _ => hC5_nn P)
    have hS6 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E), C6 P l :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun l _ => hC6_nn P l))
    rw [hCagg_def]
    rw [ENNReal.ofReal_add (by positivity) hS6,
      ENNReal.ofReal_add (by positivity) hS5,
      ENNReal.ofReal_add (by positivity) hS4,
      ENNReal.ofReal_add (by positivity) hS3,
      ENNReal.ofReal_add hC1_nn hS2]
    rw [add_mul, add_mul, add_mul, add_mul, add_mul]
    refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      ?_ h_sum2) h_sum3) h_sum4) h_sum5) h_sum6
    exact hA1
  -- Chain through the uniform `μ⁻¹`-prefactor bound.
  refine le_trans (hCrhs_bd i) ?_
  -- `ofReal (μ⁻¹ · Crhs) · aggregate ≤ ofReal (μ⁻¹ · Crhs) · (ofReal Cagg · Rhs)`.
  refine le_trans (mul_le_mul' (le_refl _) h_aggr) (le_of_eq ?_)
  -- Collect the scalar factors: `ofReal (μ⁻¹·Crhs) · ofReal Cagg = ofReal (C·μ⁻¹)`.
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hRhs_def, hφnorm_def,
    show (i.fst.val)⁻¹ * Crhs * Cagg = Crhs * Cagg * (i.fst.val)⁻¹ by ring]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- **The uniform energy bound for the eigenvector chart right-hand side
(chart-locality-free).** Chart-locality-free twin of
`eigenvectorChartRHS_eLpNorm_le_energy`, re-keyed onto `eigenvectorChartRHS_unconditional`
and the unconditional eigenbasis vector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic
g r s) i`.

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, and a component multi-index `P₀`, there is a single nonnegative
constant `C` — geometric (chart-transition / density / dimension / operator-norm
data), independent of the eigenbasis index — such that for *every* eigenbasis
index `i`, with resolvent eigenvalue `μ := i.fst.val`, the weighted `eLpNorm` of
the chart-Euclidean right-hand side `eigenvectorChartRHS_unconditional g r s i α P₀`
is bounded by `ENNReal.ofReal (C · μ⁻¹)` times the abstract `L²` norm of the
unconditional eigenbasis vector.

The explicit eigenvalue factor `μ⁻¹` stays *inside* the `∀ i`; only the geometric
constant `C` is hoisted before the `∀ i`. The proof transfers verbatim from the
`h_atlas`-keyed original via the committed `_unconditional` upstream twins: the
uniform `μ⁻¹`-prefactor bound `eigenvectorChartRHS_eLpNorm_le_uniform_unconditional`
and the six companion `_unconditional` per-atom energy lemmas, with the `μ`-powers
folded by `ofReal_mul_muPow_le_ofReal` since the resolvent eigenvalue lies in
`(0, 1]`. No chart-selection hypothesis. -/
theorem eigenvectorChartRHS_eLpNorm_le_energy_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHS_unconditional (I := I) (M := M)
            g r s i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  -- The uniform `μ⁻¹`-prefactor bound: the six-summand source aggregate.
  obtain ⟨Crhs, hCrhs_nn, hCrhs_bd⟩ :=
    eigenvectorChartRHS_eLpNorm_le_uniform_unconditional (I := I) (M := M)
      g r s α P₀
  -- The six per-atom energy bounds.
  obtain ⟨C1, hC1_nn, hC1_bd⟩ :=
    eigenvectorChartComponentFun_eLpNorm_le_energy_unconditional
      (I := I) (M := M) g r s α P₀
  -- Atoms 2 and 4 are summed over `TensorCompIdx r (s + 1)` / direction `k`;
  -- atom 6 over `TensorCompIdx r s` / direction `l`; choose uniform constants.
  choose C2 hC2_nn hC2_bd using fun P : TensorCompIdx (E := E) r (s + 1) =>
    crossLeftLimitComponent_eLpNorm_le_energy_unconditional (I := I) (M := M)
      g r s α P
  choose C3 hC3_nn hC3_bd using fun P : TensorCompIdx (E := E) r s =>
    crossRightLimitComponent_eLpNorm_le_energy_unconditional (I := I) (M := M)
      g r s α P
  choose C4 hC4_nn hC4_bd using
    fun (P : TensorCompIdx (E := E) r s) (k : Fin (Module.finrank ℝ E)) =>
      partialLpLimit_eLpNorm_le_energy_unconditional (I := I) (M := M)
        g r s α P k
  choose C5 hC5_nn hC5_bd using fun P : TensorCompIdx (E := E) r s =>
    componentLpLimit_eLpNorm_le_energy_unconditional (I := I) (M := M)
      g r s α P
  choose C6 hC6_nn hC6_bd using
    fun (P : TensorCompIdx (E := E) r s) (l : Fin (Module.finrank ℝ E)) =>
      cutoffPartialLpLimit_eLpNorm_le_energy_unconditional (I := I) (M := M)
        g r s α P l
  -- The aggregate-collapse constant: the sum of all per-atom constants over
  -- their summation indices — a finite chart-geometric quantity.
  set Cagg : ℝ :=
    C1
      + ∑ P : TensorCompIdx (E := E) r (s + 1), C2 P
      + ∑ P : TensorCompIdx (E := E) r s, C3 P
      + ∑ P : TensorCompIdx (E := E) r s, ∑ k : Fin (Module.finrank ℝ E), C4 P k
      + ∑ P : TensorCompIdx (E := E) r s, C5 P
      + ∑ P : TensorCompIdx (E := E) r s, ∑ l : Fin (Module.finrank ℝ E), C6 P l
    with hCagg_def
  have hCagg_nn : 0 ≤ Cagg := by
    rw [hCagg_def]
    have h2 : 0 ≤ ∑ P : TensorCompIdx (E := E) r (s + 1), C2 P :=
      Finset.sum_nonneg (fun P _ => hC2_nn P)
    have h3 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C3 P :=
      Finset.sum_nonneg (fun P _ => hC3_nn P)
    have h4 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), C4 P k :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun k _ => hC4_nn P k))
    have h5 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C5 P :=
      Finset.sum_nonneg (fun P _ => hC5_nn P)
    have h6 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E), C6 P l :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun l _ => hC6_nn P l))
    positivity
  -- The headline constant: the `μ⁻¹`-prefactor constant times the
  -- aggregate-collapse constant.
  refine ⟨Crhs * Cagg, mul_nonneg hCrhs_nn hCagg_nn, fun i => ?_⟩
  set μw : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμw_def
  obtain ⟨hμ_pos, hμ_le⟩ :=
    eigenvalue_mem_Ioc_unconditional (I := I) (M := M) g r s i
  have hμ_inv_nn : 0 ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  set φnorm : ℝ :=
    ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i‖ with hφnorm_def
  have hφnorm_nn : 0 ≤ φnorm := norm_nonneg _
  -- Abbreviation for the abstract-norm right-hand side factor.
  set Rhs : ℝ≥0∞ := ENNReal.ofReal φnorm with hRhs_def
  -- Each of the six atoms is `≤ ENNReal.ofReal C_atom · Rhs` (`μ`-powers folded).
  -- Atom 1.
  have hA1 :
      eLpNorm (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P₀) 2 μw
        ≤ ENNReal.ofReal C1 * Rhs := hC1_bd i
  -- Atoms 2–6 fold their `μ`-power via `ofReal_mul_muPow_le_ofReal`.
  have hfold := fun {C : ℝ} (hC : 0 ≤ C) =>
    ofReal_mul_muPow_le_ofReal (C := C) (μ := i.fst.val) hC hμ_le
  have hA2 : ∀ P : TensorCompIdx (E := E) r (s + 1),
      eLpNorm ((crossLeftLimitComponent_unconditional (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C2 P) * Rhs := fun P =>
    le_trans (hC2_bd P i)
      (mul_le_mul' (hfold (hC2_nn P)).1 (le_refl _))
  have hA3 : ∀ P : TensorCompIdx (E := E) r s,
      eLpNorm ((crossRightLimitComponent_unconditional (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C3 P) * Rhs := fun P =>
    le_trans (hC3_bd P i)
      (mul_le_mul' (hfold (hC3_nn P)).2 (le_refl _))
  have hA4 : ∀ (P : TensorCompIdx (E := E) r s)
      (k : Fin (Module.finrank ℝ E)),
      eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C4 P k) * Rhs := fun P k =>
    le_trans (hC4_bd P k i)
      (mul_le_mul' (hfold (hC4_nn P k)).1 (le_refl _))
  have hA5 : ∀ P : TensorCompIdx (E := E) r s,
      eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C5 P) * Rhs := fun P =>
    le_trans (hC5_bd P i)
      (mul_le_mul' (hfold (hC5_nn P)).2 (le_refl _))
  have hA6 : ∀ (P : TensorCompIdx (E := E) r s)
      (l : Fin (Module.finrank ℝ E)),
      eLpNorm ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
          g r s i α P l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw
        ≤ ENNReal.ofReal (C6 P l) * Rhs := fun P l =>
    le_trans (hC6_bd P l i)
      (mul_le_mul' (hfold (hC6_nn P l)).1 (le_refl _))
  -- The six-summand aggregate is bounded by `ofReal Cagg · Rhs`.
  -- First sum the finite-index families: each `∑ ofReal C_atom · Rhs`
  -- equals `ofReal (∑ C_atom) · Rhs`.
  have h_sum2 : (∑ P : TensorCompIdx (E := E) r (s + 1),
        eLpNorm ((crossLeftLimitComponent_unconditional (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r (s + 1), C2 P) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => hC2_nn P), Finset.sum_mul]
    exact Finset.sum_le_sum (fun P _ => hA2 P)
  have h_sum3 : (∑ P : TensorCompIdx (E := E) r s,
        eLpNorm ((crossRightLimitComponent_unconditional (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s, C3 P) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => hC3_nn P), Finset.sum_mul]
    exact Finset.sum_le_sum (fun P _ => hA3 P)
  have h_sum4 : (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
            g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E), C4 P k) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg
        (fun P _ => Finset.sum_nonneg (fun k _ => hC4_nn P k)), Finset.sum_mul]
    refine Finset.sum_le_sum (fun P _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hC4_nn P k), Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _ => hA4 P k)
  have h_sum5 : (∑ P : TensorCompIdx (E := E) r s,
        eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s, C5 P) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun P _ => hC5_nn P), Finset.sum_mul]
    exact Finset.sum_le_sum (fun P _ => hA5 P)
  have h_sum6 : (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          eLpNorm ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
            g r s i α P l :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
      ≤ ENNReal.ofReal (∑ P : TensorCompIdx (E := E) r s,
          ∑ l : Fin (Module.finrank ℝ E), C6 P l) * Rhs := by
    rw [ENNReal.ofReal_sum_of_nonneg
        (fun P _ => Finset.sum_nonneg (fun l _ => hC6_nn P l)), Finset.sum_mul]
    refine Finset.sum_le_sum (fun P _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => hC6_nn P l), Finset.sum_mul]
    exact Finset.sum_le_sum (fun l _ => hA6 P l)
  -- The full six-summand aggregate is bounded by `ofReal Cagg · Rhs`.
  have h_aggr :
      eLpNorm (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀) 2 μw
          + (∑ P : TensorCompIdx (E := E) r (s + 1),
              eLpNorm ((crossLeftLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              eLpNorm ((crossRightLimitComponent_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              ∑ k : Fin (Module.finrank ℝ E),
                eLpNorm ((partialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P k :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              eLpNorm ((componentLpLimit_unconditional (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2 μw)
          + (∑ P : TensorCompIdx (E := E) r s,
              ∑ l : Fin (Module.finrank ℝ E),
                eLpNorm ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                  g r s i α P l :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                  EuclN → ℝ) 2 μw)
        ≤ ENNReal.ofReal Cagg * Rhs := by
    -- The per-sum nonnegativity facts.
    have hS2 : 0 ≤ ∑ P : TensorCompIdx (E := E) r (s + 1), C2 P :=
      Finset.sum_nonneg (fun P _ => hC2_nn P)
    have hS3 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C3 P :=
      Finset.sum_nonneg (fun P _ => hC3_nn P)
    have hS4 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), C4 P k :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun k _ => hC4_nn P k))
    have hS5 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s, C5 P :=
      Finset.sum_nonneg (fun P _ => hC5_nn P)
    have hS6 : 0 ≤ ∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E), C6 P l :=
      Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun l _ => hC6_nn P l))
    rw [hCagg_def]
    rw [ENNReal.ofReal_add (by positivity) hS6,
      ENNReal.ofReal_add (by positivity) hS5,
      ENNReal.ofReal_add (by positivity) hS4,
      ENNReal.ofReal_add (by positivity) hS3,
      ENNReal.ofReal_add hC1_nn hS2]
    rw [add_mul, add_mul, add_mul, add_mul, add_mul]
    refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      ?_ h_sum2) h_sum3) h_sum4) h_sum5) h_sum6
    exact hA1
  -- Chain through the uniform `μ⁻¹`-prefactor bound.
  refine le_trans (hCrhs_bd i) ?_
  -- `ofReal (μ⁻¹ · Crhs) · aggregate ≤ ofReal (μ⁻¹ · Crhs) · (ofReal Cagg · Rhs)`.
  refine le_trans (mul_le_mul' (le_refl _) h_aggr) (le_of_eq ?_)
  -- Collect the scalar factors: `ofReal (μ⁻¹·Crhs) · ofReal Cagg = ofReal (C·μ⁻¹)`.
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hRhs_def, hφnorm_def,
    show (i.fst.val)⁻¹ * Crhs * Cagg = Crhs * Cagg * (i.fst.val)⁻¹ by ring]

/-! ## Sanity test -/

section ElaborationTest

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (α : M) (P₀ : TensorCompIdx (E := E) r s)

example :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        eLpNorm (eigenvectorChartRHS (I := I) (M := M) g r s h_atlas i α P₀) 2
            ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
  eigenvectorChartRHS_eLpNorm_le_energy (I := I) (M := M) g r s h_atlas α P₀

end ElaborationTest

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
