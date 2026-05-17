import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.VariationalIdentity
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.WeakPartialOnVolume
import DifferentialGeometry.Analysis.Laplacian.Regularity.H1Compl.WeakPartialLimit
import DifferentialGeometry.Analysis.Laplacian.Regularity.H1Compl.ToLpChartBridge
import DifferentialGeometry.Analysis.Laplacian.Regularity.H1Compl.GradientH1LipschitzBound
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.VariationalLimit

/-!
# Substantive form-B general-case variational identity

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and an
element `u_h : H1Compl g` lying in `laplacianDomain g`, this file proves the
**substantive** chart-pulled variational identity for `u_h`, matching the
shape of the smooth-case identity
`laplacianDomain_variational_identity_smooth_case`:

```
(∫_{chartTarget α} ∑_{i, j} √det g · g^{ij} · (weak ∂_i u_h)(y) · ∂_j ψ(y) dy) +
  (∫_{chartTarget α} √det g · (chart-pushed POU·u_h)(y) · ψ(y) dy) =
  chartPulledIntegralCLM g α (√det g · ψ) (fHLeibniz g α u_h hu_h)
```

where:

* `(weak ∂_i u_h)(y)` denotes the chart-pushed weak `i`-th partial
  `(chartPushedWeakPartialLp g α i (canonical) u_h).coeFn(y)`;
* `(chart-pushed POU·u_h)(y) := chartPushed (chartAtlasPOU I M) α
  (H1ComplToLp u_h : M → ℝ)(y)`;
* `fHLeibniz g α u_h hu_h` is the Leibniz-compensated `L²` class.

## Strategy

For each smooth approximating sequence `v_n → u_h` in `H1Compl g`, the
smooth-case identity gives the explicit integral identity for `v_n`. The
right-hand side converges to
`chartPulledIntegralCLM g α (√det g · ψ) (fHLeibniz g α u_h hu_h)` via the
bilinear bypass machinery in `LaplacianDomainVariationalIdentity`. The
left-hand side principal and mass terms are realised as L²-inner products
in the chart-pulled-weighted measure restricted to `chartTargetEuclid α`,
and converge via the L²-continuity of the chart-pushed-weak-partial map
`H1ComplPartialCLM` and the chart-pushed-Lp class.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainVariationalIdentityIntegralForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalLimitGeneral
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentity
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientLipschitz
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientLipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## Finiteness of the chart-pulled weighted measure on compact subsets

The chart-pulled weighted measure is finite on every compact subset of
`chartTargetEuclid α`, since `densityOnEuclid g α` is continuous on the
open chart target. -/

private lemma chartPulledWeightedMeasure_lt_top_of_compact_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (chartPulledWeightedMeasure (I := I) g α) K < ⊤ := by
  classical
  by_cases hKne : K.Nonempty
  · have h_dens_contOn : ContinuousOn (densityOnEuclid (I := I) g α) K :=
      (densityOnEuclid_continuousOn (I := I) g α).mono hK_in
    obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
      hK_compact.exists_isMaxOn hKne h_dens_contOn
    set M_d : ℝ := densityOnEuclid (I := I) g α y₀ with hM_d_def
    have hM_d_bd : ∀ y ∈ K, densityOnEuclid (I := I) g α y ≤ M_d := fun y hy =>
      hy₀_max hy
    unfold chartPulledWeightedMeasure
    rw [withDensity_apply _ hK_compact.measurableSet]
    have h_int_bd :
        (∫⁻ y in K, ENNReal.ofReal (densityOnEuclid (I := I) g α y)
          ∂(volume : Measure EuclN)) ≤
          ENNReal.ofReal M_d * (volume : Measure EuclN) K := by
      calc (∫⁻ y in K, ENNReal.ofReal (densityOnEuclid (I := I) g α y)
            ∂(volume : Measure EuclN))
          ≤ ∫⁻ _y in K, ENNReal.ofReal M_d ∂(volume : Measure EuclN) := by
            refine MeasureTheory.setLIntegral_mono_ae' hK_compact.measurableSet ?_
            refine Filter.Eventually.of_forall (fun y hy => ?_)
            exact ENNReal.ofReal_le_ofReal (hM_d_bd y hy)
        _ = ENNReal.ofReal M_d * (volume : Measure EuclN) K := by
            rw [MeasureTheory.setLIntegral_const]
    refine lt_of_le_of_lt h_int_bd ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK_compact.measure_lt_top
  · rw [Set.not_nonempty_iff_eq_empty] at hKne
    rw [hKne, measure_empty]
    exact ENNReal.zero_lt_top

private lemma chartPulledWeightedMeasure_restrict_lt_top_of_compact_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) K < ⊤ := by
  rw [Measure.restrict_apply hK_compact.measurableSet]
  refine lt_of_le_of_lt
    (measure_mono (Set.inter_subset_left)) ?_
  exact chartPulledWeightedMeasure_lt_top_of_compact_subset
    (I := I) (M := M) g α hK_compact hK_in

/-! ## MemLp 2 for bounded continuous compactly-supported functions -/

lemma continuous_compactSupport_memLp_chartPulledWeighted_restrict
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : EuclN → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp f 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨C, hC_bd⟩ : ∃ C : ℝ, ∀ y : EuclN, ‖f y‖ ≤ C :=
    hf_cont.bounded_above_of_compact_support hf_cs
  have h_aestrong : AEStronglyMeasurable f
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    hf_cont.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have h_top : MemLp f ⊤
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    memLp_top_of_bound h_aestrong C (Filter.Eventually.of_forall hC_bd)
  have h_zero_off : ∀ y, y ∉ tsupport f → f y = 0 :=
    fun y hy => image_eq_zero_of_notMem_tsupport hy
  have h_supp_finite : ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) (tsupport f) ≠ ⊤ :=
    (chartPulledWeightedMeasure_restrict_lt_top_of_compact_subset
      (I := I) (M := M) g α hf_cs hf_supp).ne
  refine h_top.mono_exponent_of_measure_support_ne_top h_zero_off h_supp_finite ?_
  exact le_top

/-! ## The principal multiplier `P_i ψ y := ∑_j invGramOnEuclid · ∂_j ψ` -/

private def principalMultiplier
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (ψ : EuclN → ℝ) : EuclN → ℝ :=
  fun y =>
    ∑ j : Fin (Module.finrank ℝ E),
      invGramOnEuclid (I := I) g α i j y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1)

private lemma principalMultiplier_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    {y : EuclN} (hy : y ∉ tsupport ψ) :
    principalMultiplier (I := I) (M := M) g α i ψ y = 0 := by
  classical
  unfold principalMultiplier
  have h_fder_zero : ∀ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = 0 := by
    intro j
    have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : ψ =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [h_compl_open.mem_nhds hy] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    have h_fder_eq : fderiv ℝ ψ y = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) y :=
      Filter.EventuallyEq.fderiv_eq h_ev
    rw [h_fder_eq]
    have h_const_zero : (fun _ : EuclN => (0 : ℝ)) =
        (Function.const EuclN (0 : ℝ)) := rfl
    rw [h_const_zero, fderiv_const]
    rfl
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [h_fder_zero, mul_zero]

private lemma principalMultiplier_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContinuousOn (principalMultiplier (I := I) (M := M) g α i ψ)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold principalMultiplier
  refine continuousOn_finset_sum _ fun j _ => ?_
  have h_inv : ContinuousOn (invGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (invGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have hψ1 : ContDiff ℝ (1 : ℕ∞) ψ := hψ.of_le (by
      have h1 : (1 : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
      exact_mod_cast h1)
  have h_fder : Continuous (fun y : EuclN =>
      (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) :=
    (hψ1.continuous_fderiv (by norm_cast)).clm_apply continuous_const
  exact h_inv.mul h_fder.continuousOn

private lemma principalMultiplier_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Continuous (principalMultiplier (I := I) (M := M) g α i ψ) := by
  classical
  refine continuous_iff_continuousAt.mpr fun y => ?_
  by_cases hy : y ∈ tsupport ψ
  · have hy_T : y ∈ chartTargetEuclid (I := I) (M := M) α := hψ_supp hy
    have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
    exact (principalMultiplier_continuousOn (I := I) (M := M) g α i hψ).continuousAt
      (hOpen.mem_nhds hy_T)
  · have h_compl_open : IsOpen ((tsupport ψ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    have h_ev : (principalMultiplier (I := I) (M := M) g α i ψ) =ᶠ[𝓝 y]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [h_compl_open.mem_nhds hy] with z hz
      exact principalMultiplier_eq_zero_off_tsupport (I := I) (M := M) g α i hz
    refine ContinuousAt.congr ?_ h_ev.symm
    exact continuousAt_const

private lemma principalMultiplier_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ_cs : HasCompactSupport ψ) :
    HasCompactSupport (principalMultiplier (I := I) (M := M) g α i ψ) := by
  classical
  refine HasCompactSupport.intro (hψ_cs : IsCompact (tsupport ψ)) (fun y hy => ?_)
  exact principalMultiplier_eq_zero_off_tsupport (I := I) (M := M) g α i hy

private lemma principalMultiplier_tsupport_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    tsupport (principalMultiplier (I := I) (M := M) g α i ψ) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  refine subset_trans ?_ hψ_supp
  refine (closure_minimal ?_ (isClosed_tsupport _))
  intro y hy
  rw [Function.mem_support] at hy
  by_contra hyψ
  exact hy (principalMultiplier_eq_zero_off_tsupport (I := I) (M := M) g α i hyψ)

/-- The principal multiplier as an `Lp 2` class. -/
private noncomputable def principalMultiplierLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  (continuous_compactSupport_memLp_chartPulledWeighted_restrict
    (I := I) (M := M) g α
    (principalMultiplier_continuous (I := I) (M := M) g α i hψ hψ_supp)
    (principalMultiplier_hasCompactSupport (I := I) (M := M) g α i hψ_cs)
    (principalMultiplier_tsupport_subset (I := I) (M := M) g α i hψ_supp)).toLp _

private lemma principalMultiplierLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      principalMultiplier (I := I) (M := M) g α i ψ := by
  unfold principalMultiplierLp
  exact MemLp.coeFn_toLp _

/-! ## The mass multiplier `ψ` itself -/

private noncomputable def massMultiplierLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  (continuous_compactSupport_memLp_chartPulledWeighted_restrict
    (I := I) (M := M) g α hψ.continuous hψ_cs hψ_supp).toLp _

private lemma massMultiplierLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ((massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      ψ := by
  unfold massMultiplierLp
  exact MemLp.coeFn_toLp _

/-! ## Change-of-measure: integrals against chart-pulled-weighted vs volume

For an integrand `A` on `chartTargetEuclid α`, the integral
`∫_chartTarget A ∂(chart-pulled-weighted)` equals
`∫_chartTarget density(y) · A(y) ∂volume`. This follows from the definition
`chart-pulled-weighted = volume.withDensity (ofReal density)` and the
positivity of `density` on `chartTargetEuclid α`. -/

private lemma densityOnEuclid_aemeasurable_restrict_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) :
    AEMeasurable (fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
  -- density is continuous on chartTargetEuclid α (open), so AEMeasurable on restrict.
  exact (densityOnEuclid_continuousOn (I := I) g α).aemeasurable
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet

private lemma densityOnEuclid_lt_top_ae_restrict_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      ENNReal.ofReal (densityOnEuclid (I := I) g α y) < ⊤ :=
  Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

/-- Change of measure: the integral against the chart-pulled weighted measure
restricted to `chartTargetEuclid α` equals `∫_chartTarget density · _ ∂vol`.

(Note: the public name aligns with downstream consumers; it converts a
single integral, not a setIntegral on a strict subset.) -/
lemma setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (g : SmoothRiemannianMetric I M) (α : M) (f : EuclN → ℝ) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α, f y
        ∂(chartPulledWeightedMeasure (I := I) g α) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * f y ∂(volume : Measure EuclN) := by
  classical
  have h_target_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  unfold chartPulledWeightedMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
      (densityOnEuclid_aemeasurable_restrict_chartTarget (I := I) (M := M) g α)
      (densityOnEuclid_lt_top_ae_restrict_chartTarget (I := I) (M := M) g α)
      f h_target_meas]
  -- The integrals over `chartTarget` of `(ofReal density y).toReal • f y` and
  -- `density y * f y` agree, since on `chartTarget`, density y > 0, hence
  -- (ofReal density y).toReal = density y.
  refine MeasureTheory.setIntegral_congr_fun h_target_meas (fun y hy => ?_)
  have hy_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy
  have : (ENNReal.ofReal (densityOnEuclid (I := I) g α y)).toReal =
      densityOnEuclid (I := I) g α y :=
    ENNReal.toReal_ofReal hy_pos.le
  rw [show (ENNReal.ofReal (densityOnEuclid (I := I) g α y)).toReal • f y =
      (ENNReal.ofReal (densityOnEuclid (I := I) g α y)).toReal * f y from rfl]
  rw [this]

/-! ## Inner-product representation of the smooth-case LHS integrals

For a smooth scalar `v : SmoothScalar g`, the smooth-case LHS principal
integral (the `∂_i v · ∂_j ψ` cross term, summed over `i, j`) and the
smooth-case LHS mass integral (`∫ density · chartPushed POU α v · ψ ∂vol`)
are each expressible as `Lp 2 ((weighted).restrict chartTarget)` inner
products. -/

/-- The smooth-case LHS principal integrand for a fixed `i`, expressed as the
integral of `P_i ψ · ∂_i v` against the chart-pulled weighted measure
restricted to `chartTargetEuclid α`. -/
private lemma smooth_lhs_principal_per_i_integral_eq_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (v : SmoothScalar g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i v y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) =
      ∫ y, principalMultiplier (I := I) (M := M) g α i ψ y *
          chartPushedPartial (I := I) (M := M) g α i v y
        ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  -- Step 1: pointwise rewrite of the integrand on chartTarget.
  have h_pointwise : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      (∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i v y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =
        densityOnEuclid (I := I) g α y *
          (principalMultiplier (I := I) (M := M) g α i ψ y *
            chartPushedPartial (I := I) (M := M) g α i v y) := by
    intro y _hy
    unfold principalMultiplier
    have h_w : ∀ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y =
          densityOnEuclid (I := I) g α y * invGramOnEuclid (I := I) g α i j y :=
      fun j => rfl
    -- Substitute each weighted entry.
    have h_each : ∀ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i v y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1) =
          densityOnEuclid (I := I) g α y *
            (invGramOnEuclid (I := I) g α i j y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) *
            chartPushedPartial (I := I) (M := M) g α i v y := by
      intro j
      rw [h_w j]
      ring
    rw [Finset.sum_congr rfl (fun j _ => h_each j)]
    -- Now LHS = ∑_j density * (invGram_{ij} * ∂_j ψ) * ∂_i v.
    -- RHS = density * (∑_j invGram_{ij} * ∂_j ψ) * ∂_i v.
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  -- Step 2: rewrite the volume integral to ∫_chartTarget density · (P_i · ∂_i v) ∂vol.
  rw [MeasureTheory.setIntegral_congr_fun h_meas_chartTarget h_pointwise]
  -- Step 3: convert ∫_chartTarget density · X ∂vol to ∫_chartTarget X ∂(weighted).
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α
    (fun y => principalMultiplier (I := I) (M := M) g α i ψ y *
      chartPushedPartial (I := I) (M := M) g α i v y)]

/-- The per-`i` smooth-case integral equals the `Lp 2` inner product
`⟨principalMultiplierLp, chartPushedPartialLp v⟩`. -/
private lemma smooth_lhs_principal_per_i_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i v y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) =
      ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
        chartPushedPartialLp (I := I) (M := M) g α i v
          (chartPushedPartial_memLp (I := I) (M := M) g α i v)⟫_ℝ := by
  classical
  rw [smooth_lhs_principal_per_i_integral_eq_weighted (I := I) (M := M) g α i hψ v]
  -- Now: ∫ y, P_i ψ y * chartPushedPartial v y ∂(weighted.restrict).
  -- This is the inner product on Lp ℝ 2 (weighted.restrict).
  rw [L2.inner_def (𝕜 := ℝ)]
  -- Replace P_i ψ_lp and chartPushedPartialLp by their a.e.-representatives.
  refine MeasureTheory.integral_congr_ae ?_
  have h_P := principalMultiplierLp_coeFn (I := I) (M := M) g α i hψ hψ_cs hψ_supp
  have h_C : ((chartPushedPartialLp (I := I) (M := M) g α i v
        (chartPushedPartial_memLp (I := I) (M := M) g α i v) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedPartial (I := I) (M := M) g α i v := by
    unfold chartPushedPartialLp
    exact MemLp.coeFn_toLp _
  filter_upwards [h_P, h_C] with y h_Py h_Cy
  -- Inner product of real-valued Lp at a point y is multiplication.
  -- h_Py rewrites the principalMultiplierLp coeFn pointwise; h_Cy similarly for chartPushedPartialLp.
  -- The RHS of the integral congruence is `⟨P_lp y, C_lp y⟩_ℝ = P_lp y * C_lp y` definitionally.
  -- After substitution: principalMultiplier ψ y * chartPushedPartial v y = (P_lp y) * (C_lp y).
  -- For reals, ⟨x, y⟩_ℝ = y * x.
  rw [show @inner ℝ _ _
      (((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y)
      (((chartPushedPartialLp (I := I) (M := M) g α i v
          (chartPushedPartial_memLp (I := I) (M := M) g α i v) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) =
      (((chartPushedPartialLp (I := I) (M := M) g α i v
          (chartPushedPartial_memLp (I := I) (M := M) g α i v) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) *
      (((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) from rfl]
  rw [h_Py, h_Cy]
  ring

/-! ## The chart-pushed Lp class for `Lp ℝ 2 μ_g` -/

/-- For any `u : Lp ℝ 2 μ_g`, the chart-pushed function
`chartPushed (chartAtlasPOU I M) α u.coeFn` is in `MemLp 2` of the
chart-pulled weighted measure restricted to `chartTargetEuclid α`. -/
noncomputable def chartPushedLpFromLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  (chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
    (I := I) (M := M) g α
    (Lp.stronglyMeasurable u).measurable
    (Lp.memLp u)).toLp _

lemma chartPushedLpFromLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedLpFromLp (I := I) (M := M) g α u :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α (u : M → ℝ) := by
  unfold chartPushedLpFromLp
  exact MemLp.coeFn_toLp _

/-- Lp-convergence of `chartPushedLpFromLp` under Lp-convergence of `u`. -/
lemma chartPushedLpFromLp_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : ℕ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {u_lim : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (h_tendsto : Tendsto u atTop (𝓝 u_lim)) :
    Tendsto (fun n => chartPushedLpFromLp (I := I) (M := M) g α (u n))
      atTop (𝓝 (chartPushedLpFromLp (I := I) (M := M) g α u_lim)) := by
  classical
  -- Convert Lp-tendsto to eLpNorm-of-diff-tendsto-zero.
  have h_norm_tendsto :
      Tendsto (fun n => ‖u n - u_lim‖) atTop (𝓝 0) := by
    have h_sub : Tendsto (fun n => u n - u_lim) atTop (𝓝 0) := by
      have := h_tendsto.sub (tendsto_const_nhds (x := u_lim))
      simpa using this
    simpa using (continuous_norm.tendsto (0 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))).comp h_sub
  -- Convert ‖u n - u_lim‖ to eLpNorm.
  have h_eLpNorm_eq : ∀ n,
      eLpNorm (((u n - u_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) =
      ENNReal.ofReal ‖u n - u_lim‖ := by
    intro n
    rw [Lp.norm_def]
    rw [ENNReal.ofReal_toReal
      ((Lp.memLp (u n - u_lim)).eLpNorm_lt_top.ne)]
  -- eLpNorm of difference tends to 0.
  have h_eLpNorm_tendsto :
      Tendsto (fun n => eLpNorm (((u n - u_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
    have h_funeq : (fun n =>
        eLpNorm (((u n - u_lim) : Lp ℝ 2 _) : M → ℝ) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)) =
        (fun n => ENNReal.ofReal ‖u n - u_lim‖) := funext h_eLpNorm_eq
    rw [h_funeq]
    have h_comp := (ENNReal.continuous_ofReal.tendsto 0).comp h_norm_tendsto
    simp only [Function.comp_def, ENNReal.ofReal_zero] at h_comp
    exact h_comp
  -- Coercion: u n.coeFn → u_lim.coeFn in eLpNorm sense.
  have h_aeEq : ∀ n, (((u n - u_lim) : Lp ℝ 2 _) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x => ((u n : Lp ℝ 2 _) : M → ℝ) x -
        ((u_lim : Lp ℝ 2 _) : M → ℝ) x) := by
    intro n
    have := MeasureTheory.Lp.coeFn_sub (u n) u_lim
    -- (a - b).coeFn =ᵐ a.coeFn - b.coeFn (pointwise sub).
    filter_upwards [this] with x hx
    exact hx
  have h_diff_tendsto :
      Tendsto (fun n => eLpNorm
        (fun x => ((u n : Lp ℝ 2 _) : M → ℝ) x - ((u_lim : Lp ℝ 2 _) : M → ℝ) x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
    have h_funeq : (fun n => eLpNorm
        (fun x => ((u n : Lp ℝ 2 _) : M → ℝ) x - ((u_lim : Lp ℝ 2 _) : M → ℝ) x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) =
      (fun n => eLpNorm (((u n - u_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) := by
      funext n
      exact MeasureTheory.eLpNorm_congr_ae (h_aeEq n).symm
    rw [h_funeq]
    exact h_eLpNorm_tendsto
  -- Apply chartPushed_tendsto_chartPulledWeightedMeasure.
  have hu_meas : ∀ n, Measurable ((u n : Lp ℝ 2 _) : M → ℝ) := fun n =>
    (Lp.stronglyMeasurable (u n)).measurable
  have hu_lim_meas : Measurable ((u_lim : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable u_lim).measurable
  have h_chartPushed_eLp_tendsto :=
    chartPushed_tendsto_chartPulledWeightedMeasure (I := I) (M := M) g α
      hu_meas hu_lim_meas h_diff_tendsto
  -- Now convert eLpNorm-tendsto-zero of chart-pushed diffs to Lp-tendsto.
  rw [tendsto_iff_dist_tendsto_zero]
  have h_dist_eq : ∀ n,
      dist (chartPushedLpFromLp (I := I) (M := M) g α (u n))
          (chartPushedLpFromLp (I := I) (M := M) g α u_lim) =
        ENNReal.toReal (eLpNorm (fun y =>
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α ((u n : Lp ℝ 2 _) : M → ℝ) y -
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α ((u_lim : Lp ℝ 2 _) : M → ℝ) y) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) := by
    intro n
    rw [dist_eq_norm, Lp.norm_def]
    have h_sub_aeEq := MeasureTheory.Lp.coeFn_sub
      (chartPushedLpFromLp (I := I) (M := M) g α (u n))
      (chartPushedLpFromLp (I := I) (M := M) g α u_lim)
    have h_coe_n := chartPushedLpFromLp_coeFn (I := I) (M := M) g α (u n)
    have h_coe_lim := chartPushedLpFromLp_coeFn (I := I) (M := M) g α u_lim
    have h_diff_ae : (((chartPushedLpFromLp (I := I) (M := M) g α (u n) -
            chartPushedLpFromLp (I := I) (M := M) g α u_lim) :
            Lp ℝ 2 _) : EuclN → ℝ) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        (fun y =>
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α ((u n : Lp ℝ 2 _) : M → ℝ) y -
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α ((u_lim : Lp ℝ 2 _) : M → ℝ) y) := by
      filter_upwards [h_sub_aeEq, h_coe_n, h_coe_lim] with y hy_sub hy_n hy_lim
      rw [hy_sub, Pi.sub_apply, hy_n, hy_lim]
    rw [MeasureTheory.eLpNorm_congr_ae h_diff_ae]
  rw [show (fun n =>
      dist (chartPushedLpFromLp (I := I) (M := M) g α (u n))
        (chartPushedLpFromLp (I := I) (M := M) g α u_lim)) =
    (fun n => ENNReal.toReal (eLpNorm (fun y =>
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α ((u n : Lp ℝ 2 _) : M → ℝ) y -
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α ((u_lim : Lp ℝ 2 _) : M → ℝ) y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))) from funext h_dist_eq]
  have h_toReal_tendsto :
      Tendsto (fun n => ENNReal.toReal (eLpNorm (fun y =>
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α ((u n : Lp ℝ 2 _) : M → ℝ) y -
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α ((u_lim : Lp ℝ 2 _) : M → ℝ) y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))) atTop (𝓝 0) := by
    have h_comp := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp
      h_chartPushed_eLp_tendsto
    simpa using h_comp
  exact h_toReal_tendsto

/-! ## Smooth-case representation of LHS mass

The smooth-case LHS mass integrand `density · chartPushed POU α v.toFun · ψ`
equals `chartPushed POU α v.toFun · ψ` against the chart-pulled weighted
measure restricted to chartTarget. This is in turn an `Lp 2` inner product
between `massMultiplierLp ψ` and `chartPushedLpFromLp (smoothToLp v)`. -/

private lemma smooth_lhs_mass_integral_eq_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) (ψ : EuclN → ℝ) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α v.toFun y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y,
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α v.toFun y * ψ y
        ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  rw [show ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α v.toFun y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α v.toFun y * ψ y)
        ∂(volume : Measure EuclN) from by
      refine MeasureTheory.setIntegral_congr_fun h_meas_chartTarget (fun y _hy => ?_)
      ring]
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α
    (fun y =>
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α v.toFun y * ψ y)]

/-- For a smooth scalar `v`, the chart-pushed Lp class of `smoothToLp v`
agrees a.e. with `chartPushed POU α v.toFun`. -/
private lemma chartPushedLpFromLp_smoothToLp_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) :
    ((chartPushedLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g v) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α v.toFun := by
  classical
  have h_lp_coeFn := chartPushedLpFromLp_coeFn (I := I) (M := M) g α
    (smoothToLp (I := I) (M := M) g v)
  -- (smoothToLp g v).coeFn =ᵐ[μ_g] v.toFun.
  have h_smooth_coe : ((smoothToLp (I := I) (M := M) g v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  refine h_lp_coeFn.trans ?_
  -- Now need: chartPushed POU α (smoothToLp v).coeFn =ᵐ chartPushed POU α v.toFun
  -- on (chart-pulled-weighted).restrict chartTarget.
  -- The chart-push is linear in the function argument; for a.e.-equal `u₁ =ᵐ[μ_g] u₂`,
  -- the chart-pushed difference has eLpNorm 0 on the chart-pulled-weighted restrict.
  -- We package this via the existing `eLpNorm_chartPushed_chartPulledWeightedMeasure_restrict_le`.
  have h_meas_lp_coe : Measurable
      ((smoothToLp (I := I) (M := M) g v : Lp ℝ 2 _) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_meas_v : Measurable v.toFun := v.smooth.continuous.measurable
  -- eLpNorm of the diff on μ_g is 0.
  have h_zero_μg : eLpNorm
        (fun x : M => ((smoothToLp (I := I) (M := M) g v :
              Lp ℝ 2 _) : M → ℝ) x - v.toFun x) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    refine (MeasureTheory.eLpNorm_eq_zero_iff
      (h_meas_lp_coe.sub h_meas_v).aestronglyMeasurable
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mpr ?_
    filter_upwards [h_smooth_coe] with x hx
    change ((smoothToLp (I := I) (M := M) g v : Lp ℝ 2 _) : M → ℝ) x - v.toFun x = 0
    rw [hx, sub_self]
  -- eLpNorm bound: eLpNorm (chartPushed_diff) ≤ C · eLpNorm (diff).
  obtain ⟨C, _hC_pos, hC_bnd⟩ :=
    eLpNorm_chartPushed_chartPulledWeightedMeasure_restrict_le (I := I) (M := M) g α
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have h_sub_meas : Measurable
      (fun x : M => ((smoothToLp (I := I) (M := M) g v :
            Lp ℝ 2 _) : M → ℝ) x - v.toFun x) :=
    h_meas_lp_coe.sub h_meas_v
  have h_diff_bound := hC_bnd h_sub_meas
  -- Rewrite the chart-pushed of (u - v.toFun) as chart-pushed(u) - chart-pushed(v).
  have h_chart_diff :
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          (fun x : M => ((smoothToLp (I := I) (M := M) g v :
                Lp ℝ 2 _) : M → ℝ) x - v.toFun x) =
        (fun y =>
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α (((smoothToLp (I := I) (M := M) g v :
                Lp ℝ 2 _) : M → ℝ)) y -
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α v.toFun y) := by
    funext y
    unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
    ring
  rw [h_chart_diff] at h_diff_bound
  rw [h_zero_μg, mul_zero] at h_diff_bound
  -- h_diff_bound: eLpNorm (chart-pushed diff) ≤ 0, so = 0.
  have h_chart_eLpNorm_zero : eLpNorm
      (fun y =>
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α (((smoothToLp (I := I) (M := M) g v :
              Lp ℝ 2 _) : M → ℝ)) y -
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α v.toFun y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) = 0 :=
    le_antisymm h_diff_bound (zero_le _)
  -- From eLpNorm = 0, get a.e. zero.
  have h_aestrong : AEStronglyMeasurable (fun y =>
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α (((smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 _) : M → ℝ)) y -
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α v.toFun y)
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    refine AEStronglyMeasurable.sub ?_ ?_
    · exact (chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
        (I := I) (M := M) g α h_meas_lp_coe (Lp.memLp _)).1
    · exact (chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
        (I := I) (M := M) g α h_meas_v v.memLp_two).1
  have h_aeEq_zero := (MeasureTheory.eLpNorm_eq_zero_iff h_aestrong
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp h_chart_eLpNorm_zero
  filter_upwards [h_aeEq_zero] with y hy
  have hy' : DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α (((smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 _) : M → ℝ)) y -
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α v.toFun y = 0 := hy
  linarith

/-- The per-smooth-case LHS-mass integral equals the `Lp 2` inner product
`⟨massMultiplierLp ψ, chartPushedLpFromLp (smoothToLp v)⟩`. -/
private lemma smooth_lhs_mass_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (v : SmoothScalar g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α v.toFun y * ψ y
        ∂(volume : Measure EuclN) =
      ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp,
        chartPushedLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g v)⟫_ℝ := by
  classical
  rw [smooth_lhs_mass_integral_eq_weighted (I := I) (M := M) g α v ψ]
  rw [L2.inner_def (𝕜 := ℝ)]
  refine MeasureTheory.integral_congr_ae ?_
  have h_ψ := massMultiplierLp_coeFn (I := I) (M := M) g α hψ hψ_cs hψ_supp
  have h_C := chartPushedLpFromLp_smoothToLp_aeEq (I := I) (M := M) g α v
  filter_upwards [h_ψ, h_C] with y h_ψy h_Cy
  -- Real inner product: ⟨x, y⟩ = y * x.
  rw [show @inner ℝ _ _
      (((massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y)
      (((chartPushedLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g v) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) =
      (((chartPushedLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g v) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) *
      (((massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) from rfl]
  rw [h_ψy, h_Cy]

/-! ## Limit-passage of the LHS principal and LHS mass integrals -/

/-- For a smooth approximating sequence `v_n → u_h` in `H1Compl g`, the
per-`i` smooth-case LHS principal integrals converge to the corresponding
form-B inner product with `chartPushedWeakPartialLp u_h`. -/
private lemma smooth_lhs_principal_per_i_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g}
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) atTop
      (𝓝 ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h⟫_ℝ) := by
  classical
  -- Rewrite each smooth-case integral as an inner product.
  have h_per_n : ∀ n,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) =
        ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
          chartPushedPartialLp (I := I) (M := M) g α i (v n)
            (chartPushedPartial_memLp (I := I) (M := M) g α i (v n))⟫_ℝ := fun n =>
    smooth_lhs_principal_per_i_eq_inner (I := I) (M := M) g α i hψ hψ_cs hψ_supp (v n)
  -- The inner product is continuous in the second argument; chartPushedWeakPartialLp
  -- is continuous in u_h; for smooth v_n, chartPushedWeakPartialLp (smoothToH1Compl v_n)
  -- = chartPushedPartialLp v_n.
  -- So the inner products of LHS converge to the target.
  have h_smooth_case_eq : ∀ n,
      chartPushedPartialLp (I := I) (M := M) g α i (v n)
          (chartPushedPartial_memLp (I := I) (M := M) g α i (v n)) =
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i)
          (smoothToH1Compl (I := I) (M := M) g (v n)) :=
    fun n => (chartPushedWeakPartialLp_smoothToH1Compl
      (I := I) (M := M) g α i
      (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) (v n)).symm
  have h_cwpL_tendsto : Tendsto (fun n => chartPushedWeakPartialLp
        (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i)
        (smoothToH1Compl (I := I) (M := M) g (v n))) atTop
      (𝓝 (chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h)) :=
    ((chartPushedWeakPartialLp_continuous
      (I := I) (M := M) g α i _).tendsto _).comp h_tendsto
  have h_inner_tendsto : Tendsto (fun n =>
        ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
          chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i)
            (smoothToH1Compl (I := I) (M := M) g (v n))⟫_ℝ) atTop
      (𝓝 ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h⟫_ℝ) :=
    Filter.Tendsto.inner tendsto_const_nhds h_cwpL_tendsto
  -- Rewrite the sequence to match.
  rw [show (fun n =>
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) =
    (fun n =>
      ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i)
          (smoothToH1Compl (I := I) (M := M) g (v n))⟫_ℝ) from by
    funext n
    rw [h_per_n n, h_smooth_case_eq n]]
  exact h_inner_tendsto

/-- For a smooth approximating sequence `v_n → u_h` in `H1Compl g`, the
smooth-case LHS mass integrals converge to the form-B mass inner product. -/
private lemma smooth_lhs_mass_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g}
    {v : ℕ → SmoothScalar g}
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
              (chartAtlasPOU I M) α (v n).toFun y * ψ y
          ∂(volume : Measure EuclN)) atTop
      (𝓝 ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp,
        chartPushedLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h)⟫_ℝ) := by
  classical
  -- Rewrite each smooth-case integral as an inner product.
  have h_per_n : ∀ n,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
              (chartAtlasPOU I M) α (v n).toFun y * ψ y
          ∂(volume : Measure EuclN) =
        ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp,
          chartPushedLpFromLp (I := I) (M := M) g α
            (smoothToLp (I := I) (M := M) g (v n))⟫_ℝ := fun n =>
    smooth_lhs_mass_eq_inner (I := I) (M := M) g α hψ hψ_cs hψ_supp (v n)
  -- smoothToLp v_n → H1ComplToLp u_h in Lp ℝ 2 μ_g.
  have h_lp_tendsto : Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n))
      atTop (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) :=
    smoothToLp_tendsto_H1ComplToLp_of_h1_tendsto (I := I) (M := M) g h_tendsto
  -- chartPushedLpFromLp ∘ smoothToLp v_n → chartPushedLpFromLp ∘ H1ComplToLp u_h
  -- by the Lp continuity of chartPushedLpFromLp.
  have h_cPL_tendsto :
      Tendsto (fun n => chartPushedLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g (v n))) atTop
        (𝓝 (chartPushedLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h))) :=
    chartPushedLpFromLp_tendsto (I := I) (M := M) g α h_lp_tendsto
  have h_inner_tendsto : Tendsto (fun n =>
        ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp,
          chartPushedLpFromLp (I := I) (M := M) g α
            (smoothToLp (I := I) (M := M) g (v n))⟫_ℝ) atTop
      (𝓝 ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp,
        chartPushedLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h)⟫_ℝ) :=
    Filter.Tendsto.inner tendsto_const_nhds h_cPL_tendsto
  rw [show (fun n =>
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
              (chartAtlasPOU I M) α (v n).toFun y * ψ y
          ∂(volume : Measure EuclN)) =
    (fun n =>
      ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp,
        chartPushedLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g (v n))⟫_ℝ) from
    funext h_per_n]
  exact h_inner_tendsto

/-- The general-case LHS principal per-i integral equals the corresponding
`Lp 2` inner product on the chart-pulled weighted measure restricted to
`chartTargetEuclid α`. -/
private lemma general_lhs_principal_per_i_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (u_h : H1Compl g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            ((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) =
      ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h⟫_ℝ := by
  classical
  have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  -- Pointwise rewrite of the integrand on chartTarget.
  have h_pointwise : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      (∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            ((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =
        densityOnEuclid (I := I) g α y *
          (principalMultiplier (I := I) (M := M) g α i ψ y *
            ((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
    intro y _hy
    unfold principalMultiplier
    have h_each : ∀ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
            ((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1) =
          densityOnEuclid (I := I) g α y *
            (invGramOnEuclid (I := I) g α i j y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) *
            ((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y := by
      intro j
      have h_w : weightedInvGramOnEuclid (I := I) g α i j y =
          densityOnEuclid (I := I) g α y * invGramOnEuclid (I := I) g α i j y := rfl
      rw [h_w]
      ring
    rw [Finset.sum_congr rfl (fun j _ => h_each j)]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [MeasureTheory.setIntegral_congr_fun h_meas_chartTarget h_pointwise]
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α
    (fun y => principalMultiplier (I := I) (M := M) g α i ψ y *
      ((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y)]
  rw [L2.inner_def (𝕜 := ℝ)]
  refine MeasureTheory.integral_congr_ae ?_
  have h_P := principalMultiplierLp_coeFn (I := I) (M := M) g α i hψ hψ_cs hψ_supp
  filter_upwards [h_P] with y h_Py
  rw [show @inner ℝ _ _
      (((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y)
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) =
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) *
      (((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) from rfl]
  rw [h_Py]
  ring

/-- The general-case LHS mass integral equals the corresponding `Lp 2` inner
product on the chart-pulled weighted measure restricted to `chartTargetEuclid α`. -/
private lemma general_lhs_mass_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (u_h : H1Compl g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            (((H1ComplToLp (I := I) (M := M) g u_h) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y * ψ y
        ∂(volume : Measure EuclN) =
      ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp,
        chartPushedLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h)⟫_ℝ := by
  classical
  have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  -- Convert: ∫ density · X · ψ ∂vol = ∫ X · ψ ∂(weighted, restrict).
  rw [show ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            (((H1ComplToLp (I := I) (M := M) g u_h) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            (((H1ComplToLp (I := I) (M := M) g u_h) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y * ψ y)
        ∂(volume : Measure EuclN) from by
      refine MeasureTheory.setIntegral_congr_fun h_meas_chartTarget (fun y _hy => ?_)
      ring]
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α
    (fun y =>
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        (((H1ComplToLp (I := I) (M := M) g u_h) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y * ψ y)]
  rw [L2.inner_def (𝕜 := ℝ)]
  refine MeasureTheory.integral_congr_ae ?_
  have h_ψ := massMultiplierLp_coeFn (I := I) (M := M) g α hψ hψ_cs hψ_supp
  have h_C := chartPushedLpFromLp_coeFn (I := I) (M := M) g α
    (H1ComplToLp (I := I) (M := M) g u_h)
  filter_upwards [h_ψ, h_C] with y h_ψy h_Cy
  rw [show @inner ℝ _ _
      (((massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y)
      (((chartPushedLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) =
      (((chartPushedLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) *
      (((massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) from rfl]
  rw [h_ψy, h_Cy]

/-- Helper: the per-`i` integrand in the general-case form-B integral, after
the change-of-measure pointwise rewriting, is `density · P_i ψ · (weak partial)`. -/
private lemma general_lhs_principal_full_integrand_pointwise
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (u_h : H1Compl g)
    {y : EuclN} (_hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
          ((chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =
      densityOnEuclid (I := I) g α y *
        (∑ i : Fin (Module.finrank ℝ E),
          principalMultiplier (I := I) (M := M) g α i ψ y *
            ((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold principalMultiplier
  have h_each : ∀ j : Fin (Module.finrank ℝ E),
      weightedInvGramOnEuclid (I := I) g α i j y *
        ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
        (fderiv ℝ ψ y) (EuclideanSpace.single j 1) =
      densityOnEuclid (I := I) g α y *
        (invGramOnEuclid (I := I) g α i j y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) *
        ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y := by
    intro j
    have h_w : weightedInvGramOnEuclid (I := I) g α i j y =
        densityOnEuclid (I := I) g α y * invGramOnEuclid (I := I) g α i j y := rfl
    rw [h_w]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h_each j)]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The general-case LHS principal full integral equals the sum of
per-i `Lp 2` inner products. -/
private lemma general_lhs_principal_eq_sum_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    (u_h : H1Compl g) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            ((chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN) =
      ∑ i : Fin (Module.finrank ℝ E),
        ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
          chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h⟫_ℝ := by
  classical
  set μ := (chartPulledWeightedMeasure (I := I) g α).restrict
    (chartTargetEuclid (I := I) (M := M) α)
  have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  -- Step a: pointwise rewrite of the integrand.
  rw [MeasureTheory.setIntegral_congr_fun h_meas_chartTarget
    (fun y hy => general_lhs_principal_full_integrand_pointwise (I := I) (M := M) g α u_h hy)]
  -- Step b: change of measure ∫ density · _ ∂vol = ∫ _ ∂(weighted, restrict).
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α
    (fun y => ∑ i : Fin (Module.finrank ℝ E),
      principalMultiplier (I := I) (M := M) g α i ψ y *
        ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 _) : EuclN → ℝ) y)]
  -- Step c: integrability of each summand.
  have h_per_i_integrable : ∀ i : Fin (Module.finrank ℝ E),
      Integrable (fun y =>
        principalMultiplier (I := I) (M := M) g α i ψ y *
          ((chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) μ := by
    intro i
    have h_P : MemLp (principalMultiplier (I := I) (M := M) g α i ψ) 2 μ :=
      continuous_compactSupport_memLp_chartPulledWeighted_restrict
        (I := I) (M := M) g α
        (principalMultiplier_continuous (I := I) (M := M) g α i hψ hψ_supp)
        (principalMultiplier_hasCompactSupport (I := I) (M := M) g α i hψ_cs)
        (principalMultiplier_tsupport_subset (I := I) (M := M) g α i hψ_supp)
    have h_C : MemLp (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ)) 2 μ :=
      Lp.memLp _
    exact MemLp.integrable_mul h_P h_C
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => h_per_i_integrable i)]
  -- Step d: identify each per-i integral with the inner product.
  refine Finset.sum_congr rfl fun i _ => ?_
  -- ∫ P_i · partial ∂μ = ⟨P_i_lp, chartPushedWeakPartialLp_i u_h⟩.
  -- Use L2.inner_def and the a.e. coercion.
  rw [L2.inner_def (𝕜 := ℝ)]
  refine MeasureTheory.integral_congr_ae ?_
  have h_P := principalMultiplierLp_coeFn (I := I) (M := M) g α i hψ hψ_cs hψ_supp
  filter_upwards [h_P] with y h_Py
  rw [show @inner ℝ _ _
      (((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y)
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) =
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) *
      (((principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y) from rfl]
  rw [h_Py]
  ring

/-! ## RHS limit-passage: smooth case → general case via the bilinear bypass

The RHS smooth-case integral
`∫_chartTarget density · (pouScalar α v_n).oneSubLap.toFun(symm y) · ψ dy`
equals `chartPulledIntegralCLM g α (density · ψ) (fHLeibniz (smoothToH1Compl v_n) _)`
via `smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz` and
`chartPulledIntegralCLM_smoothToLp`. The general-case limit follows by
combining the three bilinear-bypass tendsto lemmas. -/

private lemma rhs_smooth_tendsto_chartPulledIntegralCLM_fHLeibniz_general
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {v : ℕ → SmoothScalar g}
    (h_v_tendsto :
      Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
        atTop (𝓝 u_h)) :
    Tendsto (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ψ y ∂(volume : Measure EuclN))
      atTop (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (fHLeibniz (I := I) (M := M) g α u_h hu_h))) := by
  classical
  -- Step 1: rewrite the smooth-case integral as
  --   chartPulledIntegralCLM g α (density · ψ) (smoothToLp (pouScalar α v_n).oneSubLap).
  have h_eq_smooth : ∀ n,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ψ y ∂(volume : Measure EuclN) =
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (smoothToLp (I := I) (M := M) g
            (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical) := by
    intro n
    rw [chartPulledIntegralCLM_smoothToLp (I := I) (M := M) g α _ _ _
      (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical]
    refine MeasureTheory.setIntegral_congr_fun
      (Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α).measurableSet (fun y _ => ?_)
    ring
  -- Step 2: by smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz, the smoothToLp class
  -- equals fHLeibniz (smoothToH1Compl v_n) _.
  have h_eq_fHLeibniz_smooth : ∀ n,
      smoothToLp (I := I) (M := M) g
          (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical =
        fHLeibniz (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g (v n))
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) (v n)) :=
    fun n => smoothToLp_pouScalar_oneSubLap_eq_fHLeibniz (I := I) (M := M) g α (v n)
  -- Step 3: chartPulledIntegralCLM applied to fHLeibniz (smoothToH1Compl v_n) _ is linear in
  -- the fHLeibniz argument; expanding using fHLeibniz_smoothToH1Compl gives a sum of three
  -- chartPulledIntegralCLM applications, each of which tendsto its general-case counterpart.
  have h_fHLeibniz_eq : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (smoothToLp (I := I) (M := M) g
            (pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical) =
        chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
              (gradInnerSmooth (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (smoothToLp (I := I) (M := M) g (v n))) := by
    intro n
    rw [h_eq_fHLeibniz_smooth n, fHLeibniz_smoothToH1Compl]
    simp only [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_smul,
      smul_eq_mul]
  -- Step 4: the three bilinear-bypass limits.
  have h_lim_1 := chartPulledIntegralCLM_smoothMulLp_oneSubLap_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_supp hu_h h_v_tendsto
  have h_lim_2 := chartPulledIntegralCLM_gradInnerSmooth_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_supp h_v_tendsto
  have h_lim_3 := chartPulledIntegralCLM_smoothMulLp_tendsto
    (I := I) (M := M) g α hψ hψ_cs hψ_supp h_v_tendsto
  have h_sum_lim : Tendsto (fun n =>
        chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
              (gradInnerSmooth (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (smoothToLp (I := I) (M := M) g (v n)))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (H1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
              (gradInnerCLM (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (H1ComplToLp (I := I) (M := M) g u_h)))) := by
    refine (h_lim_1.sub ?_).sub h_lim_3
    exact (tendsto_const_nhds.mul h_lim_2 : Tendsto _ _ _)
  -- Step 5: the limit matches the chart-pulled-integral CLM applied to fHLeibniz u_h hu_h
  -- via the linearity-only `laplacianDomain_variational_identity_clm_form` theorem.
  have h_target_eq :
      chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (H1ComplToLp (I := I) (M := M) g u_h -
                laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
              (gradInnerCLM (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (H1ComplToLp (I := I) (M := M) g u_h)) =
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (fHLeibniz (I := I) (M := M) g α u_h hu_h) :=
    laplacianDomain_variational_identity_clm_form
      (I := I) (M := M) g α hu_h hψ hψ_cs hψ_supp
  -- Step 6: combine.
  rw [show (fun n =>
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y ∂(volume : Measure EuclN)) =
    (fun n =>
      chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
              (smoothToLp (I := I) (M := M) g (v n).oneSubLapClassical)) -
          (2 : ℝ) *
            chartPulledIntegralCLM (I := I) (M := M) g α
              (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
              (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
              (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
              (gradInnerSmooth (I := I) (M := M) g
                (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) (v n)) -
          chartPulledIntegralCLM (I := I) (M := M) g α
            (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
            (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
            (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
            (smoothMulLp (I := I) (M := M) g
              (laplacianOfChartPOU (I := I) (M := M) g α)
              (smoothToLp (I := I) (M := M) g (v n)))) from by
    funext n; rw [h_eq_smooth n, h_fHLeibniz_eq n]]
  rw [← h_target_eq]
  exact h_sum_lim

/-! ## Public form-B headline -/

/-- **The substantive form-B chart-pulled variational identity.**

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and an
element `u_h : H1Compl g` lying in `laplacianDomain g`, the chart-pulled
variational identity matching the smooth-case shape
`laplacianDomain_variational_identity_smooth_case` holds against any smooth
test function `ψ : EuclN → ℝ` with `tsupport ψ ⊆ chartTargetEuclid α`:

```
(∫_{chartTarget α} ∑_{i, j} √det g · g^{ij} · (chart-pushed weak ∂_i u_h)(y) · ∂_j ψ(y) dy) +
  (∫_{chartTarget α} √det g · (chart-pushed POU · u_h)(y) · ψ(y) dy) =
  chartPulledIntegralCLM g α (√det g · ψ) (fHLeibniz g α u_h hu_h)
```

This is the substantive general-case form of the smooth-case identity
`laplacianDomain_variational_identity_smooth_case`: the LHS contains the
chart-pushed weak partials of `u_h` (constructed via the H¹-Lipschitz
extension) and the chart-pushed Lp class of `H1ComplToLp u_h`; the RHS is
the chart-pulled integral of the Leibniz-compensated `L²` class
`fHLeibniz g α u_h hu_h`. -/
theorem laplacianDomain_variational_identity_general
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramOnEuclid (I := I) g α i j y *
          ((chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y *
          (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
      ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          (((H1ComplToLp (I := I) (M := M) g u_h) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) y * ψ y
      ∂(volume : Measure EuclN)) =
    chartPulledIntegralCLM (I := I) (M := M) g α
      (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
      (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
      (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
      (fHLeibniz (I := I) (M := M) g α u_h hu_h) := by
  classical
  -- Step 1: pick a smooth approximating sequence v_n → u_h.
  obtain ⟨v, h_v_tendsto⟩ :=
    exists_smooth_approx_seq (I := I) (M := M) g u_h
  -- Step 2: smooth-case identity for each v_n.
  have h_smooth_case : ∀ n,
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i (v n) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α (v n).toFun y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y ∂(volume : Measure EuclN) := fun n =>
    laplacianDomain_variational_identity_smooth_case (I := I) (M := M) g α (v n)
      hψ hψ_cs hψ_supp
  -- Step 3: LHS principal converges via sum of per-i convergences.
  have h_per_i_tendsto : ∀ i : Fin (Module.finrank ℝ E),
      Tendsto (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) atTop
      (𝓝 ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h⟫_ℝ) :=
    fun i => smooth_lhs_principal_per_i_tendsto (I := I) (M := M) g α i hψ hψ_cs hψ_supp h_v_tendsto
  -- The full LHS principal integral converges via sum of per-i convergences plus a
  -- single sum-integral swap on the smooth side.
  have h_swap_n : ∀ n,
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chartPushedPartial (I := I) (M := M) g α i (v n) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN) := by
    intro n
    -- Apply integral_finset_sum to swap ∫ and ∑_i. Need integrability per-i.
    -- The per-i integrand on chartTarget equals (via the change-of-measure) the L²
    -- inner product `⟨P_i ψ_lp, chartPushedPartialLp v_n⟩`, which IS an integral against
    -- the chart-pulled-weighted measure restricted to chartTarget. We use this to
    -- avoid proving integrability directly.
    -- Plan: rewrite each per-i integral via smooth_lhs_principal_per_i_integral_eq_weighted,
    -- to bring everything to ∂(weighted).restrict chartTarget; then linearity of integral
    -- on that measure (where each factor is MemLp 2) handles the swap.
    -- It's simpler to invoke the per-i integral identity for both sides and apply the
    -- swap on the chart-pulled-weighted-restricted measure where each `P_i · ∂_i v` is
    -- integrable (Hölder).
    set μ := (chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)
    -- Step a: per-i integral on the volume side = ∫ P_i ψ · ∂_i v_n ∂μ.
    have h_per_i_eq : ∀ i : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) =
          ∫ y, principalMultiplier (I := I) (M := M) g α i ψ y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y ∂μ := fun i =>
      smooth_lhs_principal_per_i_integral_eq_weighted (I := I) (M := M) g α i hψ (v n)
    -- Step b: also the full double-sum integral on the volume side equals the integral
    -- of `∑_i (P_i · ∂_i v_n)` on the μ side, via the same change-of-measure argument
    -- applied with the outer summation.
    have h_full_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
            (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chartPushedPartial (I := I) (M := M) g α i (v n) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
            ∂(volume : Measure EuclN) =
          ∫ y, ∑ i : Fin (Module.finrank ℝ E),
            principalMultiplier (I := I) (M := M) g α i ψ y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y ∂μ := by
      have h_meas_chartTarget : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
        (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      -- Pointwise: the double sum on chartTarget equals density · (∑_i P_i · ∂_i v_n).
      have h_pointwise : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) =
          densityOnEuclid (I := I) g α y *
            (∑ i : Fin (Module.finrank ℝ E),
              principalMultiplier (I := I) (M := M) g α i ψ y *
                chartPushedPartial (I := I) (M := M) g α i (v n) y) := by
        intro y _hy
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold principalMultiplier
        have h_each : ∀ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1) =
            densityOnEuclid (I := I) g α y *
              (invGramOnEuclid (I := I) g α i j y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1)) *
              chartPushedPartial (I := I) (M := M) g α i (v n) y := by
          intro j
          show weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1) = _
          rw [show weightedInvGramOnEuclid (I := I) g α i j y =
              densityOnEuclid (I := I) g α y * invGramOnEuclid (I := I) g α i j y from rfl]
          ring
        rw [Finset.sum_congr rfl (fun j _ => h_each j)]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      rw [MeasureTheory.setIntegral_congr_fun h_meas_chartTarget h_pointwise]
      change ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (∑ i : Fin (Module.finrank ℝ E),
              principalMultiplier (I := I) (M := M) g α i ψ y *
                chartPushedPartial (I := I) (M := M) g α i (v n) y)
          ∂(volume : Measure EuclN) = _
      rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
        (I := I) (M := M) g α
        (fun y => ∑ i : Fin (Module.finrank ℝ E),
          principalMultiplier (I := I) (M := M) g α i ψ y *
            chartPushedPartial (I := I) (M := M) g α i (v n) y)]
    -- Step c: on the μ side, swap ∫ and ∑_i.
    have h_per_i_memLp_P : ∀ i : Fin (Module.finrank ℝ E),
        MemLp (principalMultiplier (I := I) (M := M) g α i ψ) 2 μ :=
      fun i => continuous_compactSupport_memLp_chartPulledWeighted_restrict
        (I := I) (M := M) g α
        (principalMultiplier_continuous (I := I) (M := M) g α i hψ hψ_supp)
        (principalMultiplier_hasCompactSupport (I := I) (M := M) g α i hψ_cs)
        (principalMultiplier_tsupport_subset (I := I) (M := M) g α i hψ_supp)
    have h_per_i_memLp_C : ∀ i : Fin (Module.finrank ℝ E),
        MemLp (chartPushedPartial (I := I) (M := M) g α i (v n)) 2 μ :=
      fun i => chartPushedPartial_memLp (I := I) (M := M) g α i (v n)
    have h_per_i_integrable : ∀ i : Fin (Module.finrank ℝ E),
        Integrable (fun y =>
          principalMultiplier (I := I) (M := M) g α i ψ y *
            chartPushedPartial (I := I) (M := M) g α i (v n) y) μ := by
      intro i
      have h_P := h_per_i_memLp_P i
      have h_C := h_per_i_memLp_C i
      -- Cauchy-Schwarz: ‖P · C‖_{L¹} ≤ ‖P‖_{L²} · ‖C‖_{L²}, both finite ⇒ integrable.
      exact MemLp.integrable_mul h_P h_C
    rw [h_full_eq]
    rw [MeasureTheory.integral_finset_sum _ (fun i _ => h_per_i_integrable i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (h_per_i_eq i).symm
  -- The full LHS principal limit is the sum of per-i limits.
  have h_lhs_principal_tendsto : Tendsto (fun n =>
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i (v n) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) atTop
    (𝓝 (∑ i : Fin (Module.finrank ℝ E),
      ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
        chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h⟫_ℝ)) := by
    -- Combine h_swap_n with sum-of-per-i convergences.
    rw [show (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) =
      (fun n => ∑ i : Fin (Module.finrank ℝ E),
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) from funext h_swap_n]
    exact tendsto_finset_sum _ (fun i _ => h_per_i_tendsto i)
  -- LHS mass converges.
  have h_lhs_mass_tendsto :=
    smooth_lhs_mass_tendsto (I := I) (M := M) g α hψ hψ_cs hψ_supp h_v_tendsto
  -- RHS converges via the bilinear bypass.
  have h_rhs_tendsto := rhs_smooth_tendsto_chartPulledIntegralCLM_fHLeibniz_general
    (I := I) (M := M) g α hψ hψ_cs hψ_supp hu_h h_v_tendsto
  -- Sum of LHS-principal and LHS-mass converges to the sum of limits.
  have h_lhs_sum_tendsto := h_lhs_principal_tendsto.add h_lhs_mass_tendsto
  -- By the smooth-case identity, this matches the RHS convergence:
  -- per-n, LHS_n = RHS_n.
  have h_smooth_eq_fun : (fun n =>
      ((∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          weightedInvGramOnEuclid (I := I) g α i j y *
            chartPushedPartial (I := I) (M := M) g α i (v n) y *
            (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α (v n).toFun y * ψ y
        ∂(volume : Measure EuclN)))) =
    fun n =>
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          ψ y ∂(volume : Measure EuclN) := funext h_smooth_case
  -- LHS limit is the sum limit. We need LHS limit = RHS limit, i.e., the two
  -- limits coincide via the smooth-case equation per-n.
  -- LHS_n + Mass_n converges to (sum of principal + mass limits).
  -- RHS_n converges to chartPulledIntegralCLM (fHLeibniz u_h hu_h).
  -- By smooth-case equation, LHS_n + Mass_n = RHS_n. Take limits.
  have h_LHS_eq_RHS_lim : (∑ i : Fin (Module.finrank ℝ E),
        ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
          chartPushedWeakPartialLp (I := I) (M := M) g α i
            (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h⟫_ℝ) +
      ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp,
        chartPushedLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h)⟫_ℝ =
    chartPulledIntegralCLM (I := I) (M := M) g α
      (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
      (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
      (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
      (fHLeibniz (I := I) (M := M) g α u_h hu_h) := by
    -- By the smooth-case identity, the LHS sequence equals the RHS sequence;
    -- so they have the same limit. h_lhs_sum_tendsto and h_rhs_tendsto.
    have h_seq_eq : (fun n =>
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
              (chartAtlasPOU I M) α (v n).toFun y * ψ y
          ∂(volume : Measure EuclN))) =
      (fun n =>
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            ((pouScalar (I := I) (M := M) α (v n)).oneSubLapClassical.toFun)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
            ψ y ∂(volume : Measure EuclN)) := h_smooth_eq_fun
    have h_lhs_lim : Tendsto (fun n =>
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chartPushedPartial (I := I) (M := M) g α i (v n) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
              (chartAtlasPOU I M) α (v n).toFun y * ψ y
          ∂(volume : Measure EuclN))) atTop
      (𝓝 ((∑ i : Fin (Module.finrank ℝ E),
          ⟪principalMultiplierLp (I := I) (M := M) g α i hψ hψ_cs hψ_supp,
            chartPushedWeakPartialLp (I := I) (M := M) g α i
              (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h⟫_ℝ) +
        ⟪massMultiplierLp (I := I) (M := M) g α hψ hψ_cs hψ_supp,
          chartPushedLpFromLp (I := I) (M := M) g α
            (H1ComplToLp (I := I) (M := M) g u_h)⟫_ℝ)) := h_lhs_sum_tendsto
    rw [h_seq_eq] at h_lhs_lim
    exact tendsto_nhds_unique h_lhs_lim h_rhs_tendsto
  -- Now substitute the LHS_principal_general and LHS_mass_general representations.
  -- We need: form-B LHS = ∑_i ⟨P_i ψ_lp, chartPushedWeakPartialLp u_h⟩ + ⟨ψ_lp, chartPushedLpFromLp u_h⟩.
  rw [general_lhs_principal_eq_sum_inner (I := I) (M := M) g α hψ hψ_cs hψ_supp u_h,
    general_lhs_mass_eq_inner (I := I) (M := M) g α hψ hψ_cs hψ_supp u_h]
  exact h_LHS_eq_RHS_lim

end LaplacianDomainVariationalIdentityIntegralForm
end Laplacian
end Analysis
end DifferentialGeometry

end
