import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.H1Compl
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.H1ComplFromDom
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.Smooth
import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.WeakPartialOnVolume
import DifferentialGeometry.Analysis.Laplacian.Regularity.H1Compl.GradientH1LipschitzBound
import DifferentialGeometry.Analysis.Laplacian.Regularity.H1Compl.ToLpChartBridge
import DifferentialGeometry.Analysis.Laplacian.Regularity.H1Compl.WeakPartialLimit
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.VariationalIdentityIntegral
import DifferentialGeometry.Analysis.Laplacian.Operator.Operator
import DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich
import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Geometry.Laplacian
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Constructor for `ChartBilinearH1ComplData` from a `laplacianDomain g` element

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and any
`u_h : H1Compl g` with `hu_h : u_h ∈ laplacianDomain g`, this file
constructs a `ChartBilinearH1ComplData g α` instance.

The data fields are populated as follows:

* `u_chart` — the partition-of-unity-weighted chart-push of the Lp
  representative `H1ComplToLp u_h` on `chartTargetEuclid α`.
* `weak_partial i` — the chart-pushed weak `i`-partial coming from the
  H¹-Lipschitz extension `chartPushedWeakPartialLp` (against the canonical
  chart-pushed-partial Lipschitz witness).
* `f_chart` — the no-partition-of-unity chart-pullback (`chartPushedRaw`)
  of the Lp representative `fHLeibniz g α u_h hu_h`. This is the chart
  function `EuclN → ℝ` whose value at `y ∈ chartTargetEuclid α` is
  `(fHLeibniz : M → ℝ) ((extChartAt I α).symm ((toEuclidean).symm y))`,
  and zero outside `chartTargetEuclid α`.

The variational identity is then a direct consequence of the form-B
headline `laplacianDomain_variational_identity_general`, with the
RHS rewritten in setIntegral form via the `chartPulledIntegralCLM` ↔
setIntegral bridge developed below.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace LaplacianDomainChartData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearSmooth
open DifferentialGeometry.Analysis.Laplacian.ChartPulledIntegralContinuity
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentityFormB
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## File-local Borel-space instances -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-! ## Measurability of `chartPushedRaw` for measurable input -/

/-- A globally Borel-measurable extension of `(extChartAt I α).symm` taking a
fixed default value (here `α : M`) outside the chart target. -/
private noncomputable def extChartAtSymmGlobal (α : M) : E → M := by
  classical
  exact (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α)

omit [I.Boundaryless] [CompactSpace M] in
private lemma extChartAtSymmGlobal_eq_on_target (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    extChartAtSymmGlobal (I := I) (M := M) α y = (extChartAt I α).symm y := by
  classical
  change (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α) y = _
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

omit [I.Boundaryless] [CompactSpace M] in
private lemma extChartAtSymmGlobal_measurable (α : M) :
    Measurable (extChartAtSymmGlobal (I := I) (M := M) α) := by
  classical
  unfold extChartAtSymmGlobal
  exact ContinuousOn.measurable_piecewise
    (continuousOn_extChartAt_symm (I := I) α)
    continuousOn_const
    (DifferentialGeometry.Integral.Measure.measurableSet_extChartAt_target
      (I := I) (M := M) α)

omit [I.Boundaryless] [CompactSpace M] in
private lemma chartPushedRaw_measurable (α : M) {F : M → ℝ}
    (hF_meas : Measurable F) :
    Measurable (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F) := by
  classical
  have h_extSymm_meas : Measurable (extChartAtSymmGlobal (I := I) (M := M) α) :=
    extChartAtSymmGlobal_measurable (I := I) (M := M) α
  -- The function `F ∘ extSymm ∘ toE.symm` is measurable.
  have h_comp : Measurable
      (fun y : EuclN =>
        F (extChartAtSymmGlobal (I := I) (M := M) α
          ((toEuclidean (E := E)).symm y))) :=
    hF_meas.comp (h_extSymm_meas.comp
      (toEuclidean (E := E)).symm.continuous.measurable)
  -- chartPushedRaw α F = piecewise on chartTargetEuclid α.
  have hCT_meas : MeasurableSet
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_piecewise :
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F =
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α).piecewise
          (fun y : EuclN =>
            F (extChartAtSymmGlobal (I := I) (M := M) α
              ((toEuclidean (E := E)).symm y)))
          (fun _ : EuclN => (0 : ℝ)) := by
    funext y
    by_cases hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · rw [Set.piecewise_eq_of_mem _ _ _ hy]
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) α F hy]
      have h_toE_symm_in : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        rcases hy with ⟨w, hw_target, hwy⟩
        have h_eq : (toEuclidean (E := E)).symm y = w := by
          rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
        rw [h_eq]; exact hw_target
      rw [extChartAtSymmGlobal_eq_on_target (I := I) (M := M) α h_toE_symm_in]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
        (I := I) (M := M) α F hy]
  rw [h_piecewise]
  exact Measurable.piecewise hCT_meas h_comp measurable_const

/-! ## `chartLocalMeasure` versus `riemannianMeasure` on chart src

The chart-local measure `chartLocalMeasure g α` agrees with the Riemannian
measure `μ_g = riemannianMeasure g (chartAtlasPOU I M)` on `(chartAt H α).source`.
Since `chartLocalMeasure g α` vanishes outside `(chartAt H α).source`
(`chartLocalMeasure_apply_of_disjoint_source`), this yields a measure-level
bound `∫⁻ F d(chartLocalMeasure g α) ≤ ∫⁻ F dμ_g` for nonneg measurable F. -/

omit [I.Boundaryless] in
private lemma lintegral_chartLocalMeasure_le_lintegral_riemannianVolumeMeasure
    (g : SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g α) ≤
      ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Strategy: F restricted to chart src equals Ftilde, and Ftilde = 0 outside chart src.
  -- Apply `riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn` to Ftilde.
  set Ftilde : M → ℝ≥0∞ := (chartAt H α).source.indicator F with hFtilde_def
  have hFtilde_meas : Measurable Ftilde := hF.indicator (chartAt H α).open_source.measurableSet
  have hFtilde_zero_off : ∀ x, x ∉ (chartAt H α).source → Ftilde x = 0 := fun x hx =>
    Set.indicator_of_notMem hx _
  have h_chart_eq_μ :
      ∫⁻ x, Ftilde x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫⁻ x, Ftilde x ∂(chartLocalMeasure (I := I) g α) := by
    -- riemannianVolumeMeasure := riemannianMeasure g (chartAtlasPOU I M)
    change ∫⁻ x, Ftilde x ∂(riemannianMeasure (I := I) g (chartAtlasPOU I M)) =
      ∫⁻ x, Ftilde x ∂(chartLocalMeasure (I := I) g α)
    exact DifferentialGeometry.Analysis.Sobolev.Chart.riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hFtilde_meas hFtilde_zero_off
  -- ∫⁻ F d(chartLocalMeasure) = ∫⁻ Ftilde d(chartLocalMeasure)
  -- since chartLocalMeasure is supported in chart src.
  have h_off_zero :
      (chartLocalMeasure (I := I) g α) ((chartAt H α).source)ᶜ = 0 :=
    chartLocalMeasure_apply_of_disjoint_source (I := I) g α
      ((chartAt H α).open_source.measurableSet.compl)
      disjoint_compl_left
  have h_ae_F_eq_Ftilde : F =ᵐ[chartLocalMeasure (I := I) g α] Ftilde := by
    -- F = Ftilde on chart src; chart src complement is null.
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ h_off_zero
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    have hx' : x ∈ (chartAt H α).sourceᶜ ∨ x ∈ (chartAt H α).source := by
      by_cases h : x ∈ (chartAt H α).source
      · exact Or.inr h
      · exact Or.inl h
    rcases hx' with hxc | hxsrc
    · exact hxc
    · exfalso; apply hx; rw [hFtilde_def, Set.indicator_of_mem hxsrc]
  have h_chartLocal_F_eq_Ftilde :
      ∫⁻ x, F x ∂(chartLocalMeasure (I := I) g α) =
        ∫⁻ x, Ftilde x ∂(chartLocalMeasure (I := I) g α) :=
    MeasureTheory.lintegral_congr_ae h_ae_F_eq_Ftilde
  rw [h_chartLocal_F_eq_Ftilde, ← h_chart_eq_μ]
  -- ∫⁻ Ftilde ≤ ∫⁻ F, since Ftilde ≤ F.
  refine MeasureTheory.lintegral_mono fun x => ?_
  by_cases hx : x ∈ (chartAt H α).source
  · rw [hFtilde_def, Set.indicator_of_mem hx]
  · rw [hFtilde_def, Set.indicator_of_notMem hx]; exact zero_le _

/-! ## Lintegral bound for the chart-pulled-weighted integral of `chartPushedRaw F`

For any measurable `F : M → ℝ`, we have the lintegral bound

```
∫⁻ y in chartTarget α, density(y) · ‖chartPushedRaw F y‖² ∂vol
  ≤ (1/c_E) · ∫⁻ x, ‖F x‖² dμ_g
```

where `c_E > 0` is the Haar scaling factor. -/

private lemma lintegral_density_chartPushedRaw_pow_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ} (hF_meas : Measurable F) {p : ℝ} (_hp_pos : 0 < p) :
    (DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) *
      ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
          ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ p
        ∂(volume : Measure EuclN) ≤
      ∫⁻ x, ‖F x‖ₑ ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  -- Step 1: replace the chartPushedRaw value on chartTarget by F ∘ symm ∘ toE.symm.
  have h_target_meas :
      MeasurableSet (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_rewrite :
      ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ p
          ∂(volume : Measure EuclN) =
        ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ p
          ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setLIntegral_congr_fun h_target_meas (fun y hy => ?_)
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α F hy]
  rw [h_rewrite]
  -- Step 2: apply chartLocalMeasure_lintegral_via_chartTargetEuclid.
  have h_G_meas : Measurable (fun x : M => ‖F x‖ₑ ^ p) :=
    (hF_meas.enorm).pow_const p
  have h_bridge :
      ∫⁻ x, ‖F x‖ₑ ^ p ∂(chartLocalMeasure (I := I) g α) =
      (DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ p
          ∂(volume : Measure EuclN) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartLocalMeasure_lintegral_via_chartTargetEuclid
      (I := I) (M := M) g α h_G_meas
  have h_density_eq : ∀ y : EuclN,
      DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        densityOnEuclid (I := I) g α y := fun y => rfl
  have h_setLInt_eq :
      ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ p
          ∂(volume : Measure EuclN) =
        ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ p
          ∂(volume : Measure EuclN) := by
    refine MeasureTheory.setLIntegral_congr_fun h_target_meas (fun y _ => ?_)
    rw [h_density_eq y]
  rw [h_setLInt_eq] at h_bridge
  rw [← h_bridge]
  exact lintegral_chartLocalMeasure_le_lintegral_riemannianVolumeMeasure
    (I := I) (M := M) g α h_G_meas

/-! ## `MemLp 2` of `chartPushedRaw F` against the chart-pulled weighted measure -/

/-- For any measurable `F : M → ℝ` in `MemLp 2 μ_g`, the chart-pullback function
`chartPushedRaw I α F` is in `MemLp 2` of the chart-pulled weighted measure
restricted to `chartTargetEuclid α`. -/
private lemma chartPushedRaw_memLp_chartPulledWeighted
    (g : SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ} (hF_meas : Measurable F)
    (hF_memLp : MemLp F 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MemLp (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
  classical
  refine ⟨(chartPushedRaw_measurable (I := I) (M := M) α hF_meas).aestronglyMeasurable, ?_⟩
  -- eLpNorm < ⊤ via lintegral bound.
  -- eLpNorm² = ∫⁻ |chartPushedRaw F|² d(chartPulledWeighted.restrict chartTarget)
  --         = ∫⁻_chartTarget density · |chartPushedRaw F|² ∂vol
  -- ≤ (1/c_E) · ‖F‖_Lp².
  set μ_w : Measure EuclN :=
    (chartPulledWeightedMeasure (I := I) g α).restrict
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
  have hCT_meas :
      MeasurableSet (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h_two_ne_zero h_two_ne_top]
  rw [h_two_toReal]
  -- We need to show (∫⁻ ‖chartPushedRaw F‖² ∂μ_w)^{1/2} < ⊤.
  -- This follows from ENNReal.rpow_lt_top_of_nonneg applied with the ≠ ⊤ statement.
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  -- Goal: ∫⁻ ‖chartPushedRaw F‖² ∂μ_w ≠ ⊤
  show ∫⁻ y, ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ) ∂μ_w ≠ ⊤
  -- Compute the lintegral against μ_w = (chartPulledWeighted).restrict chartTarget
  have h_lint_eq :
      ∫⁻ y, ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ) ∂μ_w =
        ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure EuclN) := by
    change ∫⁻ y, ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
        ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) = _
    unfold chartPulledWeightedMeasure
    rw [show
        ((volume : Measure EuclN).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) =
          ((volume : Measure EuclN).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y)) from
        MeasureTheory.restrict_withDensity hCT_meas _]
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀
        ((volume : Measure EuclN).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        (f := fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        ?_ ?_]
    · -- Show: ∫⁻ y, density * ‖chartPushedRaw‖² = ∫⁻ y in chartTarget, density * ...
      -- We need to factor mul into the pointwise function.
      simp only [Pi.mul_apply]
    · refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      exact (densityOnEuclid_continuousOn (I := I) g α).aemeasurable
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
          (I := I) (M := M) α).measurableSet
    · refine Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [h_lint_eq]
  -- Use the c_E-scaled bound.
  have h_c_E_pos : (0 : ℝ≥0∞) <
      (DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) := by
    exact_mod_cast DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor_pos
  have h_c_E_ne_zero : (DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) ≠ 0 :=
    ne_of_gt h_c_E_pos
  have h_c_E_ne_top : (DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) ≠ ⊤ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor_ennreal_ne_top
  have h_bound :=
    lintegral_density_chartPushedRaw_pow_le (I := I) (M := M) g α (p := 2) hF_meas
      (by norm_num : (0 : ℝ) < 2)
  have h_RHS_lt_top : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) < ⊤ := by
    have h_eLp_lt_top := hF_memLp.2
    have h_eLp_eq : eLpNorm F 2 (riemannianVolumeMeasure (I := I) (M := M) g) ^ (2 : ℝ) =
        ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h_two_ne_zero h_two_ne_top]
      rw [h_two_toReal]
      have h2_eq : ((∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) =
          (∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ (((1 : ℝ) / 2) * 2) := by
        rw [← ENNReal.rpow_mul]
      rw [h2_eq]
      norm_num
    rw [← h_eLp_eq]
    refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
    exact h_eLp_lt_top.ne
  intro h_contra
  rw [h_contra, ENNReal.mul_top h_c_E_ne_zero] at h_bound
  exact absurd h_bound (not_le.mpr h_RHS_lt_top)

/-! ## eLpNorm bound for `chartPushedRaw` -/

/-- For any measurable `F : M → ℝ` (in particular Lp.coeFn), the eLpNorm of
`chartPushedRaw I α F` against the chart-pulled weighted measure restricted to
`chartTargetEuclid α` is bounded by `(1/√c_E) · eLpNorm F μ_g`. -/
private lemma eLpNorm_chartPushedRaw_le
    (g : SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ} (hF_meas : Measurable F) :
    eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) ≤
      ((DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞))⁻¹ ^ ((1 : ℝ)/2) *
        eLpNorm F 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set c_E := DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E
  have h_c_E_pos : (0 : ℝ≥0∞) < (c_E : ℝ≥0∞) := by
    exact_mod_cast DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor_pos
  have h_c_E_ne_zero : (c_E : ℝ≥0∞) ≠ 0 := ne_of_gt h_c_E_pos
  have h_c_E_ne_top : (c_E : ℝ≥0∞) ≠ ⊤ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor_ennreal_ne_top
  have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hCT_meas :
      MeasurableSet (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  -- Compute the LHS in lintegral form.
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h_two_ne_zero h_two_ne_top]
  rw [h_two_toReal]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h_two_ne_zero h_two_ne_top]
  rw [h_two_toReal]
  -- LHS: (∫⁻ ‖chartPushedRaw F‖² d(chartPulledWeighted.restrict chartTarget))^{1/2}
  -- RHS: (1/c_E)^{1/2} · (∫⁻ ‖F‖² dμ_g)^{1/2}
  have h_lint_eq :
      ∫⁻ y, ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
        ∂((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)) =
        ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure EuclN) := by
    unfold chartPulledWeightedMeasure
    rw [show
        ((volume : Measure EuclN).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) =
          ((volume : Measure EuclN).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y)) from
        MeasureTheory.restrict_withDensity hCT_meas _]
    rw [MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable₀
        ((volume : Measure EuclN).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        (f := fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        ?_ ?_]
    · simp only [Pi.mul_apply]
    · refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
      exact (densityOnEuclid_continuousOn (I := I) g α).aemeasurable
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
          (I := I) (M := M) α).measurableSet
    · refine Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [h_lint_eq]
  have h_bound :=
    lintegral_density_chartPushedRaw_pow_le (I := I) (M := M) g α (p := 2) hF_meas
      (by norm_num : (0 : ℝ) < 2)
  -- c_E · LHS_lint ≤ RHS_lint. Take both to ^{1/2}.
  -- Hence LHS_lint^{1/2} ≤ (c_E^{-1})^{1/2} · RHS_lint^{1/2}.
  have h_div : ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
          ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
        ∂(volume : Measure EuclN) ≤
      (c_E : ℝ≥0∞)⁻¹ *
        ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    -- From c_E · A ≤ B, derive A ≤ c_E⁻¹ · B.
    have h_inv_mul : (c_E : ℝ≥0∞)⁻¹ * ((c_E : ℝ≥0∞) *
        ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
            ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
              ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
            ∂(volume : Measure EuclN)) =
        ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
            ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
              ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
            ∂(volume : Measure EuclN) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel h_c_E_ne_zero h_c_E_ne_top, one_mul]
    calc ∫⁻ y in _, _ ∂_
        = (c_E : ℝ≥0∞)⁻¹ * ((c_E : ℝ≥0∞) *
            ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α,
                ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
                  ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
                ∂(volume : Measure EuclN)) := h_inv_mul.symm
      _ ≤ (c_E : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
          gcongr
  -- Take (1/2)-th roots of both sides.
  have h_pow_le : (∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
          ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α F y‖ₑ ^ (2 : ℝ)
        ∂(volume : Measure EuclN)) ^ ((1 : ℝ) / 2) ≤
      ((c_E : ℝ≥0∞)⁻¹ *
        ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        ^ ((1 : ℝ) / 2) :=
    ENNReal.rpow_le_rpow h_div (by positivity)
  refine h_pow_le.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / 2)]

/-! ## The `chartPushedRaw` Lp class for any `Lp ℝ 2 μ_g` -/

/-- For any Lp class `F : Lp ℝ 2 μ_g`, the chart-pullback function
`chartPushedRaw I α (F : M → ℝ)` is in `MemLp 2` of the chart-pulled
weighted measure restricted to `chartTargetEuclid α`. -/
noncomputable def chartPushedRawLpFromLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)) :=
  (chartPushedRaw_memLp_chartPulledWeighted (I := I) (M := M) g α
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)).toLp _

lemma chartPushedRawLpFromLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M)
    (F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        ((F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  unfold chartPushedRawLpFromLp
  exact MemLp.coeFn_toLp _

/-! ## Lp-convergence of `chartPushedRawLpFromLp` -/

/-- `chartPushedRawLpFromLp` preserves Lp-tendsto. The proof follows
`chartPushedLpFromLp_tendsto` (form-B), using the eLpNorm bound for
`chartPushedRaw`. -/
lemma chartPushedRawLpFromLp_tendsto
    (g : SmoothRiemannianMetric I M) (α : M)
    {F : ℕ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {F_lim : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (h_tendsto : Tendsto F atTop (𝓝 F_lim)) :
    Tendsto (fun n => chartPushedRawLpFromLp (I := I) (M := M) g α (F n))
      atTop (𝓝 (chartPushedRawLpFromLp (I := I) (M := M) g α F_lim)) := by
  classical
  -- Convert Lp-tendsto to eLpNorm-of-diff-tendsto-zero.
  have h_norm_tendsto :
      Tendsto (fun n => ‖F n - F_lim‖) atTop (𝓝 0) := by
    have h_sub : Tendsto (fun n => F n - F_lim) atTop (𝓝 0) := by
      have := h_tendsto.sub (tendsto_const_nhds (x := F_lim))
      simpa using this
    simpa using (continuous_norm.tendsto (0 :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))).comp h_sub
  -- Convert ‖F n - F_lim‖ to eLpNorm.
  have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_eLpNorm_eq : ∀ n,
      eLpNorm (((F n - F_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) =
      ENNReal.ofReal ‖F n - F_lim‖ := by
    intro n
    rw [Lp.norm_def]
    rw [ENNReal.ofReal_toReal
      ((Lp.memLp (F n - F_lim)).eLpNorm_lt_top.ne)]
  have h_eLpNorm_tendsto :
      Tendsto (fun n => eLpNorm (((F n - F_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
    have h_funeq : (fun n =>
        eLpNorm (((F n - F_lim) : Lp ℝ 2 _) : M → ℝ) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)) =
        (fun n => ENNReal.ofReal ‖F n - F_lim‖) := funext h_eLpNorm_eq
    rw [h_funeq]
    have h_comp := (ENNReal.continuous_ofReal.tendsto 0).comp h_norm_tendsto
    simp only [Function.comp_def, ENNReal.ofReal_zero] at h_comp
    exact h_comp
  -- The eLpNorm of (F n - F_lim).coeFn agrees with eLpNorm of (F n).coeFn - F_lim.coeFn.
  have h_aeEq : ∀ n, (((F n - F_lim) : Lp ℝ 2 _) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x -
        ((F_lim : Lp ℝ 2 _) : M → ℝ) x) := by
    intro n
    have := MeasureTheory.Lp.coeFn_sub (F n) F_lim
    filter_upwards [this] with x hx
    exact hx
  have h_diff_tendsto :
      Tendsto (fun n => eLpNorm
        (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
    have h_funeq : (fun n => eLpNorm
        (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) =
      (fun n => eLpNorm (((F n - F_lim) : Lp ℝ 2 _) : M → ℝ) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) := by
      funext n
      exact MeasureTheory.eLpNorm_congr_ae (h_aeEq n).symm
    rw [h_funeq]
    exact h_eLpNorm_tendsto
  -- Apply the eLpNorm bound for chartPushedRaw.
  have h_meas : ∀ n, Measurable (fun x : M => ((F n : Lp ℝ 2 _) : M → ℝ) x -
      ((F_lim : Lp ℝ 2 _) : M → ℝ) x) := fun n =>
    ((Lp.stronglyMeasurable (F n)).measurable).sub
      (Lp.stronglyMeasurable F_lim).measurable
  have h_chart_eLp_tendsto :
      Tendsto (fun n =>
        eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x)) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) atTop (𝓝 0) := by
    set c := ((DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞))⁻¹ ^ ((1 : ℝ)/2)
      with hc_def
    have h_const_tendsto :
        Tendsto (fun n => c *
          eLpNorm
            (fun x : M => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x) 2
            (riemannianVolumeMeasure (I := I) (M := M) g)) atTop (𝓝 0) := by
      have h_c_ne_top : c ≠ ⊤ := by
        rw [hc_def]
        refine ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_
        exact ENNReal.inv_ne_top.mpr
          (DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor_ennreal_ne_zero
            (E := E))
      have h := ENNReal.Tendsto.const_mul (a := c) (b := 0) h_diff_tendsto (Or.inr h_c_ne_top)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_const_tendsto
      (fun _ => zero_le _)
      (fun n => eLpNorm_chartPushedRaw_le (I := I) (M := M) g α (h_meas n))
  -- Now convert to Lp norm of chartPushedRawLpFromLp F_n - F_lim.
  rw [tendsto_iff_dist_tendsto_zero]
  have h_dist_eq : ∀ n,
      dist (chartPushedRawLpFromLp (I := I) (M := M) g α (F n))
          (chartPushedRawLpFromLp (I := I) (M := M) g α F_lim) =
        ENNReal.toReal (eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
            (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x)) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) := by
    intro n
    rw [dist_eq_norm, Lp.norm_def]
    have h_sub_aeEq := MeasureTheory.Lp.coeFn_sub
      (chartPushedRawLpFromLp (I := I) (M := M) g α (F n))
      (chartPushedRawLpFromLp (I := I) (M := M) g α F_lim)
    have h_coe_n := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α (F n)
    have h_coe_lim := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α F_lim
    have h_diff_ae : (((chartPushedRawLpFromLp (I := I) (M := M) g α (F n) -
            chartPushedRawLpFromLp (I := I) (M := M) g α F_lim) :
            Lp ℝ 2 _) : EuclN → ℝ) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x) := by
      filter_upwards [h_sub_aeEq, h_coe_n, h_coe_lim] with y hy_sub hy_n hy_lim
      rw [hy_sub, Pi.sub_apply, hy_n, hy_lim]
      -- chartPushedRaw is linear: chartPushedRaw(F₁ - F₂) y = chartPushedRaw(F₁) y - chartPushedRaw(F₂) y
      unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
      by_cases hy : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
      · simp [hy]
      · simp [hy]
    rw [MeasureTheory.eLpNorm_congr_ae h_diff_ae]
  rw [show (fun n =>
      dist (chartPushedRawLpFromLp (I := I) (M := M) g α (F n))
        (chartPushedRawLpFromLp (I := I) (M := M) g α F_lim)) =
    (fun n => ENNReal.toReal (eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)))) from funext h_dist_eq]
  have h_toReal_tendsto :
      Tendsto (fun n => ENNReal.toReal (eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
          (fun x => ((F n : Lp ℝ 2 _) : M → ℝ) x - ((F_lim : Lp ℝ 2 _) : M → ℝ) x)) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)))) atTop (𝓝 0) := by
    have h_comp := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp
      h_chart_eLp_tendsto
    simpa using h_comp
  exact h_toReal_tendsto

/-! ## The integral identity: chart-pulled CLM in setIntegral form

The crucial identity bridging the form-B headline's RHS to a setIntegral form:
for any `F : Lp ℝ 2 μ_g`, the chart-pulled integral CLM applied at `F` equals
the chart-target setIntegral of `density · chartPushedRaw F · ψ` against
volume. -/

/-- The smooth-case identity: for a smooth scalar `v`, the chart-pulled integral
CLM at `smoothToLp v` against weight `density · ψ` equals the chart-target setIntegral
of `density · chartPushedRaw v · ψ`. -/
private lemma chartPulledIntegralCLM_density_ψ_smoothToLp_eq_setIntegral
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    (v : SmoothScalar g) :
    chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothToLp (I := I) (M := M) g v) =
      ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v.toFun y *
          ψ y ∂(volume : Measure EuclN) := by
  classical
  -- Apply chartPulledIntegralCLM_smoothToLp with θ := density · ψ.
  -- The result: chartPulledIntegralCLM (density·ψ) (smoothToLp v) =
  --   ∫_chartTarget v.toFun(symm(toE.symm y)) · (density y · ψ y) ∂vol.
  have h_clm : chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothToLp (I := I) (M := M) g v) =
      ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        v.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          (densityOnEuclid (I := I) g α y * ψ y) ∂(volume : Measure EuclN) :=
    chartPulledIntegralCLM_smoothToLp (I := I) (M := M) g α
      (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
      (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
      (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
      v
  rw [h_clm]
  refine MeasureTheory.setIntegral_congr_fun
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet (fun y hy => ?_)
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
    (I := I) (M := M) α v.toFun hy]
  ring

/-! ## RHS as an inner product on the chart-pulled weighted measure

For any `g_lp : Lp ℝ 2 (chartPulledWeightedMeasure.restrict chartTarget)`,
the integral
```
∫_{chartTarget} density(y) · g_lp.coeFn(y) · ψ(y) ∂vol
```
equals an L² inner product between a fixed test class (`ψ_lp`) and `g_lp`.
This bridges the integral to a continuous linear functional on the Lp space.
-/

/-- `ψ` as an Lp class in `Lp ℝ 2 (chartPulledWeightedMeasure.restrict chartTarget)`.
ψ is continuous, compactly supported, and `tsupport ψ ⊆ chartTarget`, hence
`MemLp 2` of the weighted-restricted measure (continuous functions with compact
support are bounded, and the measure is finite on the support). -/
private lemma psi_memLp_chartPulledWeighted
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :
    MemLp ψ 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) :=
  continuous_compactSupport_memLp_chartPulledWeighted_restrict
    (I := I) (M := M) g α hψ.continuous hψ_cs hψ_supp

/-- The integral `∫_{chartTarget} density · f · ψ ∂vol` equals
`∫_{chartTarget} f · ψ ∂(chartPulledWeighted)`, for measurable `f`. -/
private lemma setIntegral_density_eq_integral_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    (f ψ : EuclN → ℝ) :
    ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y * f y * ψ y
      ∂(volume : Measure EuclN) =
    ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α, f y * ψ y
      ∂(chartPulledWeightedMeasure (I := I) g α) := by
  classical
  have h_meas_chartTarget :
      MeasurableSet (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  rw [show ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * f y * ψ y
        ∂(volume : Measure EuclN) =
      ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * (f y * ψ y)
        ∂(volume : Measure EuclN) from by
      refine MeasureTheory.setIntegral_congr_fun h_meas_chartTarget (fun y _hy => ?_)
      ring]
  rw [← setIntegral_chartPulledWeighted_eq_setIntegral_density_mul_volume
    (I := I) (M := M) g α (fun y => f y * ψ y)]

/-- The inner product representation: for any
`G : Lp ℝ 2 (chartPulledWeightedMeasure.restrict chartTarget)`,
```
∫_{chartTarget} density(y) · G.coeFn(y) · ψ(y) ∂vol
  = ⟪ψ_lp, G⟫_{L²((chartPulledWeighted).restrict chartTarget)},
```
where `ψ_lp = MemLp.toLp ψ` (the Lp class of ψ against the weighted measure). -/
private lemma setIntegral_density_G_psi_eq_inner
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    (G : Lp ℝ 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))) :
    ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        ((G : EuclN → ℝ) y) * ψ y ∂(volume : Measure EuclN) =
      @inner ℝ _ _
        ((psi_memLp_chartPulledWeighted
          (I := I) (M := M) g α hψ hψ_cs hψ_supp).toLp ψ) G := by
  classical
  -- Step 1: rewrite LHS via setIntegral_density_eq_integral_weighted.
  -- LHS: ∫_{chartTarget} density · G · ψ ∂vol = ∫_{chartTarget} G · ψ ∂(chartPulledWeighted)
  rw [setIntegral_density_eq_integral_weighted (I := I) (M := M) g α
    ((G : EuclN → ℝ)) ψ]
  -- Step 2: convert RHS to ∫ ⟨ψ_lp.coeFn, G⟩ ∂μ_w via L2.inner_def.
  rw [L2.inner_def
    ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α
      hψ hψ_cs hψ_supp).toLp ψ) G]
  -- LHS: ∫_{chartTarget} G · ψ ∂(chartPulledWeighted) = ∫ G · ψ ∂(chartPulledWeighted.restrict chartTarget)
  -- (setIntegral notation = integral against restricted measure).
  -- LHS: ∫ G · ψ ∂μ_w; RHS: ∫ ⟨ψ_lp.coeFn, G.coeFn⟩_ℝ ∂μ_w.
  -- For reals, ⟨a, b⟩_ℝ = b * a.
  have hae_psi : ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α
      hψ hψ_cs hψ_supp).toLp ψ : Lp ℝ 2 _) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)] ψ :=
    MemLp.coeFn_toLp _
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hae_psi] with y hy_psi
  rw [hy_psi]
  rw [show @inner ℝ _ _ (ψ y) ((G : EuclN → ℝ) y) =
      ((G : EuclN → ℝ) y) * ψ y from RCLike.inner_apply _ _]

/-! ## The integral identity for general `F : Lp ℝ 2 μ_g`

The smooth-case identity at line 725 of this file extends to arbitrary
`F : Lp ℝ 2 μ_g` by density: smooth scalars are Lp-dense in `Lp ℝ 2 μ_g`,
and both sides of the identity are continuous in `F`. -/

/-! ## Auxiliary: a.e. equality of `chartPushedRaw` for ae-equal manifold functions

For measurable `f₁, f₂ : M → ℝ` with `f₁ =ᵐ_{μ_g} f₂`, the chart-pullbacks
`chartPushedRaw I α f₁ =ᵐ chartPushedRaw I α f₂` w.r.t. the chart-pulled
weighted measure restricted to `chartTargetEuclid α`. This uses the
`lintegral_density_chartPushedRaw_pow_le` bound applied to the difference. -/

lemma chartPushedRaw_aeEq_of_aeEq
    (g : SmoothRiemannianMetric I M) (α : M)
    {f₁ f₂ : M → ℝ} (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (h_ae : f₁ =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] f₂) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f₁ =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α f₂ := by
  classical
  -- Consider d := f₁ - f₂. Then d =ᵐ_μ_g 0, so ∫⁻ ‖d‖² dμ_g = 0.
  -- By lintegral_density_chartPushedRaw_pow_le with p=2,
  -- c_E · ∫⁻ y in chartTarget, density y · ‖chartPushedRaw d y‖² ∂vol ≤ 0,
  -- so the integrand is 0 a.e. on vol.restrict chartTarget.
  -- Density > 0 on chartTarget, so ‖chartPushedRaw d y‖² = 0 a.e. on vol.restrict chartTarget.
  -- Hence chartPushedRaw f₁ y = chartPushedRaw f₂ y a.e. on vol.restrict chartTarget.
  -- Transfer to μ_w.restrict chartTarget via vol << μ_w on chartTarget (mutual absolute continuity).
  set d : M → ℝ := fun x => f₁ x - f₂ x with hd_def
  have hd_meas : Measurable d := hf₁.sub hf₂
  have hd_ae_zero : d =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] (fun _ => (0 : ℝ)) := by
    filter_upwards [h_ae] with x hx
    change f₁ x - f₂ x = 0
    rw [hx, sub_self]
  have h_lint_d_zero : ∫⁻ x, ‖d x‖ₑ ^ (2 : ℝ)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    have h_eq : (fun x : M => ‖d x‖ₑ ^ (2 : ℝ)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] (fun _ : M => (0 : ℝ≥0∞)) := by
      filter_upwards [hd_ae_zero] with x hx
      rw [hx]; simp
    rw [MeasureTheory.lintegral_congr_ae h_eq]; simp
  have h_bound :=
    lintegral_density_chartPushedRaw_pow_le (I := I) (M := M) g α
      (F := d) hd_meas (p := 2) (by norm_num)
  rw [h_lint_d_zero] at h_bound
  have h_c_E_pos : (0 : ℝ≥0∞) <
      (DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) := by
    exact_mod_cast DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor_pos
  have h_c_E_ne_zero :
      (DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) ≠ 0 :=
    ne_of_gt h_c_E_pos
  have h_set_lint_zero :
      ∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
          ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α d y‖ₑ ^ (2 : ℝ)
        ∂(volume : Measure EuclN) = 0 := by
    have h_mul_eq : (DifferentialGeometry.Analysis.Sobolev.Chart.euclideanHaarFactor E : ℝ≥0∞) *
        (∫⁻ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
            ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α d y‖ₑ ^ (2 : ℝ)
          ∂(volume : Measure EuclN)) = 0 := le_antisymm h_bound (zero_le _)
    rcases mul_eq_zero.mp h_mul_eq with hzero | hzero
    · exact absurd hzero h_c_E_ne_zero
    · exact hzero
  -- ae statement on vol.restrict chartTarget.
  have h_chartTarget_meas :
      MeasurableSet (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have h_density_pos_ae :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)),
      ENNReal.ofReal (densityOnEuclid (I := I) g α y) > 0 := by
    rw [ae_restrict_iff' h_chartTarget_meas]
    refine Filter.Eventually.of_forall fun y hy => ?_
    exact ENNReal.ofReal_pos.mpr (densityOnEuclid_pos (I := I) g α hy)
  have h_aestrong :
      AEMeasurable (fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
          ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α d y‖ₑ ^ (2 : ℝ))
      ((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
    refine AEMeasurable.mul ?_ ?_
    · refine (ENNReal.measurable_ofReal.comp_aemeasurable ?_)
      exact (densityOnEuclid_continuousOn (I := I) g α).aemeasurable
        h_chartTarget_meas
    · refine AEMeasurable.pow_const ?_ _
      exact (chartPushedRaw_measurable (I := I) (M := M) α hd_meas).enorm.aemeasurable
  have h_integrand_ae_zero :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)),
      ENNReal.ofReal (densityOnEuclid (I := I) g α y) *
        ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α d y‖ₑ ^ (2 : ℝ) = 0 :=
    (MeasureTheory.lintegral_eq_zero_iff' h_aestrong).mp h_set_lint_zero
  have h_chartPushed_d_zero :
      ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)),
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α d y = 0 := by
    filter_upwards [h_integrand_ae_zero, h_density_pos_ae] with y hy h_pos
    rcases mul_eq_zero.mp hy with h | h
    · exact absurd h h_pos.ne'
    · have h_enorm_zero : ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α d y‖ₑ = 0 := by
        have : (‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α d y‖ₑ) ^ (2 : ℝ) =
            ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α d y‖ₑ ^ (2 : ℝ) := rfl
        rw [this] at h
        have h_two_pos : (0 : ℝ) < 2 := by norm_num
        have h_rpow := ENNReal.rpow_eq_zero_iff.mp h
        rcases h_rpow with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact h1
        · exact absurd h2 (by norm_num)
      exact (enorm_eq_zero (a := DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α d y)).mp h_enorm_zero
  -- Transfer to μ_w.restrict chartTarget.
  -- μ_w.restrict chartTarget = (vol.withDensity density).restrict chartTarget
  --   = (vol.restrict chartTarget).withDensity density.
  -- For any A: μ_w.restrict chartTarget (A) = ∫_{A ∩ chartTarget} density dvol.
  -- If vol.restrict chartTarget (A) = 0 (i.e. vol(A ∩ chartTarget) = 0), then μ_w-integrand is 0 a.e. on A, so μ_w(A ∩ chartTarget) = 0.
  -- Hence μ_w.restrict chartTarget << vol.restrict chartTarget.
  have h_abs_cts :
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) ≪
      (volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
    unfold chartPulledWeightedMeasure
    rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) =
        ((volume : Measure EuclN).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      from MeasureTheory.restrict_withDensity h_chartTarget_meas _]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_chartPushed_d_zero_w :=
    h_abs_cts.ae_le h_chartPushed_d_zero
  -- chartPushedRaw d = chartPushedRaw f₁ - chartPushedRaw f₂ pointwise (where both are nonzero or off chartTarget).
  filter_upwards [h_chartPushed_d_zero_w] with y hy
  -- Goal: chartPushedRaw f₁ y = chartPushedRaw f₂ y.
  -- We use the case split on y ∈ chartTarget.
  by_cases h_in_chart : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α
  · -- On chartTarget: chartPushedRaw f y = f(symm(toE.symm y)).
    -- chartPushedRaw d y = d(symm(toE.symm y)) = f₁(symm(...)) - f₂(symm(...)) = 0.
    -- So f₁(symm(...)) = f₂(symm(...)), hence chartPushedRaw f₁ y = chartPushedRaw f₂ y.
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α d h_in_chart] at hy
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α f₁ h_in_chart]
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α f₂ h_in_chart]
    rw [hd_def] at hy
    linarith [sub_eq_zero.mp hy]
  · -- Off chartTarget: both sides are zero.
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α f₁ h_in_chart]
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α f₂ h_in_chart]

/-- For any `F : Lp ℝ 2 μ_g`, the chart-pulled integral CLM at `F` against
the weight `density · ψ` equals the chart-target setIntegral of
`density · (chartPushedRawLpFromLp F).coeFn · ψ ∂vol`. This is the general
form of the smooth-case identity, extended by density from smooth scalars. -/
theorem chartPulledIntegralCLM_density_ψ_eq_setIntegral
    (g : SmoothRiemannianMetric I M) (α : M)
    {ψ : EuclN → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_cs : HasCompactSupport ψ)
    (hψ_supp : tsupport ψ ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)
    (F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp) F =
      ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((chartPushedRawLpFromLp (I := I) (M := M) g α F :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α))) : EuclN → ℝ) y *
          ψ y ∂(volume : Measure EuclN) := by
  classical
  -- Strategy: smooth-dense approximation. Pick v_n → F in Lp(μ_g).
  obtain ⟨v, h_v_tendsto⟩ :=
    DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1ComplFromDom.exists_smooth_approx_seq_lp
      (I := I) (M := M) g F
  -- LHS is continuous in F (CLM applied to F).
  have h_LHS_tendsto :
      Tendsto (fun n =>
        chartPulledIntegralCLM (I := I) (M := M) g α
          (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
          (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
          (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
          (smoothToLp (I := I) (M := M) g (v n))) atTop
      (𝓝 (chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp) F)) :=
    chartPulledIntegralCLM_tendsto (I := I) (M := M) g α
      (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
      (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
      (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
      h_v_tendsto
  -- Apply the smooth-case identity for each v_n.
  have h_smooth_case : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothToLp (I := I) (M := M) g (v n)) =
      ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α (v n).toFun y *
          ψ y ∂(volume : Measure EuclN) := fun n =>
    chartPulledIntegralCLM_density_ψ_smoothToLp_eq_setIntegral
      (I := I) (M := M) g α hψ hψ_cs hψ_supp (v n)
  -- Bridge: chartPushedRawLpFromLp (smoothToLp v_n) coeFn =ᵐ chartPushedRaw v_n.toFun.
  have h_aeEq : ∀ n,
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g (v n)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α (v n).toFun := by
    intro n
    have h_coe := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
      (smoothToLp (I := I) (M := M) g (v n))
    have h_smoothLp_aeEq :
        ((smoothToLp (I := I) (M := M) g (v n) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] (v n).toFun :=
      MemLp.coeFn_toLp (v n).memLp_two
    have h_bridge := chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      (Lp.stronglyMeasurable _).measurable
      ((v n).smooth.continuous.measurable)
      h_smoothLp_aeEq
    exact h_coe.trans h_bridge
  -- Convert RHS for v_n: ∫ density · chartPushedRaw v_n.toFun · ψ ∂vol
  --                    = ∫ density · chartPushedRawLpFromLp(smoothToLp v_n).coeFn · ψ ∂vol.
  have h_RHS_v_n_eq : ∀ n,
      ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α (v n).toFun y *
          ψ y ∂(volume : Measure EuclN) =
        ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          ((chartPushedRawLpFromLp (I := I) (M := M) g α
            (smoothToLp (I := I) (M := M) g (v n)) :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α))) : EuclN → ℝ) y *
          ψ y ∂(volume : Measure EuclN) := by
    intro n
    rw [setIntegral_density_eq_integral_weighted (I := I) (M := M) g α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α (v n).toFun) ψ]
    rw [setIntegral_density_eq_integral_weighted (I := I) (M := M) g α
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g (v n)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) ψ]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [(h_aeEq n).symm] with y hy
    rw [hy]
  -- Convert each side via inner product against ψ_lp.
  have h_inner_v_n : ∀ n,
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothToLp (I := I) (M := M) g (v n)) =
      @inner ℝ _ _
        ((psi_memLp_chartPulledWeighted
          (I := I) (M := M) g α hψ hψ_cs hψ_supp).toLp ψ)
        (chartPushedRawLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g (v n))) := by
    intro n
    rw [h_smooth_case n, h_RHS_v_n_eq n]
    rw [setIntegral_density_G_psi_eq_inner (I := I) (M := M) g α
      hψ hψ_cs hψ_supp (chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g (v n)))]
  -- Goal: rewrite as inner product against ψ_lp.
  rw [setIntegral_density_G_psi_eq_inner (I := I) (M := M) g α
    hψ hψ_cs hψ_supp (chartPushedRawLpFromLp (I := I) (M := M) g α F)]
  -- Now both sides are limits of the same sequence.
  have h_chartPushedRaw_tendsto :
      Tendsto (fun n => chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g (v n))) atTop
      (𝓝 (chartPushedRawLpFromLp (I := I) (M := M) g α F)) :=
    chartPushedRawLpFromLp_tendsto (I := I) (M := M) g α h_v_tendsto
  have h_inner_tendsto : Tendsto (fun n => @inner ℝ _ _
      ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α hψ hψ_cs hψ_supp).toLp ψ)
      (chartPushedRawLpFromLp (I := I) (M := M) g α
        (smoothToLp (I := I) (M := M) g (v n)))) atTop
    (𝓝 (@inner ℝ _ _
      ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α hψ hψ_cs hψ_supp).toLp ψ)
      (chartPushedRawLpFromLp (I := I) (M := M) g α F))) := by
    have h_inner_cont :
        Continuous (fun G => @inner ℝ _ _
          ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α hψ hψ_cs hψ_supp).toLp ψ)
          G) := continuous_const.inner continuous_id
    exact (h_inner_cont.tendsto _).comp h_chartPushedRaw_tendsto
  have h_LHS_eq_inner_seq : (fun n =>
      chartPulledIntegralCLM (I := I) (M := M) g α
        (densityPsi_cont (I := I) (M := M) (g := g) (α := α) hψ hψ_supp)
        (densityPsi_cs (I := I) (M := M) (g := g) (α := α) hψ_cs)
        (densityPsi_supp (I := I) (M := M) (g := g) (α := α) hψ_supp)
        (smoothToLp (I := I) (M := M) g (v n))) =
      (fun n => @inner ℝ _ _
        ((psi_memLp_chartPulledWeighted (I := I) (M := M) g α hψ hψ_cs hψ_supp).toLp ψ)
        (chartPushedRawLpFromLp (I := I) (M := M) g α
          (smoothToLp (I := I) (M := M) g (v n)))) := funext h_inner_v_n
  rw [h_LHS_eq_inner_seq] at h_LHS_tendsto
  exact tendsto_nhds_unique h_LHS_tendsto h_inner_tendsto

/-! ## Auxiliary: weak partial on the full chart target

The lemma `hasWeakPartialDeriv_chartPushedWeakPartialLp_on_compact` proves
the weak partial relation only on open sets `Ω ⊆ K` with `K` compact and
`K ⊆ chartTargetEuclid α`. To populate the `weak_partial_isWeakPartial`
struct field, we extend the relation to the full open `chartTargetEuclid α`
via a precompact-neighborhood argument. -/

/-- The chart-pushed weak partial is a weak partial of
`chartPushed POU α (H1ComplToLp u_h).coeFn` on the full open
`chartTargetEuclid α`. -/
theorem hasWeakPartialDeriv_chartPushedWeakPartialLp_on_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (u_h : H1Compl g) :
    DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
      (((chartPushedWeakPartialLp (I := I) (M := M) g α j
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α j) u_h
       ) : EuclN → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  -- Test function φ with tsupport ⊆ chartTarget.
  intro φ hφ_smooth hφ_cs hφ_supp
  -- Build a precompact open Ω' with tsupport φ ⊆ Ω' ⊆ closure Ω' ⊆ chartTarget.
  have hΩ_open :
      IsOpen (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  obtain ⟨δ, hδ_pos, hδ_subset⟩ :
      ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ (tsupport φ) ⊆
        DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α :=
    hφ_cs.exists_cthickening_subset_open hΩ_open hφ_supp
  set Ω' : Set EuclN := Metric.thickening δ (tsupport φ) with hΩ'_def
  set K : Set EuclN := Metric.cthickening δ (tsupport φ) with hK_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have hK_compact : IsCompact K := hφ_cs.cthickening
  have hΩ'_subset_K : Ω' ⊆ K := Metric.thickening_subset_cthickening δ (tsupport φ)
  have hK_in : K ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α := hδ_subset
  have h_tsupport_in_Ω' : tsupport φ ⊆ Ω' :=
    Metric.self_subset_thickening hδ_pos _
  -- Apply the local weak-partial lemma on Ω'.
  have h_local :=
    hasWeakPartialDeriv_chartPushedWeakPartialLp_on_compact
      (I := I) (M := M) g α j u_h hΩ'_open hK_compact hΩ'_subset_K hK_in
  -- Now reduce ∫_{chartTarget} to ∫_{Ω'}, using tsupport φ ⊆ Ω'.
  have h_identity := h_local φ hφ_smooth hφ_cs h_tsupport_in_Ω'
  -- h_identity: ∫_{Ω'} f · fderiv φ (e_j) = -∫_{Ω'} g · φ.
  -- Goal: ∫_{chartTarget} f · fderiv φ (e_j) = -∫_{chartTarget} g · φ.
  -- We use the fact that fderiv φ vanishes outside tsupport φ, hence outside Ω'.
  set f := DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
    (chartAtlasPOU I M) α
    ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) with hf_def
  set g_chart := ((chartPushedWeakPartialLp (I := I) (M := M) g α j
    (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α j) u_h
   ) : EuclN → ℝ) with hg_chart_def
  -- Outside tsupport φ, both φ and fderiv ℝ φ are zero.
  -- So the integrals over chartTarget and Ω' agree.
  have h_chartTarget_meas :
      MeasurableSet (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := hΩ_open.measurableSet
  have hΩ'_meas : MeasurableSet Ω' := hΩ'_open.measurableSet
  have hΩ'_subset_chartTarget : Ω' ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α := hΩ'_subset_K.trans hK_in
  -- The fderiv of φ vanishes outside tsupport φ (φ is locally constant 0 there).
  have h_fderiv_zero : ∀ x ∉ tsupport φ, fderiv ℝ φ x = 0 := by
    intro x hx
    have h_compl_open : IsOpen ((tsupport φ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    have hx_in_compl : x ∈ (tsupport φ)ᶜ := hx
    have hφ_zero_nbhd : ∀ᶠ y in 𝓝 x, φ y = 0 := by
      filter_upwards [h_compl_open.mem_nhds hx_in_compl] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hφ_const_zero : fderiv ℝ φ x = fderiv ℝ (fun _ : EuclN => (0 : ℝ)) x := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hφ_zero_nbhd] with y hy
      rw [hy]
    rw [hφ_const_zero]
    simp
  -- LHS: ∫_{chartTarget} f · fderiv φ (e_j) = ∫_{Ω'} f · fderiv φ (e_j) (since rest is 0).
  have h_LHS_eq :
      ∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
      ∫ x in Ω', f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
    -- ∫_{chartTarget} F = ∫_{Ω'} F + ∫_{chartTarget \ Ω'} F.
    -- F = 0 on chartTarget \ Ω' since fderiv φ = 0 outside tsupport φ ⊆ Ω'.
    rw [show ∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        ∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) x
        from by
      refine (MeasureTheory.setIntegral_congr_fun h_chartTarget_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem hx]]
    rw [show ∫ x in Ω', f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        ∫ x in Ω', (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) x from by
      refine (MeasureTheory.setIntegral_congr_fun hΩ'_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem (hΩ'_subset_chartTarget hx)]]
    -- Now both sides are integrals of the indicator on different sets.
    -- The indicator vanishes outside chartTarget. We need to show the integral
    -- depends only on Ω' (where the indicator might be non-zero).
    -- Specifically, outside Ω', fderiv φ (and thus the integrand) is zero.
    have h_outside_Ω' : ∀ x ∈ (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) \ Ω',
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α).indicator
          (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) x = 0 := by
      intro x ⟨hx_in_chart, hx_notin_Ω'⟩
      rw [Set.indicator_of_mem hx_in_chart]
      have hx_notin_tsupport : x ∉ tsupport φ := fun hx => hx_notin_Ω' (h_tsupport_in_Ω' hx)
      rw [h_fderiv_zero x hx_notin_tsupport]
      simp
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (f := _) (s := Ω')]
    · rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (f := _) (s := DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)]
      intro x hx
      by_cases hx_in_chart : x ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
      · exact absurd hx_in_chart hx
      · rw [Set.indicator_of_notMem hx_in_chart]
    intro x hx
    by_cases hx_in_chart : x ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · -- x ∈ chartTarget but x ∉ Ω'. Then h_outside_Ω' applies.
      exact h_outside_Ω' x ⟨hx_in_chart, hx⟩
    · rw [Set.indicator_of_notMem hx_in_chart]
  -- RHS: ∫_{chartTarget} g_chart · φ = ∫_{Ω'} g_chart · φ.
  have h_RHS_eq :
      ∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        g_chart x * φ x =
      ∫ x in Ω', g_chart x * φ x := by
    -- Similar argument: outside tsupport φ, φ = 0; tsupport φ ⊆ Ω'.
    rw [show ∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          g_chart x * φ x =
        ∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => g_chart x * φ x) x
        from by
      refine (MeasureTheory.setIntegral_congr_fun h_chartTarget_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem hx]]
    rw [show ∫ x in Ω', g_chart x * φ x =
        ∫ x in Ω', (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α).indicator
            (fun x => g_chart x * φ x) x from by
      refine (MeasureTheory.setIntegral_congr_fun hΩ'_meas (fun x hx => ?_)).symm
      rw [Set.indicator_of_mem (hΩ'_subset_chartTarget hx)]]
    have h_outside_Ω' : ∀ x ∈ (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) \ Ω',
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α).indicator
          (fun x => g_chart x * φ x) x = 0 := by
      intro x ⟨hx_in_chart, hx_notin_Ω'⟩
      rw [Set.indicator_of_mem hx_in_chart]
      have hx_notin_tsupport : x ∉ tsupport φ := fun hx => hx_notin_Ω' (h_tsupport_in_Ω' hx)
      have hφ_x_zero : φ x = 0 := image_eq_zero_of_notMem_tsupport hx_notin_tsupport
      rw [hφ_x_zero, mul_zero]
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (f := _) (s := Ω')]
    · rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (f := _) (s := DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α)]
      intro x hx
      by_cases hx_in_chart : x ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α
      · exact absurd hx_in_chart hx
      · rw [Set.indicator_of_notMem hx_in_chart]
    intro x hx
    by_cases hx_in_chart : x ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α
    · exact h_outside_Ω' x ⟨hx_in_chart, hx⟩
    · rw [Set.indicator_of_notMem hx_in_chart]
  rw [h_LHS_eq, h_RHS_eq]
  exact h_identity

/-! ## Constructor for `ChartBilinearH1ComplData` from a `laplacianDomain g` element

We package the data fields and discharge each condition. -/

/-- The chart-bilinear data associated with an element `u_h ∈ laplacianDomain g`. -/
noncomputable def chartBilinearH1ComplData_of_laplacianDomain
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    ChartBilinearH1ComplData (I := I) (M := M) g α where
  u_chart :=
    ((chartPushedLpFromLp (I := I) (M := M) g α
      (H1ComplToLp (I := I) (M := M) g u_h) :
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))) : EuclN → ℝ)
  f_chart :=
    ((chartPushedRawLpFromLp (I := I) (M := M) g α
      (fHLeibniz (I := I) (M := M) g α u_h hu_h) :
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))) : EuclN → ℝ)
  weak_partial := fun i =>
    ((chartPushedWeakPartialLp (I := I) (M := M) g α i
      (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α))) : EuclN → ℝ)
  u_chart_memLp_weighted :=
    Lp.memLp (chartPushedLpFromLp (I := I) (M := M) g α
      (H1ComplToLp (I := I) (M := M) g u_h))
  f_chart_memLp_weighted :=
    Lp.memLp (chartPushedRawLpFromLp (I := I) (M := M) g α
      (fHLeibniz (I := I) (M := M) g α u_h hu_h))
  weak_partial_locally_memLp := fun i K hK hK_in =>
    chartPushedWeakPartialLp_locally_memLp (I := I) (M := M) g α i u_h hK hK_in
  weak_partial_isWeakPartial := fun i => by
    -- The chart-pushed weak partial coeFn is a weak partial of u_chart.
    -- The lemma `hasWeakPartialDeriv_chartPushedWeakPartialLp_on_chartTarget` proves the
    -- relation for `f = chartPushed POU` directly. We need it for `f = u_chart =
    -- chartPushedLpFromLp.coeFn`, which agrees a.e. with chartPushed POU on weighted.restrict chartTarget.
    -- Transfer via mutual absolute continuity vol.restrict chartTarget ↔ weighted.restrict chartTarget.
    have h_base := hasWeakPartialDeriv_chartPushedWeakPartialLp_on_chartTarget
      (I := I) (M := M) g α i u_h
    intro φ hφ_smooth hφ_cs hφ_supp
    have h_id := h_base φ hφ_smooth hφ_cs hφ_supp
    have h_coeFn := chartPushedLpFromLp_coeFn (I := I) (M := M) g α
      (H1ComplToLp (I := I) (M := M) g u_h)
    have h_meas : MeasurableSet
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α).measurableSet
    -- ae statement on weighted.restrict chartTarget.
    have h_w_abs : (chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) ≪
        (volume : Measure EuclN).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
      unfold chartPulledWeightedMeasure
      rw [show ((volume : Measure EuclN).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) =
          ((volume : Measure EuclN).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        from MeasureTheory.restrict_withDensity h_meas _]
      exact MeasureTheory.withDensity_absolutelyContinuous _ _
    have h_v_abs_w :
        (volume : Measure EuclN).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) ≪
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
      -- Use density > 0 strictly on chartTarget.
      intro A hA
      unfold chartPulledWeightedMeasure at hA
      rw [show ((volume : Measure EuclN).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) =
          ((volume : Measure EuclN).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)).withDensity
            (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        from MeasureTheory.restrict_withDensity h_meas _] at hA
      rw [MeasureTheory.withDensity_apply_eq_zero'
        (μ := (volume : Measure EuclN).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))
        (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
        (ENNReal.measurable_ofReal.comp_aemeasurable
          ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_meas))] at hA
      -- hA: vol.restrict chartTarget {y | ENNReal.ofReal (density y) ≠ 0 ∧ y ∈ A} = 0.
      -- We show vol.restrict chartTarget A ≤ vol.restrict chartTarget {y | density ≠ 0 ∧ y ∈ A}.
      -- Both measures count only y ∈ chartTarget. On chartTarget, density > 0, so density ≠ 0.
      -- Hence on chartTarget, {y ∈ A} ⊆ {density ≠ 0 ∧ y ∈ A}.
      -- Set A is null wrt vol.restrict chartTarget iff vol(A ∩ chartTarget) = 0.
      rw [Measure.restrict_apply' h_meas]
      -- Goal: vol(A ∩ chartTarget) = 0.
      -- We have hA: vol.restrict chartTarget ({density ≠ 0} ∩ A) = 0,
      -- which by Measure.restrict_apply' = vol({density ≠ 0} ∩ A ∩ chartTarget) = 0.
      rw [Measure.restrict_apply' h_meas] at hA
      -- hA: vol({density ≠ 0} ∩ A ∩ chartTarget) = 0.
      -- We show A ∩ chartTarget ⊆ {density ≠ 0} ∩ A ∩ chartTarget.
      refine MeasureTheory.measure_mono_null ?_ hA
      intro y ⟨hy_A, hy_chart⟩
      refine ⟨⟨?_, hy_A⟩, hy_chart⟩
      have h_pos : 0 < densityOnEuclid (I := I) g α y :=
        densityOnEuclid_pos (I := I) g α hy_chart
      exact (ENNReal.ofReal_pos.mpr h_pos).ne'
    -- Now transfer h_coeFn from weighted.restrict to vol.restrict.
    have h_coeFn_vol : ((chartPushedLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h)) : EuclN → ℝ) =ᵐ[
          (volume : Measure EuclN).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) :=
      h_v_abs_w.ae_le h_coeFn
    -- Now rewrite the LHS integral via setIntegral_congr_ae.
    -- Goal: ∫_{chartTarget} u_chart · ∂_i φ = -∫_{chartTarget} weak_partial · φ.
    -- h_id says: ∫_{chartTarget} chartPushed POU · ∂_i φ = -∫_{chartTarget} weak_partial · φ.
    -- So we need ∫_{chartTarget} u_chart · ∂_i φ = ∫_{chartTarget} chartPushed POU · ∂_i φ.
    -- By ae-equality of u_chart and chartPushed POU on vol.restrict chartTarget.
    have h_int_eq :
        ∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          ((chartPushedLpFromLp (I := I) (M := M) g α
            (H1ComplToLp (I := I) (M := M) g u_h) :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α))) : EuclN → ℝ) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
        ∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) x *
            (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_coeFn_vol] with x hx
      rw [hx]
    -- The struct field uses MetricExtension.chartTargetEuclid; our h_int_eq uses
    -- Sobolev.Chart.chartTargetEuclid. They're definitionally equal.
    change ∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α,
        ((chartPushedLpFromLp (I := I) (M := M) g α
          (H1ComplToLp (I := I) (M := M) g u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) : EuclN → ℝ) x *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
      -∫ x in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α,
        ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α))) : EuclN → ℝ) x * φ x
    rw [h_int_eq]
    exact h_id
  variational_identity := by
    -- Apply the form-B headline; convert RHS via Part A.
    intro ψ hψ hψ_cs hψ_supp
    have h_formB := laplacianDomain_variational_identity_general
      (I := I) (M := M) g α hu_h hψ hψ_cs hψ_supp
    -- h_formB: LHS_principal + LHS_mass = chartPulledIntegralCLM (density·ψ) (fHLeibniz)
    --   where:
    --     LHS_principal: ∫_{chartTarget} ∑_{i,j} weightedInvGram · chartPushedWeakPartialLp(u_h) i · ∂_j ψ ∂vol
    --     LHS_mass: ∫_{chartTarget} density · chartPushed POU (H1ComplToLp u_h) · ψ ∂vol
    -- Convert RHS using Part A.
    have h_partA := chartPulledIntegralCLM_density_ψ_eq_setIntegral
      (I := I) (M := M) g α hψ hψ_cs hψ_supp
      (fHLeibniz (I := I) (M := M) g α u_h hu_h)
    -- h_partA: chartPulledIntegralCLM... fHLeibniz = ∫_{chartTarget} density · chartPushedRawLpFromLp(fHLeibniz).coeFn · ψ ∂vol
    -- The form-B LHS mass uses chartPushed POU α (H1ComplToLp u_h).coeFn directly; we use u_chart = chartPushedLpFromLp(...).coeFn.
    -- These agree a.e. by chartPushedLpFromLp_coeFn.
    rw [h_partA] at h_formB
    -- Now rewrite the form-B LHS mass using u_chart, then we're done.
    -- u_chart = chartPushedLpFromLp(H1ComplToLp u_h) .coeFn =ᵐ chartPushed POU α (H1ComplToLp u_h).coeFn.
    have h_u_chart_ae := chartPushedLpFromLp_coeFn (I := I) (M := M) g α
      (H1ComplToLp (I := I) (M := M) g u_h)
    -- We need to transfer this to a setIntegral_congr_ae over vol.restrict chartTarget,
    -- but the integral is wrt vol, with integrand involving density · u_chart · ψ.
    -- Since u_chart =ᵐ_weighted chartPushed POU, and density·ψ is a "test", we get the same integrals
    -- but only modulo ae wrt weighted. We need ae wrt vol on chartTarget.
    -- Approach: rewrite both setIntegrals using setIntegral_density_eq_integral_weighted.
    -- ∫_{chartTarget} density · g · ψ ∂vol = ∫_{chartTarget} g · ψ ∂(weighted).
    rw [setIntegral_density_eq_integral_weighted (I := I) (M := M) g α
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) ψ] at h_formB
    -- Now h_formB has LHS_mass: ∫_{chartTarget} chartPushed POU · ψ ∂(weighted).
    -- We want to rewrite to ∫_{chartTarget} u_chart · ψ ∂(weighted) via ae.
    -- This needs setIntegral_congr_ae against the restricted measure.
    have h_LHS_mass_eq :
        ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
            (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) y * ψ y
          ∂(chartPulledWeightedMeasure (I := I) g α) =
        ∫ y in DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α,
          ((chartPushedLpFromLp (I := I) (M := M) g α
            (H1ComplToLp (I := I) (M := M) g u_h) :
            Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α))) : EuclN → ℝ) y * ψ y
          ∂(chartPulledWeightedMeasure (I := I) g α) := by
      -- ae-rewrite on chartPulledWeighted.restrict chartTarget.
      -- ∫_{chartTarget} F ∂weighted = ∫ F ∂(weighted.restrict chartTarget).
      refine MeasureTheory.integral_congr_ae ?_
      -- The ae statement is on weighted.restrict chartTarget.
      -- h_u_chart_ae is on weighted.restrict chartTarget.
      filter_upwards [h_u_chart_ae] with y hy
      rw [hy]
    rw [h_LHS_mass_eq] at h_formB
    -- Convert back to the vol form.
    rw [← setIntegral_density_eq_integral_weighted (I := I) (M := M) g α
      ((chartPushedLpFromLp (I := I) (M := M) g α
        (H1ComplToLp (I := I) (M := M) g u_h) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) ψ] at h_formB
    exact h_formB

/-! ## Convenience accessors for the constructor output -/

/-- The `u_chart` field of the structure returned by
`chartBilinearH1ComplData_of_laplacianDomain` equals the chart-pushed Lp class
coercion (with-ρα). -/
lemma chartBilinearH1ComplData_of_laplacianDomain_u_chart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h).u_chart =
      ((chartPushedLpFromLp (I := I) (M := M) g α
        (H1ComplToLp (I := I) (M := M) g u_h) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) := rfl

/-- The `weak_partial` field of the structure returned by
`chartBilinearH1ComplData_of_laplacianDomain` equals the chart-pushed weak
partial Lp class coercion. -/
lemma chartBilinearH1ComplData_of_laplacianDomain_weak_partial_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h).weak_partial i =
      ((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) := rfl

/-- The `f_chart` field of the structure returned by
`chartBilinearH1ComplData_of_laplacianDomain` equals the chart-pullback Lp class
coercion (no-ρα) of `fHLeibniz`. -/
lemma chartBilinearH1ComplData_of_laplacianDomain_f_chart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α hu_h).f_chart =
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
        (fHLeibniz (I := I) (M := M) g α u_h hu_h) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α))) : EuclN → ℝ) := rfl

end LaplacianDomainChartData
end Laplacian
end Analysis
end DifferentialGeometry
