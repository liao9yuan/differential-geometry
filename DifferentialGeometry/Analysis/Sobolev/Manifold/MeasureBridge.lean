import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich
import DifferentialGeometry.Integral.Measure.Glue
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Integral.Measure.Invariance
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Bridge between the Riemannian measure and Euclidean volume on chart targets

For a function `u : M → ℝ` on a smooth Riemannian manifold supported in a single
chart `α`, this file provides quantitative comparisons between

* the global Riemannian-measure `eLpNorm` of `u` on `M`, and
* the Euclidean-volume `eLpNorm` of the chart-pushed function on the chart target
  inside `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`.

The chart-pushed function comes in two flavours: a *raw* version
`chartPushedRaw I α u`, which composes `u` with the inverse chart and
`toEuclidean.symm`, and the partition-of-unity-weighted version `chartPushed`
already defined in `Sobolev/Chart.lean`. The raw version is the natural target
for the chart-target Euclidean integral, since it carries no partition-of-unity
weight.

The constants depend only on the chart `α` and the metric `g` (specifically:
the Haar / volume scale factor on the model space, and the supremum / infimum
of the smooth positive density `chartDensity g α` on the compact image of
`tsupport u`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Raw chart pushforward (no partition-of-unity weight) -/

variable (I)

/-- Raw chart pushforward of `u : M → ℝ` at chart `α`, with the
partition-of-unity weight removed. Outside the toEuclidean image of the chart
target the value is `0`. -/
def chartPushedRaw (α : M) (u : M → ℝ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      u ((extChartAt I α).symm (toEuclidean.symm y))
    else 0

variable {I}

/-- On the chart target image, the raw chart pushforward is `u ∘ symm`. -/
lemma chartPushedRaw_apply_of_mem (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α u y =
      u ((extChartAt I α).symm (toEuclidean.symm y)) := by
  classical
  unfold chartPushedRaw; simp [hy]

/-- Outside the chart target image, the raw chart pushforward is zero. -/
lemma chartPushedRaw_apply_of_notMem (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α u y = 0 := by
  classical
  unfold chartPushedRaw; simp [hy]

/-- The raw pushforward vanishes outside the chart target image. -/
lemma chartPushedRaw_eq_zero_off_chartTargetEuclid (α : M) (u : M → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α u y = 0 :=
  chartPushedRaw_apply_of_notMem α u hy

/-! ## File-local helpers -/

/-- The extended-chart target is Borel-measurable in `E`. -/
private lemma extChartAt_target_measurableSet (α : M) :
    MeasurableSet (extChartAt I α).target :=
  DifferentialGeometry.Integral.Measure.measurableSet_extChartAt_target
    (I := I) (M := M) α

/-! ## The chart-target image (under `toEuclidean`) is measurable -/

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- `toEuclidean` is a measurable embedding (since it is a homeomorphism). -/
private lemma toEuclidean_measurableEmbedding :
    MeasurableEmbedding (toEuclidean : E → EuclN E) :=
  (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv.measurableEmbedding

/-- The chart-target image (under `toEuclidean`) is measurable. -/
lemma chartTargetEuclid_measurableSet (α : M) :
    MeasurableSet (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chartTargetEuclid
  have hT : MeasurableSet (extChartAt I α).target :=
    extChartAt_target_measurableSet (I := I) (M := M) α
  exact (toEuclidean_measurableEmbedding (E := E)).measurableSet_image.mpr hT

/-- The chart-target image (under `toEuclidean`) coincides with the preimage of
the chart target under `toEuclidean.symm`. -/
lemma chartTargetEuclid_eq_preimage_symm (α : M) :
    chartTargetEuclid (I := I) (M := M) α =
      (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target := by
  unfold chartTargetEuclid
  ext y
  refine ⟨fun ⟨x, hx, hxy⟩ => ?_, fun hy => ⟨toEuclidean.symm y, hy, ?_⟩⟩
  · simp only [Set.mem_preimage]
    rw [← hxy, ContinuousLinearEquiv.symm_apply_apply]
    exact hx
  · exact (toEuclidean (E := E)).apply_symm_apply y

/-- `(extChartAt I α).symm ∘ toEuclidean.symm` sends `chartTargetEuclid α`
into `(chartAt H α).source`. -/
lemma symm_toEuclidean_symm_mem_chartAtSource (α : M)
    {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (chartAt H α).source := by
  rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
  have hsource : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈
      (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
    (I := I) (M := M)] at hsource

/-- `(extChartAt I α).symm ∘ toEuclidean.symm` is continuous on
`chartTargetEuclid α`. -/
lemma continuousOn_symm_toEuclideanSymm (α : M) :
    ContinuousOn
      (fun y : EuclN E =>
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hy_target : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    intro y hy
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  exact (continuousOn_extChartAt_symm (I := I) α).comp
    (toEuclidean (E := E)).symm.continuous.continuousOn hy_target

/-! ## Pushforward of `modelHaar` along `toEuclidean` -/

/-- The pushforward of `modelHaar` along the continuous linear equivalence
`toEuclidean : E ≃L[ℝ] EuclN E` is itself an additive Haar measure on `EuclN E`. -/
private instance modelHaar_map_toEuclidean_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure
      (Measure.map (toEuclidean : E ≃L[ℝ] EuclN E)
        (DifferentialGeometry.Integral.Measure.modelHaar (E := E))) :=
  ContinuousLinearEquiv.isAddHaarMeasure_map
    (toEuclidean : E ≃L[ℝ] EuclN E)
    (DifferentialGeometry.Integral.Measure.modelHaar (E := E))

/-- The Haar scaling constant: a positive `ℝ≥0` such that
`Measure.map toEuclidean modelHaar = c • volume` on Euclidean space. -/
private noncomputable def euclideanHaarFactor (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ℝ≥0 :=
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  MeasureTheory.Measure.addHaarScalarFactor
    (Measure.map (toEuclidean : E → EuclN E)
      (DifferentialGeometry.Integral.Measure.modelHaar (E := E)))
    (volume : Measure (EuclN E))

/-- The Haar scaling constant is positive. -/
private lemma euclideanHaarFactor_pos :
    0 < euclideanHaarFactor E :=
  MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

/-- The Haar scaling constant is nonzero (as `ℝ≥0`). -/
private lemma euclideanHaarFactor_ne_zero :
    euclideanHaarFactor E ≠ 0 :=
  ne_of_gt euclideanHaarFactor_pos

/-- The Haar scaling constant viewed as `ℝ≥0∞` is nonzero. -/
private lemma euclideanHaarFactor_ennreal_ne_zero :
    (euclideanHaarFactor E : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast euclideanHaarFactor_ne_zero

/-- The Haar scaling constant viewed as `ℝ≥0∞` is finite. -/
private lemma euclideanHaarFactor_ennreal_ne_top :
    (euclideanHaarFactor E : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top

/-- The pushforward equation: `Measure.map toEuclidean modelHaar = c_E • volume`
on Euclidean space, where `c_E = euclideanHaarFactor E`. -/
private lemma map_toEuclidean_modelHaar_eq_smul_volume :
    Measure.map (toEuclidean : E → EuclN E)
        (DifferentialGeometry.Integral.Measure.modelHaar (E := E)) =
      (euclideanHaarFactor E) • (volume : Measure (EuclN E)) := by
  classical
  exact MeasureTheory.Measure.isAddLeftInvariant_eq_smul _ _

/-! ## Lintegral identities tying `modelHaar` to `volume` on Euclidean side -/

/-- Auxiliary lintegral identity: pushing a `modelHaar`-integral on `E`
through `toEuclidean` to a `Measure.map toEuclidean modelHaar`-integral on
`EuclN E`. -/
private lemma lintegral_modelHaar_eq_lintegral_map_toEuclidean
    (G : E → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)) =
      ∫⁻ y, G ((toEuclidean (E := E)).symm y)
        ∂(Measure.map (toEuclidean : E → EuclN E)
          (DifferentialGeometry.Integral.Measure.modelHaar (E := E))) := by
  classical
  rw [MeasureTheory.lintegral_map
    (μ := DifferentialGeometry.Integral.Measure.modelHaar (E := E))
    (g := (toEuclidean : E → EuclN E))
    (f := fun y => G ((toEuclidean (E := E)).symm y))
    (hg := (toEuclidean (E := E)).continuous.measurable)
    (hf := hG.comp ((toEuclidean (E := E)).symm.continuous.measurable))]
  refine MeasureTheory.lintegral_congr (fun x => ?_)
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- Lintegral identity: pushing the integral on `E` to one on `EuclN E`
weighted by the Haar scaling constant times `volume`. -/
private lemma lintegral_modelHaar_eq_const_smul_lintegral_volume
    (G : E → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)) =
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y, G ((toEuclidean (E := E)).symm y)
          ∂(volume : Measure (EuclN E)) := by
  classical
  rw [lintegral_modelHaar_eq_lintegral_map_toEuclidean (E := E) G hG]
  rw [map_toEuclidean_modelHaar_eq_smul_volume (E := E)]
  rw [MeasureTheory.lintegral_smul_measure]
  rfl

/-! ## Globalised inverse chart helper -/

/-- Globalisation of `(extChartAt I α).symm`, agreeing with it on the chart
target and equal to a fixed default value off the target. The resulting function
is Borel measurable on all of `E`. The default value is `α` itself. -/
private noncomputable def extChartAtSymmGlob (α : M) : E → M := by
  classical
  exact (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α)

/-- The globalised inverse chart agrees with the inverse chart on the chart target. -/
private lemma extChartAtSymmGlob_eq_on_target (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    extChartAtSymmGlob (I := I) α y = (extChartAt I α).symm y := by
  classical
  change (extChartAt I α).target.piecewise
    (fun y : E => (extChartAt I α).symm y)
    (fun _ : E => α) y = _
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

/-- The globalised inverse chart is Borel measurable on all of `E`. -/
private lemma extChartAtSymmGlob_measurable (α : M) :
    Measurable (extChartAtSymmGlob (I := I) (M := M) α) := by
  classical
  unfold extChartAtSymmGlob
  exact ContinuousOn.measurable_piecewise
    (continuousOn_extChartAt_symm (I := I) α)
    continuousOn_const
    (extChartAt_target_measurableSet (I := I) (M := M) α)

/-! ## Bridge: chart-local lintegral expressed in chart-target Euclidean form -/

/-- The chart-local lintegral of any measurable `F : M → ℝ≥0∞` equals the
Euclidean integral over the chart target image weighted by the chart density,
times the Haar scaling factor. -/
lemma chartLocalMeasure_lintegral_via_chartTargetEuclid
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g α) =
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            F ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(volume : Measure (EuclN E)) := by
  classical
  rw [DifferentialGeometry.Integral.Measure.chartLocalMeasure_lintegral
    (I := I) (M := M) g α hF]
  -- Replace symm by symm_glob INSIDE target (pointwise equal there).
  set G_glob : E → ℝ≥0∞ := fun y =>
    ENNReal.ofReal
        (DifferentialGeometry.Integral.Measure.chartDensity g α
          (extChartAtSymmGlob (I := I) α y)) *
      F (extChartAtSymmGlob (I := I) α y)
  have hT : MeasurableSet (extChartAt I α).target :=
    extChartAt_target_measurableSet (I := I) (M := M) α
  have hG_glob_eq_on_target : ∀ y ∈ (extChartAt I α).target,
      G_glob y =
        ENNReal.ofReal
            (DifferentialGeometry.Integral.Measure.chartDensity g α
              ((extChartAt I α).symm y)) *
          F ((extChartAt I α).symm y) := by
    intro y hy
    change ENNReal.ofReal
        (DifferentialGeometry.Integral.Measure.chartDensity g α
          (extChartAtSymmGlob (I := I) α y)) *
      F (extChartAtSymmGlob (I := I) α y) = _
    rw [extChartAtSymmGlob_eq_on_target (I := I) (M := M) (α := α) hy]
  rw [show (∫⁻ y in (extChartAt I α).target,
        ENNReal.ofReal
            (DifferentialGeometry.Integral.Measure.chartDensity g α
              ((extChartAt I α).symm y)) *
          F ((extChartAt I α).symm y)
          ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E))) =
      ∫⁻ y in (extChartAt I α).target, G_glob y
        ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E))
      from MeasureTheory.setLIntegral_congr_fun hT
        (fun y hy => (hG_glob_eq_on_target y hy).symm)]
  -- G_glob is measurable on E.
  have hsymm_glob_meas : Measurable (extChartAtSymmGlob (I := I) (M := M) α) :=
    extChartAtSymmGlob_measurable (I := I) (M := M) α
  have hF_glob_meas : Measurable
      (fun y : E => F (extChartAtSymmGlob (I := I) α y)) := hF.comp hsymm_glob_meas
  have hdens_glob_meas : Measurable
      (fun y : E =>
        DifferentialGeometry.Integral.Measure.chartDensity g α
          (extChartAtSymmGlob (I := I) α y)) := by
    -- Reduce to a piecewise of: dens ∘ symm on target, constant α off target.
    have h_piecewise :
        (fun y : E =>
          DifferentialGeometry.Integral.Measure.chartDensity g α
            (extChartAtSymmGlob (I := I) α y)) =
        (extChartAt I α).target.piecewise
          (fun y : E =>
            DifferentialGeometry.Integral.Measure.chartDensity g α
              ((extChartAt I α).symm y))
          (fun _ : E =>
            DifferentialGeometry.Integral.Measure.chartDensity g α α) := by
      funext y
      by_cases hy : y ∈ (extChartAt I α).target
      · rw [Set.piecewise_eq_of_mem _ _ _ hy]
        rw [extChartAtSymmGlob_eq_on_target (I := I) (M := M) (α := α) hy]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hy]
        change DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).target.piecewise
            (fun y : E => (extChartAt I α).symm y)
            (fun _ : E => α) y) = _
        rw [Set.piecewise_eq_of_notMem _ _ _ hy]
    rw [h_piecewise]
    have hsymm_cont : ContinuousOn (extChartAt I α).symm
        (extChartAt I α).target := continuousOn_extChartAt_symm (I := I) α
    have hsubset : ∀ y ∈ (extChartAt I α).target,
        (extChartAt I α).symm y ∈ (chartAt H α).source := by
      intro y hy
      have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy
      rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hsource
    have h_orig_cont : ContinuousOn
        (fun y : E =>
          DifferentialGeometry.Integral.Measure.chartDensity g α
            ((extChartAt I α).symm y)) (extChartAt I α).target :=
      (DifferentialGeometry.Integral.Measure.chartDensity_continuousOn
        (I := I) (M := M) g α).comp hsymm_cont hsubset
    exact ContinuousOn.measurable_piecewise h_orig_cont continuousOn_const hT
  -- ofReal density ∘ symm_glob is Measurable.
  have hofReal_dens_meas : Measurable
      (fun y : E => ENNReal.ofReal
        (DifferentialGeometry.Integral.Measure.chartDensity g α
          (extChartAtSymmGlob (I := I) α y))) :=
    ENNReal.measurable_ofReal.comp hdens_glob_meas
  -- G_glob is Measurable.
  have hG_glob_meas : Measurable G_glob := by
    change Measurable (fun y => ENNReal.ofReal
        (DifferentialGeometry.Integral.Measure.chartDensity g α
          (extChartAtSymmGlob (I := I) α y)) *
      F (extChartAtSymmGlob (I := I) α y))
    exact hofReal_dens_meas.mul hF_glob_meas
  -- target.indicator G_glob is Measurable.
  have hG_glob_indic_meas : Measurable ((extChartAt I α).target.indicator G_glob) :=
    hG_glob_meas.indicator hT
  rw [← MeasureTheory.lintegral_indicator hT (f := G_glob)]
  rw [lintegral_modelHaar_eq_const_smul_lintegral_volume (E := E)
    (G := (extChartAt I α).target.indicator G_glob) hG_glob_indic_meas]
  congr 1
  rw [← MeasureTheory.lintegral_indicator
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)]
  refine MeasureTheory.lintegral_congr (fun y => ?_)
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    rw [Set.indicator_of_mem hy_target, Set.indicator_of_mem hy]
    change ENNReal.ofReal
        (DifferentialGeometry.Integral.Measure.chartDensity g α
          (extChartAtSymmGlob (I := I) α ((toEuclidean (E := E)).symm y))) *
      F (extChartAtSymmGlob (I := I) α ((toEuclidean (E := E)).symm y)) = _
    rw [extChartAtSymmGlob_eq_on_target (I := I) (M := M) (α := α) hy_target]
  · have hy_target : (toEuclidean (E := E)).symm y ∉ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    rw [Set.indicator_of_notMem hy_target, Set.indicator_of_notMem hy]

/-! ## Bound for the chart density on a compact subset of the chart target -/

/-- The chart density is strictly positive at points of the chart target. -/
lemma chartDensity_pos_on_target
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    0 < DifferentialGeometry.Integral.Measure.chartDensity g α
      ((extChartAt I α).symm y) := by
  apply DifferentialGeometry.Integral.Measure.chartDensity_pos
  rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
    (I := I) (M := M)]
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
    (I := I) (M := M)] at hsource

/-- Continuity of the chart density (composed with the chart inverse) on the chart target. -/
lemma chartDensity_symm_continuousOn_target
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn
      (fun y : E =>
        DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).symm y))
      (extChartAt I α).target := by
  refine (DifferentialGeometry.Integral.Measure.chartDensity_continuousOn
      (I := I) (M := M) g α).comp (continuousOn_extChartAt_symm (I := I) α) ?_
  intro y hy
  have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
    (I := I) (M := M)] at hsource

/-- Existence of a strict positive sup bound on a nonempty compact subset of the chart
target. -/
lemma exists_sup_chartDensity_on_compact_pos
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hKne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target) :
    ∃ M_sup : ℝ, 0 < M_sup ∧ ∀ y ∈ K,
      DifferentialGeometry.Integral.Measure.chartDensity g α
        ((extChartAt I α).symm y) ≤ M_sup := by
  classical
  have hdens_cont : ContinuousOn
      (fun y : E =>
        DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).symm y)) K :=
    (chartDensity_symm_continuousOn_target (I := I) (M := M) g α).mono hK_sub
  obtain ⟨y₀, hy₀_mem, hy₀_max⟩ :=
    hK_compact.exists_isMaxOn hKne hdens_cont
  refine ⟨DifferentialGeometry.Integral.Measure.chartDensity g α
    ((extChartAt I α).symm y₀),
    chartDensity_pos_on_target (I := I) (M := M) g α (hK_sub hy₀_mem),
    fun y hy => hy₀_max hy⟩

/-- Existence of a strict positive inf bound on a nonempty compact subset of the chart
target. -/
lemma exists_inf_chartDensity_on_compact
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hKne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target) :
    ∃ M_inf : ℝ, 0 < M_inf ∧ ∀ y ∈ K,
      M_inf ≤ DifferentialGeometry.Integral.Measure.chartDensity g α
        ((extChartAt I α).symm y) := by
  classical
  have hdens_cont : ContinuousOn
      (fun y : E =>
        DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).symm y)) K :=
    (chartDensity_symm_continuousOn_target (I := I) (M := M) g α).mono hK_sub
  obtain ⟨y₀, hy₀_mem, hy₀_min⟩ :=
    hK_compact.exists_isMinOn hKne hdens_cont
  refine ⟨DifferentialGeometry.Integral.Measure.chartDensity g α
    ((extChartAt I α).symm y₀),
    chartDensity_pos_on_target (I := I) (M := M) g α (hK_sub hy₀_mem),
    fun y hy => hy₀_min hy⟩

/-! ## Compact image of `tsupport u` in the chart target -/

/-- If `tsupport u ⊆ chartAt α source`, then `(extChartAt I α) '' (tsupport u)`
is compact in `E` and contained in the chart target. -/
lemma image_extChartAt_tsupport_compact_subset_target
    [CompactSpace M] {u : M → ℝ} {α : M}
    (hu_supp : tsupport u ⊆ (chartAt H α).source) :
    IsCompact ((extChartAt I α) '' (tsupport u)) ∧
      (extChartAt I α) '' (tsupport u) ⊆ (extChartAt I α).target := by
  refine ⟨?_, ?_⟩
  · have hsub : tsupport u ⊆ (extChartAt I α).source := by
      intro x hx
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hu_supp hx
    have hcont : ContinuousOn (extChartAt I α) (tsupport u) :=
      (continuousOn_extChartAt α).mono hsub
    exact ((isClosed_tsupport _).isCompact).image_of_continuousOn hcont
  · rintro y ⟨x, hx, rfl⟩
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hu_supp hx
    exact (extChartAt I α).map_source hxsrc

/-- The toEuclidean image of `(extChartAt I α) '' (tsupport u)` is compact in `EuclN E`. -/
lemma image_toEuclidean_extChartAt_tsupport_compact
    [CompactSpace M] {u : M → ℝ} {α : M}
    (hu_supp : tsupport u ⊆ (chartAt H α).source) :
    IsCompact (toEuclidean ''
      ((extChartAt I α) '' (tsupport (u : M → ℝ)))) :=
  ((image_extChartAt_tsupport_compact_subset_target (I := I) (M := M)
    (u := u) (α := α) hu_supp).1).image (toEuclidean (E := E)).continuous

/-- The toEuclidean image of `(extChartAt I α) '' (tsupport u)` is contained in
`chartTargetEuclid α`. -/
lemma image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
    {u : M → ℝ} {α : M}
    (hu_supp : tsupport u ⊆ (chartAt H α).source) :
    toEuclidean ''
      ((extChartAt I α) '' (tsupport (u : M → ℝ))) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  rintro y ⟨z, hz, rfl⟩
  rcases hz with ⟨x, hx, hxz⟩
  refine ⟨z, ?_, rfl⟩
  rw [← hxz]
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I) (M := M)]
    exact hu_supp hx
  exact (extChartAt I α).map_source hxsrc

/-! ## Chart-pushed raw vanishes outside the toEuclidean image of `(extChartAt I α) '' tsupport u` -/

/-- The raw chart pushforward vanishes (within the chart target) outside
`toEuclidean '' ((extChartAt I α) '' (tsupport u))`. -/
lemma chartPushedRaw_eq_zero_off_image_tsupport
    {u : M → ℝ} (α : M)
    {y : EuclN E} (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off : y ∉ toEuclidean '' ((extChartAt I α) '' (tsupport u))) :
    chartPushedRaw I α u y = 0 := by
  classical
  obtain ⟨z, hz_target, hzy⟩ := hy_target
  have hsymm_source : (extChartAt I α).symm z ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hz_target
  have hz_eq : (extChartAt I α) ((extChartAt I α).symm z) = z :=
    (extChartAt I α).right_inv hz_target
  have hy_symm : (toEuclidean (E := E)).symm y = z := by
    rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
  have hy_target' : y ∈ chartTargetEuclid (I := I) (M := M) α := ⟨z, hz_target, hzy⟩
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hy_target']
  rw [hy_symm]
  by_contra hu_ne
  apply hy_off
  refine ⟨z, ⟨(extChartAt I α).symm z, ?_, hz_eq⟩, hzy⟩
  exact subset_tsupport _ (Function.mem_support.mpr hu_ne)

/-! ## Chart-source-supported `u`: passage from `riemannianMeasure` to chart-local -/

/-- For `u` supported in `chartAt α source`, the lintegral of `‖u‖ₑ ^ p`
under `riemannianMeasure g (chartAtlasPOU I M)` agrees with the lintegral
under `chartLocalMeasure g α`. -/
lemma lintegral_enorm_pow_riemannianMeasure_eq_chartLocalMeasure_of_supportIn
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu_supp : tsupport u ⊆ (chartAt H α).source)
    {p : ℝ} (hp_pos : 0 < p) :
    ∫⁻ x, ‖u x‖ₑ ^ p
        ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) =
      ∫⁻ x, ‖u x‖ₑ ^ p
        ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g α) := by
  classical
  apply riemannianMeasure_lintegral_eq_chartLocalMeasure_of_supportIn (I := I) (M := M) g α
  · exact (hu_meas.enorm).pow_const p
  · intro x hx
    have hx_notsupp : x ∉ tsupport u := fun hcontra => hx (hu_supp hcontra)
    have hu_x_zero : u x = 0 := image_eq_zero_of_notMem_tsupport hx_notsupp
    rw [hu_x_zero]
    rw [enorm_zero, ENNReal.zero_rpow_of_pos hp_pos]

/-! ## Bridge identity for the lintegral of `‖u‖ₑ ^ p` -/

/-- Combined bridge identity: for `u : M → ℝ` supported in `chartAt α source`
on a closed manifold, the lintegral of `‖u‖ₑ ^ p` against the Riemannian
measure equals the Euclidean integral of `density · ‖chartPushedRaw u‖ₑ ^ p`
over `chartTargetEuclid α`, with the Haar scaling factor. -/
lemma lintegral_enorm_pow_riemannianMeasure_eq_const_mul_chartTargetEuclid
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu_supp : tsupport u ⊆ (chartAt H α).source)
    {p : ℝ} (hp_pos : 0 < p) :
    ∫⁻ x, ‖u x‖ₑ ^ p
        ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) =
      (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E)) := by
  classical
  rw [lintegral_enorm_pow_riemannianMeasure_eq_chartLocalMeasure_of_supportIn
      (I := I) (M := M) g α hu_meas hu_supp hp_pos]
  rw [chartLocalMeasure_lintegral_via_chartTargetEuclid (I := I) (M := M) g α
    (F := fun x => ‖u x‖ₑ ^ p) ((hu_meas.enorm).pow_const p)]
  congr 1
  refine MeasureTheory.setLIntegral_congr_fun
    (chartTargetEuclid_measurableSet (I := I) (M := M) α) ?_
  intro y hy
  change ENNReal.ofReal _ * ‖u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ^ p =
    ENNReal.ofReal _ * ‖chartPushedRaw I α u y‖ₑ ^ p
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hy]

/-! ## Forward bound: lintegral over `μ_g` ≤ const · lintegral over volume -/

/-- Forward bridge inequality at the level of lintegrals:
`∫⁻ ‖u‖ₑ^p dμ_g ≤ const · ∫⁻ ‖chartPushedRaw u‖ₑ^p dvolume`. -/
theorem lintegral_riemannianMeasure_le_const_mul_lintegral_chartPushedRaw
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu_supp : tsupport u ⊆ (chartAt H α).source)
    {p : ℝ} (hp_pos : 0 < p) :
    ∃ C_α : ℝ, 0 < C_α ∧
      ∫⁻ x, ‖u x‖ₑ ^ p
          ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C_α *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ‖chartPushedRaw I α u y‖ₑ ^ p
              ∂(volume : Measure (EuclN E)) := by
  classical
  by_cases hu_zero_supp : (tsupport u).Nonempty
  · -- Nonempty support: standard argument.
    set K : Set E := (extChartAt I α) '' (tsupport u)
    have hK_decomp :=
      image_extChartAt_tsupport_compact_subset_target
        (I := I) (M := M) (u := u) (α := α) hu_supp
    obtain ⟨hK_compact, hK_sub_target⟩ := hK_decomp
    have hK_ne : K.Nonempty := hu_zero_supp.image _
    obtain ⟨M_sup, hM_sup_pos, hM_sup_le⟩ :=
      exists_sup_chartDensity_on_compact_pos (I := I) (M := M) g α hK_compact
        hK_ne hK_sub_target
    set C_α : ℝ := (euclideanHaarFactor E : ℝ) * M_sup with hC_α_def
    have hC_pos : 0 < C_α := by
      apply mul_pos
      · exact_mod_cast euclideanHaarFactor_pos
      · exact hM_sup_pos
    refine ⟨C_α, hC_pos, ?_⟩
    rw [lintegral_enorm_pow_riemannianMeasure_eq_const_mul_chartTargetEuclid
        (I := I) (M := M) g α hu_meas hu_supp hp_pos]
    set K_eucl : Set (EuclN E) := toEuclidean '' K with hK_eucl_def
    have hpt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
            (DifferentialGeometry.Integral.Measure.chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖chartPushedRaw I α u y‖ₑ ^ p
        ≤ ENNReal.ofReal M_sup * ‖chartPushedRaw I α u y‖ₑ ^ p := by
      intro y hy_target
      by_cases hy_K : y ∈ K_eucl
      · obtain ⟨x, hx_K, hxy⟩ := hy_K
        have hx_target : x ∈ (extChartAt I α).target := hK_sub_target hx_K
        have hsym_eq : (toEuclidean (E := E)).symm y = x := by
          rw [← hxy]; exact (toEuclidean (E := E)).symm_apply_apply x
        have hbound :
            DifferentialGeometry.Integral.Measure.chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
              ≤ M_sup := by
          rw [hsym_eq]; exact hM_sup_le x hx_K
        have h_density_le :
            ENNReal.ofReal
                (DifferentialGeometry.Integral.Measure.chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
              ≤ ENNReal.ofReal M_sup :=
          ENNReal.ofReal_le_ofReal hbound
        gcongr
      · have hpr_zero : chartPushedRaw I α u y = 0 :=
          chartPushedRaw_eq_zero_off_image_tsupport
            (I := I) (M := M) (u := u) α hy_target hy_K
        rw [hpr_zero, enorm_zero, ENNReal.zero_rpow_of_pos hp_pos]
        simp
    calc (euclideanHaarFactor E : ℝ≥0∞) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (DifferentialGeometry.Integral.Measure.chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E))
        ≤ (euclideanHaarFactor E : ℝ≥0∞) *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal M_sup * ‖chartPushedRaw I α u y‖ₑ ^ p
              ∂(volume : Measure (EuclN E)) := by
          have h_int_le : (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                    (DifferentialGeometry.Integral.Measure.chartDensity g α
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  ‖chartPushedRaw I α u y‖ₑ ^ p
                ∂(volume : Measure (EuclN E)))
              ≤ (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal M_sup * ‖chartPushedRaw I α u y‖ₑ ^ p
                ∂(volume : Measure (EuclN E))) :=
            MeasureTheory.setLIntegral_mono_ae'
              (chartTargetEuclid_measurableSet (I := I) (M := M) α)
              (Filter.Eventually.of_forall hpt)
          gcongr
      _ = (euclideanHaarFactor E : ℝ≥0∞) * ENNReal.ofReal M_sup *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ‖chartPushedRaw I α u y‖ₑ ^ p
              ∂(volume : Measure (EuclN E)) := by
          rw [MeasureTheory.lintegral_const_mul']
          · ring
          · exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C_α *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ‖chartPushedRaw I α u y‖ₑ ^ p
              ∂(volume : Measure (EuclN E)) := by
          congr 1
          rw [hC_α_def]
          rw [ENNReal.ofReal_mul]
          · congr 1
            rw [ENNReal.ofReal_coe_nnreal]
          · exact NNReal.coe_nonneg _
  · -- Empty support: u = 0 ⇒ LHS = 0 ≤ RHS.
    rw [Set.not_nonempty_iff_eq_empty] at hu_zero_supp
    have hu_zero : u = 0 := by
      funext x
      have hx_notsupp : x ∉ tsupport u := by rw [hu_zero_supp]; simp
      exact image_eq_zero_of_notMem_tsupport hx_notsupp
    refine ⟨1, one_pos, ?_⟩
    rw [hu_zero]
    -- The LHS is `∫⁻ x, (‖0‖ₑ : ℝ≥0∞) ^ p dμ_g = ∫⁻ x, 0 dμ_g = 0` since p > 0.
    have h_pt : (‖(0 : ℝ)‖ₑ : ℝ≥0∞) ^ p = 0 := by
      rw [enorm_zero, ENNReal.zero_rpow_of_pos hp_pos]
    have hLHS_zero : (∫⁻ _ : M, (‖(0 : ℝ)‖ₑ : ℝ≥0∞) ^ p
        ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))) = 0 := by
      rw [h_pt]
      simp [MeasureTheory.lintegral_const]
    change ∫⁻ x, (‖(0 : M → ℝ) x‖ₑ : ℝ≥0∞) ^ p
        ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
      ≤ _
    rw [show (fun x : M => (‖(0 : M → ℝ) x‖ₑ : ℝ≥0∞) ^ p) =
        fun _ => (‖(0 : ℝ)‖ₑ : ℝ≥0∞) ^ p by funext x; rfl, hLHS_zero]
    exact zero_le _

/-! ## eLpNorm versions of the bridge -/

/-- Bridge inequality at the level of `eLpNorm`s, using the raw chart pushforward
on the Euclidean side. For `1 ≤ p`, `p ≠ ∞`, and a `u : M → ℝ` supported in the
chart-α source on a closed manifold, we have

`eLpNorm u p μ_g ≤ ENNReal.ofReal C_α^{1/p} · eLpNorm chartPushedRaw u p volume`

where `C_α` depends on the chart and the metric only. -/
theorem eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu_supp : tsupport u ⊆ (chartAt H α).source) :
    ∃ C_α : ℝ, 0 < C_α ∧
      eLpNorm u p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C_α *
            eLpNorm (chartPushedRaw I α u) p
              ((volume : Measure (EuclN E)).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_one; exact absurd hp_one (by norm_num)
  -- p.toReal > 0.
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  -- Apply the lintegral-level bound.
  obtain ⟨C, hC_pos, hbnd⟩ :=
    lintegral_riemannianMeasure_le_const_mul_lintegral_chartPushedRaw
      (I := I) (M := M) g α hu_meas hu_supp hp_toReal_pos
  -- Convert to eLpNorm form by raising to 1/p.toReal.
  -- eLpNorm f p μ = (∫⁻ ‖f‖ₑ^p.toReal dμ)^(1/p.toReal).
  -- LHS_eLpNorm = (LHS_lint)^(1/p.toReal).
  -- RHS_eLpNorm = (RHS_lint)^(1/p.toReal).
  -- Bound: LHS_lint ≤ (ENNReal.ofReal C) · RHS_lint.
  -- Hence LHS_eLpNorm ≤ ((ENNReal.ofReal C)^(1/p.toReal) · RHS_eLpNorm).
  -- Set C' := C^(1/p.toReal).
  refine ⟨C ^ (1 / p.toReal), Real.rpow_pos_of_pos hC_pos _, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
  -- Want: (∫⁻ ‖u‖ₑ^p.toReal dμ_g)^(1/p.toReal) ≤
  --   ENNReal.ofReal (C^(1/p.toReal)) · eLpNorm chartPushedRaw u p (vol.restrict ...).
  -- Step 1: apply the lintegral bound, then take p.toReal-th root.
  have h_lint_bound :
      ∫⁻ x, ‖u x‖ₑ ^ p.toReal
          ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
              ∂(volume : Measure (EuclN E)) := hbnd
  -- Convert RHS lintegral over chartTargetEuclid to lintegral over volume.restrict.
  have h_RHS_eq :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
        ∂(volume : Measure (EuclN E))) =
      ∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
        ∂((volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := rfl
  rw [h_RHS_eq] at h_lint_bound
  -- Now: (LHS_lint)^(1/p.toReal) ≤ (RHS_lint)^(1/p.toReal),
  -- where RHS_lint = ENNReal.ofReal C * something.
  have h_pow_le :
      (∫⁻ x, ‖u x‖ₑ ^ p.toReal
          ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))) ^
            (1 / p.toReal)
        ≤ (ENNReal.ofReal C *
            ∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
              ∂((volume : Measure (EuclN E)).restrict
                (chartTargetEuclid (I := I) (M := M) α))) ^
              (1 / p.toReal) := by
    apply ENNReal.rpow_le_rpow h_lint_bound
    positivity
  refine h_pow_le.trans ?_
  -- (a · b)^r = a^r · b^r in ENNReal (for r ≥ 0).
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.toReal)]
  -- Goal: ENNReal.ofReal C ^ (1/p.toReal) * (∫⁻...)^(1/p.toReal)
  --     ≤ ENNReal.ofReal (C^(1/p.toReal)) * eLpNorm.
  -- Recognize the RHS lintegral^(1/p.toReal) as eLpNorm.
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
  -- Now (a*b ≤ a'*b'), suffices a ≤ a' (and b = b').
  gcongr
  -- Goal: ENNReal.ofReal C ^ (1/p.toReal) ≤ ENNReal.ofReal (C^(1/p.toReal)).
  -- Use ENNReal.ofReal_rpow_of_pos.
  rw [← ENNReal.ofReal_rpow_of_pos hC_pos]

/-! ## Reverse direction: lintegral over volume ≤ const · lintegral over μ_g -/

/-- Reverse bridge inequality at the level of lintegrals:
`∫⁻ ‖chartPushedRaw u‖ₑ^p dvolume ≤ const · ∫⁻ ‖u‖ₑ^p dμ_g`. -/
theorem lintegral_chartPushedRaw_le_const_mul_lintegral_riemannianMeasure
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu_supp : tsupport u ⊆ (chartAt H α).source)
    {p : ℝ} (hp_pos : 0 < p) :
    ∃ C_α : ℝ, 0 < C_α ∧
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E))
        ≤ ENNReal.ofReal C_α *
            ∫⁻ x, ‖u x‖ₑ ^ p
              ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
  classical
  by_cases hu_zero_supp : (tsupport u).Nonempty
  · -- Nonempty support: standard argument.
    set K : Set E := (extChartAt I α) '' (tsupport u)
    have hK_decomp :=
      image_extChartAt_tsupport_compact_subset_target
        (I := I) (M := M) (u := u) (α := α) hu_supp
    obtain ⟨hK_compact, hK_sub_target⟩ := hK_decomp
    have hK_ne : K.Nonempty := hu_zero_supp.image _
    obtain ⟨M_inf, hM_inf_pos, hM_inf_le⟩ :=
      exists_inf_chartDensity_on_compact (I := I) (M := M) g α hK_compact
        hK_ne hK_sub_target
    set C_α : ℝ := ((euclideanHaarFactor E : ℝ) * M_inf)⁻¹ with hC_α_def
    have hC_pos : 0 < C_α := by
      rw [hC_α_def]
      apply inv_pos.mpr
      apply mul_pos
      · exact_mod_cast euclideanHaarFactor_pos
      · exact hM_inf_pos
    refine ⟨C_α, hC_pos, ?_⟩
    rw [lintegral_enorm_pow_riemannianMeasure_eq_const_mul_chartTargetEuclid
        (I := I) (M := M) g α hu_meas hu_supp hp_pos]
    -- Need: ∫⁻ ‖chartPushedRaw u‖^p dvol
    --   ≤ ENNReal.ofReal C * (haarFactor · ∫⁻ density · ‖chartPushedRaw u‖^p dvol).
    -- = (haarFactor · M_inf)⁻¹ · (haarFactor · ∫⁻ density · ‖chartPushedRaw u‖^p dvol)
    -- = (haarFactor · M_inf)⁻¹ · haarFactor · ∫⁻ density · ‖chartPushedRaw u‖^p dvol.
    -- Want this ≥ ∫⁻ ‖chartPushedRaw u‖^p dvol on the chartTarget.
    -- Since ∫⁻ density · ‖chartPushedRaw u‖^p dvol ≥ M_inf · ∫⁻ ‖chartPushedRaw u‖^p dvol on supp(chartPushedRaw u),
    -- and chartPushedRaw u vanishes outside K_eucl ⊆ chartTarget, we have
    -- ∫⁻ density · ‖chartPushedRaw u‖^p dvol = ∫⁻_{K_eucl} density · ‖chartPushedRaw u‖^p dvol
    --   ≥ M_inf · ∫⁻_{K_eucl} ‖chartPushedRaw u‖^p dvol = M_inf · ∫⁻ ‖chartPushedRaw u‖^p dvol on chartTarget.
    set K_eucl : Set (EuclN E) := toEuclidean '' K with hK_eucl_def
    -- Pointwise bound on chartTargetEuclid:
    -- ‖chartPushedRaw u y‖^p
    --   ≤ density(...)/M_inf · ‖chartPushedRaw u y‖^p (when chartPushedRaw u y ≠ 0, i.e. y ∈ K_eucl).
    --   = 0 (when chartPushedRaw u y = 0).
    have hpt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal (M_inf) * ‖chartPushedRaw I α u y‖ₑ ^ p
          ≤ ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖chartPushedRaw I α u y‖ₑ ^ p := by
      intro y hy_target
      by_cases hy_K : y ∈ K_eucl
      · obtain ⟨x, hx_K, hxy⟩ := hy_K
        have hx_target : x ∈ (extChartAt I α).target := hK_sub_target hx_K
        have hsym_eq : (toEuclidean (E := E)).symm y = x := by
          rw [← hxy]; exact (toEuclidean (E := E)).symm_apply_apply x
        have hbound :
            M_inf ≤
            DifferentialGeometry.Integral.Measure.chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
          rw [hsym_eq]; exact hM_inf_le x hx_K
        have h_density_ge :
            ENNReal.ofReal M_inf
              ≤ ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :=
          ENNReal.ofReal_le_ofReal hbound
        gcongr
      · -- y ∉ K_eucl: chartPushedRaw u y = 0.
        have hpr_zero : chartPushedRaw I α u y = 0 :=
          chartPushedRaw_eq_zero_off_image_tsupport
            (I := I) (M := M) (u := u) α hy_target hy_K
        rw [hpr_zero, enorm_zero, ENNReal.zero_rpow_of_pos hp_pos]
        simp
    -- Multiply both sides through; LHS over chartTargetEuclid.
    have h_int_le : (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal M_inf * ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E)))
        ≤ (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E))) :=
      MeasureTheory.setLIntegral_mono_ae'
        (chartTargetEuclid_measurableSet (I := I) (M := M) α)
        (Filter.Eventually.of_forall hpt)
    -- Pull the constant ENNReal.ofReal M_inf out of the LHS.
    have h_LHS_eq : (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal M_inf * ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E))) =
        ENNReal.ofReal M_inf *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
      rw [MeasureTheory.lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    rw [h_LHS_eq] at h_int_le
    -- Now: ofReal M_inf * lhs_int ≤ rhs_int (which has the density factor).
    -- Hence: lhs_int ≤ (ofReal M_inf)⁻¹ · rhs_int.
    -- Multiply by haarFactor: rhs of theorem.
    have hM_inf_ennreal_pos : (ENNReal.ofReal M_inf : ℝ≥0∞) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hM_inf_pos
    have hM_inf_ennreal_ne_top : (ENNReal.ofReal M_inf : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    -- Key combined product: D := haarFactor * ENNReal.ofReal M_inf.
    set D : ℝ≥0∞ := (euclideanHaarFactor E : ℝ≥0∞) * ENNReal.ofReal M_inf with hD_def
    have hD_pos : D ≠ 0 := mul_ne_zero euclideanHaarFactor_ennreal_ne_zero
      hM_inf_ennreal_pos
    have hD_ne_top : D ≠ ⊤ := ENNReal.mul_ne_top
      euclideanHaarFactor_ennreal_ne_top hM_inf_ennreal_ne_top
    -- Step: h_int_le gives ofReal M_inf · LHS ≤ RHS_dens. Multiply by haarFactor:
    --   D · LHS ≤ haarFactor · RHS_dens.
    -- Hence LHS · D ≤ haarFactor · RHS_dens, so LHS ≤ D⁻¹ · (haarFactor · RHS_dens).
    -- ENNReal.ofReal C_α = D⁻¹ (since C_α = (haarFactor · M_inf)⁻¹).
    have hC_eq_D_inv : ENNReal.ofReal C_α = D⁻¹ := by
      rw [hC_α_def, hD_def]
      have h_prod_pos : 0 < (euclideanHaarFactor E : ℝ) * M_inf := by
        apply mul_pos
        · exact_mod_cast euclideanHaarFactor_pos
        · exact hM_inf_pos
      rw [show ((euclideanHaarFactor E : ℝ) * M_inf)⁻¹ =
            (1 : ℝ) / ((euclideanHaarFactor E : ℝ) * M_inf) from by rw [one_div]]
      rw [ENNReal.ofReal_div_of_pos h_prod_pos]
      rw [ENNReal.ofReal_one]
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
      rw [ENNReal.ofReal_coe_nnreal]
      rw [one_div]
    rw [hC_eq_D_inv]
    -- Goal: LHS_int ≤ D⁻¹ · (haarFactor · RHS_dens).
    -- We have: ofReal M_inf · LHS_int ≤ RHS_dens (= h_int_le).
    -- Multiply by haarFactor to get D · LHS_int ≤ haarFactor · RHS_dens.
    have h_step : D * (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ‖chartPushedRaw I α u y‖ₑ ^ p ∂(volume : Measure (EuclN E)))
        ≤ (euclideanHaarFactor E : ℝ≥0∞) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (DifferentialGeometry.Integral.Measure.chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
      rw [hD_def, mul_assoc]
      gcongr
    -- Convert: D · LHS ≤ X ⟺ LHS ≤ D⁻¹ · X (using ENNReal.le_inv_mul_iff_mul_le for D ≠ 0, ⊤).
    rwa [ENNReal.mul_le_iff_le_inv hD_pos hD_ne_top] at h_step
  · -- Empty support: u = 0 ⇒ both sides are 0.
    rw [Set.not_nonempty_iff_eq_empty] at hu_zero_supp
    have hu_zero : u = 0 := by
      funext x
      have hx_notsupp : x ∉ tsupport u := by rw [hu_zero_supp]; simp
      exact image_eq_zero_of_notMem_tsupport hx_notsupp
    refine ⟨1, one_pos, ?_⟩
    rw [hu_zero]
    -- chartPushedRaw I α 0 y = 0 for all y; so LHS = 0.
    have hLHS_zero : (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ‖chartPushedRaw I α (0 : M → ℝ) y‖ₑ ^ p ∂(volume : Measure (EuclN E))) = 0 := by
      have hcp_zero : ∀ y, chartPushedRaw I α (0 : M → ℝ) y = 0 := by
        intro y
        by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
        · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α (0 : M → ℝ) hy]; rfl
        · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α (0 : M → ℝ) hy]
      have hpw : ∀ y : EuclN E, ‖chartPushedRaw I α (0 : M → ℝ) y‖ₑ ^ p = 0 := by
        intro y
        rw [hcp_zero y, enorm_zero, ENNReal.zero_rpow_of_pos hp_pos]
      simp_rw [hpw]
      simp [MeasureTheory.lintegral_const]
    rw [hLHS_zero]
    exact zero_le _

/-- Reverse bridge inequality at the level of `eLpNorm`s. -/
theorem eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu_supp : tsupport u ⊆ (chartAt H α).source) :
    ∃ C_α : ℝ, 0 < C_α ∧
      eLpNorm (chartPushedRaw I α u) p
          ((volume : Measure (EuclN E)).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C_α *
            eLpNorm u p
              (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_one; exact absurd hp_one (by norm_num)
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  obtain ⟨C, hC_pos, hbnd⟩ :=
    lintegral_chartPushedRaw_le_const_mul_lintegral_riemannianMeasure
      (I := I) (M := M) g α hu_meas hu_supp hp_toReal_pos
  refine ⟨C ^ (1 / p.toReal), Real.rpow_pos_of_pos hC_pos _, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
  have h_LHS_eq :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
        ∂(volume : Measure (EuclN E))) =
      ∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
        ∂((volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := rfl
  rw [h_LHS_eq] at hbnd
  have h_pow_le :
      (∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
          ∂((volume : Measure (EuclN E)).restrict
            (chartTargetEuclid (I := I) (M := M) α))) ^
            (1 / p.toReal)
        ≤ (ENNReal.ofReal C *
            ∫⁻ x, ‖u x‖ₑ ^ p.toReal
              ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))) ^
              (1 / p.toReal) := by
    apply ENNReal.rpow_le_rpow hbnd
    positivity
  refine h_pow_le.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.toReal)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
  gcongr
  rw [← ENNReal.ofReal_rpow_of_pos hC_pos]

/-! ## Forward bridge with a uniform constant determined by a fixed compact set -/

/-- Forward bridge inequality with a uniform constant. The constant `C_K`
depends only on a fixed compact set `K ⊆ (extChartAt I α).target`, not on the
particular function `u`. As long as `(extChartAt I α) '' (tsupport u) ⊆ K`,
the bound holds with this fixed constant. -/
theorem lintegral_riemannianMeasure_le_const_mul_lintegral_chartPushedRaw_uniform
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hK_ne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ (chartAt H α).source →
      (extChartAt I α) '' (tsupport u) ⊆ K →
      ∀ {p : ℝ}, 0 < p →
      ∫⁻ x, ‖u x‖ₑ ^ p
          ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C_K *
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ‖chartPushedRaw I α u y‖ₑ ^ p
              ∂(volume : Measure (EuclN E)) := by
  classical
  obtain ⟨M_sup, hM_sup_pos, hM_sup_le⟩ :=
    exists_sup_chartDensity_on_compact_pos (I := I) (M := M) g α hK_compact hK_ne hK_sub
  set C_K : ℝ := (euclideanHaarFactor E : ℝ) * M_sup with hC_K_def
  have hC_K_pos : 0 < C_K := by
    apply mul_pos
    · exact_mod_cast euclideanHaarFactor_pos
    · exact hM_sup_pos
  refine ⟨C_K, hC_K_pos, ?_⟩
  intro u hu_meas hu_supp hu_supp_K p hp_pos
  -- The proof mirrors the per-u version, but using the K-uniform M_sup bound.
  rw [lintegral_enorm_pow_riemannianMeasure_eq_const_mul_chartTargetEuclid
      (I := I) (M := M) g α hu_meas hu_supp hp_pos]
  set K_eucl : Set (EuclN E) :=
    (toEuclidean : E ≃L[ℝ] EuclN E) '' ((extChartAt I α) '' (tsupport u))
    with hK_eucl_def
  have hpt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal
          (DifferentialGeometry.Integral.Measure.chartDensity g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        ‖chartPushedRaw I α u y‖ₑ ^ p
      ≤ ENNReal.ofReal M_sup * ‖chartPushedRaw I α u y‖ₑ ^ p := by
    intro y hy_target
    by_cases hy_K_eucl : y ∈ K_eucl
    · obtain ⟨z_E, hz_E_chart, hz_Ey⟩ := hy_K_eucl
      have hz_in_K : z_E ∈ K := hu_supp_K hz_E_chart
      have hz_target : z_E ∈ (extChartAt I α).target := hK_sub hz_in_K
      have hsym_eq : (toEuclidean (E := E)).symm y = z_E := by
        rw [← hz_Ey]; exact (toEuclidean (E := E)).symm_apply_apply z_E
      have hbound :
          DifferentialGeometry.Integral.Measure.chartDensity g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
            ≤ M_sup := by
        rw [hsym_eq]; exact hM_sup_le z_E hz_in_K
      have h_density_le :
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
            ≤ ENNReal.ofReal M_sup :=
        ENNReal.ofReal_le_ofReal hbound
      gcongr
    · -- y ∉ K_eucl: chartPushedRaw u y = 0.
      have hpr_zero : chartPushedRaw I α u y = 0 :=
        chartPushedRaw_eq_zero_off_image_tsupport
          (I := I) (M := M) (u := u) α hy_target hy_K_eucl
      rw [hpr_zero, enorm_zero, ENNReal.zero_rpow_of_pos hp_pos]
      simp
  calc (euclideanHaarFactor E : ℝ≥0∞) *
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
              (DifferentialGeometry.Integral.Measure.chartDensity g α
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E))
      ≤ (euclideanHaarFactor E : ℝ≥0∞) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal M_sup * ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
        have h_int_le : (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                  (DifferentialGeometry.Integral.Measure.chartDensity g α
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                ‖chartPushedRaw I α u y‖ₑ ^ p
              ∂(volume : Measure (EuclN E)))
            ≤ (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal M_sup * ‖chartPushedRaw I α u y‖ₑ ^ p
              ∂(volume : Measure (EuclN E))) :=
          MeasureTheory.setLIntegral_mono_ae'
            (chartTargetEuclid_measurableSet (I := I) (M := M) α)
            (Filter.Eventually.of_forall hpt)
        gcongr
    _ = (euclideanHaarFactor E : ℝ≥0∞) * ENNReal.ofReal M_sup *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
        rw [MeasureTheory.lintegral_const_mul']
        · ring
        · exact ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal C_K *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
        congr 1
        rw [hC_K_def]
        rw [ENNReal.ofReal_mul]
        · congr 1
          rw [ENNReal.ofReal_coe_nnreal]
        · exact NNReal.coe_nonneg _

/-- Forward bridge inequality at the level of `eLpNorm`s with a uniform constant. -/
theorem eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hK_ne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ (chartAt H α).source →
      (extChartAt I α) '' (tsupport u) ⊆ K →
      eLpNorm u p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C_K *
            eLpNorm (chartPushedRaw I α u) p
              ((volume : Measure (EuclN E)).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_one; exact absurd hp_one (by norm_num)
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  obtain ⟨C, hC_pos, hC_bnd⟩ :=
    lintegral_riemannianMeasure_le_const_mul_lintegral_chartPushedRaw_uniform
      (I := I) (M := M) g α hK_compact hK_ne hK_sub
  refine ⟨C ^ (1 / p.toReal), Real.rpow_pos_of_pos hC_pos _, ?_⟩
  intro u hu_meas hu_supp hu_K
  have h_lint := hC_bnd hu_meas hu_supp hu_K hp_toReal_pos
  -- Convert RHS lintegral over chartTargetEuclid α to one over (volume.restrict ...).
  -- These are definitionally equal.
  have h_lint' :
      ∫⁻ x, ‖u x‖ₑ ^ p.toReal
          ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C *
            ∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
              ∂((volume : Measure (EuclN E)).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := h_lint
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
  have h_pow_le :
      (∫⁻ x, ‖u x‖ₑ ^ p.toReal
          ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))) ^
            (1 / p.toReal)
        ≤ (ENNReal.ofReal C *
            ∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
              ∂((volume : Measure (EuclN E)).restrict
                (chartTargetEuclid (I := I) (M := M) α))) ^
              (1 / p.toReal) := by
    apply ENNReal.rpow_le_rpow h_lint'
    positivity
  refine h_pow_le.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.toReal)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
  gcongr
  rw [← ENNReal.ofReal_rpow_of_pos hC_pos]

end Chart
end Sobolev
end Analysis
end DifferentialGeometry

/-! ## Reverse bridge with a uniform constant determined by a fixed compact subset of `(extChartAt I α).target`

We add the K-uniform reverse-direction lintegral and `eLpNorm` inequalities,
mirroring the existing forward K-uniform bridge. The constant depends only on
the compact set `K ⊆ (extChartAt I α).target`, the chart `α`, and the metric
`g`, and is uniform in `u : M → ℝ` whose chart-image of `tsupport u` lies in `K`. -/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Reverse bridge inequality at the level of lintegrals with a uniform
constant on the Euclidean side.  The constant `C_K` depends only on a fixed
compact set `K ⊆ (extChartAt I α).target`, not on the particular function `u`.
As long as `(extChartAt I α) '' (tsupport u) ⊆ K`, the bound holds with this
fixed constant. -/
theorem lintegral_chartPushedRaw_le_const_mul_lintegral_riemannianMeasure_uniform
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hK_ne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ (chartAt H α).source →
      (extChartAt I α) '' (tsupport u) ⊆ K →
      ∀ {p : ℝ}, 0 < p →
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
        ≤ ENNReal.ofReal C_K *
            ∫⁻ x, ‖u x‖ₑ ^ p
              ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
  classical
  obtain ⟨M_inf, hM_inf_pos, hM_inf_le⟩ :=
    exists_inf_chartDensity_on_compact (I := I) (M := M) g α hK_compact hK_ne hK_sub
  set C_K : ℝ := ((euclideanHaarFactor E : ℝ) * M_inf)⁻¹ with hC_K_def
  have hC_K_pos : 0 < C_K := by
    rw [hC_K_def]
    apply inv_pos.mpr
    apply mul_pos
    · exact_mod_cast euclideanHaarFactor_pos
    · exact hM_inf_pos
  refine ⟨C_K, hC_K_pos, ?_⟩
  intro u hu_meas hu_supp hu_supp_K p hp_pos
  -- Mirror of the per-`u` reverse-bridge proof, with K-uniform `M_inf`.
  rw [lintegral_enorm_pow_riemannianMeasure_eq_const_mul_chartTargetEuclid
      (I := I) (M := M) g α hu_meas hu_supp hp_pos]
  set K_eucl : Set (EuclN E) := toEuclidean ''
    ((extChartAt I α) '' (tsupport u)) with hK_eucl_def
  have hpt : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ENNReal.ofReal (M_inf) * ‖chartPushedRaw I α u y‖ₑ ^ p
        ≤ ENNReal.ofReal
            (DifferentialGeometry.Integral.Measure.chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          ‖chartPushedRaw I α u y‖ₑ ^ p := by
    intro y hy_target
    by_cases hy_K_eucl : y ∈ K_eucl
    · obtain ⟨z_E, hz_E_chart, hz_Ey⟩ := hy_K_eucl
      have hz_in_K : z_E ∈ K := hu_supp_K hz_E_chart
      have hz_target : z_E ∈ (extChartAt I α).target := hK_sub hz_in_K
      have hsym_eq : (toEuclidean (E := E)).symm y = z_E := by
        rw [← hz_Ey]; exact (toEuclidean (E := E)).symm_apply_apply z_E
      have hbound :
          M_inf ≤
          DifferentialGeometry.Integral.Measure.chartDensity g α
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
        rw [hsym_eq]; exact hM_inf_le z_E hz_in_K
      have h_density_ge :
          ENNReal.ofReal M_inf
            ≤ ENNReal.ofReal
            (DifferentialGeometry.Integral.Measure.chartDensity g α
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :=
        ENNReal.ofReal_le_ofReal hbound
      gcongr
    · -- y ∉ K_eucl: chartPushedRaw u y = 0.
      have hpr_zero : chartPushedRaw I α u y = 0 :=
        chartPushedRaw_eq_zero_off_image_tsupport
          (I := I) (M := M) (u := u) α hy_target hy_K_eucl
      rw [hpr_zero, enorm_zero, ENNReal.zero_rpow_of_pos hp_pos]
      simp
  have h_int_le :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal M_inf * ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E)))
        ≤ (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (DifferentialGeometry.Integral.Measure.chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E))) :=
    MeasureTheory.setLIntegral_mono_ae'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)
      (Filter.Eventually.of_forall hpt)
  have h_LHS_eq :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal M_inf * ‖chartPushedRaw I α u y‖ₑ ^ p
          ∂(volume : Measure (EuclN E))) =
        ENNReal.ofReal M_inf *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
    rw [MeasureTheory.lintegral_const_mul']
    exact ENNReal.ofReal_ne_top
  rw [h_LHS_eq] at h_int_le
  have hM_inf_ennreal_pos : (ENNReal.ofReal M_inf : ℝ≥0∞) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hM_inf_pos
  have hM_inf_ennreal_ne_top : (ENNReal.ofReal M_inf : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  set D : ℝ≥0∞ := (euclideanHaarFactor E : ℝ≥0∞) * ENNReal.ofReal M_inf with hD_def
  have hD_pos : D ≠ 0 :=
    mul_ne_zero euclideanHaarFactor_ennreal_ne_zero hM_inf_ennreal_pos
  have hD_ne_top : D ≠ ⊤ :=
    ENNReal.mul_ne_top euclideanHaarFactor_ennreal_ne_top hM_inf_ennreal_ne_top
  have hC_eq_D_inv : ENNReal.ofReal C_K = D⁻¹ := by
    rw [hC_K_def, hD_def]
    have h_prod_pos : 0 < (euclideanHaarFactor E : ℝ) * M_inf := by
      apply mul_pos
      · exact_mod_cast euclideanHaarFactor_pos
      · exact hM_inf_pos
    rw [show ((euclideanHaarFactor E : ℝ) * M_inf)⁻¹ =
          (1 : ℝ) / ((euclideanHaarFactor E : ℝ) * M_inf) from by rw [one_div]]
    rw [ENNReal.ofReal_div_of_pos h_prod_pos]
    rw [ENNReal.ofReal_one]
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    rw [ENNReal.ofReal_coe_nnreal]
    rw [one_div]
  rw [hC_eq_D_inv]
  have h_step :
      D * (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
          ‖chartPushedRaw I α u y‖ₑ ^ p ∂(volume : Measure (EuclN E)))
        ≤ (euclideanHaarFactor E : ℝ≥0∞) *
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
                (DifferentialGeometry.Integral.Measure.chartDensity g α
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              ‖chartPushedRaw I α u y‖ₑ ^ p
            ∂(volume : Measure (EuclN E)) := by
    rw [hD_def, mul_assoc]
    gcongr
  rwa [ENNReal.mul_le_iff_le_inv hD_pos hD_ne_top] at h_step

/-- Reverse bridge inequality at the level of `eLpNorm`s with a uniform
constant on the Euclidean side. -/
theorem eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK_compact : IsCompact K) (hK_ne : K.Nonempty)
    (hK_sub : K ⊆ (extChartAt I α).target)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C_K : ℝ, 0 < C_K ∧ ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ (chartAt H α).source →
      (extChartAt I α) '' (tsupport u) ⊆ K →
      eLpNorm (chartPushedRaw I α u) p
          ((volume : Measure (EuclN E)).restrict
            (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal C_K *
            eLpNorm u p
              (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)) := by
  classical
  have hp_ne_zero : p ≠ 0 := by
    intro h; rw [h] at hp_one; exact absurd hp_one (by norm_num)
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  obtain ⟨C, hC_pos, hC_bnd⟩ :=
    lintegral_chartPushedRaw_le_const_mul_lintegral_riemannianMeasure_uniform
      (I := I) (M := M) g α hK_compact hK_ne hK_sub
  refine ⟨C ^ (1 / p.toReal), Real.rpow_pos_of_pos hC_pos _, ?_⟩
  intro u hu_meas hu_supp hu_K
  have h_lint := hC_bnd hu_meas hu_supp hu_K hp_toReal_pos
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
  have h_LHS_eq :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
        ∂(volume : Measure (EuclN E))) =
      ∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
        ∂((volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)) := rfl
  rw [h_LHS_eq] at h_lint
  have h_pow_le :
      (∫⁻ y, ‖chartPushedRaw I α u y‖ₑ ^ p.toReal
          ∂((volume : Measure (EuclN E)).restrict
            (chartTargetEuclid (I := I) (M := M) α))) ^
            (1 / p.toReal)
        ≤ (ENNReal.ofReal C *
            ∫⁻ x, ‖u x‖ₑ ^ p.toReal
              ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))) ^
              (1 / p.toReal) := by
    apply ENNReal.rpow_le_rpow h_lint
    positivity
  refine h_pow_le.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.toReal)]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top]
  gcongr
  rw [← ENNReal.ofReal_rpow_of_pos hC_pos]

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
