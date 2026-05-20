import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridge
import DifferentialGeometry.Integral.L2.SmoothSections.Defs
import DifferentialGeometry.Tensor.RSTensor.Defs

/-!
# Chart-pulled squared norm of a tensor section

For a smooth Riemannian manifold `(M, g)` and a fiberwise section
`S : Π b : M, TensorRSSpace r s I b` of the `(r,s)`-tensor bundle, this file
defines the *chart-pulled squared norm function*

  `tensorTrivProjPushedNormSq g r s α S : EuclN E → ℝ`

obtained by composing `S` with the inverse extended chart at `α`, sending the
result through the fiber-to-model identification `TensorRSSpace.toModel`, and
squaring the resulting model-fiber norm. The value is zero outside the chart
target image (`chartTargetEuclid α`).

The construction mirrors the scalar `chartPushedRaw` infrastructure in the
companion `Sobolev/Manifold/MeasureBridge.lean` file. We expose the basic
analytic properties:

* continuity on the chart target (for sections whose total-space map is
  continuous on the chart source);
* compact support (for sections whose pointwise norm is supported inside the
  chart source on a compact manifold);
* measurability (for sections whose total-space map is measurable);
* integrability on the chart target (a consequence of the previous two on
  compact manifolds).
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function Tensor0SBundle
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

open DifferentialGeometry.Analysis.Sobolev.Chart

/-! ## Definition: chart-pulled squared model-fiber norm -/

variable (I) in
/-- Chart-pulled squared norm of the tensor section `S` at chart center `α`.

On the chart-target image `chartTargetEuclid α` the value is
`‖TensorRSSpace.toModel (S ((extChartAt I α).symm (toEuclidean.symm y)))‖^2`;
outside the chart-target image the value is zero. -/
def tensorTrivProjPushedNormSq
    (_g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) : EuclN → ℝ := by
  classical
  exact fun y =>
    if y ∈ chartTargetEuclid (I := I) (M := M) α then
      ‖TensorRSSpace.toModel
        (S ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))‖ ^ 2
    else 0

/-- On the chart-target image, the chart-pulled squared norm has the explicit
formula in terms of the inverse chart. -/
lemma tensorTrivProjPushedNormSq_apply_of_mem
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y =
      ‖TensorRSSpace.toModel
        (S ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))‖ ^ 2 := by
  classical
  unfold tensorTrivProjPushedNormSq
  simp [hy]

/-- Outside the chart-target image, the chart-pulled squared norm is zero. -/
lemma tensorTrivProjPushedNormSq_apply_of_notMem
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    {y : EuclN}
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y = 0 := by
  classical
  unfold tensorTrivProjPushedNormSq
  simp [hy]

/-- The chart-pulled squared norm vanishes outside the chart-target image. -/
lemma tensorTrivProjPushedNormSq_eq_zero_off_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (y : EuclN)
    (hy : y ∉ chartTargetEuclid (I := I) (M := M) α) :
    tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y = 0 :=
  tensorTrivProjPushedNormSq_apply_of_notMem (I := I) (M := M) g r s α S hy

/-- The chart-pulled squared norm is nonnegative everywhere. -/
lemma tensorTrivProjPushedNormSq_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (y : EuclN) :
    0 ≤ tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y := by
  classical
  unfold tensorTrivProjPushedNormSq
  split_ifs with hy
  · exact sq_nonneg _
  · exact le_rfl

/-! ## Continuity on the chart target -/

/-- The chart-pulled squared norm is continuous on the chart-target image,
provided the underlying section is continuous on the chart source. The
continuity hypothesis is phrased as continuity of the model-fiber image
`x ↦ ‖TensorRSSpace.toModel (S x)‖^2` on `(chartAt H α).source`, which is the
natural form coming from a smooth or continuous bundle section. -/
theorem tensorTrivProjPushedNormSq_continuousOn_chartTarget
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (hS : ContinuousOn
      (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2)
      ((chartAt H α).source)) :
    ContinuousOn (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- On the chart target, the function equals the continuous composition of
  -- `‖TensorRSSpace.toModel (S ·)‖^2` with `(extChartAt α).symm ∘ toEuclidean.symm`.
  have hcomp : ContinuousOn
      (fun y : EuclN =>
        ‖TensorRSSpace.toModel
          (S ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))‖ ^ 2)
      (chartTargetEuclid (I := I) (M := M) α) := by
    -- Step 1: `symm ∘ toEuclidean.symm` is continuous on chartTargetEuclid and
    -- lands inside `(chartAt H α).source`.
    have hmaps : MapsTo
        (fun y : EuclN =>
          (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (chartTargetEuclid (I := I) (M := M) α)
        ((chartAt H α).source) := by
      intro y hy
      exact symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
    have hcont :=
      continuousOn_symm_toEuclideanSymm (I := I) (M := M) (α := α)
    exact hS.comp hcont hmaps
  -- Combine with the indicator/zero behaviour outside.
  refine ContinuousOn.congr hcomp ?_
  intro y hy
  exact tensorTrivProjPushedNormSq_apply_of_mem (I := I) (M := M) g r s α S hy

/-! ## Compact support -/

/-- The chart-pulled squared norm vanishes outside the toEuclidean image of
the chart-source-contained tsupport of the section. -/
private lemma tensorTrivProjPushedNormSq_eq_zero_off_image_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    {y : EuclN}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hy_off :
      y ∉ toEuclidean ''
        ((extChartAt I α) '' (tsupport
          (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2)))) :
    tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y = 0 := by
  classical
  rw [tensorTrivProjPushedNormSq_apply_of_mem (I := I) (M := M) g r s α S hy_target]
  -- Argue the point `(extChartAt α).symm (toEuclidean.symm y)` is off `tsupport`
  -- of the model-fiber-norm-squared function.
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  by_contra hne
  apply hy_off
  -- Recover the chart-target witness `z := toEuclidean.symm y`.
  obtain ⟨z, hz_target, hzy⟩ := hy_target
  have hsym_eq : (toEuclidean (E := E)).symm y = z := by
    rw [← hzy]; exact (toEuclidean (E := E)).symm_apply_apply z
  have hxz : x = (extChartAt I α).symm z := by
    rw [hx_def, hsym_eq]
  have hx_supp :
      x ∈ tsupport (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2) :=
    subset_tsupport _ (Function.mem_support.mpr hne)
  refine ⟨z, ⟨x, hx_supp, ?_⟩, hzy⟩
  rw [hxz]
  exact (extChartAt I α).right_inv hz_target

/-- The chart-pulled squared norm has compact support, provided the underlying
model-fiber-norm-squared function on `M` has compact support contained in the
chart source. -/
theorem tensorTrivProjPushedNormSq_hasCompactSupport
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (hS_supp :
      tsupport (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2) ⊆
        (chartAt H α).source) :
    HasCompactSupport
      (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) := by
  classical
  -- The carrier set in Euclidean space is the toEuclidean image of the
  -- extChartAt image of the tsupport of `‖toModel (S ·)‖^2`. This set is
  -- compact (continuous image of a compact set in `M`).
  -- We use `HasCompactSupport.intro` with this compact set.
  set u : M → ℝ := fun x => ‖TensorRSSpace.toModel (S x)‖ ^ 2 with hu_def
  -- Image of tsupport `u` under extChartAt is compact and contained in chart target.
  obtain ⟨hcompact_image, hsub_target⟩ :=
    image_extChartAt_tsupport_compact_subset_target
      (I := I) (M := M) (u := u) (α := α) hS_supp
  set K : Set EuclN := toEuclidean '' ((extChartAt I α) '' (tsupport u)) with hK_def
  have hK_compact : IsCompact K :=
    hcompact_image.image (toEuclidean (E := E)).continuous
  -- Off `K`, the function is zero.
  -- Use `HasCompactSupport` via `hasCompactSupport_iff_eventuallyEq` or the
  -- direct closed-support definition.
  refine HasCompactSupport.of_support_subset_isCompact hK_compact ?_
  intro y hy_supp
  -- `hy_supp : y ∈ support (tensorTrivProjPushedNormSq ...)`.
  -- Argue by contradiction that `y ∈ K`.
  by_contra hy_notK
  apply hy_supp
  -- Either `y` is off the chart-target image, in which case the value is zero;
  -- or `y` is in the chart-target image but off `K`, in which case the value
  -- is zero by `tensorTrivProjPushedNormSq_eq_zero_off_image_tsupport`.
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · -- Off `K` (= image of `tsupport u`), the function is zero on chart target.
    exact tensorTrivProjPushedNormSq_eq_zero_off_image_tsupport
      (I := I) (M := M) g r s α S hy_target hy_notK
  · exact tensorTrivProjPushedNormSq_apply_of_notMem
      (I := I) (M := M) g r s α S hy_target

/-! ## Measurability -/

/-- Auxiliary: the chart-target image `chartTargetEuclid α` is Borel-measurable.
This is just `chartTargetEuclid_measurableSet` reflected into the current
namespace for convenience. -/
private lemma chartTargetEuclid_measurableSet'
    (α : M) :
    MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
  chartTargetEuclid_measurableSet (I := I) (M := M) α

/-- The chart-pulled squared norm is Borel measurable on the Euclidean target,
provided the underlying model-fiber-norm-squared function on `M` is measurable. -/
theorem tensorTrivProjPushedNormSq_measurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (hS_meas :
      Measurable (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2)) :
    Measurable (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) := by
  classical
  -- Pull back via `(extChartAt α).symm ∘ toEuclidean.symm`, but only on the
  -- chart target where this composition is meaningful; outside we have zero.
  -- We use the globalisation trick from MeasureBridge: replace `extChartAt.symm`
  -- by a globalised version on `E` (constantly `α` off the chart target), and
  -- use Borel measurability of the resulting composition.
  -- Define the function on `EuclN` directly via an indicator of `chartTargetEuclid α`.
  set u : M → ℝ := fun x => ‖TensorRSSpace.toModel (S x)‖ ^ 2 with hu_def
  -- Build a globalised inverse chart on `E`: agrees with `extChartAt.symm` on
  -- target, equals `α` off target. Then `u ∘ extChartAtSymmGlob` is Borel
  -- measurable on `E`.
  have hsymm_glob_meas :
      Measurable (fun y : E =>
        ((extChartAt I α).target.piecewise
          (fun y : E => (extChartAt I α).symm y)
          (fun _ : E => α)) y) := by
    refine ContinuousOn.measurable_piecewise
      (continuousOn_extChartAt_symm (I := I) α) continuousOn_const ?_
    exact DifferentialGeometry.Integral.Measure.measurableSet_extChartAt_target
      (I := I) (M := M) α
  -- Compose with `u`, then with `toEuclidean.symm`.
  have hu_pull :
      Measurable (fun y : E =>
        u (((extChartAt I α).target.piecewise
              (fun y : E => (extChartAt I α).symm y)
              (fun _ : E => α)) y)) :=
    hS_meas.comp hsymm_glob_meas
  have htoEucl :
      Measurable ((toEuclidean (E := E)).symm : EuclN → E) :=
    (toEuclidean (E := E)).symm.continuous.measurable
  have hu_pull' :
      Measurable (fun z : EuclN =>
        u (((extChartAt I α).target.piecewise
              (fun y : E => (extChartAt I α).symm y)
              (fun _ : E => α)) ((toEuclidean (E := E)).symm z))) :=
    hu_pull.comp htoEucl
  -- The function is the indicator of `chartTargetEuclid α` times this.
  have hindic_meas :
      Measurable ((chartTargetEuclid (I := I) (M := M) α).indicator
        (fun z : EuclN =>
          u (((extChartAt I α).target.piecewise
                (fun y : E => (extChartAt I α).symm y)
                (fun _ : E => α)) ((toEuclidean (E := E)).symm z)))) :=
    hu_pull'.indicator (chartTargetEuclid_measurableSet' (I := I) (M := M) α)
  -- Show our function equals this indicator pointwise.
  have heq :
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S =
        (chartTargetEuclid (I := I) (M := M) α).indicator
          (fun z : EuclN =>
            u (((extChartAt I α).target.piecewise
                  (fun y : E => (extChartAt I α).symm y)
                  (fun _ : E => α)) ((toEuclidean (E := E)).symm z))) := by
    funext y
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [tensorTrivProjPushedNormSq_apply_of_mem
            (I := I) (M := M) g r s α S hy]
      rw [Set.indicator_of_mem hy]
      -- Show piecewise is `extChartAt.symm` on chart target.
      have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
        have hpre :
            chartTargetEuclid (I := I) (M := M) α =
              (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target :=
          chartTargetEuclid_eq_preimage_symm (I := I) (M := M) (α := α)
        rw [hpre] at hy; exact hy
      rw [Set.piecewise_eq_of_mem _ _ _ hy_target]
    · rw [tensorTrivProjPushedNormSq_apply_of_notMem
            (I := I) (M := M) g r s α S hy]
      rw [Set.indicator_of_notMem hy]
  rw [heq]
  exact hindic_meas

/-! ## Integrability on the chart target -/

/-- The chart-pulled squared norm is integrable on the chart-target image,
provided the underlying model-fiber-norm-squared function on `M` is measurable
and has compact support contained in the chart source (so the function on
`EuclN` is bounded with compact support). The manifold is taken compact for
convenience: this ensures the compact-support consequence holds globally on
the chart-target image. -/
theorem tensorTrivProjPushedNormSq_integrableOn
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b)
    (hS_meas :
      Measurable (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2))
    (hS_supp :
      tsupport (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2) ⊆
        (chartAt H α).source)
    (hS_cont :
      ContinuousOn
        (fun x : M => ‖TensorRSSpace.toModel (S x)‖ ^ 2)
        ((chartAt H α).source)) :
    IntegrableOn (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S)
      (chartTargetEuclid (I := I) (M := M) α)
      (volume : MeasureTheory.Measure EuclN) := by
  classical
  -- Strategy: bound the chart-pulled squared norm by the indicator of a
  -- compact set `K ⊆ chartTargetEuclid α` on which the function is bounded
  -- (continuous on the compact set, hence bounded). Outside `K` the function
  -- is zero, so this gives global integrability.
  have hmeas :
      Measurable (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) :=
    tensorTrivProjPushedNormSq_measurable
      (I := I) (M := M) g r s α S hS_meas
  have hcont_target :
      ContinuousOn (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S)
        (chartTargetEuclid (I := I) (M := M) α) :=
    tensorTrivProjPushedNormSq_continuousOn_chartTarget
      (I := I) (M := M) g r s α S hS_cont
  set u : M → ℝ := fun x => ‖TensorRSSpace.toModel (S x)‖ ^ 2 with hu_def
  obtain ⟨hK_compact_image, _hK_sub_target⟩ :=
    image_extChartAt_tsupport_compact_subset_target
      (I := I) (M := M) (u := u) (α := α) hS_supp
  set K : Set EuclN := toEuclidean '' ((extChartAt I α) '' (tsupport u)) with hK_def
  have hK_compact : IsCompact K :=
    hK_compact_image.image (toEuclidean (E := E)).continuous
  have hK_sub :
      K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    image_toEuclidean_extChartAt_tsupport_subset_chartTargetEuclid
      (I := I) (M := M) (u := u) (α := α) hS_supp
  have hcont_K :
      ContinuousOn (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) K :=
    hcont_target.mono hK_sub
  -- The function is integrable on `K`.
  have hint_K :
      IntegrableOn (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) K
        (volume : MeasureTheory.Measure EuclN) :=
    ContinuousOn.integrableOn_compact hK_compact hcont_K
  -- Outside `K`, the function vanishes.
  have hzero_off_K : ∀ y, y ∉ K →
      tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S y = 0 := by
    intro y hy_notK
    by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact tensorTrivProjPushedNormSq_eq_zero_off_image_tsupport
        (I := I) (M := M) g r s α S hy_target hy_notK
    · exact tensorTrivProjPushedNormSq_apply_of_notMem
        (I := I) (M := M) g r s α S hy_target
  -- Global integrability follows: on `K^c` the function is zero, so its global
  -- integral splits into the integral on `K` (finite by hint_K).
  have hf_integrable :
      Integrable (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S)
        (volume : MeasureTheory.Measure EuclN) := by
    have hindic_eq :
        tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S =
          K.indicator (tensorTrivProjPushedNormSq (I := I) (M := M) g r s α S) := by
      funext y
      by_cases hy_K : y ∈ K
      · rw [Set.indicator_of_mem hy_K]
      · rw [Set.indicator_of_notMem hy_K, hzero_off_K y hy_K]
    rw [hindic_eq]
    exact hint_K.integrable_indicator hK_compact.measurableSet
  exact hf_integrable.integrableOn

end Measure
end Integral
end DifferentialGeometry

end
