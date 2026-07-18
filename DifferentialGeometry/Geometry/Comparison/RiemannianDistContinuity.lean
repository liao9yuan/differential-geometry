import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Continuity of the Riemannian extended distance from a fixed base point

For a smooth Riemannian metric `g` on a smooth manifold `M` and a fixed
base point `p : M`, the map `q ↦ riemannianEDist I p q` is continuous for
the manifold topology on `M`.

The proof installs, from the metric data `g`, the auxiliary fibre instances
`Bundle.RiemannianBundle (TangentSpace I)` (from `g.toRiemannianMetric`)
and `IsContinuousRiemannianBundle E (TangentSpace I)` (from the
smooth-implies-continuous inner product of `g`), then builds Mathlib's
`PseudoEMetricSpace.ofRiemannianMetric I M`. By construction (via
`PseudoEMetricSpace.ofEDistOfTopology`) this pseudo-emetric structure has

* `edist = riemannianEDist I` (definitionally), and
* a topology *definitionally equal* to the ambient manifold topology
  (`UniformSpace.ofFunOfHasBasis` sets `toTopologicalSpace := t`).

Continuity of the extended distance (`Continuous.edist`) for this
pseudo-emetric structure therefore yields continuity of
`q ↦ riemannianEDist I p q` for the manifold topology directly.

The regularity hypothesis `[RegularSpace M]` required by
`PseudoEMetricSpace.ofRiemannianMetric` is discharged from the manifold
structure: a finite-dimensional manifold is locally compact
(`Manifold.locallyCompact_of_finiteDimensional`), and a weakly locally
compact `R1` (here Hausdorff) space is regular.

This is the prerequisite continuity input for the open/closed clopen
decomposition in radial-geodesic surjectivity arguments.
-/

open Set Function Filter Bundle Manifold Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal NNReal

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Integral.Measure (SmoothRiemannianMetric)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

omit [InnerProductSpace ℝ E] in
/-- **Continuity of the Riemannian extended distance from a fixed base point.**

For a smooth Riemannian metric `g` and a fixed `p : M`, the map
`q ↦ riemannianEDist I p q` is continuous for the manifold topology on `M`.

The auxiliary fibre instances `RiemannianBundle (TangentSpace I)` and
`IsContinuousRiemannianBundle E (TangentSpace I)` are installed from `g`
inside the proof, exactly as Mathlib's `riemannianEDist` API expects; the
statement itself uses only the manifold topology and the metric data `g`.

Mathlib's `PseudoEMetricSpace.ofRiemannianMetric I M` provides a pseudo
extended metric whose `edist` is `riemannianEDist I` and whose topology is
definitionally the ambient one; continuity of `edist` (`Continuous.edist`)
then transfers to `riemannianEDist`.

The regularity hypothesis of `ofRiemannianMetric` is discharged locally
from finite-dimensionality (local compactness) together with the
Hausdorff hypothesis. -/
theorem continuous_riemannianEDist
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    Continuous (fun q : M ↦ riemannianEDist I p q) := by
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  haveI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  haveI : RegularSpace M := inferInstance
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact (continuous_const.edist continuous_id)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [T2Space M] in
/-- On a sufficiently small convex extended-chart ball, the chart inverse is
Lipschitz for the Riemannian extended distance. -/
theorem chart_symm_edist_le
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (x : M) :
    ∃ C : ℝ≥0, 0 < C ∧ ∃ r : ℝ, 0 < r ∧
      ∀ y ∈ Metric.ball (extChartAt I x x) r ∩ range I,
        ∀ z ∈ Metric.ball (extChartAt I x x) r ∩ range I,
          riemannianEDist I ((extChartAt I x).symm y)
              ((extChartAt I x).symm z) ≤ C * edist y z := by
  rcases eventually_enorm_mfderivWithin_symm_extChartAt_lt I x with
    ⟨C, C_pos, hC⟩
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      Metric.ball (extChartAt I x x) r ∩ range I ⊆
        (extChartAt I x).target ∩
          {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C} :=
    Metric.mem_nhdsWithin_iff.1
      (inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  refine ⟨C, C_pos, r, r_pos, ?_⟩
  intro y hy z hz
  let eta := ContinuousAffineMap.lineMap (R := ℝ) y z
  set gamma := (extChartAt I x).symm ∘ eta
  have heta : Icc 0 1 ⊆ ⇑eta ⁻¹' ((extChartAt I x).target ∩
      {w | ‖mfderiv[range I] (extChartAt I x).symm w‖ₑ < C}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, eta]
    apply Subset.trans _ hr
    exact ((convex_ball _ _).inter I.convex_range).segment_subset hy hz
  simp only [preimage_inter, subset_inter_iff] at heta
  have eta_smooth : CMDiff[Icc 0 1] 1 eta := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hdist :
      riemannianEDist I ((extChartAt I x).symm y)
          ((extChartAt I x).symm z) ≤ pathELength I gamma 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp eta_smooth heta.1
    · simp [gamma, eta, ContinuousAffineMap.coe_lineMap_eq]
    · simp [gamma, eta, ContinuousAffineMap.coe_lineMap_eq]
  apply hdist.trans
  rw [← lintegral_fderiv_lineMap_eq_edist,
    pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
  have hcomp : mfderiv[Icc 0 1] gamma t =
      (mfderiv[range I] (extChartAt I x).symm (eta t)) ∘L
        (mfderiv[Icc 0 1] eta t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (heta.1 ht)
    · exact eta_smooth.mdifferentiableOn one_ne_zero t ht
    · exact heta.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have happly : mfderiv[Icc 0 1] gamma t 1 =
      (mfderiv[range I] (extChartAt I x).symm (eta t))
        (mfderiv[Icc 0 1] eta t 1) := congr($hcomp 1)
  rw [happly]
  apply (ContinuousLinearMap.le_opNorm_enorm _ _).trans
  gcongr
  · exact (heta.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [T2Space M] in
/-- The inverse of a fixed extended chart is locally Lipschitz for the
Riemannian extended distance at every point of its target. -/
theorem chart_inv_edist_le
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (α : M) {y₀ : E} (hy₀ : y₀ ∈ (extChartAt I α).target) :
    ∃ C : ℝ≥0, ∃ s ∈ 𝓝[(extChartAt I α).target] y₀,
      ∀ y ∈ s, ∀ z ∈ s,
        riemannianEDist I ((extChartAt I α).symm y)
            ((extChartAt I α).symm z) ≤ C * edist y z := by
  let q := (extChartAt I α).symm y₀
  rcases chart_symm_edist_le (I := I) q with ⟨C, -, r, hr, hq⟩
  let F := extChartAt I q ∘ (extChartAt I α).symm
  have hyCoord :
      y₀ ∈ ((extChartAt I α).symm ≫ extChartAt I q).source := by
    rw [PartialEquiv.trans_source]
    exact ⟨hy₀, by simpa only [q] using mem_extChartAt_source (I := I) q⟩
  have hF : ContDiffWithinAt ℝ 1 F (range I) y₀ := by
    simpa only [F] using
      contDiffWithinAt_ext_coord_change (I := I) q α hyCoord
  obtain ⟨K, t, ht, hKt⟩ :=
    hF.exists_lipschitzOnWith I.convex_range
  have hsrc :
      (extChartAt I α).symm ⁻¹' (extChartAt I q).source ∈ 𝓝 y₀ :=
    (continuousAt_extChartAt_symm'' (I := I) hy₀).preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := I) q)
  have hF0 : F y₀ = extChartAt I q q := by
    simp only [F, Function.comp_apply, q]
  have hball :
      F ⁻¹' Metric.ball (extChartAt I q q) r ∈ 𝓝[range I] y₀ := by
    apply hF.continuousWithinAt.preimage_mem_nhdsWithin
    simpa only [hF0] using Metric.ball_mem_nhds (extChartAt I q q) hr
  let s := t ∩ (extChartAt I α).target ∩
    ((extChartAt I α).symm ⁻¹' (extChartAt I q).source) ∩
      (F ⁻¹' Metric.ball (extChartAt I q q) r)
  have hsRange : s ∈ 𝓝[range I] y₀ := by
    exact inter_mem
      (inter_mem
        (inter_mem ht (extChartAt_target_mem_nhdsWithin_of_mem hy₀))
        (mem_nhdsWithin_of_mem_nhds hsrc))
      hball
  have hsTarget : s ∈ 𝓝[(extChartAt I α).target] y₀ :=
    (nhdsWithin_mono y₀ (extChartAt_target_subset_range α)) hsRange
  refine ⟨C * K, s, hsTarget, ?_⟩
  intro y hy z hz
  rcases hy with ⟨⟨⟨hyt, hyTarget⟩, hySource⟩, hyBall⟩
  rcases hz with ⟨⟨⟨hzt, hzTarget⟩, hzSource⟩, hzBall⟩
  have hyRange : F y ∈ range I :=
    extChartAt_target_subset_range q
      ((extChartAt I q).map_source hySource)
  have hzRange : F z ∈ range I :=
    extChartAt_target_subset_range q
      ((extChartAt I q).map_source hzSource)
  have hyInv :
      (extChartAt I q).symm (F y) = (extChartAt I α).symm y := by
    simpa only [F, Function.comp_apply] using
      (extChartAt I q).left_inv hySource
  have hzInv :
      (extChartAt I q).symm (F z) = (extChartAt I α).symm z := by
    simpa only [F, Function.comp_apply] using
      (extChartAt I q).left_inv hzSource
  rw [← hyInv, ← hzInv]
  refine (hq (F y) ⟨hyBall, hyRange⟩ (F z) ⟨hzBall, hzRange⟩).trans ?_
  calc
    (C : ℝ≥0∞) * edist (F y) (F z)
        ≤ C * (K * edist y z) := mul_right_mono (hKt hyt hzt)
    _ = (C * K) * edist y z := by simp only [mul_assoc]

omit [InnerProductSpace ℝ E] in
/-- **Continuity on the finite locus of the real Riemannian distance from a fixed
base point.**

There is no separate `riemannianDist` definition in Mathlib; the real-valued
Riemannian distance is `(riemannianEDist I p ·).toReal`. Since `ENNReal.toReal`
is discontinuous at `∞` (and `riemannianEDist I p q = ∞` is possible when no
`C¹` path joins `p` to `q`), the real distance is *not* globally continuous on a
non-complete manifold. It is, however, continuous on the locus where the
extended distance is finite, which is what the corollary records: on
`{q | riemannianEDist I p q ≠ ∞}` the map `q ↦ (riemannianEDist I p q).toReal`
is continuous. -/
theorem continuousOn_riemannianEDist_toReal_on_finite
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    ContinuousOn (fun q : M ↦ (riemannianEDist I p q).toReal)
      {q : M | riemannianEDist I p q ≠ (∞ : ℝ≥0∞)} := by
  letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  refine ENNReal.continuousOn_toReal.comp'
    (continuous_riemannianEDist g p).continuousOn (fun q hq ↦ ?_)
  exact hq

end Riemannian
end Geometry
end DifferentialGeometry

end
