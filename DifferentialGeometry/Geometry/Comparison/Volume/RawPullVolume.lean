import DifferentialGeometry.Geometry.Comparison.Volume.BishopPolarFramed
import DifferentialGeometry.Geometry.Comparison.Volume.BishopRawDensity
import DifferentialGeometry.Geometry.Comparison.Volume.SegmentDensity

noncomputable section

open Filter Metric Set Bundle Manifold MeasureTheory
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The raw pull volume of a normal-frame Euclidean ball, measured in the
unframed chart-model coordinates of the raw exponential map. -/
def rawPullVol
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in (normalFrame (I := I) (E := E) g p) '' Metric.ball (0 : E) R,
    ENNReal.ofReal
      (mapJacDensity (I := I) g
        (fun b : E => expMap (I := I) g p
          (show TangentSpace I p from b)) v)
      ∂(modelHaar (E := E))

omit [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Raw-domain coverage, positive-time differential injectivity, and
nonnegative radial Ricci curvature bound the pull volume by the Euclidean
model-ball volume. -/
theorem rawPullVol_le_eucl
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ)
    (hdom : ∀ v ∈ (normalFrame (I := I) (E := E) g p) ''
        Metric.ball (0 : E) R, ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from t • v) ∈ expDomain (I := I) g p)
    (hinj : ∀ v ∈ (normalFrame (I := I) (E := E) g p) ''
        Metric.ball (0 : E) R, ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p
          (show TangentSpace I p from b) : M)) (t • v)))
    (hRic : ∀ v ∈ (normalFrame (I := I) (E := E) g p) ''
        Metric.ball (0 : E) R, ∀ t ∈ Ioo (0 : ℝ) 1,
      0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p v t)
        (curveVelocity (I := I) (radialCurve (I := I) g p v) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p v) t)) :
    rawPullVol (I := I) g p R ≤
      (volume : Measure E) (Metric.ball (0 : E) R) := by
  classical
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  let K : Set E := L '' Metric.ball (0 : E) R
  let F : E → M := fun b =>
    expMap (I := I) g p (show TangentSpace I p from b)
  have hball : MeasurableSet (Metric.ball (0 : E) R) :=
    Metric.isOpen_ball.measurableSet
  have hK : MeasurableSet K := by
    exact L.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hball
  have hpre : L ⁻¹' K = Metric.ball (0 : E) R := by
    exact Set.preimage_image_eq _ L.injective
  have hpoint : ∀ v ∈ K,
      mapJacDensity (I := I) g F v ≤ normalChartDensity (I := I) g p 0 := by
    intro v hv
    have hv' : v ∈ (normalFrame (I := I) (E := E) g p) ''
        Metric.ball (0 : E) R := by
      simpa only [K, L] using hv
    have hvdom : (show TangentSpace I p from v) ∈ expDomain (I := I) g p := by
      simpa only [one_smul] using hdom v hv' 1 ⟨zero_le_one, le_rfl⟩
    change mapJacDensity (I := I) g
        (fun b : E => expMap (I := I) g p
          (show TangentSpace I p from b)) v ≤ _
    rw [raw_exp_density (I := I) g p v hvdom]
    exact rawDens_le_of_inj (I := I) g p v (hdom v hv')
      (hinj v hv') (hRic v hv')
  calc
    rawPullVol (I := I) g p R =
        ∫⁻ v in K, ENNReal.ofReal (mapJacDensity (I := I) g F v)
          ∂(modelHaar (E := E)) := by
            rfl
    _ ≤ ∫⁻ _v in K, ENNReal.ofReal
          (normalChartDensity (I := I) g p 0) ∂(modelHaar (E := E)) := by
        refine MeasureTheory.setLIntegral_mono_ae measurable_const.aemeasurable ?_
        exact Filter.Eventually.of_forall fun v hv =>
          ENNReal.ofReal_le_ofReal (hpoint v hv)
    _ = (ENNReal.ofReal (normalChartDensity (I := I) g p 0) •
          modelHaar (E := E)) K := by
        rw [setLIntegral_const]
        simp only [Measure.smul_apply, smul_eq_mul]
    _ = Measure.map L (volume : Measure E) K := by
        simpa only [L] using congrArg (fun μ : Measure E => μ K)
          (normalHaar_eq (E := E) (M := M) (I := I) g p)
    _ = (volume : Measure E) (L ⁻¹' K) := by
        rw [Measure.map_apply L.continuous.measurable hK]
    _ = (volume : Measure E) (Metric.ball (0 : E) R) := by
        rw [hpre]

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
