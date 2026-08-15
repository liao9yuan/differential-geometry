import DifferentialGeometry.Geometry.Comparison.HalfSqDistGrad

set_option autoImplicit false

open Set Manifold Bundle MeasureTheory intervalIntegral
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem radial_min_len
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (u : TangentSpace I p) {L : ℝ}
    (hL : 0 ≤ L) (hu : g.inner p u u = 1)
    (hdist : L = (riemannianEDist I p
      (intrinsicGeodesic (I := I) g hEnorm p u L)).toReal) :
    ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = p →
      η L = intrinsicGeodesic (I := I) g hEnorm p u L →
      arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u) 0 L ≤
        arcLength (I := I) g η 0 L := by
  intro η hη hη0 hηL
  have hη_nonneg : 0 ≤ arcLength (I := I) g η 0 L := by
    unfold arcLength
    exact intervalIntegral.integral_nonneg hL
      (fun _ _ => Real.sqrt_nonneg _)
  have hed :=
    riemannianEDist_le_arcLength
      (I := I) g hL hη (fun s _ => hEnorm (η s) _)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
  have hL_le : L ≤ arcLength (I := I) g η 0 L := by
    rw [hη0, hηL, ENNReal.toReal_ofReal hη_nonneg] at hreal
    exact hdist.trans_le hreal
  rw [arcLength_radial (I := I) g hEnorm p u 0 L,
    hu, Real.sqrt_one, sub_zero, mul_one]
  exact hL_le

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
