import DifferentialGeometry.Geometry.Comparison.Volume.RawRadialGronwall
import DifferentialGeometry.Geometry.Exponential.RawFramedLocalDiffeo

noncomputable section

open Set Bundle Function Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]

/-- Curvature control on a framed raw radial segment makes the differential of
the framed exponential injective at its model launch vector. -/
theorem framed_mfderiv_inj
    (g : SmoothRiemannianMetric I M) (p : M) (z : E)
    {K R Vb : ℝ}
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from
        t • normalFrame (I := I) (E := E) g p z) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (hV : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (g.inner
        (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t)
        (curveVelocity (I := I)
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z)) t)
        (curveVelocity (I := I)
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z)) t)) ≤ Vb)
    (hRm : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t))) ≤ R)
    (hcoef :
      Real.sqrt ((Fintype.card
        (Fin 1 → Fin (Module.finrank ℝ E)) : ℝ)) * R * Vb ^ 2 ≤ K)
    (hsmall : gronwallBound 0 (max K 1) K 1 < 1) :
    Function.Injective
      (mfderiv 𝓘(ℝ, E) I (framedExpMap (I := I) (E := E) g p) z) := by
  have hraw := rawExp_mfderiv_inj (I := I) g p
    (normalFrame (I := I) (E := E) g p z) hdom hK hVb hV hRm hcoef hsmall
  have hz : normalFrame (I := I) (E := E) g p z ∈ expDomain (I := I) g p := by
    simpa only [one_smul] using hdom 1 ⟨zero_le_one, le_rfl⟩
  rw [mfderiv_framedMap (I := I) g p hz]
  exact hraw.comp (normalFrame (I := I) (E := E) g p).injective

/-- Uniform raw radial curvature control gives a local diffeomorphism for the
framed exponential on an open model-space set. -/
theorem framed_locdiff_rm
    (g : SmoothRiemannianMetric I M) (p : M) {U : Set E}
    (hU : IsOpen U) {K R Vb : ℝ}
    (hdom : ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from
        t • normalFrame (I := I) (E := E) g p z) ∈ expDomain (I := I) g p)
    (hK : 0 ≤ K) (hVb : 0 ≤ Vb)
    (hV : ∀ z ∈ U, ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (g.inner
        (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t)
        (curveVelocity (I := I)
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z)) t)
        (curveVelocity (I := I)
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z)) t)) ≤ Vb)
    (hRm : ∀ z ∈ U, ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t) 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At
          (I := I) (M := M) g
          (radialCurve (I := I) g p (normalFrame (I := I) (E := E) g p z) t))) ≤ R)
    (hcoef :
      Real.sqrt ((Fintype.card
        (Fin 1 → Fin (Module.finrank ℝ E)) : ℝ)) * R * Vb ^ 2 ≤ K)
    (hsmall : gronwallBound 0 (max K 1) K 1 < 1) :
    IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap (I := I) (E := E) g p) U := by
  apply framedExp_locdiff (I := I) g p hU
  · intro z hz
    simpa only [one_smul] using hdom z hz 1 ⟨zero_le_one, le_rfl⟩
  · intro z hz
    exact framed_mfderiv_inj (I := I) g p z (hdom z hz) hK hVb
      (hV z hz) (hRm z hz) hcoef hsmall

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
