import DifferentialGeometry.Geometry.Comparison.CompactGeodesic
import DifferentialGeometry.Geometry.Geodesic.VelocityLift
import DifferentialGeometry.Geometry.Exponential.Defs

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A tangent vector shorter than a compact metric radius belongs to the raw
exponential domain, without assuming ambient completeness. -/
theorem mem_expDom_of_cpt
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (v : TangentSpace I x) {r : ℝ}
    (hv : Real.sqrt (g.inner x v v) < r)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall x (ENNReal.ofReal r))) :
    v ∈ expDomain (I := I) g x := by
  obtain ⟨gamma, J, hJ_open, hJ_conn, h0, h1, hgeo, hcont, hgamma0, hvel⟩ :=
    exists_geo_one_cpt (I := I) g hEnorm x v hv hcpt
  have hlift0 :
      velocityLift (I := I) gamma 0 =
        (⟨x, v⟩ : TangentBundle I M) := by
    apply TotalSpace.ext hgamma0
    exact heq_of_eq hvel
  have hinit : IsGeodesicOnWithInitial (I := I) g gamma J x v :=
    ⟨velocityLift (I := I) gamma, velocityLift_proj (I := I) gamma,
      hlift0, geoLift_isIntegralOn (I := I) g hJ_open hgeo hcont⟩
  rw [mem_expDomain_iff]
  exact ⟨gamma, J, hJ_open, hJ_conn, h0, h1, hinit⟩

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
