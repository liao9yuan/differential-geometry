import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Geometry.Geodesic.CrossVFReduction
import DifferentialGeometry.Geometry.Geodesic.MaximalRescaling

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A raw radial exponential curve satisfies the geodesic equation at every
time whose scaled vector lies in the raw exponential domain. -/
theorem raw_radial_geo_at
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) {t : ℝ}
    (ht : t • v ∈ expDomain (I := I) g p) :
    HasGeodesicEquationAt (I := I) g
      (fun s : ℝ => expMap (I := I) g p (s • v)) t := by
  classical
  have hline : Continuous (fun s : ℝ => s • v) :=
    continuous_id.smul continuous_const
  have hdom_ev : ∀ᶠ s in 𝓝 t, s • v ∈ expDomain (I := I) g p :=
    hline.continuousAt ((isOpen_expDomain (I := I) g p).mem_nhds ht)
  have hraw_max :
      (fun s : ℝ => expMap (I := I) g p (s • v)) =ᶠ[𝓝 t]
        (fun s => maximalGeodesic (I := I) g p v s) := by
    filter_upwards [hdom_ev] with s hs
    by_cases hs0 : s = 0
    · subst s
      rw [zero_smul, expMap_zero (I := I), maximalGeodesic_zero (I := I)]
    · exact (expMap_smul_max_ne (I := I) g p v hs0 hs).2
  have htmax : t ∈ maximalGeodesicInterval (I := I) g p v := by
    by_cases ht0 : t = 0
    · subst t
      exact zero_mem_maximalGeodesicInterval (I := I) g p v
    · exact (expMap_smul_max_ne (I := I) g p v ht0 ht).1
  obtain ⟨η, J, hJopen, hJconn, h0J, htJ, hη⟩ := htmax
  have hmax_eta :
      (fun s => maximalGeodesic (I := I) g p v s) =ᶠ[𝓝 t] η := by
    have heq := maximalGeo_eqOn (I := I) g hJopen hJconn h0J hη
    filter_upwards [hJopen.mem_nhds htJ] with s hs
    exact heq hs
  have hgeo_eta : HasGeodesicEquationAt (I := I) g η t :=
    (hη.geoAt (hJopen.mem_nhds htJ)).hasGeodesicEquationAt g
  have hgeo_max : HasGeodesicEquationAt (I := I) g
      (fun s => maximalGeodesic (I := I) g p v s) t :=
    HasGeodesicEquationAt.congr_of_eventuallyEq_at
      hmax_eta.eq_of_nhds hmax_eta hgeo_eta
  exact HasGeodesicEquationAt.congr_of_eventuallyEq_at
    hraw_max.eq_of_nhds hraw_max hgeo_max

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

