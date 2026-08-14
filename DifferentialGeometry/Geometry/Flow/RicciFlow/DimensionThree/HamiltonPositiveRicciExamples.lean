import DifferentialGeometry.Geometry.Curvature.ConstantRicci
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.HamiltonPositiveRicciAdapter

noncomputable section

open Bundle Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

omit [SigmaCompactSpace M] in
private theorem posRicci_of_const
    {g : SmoothRiemannianMetric I M}
    (hdim : 1 < Module.finrank ℝ E)
    (h : ConstPosSecMetric (I := I) (M := M) g) :
    PosRicciMetric (I := I) (M := M) g := by
  rcases h with ⟨c, hc, hsec⟩
  intro x v hv
  rw [DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor,
    DifferentialGeometry.Integral.Connection.ricci_of_sec
      (I := I) g c hsec x v v]
  have hdR : 0 < (Module.finrank ℝ E : ℝ) - 1 :=
    sub_pos.mpr (by exact_mod_cast hdim)
  exact mul_pos (mul_pos hdR hc) (g.pos x v hv)

abbrev Sphere3Ambient := EuclideanSpace ℝ (Fin 4)

abbrev RoundSphere3 := sphere (0 : Sphere3Ambient) 1

local instance : Fact (Module.finrank ℝ Sphere3Ambient = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

local instance : NeZero
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

theorem roundSphere3_closed :
    Closed3Manifold (I := 𝓡 3) (M := RoundSphere3) := by
  refine ⟨inferInstance, ?_, inferInstance, ?_⟩
  · exact isConnected_iff_connectedSpace.mp
      (isConnected_sphere
        (Module.one_lt_rank_of_one_lt_finrank (by
          norm_num [Sphere3Ambient, finrank_euclideanSpace_fin]))
        (0 : Sphere3Ambient) (by norm_num))
  · norm_num [finrank_euclideanSpace_fin]

theorem roundSphere3_pos :
    AdmitsPosRicci (I := 𝓡 3) (M := RoundSphere3) := by
  refine ⟨Geometry.roundMetric (E := Sphere3Ambient) (n := 3), ?_⟩
  apply posRicci_of_const (by norm_num [finrank_euclideanSpace_fin])
  exact Geometry.roundMetric_constPosSec
    (E := Sphere3Ambient) (n := 3)

theorem roundSphere3_concl :
    AdmitsConstPosSec (I := 𝓡 3) (M := RoundSphere3) ∧
      SphericalSpaceForm (I := 𝓡 3) (M := RoundSphere3) :=
  ham3_main (I := 𝓡 3) (M := RoundSphere3)
    roundSphere3_closed roundSphere3_pos

theorem roundQuot_closed
    (D : Geometry.RoundQuotientData (EuclideanSpace ℝ (Fin 4)) 3) :
    Closed3Manifold (I := 𝓡 3) (M := D.Q) := by
  refine ⟨D.compactSpace, D.connectedSpace, inferInstance, ?_⟩
  norm_num [finrank_euclideanSpace_fin]

theorem roundQuot_pos
    (D : Geometry.RoundQuotientData (EuclideanSpace ℝ (Fin 4)) 3) :
    AdmitsPosRicci (I := 𝓡 3) (M := D.Q) := by
  refine ⟨D.gQuot, ?_⟩
  apply posRicci_of_const (by norm_num [finrank_euclideanSpace_fin])
  exact D.gQuot_constPosSec

theorem roundQuot_concl
    (D : Geometry.RoundQuotientData (EuclideanSpace ℝ (Fin 4)) 3) :
    AdmitsConstPosSec (I := 𝓡 3) (M := D.Q) ∧
      SphericalSpaceForm (I := 𝓡 3) (M := D.Q) :=
  ham3_main (I := 𝓡 3) (M := D.Q)
    (roundQuot_closed D) (roundQuot_pos D)

end DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci

end
