import DifferentialGeometry.Geometry.Geodesic.Equation
import DifferentialGeometry.Geometry.Geodesic.Existence
import DifferentialGeometry.Geometry.Geodesic.MaximalInterval
import DifferentialGeometry.Geometry.Geodesic.GlobalUniqueness
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

def expMap (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) : M :=
  maximalGeodesic (I := I) g p v 1

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma expMap_def (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    expMap (I := I) g p v = maximalGeodesic (I := I) g p v 1 := rfl

def expDomain (g : SmoothRiemannianMetric I M) (p : M) : Set (TangentSpace I p) :=
  {v | (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v}

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma mem_expDomain_iff
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p} :
    v ∈ expDomain (I := I) g p ↔
      (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p v := Iff.rfl

section StationaryWitness

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem maximalGeodesicWitness_zero_all_times
    (g : SmoothRiemannianMetric I M) (p : M) (t : ℝ) :
    MaximalGeodesicWitness (I := I) g p (0 : TangentSpace I p) t := by
  classical
  refine ⟨fun _ : ℝ => p, Set.univ, isOpen_univ, isPreconnected_univ,
    Set.mem_univ _, Set.mem_univ _, ?_⟩
  refine ⟨fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M), ?_, rfl, ?_⟩
  · intro _; rfl
  · have hvf_zero : geodesicVectorField (I := I) g
        (⟨p, (0 : E)⟩ : TangentBundle I M) = 0 :=
      geodesicVectorField_zero_section (I := I) g p
    exact (isMIntegralCurve_const hvf_zero).isMIntegralCurveOn Set.univ

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem zero_mem_expDomain (g : SmoothRiemannianMetric I M) (p : M) :
    (0 : TangentSpace I p) ∈ expDomain (I := I) g p :=
  maximalGeodesicWitness_zero_all_times (I := I) g p 1

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem expDomain_nonempty (g : SmoothRiemannianMetric I M) (p : M) :
    (expDomain (I := I) g p).Nonempty :=
  ⟨0, zero_mem_expDomain (I := I) g p⟩

end StationaryWitness

section JunkValue

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem expMap_of_not_mem_expDomain
    {g : SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    (hv : v ∉ expDomain (I := I) g p) :
    expMap (I := I) g p v = p := by
  unfold expMap
  exact maximalGeodesic_of_not_mem (I := I) hv

end JunkValue

section ExpMapZeroWitnessLevel

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem maximalGeodesicChosenCurve_zero_start_eq
    (g : SmoothRiemannianMetric I M) (p : M) :
    maximalGeodesicChosenCurve (I := I) g p (0 : TangentSpace I p)
      (maximalGeodesicWitness_zero_all_times (I := I) g p 1) 0 = p := by
  obtain ⟨_J, _hJ_open, _hJ_conn, _h0J, _h1J, hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (0 : TangentSpace I p)
      (maximalGeodesicWitness_zero_all_times (I := I) g p 1)
  exact hγ.start_eq

end ExpMapZeroWitnessLevel

section ZeroVelocityPropagation

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
private lemma isMIntegralCurve_const_zero_section
    (g : SmoothRiemannianMetric I M) (p : M) :
    IsMIntegralCurve (fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M))
      (geodesicVectorField (I := I) g) :=
  isMIntegralCurve_const (geodesicVectorField_zero_section (I := I) g p)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem isMIntegralCurveOn_zero_section_eq_const
    (g : SmoothRiemannianMetric I M) (p : M)
    {f : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hf : IsMIntegralCurveOn f (geodesicVectorField (I := I) g) J)
    (hf0 : f 0 = (⟨p, (0 : E)⟩ : TangentBundle I M)) :
    ∀ t ∈ J, f t = (⟨p, (0 : E)⟩ : TangentBundle I M) := by
  set c : ℝ → TangentBundle I M :=
    fun _ : ℝ => (⟨p, (0 : E)⟩ : TangentBundle I M) with hc_def
  have hc_int : IsMIntegralCurve c (geodesicVectorField (I := I) g) :=
    isMIntegralCurve_const_zero_section (I := I) g p
  have hc_on : IsMIntegralCurveOn c (geodesicVectorField (I := I) g) J :=
    hc_int.isMIntegralCurveOn J
  have hfc : Set.EqOn f c J :=
    gvf_eqOn (I := I) g hJ_open hJ_conn h0J hf hc_on (by simpa [hc_def] using hf0)
  intro t ht
  simpa [hc_def] using hfc ht

end ZeroVelocityPropagation

section ExpMapZero

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem maximalGeodesicWitness_zero_curve_eq_p
    {g : SmoothRiemannianMetric I M} {p : M}
    {γ : ℝ → M} {J : Set ℝ}
    (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J) (h0J : (0 : ℝ) ∈ J)
    (hγ : IsGeodesicOnWithInitial (I := I) g γ J p (0 : TangentSpace I p)) :
    ∀ s ∈ J, γ s = p := by
  obtain ⟨f, hproj, hf0, hf_int⟩ := hγ
  intro s hs
  have hf_eq : f s = (⟨p, (0 : E)⟩ : TangentBundle I M) :=
    isMIntegralCurveOn_zero_section_eq_const (I := I) g p
      hJ_open hJ_conn h0J hf_int hf0 s hs
  have := hproj s
  rw [hf_eq] at this
  exact this.symm

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem expMap_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    expMap (I := I) g p (0 : TangentSpace I p) = p := by
  unfold expMap
  have h1 : (1 : ℝ) ∈ maximalGeodesicInterval (I := I) g p
      (0 : TangentSpace I p) :=
    maximalGeodesicWitness_zero_all_times (I := I) g p 1
  rw [maximalGeodesic_of_mem (I := I) (g := g) (p := p)
    (v := (0 : TangentSpace I p)) h1]
  obtain ⟨J, hJ_open, hJ_conn, h0J, h1J, hγ⟩ :=
    maximalGeodesicChosenCurve_spec (I := I) g p (0 : TangentSpace I p) h1
  exact maximalGeodesicWitness_zero_curve_eq_p (I := I)
    hJ_open hJ_conn h0J hγ 1 h1J

end ExpMapZero

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
