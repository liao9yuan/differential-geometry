import DifferentialGeometry.Analysis.Sobolev.Manifold.Lipschitz
import DifferentialGeometry.Geometry.Comparison.BusemannLine

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Metric Set Topology
open scoped Bundle ENNReal Manifold NNReal

namespace DifferentialGeometry

open Analysis.Sobolev
open Geometry.Riemannian
open Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
/-- On a sufficiently small Euclidean chart ball, the sum of the two Busemann
functions determined by a minimizing line belongs to `W^{1,2}`. -/
theorem buse_pair_memW1p
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {gamma : ℝ → M} (hgamma : IsMinimizingLine (I := I) g gamma) (alpha : M) :
    ∃ r : ℝ, 0 < r ∧
      DeGiorgi.MemW1p 2
        (Chart.chartPushedRaw (I := I) (M := M) alpha (fun x : M ↦
          busemann (I := I) gamma x +
            busemann (I := I) (fun t : ℝ ↦ gamma (-t)) x))
        (Metric.ball
          (toEuclidean (E := E) (extChartAt I alpha alpha)) r) := by
  classical
  let u : M → ℝ := fun x ↦
    busemann (I := I) gamma x +
      busemann (I := I) (fun t : ℝ ↦ gamma (-t)) x
  have hpos : ∀ x y, edist (busemann (I := I) gamma x)
      (busemann (I := I) gamma y) ≤
      (1 : ENNReal) * riemannianEDistOf (I := I) g x y := by
    intro x y
    rw [one_mul, riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnorm, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_toReal (Exponential.riemannianEDist_ne_top (I := I) x y)]
    exact ENNReal.ofReal_le_ofReal (busemann_dist (I := I) hgamma.pos_ray x y)
  have hneg : ∀ x y, edist (busemann (I := I) (fun t : ℝ ↦ gamma (-t)) x)
      (busemann (I := I) (fun t : ℝ ↦ gamma (-t)) y) ≤
      (1 : ENNReal) * riemannianEDistOf (I := I) g x y := by
    intro x y
    rw [one_mul, riemannianEDistOf_eq_riemannianEDist
      (I := I) g hEnorm, edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_toReal (Exponential.riemannianEDist_ne_top (I := I) x y)]
    exact ENNReal.ofReal_le_ofReal (busemann_dist (I := I) hgamma.neg_ray x y)
  have hu : ∀ x y, edist (u x) (u y) ≤
      (2 : ENNReal) * riemannianEDistOf (I := I) g x y := by
    intro x y
    calc
      edist (u x) (u y) ≤
          edist (busemann (I := I) gamma x) (busemann (I := I) gamma y) +
            edist (busemann (I := I) (fun t : ℝ ↦ gamma (-t)) x)
              (busemann (I := I) (fun t : ℝ ↦ gamma (-t)) y) := by
        exact edist_add_add_le _ _ _ _
      _ ≤ riemannianEDistOf (I := I) g x y +
          riemannianEDistOf (I := I) g x y := by
        simpa only [one_mul] using add_le_add (hpos x y) (hneg x y)
      _ = (2 : ENNReal) * riemannianEDistOf (I := I) g x y := by
        rw [two_mul]
  simpa only [u] using
    Chart.raw_memW1p_of_lip (I := I) g alpha hu

end DifferentialGeometry
