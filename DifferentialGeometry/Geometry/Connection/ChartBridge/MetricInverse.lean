import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Tensor.RSTensor.CotangentRiemannian
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem chartInvGram_inverse
    (g : SmoothRiemannianMetric I M) (alpha : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) alpha).baseSet) :
    MetricInverseInBasis_gen (I := I) g x
      (chartBasisFamily (I := I) alpha hx)
      (fun i j => chartInvGramMatrix (I := I) g alpha x i j) := by
  classical
  have hgram : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (chartBasisFamily (I := I) alpha hx i)
          (chartBasisFamily (I := I) alpha hx j) =
        chartGramMatrix (I := I) g alpha x i j := by
    intro i j
    rw [chartBasisFamily_apply, chartBasisFamily_apply]
    exact (chartGramMatrix_apply (I := I) g alpha x i j).symm
  intro i j
  refine ⟨?_, ?_⟩
  · simp only [hgram]
    rw [← Matrix.mul_apply,
      chartInvGramMatrix_mul_chartGramMatrix (I := I) g alpha hx,
      Matrix.one_apply]
  · simp only [hgram]
    rw [← Matrix.mul_apply,
      chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hx,
      Matrix.one_apply]

omit [FiniteDimensional ℝ E] in
theorem metricInverseInBasis_identity_of_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0) :
    MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)) := by
  classical
  intro i j
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_eq_single i]
    · rw [identityInvMetric_apply_self, one_mul]
      exact horth i j
    · intro k _ hk
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne (fun h => hk h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Finset.sum_eq_single j]
    · rw [identityInvMetric_apply_self, mul_one]
      exact horth i j
    · intro k _ hk
      rw [identityInvMetric, diagonalInvMetric_eq_zero_of_ne hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h

end DifferentialGeometry.Geometry.Connection
