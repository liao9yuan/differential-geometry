import DifferentialGeometry.Geometry.Metric.ChartGram

/-!
# Chart-basis metric readouts

This module records the two basic chart-frame identities used by coordinate
metric calculations: evaluation of the metric on chart-basis vectors and
recomposition of a tangent vector from its chart-basis coordinates.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Evaluation of `g.inner x` on two chart-basis frame vectors recovers the
chart Gram matrix entry. -/
lemma g_inner_eq_chartGramMatrix_basis
    (g : SmoothRiemannianMetric I M) (α : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) =
      chartGramMatrix (I := I) g α x i j :=
  (chartGramMatrix_apply (I := I) g α x i j).symm

/-- Decomposition of a tangent vector in the chart-basis frame: at any point of
the trivialization base set, `v` is the sum over `i` of the trivialization
coordinates of `v` scaled by the chart-basis frame vectors. -/
lemma chartBasisVecFiber_recompose
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr
          ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)) i •
        chartBasisVecFiber (I := I) α i x := by
  classical
  set T : Bundle.Trivialization E
      (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  have hsymm_apply :
      T.symmL ℝ x (T.continuousLinearMapAt ℝ x v) = v :=
    T.symmL_continuousLinearMapAt (R := ℝ) hx v
  set vE : E := T.continuousLinearMapAt ℝ x v with hvE_def
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  have hdecomp : vE = ∑ i, b.repr vE i • b i :=
    (Module.Basis.sum_repr b vE).symm
  have hsymm_sum := congrArg (T.symmL ℝ x) hdecomp
  rw [hsymm_apply] at hsymm_sum
  rw [map_sum] at hsymm_sum
  have hbasis : ∀ i, T.symmL ℝ x (b i) = chartBasisVecFiber (I := I) α i x := by
    intro i
    rfl
  rw [hsymm_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, hbasis i]

end Connection
end Integral
end DifferentialGeometry
