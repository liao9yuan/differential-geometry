import DifferentialGeometry.Metric.Basic
import DifferentialGeometry.PDE.DeTurck.Transformation
import DifferentialGeometry.PDE.ParabolicShortTime
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Chart-component witnesses for an abstract metric operator

Type-level scaffolding for the chart-component smoothness and chart-component
symmetry of an abstract operator `F` on smooth Riemannian metrics, in the shape
consumed by the Phase 7/8 quasi-linear short-time existence pipeline.
-/

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open Bundle MeasureTheory
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Chart-component smoothness witness for an abstract metric operator `F`
under the hypothesis that `F` has smooth quasi-linear dependence on metric data:
for every metric `g`, basepoint `α`, and pair of model-basis indices `(i, j)`,
the scalar function `x ↦ F g x (chartModelBasis E i) (chartModelBasis E j)` is
`C^∞` on the chart source at `α`.

This is a projection from the first conjunct of `IsSmoothQuasilinearMetricRHS`.
Shape patterned on `chartDeTurckOpMatrix_contMDiffOn`
(`PDE/DeTurck/Transformation.lean`). -/
theorem F_canonical_chart_component_smooth
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hF : DifferentialGeometry.PDE.IsSmoothQuasilinearMetricRHS (I := I) F)
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => F g x (chartModelBasis E i) (chartModelBasis E j))
      (chartAt H α).source :=
  hF.1 g α i j

/-- Chart-component symmetry witness for an abstract metric operator `F`
under the hypothesis that `F`'s output is symmetric in its two tangent-vector
arguments: at every basepoint `x`, the chart-matrix entries
`F g x (chartModelBasis E i) (chartModelBasis E j)` are symmetric in the
pair of model-basis indices `(i, j)`.

Shape patterned on `chartDeTurckOpMatrix_symm`
(`PDE/DeTurck/Transformation.lean`). -/
theorem F_chart_component_symmetric
    (F : SmoothRiemannianMetric I M →
         (∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
    (hSymm : ∀ (g : SmoothRiemannianMetric I M) (x : M)
      (v w : TangentSpace I x), F g x v w = F g x w v)
    (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    F g x (chartModelBasis E i) (chartModelBasis E j)
      = F g x (chartModelBasis E j) (chartModelBasis E i) :=
  hSymm g x (chartModelBasis E i) (chartModelBasis E j)

end RicciFlow
end PDE
end DifferentialGeometry
