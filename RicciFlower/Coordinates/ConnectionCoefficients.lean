import RicciFlower.Coordinates.Christoffel
import RicciFlower.Coordinates.CoordinateFrame
import RicciFlower.Tensor.RSTensor.NablaOnTensors

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coordinate connection coefficients

This file contains the bridge between the fixed-chart connection endomorphism
used by `NablaOnTensors` and the Christoffel coefficients in the chart-induced
coordinate frame.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle Set TensorLieDeriv Filter
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I (⊤ : WithTop ℕ∞) M]
variable [IsManifold I ((⊤ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace Real]

/-- A chart-constant tangent field for a model basis vector agrees near the
base point with the corresponding coordinate-frame vector field. -/
theorem tangentConstInChart_eq_coordinateFrame_eventually
    (x₀ : M) (i : CoordinateIdx E) :
    (tangentConstInChart (𝕜 := Real) (I := I) x₀ ((Module.finBasis Real E) i) :
        (x : M) → TangentSpace I x) =ᶠ[𝓝 x₀]
      coordinateFrameAt (I := I) x₀ i := by
  filter_upwards
    [((coordinateTrivializationAt (I := I) x₀).open_baseSet.mem_nhds
      (coordinateFrameAt_mem (I := I) x₀))] with x hx
  have hx_src : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  rw [tangentConstInChart_apply]
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hx_src]
  rw [coordinateFrameAt_apply_of_mem (I := I) (x₀ := x₀) (x := x) hx i]
  rfl

set_option linter.flexible false in
/-- Model connection coefficients agree with coordinate-frame Christoffel
coefficients in the chart-induced coordinate frame. -/
theorem connCoeff_eq_christoffelAlong_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (j k : CoordinateIdx E) :
    connectionEndomorphismCoeff (𝕜 := Real) (E := E) (Module.finBasis Real E)
        (connectionEndomorphismInChart (𝕜 := Real) (I := I) cov X x₀
          (extChartAt I x₀ x₀)) j k =
      christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        x₀ (X x₀) j k := by
  classical
  let e := coordinateTrivializationAt (I := I) x₀
  have hx_base : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hconst :
      MDiffAt
        (T% (tangentConstInChart (𝕜 := Real) (I := I) x₀
          ((Module.finBasis Real E) j) : (x : M) → TangentSpace I x)) x₀ :=
    mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x₀) (p := x₀)
      ((Module.finBasis Real E) j) hx_base
  have hframe :
      MDiffAt (T% (coordinateFrameAt (I := I) x₀ j)) x₀ :=
    ((coordinateFrameAt_isLocalFrame_one (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j).mdifferentiableAt one_ne_zero
  have hcov :
      cov (tangentConstInChart (𝕜 := Real) (I := I) x₀
            ((Module.finBasis Real E) j)) x₀ =
        cov (coordinateFrameAt (I := I) x₀ j) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hconst hframe
      (by simp)
      (tangentConstInChart_eq_coordinateFrame_eventually (I := I) x₀ j)
  unfold connectionEndomorphismCoeff christoffelAlongInFrame
  rw [connectionEndomorphismInChart_apply_of_mem
    (𝕜 := Real) (I := I) cov X x₀ (mem_extChartAt_target x₀)
    ((Module.finBasis Real E) j)]
  rw [extChartAt_to_inv]
  rw [hcov]
  rw [coordinateFrameAt_coeff_eq_toBasis_coord]
  rw [coordinateFrameAt_toBasis_eq_finBasis]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I) (x₀ := x₀) (x := x₀) (mem_chart_source H x₀)]
  rw [mfderiv_extChartAt_self]
  rfl

end Coordinates
end RicciFlower
