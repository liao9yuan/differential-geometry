import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.BanachIC
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
A self-map `f : M → M` that is `C^∞` when read through every chart of an
atlas is globally `C^∞` on `M`. This is the chart-glue step used to lift
chart-local smooth-in-IC of the Picard-Lindelöf flow to manifold-level
smoothness of the time-dependent vector field's spatial flow slice.

Signature shape: from chart-local smoothness of `f` at every point of `M`,
in the sense of `ContMDiffAt I I ∞ f x`, conclude `ContMDiff I I ∞ f`.
-/
theorem chart_glue_smooth_of_chart_local_smooth
    (f : M → M)
    (h : ∀ x : M, ContMDiffAt I I ∞ f x) :
    ContMDiff I I ∞ f := h

end DifferentialGeometry.PDE.RicciFlow.ODE
