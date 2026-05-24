import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.PointwiseLocal
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.UniformExistence
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Glue
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.MFDerivPackage

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem time_dependent_vf_globalflow_on_closed_mfd
    (X : ℝ → ∀ x : M, TangentSpace I x) :
    ∃ T : ℝ, 0 < T := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
