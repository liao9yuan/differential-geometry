import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Glue
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.BanachIC
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.ChartGlue
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
For a time-dependent vector field `X` on a closed manifold, the global flow
`Φ : ℝ → M → M` produced by `time_dependent_vf_global_flow_glue` is, at every
fixed time `t < T`, a smooth self-map of `M`.

The flow `Φ`, its horizon `T`, and the initial-condition / flow-equation
hypotheses are supplied as arguments so that the smoothness conclusion is
stated about the same flow used downstream in
`time_dependent_vf_globalflow_on_closed_mfd`.
-/
theorem time_dependent_vf_flow_smooth_in_space
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (T : ℝ) (_hT : 0 < T) (Φ : ℝ → M → M)
    (_hInit : ∀ x : M, Φ 0 x = x)
    (_hFlow : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici 0) t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ t x)))) :
    ∀ t : ℝ, t < T → ContMDiff I I ∞ (Φ t) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
