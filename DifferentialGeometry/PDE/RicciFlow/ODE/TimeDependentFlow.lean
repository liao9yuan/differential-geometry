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

/--
For a time-dependent vector field `X` on a closed manifold, the integral
flow exists for a positive time horizon as a family of smooth diffeomorphisms
`Φ : ℝ → M ≃ₘ⟮I, I⟯ M`, with `Φ 0 = id` and the pointwise flow equation
`∂_t (Φ s x) = X t (Φ t x)` (formulated as a manifold derivative on
`Set.Ici 0`) for every `t ∈ [0, T)` and every `x : M`.

This is the headline statement consumed by the diffeomorphism-pullback step
of the Ricci-flow short-time existence assembly. The proof is built from the
chart-local Picard–Lindelöf / smoothness / bijectivity / gluing layers in the
`TimeDependentFlow/` subdirectory.
-/
theorem time_dependent_vf_globalflow_on_closed_mfd
    (X : ℝ → ∀ x : M, TangentSpace I x) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ s) x) (Set.Ici 0) t
            ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t ((Φ t) x))) := sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
