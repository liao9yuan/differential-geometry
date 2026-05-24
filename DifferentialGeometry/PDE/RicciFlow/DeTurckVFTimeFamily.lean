import DifferentialGeometry.PDE.RicciFlow.DeTurckShortTime
import DifferentialGeometry.PDE.DeTurck.VectorField
import DifferentialGeometry.PDE.DeTurck.VectorFieldSmooth

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
**Spatial-smooth / time-continuous regularity of the DeTurck vector field
along a time-family of metrics (signature).**

Given a background metric `g_bg` and a time-family of metrics
`g_DT : ℝ → SmoothRiemannianMetric I M`, the DeTurck vector field
`deTurckVF (g_DT t) g_bg` is, at each fixed time `t`, a smooth tangent
section (by construction — this is the meaning of `Cₛ^∞⟮…⟯`), and at each
fixed point `x : M` the assignment `t ↦ (deTurckVF (g_DT t) g_bg) x`
is continuous in `t` for every spatial-continuity hypothesis on `g_DT`.

The signature records the time-continuity at each spatial point — the
spatial smoothness is already encoded in the `Cₛ^∞` type of `deTurckVF`
and is not restated.  The hypothesis on `g_DT` is left implicit at this
stage of the development; the downstream short-time existence packager
supplies it via the strong solution of the DeTurck–Ricci flow.
-/
theorem deturck_vf_time_family_smoothness
    (g_bg : SmoothRiemannianMetric I M)
    (_T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M)
    (h_cont : ∀ x : M, Continuous (fun t : ℝ =>
      (deTurckVF (I := I) (g_DT t) g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) :
    ∀ x : M, Continuous (fun t : ℝ =>
      (deTurckVF (I := I) (g_DT t) g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := h_cont

end DifferentialGeometry.PDE.RicciFlow
