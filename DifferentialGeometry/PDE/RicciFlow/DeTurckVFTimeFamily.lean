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
should be continuous in `t` whenever `g_DT` enjoys an appropriate
spatial-`C¹` time-continuity hypothesis.

The signature records the time-continuity at each spatial point — the
spatial smoothness is already encoded in the `Cₛ^∞` type of `deTurckVF`
and is not restated.

Missing prerequisites (none currently substantiated in the project):
  1. A genuine time-regularity hypothesis on `g_DT`.  As stated the
     theorem is vacuously false for an arbitrary `g_DT` (no link
     between `g_DT t₁` and `g_DT t₂` is assumed).  The intended
     hypothesis is `t ↦ (g_DT t).inner x v w` continuous on `[0, T)`
     for every `x, v, w` — i.e. the conclusion of
     `maxreg_solution_in_c1_via_sobolev_embedding`
     (`PDE/RicciFlow/DeTurckSolutionC1.lean`).  It is not yet exposed
     in this signature.
  2. Continuity of the assignment `g ↦ deTurckVF g g_bg` in the
     `C¹`-section topology.  In a chart its components are
     `W^i(g) = g^{jk}(Γ^i_{jk}(g) − Γ̄^i_{jk}(g_bg))`, a rational
     expression in `(g, ∂g)` whose continuous dependence on the
     inputs is the content of `deturck_vf_continuous_in_c1_input`.
     That lemma is itself currently a packaging stub (the chart-formula
     ↦ inverse-Gram-+-Christoffel substantive proof has not been
     written in the project).
-/
theorem deturck_vf_time_family_smoothness
    (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (g_DT : ℝ → SmoothRiemannianMetric I M) :
    ∀ x : M, Continuous (fun t : ℝ =>
      (deTurckVF (I := I) (g_DT t) g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := sorry

end DifferentialGeometry.PDE.RicciFlow
