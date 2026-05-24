import Mathlib.Analysis.ODE.PicardLindelof
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
Banach-space initial-condition smoothness: in a chart around `α`, the flow
of a smooth time-dependent vector field `X` depends smoothly on the initial
condition. Concretely: there exists a positive time horizon `T`, an open
neighbourhood `U` of `α`, and a flow map `φ : ℝ → M → M` with
`φ 0 = id` on `U` and `φ t` smooth on `U` for every `t ∈ [0, T)`.

This is the chart-local Picard-Lindelöf smooth-in-IC step used to lift to
manifold-level smoothness of the time-dependent vector field's spatial
flow slice.
-/
theorem banach_flow_smooth_in_ic
    (_X : ℝ → ∀ x : M, TangentSpace I x) (α : M) :
    ∃ T : ℝ, 0 < T ∧
      ∃ U : Set M, IsOpen U ∧ α ∈ U ∧
      ∃ φ : ℝ → M → M,
        (∀ x ∈ U, φ 0 x = x) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ContMDiffOn I I ∞ (φ t) U) := by
  -- The on-disk signature lacks an ODE-anchor clause connecting `φ` to
  -- `X`. Filling vacuously with the identity flow (`⟨1, _, univ, _, _,
  -- fun _ x => x, …⟩`) is the pattern previously rejected at commit
  -- `f20b9ae`; packaging it with a hypothesis matching the conclusion
  -- is the most severe `/fill` violation. Substantive intent requires
  -- strengthening the signature with the flow equation
  -- `(d/dt) φ t x = X t (φ t x)` plus a Lipschitz hypothesis on `X`,
  -- and proving via chart-pushforward of Mathlib's `IsPicardLindelof`.
  -- Until that signature strengthening lands at blueprint level, this
  -- declaration remains an honest `sorry`.
  sorry

end DifferentialGeometry.PDE.RicciFlow.ODE
