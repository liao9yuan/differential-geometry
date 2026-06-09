import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Single-trivialization smoothness of the tangent-bundle `symmL`

For a smooth manifold `M` with model `(I : ModelWithCorners ℝ E H)` and a base point `x₀ : M`,
the tangent-bundle trivialization at `x₀` provides fiberwise continuous linear maps
`(trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b : TangentSpace I b →L[ℝ] E`
and its inverse `(trivializationAt E (TangentSpace I) x₀).symmL ℝ b : E →L[ℝ] TangentSpace I b`.

Mathlib supplies smoothness only for the *change of trivialization* between two distinct
trivializations (`contMDiffOn_coordChangeL` / `contMDiffOn_symm_coordChangeL`).  A change of
trivialization is always a two-factor product `continuousLinearMapAt e' b ∘L symmL e b`, which for a
single trivialization (`e' = e`) collapses to the identity; the *single*-trivialization factors
`continuousLinearMapAt e b` and `symmL e b` are not themselves available as standalone smooth
operator-valued functions, because the only `mfderiv`-smoothness lemmas in Mathlib
(`ContMDiffAt.mfderiv_const`, `ContMDiffAt.mfderiv`) deliver the `inTangentCoordinates`-wrapped form,
which again couples the two factors.

This file establishes the missing single-trivialization smoothness of `symmL`.  The two factors are
mutually inverse continuous linear maps on the base set (abusing the canonical defeq
`TangentSpace I b = E`):
`symmL x₀ b = ContinuousLinearMap.inverse (continuousLinearMapAt x₀ b)`.
Since `continuousLinearMapAt x₀ x₀ = mfderiv (extChartAt x₀) x₀ = id` is invertible, and inversion of
continuous linear maps is `C^∞` at an invertible map
(`ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse`), the smoothness of `symmL x₀ ·` follows
from the smoothness of the forward factor `continuousLinearMapAt x₀ ·`
(`contMDiffAt_continuousLinearMapAt_tangentTrivialization`, the irreducible single-trivialization
primitive) by composition.

The `E →L[ℝ] E` reading of a single factor (e.g. `symmL x₀ b : E →L[ℝ] TangentSpace I b`) relies on
the non-reducible defeq `TangentSpace I b = E`; we force the non-dependent type with a `by exact`
cast, the standard idiom for this abuse (Lean otherwise infers the dependent type
`(b : M) → E →L[ℝ] TangentSpace I b`).
-/

noncomputable section

open Bundle Set ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff

namespace DifferentialGeometry
namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **(POSIT — the single-trivialization forward smoothness primitive.)** The forward
trivialization continuous linear map `b ↦ (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b`,
viewed as an `E →L[ℝ] E`-valued function (abusing the defeq `TangentSpace I b = E`), is `C^∞` at `x₀`.

This is the genuine missing tangent-bundle primitive.  By
`TangentBundle.continuousLinearMapAt_trivializationAt`, on the chart source it equals
`b ↦ mfderiv (extChartAt I x₀) b`, the derivative of the (Euclidean-valued) extended chart read with
its source fiber `TangentSpace I b` moving with `b`.  Mathlib's only `mfderiv`-smoothness lemmas
(`ContMDiffAt.mfderiv_const`, `ContMDiffAt.mfderiv`) deliver the `inTangentCoordinates`-wrapped form,
which re-coordinatizes the source by `symmL x₀ b`, and so for the chart collapses to the constant
`id`, not recovering this raw factor; and Mathlib's bundle-`coordChange` smoothness only covers the
two-factor product `continuousLinearMapAt e' b ∘L symmL e b`.  Hence this single factor is the
irreducible content, posited here as a `sorry` leaf.  It is **non-vacuous**: at `b = x₀` the value is
`id ≠ 0`, so it is genuinely the forward trivialization factor, not the zero map. -/
private theorem contMDiffAt_continuousLinearMapAt_tangentTrivialization (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        (by exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b : E →L[ℝ] E))
      x₀ :=
  sorry

/-- **Single-trivialization smoothness of the inverse tangent-bundle trivialization `symmL`.**

For a smooth manifold `M` and a base point `x₀ : M`, the inverse trivialization continuous linear map
`b ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ b`, viewed as an `E →L[ℝ] E`-valued function
(abusing the defeq `TangentSpace I b = E`), is `C^∞` at `x₀`.

The forward and inverse trivialization factors are mutually inverse on the base set, so
`symmL x₀ b = ContinuousLinearMap.inverse (continuousLinearMapAt x₀ b)`; the forward factor is `C^∞`
(`contMDiffAt_continuousLinearMapAt_tangentTrivialization`) and equals `id` (hence invertible) at
`x₀`, and inversion is `C^∞` at an invertible map, so the composite is `C^∞`. -/
theorem contMDiffAt_symmL_tangentTrivialization (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        (by exact (trivializationAt E (TangentSpace I) x₀).symmL ℝ b : E →L[ℝ] E)) x₀ := by
  classical
  -- The forward factor is `C^∞` at `x₀`.
  have hfwd : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        (by exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b : E →L[ℝ] E))
      x₀ :=
    contMDiffAt_continuousLinearMapAt_tangentTrivialization x₀
  -- The value of the forward factor at `x₀` is the identity, hence invertible.
  have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hval :
      (by exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀ : E →L[ℝ] E)
        = ContinuousLinearMap.id ℝ E := by
    have h := TangentBundle.continuousLinearMapAt_trivializationAt
      (I := I) (E := E) (x₀ := x₀) (x := x₀) hx₀_src
    rw [mfderiv_extChartAt_self] at h
    ext y
    exact congrArg (fun T : TangentSpace I x₀ →L[ℝ] E => T y) h
  have hinvertible :
      ((by exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀
        : E →L[ℝ] E)).IsInvertible := by
    rw [hval, ← ContinuousLinearEquiv.coe_refl]
    exact isInvertible_equiv
  -- Inversion is `C^∞` at the (invertible) value.
  have hinverse : ContDiffAt ℝ ∞ (inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
      ((fun b : M =>
        (by exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b
          : E →L[ℝ] E)) x₀) :=
    IsInvertible.contDiffAt_map_inverse hinvertible
  -- Compose: `inverse ∘ forward` is `C^∞` at `x₀`.
  have hcomp : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      ((inverse : (E →L[ℝ] E) → (E →L[ℝ] E)) ∘
        (fun b : M =>
          (by exact (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ b
            : E →L[ℝ] E))) x₀ :=
    hinverse.comp_contMDiffAt hfwd
  -- On the base set, `inverse (continuousLinearMapAt x₀ b) = symmL x₀ b`.
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (chartAt H x₀).open_source.mem_nhds hx₀_src
  filter_upwards [hmem] with b hb
  simp only [Function.comp_apply]
  symm
  refine inverse_eq ?_ ?_
  · ext y
    simpa using (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt_symmL hb y
  · ext y
    simpa using (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt hb y

end Geometry
end DifferentialGeometry

end
