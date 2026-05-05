import DifferentialGeometry.VectorBundle.Frame
import DifferentialGeometry.VectorBundle.Section
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# SmoothExtension: Extending a locally smooth tangent-section to a global smooth section

Phase B, substep B.2 of the Realization programme.

## Summary

Given a raw tangent-section `σ : Π x : M, TangentSpace I x` that is `ContMDiffOn ∞`
(in total-space form) on an open neighborhood `u` of `x₀`, this file produces a
globally smooth `ContMDiffSection` that agrees with `σ` on a neighborhood of `x₀`.

## Note on the hypothesis

The substep B.2 task originally specified the hypothesis as `ContMDiffAt I (I.prod 𝓘(ℝ,E)) ∞`
at the single point `x₀`. However, that hypothesis is mathematically insufficient to
produce a globally `C^∞` extension with germ-equality at `x₀`: a function that is
`ContMDiffAt ∞` at a single point is not, in general, `ContMDiff ∞` on any
neighborhood of that point (the neighborhoods of smoothness in `ContMDiffAt ∞`
may shrink with the smoothness order). Indeed, if `σ' =ᶠ[𝓝 x₀] σ` and `σ'` is
globally `C^∞`, then `σ` must itself be `C^∞` on the same neighborhood — a
strictly stronger condition than `ContMDiffAt ∞`.

We therefore strengthen the hypothesis to `ContMDiffOn I (I.prod 𝓘(ℝ,E)) ∞ σ_total u`
on an open neighborhood `u` of `x₀`. This matches the existing codebase idiom
(`exists_contMDiffSection_eqOn_nhd` in `DifferentialGeometry/VectorBundle/Frame.lean`)
and is the natural hypothesis for a germ-extension theorem.

## Main declarations

* `smoothExtensionAt` — given `σ` smooth on a neighborhood of `x₀`, produces a
  globally smooth section `σ' : Cₛ^∞⟮I; E, TangentSpace I⟯`.
* `smoothExtensionAt_eventuallyEq` — `σ'` agrees with `σ` on a neighborhood of `x₀`.

## Implementation

We use the pre-existing lemma `exists_contMDiffSection_eqOn_nhd` from
`DifferentialGeometry/VectorBundle/Frame.lean`. That lemma takes a family of
sections that are smooth on an open neighborhood of a point and produces globally
smooth extensions via bump-multiplication. Here we apply it to the singleton
family `{σ}`, giving a single global extension.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Bundle Filter

noncomputable section

namespace Realization

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- Given a raw tangent-section `σ` that is `ContMDiffOn ∞` in total-space form on
an open neighborhood `u` of `x₀`, extract a globally smooth tangent-section
`σ' : Cₛ^∞⟮I; E, TangentSpace I⟯` that agrees with `σ` on a neighborhood of `x₀`. -/
noncomputable def smoothExtensionAt
    (σ : Π x : M, TangentSpace I x) (x₀ : M) {u : Set M} (hu : IsOpen u) (hx : x₀ ∈ u)
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) u) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  -- Feed the singleton family `fun _ : Unit => σ` into `exists_contMDiffSection_eqOn_nhd`.
  -- The result is a family `s' : Unit → Cₛ^∞⟮...⟯` with `s' () =ᶠ σ` at `x₀`.
  -- We then take `s' ()`.
  (Classical.choose
    (exists_contMDiffSection_eqOn_nhd
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (ι := Unit) (s := fun _ => σ) (u := u) (n := ⊤)
      (fun _ => hσ) hu hx)) ()

/-- The `smoothExtensionAt` extension agrees with the original section on a
neighborhood of `x₀`. -/
theorem smoothExtensionAt_eventuallyEq
    (σ : Π x : M, TangentSpace I x) (x₀ : M) {u : Set M} (hu : IsOpen u) (hx : x₀ ∈ u)
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, σ y⟩ : TotalSpace E (TangentSpace I))) u) :
    (⇑(smoothExtensionAt I M σ x₀ hu hx hσ) : Π x, TangentSpace I x) =ᶠ[𝓝 x₀] σ := by
  -- The `Classical.choose_spec` gives us the eventual-equality on `Unit`-indexed
  -- families, from which we extract the Unit () case.
  have hspec := Classical.choose_spec
    (exists_contMDiffSection_eqOn_nhd
      (I := I) (F := E) (V := (TangentSpace I : M → Type _))
      (ι := Unit) (s := fun _ => σ) (u := u) (n := ⊤)
      (fun _ => hσ) hu hx)
  -- `hspec : ∀ᶠ x in 𝓝 x₀, ∀ i : Unit, (Classical.choose ...) i x = σ x`
  filter_upwards [hspec] with x hx_eq
  exact hx_eq ()

/-! ### Sanity check

For a globally smooth section `Y`, feeding `⇑Y` (on the whole manifold, which is open)
produces an extension that agrees with `Y` on a neighborhood of `x₀`. -/

example (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    (⇑(smoothExtensionAt I M (⇑Y) x₀ (u := Set.univ) isOpen_univ (Set.mem_univ _)
      (fun y _ => (Y.contMDiff y).contMDiffWithinAt))
      : Π x, TangentSpace I x) =ᶠ[𝓝 x₀] (⇑Y : Π x, TangentSpace I x) :=
  smoothExtensionAt_eventuallyEq I M (⇑Y) x₀ isOpen_univ (Set.mem_univ _)
    (fun y _ => (Y.contMDiff y).contMDiffWithinAt)

end Realization

end
