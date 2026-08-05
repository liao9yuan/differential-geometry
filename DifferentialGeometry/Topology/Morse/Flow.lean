import DifferentialGeometry.Topology.Morse.Defs
import Mathlib.Geometry.Manifold.Diffeomorph

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open scoped Manifold

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H}
variable (f : M → ℝ) (a b : ℝ)

-- A normalized gradient-like flow: it translates the value of f at unit speed
-- on the strip f⁻¹([a, b]).
structure GradientLikeFlow (I : ModelWithCorners ℝ E H) (f : M → ℝ) (a b : ℝ) where
  flow : ℝ → M → M
  flow_zero : ∀ x : M, flow 0 x = x
  flow_add : ∀ s t : ℝ, flow (s + t) = flow s ∘ flow t
  contMDiffAt : ∀ t : ℝ, ∀ x : M, ContMDiffAt I I (⊤ : WithTop ℕ∞) (fun x : M => flow t x) x
  contMDiffAt_t : ∀ x : M, ContMDiffAt 𝓘(ℝ, ℝ) I (⊤ : WithTop ℕ∞) (fun t : ℝ => flow t x) (0 : ℝ)
  map_mono : ∀ x : M, ∀ t : ℝ, x ∈ sublevel f b → t ∈ Set.Icc 0 (b - a) →
    f (flow t x) = f x - t

-- The time-t map of a gradient-like flow is a diffeomorphism of the manifold.
def GradientLikeFlow.toDiffeomorph (Φ : GradientLikeFlow I f a b) (t : ℝ) :
    Diffeomorph I I M M (⊤ : WithTop ℕ∞) where
  toEquiv :=
    { toFun := Φ.flow t
      invFun := Φ.flow (-t)
      left_inv := by
        intro x
        have h := congrFun (Φ.flow_add (-t) t) x
        change Φ.flow (-t) (Φ.flow t x) = x
        calc
          Φ.flow (-t) (Φ.flow t x) = (Φ.flow (-t) ∘ Φ.flow t) x := rfl
          _ = Φ.flow (-t + t) x := h.symm
          _ = Φ.flow 0 x := by simp
          _ = x := Φ.flow_zero x
      right_inv := by
        intro x
        have h := congrFun (Φ.flow_add t (-t)) x
        change Φ.flow t (Φ.flow (-t) x) = x
        calc
          Φ.flow t (Φ.flow (-t) x) = (Φ.flow t ∘ Φ.flow (-t)) x := rfl
          _ = Φ.flow (t + -t) x := h.symm
          _ = Φ.flow 0 x := by simp
          _ = x := Φ.flow_zero x }
  contMDiff_toFun := Φ.contMDiffAt t
  contMDiff_invFun := Φ.contMDiffAt (-t)

end

end DifferentialGeometry.Topology.Morse
