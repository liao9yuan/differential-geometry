/-
Authors: Jack McCarthy
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom

noncomputable section

namespace Bundle

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B : Type*}
variable (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)]

abbrev dual : B → Type _ :=
  fun x => E x →L[𝕜] 𝕜

end Bundle

open scoped Manifold ContDiff

universe u

private abbrev I := modelWithCornersSelf ℂ ℂ

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold I ω X]

abbrev CotangentSpace (x : X) := Bundle.dual ℂ (TangentSpace I) x

def CotangentBundle := Bundle.TotalSpace (ℂ →L[ℂ] ℂ) (Bundle.dual ℂ (TangentSpace I : X → Type _))

/-! ### 1-forms -/

/-- A holomorphic 1-form -/
def OneForm := Cₛ^1⟮I; ℂ →L[ℂ] ℂ, (CotangentSpace : X → Type _)⟯

namespace OneForm

/-- 1-forms are an additive, commutative group -/
instance instAddCommGroup : AddCommGroup (OneForm (X := X)) :=
  ContMDiffSection.instAddCommGroup

/-- 1-forms are a module over `ℂ` -/
instance instModule : Module ℂ (OneForm (X := X)) :=
  ContMDiffSection.instModule

end OneForm

/-- The genus of a compact Riemann surface is the dimension of its space of holomorphic 1-forms. -/
def genus : ℕ := Module.finrank ℂ (OneForm (X := X))

end
