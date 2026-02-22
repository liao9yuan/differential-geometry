import DifferentialGeometry.Algebra.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Smooth Bilinear Form
Algebraic formulation of a (0,2)-tensor.
-/

variable (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]

/-- Smooth Bilinear Form structure enforcing bilinearity.
Input: (V, V)
Output: R -/
structure SmoothBilinearForm where
  val : V → V → R
  add_left : ∀ X₁ X₂ Y : V, val (X₁ + X₂) Y = val X₁ Y + val X₂ Y
  smul_left : ∀ (a : R) (X Y : V), val (a • X) Y = a * val X Y
  add_right : ∀ X Y₁ Y₂ : V, val X (Y₁ + Y₂) = val X Y₁ + val X Y₂
  smul_right : ∀ (a : R) (X Y : V), val X (a • Y) = a * val X Y

/-- Coercion from `SmoothBilinearForm R V` to a function `V → V → R`, allowing function evaluation syntax `T X Y`.
Input: (SmoothBilinearForm R V)
Output: V → V → R -/
instance : CoeFun (SmoothBilinearForm R V) (fun _ => V → V → R) where
  coe T := T.val

/-- Extensionality lemma for smooth bilinear forms.
Prove that two smooth bilinear forms are identically equal if their evaluations on all vector fields match.
Input: (SmoothBilinearForm R V, SmoothBilinearForm R V)
Output: Prop -/
@[ext]
lemma ext (T₁ T₂ : SmoothBilinearForm R V) (h : ∀ X Y : V, T₁ X Y = T₂ X Y) : T₁ = T₂ := by
  cases T₁
  cases T₂
  congr
  funext X Y
  exact h X Y

/-- Defines the zero smooth bilinear form which returns the zero element of `R` for any vector fields.
Input: (R, V)
Output: Zero (SmoothBilinearForm R V) -/
instance : Zero (SmoothBilinearForm R V) where
  zero := {
    val := fun _ _ => 0
    add_left := by simp
    smul_left := by simp
    add_right := by simp
    smul_right := by simp
  }
