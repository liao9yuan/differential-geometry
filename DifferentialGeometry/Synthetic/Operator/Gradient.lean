import DifferentialGeometry.Synthetic.Algebra.Metric
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Gradient Operator
-/

section GradientDefs

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- The covector df: X ↦ X(f), as an R-linear map. -/
def df_covector (emb : DerivationEmbedding k R V) (u : R) : V →ₗ[R] R where
  toFun X := action emb X u
  map_add' X Y := action_add_left emb X Y u
  map_smul' c X := by simp [action_smul_left emb c X u, smul_eq_mul]

/-- Gradient of a scalar function `u`.
    grad(u) = sharp(df), the vector field metrically dual to the covector df. -/
noncomputable def grad (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (u : R) : V :=
  met.sharp (df_covector emb u)

lemma g_grad (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (u : R) (X : V) :
    met.g (grad emb met u) X = action emb X u :=
  met.g_sharp (df_covector emb u) X

lemma grad_add (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (f g : R) :
    grad emb met (f + g) = grad emb met f + grad emb met g := by
  apply met.eq_of_forall_g_eq; intro Z
  -- goal is g_tensor ![...] ![] = g_tensor ![...] ![]; these are defeq to met.g ... Z
  change met.g (grad emb met (f + g)) Z =
       met.g (grad emb met f + grad emb met g) Z
  rw [met.g_add_left, g_grad, g_grad, g_grad, action_add_right]

lemma grad_sub (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (f g : R) :
    grad emb met (f - g) = grad emb met f - grad emb met g := by
  apply met.eq_of_forall_g_eq; intro Z
  change met.g (grad emb met (f - g)) Z =
       met.g (grad emb met f - grad emb met g) Z
  have g_sub_left : ∀ A B C : V, met.g (A - B) C = met.g A C - met.g B C := by
    intro A B C
    calc met.g (A - B) C = met.g (A + -B) C := by rw [sub_eq_add_neg]
      _ = met.g A C + met.g (-B) C := met.g_add_left _ _ _
      _ = met.g A C + -(met.g B C) := by
          congr 1; rw [show -B = (-1 : R) • B from by rw [neg_one_smul], met.g_smul_left]; ring
      _ = met.g A C - met.g B C := by rw [sub_eq_add_neg]
  rw [g_sub_left, g_grad, g_grad, g_grad, action_sub_right]

end GradientDefs
