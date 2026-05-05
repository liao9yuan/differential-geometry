import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Lie Derivative

Synthetic Lie derivative on tensor fields.

The general definition is on `TensorData R V r s`.  It is characterized by
the textbook rules:
* on functions it is directional derivative;
* it satisfies the tensor-product Leibniz rule;
* evaluation/contraction with vector and covector slots satisfies Leibniz;
* on exact one-forms, it commutes with exterior derivative of functions.
-/

open BigOperators
open SyntheticTensor

section LieDeriv

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

private theorem bracket_leibniz_right
    (emb : DerivationEmbedding k R V) (X : V) (f : R) (Y : V) :
    bracket emb X (f • Y) = (emb.embed X) f • Y + f • bracket emb X Y := by
  simpa [action, add_comm] using bracket_smul_right emb f X Y

/-- The exterior derivative of a synthetic function: `df(Y) = Y(f)`. -/
def exteriorDerivativeFunction (emb : DerivationEmbedding k R V) (f : R) : V →ₗ[R] R where
  toFun Y := action emb Y f
  map_add' Y Z := action_add_left emb Y Z f
  map_smul' c Y := by
    simpa [smul_eq_mul] using action_smul_left emb c Y f

@[simp] theorem exteriorDerivativeFunction_apply
    (emb : DerivationEmbedding k R V) (f : R) (Y : V) :
    exteriorDerivativeFunction emb f Y = action emb Y f := rfl

/--
Lie derivative of a covector:
`(L_X α)(Y) = X(α(Y)) - α([X,Y])`.
-/
noncomputable def lieDerivDual (emb : DerivationEmbedding k R V)
    (X : V) (α : V →ₗ[R] R) : V →ₗ[R] R :=
  nabla_dual emb (bracket emb)
    (fun X Y Z => bracket_add_right emb X Y Z)
    (fun X f Y => bracket_leibniz_right emb X f Y)
    X α

@[simp] theorem lieDerivDual_apply
    (emb : DerivationEmbedding k R V) (X : V) (α : V →ₗ[R] R) (Y : V) :
    lieDerivDual emb X α Y = action emb X (α Y) - α (bracket emb X Y) := rfl

/--
Lie derivative of an `(r,s)` tensor field.

The definition is the evaluation/contraction rule:
`L_X` differentiates the scalar `T(vs; αs)` and subtracts the contribution
from applying `L_X` to every vector and covector argument.
-/
noncomputable def lieDerivTensor (emb : DerivationEmbedding k R V)
    (X : V) {r s : ℕ} (T : TensorData R V r s) : TensorData R V r s :=
  nabla_tensor emb (bracket emb)
    (fun X Y Z => bracket_add_right emb X Y Z)
    (fun X f Y => bracket_leibniz_right emb X f Y)
    X T

/-- Evaluation formula for the synthetic Lie derivative of a tensor. -/
theorem lieDerivTensor_eval
    (emb : DerivationEmbedding k R V) (X : V) {r s : ℕ}
    (T : TensorData R V r s) (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) :
    lieDerivTensor emb X T vs αs =
      action emb X (T vs αs)
      - ∑ i : Fin s, T (Function.update vs i (bracket emb X (vs i))) αs
      - ∑ j : Fin r, T vs (Function.update αs j (lieDerivDual emb X (αs j))) := rfl

/-- Axiom 1 in theorem form: on functions, `L_X f = X(f)`. -/
theorem lieDerivTensor_function
    (emb : DerivationEmbedding k R V) (X : V) (f : R) :
    lieDerivTensor emb X (scalarToData (R := R) (V := V) f) =
      scalarToData (R := R) (V := V) (action emb X f) := by
  ext vs αs
  rw [show vs = ![] from by ext i; exact i.elim0,
    show αs = ![] from by ext i; exact i.elim0]
  simp [lieDerivTensor_eval, scalarToData]

/-- Axiom 2 in theorem form: `L_X(S ⊗ T) = (L_X S) ⊗ T + S ⊗ (L_X T)`. -/
theorem lieDerivTensor_tensor_prod
    (emb : DerivationEmbedding k R V) (X : V)
    {r₁ s₁ r₂ s₂ : ℕ}
    (S : TensorData R V r₁ s₁) (T : TensorData R V r₂ s₂) :
    lieDerivTensor emb X (tensor_prod S T) =
      tensor_prod (lieDerivTensor emb X S) T +
        tensor_prod S (lieDerivTensor emb X T) := by
  unfold lieDerivTensor
  exact nabla_tensor_prod emb (bracket emb)
    (fun X Y Z => bracket_add_right emb X Y Z)
    (fun X f Y => bracket_leibniz_right emb X f Y)
    X S T

/--
Axiom 3 in theorem form, generalized to all tensor slots.

Moving terms in the evaluation formula gives the Leibniz rule for the complete
contraction/evaluation of `T` against vector and covector arguments.
-/
theorem lieDerivTensor_full_contraction_rule
    (emb : DerivationEmbedding k R V) (X : V) {r s : ℕ}
    (T : TensorData R V r s) (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) :
    action emb X (T vs αs) =
      lieDerivTensor emb X T vs αs +
        ∑ i : Fin s, T (Function.update vs i (bracket emb X (vs i))) αs +
        ∑ j : Fin r, T vs (Function.update αs j (lieDerivDual emb X (αs j))) := by
  rw [lieDerivTensor_eval]
  ring

/-- The covariant-only version of Axiom 3 from the text. -/
theorem lieDerivTensor_covariant_contraction_rule
    (emb : DerivationEmbedding k R V) (X : V) {s : ℕ}
    (T : TensorData R V 0 s) (Y : Fin s → V) :
    action emb X (T Y ![]) =
      lieDerivTensor emb X T Y ![] +
        ∑ i : Fin s, T (Function.update Y i (bracket emb X (Y i))) ![] := by
  simpa using
    lieDerivTensor_full_contraction_rule emb X T Y
      (![ ] : Fin 0 → (V →ₗ[R] R))

/-- Axiom 4 in theorem form: `L_X (df) = d(L_X f)`. -/
theorem lieDerivDual_exteriorDerivativeFunction
    (emb : DerivationEmbedding k R V) (X : V) (f : R) :
    lieDerivDual emb X (exteriorDerivativeFunction emb f) =
      exteriorDerivativeFunction emb (action emb X f) := by
  ext Y
  change action emb X (action emb Y f) - action emb (bracket emb X Y) f =
    action emb Y (action emb X f)
  rw [action_bracket]
  ring

/-- The Lie derivative of a vector field is its bracket with the differentiating field. -/
theorem lieDerivTensor_vector
    (emb : DerivationEmbedding k R V) (X Y : V) :
    lieDerivTensor emb X (vectorToData (R := R) Y) =
      vectorToData (R := R) (bracket emb X Y) := by
  unfold lieDerivTensor
  exact nabla_vector emb (bracket emb)
    (fun X Y Z => bracket_add_right emb X Y Z)
    (fun X f Y => bracket_leibniz_right emb X f Y)
    X Y

/-- The Lie derivative of a metric tensor along a vector field. -/
noncomputable def lieDerivMetric (emb : DerivationEmbedding k R V) (met : MetricDuality R V) (X Y Z : V) : R :=
  action emb X (met.g Y Z) - met.g (bracket emb X Y) Z - met.g Y (bracket emb X Z)

/-- The metric-specific formula is the `(0,2)` tensor Lie derivative of `g`. -/
theorem lieDerivMetric_eq_lieDerivTensor
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) (X Y Z : V) :
    lieDerivMetric emb met X Y Z =
      lieDerivTensor emb X met.g_tensor ![Y, Z] ![] := by
  rw [lieDerivTensor_eval]
  simp only [lieDerivMetric, MetricDuality.g, Finset.sum_of_isEmpty, sub_zero]
  rw [Fin.sum_univ_two]
  have h0 :
      Function.update (![Y, Z] : Fin 2 → V) 0 (bracket emb X Y) =
        ![bracket emb X Y, Z] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have h1 :
      Function.update (![Y, Z] : Fin 2 → V) 1 (bracket emb X Z) =
        ![Y, bracket emb X Z] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have h0' :
      Function.update (![Y, Z] : Fin 2 → V) 0
          (bracket emb X ((![Y, Z] : Fin 2 → V) 0)) =
        ![bracket emb X Y, Z] := by
    simpa using h0
  have h1' :
      Function.update (![Y, Z] : Fin 2 → V) 1
          (bracket emb X ((![Y, Z] : Fin 2 → V) 1)) =
        ![Y, bracket emb X Z] := by
    simpa using h1
  rw [h0', h1']
  ring

private lemma g_sub_left (met : MetricDuality R V) (A B C : V) :
    met.g (A - B) C = met.g A C - met.g B C := by
  calc met.g (A - B) C = met.g (A + -B) C := by rw [sub_eq_add_neg]
    _ = met.g A C + met.g (-B) C := met.g_add_left _ _ _
    _ = met.g A C + -(met.g B C) := by
        congr 1; rw [show -B = (-1 : R) • B from by rw [neg_one_smul], met.g_smul_left]; ring
    _ = met.g A C - met.g B C := by rw [sub_eq_add_neg]

private lemma g_sub_right (met : MetricDuality R V) (A B C : V) :
    met.g A (B - C) = met.g A B - met.g A C := by
  rw [met.g_symm A (B - C), g_sub_left, met.g_symm B, met.g_symm C]

/-- The Lie derivative of the metric equals the symmetrized covariant derivative. -/
theorem lieDerivMetric_eq_nabla
    (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    (conn : V → V → V)
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (X Y Z : V) :
    lieDerivMetric emb met X Y Z = met.g (conn Y X) Z + met.g Y (conn Z X) := by
  unfold lieDerivMetric action
  rw [h_mc X Y Z]
  have h1 : bracket emb X Y = conn X Y - conn Y X := (h_tf X Y).symm
  have h2 : bracket emb X Z = conn X Z - conn Z X := (h_tf X Z).symm
  rw [h1, h2, g_sub_left, g_sub_right]
  abel

end LieDeriv
