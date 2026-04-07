import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Algebra.Metric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Tensor Inner Product
Inner product of two (0,2)-tensors using the Trace of the composition of their musical endomorphisms.
-/

open DifferentialGeometry TensorAlgebra

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable (metric : MetricDuality R V)
def contract4 (T : AbstractTensor R V 4 4) : AbstractTensor R V 0 0 :=
  contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (contract (r:=2) (s:=2) (contract (r:=3) (s:=3) T)))

-- 2. Define Tensor Inner Product
def tensorInnerProduct (T S : AbstractBilinearForm R V) : R :=
  toScalar (
    contract4 (
      tensor_prod (r1:=4) (s1:=0) (r2:=0) (s2:=4)
        (tensor_prod (r1:=2) (s1:=0) (r2:=2) (s2:=0) metric.g_inv metric.g_inv)
        (tensor_prod (r1:=0) (s1:=2) (r2:=0) (s2:=2) T S)
    )
  )

class TensorInnerProductRules (R V : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : MetricDuality R V) where
  inner_symm : ∀ (T S : AbstractBilinearForm R V), tensorInnerProduct metric T S = tensorInnerProduct metric S T
  inner_trace : ∀ (T S : AbstractBilinearForm R V), tensorInnerProduct metric T S = tensor_eval (metric_trace metric (0: Fin 2) (0: Fin 1) (TensorAlgebra.contract (r:=0) (s:=2) (TensorAlgebra.tensor_prod (r1:=1) (s1:=1) (r2:=0) (s2:=2) (raise_index metric (0: Fin 2) T) S))) ![] ![]

variable [IR : TensorInnerProductRules R V metric]

def tensorNormSq (T : AbstractBilinearForm R V) : R := tensorInnerProduct metric T T

-- 3. Prove Inner Product Properties

-- Lemma 1: tensor_inner_symm
lemma tensor_inner_symm (T S : AbstractBilinearForm R V) :
    tensorInnerProduct metric T S = tensorInnerProduct metric S T := by
  exact IR.inner_symm T S

-- Lemma 2: tensor_inner_add_left
lemma tensor_inner_add_left (T₁ T₂ S : AbstractBilinearForm R V) :
    tensorInnerProduct metric (T₁ + T₂) S = tensorInnerProduct metric T₁ S + tensorInnerProduct metric T₂ S := by
  dsimp [tensorInnerProduct, contract4]
  have h_add : T₁ + T₂ = TensorAlgebra.add (r:=0) (s:=2) T₁ T₂ := rfl
  simp only [h_add, tensor_prod_add_left, tensor_prod_add_right, contract_add, toScalar_add]

-- Lemma 3: tensor_inner_smul_left
lemma tensor_inner_smul_left (c : R) (T S : AbstractBilinearForm R V) :
    tensorInnerProduct metric (c • T) S = c * tensorInnerProduct metric T S := by
  dsimp [tensorInnerProduct, contract4]
  have h_smul : c • T = TensorAlgebra.smul (r:=0) (s:=2) c T := rfl
  simp only [h_smul, tensor_prod_smul_left, tensor_prod_smul_right, contract_smul, toScalar_smul]

-- Lemma 4: tensor_inner_add_right
lemma tensor_inner_add_right (T S₁ S₂ : AbstractBilinearForm R V) :
    tensorInnerProduct metric T (S₁ + S₂) = tensorInnerProduct metric T S₁ + tensorInnerProduct metric T S₂ := by
  rw [tensor_inner_symm metric T (S₁ + S₂)]
  rw [tensor_inner_add_left metric S₁ S₂ T]
  rw [tensor_inner_symm metric S₁ T]
  rw [tensor_inner_symm metric S₂ T]

-- Lemma 5: tensor_inner_smul_right
lemma tensor_inner_smul_right (c : R) (T S : AbstractBilinearForm R V) :
    tensorInnerProduct metric T (c • S) = c * tensorInnerProduct metric T S := by
  rw [tensor_inner_symm metric T (c • S)]
  rw [tensor_inner_smul_left metric c S T]
  rw [tensor_inner_symm metric S T]

/-- $|T + aS + bW|^2$ expansion -/
lemma expand_norm_sq_add3
  (T S W : AbstractBilinearForm R V)
  (a b : R) :
  tensorNormSq metric (T + a • S + b • W) =
  tensorNormSq metric T +
  a^2 * tensorNormSq metric S +
  b^2 * tensorNormSq metric W +
  (2:R) * a * tensorInnerProduct metric T S +
  (2:R) * b * tensorInnerProduct metric T W +
  (2:R) * a * b * tensorInnerProduct metric S W := by
  dsimp [tensorNormSq]
  simp only [tensor_inner_add_left metric, tensor_inner_add_right metric,
             tensor_inner_smul_left metric, tensor_inner_smul_right metric,
             tensor_inner_symm metric S T, tensor_inner_symm metric W T, tensor_inner_symm metric W S]
  ring



-- Lemma 6: tensor_inner_sub_left
lemma tensor_inner_sub_left (T₁ T₂ S : AbstractBilinearForm R V) :
    tensorInnerProduct metric (T₁ - T₂) S = tensorInnerProduct metric T₁ S - tensorInnerProduct metric T₂ S := by
  have h_add : T₁ - T₂ = T₁ + (-1:R) • T₂ := rfl
  rw [h_add]
  rw [tensor_inner_add_left, tensor_inner_smul_left]
  ring_nf

-- Lemma 7: tensor_inner_sub_right
lemma tensor_inner_sub_right (T S₁ S₂ : AbstractBilinearForm R V) :
    tensorInnerProduct metric T (S₁ - S₂) = tensorInnerProduct metric T S₁ - tensorInnerProduct metric T S₂ := by
  have h_add : S₁ - S₂ = S₁ + (-1:R) • S₂ := rfl
  rw [h_add]
  rw [tensor_inner_add_right, tensor_inner_smul_right]
  ring_nf

/-- $|A - bB - cC|^2$ expansion -/
lemma expand_norm_sq_sub3
  (A B C : AbstractBilinearForm R V)
  (b c : R) :
  tensorNormSq metric (A - b • B - c • C) =
  tensorNormSq metric A +
  b^2 * tensorNormSq metric B +
  c^2 * tensorNormSq metric C -
  (2:R) * b * tensorInnerProduct metric A B -
  (2:R) * c * tensorInnerProduct metric A C +
  (2:R) * b * c * tensorInnerProduct metric B C := by
  dsimp [tensorNormSq]
  simp only [tensor_inner_sub_left metric, tensor_inner_sub_right metric,
             tensor_inner_smul_left metric, tensor_inner_smul_right metric,
             tensor_inner_symm metric B A, tensor_inner_symm metric C A, tensor_inner_symm metric C B]
  ring
