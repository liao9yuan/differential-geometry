import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Algebra.Metric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Tensor Inner Product
Inner product of two (0,2)-tensors using the Trace of the composition of their musical endomorphisms.
-/

open DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable (metric : MetricDuality R V)
variable [TraceOperator R V] [TR : TraceLinearityRules R V]

-- 2. Define Tensor Inner Product
def tensorInnerProduct (T S : SmoothBilinearForm R V) : R :=
  TraceOperator.trace ((fun X => metric.raise T X) ∘ (fun X => metric.raise S X))

def tensorNormSq (T : SmoothBilinearForm R V) : R := tensorInnerProduct metric T T

-- 3. Prove Inner Product Properties

-- Lemma 1: tensor_inner_symm
lemma tensor_inner_symm (T S : SmoothBilinearForm R V) :
    tensorInnerProduct metric T S = tensorInnerProduct metric S T := by
  dsimp [tensorInnerProduct]
  exact TR.trace_comm

-- Helper lemmas for Linearity of Musical Endomorphisms
omit [TraceOperator R V] TR in
lemma to_endo_add (T₁ T₂ : SmoothBilinearForm R V) :
    (fun X => metric.raise (T₁ + T₂) X) =
    (fun X => metric.raise T₁ X + metric.raise T₂ X) := by
  funext X
  exact raise_add metric T₁ T₂ X

omit [TraceOperator R V] TR in
lemma to_endo_smul (c : R) (T : SmoothBilinearForm R V) :
    (fun X => metric.raise (c • T) X) =
    fun X => c • metric.raise T X := by
  funext X
  exact raise_smul metric T c X

-- Lemma 2: tensor_inner_add_left
lemma tensor_inner_add_left (T₁ T₂ S : SmoothBilinearForm R V) :
    tensorInnerProduct metric (T₁ + T₂) S = tensorInnerProduct metric T₁ S + tensorInnerProduct metric T₂ S := by
  dsimp [tensorInnerProduct]
  rw [to_endo_add metric]
  have h_comp_dist : ((fun X => metric.raise T₁ X + metric.raise T₂ X) ∘ (fun X => metric.raise S X)) =
                     ((fun X => metric.raise T₁ X) ∘ (fun X => metric.raise S X)) + ((fun X => metric.raise T₂ X) ∘ (fun X => metric.raise S X)) := rfl
  rw [h_comp_dist]
  exact TR.trace_add

-- Lemma 3: tensor_inner_smul_left
lemma tensor_inner_smul_left (c : R) (T S : SmoothBilinearForm R V) :
    tensorInnerProduct metric (c • T) S = c * tensorInnerProduct metric T S := by
  dsimp [tensorInnerProduct]
  rw [to_endo_smul metric]
  have h_comp_smul : ((fun X => c • metric.raise T X) ∘ (fun X => metric.raise S X)) =
                     fun X => c • (((fun X => metric.raise T X) ∘ (fun X => metric.raise S X)) X) := rfl
  rw [h_comp_smul]
  exact TR.trace_smul

-- Lemma 4: tensor_inner_add_right
lemma tensor_inner_add_right (T S₁ S₂ : SmoothBilinearForm R V) :
    tensorInnerProduct metric T (S₁ + S₂) = tensorInnerProduct metric T S₁ + tensorInnerProduct metric T S₂ := by
  rw [tensor_inner_symm metric T (S₁ + S₂)]
  rw [tensor_inner_add_left metric S₁ S₂ T]
  rw [tensor_inner_symm metric S₁ T]
  rw [tensor_inner_symm metric S₂ T]

-- Lemma 5: tensor_inner_smul_right
lemma tensor_inner_smul_right (c : R) (T S : SmoothBilinearForm R V) :
    tensorInnerProduct metric T (c • S) = c * tensorInnerProduct metric T S := by
  rw [tensor_inner_symm metric T (c • S)]
  rw [tensor_inner_smul_left metric c S T]
  rw [tensor_inner_symm metric S T]

/-- $|T + aS + bW|^2$ expansion -/
lemma expand_norm_sq_add3
  (T S W : SmoothBilinearForm R V)
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

/-- $|A - bB - cC|^2$ expansion -/
lemma expand_norm_sq_sub3
  (A B C : SmoothBilinearForm R V)
  (b c : R) :
  tensorNormSq metric (A - b • B - c • C) =
  tensorNormSq metric A +
  b^2 * tensorNormSq metric B +
  c^2 * tensorNormSq metric C -
  (2:R) * b * tensorInnerProduct metric A B -
  (2:R) * c * tensorInnerProduct metric A C +
  (2:R) * b * c * tensorInnerProduct metric B C := by
  dsimp [tensorNormSq]
  have h1 : A - b • B - c • C = A + (-b) • B + (-c) • C := by
    ext X Y
    change (A - b • B - c • C) X Y = (A + (-b) • B + (-c) • C) X Y
    change A X Y - b * B X Y - c * C X Y = A X Y + (-b) * B X Y + (-c) * C X Y
    ring
  rw [h1]
  simp only [tensor_inner_add_left metric, tensor_inner_add_right metric,
             tensor_inner_smul_left metric, tensor_inner_smul_right metric,
             tensor_inner_symm metric B A, tensor_inner_symm metric C A, tensor_inner_symm metric C B]
  ring
