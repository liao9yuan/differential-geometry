import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Algebra.Musical
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Tensor Inner Product
Inner product of two (0,2)-tensors using the Trace of the composition of their musical endomorphisms.
-/

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
variable (metric : MetricDuality R V)
variable [TraceOperator R V] [TR : TraceLinearityRules R V]

-- 2. Define Tensor Inner Product
def tensorInnerProduct (T S : SmoothBilinearForm R V) : R :=
  TraceOperator.trace ((fun X => metric.raise T X) ∘ (fun X => metric.raise S X))

def tensorNormSq (T : SmoothBilinearForm R V) : R := tensorInnerProduct metric T T

-- 3. Prove Inner Product Properties

-- Lemma 1: inner_symm
lemma inner_symm (T S : SmoothBilinearForm R V) :
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

-- Lemma 2: inner_add_left
lemma inner_add_left (T₁ T₂ S : SmoothBilinearForm R V) :
    tensorInnerProduct metric (T₁ + T₂) S = tensorInnerProduct metric T₁ S + tensorInnerProduct metric T₂ S := by
  dsimp [tensorInnerProduct]
  rw [to_endo_add metric]
  have h_comp_dist : ((fun X => metric.raise T₁ X + metric.raise T₂ X) ∘ (fun X => metric.raise S X)) =
                     ((fun X => metric.raise T₁ X) ∘ (fun X => metric.raise S X)) + ((fun X => metric.raise T₂ X) ∘ (fun X => metric.raise S X)) := rfl
  rw [h_comp_dist]
  exact TR.trace_add

-- Lemma 3: inner_smul_left
lemma inner_smul_left (c : R) (T S : SmoothBilinearForm R V) :
    tensorInnerProduct metric (c • T) S = c * tensorInnerProduct metric T S := by
  dsimp [tensorInnerProduct]
  rw [to_endo_smul metric]
  have h_comp_smul : ((fun X => c • metric.raise T X) ∘ (fun X => metric.raise S X)) =
                     fun X => c • (((fun X => metric.raise T X) ∘ (fun X => metric.raise S X)) X) := rfl
  rw [h_comp_smul]
  exact TR.trace_smul

-- Lemma 4: inner_add_right
lemma inner_add_right (T S₁ S₂ : SmoothBilinearForm R V) :
    tensorInnerProduct metric T (S₁ + S₂) = tensorInnerProduct metric T S₁ + tensorInnerProduct metric T S₂ := by
  rw [inner_symm metric T (S₁ + S₂)]
  rw [inner_add_left metric S₁ S₂ T]
  rw [inner_symm metric S₁ T]
  rw [inner_symm metric S₂ T]

-- Lemma 5: inner_smul_right
lemma inner_smul_right (c : R) (T S : SmoothBilinearForm R V) :
    tensorInnerProduct metric T (c • S) = c * tensorInnerProduct metric T S := by
  rw [inner_symm metric T (c • S)]
  rw [inner_smul_left metric c S T]
  rw [inner_symm metric S T]
