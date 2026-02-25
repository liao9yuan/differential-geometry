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

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [ScalarMul R V]
variable (metric : MetricTensor R V) [MusicalIsomorphism R V metric]
variable [TraceOperator R V] [TR : TraceLinearityRules R V]

-- 2. Define Tensor Inner Product
def tensorInnerProduct (T S : SmoothBilinearForm R V) : R :=
  TraceOperator.trace ((fun X => MusicalIsomorphism.sharp metric (T X)) ∘ (fun X => MusicalIsomorphism.sharp metric (S X)))

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
    (fun X => MusicalIsomorphism.sharp metric ((T₁ + T₂) X)) =
    (fun X => MusicalIsomorphism.sharp metric (T₁ X) + MusicalIsomorphism.sharp metric (T₂ X)) := by
  funext X
  have eq1 : (T₁ + T₂) X = fun Y => T₁ X Y + T₂ X Y := rfl
  rw [eq1]
  exact MusicalIsomorphism.sharp_add (metric := metric) (T₁ X) (T₂ X)

omit [TraceOperator R V] TR in
lemma to_endo_smul (c : R) (T : SmoothBilinearForm R V) :
    (fun X => MusicalIsomorphism.sharp metric ((c • T) X)) =
    fun X => ScalarMul.smul c (MusicalIsomorphism.sharp metric (T X)) := by
  funext X
  have eq1 : (c • T) X = fun Y => c * T X Y := rfl
  rw [eq1]
  exact MusicalIsomorphism.sharp_smul (metric := metric) c (T X)

-- Lemma 2: inner_add_left
lemma inner_add_left (T₁ T₂ S : SmoothBilinearForm R V) :
    tensorInnerProduct metric (T₁ + T₂) S = tensorInnerProduct metric T₁ S + tensorInnerProduct metric T₂ S := by
  dsimp [tensorInnerProduct]
  rw [to_endo_add metric]
  have h_comp_dist : ((fun X => MusicalIsomorphism.sharp metric (T₁ X) + MusicalIsomorphism.sharp metric (T₂ X)) ∘ (fun X => MusicalIsomorphism.sharp metric (S X))) =
                     ((fun X => MusicalIsomorphism.sharp metric (T₁ X)) ∘ (fun X => MusicalIsomorphism.sharp metric (S X))) + ((fun X => MusicalIsomorphism.sharp metric (T₂ X)) ∘ (fun X => MusicalIsomorphism.sharp metric (S X))) := rfl
  rw [h_comp_dist]
  exact TR.trace_add

-- Lemma 3: inner_smul_left
lemma inner_smul_left (c : R) (T S : SmoothBilinearForm R V) :
    tensorInnerProduct metric (c • T) S = c * tensorInnerProduct metric T S := by
  dsimp [tensorInnerProduct]
  rw [to_endo_smul metric]
  have h_comp_smul : ((fun X => ScalarMul.smul c (MusicalIsomorphism.sharp metric (T X))) ∘ (fun X => MusicalIsomorphism.sharp metric (S X))) =
                     fun X => ScalarMul.smul c (((fun X => MusicalIsomorphism.sharp metric (T X)) ∘ (fun X => MusicalIsomorphism.sharp metric (S X))) X) := rfl
  rw [h_comp_smul]
  exact TR.trace_smul
