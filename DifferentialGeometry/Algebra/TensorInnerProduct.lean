import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Algebra.MusicalEndomorphism
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Tensor Inner Product
Inner product of two (0,2)-tensors using the Trace of the composition of their musical endomorphisms.
-/

-- 1. Axiomatize Trace Linearity
class TraceLinearityRules (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [ScalarMul R V] [TraceOperator R V] where
  trace_add : ∀ (A B : V → V), (TraceOperator.trace (A + B) : R) = TraceOperator.trace A + TraceOperator.trace B
  trace_smul : ∀ (c : R) (A : V → V), (TraceOperator.trace (fun X => ScalarMul.smul c (A X)) : R) = c * TraceOperator.trace A
  trace_comm : ∀ (A B : V → V), (TraceOperator.trace (A ∘ B) : R) = TraceOperator.trace (B ∘ A)

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [ScalarMul R V]
variable (metric : MetricTensor R V) [MusicalEndomorphism R V metric]
variable [TraceOperator R V] [TR : TraceLinearityRules R V]

-- 2. Define Tensor Inner Product
def tensorInnerProduct (T S : SmoothBilinearForm R V) : R :=
  TraceOperator.trace ((MusicalEndomorphism.to_endo (metric := metric) T) ∘ (MusicalEndomorphism.to_endo (metric := metric) S))

-- 3. Prove Inner Product Properties

-- Lemma 1: inner_symm
lemma inner_symm (T S : SmoothBilinearForm R V) :
    tensorInnerProduct metric T S = tensorInnerProduct metric S T := by
  dsimp [tensorInnerProduct]
  have h_comm := TR.trace_comm ((MusicalEndomorphism.to_endo (metric := metric) T)) ((MusicalEndomorphism.to_endo (metric := metric) S))
  exact h_comm

variable [NonDegenerateMetric R V metric]

-- Helper lemmas for Linearity of Musical Endomorphisms
omit [TraceOperator R V] TR in
lemma to_endo_add (T₁ T₂ : SmoothBilinearForm R V) :
    MusicalEndomorphism.to_endo (metric := metric) (T₁ + T₂) =
    (MusicalEndomorphism.to_endo (metric := metric) T₁) + (MusicalEndomorphism.to_endo (metric := metric) T₂) := by
  funext X
  apply NonDegenerateMetric.eq_of_forall_g_eq (R := R) (metric := metric)
  intro Y
  rw [MusicalEndomorphism.g_endo]
  have h1 : (T₁ + T₂) X Y = T₁ X Y + T₂ X Y := rfl
  rw [h1]
  have h_pi : (((MusicalEndomorphism.to_endo (metric := metric) T₁) + (MusicalEndomorphism.to_endo (metric := metric) T₂)) X) = (MusicalEndomorphism.to_endo (metric := metric) T₁) X + (MusicalEndomorphism.to_endo (metric := metric) T₂) X := rfl
  have h2 : metric.g (((MusicalEndomorphism.to_endo (metric := metric) T₁) + (MusicalEndomorphism.to_endo (metric := metric) T₂)) X) Y = metric.g (((MusicalEndomorphism.to_endo (metric := metric) T₁) X) + ((MusicalEndomorphism.to_endo (metric := metric) T₂) X)) Y := by rw [h_pi]
  rw [h2]
  rw [metric.bilinear_add_left]
  rw [MusicalEndomorphism.g_endo]
  rw [MusicalEndomorphism.g_endo]

omit [TraceOperator R V] TR in
lemma to_endo_smul (c : R) (T : SmoothBilinearForm R V) :
    MusicalEndomorphism.to_endo (metric := metric) (c • T) =
    fun X => ScalarMul.smul c (MusicalEndomorphism.to_endo (metric := metric) T X) := by
  funext X
  apply NonDegenerateMetric.eq_of_forall_g_eq (R := R) (metric := metric)
  intro Y
  rw [MusicalEndomorphism.g_endo]
  have h1 : (c • T) X Y = c * T X Y := rfl
  rw [h1]
  have h_endo := MusicalEndomorphism.g_endo (metric := metric) T X Y
  have h_endo_symm : T X Y = metric.g (MusicalEndomorphism.to_endo (metric := metric) T X) Y := h_endo.symm
  rw [h_endo_symm]
  have h_smul_symm := (metric.bilinear_smul_left c (MusicalEndomorphism.to_endo (metric := metric) T X) Y).symm
  rw [h_smul_symm]

-- Lemma 2: inner_add_left
lemma inner_add_left (T₁ T₂ S : SmoothBilinearForm R V) :
    tensorInnerProduct metric (T₁ + T₂) S = tensorInnerProduct metric T₁ S + tensorInnerProduct metric T₂ S := by
  dsimp [tensorInnerProduct]
  rw [to_endo_add metric]
  have h_comp_dist : (((MusicalEndomorphism.to_endo (metric := metric) T₁) + (MusicalEndomorphism.to_endo (metric := metric) T₂)) ∘ MusicalEndomorphism.to_endo (metric := metric) S) =
                     ((MusicalEndomorphism.to_endo (metric := metric) T₁) ∘ (MusicalEndomorphism.to_endo (metric := metric) S)) + ((MusicalEndomorphism.to_endo (metric := metric) T₂) ∘ (MusicalEndomorphism.to_endo (metric := metric) S)) := rfl
  rw [h_comp_dist]
  have h_add := TR.trace_add ((MusicalEndomorphism.to_endo (metric := metric) T₁) ∘ (MusicalEndomorphism.to_endo (metric := metric) S)) ((MusicalEndomorphism.to_endo (metric := metric) T₂) ∘ (MusicalEndomorphism.to_endo (metric := metric) S))
  exact h_add

-- Lemma 3: inner_smul_left
lemma inner_smul_left (c : R) (T S : SmoothBilinearForm R V) :
    tensorInnerProduct metric (c • T) S = c * tensorInnerProduct metric T S := by
  dsimp [tensorInnerProduct]
  rw [to_endo_smul metric]
  have h_comp_smul : ((fun X => ScalarMul.smul c ((MusicalEndomorphism.to_endo (metric := metric) T) X)) ∘ (MusicalEndomorphism.to_endo (metric := metric) S)) =
                     fun X => ScalarMul.smul c (((MusicalEndomorphism.to_endo (metric := metric) T) ∘ (MusicalEndomorphism.to_endo (metric := metric) S)) X) := rfl
  rw [h_comp_smul]
  have h_smul := TR.trace_smul c ((MusicalEndomorphism.to_endo (metric := metric) T) ∘ (MusicalEndomorphism.to_endo (metric := metric) S))
  exact h_smul
