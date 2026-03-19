import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Operators.Variation
import DifferentialGeometry.Flows.RicciFlow.Basic
import DifferentialGeometry.Analysis.RicciTensor
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.style.longLine false

open AbstractDerivationAction

open DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V]
variable [DerivationRules R V]

/-!
# Evolution of the Connection under Ricci Flow

This file establishes the evolution equation for the Levi-Civita connection
under the Ricci flow equation.
-/

/-- Proves that the derivation action on the constant 1 is zero: $X(1) = 0$. -/
lemma action_one (X : V) : action X (1:R) = 0 := by
  have h1 : action X ((1:R) * (1:R)) = action X (1:R) * (1:R) + (1:R) * action X (1:R) := DerivationRules.action_smul_right X (1:R) (1:R)
  have h2 : (1:R) * (1:R) = (1:R) := by ring
  rw [h2] at h1
  have h3 : action X (1:R) * (1:R) = action X (1:R) := by ring
  have h4 : (1:R) * action X (1:R) = action X (1:R) := by ring
  rw [h3, h4] at h1
  calc action X (1:R) = action X (1:R) + action X (1:R) - action X (1:R) := by abel
    _ = action X (1:R) - action X (1:R) := by rw [← h1]
    _ = 0 := by abel

/-- Proves that if the derivation action on a constant $c$ is zero, then $X(c + c) = 0$. -/
lemma action_bit0_const (X : V) (c : R) (hc : action X c = 0) : action X (c + c) = 0 := by
  have h : action X (c + c) = action X c + action X c := DerivationRules.action_add_right X c c
  rw [hc, add_zero] at h
  exact h

/-- Proves that the derivation action on the constant 2 is zero: $X(2) = 0$. -/
lemma action_two (X : V) : action X (2:R) = 0 := by
  have h_two : (2:R) = (1:R) + (1:R) := by ring
  rw [h_two]
  exact action_bit0_const X (1:R) (action_one X)

variable [TraceOperator R V] [LieDerivationRules R V] [TraceLinearityRules R V]
variable [Invertible (2 : R)]

/-- The covariant derivative of the Ricci form at time t. -/
def ricci_cov_deriv {Time : Type} [TimeDerivative Time R] [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V) (conn_fam : Time → AbstractAffineConnection R V) (t : Time) (X Y Z : V) : R :=
  action X ((ricciForm (conn_fam t)) Y Z)
  - (ricciForm (conn_fam t)) ((nabla_fam g_fam t).nabla X Y) Z
  - (ricciForm (conn_fam t)) Y ((nabla_fam g_fam t).nabla X Z)

/--
Mathematical Identity: $\partial_t \Gamma_{ij}^k = - g^{kl} ( \nabla_i R_{jl} + \nabla_j R_{il} - \nabla_l R_{ij} )$
books/Poincare_Conjecture_Blueprint/chapter03b.tex, around line 397 (Corollary: Evolution of Christoffel Symbols under Ricci Flow)
-/
lemma connection_evolution {Time : Type}
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)
  (conn_fam : Time → AbstractAffineConnection R V)
  [MetricTimeDerivativeRules Time R V g_fam]
  [RicciFlow Time (fun t => (g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) conn_fam]
  (X Y Z : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z =
  - ricci_cov_deriv g_fam conn_fam t X Y Z
  - ricci_cov_deriv g_fam conn_fam t Y X Z
  + ricci_cov_deriv g_fam conn_fam t Z X Y := by
  have h_metric_var : (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t).val = fun A B => (- (2:R)) * (ricciForm (conn_fam t)) A B := by
    have heq : metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t = (- (2:R)) • ricciForm (conn_fam t) := RicciFlow.evolution t
    rw [heq]
    rfl
  /- Proves that the derivation action on the constant -2 is zero: $X(-2) = 0$. -/
  have action_neg_two : ∀ X : V, action X (- (2:R)) = 0 := by
    intro X
    rw [action_neg X (2:R), action_two X, neg_zero]
  /- Proves that the constant factor -2 commutes with the derivation action: $X(-2f) = -2 X(f)$. -/
  have action_mul_const : ∀ (X : V) (f : R), action X ((- (2:R)) * f) = (- (2:R)) * action X f := by
    intro X f
    rw [DerivationRules.action_smul_right X (- (2:R)) f, action_neg_two X, zero_mul, zero_add]
  have h_cov_eq : ∀ A B C : V, h_cov_deriv g_fam t A B C = (- (2:R)) * ricci_cov_deriv g_fam conn_fam t A B C := by
    intro A B C
    dsimp [h_cov_deriv, ricci_cov_deriv]
    have hm : ∀ Y Z : V, (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t).val Y Z = (- (2:R)) * ricciForm (conn_fam t) Y Z := by
      intro Y Z
      exact congrFun (congrFun h_metric_var Y) Z
    rw [hm B C, hm ((nabla_fam g_fam t).nabla A B) C, hm B ((nabla_fam g_fam t).nabla A C)]
    rw [action_mul_const A (ricciForm (conn_fam t) B C)]
    ring
  have h_variation := connection_variation g_fam X Y Z t
  have h_rhs : h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y =
    2 * (- ricci_cov_deriv g_fam conn_fam t X Y Z - ricci_cov_deriv g_fam conn_fam t Y X Z + ricci_cov_deriv g_fam conn_fam t Z X Y) := by
    rw [h_cov_eq X Y Z, h_cov_eq Y X Z, h_cov_eq Z X Y]
    ring
  rw [h_rhs] at h_variation
  have h_cancel : ∀ (W : R) (U : R), 2 * W = 2 * U → W = U := by
    intro W U h_eq
    calc W = ⅟2 * (2 * W) := by rw [← mul_assoc, invOf_mul_self, one_mul]
      _ = ⅟2 * (2 * U) := by rw [h_eq]
      _ = U := by rw [← mul_assoc, invOf_mul_self, one_mul]
  apply h_cancel
  exact h_variation
