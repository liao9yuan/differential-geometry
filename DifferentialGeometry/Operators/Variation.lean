import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Analysis.TensorInnerProduct
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Time Derivatives and Variation
Defines generic time derivatives and variation of metric.
-/

open AbstractDerivationAction AbstractLieBracket DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]


-- 1. Generic Time Derivative
/-- Generic time derivative operator.
Defines the `partial_t` operator for time-dependent functions.
Input: (Type, Type)
Output: Type -/
class TimeDerivative (Time α : Type) where
  partial_t : (Time → α) → Time → α

-- 2. Time Derivative Rules
/-- Rules for the generic time derivative operator.
Axiomatizes the additivity and scalar multiplication linearity of the time derivative.
Input: (Type, Type, Type)
Output: Type -/
class TimeDerivativeRules (Time R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [TimeDerivative Time R] where
  t_add : ∀ (f₁ f₂ : Time → R) (t : Time),
    TimeDerivative.partial_t (fun s => f₁ s + f₂ s) t = TimeDerivative.partial_t f₁ t + TimeDerivative.partial_t f₂ t
  t_smul : ∀ (c : R) (f : Time → R) (t : Time),
    TimeDerivative.partial_t (fun s => c * f s) t = c * TimeDerivative.partial_t f t

-- 3. Metric Variation Form
/-- Operator for metric variation.
Constructed explicitly from bilinear function of metric derivative.
-/
def metric_var_form {Time R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivativeRules Time R V]
  (g_fam : Time → AbstractMetricTensor R V) (t : Time) : AbstractBilinearForm R V :=
  TensorAlgebra.fromBilinear {
    toFun := fun X => {
      toFun := fun Y => TimeDerivative.partial_t (fun s => (g_fam s).g X Y) t
      map_add' := fun Y₁ Y₂ => by
        have h_add : (fun s => (g_fam s).g X (Y₁ + Y₂)) = (fun s => (g_fam s).g X Y₁) + (fun s => (g_fam s).g X Y₂) := by
          ext s
          exact eval02_add_right (g_fam s).g_tensor X Y₁ Y₂
        rw [h_add]
        exact TimeDerivativeRules.t_add V _ _ t
      map_smul' := fun c Y => by
        have h_smul : (fun s => (g_fam s).g X (c • Y)) = fun s => c * (g_fam s).g X Y := by
          ext s
          exact eval02_smul_right (g_fam s).g_tensor c X Y
        rw [h_smul]
        exact TimeDerivativeRules.t_smul V _ _ t
    }
    map_add' := fun X₁ X₂ => by
      ext Y
      change TimeDerivative.partial_t (fun s => (g_fam s).g (X₁ + X₂) Y) t =
             TimeDerivative.partial_t (fun s => (g_fam s).g X₁ Y) t +
             TimeDerivative.partial_t (fun s => (g_fam s).g X₂ Y) t
      have h_add : (fun s => (g_fam s).g (X₁ + X₂) Y) = (fun s => (g_fam s).g X₁ Y) + (fun s => (g_fam s).g X₂ Y) := by
        ext s
        exact eval02_add_left (g_fam s).g_tensor X₁ X₂ Y
      rw [h_add]
      exact TimeDerivativeRules.t_add V _ _ t
    map_smul' := fun c X => by
      ext Y
      change TimeDerivative.partial_t (fun s => (g_fam s).g (c • X) Y) t =
             c * TimeDerivative.partial_t (fun s => (g_fam s).g X Y) t
      have h_smul : (fun s => (g_fam s).g (c • X) Y) = fun s => c * (g_fam s).g X Y := by
        ext s
        exact eval02_smul_left (g_fam s).g_tensor c X Y
      rw [h_smul]
      exact TimeDerivativeRules.t_smul V _ _ t
  }

lemma metric_var_form_eval {Time R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivativeRules Time R V] (g_fam : Time → AbstractMetricTensor R V) (t : Time) (X Y : V) :
  eval02 (metric_var_form g_fam t) X Y = TimeDerivative.partial_t (fun s => (g_fam s).g X Y) t := by
  dsimp [metric_var_form, eval02]
  rw [TensorAlgebra.contract_fromBilinear]
  rfl

-- 4. Metric Time Derivative Calculus Axioms
/-- Product rule and constant rules for time derivatives involving the metric. -/
class MetricTimeDerivativeRules (Time R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TR_OP : TraceOperator R V]
  [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V) where
  t_const_R : ∀ (c : R) (t : Time), TimeDerivative.partial_t (fun _ => c) t = 0
  t_const_V : ∀ (X : V) (t : Time), TimeDerivative.partial_t (fun _ => X) t = 0
  t_trace : ∀ (A : Time → (V → V)) (t : Time),
    (TimeDerivative.partial_t (fun s => (@TraceOperator.trace R V TR_OP (A s) : R)) t : R) =
    (@TraceOperator.trace R V TR_OP (fun X => TimeDerivative.partial_t (fun s => A s X) t) : R)
  t_metric : ∀ (X Y : Time → V) (t : Time),
    TimeDerivative.partial_t (fun s => (g_fam s).g (X s) (Y s)) t =
    eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) (X t) (Y t) +
    (g_fam t).g (TimeDerivative.partial_t X t) (Y t) +
    (g_fam t).g (X t) (TimeDerivative.partial_t Y t)

lemma metric_zero_right {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) (X : V) : metric.g X 0 = 0 := by
  have h1 : metric.g X (0 + 0) = metric.g X 0 + metric.g X 0 := by
    have h1a : metric.g (0 + 0) X = metric.g 0 X + metric.g 0 X := metric.bilinear_add_left 0 0 X
    have h1b : metric.g X (0 + 0) = metric.g (0 + 0) X := metric.symm X (0 + 0)
    have h1c : metric.g X 0 = metric.g 0 X := metric.symm X 0
    rw [h1b, h1a, ← h1c]
  calc metric.g X 0 = metric.g X 0 + metric.g X 0 - metric.g X 0 := by abel
    _ = metric.g X (0 + 0) - metric.g X 0 := by rw [← h1]
    _ = metric.g X 0 - metric.g X 0 := by rw [add_zero]
    _ = 0 := by abel

lemma metric_zero_left {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) (X : V) : metric.g 0 X = 0 := by
  have h1 : metric.g 0 X = metric.g X 0 := metric.symm 0 X
  rw [h1]
  exact metric_zero_right metric X

-- 5. Inverse Metric Variation
/-- Variation of the raised index tensor (inverse metric). -/
lemma raise_variation {Time R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TraceOperator R V] [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (T : AbstractBilinearForm R V) (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y =
  - eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y := by
  have h1 : (fun s => (g_fam s).g ((g_fam s).raise T X) Y) = fun s => eval02 T X Y := by
    funext s
    exact (g_fam s).g_raise T X Y
  have h2 : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise T X) Y) t =
            TimeDerivative.partial_t (fun s => eval02 T X Y) t := by
    rw [h1]
  have h3 : TimeDerivative.partial_t (fun s => eval02 T X Y) t = 0 := by
    exact MetricTimeDerivativeRules.t_const_R g_fam (eval02 T X Y) t
  have h4 : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise T X) Y) t =
            eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y +
            (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y +
            (g_fam t).g ((g_fam t).raise T X) (TimeDerivative.partial_t (fun s => Y) t) := by
    exact MetricTimeDerivativeRules.t_metric (g_fam:=g_fam) (fun s => (g_fam s).raise T X) (fun s => Y) t
  have h5 : TimeDerivative.partial_t (fun s => Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Y t
  have h6 : (g_fam t).g ((g_fam t).raise T X) (TimeDerivative.partial_t (fun s => Y) t) = 0 := by
    rw [h5]
    exact metric_zero_right ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) ((g_fam t).raise T X)
  have h7 : 0 = eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y +
                (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y := by
    calc 0 = TimeDerivative.partial_t (fun s => eval02 T X Y) t := h3.symm
         _ = TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise T X) Y) t := h2.symm
         _ = eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y +
             (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y +
             (g_fam t).g ((g_fam t).raise T X) (TimeDerivative.partial_t (fun s => Y) t) := h4
         _ = eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y +
             (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y + 0 := by rw [h6]
         _ = eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y +
             (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y := by abel
  calc (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y
     = eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y +
       (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y
       - eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y := by abel
     _ = 0 - eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y := by rw [← h7]
     _ = - eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y := by abel

-- 6. Metric Trace Variation
/-- Time variation of the trace of a fixed metric. -/
lemma tr_g_variation {Time R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TR_OP : TraceOperator R V] [TR : TraceLinearityRules R V]
  [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (T : AbstractBilinearForm R V) (t : Time) [IR : TensorInnerProductRules R V (g_fam t)] :
  (TimeDerivative.partial_t (fun s => (@TraceOperator.trace R V TR_OP (fun X => (g_fam s).raise T X) : R)) t : R) =
  - tensorInnerProduct (g_fam t) (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) T := by
  have h1 : (TimeDerivative.partial_t (fun s => (@TraceOperator.trace R V TR_OP (fun X => (g_fam s).raise T X) : R)) t : R) =
            (@TraceOperator.trace R V TR_OP (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) : R) :=
    MetricTimeDerivativeRules.t_trace g_fam (fun s X => (g_fam s).raise T X) t
  have vector_eq : ∀ X, TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t =
                        - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) := by
    intro X
    apply (g_fam t).toNonDegenerateMetric.eq_of_forall_g_eq
    intro Y
    have step1 := raise_variation g_fam T X Y t
    have step2 : (g_fam t).g (- (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) Y =
                 - (g_fam t).g ((g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) Y := by
      exact metric_neg_left ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) ((g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) Y
    have step3 : (g_fam t).g ((g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) Y =
                 eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y := by
      exact (g_fam t).g_raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) Y
    rw [step2, step3]
    exact step1
  have h2 : (@TraceOperator.trace R V TR_OP (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) : R) =
            (@TraceOperator.trace R V TR_OP (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) := by
    have heq : (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) =
               (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) := by
      funext X
      exact vector_eq X
    rw [heq]
  have h3 : (@TraceOperator.trace R V TR_OP (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) =
            (@TraceOperator.trace R V TR_OP (fun X => (-1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) := by
    have heq2 : (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) =
                (fun X => (-1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) := by
      funext X
      have eqst : (-1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) =
                  - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X) := by
        rw [neg_smul, one_smul]
      exact eqst.symm
    rw [heq2]
  have h4 : (@TraceOperator.trace R V TR_OP (fun X => (-1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) =
            (-1:R) * (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) := by
    exact TR.trace_smul
  have h5 : (-1:R) * (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) =
            - (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) := by
    ring
  have h6 : tensorInnerProduct (g_fam t) (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) T =
            (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) := by
    exact IR.inner_trace (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) T
  calc (TimeDerivative.partial_t (fun s => (@TraceOperator.trace R V TR_OP (fun X => (g_fam s).raise T X) : R)) t : R)
     = (@TraceOperator.trace R V TR_OP (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) : R) := h1
   _ = (@TraceOperator.trace R V TR_OP (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) := h2
   _ = (@TraceOperator.trace R V TR_OP (fun X => (-1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) := h3
   _ = (-1:R) * (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) := h4
   _ = - (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((g_fam t).raise T X)) : R) := h5
   _ = - tensorInnerProduct (g_fam t) (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) T := by rw [h6]

-- 7. Variation of the Connection (Palatini Identity)

/-- Axiom relating time derivatives to derivation action. -/
class ActionTimeDerivativeRules (Time R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
  [TimeDerivative Time R] [AbstractDerivationAction R V] where
  t_action : ∀ (X : V) (f : Time → R) (t : Time),
    TimeDerivative.partial_t (fun s => action X (f s)) t = action X (TimeDerivative.partial_t f t)

variable [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] [Invertible (2 : R)]

/-- The unique Levi-Civita connection associated to a metric family at time s. -/
abbrev nabla_fam {Time : Type} (g_fam : Time → MetricDuality R V) (t : Time) : AbstractAffineConnection R V :=
  koszul_connection (g_fam t)

/-- The covariant derivative of the symmetric bilinear form h = ∂_t g at time t.
(∇_X h)(Y, Z) = X(h(Y, Z)) - h(∇_X Y, Z) - h(Y, ∇_X Z)
-/
def h_cov_deriv {Time : Type} [TimeDerivative Time R] [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V)  (t : Time) (X Y Z : V) : R :=
  action X (eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) Y Z)
  - eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ((nabla_fam g_fam t).nabla X Y) Z
  - eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) Y ((nabla_fam g_fam t).nabla X Z)

/-- Palatini identity for the variation of the Levi-Civita connection. -/
lemma connection_variation {Time : Type} [TimeDerivative Time R] [TimeDerivative Time V]
  [TraceOperator R V] [TraceLinearityRules R V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (X Y Z : V) (t : Time) :
  2 * (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z =
  h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y := by
  let h (A B : V) := eval02 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) A B
  let n (A B : V) := (nabla_fam g_fam t).nabla A B

  have l_add : ∀ (f₁ f₂ : Time → R), TimeDerivative.partial_t (fun s => f₁ s + f₂ s) t = TimeDerivative.partial_t f₁ t + TimeDerivative.partial_t f₂ t := fun f₁ f₂ => TimeDerivativeRules.t_add V f₁ f₂ t
  have l_sub : ∀ (f₁ f₂ : Time → R), TimeDerivative.partial_t (fun s => f₁ s - f₂ s) t = TimeDerivative.partial_t f₁ t - TimeDerivative.partial_t f₂ t := by
    intro f₁ f₂
    have hr : (fun s => f₁ s - f₂ s) = (fun s => f₁ s + (-1:R) * f₂ s) := by funext s; ring
    rw [hr, l_add f₁ _, TimeDerivativeRules.t_smul V (-1:R) f₂ t]
    ring

  have pt_Z : TimeDerivative.partial_t (fun s => Z) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Z t

  have pt_term : TimeDerivative.partial_t (fun s => (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) t =
                 (h ((nabla_fam g_fam t).nabla X Y) Z) +
                 (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z +
                 (g_fam t).g ((nabla_fam g_fam t).nabla X Y) (TimeDerivative.partial_t (fun s => Z) t) :=
    MetricTimeDerivativeRules.t_metric (fun s => (nabla_fam g_fam s).nabla X Y) (fun s => Z) t

  have h_zero : (g_fam t).g ((nabla_fam g_fam t).nabla X Y) (TimeDerivative.partial_t (fun s => Z) t) = 0 := by
    rw [pt_Z]
    exact metric_zero_right ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) ((nabla_fam g_fam t).nabla X Y)

  have pt_smul : TimeDerivative.partial_t (fun s => 2 * (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) t =
                 2 * TimeDerivative.partial_t (fun s => (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) t :=
    TimeDerivativeRules.t_smul V 2 (fun s => (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) t

  have hLHS : TimeDerivative.partial_t (fun s => 2 * (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) t =
              2 * (h (n X Y) Z + (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z) := by
    rw [pt_term, h_zero] at pt_smul
    have pt_term2 : h (n X Y) Z + (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z + 0 =
                    h (n X Y) Z + (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z := by abel
    rw [pt_term2] at pt_smul
    exact pt_smul

  have pt1 : TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z)) t = action X (h Y Z) := by
    have pt1_base := ActionTimeDerivativeRules.t_action X (fun s => (g_fam s).g Y Z) t
    have h_sub : TimeDerivative.partial_t (fun s => (g_fam s).g Y Z) t = h Y Z := by
      exact (metric_var_form_eval (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t Y Z).symm
    rw [h_sub] at pt1_base
    exact pt1_base
  have pt2 : TimeDerivative.partial_t (fun s => action Y ((g_fam s).g X Z)) t = action Y (h X Z) := by
    have pt2_base := ActionTimeDerivativeRules.t_action Y (fun s => (g_fam s).g X Z) t
    have h_sub : TimeDerivative.partial_t (fun s => (g_fam s).g X Z) t = h X Z := by
      exact (metric_var_form_eval (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t X Z).symm
    rw [h_sub] at pt2_base
    exact pt2_base
  have pt3 : TimeDerivative.partial_t (fun s => action Z ((g_fam s).g X Y)) t = action Z (h X Y) := by
    have pt3_base := ActionTimeDerivativeRules.t_action Z (fun s => (g_fam s).g X Y) t
    have h_sub : TimeDerivative.partial_t (fun s => (g_fam s).g X Y) t = h X Y := by
      exact (metric_var_form_eval (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t X Y).symm
    rw [h_sub] at pt3_base
    exact pt3_base

  have pt_X : TimeDerivative.partial_t (fun s => X) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam X t
  have pt_Y : TimeDerivative.partial_t (fun s => Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Y t

  have pt_bYZ : TimeDerivative.partial_t (fun s => bracket Y Z) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam (bracket Y Z) t
  have pt_term4 : TimeDerivative.partial_t (fun s => (g_fam s).g X (bracket Y Z)) t =
                  h X (bracket Y Z) + (g_fam t).g (TimeDerivative.partial_t (fun s => X) t) (bracket Y Z) + (g_fam t).g X (TimeDerivative.partial_t (fun s => bracket Y Z) t) :=
    MetricTimeDerivativeRules.t_metric (fun s => X) (fun s => bracket Y Z) t

  have hz4a : (g_fam t).g 0 (bracket Y Z) = 0 := metric_zero_left ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) (bracket Y Z)
  have hz4b : (g_fam t).g X 0 = 0 := metric_zero_right ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) X

  have pt4 : TimeDerivative.partial_t (fun s => (g_fam s).g X (bracket Y Z)) t = h X (bracket Y Z) := by
    rw [pt_X, pt_bYZ, hz4a, hz4b] at pt_term4
    calc TimeDerivative.partial_t (fun s => (g_fam s).g X (bracket Y Z)) t = h X (bracket Y Z) + 0 + 0 := pt_term4
      _ = h X (bracket Y Z) := by abel

  have pt_bZX : TimeDerivative.partial_t (fun s => bracket Z X) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam (bracket Z X) t
  have pt_term5 : TimeDerivative.partial_t (fun s => (g_fam s).g Y (bracket Z X)) t =
                  h Y (bracket Z X) + (g_fam t).g (TimeDerivative.partial_t (fun s => Y) t) (bracket Z X) + (g_fam t).g Y (TimeDerivative.partial_t (fun s => bracket Z X) t) :=
    MetricTimeDerivativeRules.t_metric (fun s => Y) (fun s => bracket Z X) t
  have hz5a : (g_fam t).g 0 (bracket Z X) = 0 := metric_zero_left ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) (bracket Z X)
  have hz5b : (g_fam t).g Y 0 = 0 := metric_zero_right ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) Y

  have pt5 : TimeDerivative.partial_t (fun s => (g_fam s).g Y (bracket Z X)) t = h Y (bracket Z X) := by
    rw [pt_Y, pt_bZX, hz5a, hz5b] at pt_term5
    calc TimeDerivative.partial_t (fun s => (g_fam s).g Y (bracket Z X)) t = h Y (bracket Z X) + 0 + 0 := pt_term5
      _ = h Y (bracket Z X) := by abel

  have pt_bXY : TimeDerivative.partial_t (fun s => bracket X Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam (bracket X Y) t
  have pt_term6 : TimeDerivative.partial_t (fun s => (g_fam s).g Z (bracket X Y)) t =
                  h Z (bracket X Y) + (g_fam t).g (TimeDerivative.partial_t (fun s => Z) t) (bracket X Y) + (g_fam t).g Z (TimeDerivative.partial_t (fun s => bracket X Y) t) :=
    MetricTimeDerivativeRules.t_metric (fun s => Z) (fun s => bracket X Y) t
  have hz6a : (g_fam t).g 0 (bracket X Y) = 0 := metric_zero_left ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) (bracket X Y)
  have hz6b : (g_fam t).g Z 0 = 0 := metric_zero_right ((g_fam t).toNonDegenerateMetric.toAbstractMetricTensor) Z

  have pt6 : TimeDerivative.partial_t (fun s => (g_fam s).g Z (bracket X Y)) t = h Z (bracket X Y) := by
    rw [pt_Z, pt_bXY, hz6a, hz6b] at pt_term6
    calc TimeDerivative.partial_t (fun s => (g_fam s).g Z (bracket X Y)) t = h Z (bracket X Y) + 0 + 0 := pt_term6
      _ = h Z (bracket X Y) := by abel

  have hRHS : TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y) - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X) + (g_fam s).g Z (bracket X Y)) t =
              action X (h Y Z) + action Y (h X Z) - action Z (h X Y) - h X (bracket Y Z) + h Y (bracket Z X) + h Z (bracket X Y) := by
    have step1 : TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y) - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X) + (g_fam s).g Z (bracket X Y)) t =
                 TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y) - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X)) t +
                 TimeDerivative.partial_t (fun s => (g_fam s).g Z (bracket X Y)) t := l_add _ _
    have step2 : TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y) - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X)) t =
                 TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y) - (g_fam s).g X (bracket Y Z)) t +
                 TimeDerivative.partial_t (fun s => (g_fam s).g Y (bracket Z X)) t := l_add _ _
    have step3 : TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y) - (g_fam s).g X (bracket Y Z)) t =
                 TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y)) t -
                 TimeDerivative.partial_t (fun s => (g_fam s).g X (bracket Y Z)) t := l_sub _ _
    have step4 : TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y)) t =
                 TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z)) t -
                 TimeDerivative.partial_t (fun s => action Z ((g_fam s).g X Y)) t := l_sub _ _
    have step5 : TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z)) t =
                 TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z)) t + TimeDerivative.partial_t (fun s => action Y ((g_fam s).g X Z)) t := l_add _ _
    rw [step1, step2, step3, step4, step5]
    rw [pt1, pt2, pt3, pt4, pt5, pt6]

  have koszul_eq : ∀ s, 2 * (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z =
    action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y)
    - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X) + (g_fam s).g Z (bracket X Y) := by
    intro s
    exact levi_civita_uniqueness ((nabla_fam g_fam s)) ((g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) X Y Z

  have h_base : TimeDerivative.partial_t (fun s => 2 * (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) t =
                TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y) - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X) + (g_fam s).g Z (bracket X Y)) t := by
    have func_eq : (fun s => 2 * (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) =
                   (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y) - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X) + (g_fam s).g Z (bracket X Y)) := by
      funext s
      exact koszul_eq s
    rw [func_eq]

  rw [hLHS, hRHS] at h_base

  have torsion_free : ∀ A B : V, n A B - n B A = bracket A B := TorsionFree.torsion_zero (conn:=(nabla_fam g_fam t))

  have h_symm : ∀ A B : V, h A B = h B A := by
    intro A B
    dsimp [h]
    rw [metric_var_form_eval (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor), metric_var_form_eval (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor)]
    have step : (fun s => (g_fam s).g A B) = (fun s => (g_fam s).g B A) := by
      funext s
      exact (g_fam s).symm A B
    change TimeDerivative.partial_t (fun s => (g_fam s).g A B) t = TimeDerivative.partial_t (fun s => (g_fam s).g B A) t
    rw [step]

  have h_add_right : ∀ A B C : V, h A (B + C) = h A B + h A C := eval02_add_right _
  have h_smul_right : ∀ c A B, h A (c • B) = c * h A B := eval02_smul_right _

  have h_neg_right : ∀ A B : V, h A (-B) = - h A B := by
    intro A B
    calc h A (-B) = h A ((-1:R) • B) := by rw [neg_one_smul]
      _ = (-1:R) * h A B := h_smul_right (-1) A B
      _ = - h A B := by ring

  have h_sub_right : ∀ A B C : V, h A (B - C) = h A B - h A C := by
    intro A B C
    have r1 : h A (B - C) = h A (B + -C) := by rw [sub_eq_add_neg]
    have r2 : h A (B + -C) = h A B + h A (-C) := h_add_right A B (-C)
    have r3 : h A (-C) = - h A C := h_neg_right A C
    rw [r1, r2, r3]
    ring

  have b1 : h X (bracket Y Z) = h X (n Y Z) - h X (n Z Y) := by rw [← torsion_free Y Z, h_sub_right]
  have b2 : h Y (bracket Z X) = h Y (n Z X) - h Y (n X Z) := by rw [← torsion_free Z X, h_sub_right]
  have b3 : h Z (bracket X Y) = h Z (n X Y) - h Z (n Y X) := by rw [← torsion_free X Y, h_sub_right]

  have eq_cov_deriv : h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y =
    action X (h Y Z) - h (n X Y) Z - h Y (n X Z) +
    (action Y (h X Z) - h (n Y X) Z - h X (n Y Z)) -
    (action Z (h X Y) - h (n Z X) Y - h X (n Z Y)) := by
    dsimp [h_cov_deriv, h, n]

  have a1 : h (n X Y) Z = h Z (n X Y) := h_symm _ _
  have a2 : h (n Y X) Z = h Z (n Y X) := h_symm _ _
  have a3 : h (n Z X) Y = h Y (n Z X) := h_symm _ _

  have step_rhs : action X (h Y Z) + action Y (h X Z) - action Z (h X Y) - h X (bracket Y Z) + h Y (bracket Z X) + h Z (bracket X Y) =
    h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y + 2 * h Z (n X Y) := by
    rw [eq_cov_deriv, b1, b2, b3]
    rw [a1, a2, a3]
    ring

  rw [step_rhs] at h_base
  calc 2 * (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z
     = 2 * (h (n X Y) Z + (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z) - 2 * h (n X Y) Z := by ring
   _ = h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y + 2 * h Z (n X Y) - 2 * h (n X Y) Z := by rw [h_base]
   _ = h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y + 2 * h Z (n X Y) - 2 * h Z (n X Y) := by rw [a1]
   _ = h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y := by ring
