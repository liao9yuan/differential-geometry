import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Algebra.Musical
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Analysis.TensorInnerProduct
import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Time Derivatives and Variation
Defines generic time derivatives and variation of metric.
-/

open DerivationAction
open LieBracket

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]


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
/-- Time variation of a metric tensor family.
Constructs a smooth bilinear form representing the precise time derivative of the metric tensor.
Input: (Time → MetricTensor R V, Time)
Output: SmoothBilinearForm R V -/
def metric_var_form {Time : Type} [TimeDerivative Time R] [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricTensor R V) (t : Time) : SmoothBilinearForm R V where
  val := fun X Y => TimeDerivative.partial_t (fun s => (g_fam s).g X Y) t
  add_left := fun X₁ X₂ Y => by
    have h1 : (fun s => (g_fam s).g (X₁ + X₂) Y) = (fun s => (g_fam s).g X₁ Y + (g_fam s).g X₂ Y) := by
      funext s
      exact (g_fam s).bilinear_add_left X₁ X₂ Y
    rw [h1]
    exact TimeDerivativeRules.t_add V (fun s => (g_fam s).g X₁ Y) (fun s => (g_fam s).g X₂ Y) t
  smul_left := fun c X Y => by
    have h1 : (fun s => (g_fam s).g (c • X) Y) = (fun s => c * (g_fam s).g X Y) := by
      funext s
      have step := (g_fam s).bilinear_smul_left c X Y
      exact step
    rw [h1]
    exact TimeDerivativeRules.t_smul V c (fun s => (g_fam s).g X Y) t
  add_right := fun X Y₁ Y₂ => by
    have h1 : (fun s => (g_fam s).g X (Y₁ + Y₂)) = (fun s => (g_fam s).g X Y₁ + (g_fam s).g X Y₂) := by
      funext s
      have h2 : (g_fam s).g X (Y₁ + Y₂) = (g_fam s).g (Y₁ + Y₂) X := (g_fam s).symm _ _
      have h3 : (g_fam s).g (Y₁ + Y₂) X = (g_fam s).g Y₁ X + (g_fam s).g Y₂ X := (g_fam s).bilinear_add_left _ _ _
      have h4 : (g_fam s).g Y₁ X = (g_fam s).g X Y₁ := (g_fam s).symm _ _
      have h5 : (g_fam s).g Y₂ X = (g_fam s).g X Y₂ := (g_fam s).symm _ _
      rw [h2, h3, h4, h5]
    rw [h1]
    exact TimeDerivativeRules.t_add V (fun s => (g_fam s).g X Y₁) (fun s => (g_fam s).g X Y₂) t
  smul_right := fun c X Y => by
    have h1 : (fun s => (g_fam s).g X (c • Y)) = (fun s => c * (g_fam s).g X Y) := by
      funext s
      have h2 : (g_fam s).g X (c • Y) = (g_fam s).g (c • Y) X := (g_fam s).symm _ _
      have step := (g_fam s).bilinear_smul_left c Y X
      have h3 : (g_fam s).g (c • Y) X = c * (g_fam s).g Y X := step
      have h4 : (g_fam s).g Y X = (g_fam s).g X Y := (g_fam s).symm _ _
      rw [h2, h3, h4]
    rw [h1]
    exact TimeDerivativeRules.t_smul V c (fun s => (g_fam s).g X Y) t

-- 4. Metric Time Derivative Calculus Axioms
/-- Product rule and constant rules for time derivatives involving the metric. -/
class MetricTimeDerivativeRules (Time R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
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
    (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val (X t) (Y t) +
    (g_fam t).g (TimeDerivative.partial_t X t) (Y t) +
    (g_fam t).g (X t) (TimeDerivative.partial_t Y t)

lemma metric_zero_right {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (metric : MetricTensor R V) (X : V) : metric.g X 0 = 0 := by
  have h1 : metric.g X (0 + 0) = metric.g X 0 + metric.g X 0 := by
    have h1a : metric.g (0 + 0) X = metric.g 0 X + metric.g 0 X := metric.bilinear_add_left 0 0 X
    have h1b : metric.g X (0 + 0) = metric.g (0 + 0) X := metric.symm X (0 + 0)
    have h1c : metric.g X 0 = metric.g 0 X := metric.symm X 0
    rw [h1b, h1a, ← h1c]
  calc metric.g X 0 = metric.g X 0 + metric.g X 0 - metric.g X 0 := by abel
    _ = metric.g X (0 + 0) - metric.g X 0 := by rw [← h1]
    _ = metric.g X 0 - metric.g X 0 := by rw [add_zero]
    _ = 0 := by abel

lemma metric_zero_left {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (metric : MetricTensor R V) (X : V) : metric.g 0 X = 0 := by
  have h1 : metric.g 0 X = metric.g X 0 := metric.symm 0 X
  rw [h1]
  exact metric_zero_right metric X

-- 5. Inverse Metric Variation
/-- Variation of the raised index tensor (inverse metric). -/
lemma raise_variation {Time R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TraceOperator R V] [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (T : SmoothBilinearForm R V) (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y =
  - (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y := by
  have h1 : (fun s => (g_fam s).g ((g_fam s).raise T X) Y) = fun s => T X Y := by
    funext s
    exact (g_fam s).g_raise T X Y
  have h2 : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise T X) Y) t =
            TimeDerivative.partial_t (fun s => T X Y) t := by
    rw [h1]
  have h3 : TimeDerivative.partial_t (fun s => T X Y) t = 0 := by
    exact MetricTimeDerivativeRules.t_const_R g_fam (T X Y) t
  have h4 : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise T X) Y) t =
            (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y +
            (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y +
            (g_fam t).g ((g_fam t).raise T X) (TimeDerivative.partial_t (fun s => Y) t) := by
    exact MetricTimeDerivativeRules.t_metric (fun s => (g_fam s).raise T X) (fun s => Y) t
  have h5 : TimeDerivative.partial_t (fun s => Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Y t
  have h6 : (g_fam t).g ((g_fam t).raise T X) (TimeDerivative.partial_t (fun s => Y) t) = 0 := by
    rw [h5]
    exact metric_zero_right ((g_fam t).toNonDegenerateMetric.toMetricTensor) ((g_fam t).raise T X)
  have h7 : 0 = (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y +
                (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y := by
    calc 0 = TimeDerivative.partial_t (fun s => T X Y) t := h3.symm
         _ = TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise T X) Y) t := h2.symm
         _ = (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y +
             (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y +
             (g_fam t).g ((g_fam t).raise T X) (TimeDerivative.partial_t (fun s => Y) t) := h4
         _ = (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y +
             (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y + 0 := by rw [h6]
         _ = (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y +
             (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y := by abel
  calc (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y
     = (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y +
       (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y
       - (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y := by abel
     _ = 0 - (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y := by rw [← h7]
     _ = - (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y := by abel

-- 6. Metric Trace Variation
/-- Time variation of the trace of a fixed metric. -/
lemma tr_g_variation {Time R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TR_OP : TraceOperator R V] [TR : TraceLinearityRules R V]
  [TimeDerivativeRules Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (T : SmoothBilinearForm R V) (t : Time) :
  (TimeDerivative.partial_t (fun s => (@TraceOperator.trace R V TR_OP (fun X => (g_fam s).raise T X) : R)) t : R) =
  - tensorInnerProduct (g_fam t) (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) T := by
  have h1 : (TimeDerivative.partial_t (fun s => (@TraceOperator.trace R V TR_OP (fun X => (g_fam s).raise T X) : R)) t : R) =
            (@TraceOperator.trace R V TR_OP (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) : R) :=
    MetricTimeDerivativeRules.t_trace g_fam (fun s X => (g_fam s).raise T X) t
  have vector_eq : ∀ X, TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t =
                        - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X) := by
    intro X
    apply (g_fam t).toNonDegenerateMetric.eq_of_forall_g_eq
    intro Y
    have step1 := raise_variation g_fam T X Y t
    have step2 : (g_fam t).g (- (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) Y =
                 - (g_fam t).g ((g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) Y := by
      exact metric_neg_left ((g_fam t).toNonDegenerateMetric.toMetricTensor) ((g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) Y
    have step3 : (g_fam t).g ((g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) Y =
                 (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t).val ((g_fam t).raise T X) Y := by
      exact (g_fam t).g_raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X) Y
    rw [step2, step3]
    exact step1
  have h2 : (@TraceOperator.trace R V TR_OP (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) : R) =
            (@TraceOperator.trace R V TR_OP (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) := by
    have heq : (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) =
               (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) := by
      funext X
      exact vector_eq X
    rw [heq]
  have h3 : (@TraceOperator.trace R V TR_OP (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) =
            (@TraceOperator.trace R V TR_OP (fun X => (-1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) := by
    have heq2 : (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) =
                (fun X => (-1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) := by
      funext X
      have eqst : (-1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X) =
                  - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X) := by
        rw [neg_smul, one_smul]
      exact eqst.symm
    rw [heq2]
  have h4 : (@TraceOperator.trace R V TR_OP (fun X => (-1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) =
            (-1:R) * (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) := by
    exact TR.trace_smul
  have h5 : (-1:R) * (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) =
            - (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) := by
    ring
  have h6 : tensorInnerProduct (g_fam t) (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) T =
            (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) := by
    rfl
  calc (TimeDerivative.partial_t (fun s => (@TraceOperator.trace R V TR_OP (fun X => (g_fam s).raise T X) : R)) t : R)
     = (@TraceOperator.trace R V TR_OP (fun X => TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) : R) := h1
   _ = (@TraceOperator.trace R V TR_OP (fun X => - (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) := h2
   _ = (@TraceOperator.trace R V TR_OP (fun X => (-1:R) • (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) := h3
   _ = (-1:R) * (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) := h4
   _ = - (@TraceOperator.trace R V TR_OP (fun X => (g_fam t).raise (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) ((g_fam t).raise T X)) : R) := h5
   _ = - tensorInnerProduct (g_fam t) (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toMetricTensor) t) T := by rw [h6]
