import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Analysis.TensorInnerProduct
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Operator.Time
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

open AbstractDerivationAction AbstractLieBracket DifferentialGeometry TensorAlgebra

variable {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]




-- 3. Metric Variation Form
/-- Operator for metric variation.
Constructed explicitly from bilinear function of metric derivative.
-/
def metric_var_form {Time R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → AbstractMetricTensor R V) (t : Time) : AbstractBilinearForm R V :=
  TensorTimeCalculus.partial_t_tensor t (fun s => (g_fam s).g_tensor)

lemma metric_var_form_eval {Time R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V] (g_fam : Time → AbstractMetricTensor R V) (t : Time) (X Y : V) :
  tensor_eval (metric_var_form g_fam t) ![X, Y] ![] = TimeDerivative.partial_t (fun s => tensor_eval ((g_fam s).g_tensor) ![X, Y] ![]) t := by
  unfold metric_var_form
  exact TensorTimeCalculus.t_eval (vs := ![X, Y]) (αs := ![]) (fun s => (g_fam s).g_tensor) t

-- 4. Metric Time Derivative Calculus Axioms
/-- Product rule and constant rules for time derivatives involving the metric. -/
class MetricTimeDerivativeRules (Time R V : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V) where
  t_const_R : ∀ (c : R) (t : Time), TimeDerivative.partial_t (fun _ => c) t = 0
  t_const_V : ∀ (X : V) (t : Time), TimeDerivative.partial_t (fun _ => X) t = 0
  t_metric : ∀ (X Y : Time → V) (t : Time),
    TimeDerivative.partial_t (fun s => (g_fam s).g (X s) (Y s)) t =
    tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(X t), (Y t)] ![] +
    (g_fam t).g (TimeDerivative.partial_t X t) (Y t) +
    (g_fam t).g (X t) (TimeDerivative.partial_t Y t)
  t_metric_trace : ∀ (T : AbstractBilinearForm R V) (t : Time) (_ : TensorInnerProductRules R V (g_fam t)),
    TimeDerivative.partial_t (fun s => tensor_eval (metric_trace (g_fam s) (0: Fin 2) (0: Fin 1) T) ![] ![]) t =
    - tensorInnerProduct (g_fam t) (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) T
  /-- Product rule for metric trace with varying tensor:
      ∂_t[tr_{g(s)}(T(s))] = -⟨∂_t g, T(t)⟩ + tr_{g(t)}(∂_t T). -/
  t_metric_trace_varying : ∀ (T : Time → AbstractBilinearForm R V) (t : Time) (_ : TensorInnerProductRules R V (g_fam t)),
    TimeDerivative.partial_t (fun s => tensor_eval (metric_trace (g_fam s) (0: Fin 2) (0: Fin 1) (T s)) ![] ![]) t =
    - tensorInnerProduct (g_fam t) (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) (T t)
    + tensor_eval (metric_trace (g_fam t) (0: Fin 2) (0: Fin 1) (TensorTimeCalculus.partial_t_tensor t T)) ![] ![]

lemma metric_zero_right {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) (X : V) : metric.g X 0 = 0 := by
  have h1 : metric.g X (0 + 0) = metric.g X 0 + metric.g X 0 := by
    have h1a : metric.g (0 + 0) X = metric.g 0 X + metric.g 0 X := metric.bilinear_add_left 0 0 X
    have h1b : metric.g X (0 + 0) = metric.g (0 + 0) X := metric.symm X (0 + 0)
    have h1c : metric.g X 0 = metric.g 0 X := metric.symm X 0
    rw [h1b, h1a, ← h1c]
  calc metric.g X 0 = metric.g X 0 + metric.g X 0 - metric.g X 0 := by abel
    _ = metric.g X (0 + 0) - metric.g X 0 := by rw [← h1]
    _ = metric.g X 0 - metric.g X 0 := by rw [add_zero]
    _ = 0 := by abel

lemma metric_zero_left {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] (metric : AbstractMetricTensor R V) (X : V) : metric.g 0 X = 0 := by
  have h1 : metric.g 0 X = metric.g X 0 := metric.symm 0 X
  rw [h1]
  exact metric_zero_right metric X

-- 5. Inverse Metric Variation
/-- Variation of the raised index tensor (inverse metric). -/
lemma raise_variation {Time R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (T : AbstractBilinearForm R V) (X Y : V) (t : Time) :
  (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y =
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] := by
  have h1 : (fun s => (g_fam s).g ((g_fam s).raise T X) Y) = (fun s => tensor_eval (R:=R) (V:=V) T ![X, Y] ![]) := by
    funext s
    exact (g_fam s).g_raise T X Y
  have h2 : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise T X) Y) t = TimeDerivative.partial_t (fun s : Time => tensor_eval (R:=R) (V:=V) T ![X, Y] ![]) t := by rw [h1]
  have h3 : TimeDerivative.partial_t (fun s : Time => tensor_eval (R:=R) (V:=V) T ![X, Y] ![]) t = 0 := MetricTimeDerivativeRules.t_const_R g_fam (tensor_eval (R:=R) (V:=V) T ![X, Y] ![]) t
  have h4 : TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise T X) Y) t =
    tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![(g_fam t).raise T X, Y] ![] +
    (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y +
    (g_fam t).g ((g_fam t).raise T X) (TimeDerivative.partial_t (fun _ => Y) t) := MetricTimeDerivativeRules.t_metric (fun s => (g_fam s).raise T X) (fun _ => Y) t
  have h5 : TimeDerivative.partial_t (fun _ => Y) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Y t
  have h6 : (g_fam t).g ((g_fam t).raise T X) (TimeDerivative.partial_t (fun _ => Y) t) = 0 := by
    rw [h5]
    exact metric_zero_right _ _
  have h_comm : tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] + (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y = (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y + tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] := add_comm _ _
  calc (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y
    _ = (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y + tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] := by abel
    _ = tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] + (g_fam t).g (TimeDerivative.partial_t (fun s => (g_fam s).raise T X) t) Y + (g_fam t).g ((g_fam t).raise T X) (TimeDerivative.partial_t (fun _ => Y) t) - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] := by
      rw [h6, add_zero, h_comm]
    _ = TimeDerivative.partial_t (fun s => (g_fam s).g ((g_fam s).raise T X) Y) t - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] := by rw [← h4]
    _ = 0 - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] := by rw [h2, h3]
    _ = - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((g_fam t).raise T X), Y] ![] := by abel

-- 6. Metric Trace Variation
/-- Time variation of the trace of a fixed metric. -/
lemma tr_g_variation {Time R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (T : AbstractBilinearForm R V) (t : Time) [IR : TensorInnerProductRules R V (g_fam t)] :
  TimeDerivative.partial_t (fun s => tensor_eval (metric_trace (g_fam s) (0: Fin 2) (0: Fin 1) T) ![] ![]) t =
  - tensorInnerProduct (g_fam t) (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) T := by
  exact MetricTimeDerivativeRules.t_metric_trace (g_fam := g_fam) T t IR

-- 7. Variation of the Connection (Palatini Identity)



variable [AbstractDerivationAction R V] [AbstractLieBracket V] [DerivationRules R V] [Invertible (2 : R)]

/-- The unique Levi-Civita connection associated to a metric family at time s. -/
abbrev nabla_fam {Time : Type} (g_fam : Time → MetricDuality R V) (t : Time) : AbstractAffineConnection R V :=
  koszul_connection (g_fam t)

/-- The covariant derivative of the symmetric bilinear form h = ∂_t g at time t.
(∇_X h)(Y, Z) = X(h(Y, Z)) - h(∇_X Y, Z) - h(Y, ∇_X Z)
-/
def h_cov_deriv {Time : Type} [TimeDerivative Time R] [TimeDerivative Time V] [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V) (t : Time) (X Y Z : V) : R :=
  action X (tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![Y, Z] ![])
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![((nabla_fam g_fam t).nabla X Y), Z] ![]
  - tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![Y, ((nabla_fam g_fam t).nabla X Z)] ![]

/-- Palatini identity for the variation of the Levi-Civita connection. -/
lemma connection_variation {Time : Type} [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [ActionTimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]
  (X Y Z : V) (t : Time) :
  2 * (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z =
  h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y := by
  let h (A B : V) := tensor_eval (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t) ![A, B] ![]
  let n (A B : V) := (nabla_fam g_fam t).nabla A B

  -- Time derivative linearity
  have l_add : ∀ (f₁ f₂ : Time → R), TimeDerivative.partial_t (fun s => f₁ s + f₂ s) t = TimeDerivative.partial_t f₁ t + TimeDerivative.partial_t f₂ t := fun f₁ f₂ => TimeDerivativeRules.t_add V f₁ f₂ t
  have l_sub : ∀ (f₁ f₂ : Time → R), TimeDerivative.partial_t (fun s => f₁ s - f₂ s) t = TimeDerivative.partial_t f₁ t - TimeDerivative.partial_t f₂ t := by
    intro f₁ f₂
    have hr : (fun s => f₁ s - f₂ s) = (fun s => f₁ s + (-1:R) * f₂ s) := by funext s; ring
    rw [hr, l_add f₁ _, TimeDerivativeRules.t_smul V (-1:R) f₂ t]
    ring

  -- Constant vector derivatives
  have pt_Z : TimeDerivative.partial_t (fun _ : Time => Z) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam Z t

  -- Product rule for ∂_t of g(∇_X Y, Z)
  have pt_term : TimeDerivative.partial_t (fun s => (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) t =
    h (n X Y) Z +
    (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z +
    (g_fam t).g ((nabla_fam g_fam t).nabla X Y) (TimeDerivative.partial_t (fun _ : Time => Z) t) :=
    MetricTimeDerivativeRules.t_metric (g_fam := g_fam) (fun s => (nabla_fam g_fam s).nabla X Y) (fun _ => Z) t

  have h_zero : (g_fam t).g ((nabla_fam g_fam t).nabla X Y) (TimeDerivative.partial_t (fun _ : Time => Z) t) = 0 := by
    rw [pt_Z]; exact metric_zero_right _ _

  -- LHS expansion: ∂_t(2*g(∇_X Y, Z)) = 2*(h(∇_X Y, Z) + g(∂_t(∇_X Y), Z))
  have hLHS : TimeDerivative.partial_t (fun s => 2 * (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) t =
    2 * (h (n X Y) Z + (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z) := by
    have pt_smul := TimeDerivativeRules.t_smul V 2 (fun s => (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) t
    rw [pt_term, h_zero] at pt_smul
    have : h (n X Y) Z +
      (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z + 0 =
      h (n X Y) Z +
      (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z := by abel
    rw [this] at pt_smul
    exact pt_smul

  -- Helper: ∂_t(g(A, B)) = h(A, B) for constant A, B
  have h_eval : ∀ (A B : V), TimeDerivative.partial_t (fun s => (g_fam s).g A B) t = h A B := by
    intro A B
    exact (metric_var_form_eval (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t A B).symm

  -- Time derivatives of the action terms in the Koszul formula
  have pt1 : TimeDerivative.partial_t (fun s => action X ((g_fam s).g Y Z)) t = action X (h Y Z) := by
    have pt1_base := ActionTimeDerivativeRules.t_action X (fun s => (g_fam s).g Y Z) t
    rw [h_eval Y Z] at pt1_base
    exact pt1_base
  have pt2 : TimeDerivative.partial_t (fun s => action Y ((g_fam s).g X Z)) t = action Y (h X Z) := by
    have pt2_base := ActionTimeDerivativeRules.t_action Y (fun s => (g_fam s).g X Z) t
    rw [h_eval X Z] at pt2_base
    exact pt2_base
  have pt3 : TimeDerivative.partial_t (fun s => action Z ((g_fam s).g X Y)) t = action Z (h X Y) := by
    have pt3_base := ActionTimeDerivativeRules.t_action Z (fun s => (g_fam s).g X Y) t
    rw [h_eval X Y] at pt3_base
    exact pt3_base

  -- Time derivatives of the bracket metric terms: ∂_t(g(A, [B,C])) = h(A, [B,C])
  have pt_bracket : ∀ (A B C : V),
      TimeDerivative.partial_t (fun s => (g_fam s).g A (bracket B C)) t = h A (bracket B C) := by
    intro A B C
    have pt_A : TimeDerivative.partial_t (fun _ : Time => A) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam A t
    have pt_bBC : TimeDerivative.partial_t (fun _ : Time => bracket B C) t = 0 := MetricTimeDerivativeRules.t_const_V g_fam (bracket B C) t
    have pt_m := MetricTimeDerivativeRules.t_metric (g_fam := g_fam) (fun _ => A) (fun _ => bracket B C) t
    rw [pt_A, pt_bBC] at pt_m
    have hz1 : (g_fam t).g 0 (bracket B C) = 0 := metric_zero_left _ _
    have hz2 : (g_fam t).g A 0 = 0 := metric_zero_right _ _
    rw [hz1, hz2] at pt_m
    linarith [pt_m]

  have pt4 : TimeDerivative.partial_t (fun s => (g_fam s).g X (bracket Y Z)) t = h X (bracket Y Z) := pt_bracket X Y Z
  have pt5 : TimeDerivative.partial_t (fun s => (g_fam s).g Y (bracket Z X)) t = h Y (bracket Z X) := pt_bracket Y Z X
  have pt6 : TimeDerivative.partial_t (fun s => (g_fam s).g Z (bracket X Y)) t = h Z (bracket X Y) := pt_bracket Z X Y

  -- Time derivative of the full RHS of the Koszul formula
  have hRHS : TimeDerivative.partial_t (fun s =>
    action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y)
    - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X) + (g_fam s).g Z (bracket X Y)) t =
    action X (h Y Z) + action Y (h X Z) - action Z (h X Y) - h X (bracket Y Z) + h Y (bracket Z X) + h Z (bracket X Y) := by
    have step1 := l_add
      (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y) - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X))
      (fun s => (g_fam s).g Z (bracket X Y))
    have step2 := l_add
      (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y) - (g_fam s).g X (bracket Y Z))
      (fun s => (g_fam s).g Y (bracket Z X))
    have step3 := l_sub
      (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y))
      (fun s => (g_fam s).g X (bracket Y Z))
    have step4 := l_sub
      (fun s => action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z))
      (fun s => action Z ((g_fam s).g X Y))
    have step5 := l_add
      (fun s => action X ((g_fam s).g Y Z))
      (fun s => action Y ((g_fam s).g X Z))
    rw [step1, step2, step3, step4, step5, pt1, pt2, pt3, pt4, pt5, pt6]

  -- Koszul formula: 2*g(∇_X Y, Z) = Koszul 6-term expression
  have koszul_eq : ∀ s, 2 * (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z =
    action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y)
    - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X) + (g_fam s).g Z (bracket X Y) := by
    intro s
    exact levi_civita_uniqueness (nabla_fam g_fam s) ((g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) X Y Z

  -- Connect LHS and RHS via functional equality and differentiation
  have h_base : TimeDerivative.partial_t (fun s => 2 * (g_fam s).g ((nabla_fam g_fam s).nabla X Y) Z) t =
    TimeDerivative.partial_t (fun s =>
      action X ((g_fam s).g Y Z) + action Y ((g_fam s).g X Z) - action Z ((g_fam s).g X Y)
      - (g_fam s).g X (bracket Y Z) + (g_fam s).g Y (bracket Z X) + (g_fam s).g Z (bracket X Y)) t := by
    congr 1; funext s; exact koszul_eq s

  rw [hLHS, hRHS] at h_base

  -- h symmetry and bilinearity
  have torsion_free : ∀ A B : V, n A B - n B A = bracket A B := TorsionFree.torsion_zero (conn := (nabla_fam g_fam t))

  have h_symm : ∀ A B : V, h A B = h B A := by
    intro A B
    calc h A B = TimeDerivative.partial_t (fun s => (g_fam s).g A B) t := (h_eval A B).symm
      _ = TimeDerivative.partial_t (fun s => (g_fam s).g B A) t := by congr 1; funext s; exact (g_fam s).symm A B
      _ = h B A := h_eval B A

  have h_add_right : ∀ A B C : V, h A (B + C) = h A B + h A C :=
    tensor_eval_add_right (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t)
  have h_smul_right : ∀ (c : R) (A B : V), h A (c • B) = c * h A B :=
    tensor_eval_smul_right (metric_var_form (fun s => (g_fam s).toNonDegenerateMetric.toAbstractMetricTensor) t)

  have h_neg_right : ∀ A B : V, h A (-B) = - h A B := by
    intro A B
    calc h A (-B) = h A ((-1:R) • B) := by rw [neg_one_smul]
      _ = (-1:R) * h A B := h_smul_right (-1) A B
      _ = - h A B := by ring

  have h_sub_right : ∀ A B C : V, h A (B - C) = h A B - h A C := by
    intro A B C
    calc h A (B - C) = h A (B + -C) := by rw [sub_eq_add_neg]
      _ = h A B + h A (-C) := h_add_right A B (-C)
      _ = h A B + - h A C := by rw [h_neg_right]
      _ = h A B - h A C := by ring

  -- Decompose brackets using torsion-free
  have b1 : h X (bracket Y Z) = h X (n Y Z) - h X (n Z Y) := by rw [← torsion_free Y Z, h_sub_right]
  have b2 : h Y (bracket Z X) = h Y (n Z X) - h Y (n X Z) := by rw [← torsion_free Z X, h_sub_right]
  have b3 : h Z (bracket X Y) = h Z (n X Y) - h Z (n Y X) := by rw [← torsion_free X Y, h_sub_right]

  -- Expand h_cov_deriv sum
  have eq_cov_deriv : h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y =
    action X (h Y Z) - h (n X Y) Z - h Y (n X Z) +
    (action Y (h X Z) - h (n Y X) Z - h X (n Y Z)) -
    (action Z (h X Y) - h (n Z X) Y - h X (n Z Y)) := by
    dsimp [h_cov_deriv, h, n]

  -- Symmetry lemmas
  have a1 : h (n X Y) Z = h Z (n X Y) := h_symm _ _
  have a2 : h (n Y X) Z = h Z (n Y X) := h_symm _ _
  have a3 : h (n Z X) Y = h Y (n Z X) := h_symm _ _

  -- Key algebraic step: rewrite Koszul variation as h_cov_deriv sum + 2*h(Z, ∇_X Y)
  have step_rhs : action X (h Y Z) + action Y (h X Z) - action Z (h X Y) - h X (bracket Y Z) + h Y (bracket Z X) + h Z (bracket X Y) =
    h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y + 2 * h Z (n X Y) := by
    rw [eq_cov_deriv, b1, b2, b3, a1, a2, a3]
    ring

  rw [step_rhs] at h_base

  -- Final calc: extract 2*g(∂_t(∇_X Y), Z)
  calc 2 * (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z
     = 2 * (h (n X Y) Z + (g_fam t).g (TimeDerivative.partial_t (fun s => (nabla_fam g_fam s).nabla X Y) t) Z) - 2 * h (n X Y) Z := by ring
   _ = h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y + 2 * h Z (n X Y) - 2 * h (n X Y) Z := by rw [h_base]
   _ = h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y + 2 * h Z (n X Y) - 2 * h Z (n X Y) := by rw [a1]
   _ = h_cov_deriv g_fam t X Y Z + h_cov_deriv g_fam t Y X Z - h_cov_deriv g_fam t Z X Y := by ring
