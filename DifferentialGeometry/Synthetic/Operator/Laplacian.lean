import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Operator.Hessian
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Operator.CovariantDerivative
import DifferentialGeometry.Synthetic.Algebra.Trace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false
set_option linter.style.docString false

open AbstractDerivationAction DifferentialGeometry TensorAlgebra

variable {R V : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V]

/-- Laplacian of a function defined as the metric trace of its Hessian abstract tensor form.
Input: (MetricDuality R V, AbstractAffineConnection R V, R)
Output: R -/
def laplacian (metric : MetricDuality R V)
    (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] (u : R) : R :=
  tensor_eval (metric_trace metric (0: Fin 2) (0: Fin 1) (hessianForm metric conn u)) ![] ![]

/-- $\Delta(f+g) = \Delta f + \Delta g$ -/
lemma laplacian_add (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] [AbstractLieBracket V] [DerivationRules R V] (f g : R) :
  laplacian metric conn (f + g) = laplacian metric conn f + laplacian metric conn g := by
  sorry


/-- $\Delta(f-g) = \Delta f - \Delta g$ -/
lemma laplacian_sub (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] [AbstractLieBracket V] [DerivationRules R V] (f g : R) :
  laplacian metric conn (f - g) = laplacian metric conn f - laplacian metric conn g := by
  sorry

/-- $\Delta(c \cdot f) = c \cdot \Delta f$ -/
lemma laplacian_smul (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn] [AbstractLieBracket V] [DerivationRules R V] (c f : R) :
  laplacian metric conn (c * f) = c * laplacian metric conn f := by
  sorry

section GenericLaplacian

/--
Operator mapping a generic V → V → Tensor form into its metric trace.
Used for constructing the generic Laplacian from the second covariant derivative.
-/
class MetricTensorTraceOperator {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    (metric : AbstractMetricTensor R V) {r s : ℕ} where
  metric_trace_tensor : (V → V → AbstractTensor R V r s) → AbstractTensor R V r s

/--
Requirements for trace linearity on the generalized trace operator.
-/
class MetricTensorTraceRules {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    (metric : AbstractMetricTensor R V) {r s : ℕ} [MetricTensorTraceOperator metric (r := r) (s := s)] where
  trace_add : ∀ (A B : V → V → AbstractTensor R V r s),
    MetricTensorTraceOperator.metric_trace_tensor metric (fun X Y => TensorAlgebra.add (A X Y) (B X Y)) =
    TensorAlgebra.add (MetricTensorTraceOperator.metric_trace_tensor metric A) (MetricTensorTraceOperator.metric_trace_tensor metric B)
  trace_smul : ∀ (c : R) (A : V → V → AbstractTensor R V r s),
    MetricTensorTraceOperator.metric_trace_tensor metric (fun X Y => TensorAlgebra.smul c (A X Y)) =
    TensorAlgebra.smul c (MetricTensorTraceOperator.metric_trace_tensor metric A)

/--
The second covariant derivative $\nabla^2_{X,Y} T$ for an arbitrary tensor.
Defined as $\nabla_X (\nabla_Y T) - \nabla_{\nabla_X Y} T$.
-/
def SecondCovDerivTensor {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]
    (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    {r s : ℕ} (T : AbstractTensor R V r s) (X Y : V) : AbstractTensor R V r s :=
  let nXY_T := genericCovDeriv conn (conn.nabla X Y) T
  let nY_T := genericCovDeriv conn Y T
  let nX_nY_T := genericCovDeriv conn X nY_T
  TensorAlgebra.add nX_nY_T (TensorAlgebra.smul (-1:R) nXY_T)

/--
The generic rough tensor Laplacian $\Delta T$.
Constructed as $\text{tr}_g(\nabla^2 T)$.
-/
def genericLaplacian {R V : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]
    (metric : AbstractMetricTensor R V) {r s : ℕ} [MetricTensorTraceOperator metric (r := r) (s := s)]
    (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]
    (T : AbstractTensor R V r s) : AbstractTensor R V r s :=
  MetricTensorTraceOperator.metric_trace_tensor metric (SecondCovDerivTensor conn T)

end GenericLaplacian
