import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Algebra.Metric
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import DifferentialGeometry.Synthetic.Geometry.Connection

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Curvature Tensors
Definitions for Riemann curvature, Ricci curvature, and Scalar curvature.
-/

open AbstractDerivationAction
open AbstractLieBracket
open DifferentialGeometry TensorAlgebra

variable {R V : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V]

section Curvature

variable [AbstractLieBracket V] (conn : AbstractAffineConnection R V)

/-- Riemann curvature tensor.
Input: (X : V, Y : V, Z : V)
Output: V -/
def Rm (X Y Z : V) : V :=
  conn.nabla X (conn.nabla Y Z) - conn.nabla Y (conn.nabla X Z) - conn.nabla (bracket X Y) Z

/-- Ricci curvature tensor.
Input: (X : V, Y : V)
Output: R -/
def Rc [TraceOperator R V] (X Y : V) : R :=
  TraceOperator.trace (fun Z => Rm conn Z X Y)

/-- Scalar curvature.
Input: (AbstractMetricTensor R V)
Output: R -/
def ScalarCurvature [TraceOperator R V] (metric : AbstractMetricTensor R V) [MetricTraceOperator R V metric] : R :=
  MetricTraceOperator.metric_trace metric (Rc conn)

end Curvature
