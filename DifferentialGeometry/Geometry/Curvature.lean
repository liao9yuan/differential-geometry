import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Geometry.Metric
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import DifferentialGeometry.Geometry.Connection

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Curvature Tensors
Riemann, Ricci, and Scalar Curvature.
-/

open DerivationAction
open LieBracket

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [DerivationAction R V]

section Curvature

variable [LieBracket V] (conn : AffineConnection R V)

-- Riemann Curvature Tensor Rm(X,Y)Z
def Rm (X Y Z : V) : V :=
  conn.nabla X (conn.nabla Y Z) - conn.nabla Y (conn.nabla X Z) - conn.nabla (bracket X Y) Z

-- Ricci Curvature Tensor Rc(X,Y)
def Rc [TraceOperator R V] (X Y : V) : R :=
  TraceOperator.trace (fun Z => Rm conn Z X Y)

-- Scalar Curvature (R)
def ScalarCurvature [TraceOperator R V] (metric : MetricTensor R V) [MetricTraceOperator R V metric] : R :=
  MetricTraceOperator.metric_trace metric (Rc conn)

end Curvature
