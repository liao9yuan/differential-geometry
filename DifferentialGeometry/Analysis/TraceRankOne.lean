import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Metric

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Rank-One Metric Trace Rules
Algebraic definition of rank-1 trace.
-/

-- Axiomatic rules for the trace of rank-1 operators to support divergence product rule.
class MetricTraceRankOneRules (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [ScalarMul R V] (metric : MetricTensor R V) [MetricTraceOperator R V metric] where
  trace_rank_one : ∀ U W : V, MetricTraceOperator.metric_trace metric (fun Y Z => metric.g U Y * metric.g W Z) = metric.g U W
