import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Geometry.Metric
import DifferentialGeometry.Geometry.Connection
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

open DerivationAction

/-- Cyclic property of the metric trace operator for bilinear forms evaluated via the sharp operator.
Input: (MetricTensor R V)
Output: Type -/
class MetricTraceCyclic (g : MetricTensor R V) [MetricTraceOperator R V g] [InverseMetric R V g] where
  trace_cyclic : ∀ (T S : SmoothBilinearForm R V),
    MetricTraceOperator.metric_trace g (fun X Y => S (InverseMetric.inv g (fun Z => T X Z)) Y) =
    MetricTraceOperator.metric_trace g (fun X Y => T (InverseMetric.inv g (fun Z => S X Z)) Y)

variable (g : MetricTensor R V) [MetricTraceOperator R V g] [InverseMetric R V g]

/-- The inner product of two (0,2)-tensors induced by a metric.
Input: (MetricTensor R V, SmoothBilinearForm R V, SmoothBilinearForm R V)
Output: R -/
def tensorInnerProduct (T S : SmoothBilinearForm R V) : R :=
  MetricTraceOperator.metric_trace g (fun X Y => T (InverseMetric.inv g (fun Z => S X Z)) Y)

/-- The squared norm of a (0,2)-tensor induced by a metric.
Input: (MetricTensor R V, SmoothBilinearForm R V)
Output: R -/
def tensorNormSq (T : SmoothBilinearForm R V) : R :=
  tensorInnerProduct g T T

/-- The tensor inner product is symmetric.
Input: (MetricTensor R V, SmoothBilinearForm R V, SmoothBilinearForm R V)
Output: Prop -/
lemma tensorInnerProduct_symm [MetricTraceCyclic g] (T S : SmoothBilinearForm R V) :
  tensorInnerProduct g T S = tensorInnerProduct g S T := by
  dsimp [tensorInnerProduct]
  exact Eq.symm (MetricTraceCyclic.trace_cyclic (g := g) T S)

/-- The tensor inner product is additive in the first argument.
Input: (MetricTensor R V, SmoothBilinearForm R V, SmoothBilinearForm R V, SmoothBilinearForm R V)
Output: Prop -/
lemma tensorInnerProduct_add_left [MetricTraceRules R V g] (T₁ T₂ S : SmoothBilinearForm R V) :
  tensorInnerProduct g (T₁ + T₂) S = tensorInnerProduct g T₁ S + tensorInnerProduct g T₂ S := by
  dsimp [tensorInnerProduct]
  have h1 : (fun X Y : V => (T₁ + T₂) (InverseMetric.inv g (fun Z => S X Z)) Y) =
            (fun X Y : V => T₁ (InverseMetric.inv g (fun Z => S X Z)) Y + T₂ (InverseMetric.inv g (fun Z => S X Z)) Y) := by
    funext X Y
    rfl
  rw [h1, MetricTraceRules.trace_add]

/-- The tensor inner product is linear with respect to scalar multiplication in the first argument.
Input: (R, MetricTensor R V, SmoothBilinearForm R V, SmoothBilinearForm R V)
Output: Prop -/
lemma tensorInnerProduct_smul_left [MetricTraceRules R V g] (a : R) (T S : SmoothBilinearForm R V) :
  tensorInnerProduct g (a • T) S = a * tensorInnerProduct g T S := by
  dsimp [tensorInnerProduct]
  have h1 : (fun X Y : V => (a • T) (InverseMetric.inv g (fun Z => S X Z)) Y) =
            (fun X Y : V => a * T (InverseMetric.inv g (fun Z => S X Z)) Y) := by
    funext X Y
    rfl
  rw [h1, MetricTraceRules.trace_smul]
