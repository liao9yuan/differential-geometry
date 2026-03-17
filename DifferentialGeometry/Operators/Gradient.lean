import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Algebra.Musical
import DifferentialGeometry.Geometry.Connection
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [AbstractDerivationAction R V]

open AbstractDerivationAction

/-- Gradient of a scalar function `u`.
Input: (AbstractMetricTensor R V, R)
Output: V -/
def grad (metric : MetricDuality R V) (u : R) : V :=
  metric.sharp (fun X => action X u)

lemma g_grad (metric : MetricDuality R V) (u : R) (X : V) :
  metric.g (grad metric u) X = action X u := by
  dsimp [grad]
  exact metric.g_sharp (fun Y => action Y u) X

lemma grad_add [AbstractLieBracket V] [DerivationRules R V] (metric : MetricDuality R V) (f g : R) : grad metric (f + g) = grad metric f + grad metric g := by
  apply metric.toNonDegenerateMetric.eq_of_forall_g_eq
  intro X
  have h1 : metric.g (grad metric (f + g)) X = AbstractDerivationAction.action X (f + g) := g_grad metric (f + g) X
  have h2 : AbstractDerivationAction.action X (f + g) = AbstractDerivationAction.action X f + AbstractDerivationAction.action X g := DerivationRules.action_add_right X f g
  have h3 : metric.g (grad metric f + grad metric g) X = metric.g (grad metric f) X + metric.g (grad metric g) X := metric.toNonDegenerateMetric.toAbstractMetricTensor.bilinear_add_left _ _ _
  have h4 : metric.g (grad metric f) X = AbstractDerivationAction.action X f := g_grad metric f X
  have h5 : metric.g (grad metric g) X = AbstractDerivationAction.action X g := g_grad metric g X
  rw [h4, h5] at h3
  rw [h1, h2, ← h3]

lemma grad_sub [AbstractLieBracket V] [DerivationRules R V] (metric : MetricDuality R V) (f g : R) : grad metric (f - g) = grad metric f - grad metric g := by
  apply metric.toNonDegenerateMetric.eq_of_forall_g_eq
  intro X
  have h1 : metric.g (grad metric (f - g)) X = action X (f - g) := g_grad metric (f - g) X
  have action_sub : action X (f - g) = action X f - action X g := by
    have hz : f - g = f + -g := sub_eq_add_neg f g
    rw [hz]
    have h_add : action X (f + -g) = action X f + action X (-g) := DerivationRules.action_add_right X f (-g)
    rw [h_add]
    have h_neg : action X (-g) = - action X g := action_neg X g
    rw [h_neg]
    exact (sub_eq_add_neg (action X f) (action X g)).symm
  have h2 : metric.g (grad metric f - grad metric g) X = metric.g (grad metric f) X - metric.g (grad metric g) X := by
    have hsub : grad metric f - grad metric g = grad metric f + - grad metric g := sub_eq_add_neg _ _
    rw [hsub, metric.toNonDegenerateMetric.toAbstractMetricTensor.bilinear_add_left]
    have hneg : metric.g (- grad metric g) X = - metric.g (grad metric g) X := by
      have hmm : - grad metric g = (-1:R) • grad metric g := by rw [neg_one_smul]
      rw [hmm, metric.toNonDegenerateMetric.toAbstractMetricTensor.bilinear_smul_left]
      ring
    rw [hneg, ← sub_eq_add_neg]
  have h4 : metric.g (grad metric f) X = action X f := g_grad metric f X
  have h5 : metric.g (grad metric g) X = action X g := g_grad metric g X
  rw [h4, h5] at h2
  rw [h1, action_sub, ← h2]
