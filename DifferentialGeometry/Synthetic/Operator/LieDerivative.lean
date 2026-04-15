import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Lie Derivative
Definition of the Lie derivative of a metric tensor.
-/

section LieDeriv

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- The Lie derivative of a metric tensor along a vector field. -/
noncomputable def lieDerivMetric (emb : DerivationEmbedding k R V) (met : MetricDuality R V) (X Y Z : V) : R :=
  action emb X (met.g Y Z) - met.g (bracket emb X Y) Z - met.g Y (bracket emb X Z)

private lemma g_sub_left (met : MetricDuality R V) (A B C : V) :
    met.g (A - B) C = met.g A C - met.g B C := by
  calc met.g (A - B) C = met.g (A + -B) C := by rw [sub_eq_add_neg]
    _ = met.g A C + met.g (-B) C := met.g_add_left _ _ _
    _ = met.g A C + -(met.g B C) := by
        congr 1; rw [show -B = (-1 : R) • B from by rw [neg_one_smul], met.g_smul_left]; ring
    _ = met.g A C - met.g B C := by rw [sub_eq_add_neg]

private lemma g_sub_right (met : MetricDuality R V) (A B C : V) :
    met.g A (B - C) = met.g A B - met.g A C := by
  rw [met.g_symm A (B - C), g_sub_left, met.g_symm B, met.g_symm C]

/-- The Lie derivative of the metric equals the symmetrized covariant derivative. -/
theorem lieDerivMetric_eq_nabla
    (emb : DerivationEmbedding k R V)
    (met : MetricDuality R V)
    (conn : V → V → V)
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (X Y Z : V) :
    lieDerivMetric emb met X Y Z = met.g (conn Y X) Z + met.g Y (conn Z X) := by
  unfold lieDerivMetric action
  rw [h_mc X Y Z]
  have h1 : bracket emb X Y = conn X Y - conn Y X := (h_tf X Y).symm
  have h2 : bracket emb X Z = conn X Z - conn Z X := (h_tf X Z).symm
  rw [h1, h2, g_sub_left, g_sub_right]
  abel

end LieDeriv
