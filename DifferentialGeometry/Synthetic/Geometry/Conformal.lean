import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Algebra.VectorField
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open AbstractDerivationAction AbstractLieBracket DifferentialGeometry TensorAlgebra

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V]

-- Defines the conformal transformation of an affine connection algebraically.
def conformalConnection_nabla (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) (u : R) (X Y : V) : V :=
  conn.nabla X Y + (action X u) • Y + (action Y u) • X - (metric.g X Y) • (grad metric u)

local notation "⁅" X ", " Y "⁆" => bracket X Y

-- Proves that the conformally transformed connection algebraically preserves the torsion-free property of the original connection.
theorem conformal_torsion_free (metric : MetricDuality R V)
  (conn : AbstractAffineConnection R V) [AbstractLieBracket V] [TorsionFree conn] (u : R) (X Y : V) :
  conformalConnection_nabla metric conn u X Y - conformalConnection_nabla metric conn u Y X = ⁅X, Y⁆ := by
  unfold conformalConnection_nabla
  have h1 : metric.g Y X = metric.g X Y := metric.symm Y X
  have h2 : conn.nabla X Y - conn.nabla Y X = ⁅X, Y⁆ := TorsionFree.torsion_zero X Y
  calc conn.nabla X Y + (action X u) • Y + (action Y u) • X - (metric.g X Y) • (grad metric u)
      - (conn.nabla Y X + (action Y u) • X + (action X u) • Y - (metric.g Y X) • (grad metric u))
    _ = conn.nabla X Y + (action X u) • Y + (action Y u) • X - (metric.g X Y) • (grad metric u)
      - (conn.nabla Y X + (action Y u) • X + (action X u) • Y - (metric.g X Y) • (grad metric u)) := by rw [h1]
    _ = conn.nabla X Y - conn.nabla Y X := by abel
    _ = ⁅X, Y⁆ := h2
