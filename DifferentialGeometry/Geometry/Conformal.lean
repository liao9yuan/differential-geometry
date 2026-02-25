import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Algebra.Metric
import DifferentialGeometry.Operators.Gradient
import DifferentialGeometry.Algebra.Basic
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false

open DerivationAction
open LieBracket

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] [DerivationAction R V] [ScalarMul R V]

-- Defines the conformal transformation of an affine connection algebraically.
def conformalConnection_nabla (metric : MetricTensor R V) [MusicalIsomorphism R V metric]
  (conn : AffineConnection R V) (u : R) (X Y : V) : V :=
  conn.nabla X Y + ScalarMul.smul (action X u) Y + ScalarMul.smul (action Y u) X - ScalarMul.smul (metric.g X Y) (grad metric u)

local notation "⁅" X ", " Y "⁆" => bracket X Y

-- Proves that the conformally transformed connection algebraically preserves the torsion-free property of the original connection.
theorem conformal_torsion_free (metric : MetricTensor R V) [MusicalIsomorphism R V metric]
  (conn : AffineConnection R V) [LieBracket V] [TorsionFree conn] (u : R) (X Y : V) :
  conformalConnection_nabla metric conn u X Y - conformalConnection_nabla metric conn u Y X = ⁅X, Y⁆ := by
  unfold conformalConnection_nabla
  have h1 : metric.g Y X = metric.g X Y := metric.symm Y X
  have h2 : conn.nabla X Y - conn.nabla Y X = ⁅X, Y⁆ := TorsionFree.torsion_zero X Y
  calc conn.nabla X Y + ScalarMul.smul (action X u) Y + ScalarMul.smul (action Y u) X - ScalarMul.smul (metric.g X Y) (grad metric u)
      - (conn.nabla Y X + ScalarMul.smul (action Y u) X + ScalarMul.smul (action X u) Y - ScalarMul.smul (metric.g Y X) (grad metric u))
    _ = conn.nabla X Y + ScalarMul.smul (action X u) Y + ScalarMul.smul (action Y u) X - ScalarMul.smul (metric.g X Y) (grad metric u)
      - (conn.nabla Y X + ScalarMul.smul (action Y u) X + ScalarMul.smul (action X u) Y - ScalarMul.smul (metric.g X Y) (grad metric u)) := by rw [h1]
    _ = conn.nabla X Y - conn.nabla Y X := by abel
    _ = ⁅X, Y⁆ := h2
