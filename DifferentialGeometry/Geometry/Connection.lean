import DifferentialGeometry.Algebra.Basic
import DifferentialGeometry.Geometry.Metric

set_option autoImplicit false


/-!
# Affine and Levi-Civita Connections
-/

variable (R V : Type)
variable [Add R] [Mul R] [Sub R] [Neg R]
variable [Add V] [Sub V] [Neg V] [ScalarMul R V]

open DerivationAction
open LieBracket

-- 1. Affine Connection
structure AffineConnection [DerivationAction R V] where
  nabla : V → V → V
  nabla_add_left : ∀ X Y Z : V, nabla (X + Y) Z = nabla X Z + nabla Y Z
  nabla_add_right : ∀ X Y Z : V, nabla X (Y + Z) = nabla X Y + nabla X Z
  nabla_smul_left : ∀ (f : R) (X Z : V), nabla (f • X) Z = f • (nabla X Z)
  leibniz : ∀ (f : R) (X Y : V), nabla X (f • Y) = (action X f) • Y + f • (nabla X Y)

-- 2. Local Frames & Christoffel Symbols
variable {I : Type}

structure LocalFrame (I R V : Type) where
  vec : I → V
  coord : V → I → R

section Symbols

variable {R V} {I : Type}

/-- Christoffel Symbols -/
def christoffel_symbol [DerivationAction R V]
  (conn : AffineConnection R V) (frame : LocalFrame I R V) (i j k : I) : R :=
  frame.coord (conn.nabla (frame.vec i) (frame.vec j)) k

end Symbols

-- 3. Metric Compatibility & Torsion-Free Conditions
variable {R V}
variable [DerivationAction R V]

class MetricCompatible (conn : AffineConnection R V) (metric : MetricTensor R V) where
  compat : ∀ X Y Z : V,
    action X (metric.g Y Z) = metric.g (conn.nabla X Y) Z + metric.g Y (conn.nabla X Z)

class TorsionFree (conn : AffineConnection R V) [LieBracket V] where
  torsion_zero : ∀ X Y : V, conn.nabla X Y - conn.nabla Y X = bracket X Y

-- 4. Inverse Metric & Koszul Formula
class InverseMetric (R V : Type) [Add R] [Mul R] [Add V] [ScalarMul R V] (metric : MetricTensor R V) where
  inv : (V → R) → V

/-- Explicit constructor for the Levi-Civita connection using the Koszul formula. -/
def koszul_connection [Div R] [OfNat R 2] [LieBracket V]
  (metric : MetricTensor R V) [InverseMetric R V metric] : AffineConnection R V where
  nabla X Y := InverseMetric.inv metric (fun Z =>
    (action X (metric.g Y Z) + action Y (metric.g Z X) - action Z (metric.g X Y)
      - metric.g X (bracket Y Z) + metric.g Y (bracket Z X) + metric.g Z (bracket X Y)) / 2)
  nabla_add_left := sorry
  nabla_add_right := sorry
  nabla_smul_left := sorry
  leibniz := sorry

-- 5. The Fundamental Theorem of Riemannian Geometry
theorem levi_civita_exists_unique [LieBracket V] (metric : MetricTensor R V) :
  ∃ (conn : AffineConnection R V),
    (MetricCompatible conn metric ∧ TorsionFree conn) ∧
    (∀ (conn' : AffineConnection R V), MetricCompatible conn' metric ∧ TorsionFree conn' → conn' = conn) := by
  sorry

-- 5. Bundled Levi-Civita Connection
class LeviCivitaConnection (metric : MetricTensor R V) [LieBracket V] extends AffineConnection R V where
  compat : ∀ X Y Z : V, action X (metric.g Y Z) = metric.g (nabla X Y) Z + metric.g Y (nabla X Z)
  torsion_zero : ∀ X Y : V, nabla X Y - nabla Y X = bracket X Y
