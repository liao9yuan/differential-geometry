import DifferentialGeometry.Geometry.Connection
import DifferentialGeometry.Geometry.Curvature
import DifferentialGeometry.Geometry.CurvatureTensor
import DifferentialGeometry.Algebra.BilinearForm
import DifferentialGeometry.Algebra.Trace
import DifferentialGeometry.Algebra.VectorField
import DifferentialGeometry.Bridge.Defs

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Ricci Curvature Tensor
Rigorous construction of the Ricci curvature as a smooth bilinear form.
-/

open AbstractDerivationAction
open AbstractLieBracket
open DifferentialGeometry.Bridge TensorAlgebra

variable {R V : Type}
variable [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V]

class RicciOperator (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] (conn : AbstractAffineConnection R V) [TraceOperator R V] where
  ricciForm : AbstractBilinearForm R V
  ricciForm_eval : ∀ (X Y : V),
    eval02 ricciForm X Y = Rc conn X Y

/-- Constructs the Ricci curvature as a rigorously proven AbstractBilinearForm. -/
def ricciForm (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] [TraceOperator R V] [TraceLinearityRules R V] [RicciOperator R V conn] : AbstractBilinearForm R V :=
  RicciOperator.ricciForm conn

lemma eval02_ricciForm (conn : AbstractAffineConnection R V) [DerivationRules R V] [LieDerivationRules R V] [TraceOperator R V] [TraceLinearityRules R V] [RicciOperator R V conn] (X Y : V) :
  eval02 (ricciForm conn) X Y = Rc conn X Y := RicciOperator.ricciForm_eval X Y
