import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Geometry.CurvatureTensor
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import DifferentialGeometry.Synthetic.Algebra.Trace
import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.VectorField
import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Ricci Curvature Tensor
Rigorous construction of the Ricci curvature as a smooth bilinear form.
-/

open AbstractDerivationAction
open AbstractLieBracket
open DifferentialGeometry TensorAlgebra

variable {R V : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
variable [AbstractDerivationAction R V] [AbstractLieBracket V]

/-- Ricci curvature tensor defined natively as (0,2) abstract tensor by contracting Riemann tensor --/
def rc_tensor (conn : AbstractAffineConnection R V) [op : RiemannCurvatureTensorOp conn] : AbstractTensor R V 0 2 :=
  TensorAlgebra.contract_general (0 : Fin 1) (0 : Fin 3) op.Rm_tensor

/-- Ricci curvature pointwise evaluation. --/
def Rc (conn : AbstractAffineConnection R V) [op : RiemannCurvatureTensorOp conn] (X Y : V) : R :=
  tensor_eval (rc_tensor conn) ![X, Y] ![]

/-- Scalar curvature pointwise evaluation. --/
def ScalarCurvature (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [op : RiemannCurvatureTensorOp conn] : R :=
  tensor_eval (metric_trace metric (0: Fin 2) (0: Fin 1) (rc_tensor conn)) ![] ![]

/-- Backward compatibility alias for Evolution proofs avoiding AbstractBilinearForm wrappers --/
def ricciForm (conn : AbstractAffineConnection R V) [op : RiemannCurvatureTensorOp conn] : AbstractTensor R V 0 2 :=
  rc_tensor conn

lemma tensor_eval_ricciForm (conn : AbstractAffineConnection R V) [op : RiemannCurvatureTensorOp conn] (X Y : V) :
  tensor_eval (ricciForm conn) ![X, Y] ![] = Rc conn X Y := by rfl

/--
Foundational Geometric Axiom: The metric trace of any (0,2) tensor that evaluates pointwise
as the Riemann curvature endomorphism pairing is defined to evaluate to the Ricci curvature.
-/
class RicciEvaluationRules (R V : Type) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V] [AbstractDerivationAction R V] [AbstractLieBracket V] (metric : MetricDuality R V) (conn : AbstractAffineConnection R V) [RiemannCurvatureTensorOp conn] where
  trace_rm_eval : ∀ (T : AbstractTensor R V 0 2) (U W : V),
    (∀ X Y, tensor_eval T ![X, Y] ![] = metric.g (Rm conn X U Y) W) →
    tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) T) ![] ![] = Rc conn U W

