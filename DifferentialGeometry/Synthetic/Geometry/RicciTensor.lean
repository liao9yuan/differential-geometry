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
Derived Ricci trace evaluation: if a (0,2) tensor `T` evaluates pointwise as
`T(X,Y) = -g(Rm(X,U)Y, W)`, then its metric trace equals `Rc(W,U)`.

The proof is the culmination of the universal evaluation framework:
1. `Rm_symm_blocks` flips `g(Rm(X,U)Y,W) = g(Rm(Y,W)X,U)`
2. `Rm_metric_antisymm` extracts the endomorphism: `T(X,Y) = g(X, Rm(Y,W)U)`
3. `metric_trace_eval` (Axioms 1+2) gives `metric_trace T = tr(Y ↦ Rm(Y,W)U)`
4. `Contract13EvaluationRules` on `Rm_tensor` shows `Rc(W,U) = tr(X ↦ Rm(X,W)U)`
5. The two endomorphisms are *literally the same map*, completing the proof.
-/
lemma trace_rm_eval [DerivationRules R V] [LieDerivationRules R V]
    [AbstractTraceRules R V]
    (metric : MetricDuality R V) [RaiseIndexEvaluationRules R V metric]
    [Contract11EvaluationRules R V] [Contract13EvaluationRules R V]
    (conn : AbstractAffineConnection R V) [op : RiemannCurvatureTensorOp conn]
    [TorsionFree conn] [JacobiIdentity V]
    [MetricCompatible conn metric.toNonDegenerateMetric.toAbstractMetricTensor]
    (T : AbstractTensor R V 0 2) (U W : V)
    (h : ∀ X Y, tensor_eval T ![X, Y] ![] = - metric.g (Rm conn X U Y) W) :
    tensor_eval (metric_trace metric (0 : Fin 2) (0 : Fin 1) T) ![] ![] = Rc conn W U := by
  set m := metric.toNonDegenerateMetric.toAbstractMetricTensor
  -- Step 1: Derive T(X,Y) = g(X, Rm(Y,W)U) via block symmetry + metric antisymmetry
  have h_form : ∀ X Y, tensor_eval T ![X, Y] ![] = m.g X (Rm conn Y W U) := by
    intro X Y; rw [h]
    have bs := Rm_symm_blocks conn metric X U Y W
    have ma := Rm_metric_antisymm conn metric Y W X U
    calc - m.g (Rm conn X U Y) W
      _ = - m.g (Rm conn Y W X) U := by rw [bs]
      _ = m.g (Rm conn Y W U) X := by rw [ma]; ring
      _ = m.g X (Rm conn Y W U) := (m.symm _ _).symm
  -- Step 2: Construct L_T : V →ₗ[R] V as Y ↦ Rm(Y,W)U
  let L_T : V →ₗ[R] V :=
    { toFun := fun Y => Rm conn Y W U
      map_add' := fun a b => Rm_add_X conn a b W U
      map_smul' := fun r a => Rm_smul_X conn r a W U }
  -- Step 3: metric_trace_eval (Axioms 1+2): metric_trace T = tr(L_T)
  rw [metric_trace_eval metric T L_T h_form]
  -- Step 4: Rc(W,U) = tr(L_T) via Contract13 on Rm_tensor
  -- L_T = (X ↦ Rm(X,W)U), which is exactly the endomorphism from Rm_tensor at (W,U)
  symm; show Rc conn W U = AbstractTraceRules.tr L_T
  unfold Rc rc_tensor
  have h_rm : ∀ X A B (n : V →ₗ[R] R), tensor_eval op.Rm_tensor ![X, A, B] ![n] =
      n (Rm conn X A B) := by
    intro X A B n
    show TensorAlgebra.toData op.Rm_tensor ![X, A, B] ![n] = n (Rm conn X A B)
    rw [op.toData_Rm_tensor]; exact op.eval_eq X A B n
  exact Contract13EvaluationRules.contract_13_eval op.Rm_tensor
    (fun A B => { toFun := fun X => Rm conn X A B
                  map_add' := fun a b => Rm_add_X conn a b A B
                  map_smul' := fun r a => Rm_smul_X conn r a A B })
    (fun X A B n => h_rm X A B n) W U

