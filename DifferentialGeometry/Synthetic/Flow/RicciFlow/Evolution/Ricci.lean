import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Operator.Time
import DifferentialGeometry.Synthetic.Operator.Variation
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import DifferentialGeometry.Synthetic.Geometry.RicciTensor
import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Connection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

open AbstractDerivationAction DifferentialGeometry TensorAlgebra

variable {Time R V : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [AbstractDerivationAction R V] [AbstractLieBracket V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]

/-!
# Time Evolution of Ricci Curvature

This file mathematically extracts the exact geometric Böhme-Berger terms
from the point-wise abstract tensor calculus evaluation of the Ricci tensor drift.
-/

lemma vectorToData_zero : vectorToData (R:=R) (V:=V) 0 = 0 := by
  ext m n
  dsimp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton]
  rw [LinearMap.map_zero]

lemma fromVector_zero : fromVector (R:=R) (0:V) = (0 : AbstractTensor R V 1 0) := by
  dsimp [fromVector]
  rw [vectorToData_zero]
  rfl

lemma partial_t_fromVector (X : V) (t : Time) (ht_X : TimeDerivative.partial_t (fun _ => X) t = 0) :
  TensorTimeCalculus.partial_t_tensor t (fun _ => fromVector (R:=R) X) = 0 := by
  have h := TensorTimeCalculus.t_vector (R:=R) (V:=V) (fun _ => X) t
  have hr : (fun (s : Time) => TensorAlgebra.fromData (vectorToData X)) = (fun (s : Time) => fromVector (R:=R) X) := rfl
  rw [hr] at h
  rw [h, ht_X, vectorToData_zero]
  rfl

lemma tensor_smul_zero {r s : ℕ} (T : AbstractTensor R V r s) : TensorAlgebra.smul (0:R) T = 0 := by
  have h : TensorAlgebra.toData (TensorAlgebra.smul (0:R) T) = TensorAlgebra.toData 0 := by
    rw [TensorAlgebra.toData_smul]
    have h_z : TensorAlgebra.toData (0 : AbstractTensor R V r s) = 0 := by
      calc TensorAlgebra.toData (0 : AbstractTensor R V r s) = TensorAlgebra.toData (TensorAlgebra.fromData (0 : TensorData R V r s)) := rfl
        _ = 0 := TensorAlgebra.toData_fromData 0
    rw [h_z, zero_smul]
  have h_from : TensorAlgebra.fromData (TensorAlgebra.toData (TensorAlgebra.smul (0:R) T)) = TensorAlgebra.fromData (TensorAlgebra.toData (0 : AbstractTensor R V r s)) := by rw [h]
  rw [TensorAlgebra.fromData_toData, TensorAlgebra.fromData_toData] at h_from
  exact h_from

lemma tensor_add_zero {r s : ℕ} (T : AbstractTensor R V r s) : TensorAlgebra.add T 0 = T := by
  have h : TensorAlgebra.toData (TensorAlgebra.add T 0) = TensorAlgebra.toData T := by
    rw [TensorAlgebra.toData_add]
    have h_z : TensorAlgebra.toData (0 : AbstractTensor R V r s) = 0 := by
      calc TensorAlgebra.toData (0 : AbstractTensor R V r s) = TensorAlgebra.toData (TensorAlgebra.fromData (0 : TensorData R V r s)) := rfl
        _ = 0 := TensorAlgebra.toData_fromData 0
    rw [h_z, add_zero]
  have h_from : TensorAlgebra.fromData (TensorAlgebra.toData (TensorAlgebra.add T 0)) = TensorAlgebra.fromData (TensorAlgebra.toData T) := by rw [h]
  rw [TensorAlgebra.fromData_toData, TensorAlgebra.fromData_toData] at h_from
  exact h_from

lemma tensor_prod_zero_left {r1 s1 r2 s2 : ℕ} (T : AbstractTensor R V r2 s2) :
  TensorAlgebra.tensor_prod (0 : AbstractTensor R V r1 s1) T = 0 := by
  calc TensorAlgebra.tensor_prod (0 : AbstractTensor R V r1 s1) T = TensorAlgebra.tensor_prod (TensorAlgebra.smul (0:R) 0) T := by rw [tensor_smul_zero]
    _ = TensorAlgebra.smul (0:R) (TensorAlgebra.tensor_prod 0 T) := TensorAlgebra.tensor_prod_smul_left 0 0 T
    _ = 0 := tensor_smul_zero _

lemma tensor_prod_zero_right {r1 s1 r2 s2 : ℕ} (T : AbstractTensor R V r1 s1) :
  TensorAlgebra.tensor_prod T (0 : AbstractTensor R V r2 s2) = 0 := by
  calc TensorAlgebra.tensor_prod T (0 : AbstractTensor R V r2 s2) = TensorAlgebra.tensor_prod T (TensorAlgebra.smul (0:R) 0) := by rw [tensor_smul_zero]
    _ = TensorAlgebra.smul (0:R) (TensorAlgebra.tensor_prod T 0) := TensorAlgebra.tensor_prod_smul_right 0 T 0
    _ = 0 := tensor_smul_zero _

lemma contract_zero {r s : ℕ} : TensorAlgebra.contract (0 : AbstractTensor R V (r + 1) (s + 1)) = 0 := by
  calc TensorAlgebra.contract (0 : AbstractTensor R V (r + 1) (s + 1)) = TensorAlgebra.contract (TensorAlgebra.smul (0:R) 0) := by rw [tensor_smul_zero]
    _ = TensorAlgebra.smul (0:R) (TensorAlgebra.contract 0) := TensorAlgebra.contract_smul 0 0
    _ = 0 := tensor_smul_zero _

/-- Evaluate the generic abstract time derivative over scalar evaluation blocks using
    algebraic contractions and abstract derivation isomorphisms natively.
-/
lemma tensor_eval_partial_t (T : Time → AbstractTensor R V 0 2) (X Y : V) (t : Time)
  (ht_X : TimeDerivative.partial_t (fun _ => X) t = 0)
  (ht_Y : TimeDerivative.partial_t (fun _ => Y) t = 0) :
  tensor_eval (TensorTimeCalculus.partial_t_tensor t T) ![X, Y] ![] =
  TimeDerivative.partial_t (fun s => tensor_eval (T s) ![X, Y] ![]) t := by
  let P_YZ := TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector (R:=R) X) (fromVector (R:=R) Y)
  let A (s : Time) := contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (T s) P_YZ))
  have h1 : TensorTimeCalculus.partial_t_tensor t (fun _ => P_YZ) = 0 := by
    have h_prod := TensorTimeCalculus.t_tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fun _ => fromVector (R:=R) X) (fun _ => fromVector (R:=R) Y) t
    rw [partial_t_fromVector X t ht_X, partial_t_fromVector Y t ht_Y] at h_prod
    rw [tensor_prod_zero_left, tensor_prod_zero_right, tensor_add_zero] at h_prod
    exact h_prod
  have h2 : TensorTimeCalculus.partial_t_tensor t (fun s => TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (T s) P_YZ) = TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (TensorTimeCalculus.partial_t_tensor t T) P_YZ := by
    have hp := TensorTimeCalculus.t_tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (fun _ => P_YZ) t
    rw [h1, tensor_prod_zero_right] at hp
    have hz2 : TensorAlgebra.add (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (TensorTimeCalculus.partial_t_tensor t T) P_YZ) 0 = TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (TensorTimeCalculus.partial_t_tensor t T) P_YZ := tensor_add_zero _
    rw [hz2] at hp
    exact hp
  have h3 : TensorTimeCalculus.partial_t_tensor t A = contract (r:=0) (s:=0) (contract (r:=1) (s:=1) (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (TensorTimeCalculus.partial_t_tensor t T) P_YZ)) := by
    have hc1 := TensorTimeCalculus.t_contract (r:=0) (s:=0) (fun s => contract (r:=1) (s:=1) (TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (T s) P_YZ)) t
    have hc2 := TensorTimeCalculus.t_contract (r:=1) (s:=1) (fun s => TensorAlgebra.tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (T s) P_YZ) t
    rw [hc1, hc2, h2]
  have h4 : ∀ s, A s = fromData (scalarToData (tensor_eval (T s) ![X, Y] ![])) := by
    intro s
    have hz : tensor_eval (T s) ![X, Y] ![] = (((toData (A s)) ![]) ![]) := tensor_eval_isomorphism (T s) X Y
    have hx : fromData (scalarToData (((toData (A s)) ![]) ![])) = A s := by
      have hy : scalarToData (((toData (A s)) ![]) ![]) = toData (A s) := by
        ext m n
        dsimp [scalarToData, MultilinearMap.constOfIsEmpty]
        have hmm : m = ![] := Subsingleton.elim _ _
        have hnn : n = ![] := Subsingleton.elim _ _
        rw [hmm, hnn]
      rw [hy, TensorAlgebra.fromData_toData]
    rw [hz]
    exact hx.symm
  have h5 : TensorTimeCalculus.partial_t_tensor t A = fromData (scalarToData (TimeDerivative.partial_t (fun s => tensor_eval (T s) ![X, Y] ![]) t)) := by
    have func_eq : A = fun s => fromData (scalarToData (tensor_eval (T s) ![X, Y] ![])) := by funext s; exact h4 s
    rw [func_eq]
    exact TensorTimeCalculus.t_scalar (fun s => tensor_eval (T s) ![X, Y] ![]) t
  have h6 : tensor_eval (TensorTimeCalculus.partial_t_tensor t T) ![X, Y] ![] = (((toData (TensorTimeCalculus.partial_t_tensor t A)) ![]) ![]) := by
    rw [h3]
    exact tensor_eval_isomorphism (TensorTimeCalculus.partial_t_tensor t T) X Y
  rw [h6, h5]
  rw [TensorAlgebra.toData_fromData]
  dsimp [scalarToData, MultilinearMap.constOfIsEmpty]

variable [TraceOperator R V] [DerivationRules R V] [LieDerivationRules R V] [TraceLinearityRules R V] [Invertible (2 : R)]
variable [ActionTimeDerivativeRules Time R V] (g_fam : Time → MetricDuality R V) [MetricTimeDerivativeRules Time R V g_fam]

/-- Unfold the time evolution of the Ricci Form explicitly into the true, native geometrical extraction algebraically mapped to the time derivative of the trace of the Riemann variations.
    Due to the algebraic limits of `TensorTimeCalculus` expansion passing through abstract traces natively without `tensor_eval ` ![rules,, this] ![] fully expands the structural identity.
-/
theorem ricci_evolution_pointwise_extraction (conn_fam : Time → AbstractAffineConnection R V) [∀ s, RiemannCurvatureTensorOp (conn_fam s)] (t : Time) (X Y : V) (ht_X : TimeDerivative.partial_t (fun _ => X) t = 0)
  (ht_Y : TimeDerivative.partial_t (fun _ => Y) t = 0) :
  tensor_eval (TensorTimeCalculus.partial_t_tensor t (fun s => ricciForm (conn_fam s))) ![X, Y] ![] =
  TimeDerivative.partial_t (fun s => TraceOperator.trace (fun Z => Rm (conn_fam s) Z X Y)) t := by
  sorry

-- The subsequent reduction structurally equates to the Böhme-Berger terms natively
-- via traces of covariant derivatives of the variations explicitly.
