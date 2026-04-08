import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

open BigOperators

namespace DifferentialGeometry

class DualFrame (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] (d : ℕ) where
  basis : Fin d → V
  dual : Fin d → (V →ₗ[R] R)
  dual_basis_eval : ∀ i j : Fin d, dual i (basis j) = if i = j then 1 else 0
  reconstruct : ∀ v : V, v = ∑ i : Fin d, (dual i v) • basis i

namespace DualFrame

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {d : ℕ} [DualFrame R V d]

def evalHom (v : V) : (V →ₗ[R] R) →+ R where
  toFun f := f v
  map_zero' := rfl
  map_add' _ _ := rfl

lemma dual_reconstruct_apply (f : V →ₗ[R] R) (v : V) :
    f v = ∑ i : Fin d, (DualFrame.dual (R:=R) (d:=d) i v) * f (DualFrame.basis (R:=R) (d:=d) i) := by
  calc f v = f (∑ i : Fin d, (DualFrame.dual (R:=R) (d:=d) i v) • DualFrame.basis (R:=R) (d:=d) i) := congr_arg f (DualFrame.reconstruct (R:=R) (d:=d) v)
    _ = ∑ i : Fin d, f ((DualFrame.dual (R:=R) (d:=d) i v) • DualFrame.basis (R:=R) (d:=d) i) := by rw [map_sum]
    _ = ∑ i : Fin d, (DualFrame.dual (R:=R) (d:=d) i v) * f (DualFrame.basis (R:=R) (d:=d) i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.map_smul, smul_eq_mul]

lemma covector_reconstruct (f : V →ₗ[R] R) :
    f = ∑ i : Fin d, f (DualFrame.basis (R:=R) (d:=d) i) • DualFrame.dual (R:=R) (d:=d) i := by
  ext v
  symm
  calc (∑ i : Fin d, f (DualFrame.basis (R:=R) (d:=d) i) • DualFrame.dual (R:=R) (d:=d) i) v
    _ = evalHom v (∑ i : Fin d, f (DualFrame.basis (R:=R) (d:=d) i) • DualFrame.dual (R:=R) (d:=d) i) := rfl
    _ = ∑ i : Fin d, evalHom v (f (DualFrame.basis (R:=R) (d:=d) i) • DualFrame.dual (R:=R) (d:=d) i) := map_sum (evalHom v) _ _
    _ = ∑ i : Fin d, (f (DualFrame.basis (R:=R) (d:=d) i) • DualFrame.dual (R:=R) (d:=d) i) v := rfl
    _ = ∑ i : Fin d, (DualFrame.dual (R:=R) (d:=d) i v) * f (DualFrame.basis (R:=R) (d:=d) i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [LinearMap.smul_apply, smul_eq_mul, mul_comm]
    _ = f v := (dual_reconstruct_apply f v).symm

end DualFrame
end DifferentialGeometry
