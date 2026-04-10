import DifferentialGeometry.Synthetic.Analysis.TensorCalculus
import DifferentialGeometry.Synthetic.Geometry.Curvature
import DifferentialGeometry.Synthetic.Algebra.BilinearForm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Tensor Ricci Identity: Curvature Derivation Operator

This file defines the abstract curvature derivation operator R(X,Y) acting on
arbitrary tensors and proves its fundamental properties:
1. It vanishes on scalars (rank 0 0): `R_XY_scalar`
2. It equals the Riemann curvature on vectors (rank 1 0): `R_XY_vector`

These results are the building blocks for the full Tensor Ricci Identity,
which describes how curvature acts on tensors of arbitrary rank via the
derivation (Leibniz) property on tensor products.
-/

open AbstractDerivationAction AbstractLieBracket DifferentialGeometry TensorAlgebra

variable {R V : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [AbstractDerivationAction R V] [AbstractLieBracket V]


-- ============================================================
-- Section 1: Helper Lemmas
-- ============================================================

/-- Two tensors with equal toData representations are equal. -/
private lemma tensor_eq_of_toData_eq {r s : ℕ} {T₁ T₂ : AbstractTensor R V r s}
    (h : toData T₁ = toData T₂) : T₁ = T₂ := by
  rw [← fromData_toData T₁, ← fromData_toData T₂, h]

/-- toData distributes over subtraction (defined as add + smul(-1)). -/
private lemma toData_sub {r s : ℕ} (T₁ T₂ : AbstractTensor R V r s) :
    toData (T₁ - T₂) = toData T₁ + (-1 : R) • toData T₂ := by
  change toData (TensorAlgebra.add T₁ (TensorAlgebra.smul (-1 : R) T₂)) = _
  rw [toData_add, toData_smul]

/-- toData of the zero tensor is zero. -/
private lemma toData_zero_eq {r s : ℕ} :
    toData (0 : AbstractTensor R V r s) = 0 :=
  toData_fromData (0 : TensorData R V r s)

/-- scalarToData distributes over subtraction. -/
private lemma scalarToData_sub (a b : R) :
    scalarToData (R := R) (V := V) (a - b) =
    scalarToData a + (-1 : R) • scalarToData b := by
  ext m n
  dsimp [scalarToData, MultilinearMap.constOfIsEmpty]
  ring

/-- vectorToData distributes over subtraction. -/
private lemma vectorToData_sub' (X Y : V) :
    vectorToData (R := R) (X - Y) =
    vectorToData X + (-1 : R) • vectorToData Y := by
  rw [show X - Y = X + (-1 : R) • Y from by rw [neg_one_smul, sub_eq_add_neg]]
  rw [vectorToData_add, vectorToData_smul]


-- ============================================================
-- Section 2: Definition
-- ============================================================

variable (conn : AbstractAffineConnection R V) [AffineTensorCalculus conn]

/-- The abstract curvature derivation operator acting on any tensor T:
  R(X,Y)T = ∇_X(∇_Y T) - ∇_Y(∇_X T) - ∇_{[X,Y]} T.
This generalizes the Riemann curvature endomorphism to act on tensors
of arbitrary rank (r,s). -/
def R_XY (X Y : V) {r s : ℕ} (T : AbstractTensor R V r s) : AbstractTensor R V r s :=
  AffineTensorCalculus.nabla_tensor conn X (AffineTensorCalculus.nabla_tensor conn Y T)
  - AffineTensorCalculus.nabla_tensor conn Y (AffineTensorCalculus.nabla_tensor conn X T)
  - AffineTensorCalculus.nabla_tensor conn (bracket X Y) T


-- ============================================================
-- Section 3: Main Theorems
-- ============================================================

/-- R(X,Y) vanishes on scalars: R(X,Y)(f) = 0.

Proof: By nabla_scalar, ∇_X(f) = X(f) for any scalar f. Hence
  R(X,Y)(f) = X(Y(f)) - Y(X(f)) - [X,Y](f).
By action_bracket, [X,Y](f) = X(Y(f)) - Y(X(f)), so R(X,Y)(f) = 0. -/
theorem R_XY_scalar [LieDerivationRules R V] (X Y : V) (f : R) :
    R_XY conn X Y (fromScalar f) = 0 := by
  unfold R_XY fromScalar
  rw [AffineTensorCalculus.nabla_scalar Y f,
      AffineTensorCalculus.nabla_scalar X (action Y f),
      AffineTensorCalculus.nabla_scalar X f,
      AffineTensorCalculus.nabla_scalar Y (action X f),
      AffineTensorCalculus.nabla_scalar (bracket X Y) f,
      LieDerivationRules.action_bracket X Y f]
  -- Goal: fromData(scalarToData(XYf)) - fromData(scalarToData(YXf))
  --     - fromData(scalarToData(XYf - YXf)) = 0
  apply tensor_eq_of_toData_eq (R := R)
  simp only [toData_sub, toData_fromData, toData_zero_eq]
  -- Goal: (scalarToData(XYf) + (-1)•scalarToData(YXf)) + (-1)•scalarToData(XYf - YXf) = 0
  rw [← scalarToData_sub (R := R) (V := V)
        (action X (action Y f)) (action Y (action X f))]
  -- Goal: scalarToData(XYf - YXf) + (-1)•scalarToData(XYf - YXf) = 0
  rw [neg_one_smul, add_neg_cancel]

/-- R(X,Y) equals the Riemann curvature on vectors: R(X,Y)(U) = Rm(X,Y)U.

This is essentially the definition of the Riemann curvature tensor:
  Rm(X,Y)U = ∇_X(∇_Y U) - ∇_Y(∇_X U) - ∇_{[X,Y]} U. -/
theorem R_XY_vector (X Y U : V) :
    R_XY conn X Y (fromVector U) = fromVector (Rm conn X Y U) := by
  unfold R_XY fromVector Rm
  rw [AffineTensorCalculus.nabla_vector Y U,
      AffineTensorCalculus.nabla_vector X (conn.nabla Y U),
      AffineTensorCalculus.nabla_vector X U,
      AffineTensorCalculus.nabla_vector Y (conn.nabla X U),
      AffineTensorCalculus.nabla_vector (bracket X Y) U]
  -- Both sides are fromData(vectorToData(...)) with subtractions
  apply tensor_eq_of_toData_eq (R := R)
  simp only [toData_sub, toData_fromData]
  -- Goal: (vectorToData(∇X∇YU) + (-1)•vectorToData(∇Y∇XU)) + (-1)•vectorToData(∇[X,Y]U)
  --     = vectorToData(∇X∇YU - ∇Y∇XU - ∇[X,Y]U)
  rw [← vectorToData_sub' (R := R)
        (conn.nabla X (conn.nabla Y U)) (conn.nabla Y (conn.nabla X U)),
      ← vectorToData_sub' (R := R)]
