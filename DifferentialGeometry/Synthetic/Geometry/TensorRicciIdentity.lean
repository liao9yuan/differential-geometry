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


-- ============================================================
-- Section 4: Derivation Properties of R(X,Y)
-- ============================================================

/-- Sub on AbstractTensor unfolds to add + smul(-1). -/
private lemma sub_eq_add_neg_smul' {r s : ℕ} (A B : AbstractTensor R V r s) :
    A - B = TensorAlgebra.add A (TensorAlgebra.smul (-1) B) := rfl

/-- Contraction distributes over subtraction. -/
private lemma contract_sub {r s : ℕ} (A B : AbstractTensor R V (r + 1) (s + 1)) :
    TensorAlgebra.contract (A - B) = TensorAlgebra.contract A - TensorAlgebra.contract B := by
  change TensorAlgebra.contract (TensorAlgebra.add A (TensorAlgebra.smul (-1) B)) =
       TensorAlgebra.add (TensorAlgebra.contract A) (TensorAlgebra.smul (-1) (TensorAlgebra.contract B))
  rw [TensorAlgebra.contract_add, TensorAlgebra.contract_smul]

/-- R(X,Y) satisfies the Leibniz rule on tensor products:
  R(X,Y)(T ⊗ S) = R(X,Y)(T) ⊗ S + T ⊗ R(X,Y)(S).

The cross terms ∇_Y(T)⊗∇_X(S) and ∇_X(T)⊗∇_Y(S) from the double
covariant derivatives appear with opposite signs and cancel exactly. -/
theorem R_XY_tensor_prod (X Y : V) {r1 s1 r2 s2 : ℕ}
    (T : AbstractTensor R V r1 s1) (S : AbstractTensor R V r2 s2) :
    R_XY conn X Y (TensorAlgebra.tensor_prod T S) =
      TensorAlgebra.add (TensorAlgebra.tensor_prod (R_XY conn X Y T) S)
                        (TensorAlgebra.tensor_prod T (R_XY conn X Y S)) := by
  unfold R_XY
  -- Expand ∇ on tensor products (LHS) and distribute ⊗ over sums (RHS)
  simp only [sub_eq_add_neg_smul',
             AffineTensorCalculus.nabla_tensor_prod, AffineTensorCalculus.nabla_add,
             TensorAlgebra.tensor_prod_add_left, TensorAlgebra.tensor_prod_add_right,
             TensorAlgebra.tensor_prod_smul_left, TensorAlgebra.tensor_prod_smul_right]
  -- Move to TensorData level where we have AddCommGroup
  apply tensor_eq_of_toData_eq (R := R)
  simp only [TensorAlgebra.toData_add, TensorAlgebra.toData_smul, TensorAlgebra.toData_tensor_prod]
  -- Convert (-1) • x to -x, then cancel cross terms algebraically
  simp only [neg_one_smul]
  abel

/-- R(X,Y) commutes with contraction:
  R(X,Y)(contract T) = contract(R(X,Y) T).

Each ∇ commutes with contract by nabla_contract, and the result follows
from linearity of contraction. -/
theorem R_XY_contract (X Y : V) {r s : ℕ} (T : AbstractTensor R V (r + 1) (s + 1)) :
    R_XY conn X Y (TensorAlgebra.contract T) = TensorAlgebra.contract (R_XY conn X Y T) := by
  unfold R_XY
  simp only [AffineTensorCalculus.nabla_contract]
  rw [← contract_sub, ← contract_sub]


-- ============================================================
-- Section 5: Tensor Ricci Identity (Prompt 2.3)
-- ============================================================

/-- Every (0,0) tensor equals fromScalar of its scalar value. -/
private lemma fromScalar_toScalar (T : AbstractTensor R V 0 0) :
    fromScalar (R := R) (TensorAlgebra.toScalar T) = T := by
  apply tensor_eq_of_toData_eq (R := R)
  change TensorAlgebra.toData (TensorAlgebra.fromData (scalarToData (TensorAlgebra.toScalar T))) =
    TensorAlgebra.toData T
  rw [TensorAlgebra.toData_fromData, TensorAlgebra.toScalar_eq_toData]
  ext m n
  have hm : m = ![] := by ext i; exact i.elim0
  have hn : n = ![] := by ext i; exact i.elim0
  subst hm; subst hn
  dsimp [scalarToData, MultilinearMap.constOfIsEmpty]

/-- R(X,Y) vanishes on any (0,0) tensor (generalized R_XY_scalar). -/
private lemma R_XY_rank_00 [LieDerivationRules R V] (X Y : V) (T : AbstractTensor R V 0 0) :
    R_XY conn X Y T = 0 := by
  conv_lhs => rw [← fromScalar_toScalar (R := R) T]
  exact R_XY_scalar conn X Y (TensorAlgebra.toScalar T)

/-- toScalar of the zero tensor is zero. -/
private lemma toScalar_zero :
    TensorAlgebra.toScalar (0 : AbstractTensor R V 0 0) = 0 := by
  rw [TensorAlgebra.toScalar_eq_toData, toData_zero_eq]; rfl

/-- The Tensor Ricci Identity for (0,2) tensors:
  (R(X,Y) T)(U, W) = - T(Rm(X,Y)U, W) - T(U, Rm(X,Y)W).

Proof: R(X,Y) vanishes on the scalar T(U,W) (a (0,0) tensor). But by
the Leibniz rule (R_XY_tensor_prod) and contraction commutativity
(R_XY_contract), R(X,Y) distributes through the double contraction
of T ⊗ W ⊗ U, producing curvature terms on the vector slots via
R_XY_vector. The three-term sum equals zero, giving the identity.
No Fin arrays are used in the derivation — only abstract tensor algebra. -/
theorem tensor_ricci_identity [LieDerivationRules R V]
    (X Y U W : V) (T : AbstractBilinearForm R V) :
    tensor_eval (R_XY conn X Y T) ![U, W] ![] =
      - tensor_eval T ![Rm conn X Y U, W] ![] - tensor_eval T ![U, Rm conn X Y W] ![] := by
  -- Suffices to show the three-term sum vanishes
  suffices hs : tensor_eval (R_XY conn X Y T) ![U, W] ![] +
      tensor_eval T ![Rm conn X Y U, W] ![] +
      tensor_eval T ![U, Rm conn X Y W] ![] = 0 by linarith
  -- Convert tensor_eval to toData of double contractions
  simp only [tensor_eval_isomorphism]
  -- Key equation: R(X,Y) vanishes on the (0,0) evaluation tensor
  have h0 := R_XY_rank_00 conn X Y
    (TensorAlgebra.contract (R := R) (r := 0) (s := 0)
      (TensorAlgebra.contract (R := R) (r := 1) (s := 1)
        (TensorAlgebra.tensor_prod (R := R) (r1 := 0) (s1 := 2) (r2 := 2) (s2 := 0) T
          (TensorAlgebra.tensor_prod (R := R) (r1 := 1) (s1 := 0) (r2 := 1) (s2 := 0)
            (fromVector (R := R) W) (fromVector (R := R) U)))))
  -- Expand R(X,Y) through contractions, tensor products, and vectors
  rw [R_XY_contract conn, R_XY_contract conn,
      R_XY_tensor_prod conn, R_XY_tensor_prod conn,
      R_XY_vector conn X Y W, R_XY_vector conn X Y U,
      TensorAlgebra.tensor_prod_add_right] at h0
  -- Distribute contraction over addition
  simp only [TensorAlgebra.contract_add] at h0
  -- Extract the scalar equation: toScalar(A + B + C) = 0
  have h1 := congr_arg TensorAlgebra.toScalar h0
  rw [TensorAlgebra.toScalar_add, TensorAlgebra.toScalar_add, toScalar_zero] at h1
  -- Convert toScalar to toData ![] ![] to match the goal
  simp only [TensorAlgebra.toScalar_eq_toData] at h1
  -- Close by commutativity of addition in R
  linarith
