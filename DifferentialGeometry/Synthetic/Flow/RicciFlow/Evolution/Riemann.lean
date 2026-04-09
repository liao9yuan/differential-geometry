import DifferentialGeometry.Synthetic.Operator.Time
import DifferentialGeometry.Synthetic.Algebra.VectorField
import DifferentialGeometry.Synthetic.Geometry.Connection
import DifferentialGeometry.Synthetic.Geometry.Curvature
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open AbstractDerivationAction AbstractLieBracket DifferentialGeometry TensorAlgebra

/-!
# Evolution of the Riemann Curvature Tensor

This file formalizes the first variation (raw time derivative) of the Riemann
curvature endomorphism under a time-evolving family of connections.

The main result is the fundamental variation formula: for time-independent X, Y, Z,
  ∂_t[Rm(X,Y)Z] = (∇_X A)(Y,Z) - (∇_Y A)(X,Z)
where A(X,Y) = ∂_t(∇_X Y) is the connection variation tensor, and
  (∇_X A)(Y,Z) = ∇_X(A(Y,Z)) - A(∇_X Y, Z) - A(Y, ∇_X Z).

All calculus axioms (VectorTimeDerivativeRules, ConnectionTimeCalculus) live
in the Algebra/Analysis layer (Time.lean). The conn_var_sub_left identity
is derived as a theorem, not axiomatized.
-/

variable {Time R V : Type}
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  [AbstractDerivationAction R V] [AbstractLieBracket V]
  [DerivationRules R V]
  [TimeDerivative Time R] [TimeDerivative Time V]
  [TimeDerivativeRules Time R V] [TensorTimeCalculus Time R V]
  [VectorTimeDerivativeRules Time R V]
  [ConnectionTimeCalculus Time R V]


-- ============================================================
-- Section 1: Definitions
-- ============================================================

/-- Connection variation tensor: A(X,Y) = ∂_t(∇_X Y).
Measures the infinitesimal rate of change of the connection at time t.
This is a vector-valued (1,2)-tensor in the sense that A(X,Y) ∈ V. -/
def conn_var (conn_fam : Time → AbstractAffineConnection R V) (t : Time) (X Y : V) : V :=
  TimeDerivative.partial_t (fun s => (conn_fam s).nabla X Y) t

/-- Covariant derivative of the connection variation tensor:
  (∇_X A)(Y,Z) = ∇_X(A(Y,Z)) - A(∇_X Y, Z) - A(Y, ∇_X Z).
This is the covariant derivative of the vector-valued (1,2)-tensor A. -/
def nabla_conn_var (conn_fam : Time → AbstractAffineConnection R V) (t : Time) (X Y Z : V) : V :=
  (conn_fam t).nabla X (conn_var conn_fam t Y Z)
  - conn_var conn_fam t ((conn_fam t).nabla X Y) Z
  - conn_var conn_fam t Y ((conn_fam t).nabla X Z)

/-- The Riemann variation tensor: ∂_t[Rm(X,Y)Z] = (∇_X A)(Y,Z) - (∇_Y A)(X,Z).
Defined abstractly as a vector-valued function combining the covariant
derivatives of the connection variation. -/
def t_rm (conn_fam : Time → AbstractAffineConnection R V) (t : Time) (X Y Z : V) : V :=
  nabla_conn_var conn_fam t X Y Z - nabla_conn_var conn_fam t Y X Z


-- ============================================================
-- Section 2: Derived Lemmas
-- ============================================================

/-- ∇_X(-Y) = -∇_X Y for the first argument. -/
private lemma nabla_neg_left_aux (conn : AbstractAffineConnection R V) (X Z : V) :
    conn.nabla (-X) Z = - conn.nabla X Z := by
  have h1 : conn.nabla ((-1 : R) • X) Z = (-1 : R) • conn.nabla X Z := conn.nabla_smul_left (-1) X Z
  rwa [neg_one_smul, neg_one_smul] at h1

/-- ∇_{X₁-X₂} Y = ∇_{X₁} Y - ∇_{X₂} Y (subtraction in the direction argument). -/
private lemma nabla_sub_left_aux (conn : AbstractAffineConnection R V) (X₁ X₂ Z : V) :
    conn.nabla (X₁ - X₂) Z = conn.nabla X₁ Z - conn.nabla X₂ Z := by
  calc conn.nabla (X₁ - X₂) Z
      = conn.nabla (X₁ + -X₂) Z := by rw [sub_eq_add_neg]
    _ = conn.nabla X₁ Z + conn.nabla (-X₂) Z := conn.nabla_add_left X₁ (-X₂) Z
    _ = conn.nabla X₁ Z + (- conn.nabla X₂ Z) := by rw [nabla_neg_left_aux]
    _ = conn.nabla X₁ Z - conn.nabla X₂ Z := by abel

/-- The connection variation is additive under subtraction in its first argument.
Derived from `nabla_sub_left` and `VectorTimeDerivativeRules.t_sub_V`. -/
theorem conn_var_sub_left (conn_fam : Time → AbstractAffineConnection R V)
    (X₁ X₂ Y : V) (t : Time) :
    conn_var conn_fam t (X₁ - X₂) Y =
    conn_var conn_fam t X₁ Y - conn_var conn_fam t X₂ Y := by
  unfold conn_var
  have h_eq : (fun s => (conn_fam s).nabla (X₁ - X₂) Y) =
    fun s => (conn_fam s).nabla X₁ Y - (conn_fam s).nabla X₂ Y := by
    funext s; exact nabla_sub_left_aux (conn_fam s) X₁ X₂ Y
  rw [h_eq]
  exact VectorTimeDerivativeRules.t_sub_V (R := R)
    (fun s => (conn_fam s).nabla X₁ Y) (fun s => (conn_fam s).nabla X₂ Y) t


-- ============================================================
-- Section 3: Riemann Variation Theorems
-- ============================================================

variable (conn_fam : Time → AbstractAffineConnection R V)

/-- Raw 5-term expansion of the Riemann curvature variation.

Starting from Rm(X,Y)Z = ∇_X(∇_Y Z) - ∇_Y(∇_X Z) - ∇_{[X,Y]} Z,
the time derivative splits via the product rule into:
  ∂_t[Rm(X,Y)Z] = ∇_X(A(Y,Z)) + A(X, ∇_Y Z)
                 - ∇_Y(A(X,Z)) - A(Y, ∇_X Z)
                 - A([X,Y], Z)

This is the fundamental first variation before torsion-free simplification. -/
theorem riemann_variation_raw (X Y Z : V) (t : Time) :
  TimeDerivative.partial_t (fun s => Rm (conn_fam s) X Y Z) t =
  (conn_fam t).nabla X (conn_var conn_fam t Y Z) + conn_var conn_fam t X ((conn_fam t).nabla Y Z)
  - ((conn_fam t).nabla Y (conn_var conn_fam t X Z) + conn_var conn_fam t Y ((conn_fam t).nabla X Z))
  - conn_var conn_fam t (bracket X Y) Z := by
  -- Step 1: Unfold Rm to its three-term definition
  have h_unfold : (fun s => Rm (conn_fam s) X Y Z) =
    fun s => (conn_fam s).nabla X ((conn_fam s).nabla Y Z)
           - (conn_fam s).nabla Y ((conn_fam s).nabla X Z)
           - (conn_fam s).nabla (bracket X Y) Z := rfl
  rw [h_unfold]
  -- Step 2: Split ∂_t over the two subtractions (left-associative: (a-b)-c)
  have hsub1 := VectorTimeDerivativeRules.t_sub_V (R := R)
    (fun s => (conn_fam s).nabla X ((conn_fam s).nabla Y Z)
            - (conn_fam s).nabla Y ((conn_fam s).nabla X Z))
    (fun s => (conn_fam s).nabla (bracket X Y) Z) t
  have hsub2 := VectorTimeDerivativeRules.t_sub_V (R := R)
    (fun s => (conn_fam s).nabla X ((conn_fam s).nabla Y Z))
    (fun s => (conn_fam s).nabla Y ((conn_fam s).nabla X Z)) t
  rw [hsub1, hsub2]
  -- Step 3: Apply the atomic connection product rule to the two nested terms
  -- ∂_t[∇_X(∇_Y Z)] = A(X, ∇_Y Z) + ∇_X(A(Y,Z))
  have h1 : TimeDerivative.partial_t (fun s => (conn_fam s).nabla X ((conn_fam s).nabla Y Z)) t =
    conn_var conn_fam t X ((conn_fam t).nabla Y Z) +
    (conn_fam t).nabla X (conn_var conn_fam t Y Z) :=
    ConnectionTimeCalculus.t_conn_apply conn_fam X (fun s => (conn_fam s).nabla Y Z) t
  -- ∂_t[∇_Y(∇_X Z)] = A(Y, ∇_X Z) + ∇_Y(A(X,Z))
  have h2 : TimeDerivative.partial_t (fun s => (conn_fam s).nabla Y ((conn_fam s).nabla X Z)) t =
    conn_var conn_fam t Y ((conn_fam t).nabla X Z) +
    (conn_fam t).nabla Y (conn_var conn_fam t X Z) :=
    ConnectionTimeCalculus.t_conn_apply conn_fam Y (fun s => (conn_fam s).nabla X Z) t
  rw [h1, h2]
  -- Step 4: The bracket term ∂_t[∇_{[X,Y]} Z] is conn_var by definition
  have d3 : TimeDerivative.partial_t (fun s => (conn_fam s).nabla (bracket X Y) Z) t =
    conn_var conn_fam t (bracket X Y) Z := rfl
  rw [d3]
  -- Step 5: All terms now use conn_var and nabla; close by commutativity of addition
  abel

/-- Clean Riemann variation formula for torsion-free connections.

The 5-term raw expansion simplifies to 2 terms via the torsion-free
cancellation A([X,Y], Z) = A(∇_X Y, Z) - A(∇_Y X, Z):

  ∂_t[Rm(X,Y)Z] = (∇_X A)(Y,Z) - (∇_Y A)(X,Z)

This is the fundamental first variation of the Riemann curvature. -/
theorem riemann_variation [∀ s, TorsionFree (conn_fam s)] (X Y Z : V) (t : Time) :
  TimeDerivative.partial_t (fun s => Rm (conn_fam s) X Y Z) t =
  nabla_conn_var conn_fam t X Y Z - nabla_conn_var conn_fam t Y X Z := by
  rw [riemann_variation_raw conn_fam X Y Z t]
  -- Step 1: Rewrite A([X,Y], Z) using torsion-free: [X,Y] = ∇_X Y - ∇_Y X
  have h_tf : conn_var conn_fam t (bracket X Y) Z =
    conn_var conn_fam t ((conn_fam t).nabla X Y) Z -
    conn_var conn_fam t ((conn_fam t).nabla Y X) Z := by
    conv_lhs => rw [← TorsionFree.torsion_zero (conn := conn_fam t) X Y]
    exact conn_var_sub_left conn_fam
      ((conn_fam t).nabla X Y) ((conn_fam t).nabla Y X) Z t
  rw [h_tf]
  -- Step 2: Unfold nabla_conn_var and close by additive group normalization
  unfold nabla_conn_var
  abel

/-- The Riemann variation equals the abstract definition `t_rm`. -/
theorem riemann_variation_eq_t_rm [∀ s, TorsionFree (conn_fam s)] (X Y Z : V) (t : Time) :
  TimeDerivative.partial_t (fun s => Rm (conn_fam s) X Y Z) t =
  t_rm conn_fam t X Y Z := by
  rw [riemann_variation conn_fam X Y Z t]; rfl

/-- Covector evaluation of the Riemann variation: for any covector ω,
  ω(∂_t[Rm(X,Y)Z]) = ω((∇_X A)(Y,Z)) - ω((∇_Y A)(X,Z)). -/
theorem riemann_variation_eval [∀ s, TorsionFree (conn_fam s)]
  (X Y Z : V) (ω : V →ₗ[R] R) (t : Time) :
  ω (TimeDerivative.partial_t (fun s => Rm (conn_fam s) X Y Z) t) =
  ω (nabla_conn_var conn_fam t X Y Z) - ω (nabla_conn_var conn_fam t Y X Z) := by
  rw [riemann_variation conn_fam X Y Z t]
  exact ω.map_sub _ _
