import DifferentialGeometry.Synthetic.Flow.RicciFlow.Evolution.Connection
import DifferentialGeometry.Synthetic.Analysis.NablaTimeInteraction
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Riemann Curvature Variation

Connection variation and the Riemann variation formula
under torsion-free connections.
-/

open SyntheticTensor

-- ============================================================
-- Section 1: Connection Variation at Tensor Level
-- ============================================================

section ConnVarTensor

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Connection variation as a (1,0) tensor:
    A(X,Y) = ∂_t(conn_s X Y) represented as dt_tensor of vectorToData.
    Evaluates as: conn_var_vector(t,X,Y) ![] ![ω] = dt(s ↦ ω(conn_s X Y))(t). -/
noncomputable def conn_var_vector
    (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (t : Time) (X Y : V) : TensorData R V 1 0 :=
  dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X Y))

theorem conn_var_vector_eval
    (td : TimeDerivativeData R Time) (conn_fam : Time → V → V → V)
    (t : Time) (X Y : V) (ω : V →ₗ[R] R) :
    conn_var_vector td conn_fam t X Y ![] ![ω] =
    (td.dt (fun s => ω (conn_fam s X Y))) t := rfl

end ConnVarTensor

-- ============================================================
-- Section 2: Riemann Variation and Torsion-Free Simplification
-- ============================================================

section RiemannVariation

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- The Riemann variation at the scalar level (5-term expansion).

    ∂_t[ω(Rm(s)(X,Y)Z)] = ω(conn_t X A(Y,Z)) + A(X, conn_t Y Z)(ω)
      − ω(conn_t Y A(X,Z)) − A(Y, conn_t X Z)(ω) − A([X,Y], Z)(ω)

    Proof uses NablaTimeProductRule to decompose ∂_t of each conn composition,
    then collects terms. -/
theorem riemann_variation_raw
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (_hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (_hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (X Y Z : V) (ω : V →ₗ[R] R) (t : Time) :
    (td.dt (fun s => ω (Rm emb (conn_fam s) X Y Z))) t =
    nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X
      (conn_var_vector td conn_fam t Y Z) ![] ![ω]
    + conn_var_vector td conn_fam t X (conn_fam t Y Z) ![] ![ω]
    - nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) Y
        (conn_var_vector td conn_fam t X Z) ![] ![ω]
    - conn_var_vector td conn_fam t Y (conn_fam t X Z) ![] ![ω]
    - conn_var_vector td conn_fam t (bracket emb X Y) Z ![] ![ω] := by
  -- Expand Rm and split dt over subtraction
  have h_eq : (fun s => ω (Rm emb (conn_fam s) X Y Z)) =
      (fun s => ω (conn_fam s X (conn_fam s Y Z))) -
      (fun s => ω (conn_fam s Y (conn_fam s X Z))) -
      (fun s => ω (conn_fam s (bracket emb X Y) Z)) := by
    funext s; simp [Rm, map_sub]
  rw [h_eq]
  have h12 := congr_fun (map_sub td.dt
    ((fun s => ω (conn_fam s X (conn_fam s Y Z))) - (fun s => ω (conn_fam s Y (conn_fam s X Z))))
    (fun s => ω (conn_fam s (bracket emb X Y) Z))) t
  have h1 := congr_fun (map_sub td.dt
    (fun s => ω (conn_fam s X (conn_fam s Y Z)))
    (fun s => ω (conn_fam s Y (conn_fam s X Z)))) t
  simp only [Pi.sub_apply] at h12 h1; rw [h12, h1]
  -- Now the goal has three separate dt terms. Decompose each via NablaTimeProductRule.
  -- TERM 1: dt(s ↦ ω(conn_s X (conn_s Y Z))) t
  -- Use NablaTimeProductRule with T(s) = vectorToData(conn_s Y Z)
  have h_nv1 : ∀ s, vectorToData (R := R) (conn_fam s X (conn_fam s Y Z)) =
      nabla_tensor emb (conn_fam s) (ha_fam s) (hl_fam s) X
        (vectorToData (R := R) (conn_fam s Y Z)) :=
    fun s => (nabla_vector emb (conn_fam s) (ha_fam s) (hl_fam s) X (conn_fam s Y Z)).symm
  have h_pr1 := h_pr X (fun s => vectorToData (R := R) (conn_fam s Y Z)) t
  -- h_pr1 is a tensor equality. Rewrite the LHS function to match.
  have h_pr1' : dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X (conn_fam s Y Z))) =
      conn_var_tensor emb td conn_fam ha_fam hl_fam t X (vectorToData (R := R) (conn_fam t Y Z)) +
      nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X
        (dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s Y Z))) := by
    rw [show (fun s => vectorToData (R := R) (conn_fam s X (conn_fam s Y Z))) =
      (fun s => nabla_tensor emb (conn_fam s) (ha_fam s) (hl_fam s) X
        (vectorToData (R := R) (conn_fam s Y Z))) from funext h_nv1]
    exact h_pr1
  -- conn_var_tensor(X, vectorToData(V)) = conn_var_vector(X, V) when V is time-constant at t
  have h_cv1 : conn_var_tensor emb td conn_fam ha_fam hl_fam t X
      (vectorToData (R := R) (conn_fam t Y Z)) =
      conn_var_vector td conn_fam t X (conn_fam t Y Z) := by
    simp only [conn_var_tensor, conn_var_vector]
    congr 1; funext s
    exact nabla_vector emb (conn_fam s) (ha_fam s) (hl_fam s) X (conn_fam t Y Z)
  -- Evaluate term 1 at ![] ![ω]
  have h_t1 : (td.dt (fun s => ω (conn_fam s X (conn_fam s Y Z)))) t =
      conn_var_vector td conn_fam t X (conn_fam t Y Z) ![] ![ω] +
      nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X
        (conn_var_vector td conn_fam t Y Z) ![] ![ω] := by
    change (dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X (conn_fam s Y Z))) ![] ![ω]) = _
    rw [h_pr1', h_cv1]; rfl
  -- TERM 2: same structure with X↔Y
  have h_nv2 : ∀ s, vectorToData (R := R) (conn_fam s Y (conn_fam s X Z)) =
      nabla_tensor emb (conn_fam s) (ha_fam s) (hl_fam s) Y
        (vectorToData (R := R) (conn_fam s X Z)) :=
    fun s => (nabla_vector emb (conn_fam s) (ha_fam s) (hl_fam s) Y (conn_fam s X Z)).symm
  have h_pr2 := h_pr Y (fun s => vectorToData (R := R) (conn_fam s X Z)) t
  have h_pr2' : dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s Y (conn_fam s X Z))) =
      conn_var_tensor emb td conn_fam ha_fam hl_fam t Y (vectorToData (R := R) (conn_fam t X Z)) +
      nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) Y
        (dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s X Z))) := by
    rw [show (fun s => vectorToData (R := R) (conn_fam s Y (conn_fam s X Z))) =
      (fun s => nabla_tensor emb (conn_fam s) (ha_fam s) (hl_fam s) Y
        (vectorToData (R := R) (conn_fam s X Z))) from funext h_nv2]
    exact h_pr2
  have h_cv2 : conn_var_tensor emb td conn_fam ha_fam hl_fam t Y
      (vectorToData (R := R) (conn_fam t X Z)) =
      conn_var_vector td conn_fam t Y (conn_fam t X Z) := by
    simp only [conn_var_tensor, conn_var_vector]
    congr 1; funext s
    exact nabla_vector emb (conn_fam s) (ha_fam s) (hl_fam s) Y (conn_fam t X Z)
  have h_t2 : (td.dt (fun s => ω (conn_fam s Y (conn_fam s X Z)))) t =
      conn_var_vector td conn_fam t Y (conn_fam t X Z) ![] ![ω] +
      nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) Y
        (conn_var_vector td conn_fam t X Z) ![] ![ω] := by
    change (dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s Y (conn_fam s X Z))) ![] ![ω]) = _
    rw [h_pr2', h_cv2]; rfl
  -- TERM 3: bracket term (bracket is time-independent)
  have h_nv3 : ∀ s, vectorToData (R := R) (conn_fam s (bracket emb X Y) Z) =
      nabla_tensor emb (conn_fam s) (ha_fam s) (hl_fam s) (bracket emb X Y)
        (vectorToData (R := R) Z) :=
    fun s => (nabla_vector emb (conn_fam s) (ha_fam s) (hl_fam s) (bracket emb X Y) Z).symm
  have h_pr3 := h_pr (bracket emb X Y) (fun _ => vectorToData (R := R) Z) t
  have h_pr3' : dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s (bracket emb X Y) Z)) =
      conn_var_tensor emb td conn_fam ha_fam hl_fam t (bracket emb X Y) (vectorToData (R := R) Z) +
      nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) (bracket emb X Y)
        (dt_tensor td t (fun _ => vectorToData (R := R) Z)) := by
    rw [show (fun s => vectorToData (R := R) (conn_fam s (bracket emb X Y) Z)) =
      (fun s => nabla_tensor emb (conn_fam s) (ha_fam s) (hl_fam s) (bracket emb X Y)
        (vectorToData (R := R) Z)) from funext h_nv3]
    exact h_pr3
  -- dt of constant tensor = 0, and nabla of 0 = 0
  have h_const_z : dt_tensor td t (fun _ => vectorToData (R := R) Z) = 0 := dt_tensor_const td t _
  have h_cv3 : conn_var_tensor emb td conn_fam ha_fam hl_fam t (bracket emb X Y)
      (vectorToData (R := R) Z) = conn_var_vector td conn_fam t (bracket emb X Y) Z := by
    simp only [conn_var_tensor, conn_var_vector]
    congr 1; funext s
    exact nabla_vector emb (conn_fam s) (ha_fam s) (hl_fam s) (bracket emb X Y) Z
  have h_nabla_zero : nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) (bracket emb X Y)
      (0 : TensorData R V 1 0) = 0 := by
    ext vs' αs'; rw [nabla_tensor_eval]; simp [MultilinearMap.zero_apply]
  have h_t3 : (td.dt (fun s => ω (conn_fam s (bracket emb X Y) Z))) t =
      conn_var_vector td conn_fam t (bracket emb X Y) Z ![] ![ω] := by
    change (dt_tensor td t (fun s => vectorToData (R := R) (conn_fam s (bracket emb X Y) Z)) ![] ![ω]) = _
    rw [h_pr3', h_const_z, h_cv3, h_nabla_zero]; simp
  -- Combine all three terms
  rw [h_t1, h_t2, h_t3]; ring

/-- Connection variation is additive in its first argument:
    A(X₁ + X₂, Y) = A(X₁, Y) + A(X₂, Y). -/
theorem conn_var_add_left
    (td : TimeDerivativeData R Time) (conn_fam : Time → V → V → V)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (t : Time) (X₁ X₂ Y : V) :
    conn_var_vector td conn_fam t (X₁ + X₂) Y =
    conn_var_vector td conn_fam t X₁ Y + conn_var_vector td conn_fam t X₂ Y := by
  simp only [conn_var_vector]
  rw [show (fun s => vectorToData (R := R) (conn_fam s (X₁ + X₂) Y)) =
    (fun s => vectorToData (R := R) (conn_fam s X₁ Y) + vectorToData (R := R) (conn_fam s X₂ Y))
    from funext (fun s => by rw [hal_fam s X₁ X₂ Y, vectorToData_add])]
  exact dt_tensor_add td t _ _

/-- Connection variation respects subtraction in the first argument:
    A(X₁ - X₂, Y) = A(X₁, Y) - A(X₂, Y). -/
theorem conn_var_sub_left
    (td : TimeDerivativeData R Time) (conn_fam : Time → V → V → V)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (t : Time) (X₁ X₂ Y : V) :
    conn_var_vector td conn_fam t (X₁ - X₂) Y =
    conn_var_vector td conn_fam t X₁ Y - conn_var_vector td conn_fam t X₂ Y := by
  simp only [conn_var_vector]
  rw [show (fun s => vectorToData (R := R) (conn_fam s (X₁ - X₂) Y)) =
    (fun s => vectorToData (R := R) (conn_fam s X₁ Y) - vectorToData (R := R) (conn_fam s X₂ Y))
    from funext (fun s => by
      rw [show X₁ - X₂ = X₁ + (-1 : R) • X₂ from by rw [neg_one_smul, sub_eq_add_neg],
        hal_fam s X₁ _ Y, hsl_fam s (-1) X₂ Y, vectorToData_add, vectorToData_smul]
      simp [sub_eq_add_neg])]
  exact dt_tensor_sub td t _ _

/-- The covariant derivative of the connection variation (∇A).
    (∇_X A)(Y,Z) = ∇_X(A(Y,Z)) - A(∇_X Y, Z) - A(Y, ∇_X Z)
    at the scalar level (applied to ω). -/
noncomputable def nabla_conn_var_scalar
    (emb : DerivationEmbedding k R V) (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (t : Time) (X Y Z : V) (ω : V →ₗ[R] R) : R :=
  nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X
    (conn_var_vector td conn_fam t Y Z) ![] ![ω]
  - conn_var_vector td conn_fam t (conn_fam t X Y) Z ![] ![ω]
  - conn_var_vector td conn_fam t Y (conn_fam t X Z) ![] ![ω]

/-- Torsion-free simplification of the Riemann variation.
    Under torsion-free connections, the 5-term variation simplifies to:
    ∂_t Rm(X,Y,Z)(ω) = (∇_X A)(Y,Z)(ω) − (∇_Y A)(X,Z)(ω)
    where (∇_X A)(Y,Z) is the tensor-level covariant derivative of A. -/
theorem riemann_variation_torsion_free
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (h_tf : ∀ s, IsTorsionFree emb (conn_fam s))
    (X Y Z : V) (ω : V →ₗ[R] R) (t : Time) :
    (td.dt (fun s => ω (Rm emb (conn_fam s) X Y Z))) t =
    nabla_conn_var_scalar emb td conn_fam ha_fam hl_fam t X Y Z ω -
    nabla_conn_var_scalar emb td conn_fam ha_fam hl_fam t Y X Z ω := by
  rw [riemann_variation_raw emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr X Y Z ω t]
  simp only [nabla_conn_var_scalar]
  have h_bracket : conn_var_vector td conn_fam t (bracket emb X Y) Z =
      conn_var_vector td conn_fam t (conn_fam t X Y) Z -
      conn_var_vector td conn_fam t (conn_fam t Y X) Z := by
    rw [show bracket emb X Y = conn_fam t X Y - conn_fam t Y X from (h_tf t X Y).symm]
    exact conn_var_sub_left td conn_fam hal_fam hsl_fam t _ _ Z
  -- Evaluate at ![] ![ω] and simplify
  have h_ev : conn_var_vector td conn_fam t (bracket emb X Y) Z ![] ![ω] =
      conn_var_vector td conn_fam t (conn_fam t X Y) Z ![] ![ω] -
      conn_var_vector td conn_fam t (conn_fam t Y X) Z ![] ![ω] := by
    show (conn_var_vector td conn_fam t (bracket emb X Y) Z) ![] ![ω] = _
    rw [h_bracket]; simp [MultilinearMap.sub_apply]
  rw [h_ev]; ring

/-- Connects scalar-level variation to tensor-level dt_tensor.
    dt_tensor(Rm)(X,Y,Z)(ω) = dt(s ↦ ω(Rm_s(X,Y)Z)) by dt_tensor_eval + Rm_tensor_eval. -/
theorem variation_eq_dt
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (X Y Z : V) (ω : V →ₗ[R] R) (t : Time) :
    dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)) ![X, Y, Z] ![ω] =
    (td.dt (fun s => ω (Rm emb (conn_fam s) X Y Z))) t := by
  -- Both sides unfold to the same thing
  change (td.dt (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)
    ![X, Y, Z] ![ω])) t = _
  congr 1

/-- The scalar-level Riemann variation formula value.
    This is the 5-term expression from `riemann_variation_raw`, defined
    independently of dt_tensor(Rm). -/
noncomputable def riemann_variation_scalar
    (emb : DerivationEmbedding k R V) (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (t : Time) (X Y Z : V) (ω : V →ₗ[R] R) : R :=
  nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) X
    (conn_var_vector td conn_fam t Y Z) ![] ![ω]
  + conn_var_vector td conn_fam t X (conn_fam t Y Z) ![] ![ω]
  - nabla_tensor emb (conn_fam t) (ha_fam t) (hl_fam t) Y
      (conn_var_vector td conn_fam t X Z) ![] ![ω]
  - conn_var_vector td conn_fam t Y (conn_fam t X Z) ![] ![ω]
  - conn_var_vector td conn_fam t (bracket emb X Y) Z ![] ![ω]

/-- The scalar variation formula equals dt_tensor(Rm) evaluation.
    This is the bridge between the geometric formula and the tensor-level object. -/
theorem variation_scalar_eq_dt_tensor
    (emb : DerivationEmbedding k R V) (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ s, ∀ X Y Z, conn_fam s X (Y + Z) = conn_fam s X Y + conn_fam s X Z)
    (hal_fam : ∀ s, ∀ X Y Z, conn_fam s (X + Y) Z = conn_fam s X Z + conn_fam s Y Z)
    (hsl_fam : ∀ s, ∀ (f : R) X Z, conn_fam s (f • X) Z = f • conn_fam s X Z)
    (hl_fam : ∀ s, ∀ X (f : R) Y, conn_fam s X (f • Y) = (emb.embed X) f • Y + f • conn_fam s X Y)
    (h_pr : NablaTimeProductRule emb td conn_fam ha_fam hl_fam)
    (X Y Z : V) (ω : V →ₗ[R] R) (t : Time) :
    riemann_variation_scalar emb td conn_fam ha_fam hl_fam t X Y Z ω =
    dt_tensor td t (fun s => Rm_tensor emb (conn_fam s) (ha_fam s) (hal_fam s) (hsl_fam s) (hl_fam s)) ![X, Y, Z] ![ω] := by
  simp only [riemann_variation_scalar]
  rw [variation_eq_dt emb td conn_fam ha_fam hal_fam hsl_fam hl_fam X Y Z ω t]
  exact (riemann_variation_raw emb td conn_fam ha_fam hal_fam hsl_fam hl_fam h_pr X Y Z ω t).symm

end RiemannVariation
