import DifferentialGeometry.Synthetic.Analysis.NablaOnTensors
import DifferentialGeometry.Synthetic.Analysis.TimeOnTensors

/-!
# ∂_t and ∇ Interaction

- `t_nabla_tensor`: ∂_t commutes with ∇ for fixed connection
- `conn_var_tensor`: connection variation tensor
- `t_nabla_eval`: ∂_t[∇_X T] when both connection and tensor vary
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open BigOperators
open SyntheticTensor

-- ============================================================
-- ∂_t commutes with ∇ for fixed connection
-- ============================================================

section FixedConn

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- ∂_t commutes with ∇ when the connection is FIXED (not time-dependent).
    Proof uses SpatialTemporalComm for the leading X(T vs αs) term;
    correction sums commute because conn and nabla_dual are constant in time. -/
theorem t_nabla_tensor
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (h_st : SpatialTemporalComm emb td)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time) :
    dt_tensor td t (fun τ => nabla_tensor emb conn ha hl X (T τ)) =
    nabla_tensor emb conn ha hl X (dt_tensor td t T) := by
  ext vs αs
  simp only [dt_tensor_eval, nabla_tensor_eval]
  -- LHS: td.dt (fun τ => X(T τ vs αs) - Σᵢ ... - Σⱼ ...) t
  -- Split dt over subtraction and sums
  -- Leading term: SpatialTemporalComm
  have h_lead : (td.dt (fun τ => (emb.embed X) (T τ vs αs))) t =
      (emb.embed X) ((td.dt (fun τ => T τ vs αs)) t) :=
    h_st X (fun τ => T τ vs αs) t
  -- Vector correction: conn is constant, so update arg is constant
  -- td.dt (fun τ => T τ (update vs i (conn X (vs i))) αs) t
  -- = (dt_tensor td t T) (update vs i (conn X (vs i))) αs  [by def]
  -- Covector correction: nabla_dual is constant, so update arg is constant
  -- td.dt (fun τ => T τ vs (update αs j (nabla_dual ... X (αs j)))) t
  -- = (dt_tensor td t T) vs (update αs j (nabla_dual ... X (αs j)))  [by def]
  -- All correction sums are just dt_tensor evaluated at fixed arguments.
  -- So LHS = X(dt T vs αs) - Σᵢ (dt T)(update vs i ...) αs - Σⱼ (dt T) vs (update αs j ...) = RHS
  -- Formalize: split the Time → R function into three parts
  have h_eq : (fun τ => (emb.embed X) (T τ vs αs)
      - ∑ i : Fin s, T τ (Function.update vs i (conn X (vs i))) αs
      - ∑ j : Fin r, T τ vs (Function.update αs j
          (nabla_dual emb conn ha hl X (αs j)))) =
      (fun τ => (emb.embed X) (T τ vs αs))
      - (fun τ => ∑ i : Fin s, T τ (Function.update vs i (conn X (vs i))) αs)
      - (fun τ => ∑ j : Fin r, T τ vs (Function.update αs j
          (nabla_dual emb conn ha hl X (αs j)))) := by
    funext τ; simp only [Pi.sub_apply]
  rw [h_eq, map_sub, map_sub]
  simp only [Pi.sub_apply]
  -- Now use h_lead for the first term
  rw [h_lead]
  -- For the sum terms: dt distributes over Finset.sum
  -- Vector correction sum
  have h_vec : (fun τ => ∑ i : Fin s,
      T τ (Function.update vs i (conn X (vs i))) αs) =
      ∑ i : Fin s, (fun τ => T τ (Function.update vs i (conn X (vs i))) αs) := by
    funext τ; simp [Finset.sum_apply]
  -- Covector correction sum
  have h_cov : (fun τ => ∑ j : Fin r,
      T τ vs (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))) =
      ∑ j : Fin r, (fun τ => T τ vs (Function.update αs j
        (nabla_dual emb conn ha hl X (αs j)))) := by
    funext τ; simp [Finset.sum_apply]
  rw [h_vec, h_cov, map_sum, map_sum]; simp [Finset.sum_apply]

end FixedConn

-- ============================================================
-- Connection variation tensor
-- ============================================================

section ConnVar

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Connection variation tensor: measures how ∇_X T changes as the connection varies.
    conn_var_tensor(t, X, T) = ∂_t[∇^(s)_X T] with T FIXED (not time-dependent).

    Evaluation: conn_var_tensor(t, X, T)(vs)(αs) =
      - Σᵢ dt(s ↦ T(update vs i (conn(s) X (vs i)))(αs)) at t
      - Σⱼ dt(s ↦ T(vs)(update αs j (∇*^(s)_X αⱼ))) at t

    The leading X(T vs αs) term vanishes because T is constant in time. -/
noncomputable def conn_var_tensor
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (T : TensorData R V r s) : TensorData R V r s :=
  dt_tensor td t (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T)

/-- Evaluation formula for conn_var_tensor. The leading X-term vanishes
    because T doesn't depend on time. -/
theorem conn_var_tensor_eval
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (T : TensorData R V r s) (vs αs) :
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X T vs αs =
    - (td.dt (fun τ => ∑ i : Fin s,
        T (Function.update vs i (conn_fam τ X (vs i))) αs)) t
    - (td.dt (fun τ => ∑ j : Fin r,
        T vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j))))) t := by
  simp only [conn_var_tensor, dt_tensor_eval, nabla_tensor_eval]
  -- The leading X(T vs αs) term is constant → dt kills it
  have h_const : (td.dt (fun _ => (emb.embed X) (T vs αs))) t = 0 :=
    congr_fun (t_const_R td ((emb.embed X) (T vs αs))) t
  -- Split the subtraction
  have h_eq : (fun τ => (emb.embed X) (T vs αs)
      - ∑ i : Fin s, T (Function.update vs i (conn_fam τ X (vs i))) αs
      - ∑ j : Fin r, T vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) =
      (fun _ => (emb.embed X) (T vs αs))
      - (fun τ => ∑ i : Fin s, T (Function.update vs i (conn_fam τ X (vs i))) αs)
      - (fun τ => ∑ j : Fin r, T vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ; simp only [Pi.sub_apply]
  rw [h_eq, map_sub, map_sub]
  simp only [Pi.sub_apply, h_const]; ring

end ConnVar

-- ============================================================
-- Exact evaluation for ∂_t[∇^(s)_X T(s)] (varying conn + varying T)
-- ============================================================

section VaryingConnT

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Exact evaluation formula for ∂_t[∇^(s)_X T(s)] when both connection and tensor
    vary with time. Uses SpatialTemporalComm for the leading term; correction sums
    retain the full time-dependent expressions under dt.

    This generalizes both t_nabla_tensor (conn fixed) and conn_var_tensor (T fixed). -/
theorem t_nabla_eval
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (h_st : SpatialTemporalComm emb td)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time) (vs αs) :
    dt_tensor td t (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ))
      vs αs =
    (emb.embed X) ((td.dt (fun τ => T τ vs αs)) t)
    - (td.dt (fun τ => ∑ i : Fin s,
        T τ (Function.update vs i (conn_fam τ X (vs i))) αs)) t
    - (td.dt (fun τ => ∑ j : Fin r,
        T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j))))) t := by
  simp only [dt_tensor_eval, nabla_tensor_eval]
  have h_eq : (fun τ => (emb.embed X) (T τ vs αs)
      - ∑ i : Fin s, T τ (Function.update vs i (conn_fam τ X (vs i))) αs
      - ∑ j : Fin r, T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) =
      (fun τ => (emb.embed X) (T τ vs αs))
      - (fun τ => ∑ i : Fin s, T τ (Function.update vs i (conn_fam τ X (vs i))) αs)
      - (fun τ => ∑ j : Fin r, T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ; simp only [Pi.sub_apply]
  rw [h_eq, map_sub, map_sub]
  simp only [Pi.sub_apply]
  -- Leading term: SpatialTemporalComm
  rw [h_st X (fun τ => T τ vs αs) t]

/-- conn_var_tensor is additive in T. -/
theorem conn_var_tensor_add
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (T₁ T₂ : TensorData R V r s) :
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X (T₁ + T₂) =
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X T₁ +
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X T₂ := by
  simp only [conn_var_tensor]
  have h : (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T₁ + T₂)) =
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₁ +
                nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₂) := by
    funext τ; exact nabla_add emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₁ T₂
  rw [h]; exact dt_tensor_add td t _ _

/-- conn_var_tensor commutes with constant R-scalar multiplication. -/
theorem conn_var_tensor_smul
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (c : R) (T : TensorData R V r s) :
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X (c • T) =
    c • conn_var_tensor emb td conn_fam ha_fam hl_fam t X T := by
  simp only [conn_var_tensor]
  have h : (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (c • T)) =
      (fun τ => c • nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T +
                (emb.embed X) c • T) := by
    funext τ; ext vs αs
    rw [nabla_smul emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X c T vs αs]
    simp [MultilinearMap.add_apply, MultilinearMap.smul_apply, smul_eq_mul]; ring
  rw [h, dt_tensor_add, dt_tensor_smul_const, dt_tensor_const]
  simp [add_zero]

end VaryingConnT

-- ============================================================
-- Deferred item 1: t_linear_map
-- ∂_t(ω(F(s))) = dt_tensor evaluation at vectorToData(F(s))
-- ============================================================

section TLinearMap

variable {R V Time : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- ∂_t(ω(F(s))) equals the evaluation of dt_tensor on vectorToData(F(s)) at covector ω.
    This is the canonical way to express "∂_t commutes with constant covectors"
    in the transparent tensor framework. Proof by rfl. -/
theorem t_linear_map (td : TimeDerivativeData R Time) (t : Time)
    (ω : V →ₗ[R] R) (F : Time → V) :
    (td.dt (fun s => ω (F s))) t =
    dt_tensor td t (fun s => vectorToData (R := R) (F s)) ![] ![ω] :=
  rfl

end TLinearMap

-- ============================================================
-- Deferred item 2: t_conn_apply
-- ∂_t commutes with ∇_X on vectors (fixed connection).
-- The vector-level specialization of t_nabla_tensor.
-- ============================================================

section TConnApply

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- For a FIXED connection, ∂_t commutes with ∇_X on vectors:
    ∂_t[vectorToData(conn X (F τ))] = ∇_X(∂_t[vectorToData(F τ)]).
    Derived from t_nabla_tensor applied to T(τ) = vectorToData(F(τ)),
    using nabla_vector to identify ∇_X(vectorToData v) = vectorToData(conn X v). -/
theorem t_conn_apply
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R Time)
    (h_st : SpatialTemporalComm emb td)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (F : Time → V) (t : Time) :
    dt_tensor td t (fun τ => vectorToData (R := R) (conn X (F τ))) =
    nabla_tensor emb conn ha hl X (dt_tensor td t (fun τ => vectorToData (R := R) (F τ))) := by
  -- Step 1: Rewrite LHS using nabla_vector in reverse
  have h_eq : (fun τ => vectorToData (R := R) (conn X (F τ))) =
      (fun τ => nabla_tensor emb conn ha hl X (vectorToData (R := R) (F τ))) := by
    funext τ; exact (nabla_vector emb conn ha hl X (F τ)).symm
  rw [h_eq]
  -- Step 2: Apply t_nabla_tensor (∂_t commutes with ∇ for fixed connection)
  exact t_nabla_tensor emb td h_st conn ha hl X (fun τ => vectorToData (R := R) (F τ)) t

end TConnApply
