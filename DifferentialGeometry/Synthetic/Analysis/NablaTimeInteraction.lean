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

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- ∂_t commutes with ∇ when the connection is FIXED (not time-dependent).
    Proof uses SpatialTemporalComm for the leading X(T vs αs) term;
    correction sums commute because conn and nabla_dual are constant in time.

    The smoothness hypothesis `hT` gives smoothness of every scalar slice of
    `T`. The first sum's summands are also slices of T (at fixed arguments),
    so closure follows via `isSmoothFam_sum`. The *spatial* derivative family
    `fun τ => (emb.embed X)(T τ vs αs)` is supplied separately as `hXT`. -/
theorem t_nabla_tensor
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs))
    (hXT : ∀ vs αs, td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)))
    (hT_nabla : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb conn ha hl X (T τ) vs αs)) :
    dt_tensor td t (fun τ => nabla_tensor emb conn ha hl X (T τ)) hT_nabla =
    nabla_tensor emb conn ha hl X (dt_tensor td t T hT) := by
  ext vs αs
  simp only [dt_tensor_eval, nabla_tensor_eval]
  -- Split the lambda into three parts
  have h_eq : (fun τ => (emb.embed X) (T τ vs αs)
      - ∑ i : Fin s, T τ (Function.update vs i (conn X (vs i))) αs
      - ∑ j : Fin r, T τ vs (Function.update αs j
          (nabla_dual emb conn ha hl X (αs j)))) =
      (fun τ => (emb.embed X) (T τ vs αs))
      - (fun τ => ∑ i : Fin s, T τ (Function.update vs i (conn X (vs i))) αs)
      - (fun τ => ∑ j : Fin r, T τ vs (Function.update αs j
          (nabla_dual emb conn ha hl X (αs j)))) := by
    funext τ; simp only [Pi.sub_apply]
  -- Vector correction sum: factor out finset sum from lambda
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
  -- Smoothness of the three pieces
  have hS_X : td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)) := hXT vs αs
  have hS_vec_i : ∀ i : Fin s, td.isSmoothFam
      (fun τ => T τ (Function.update vs i (conn X (vs i))) αs) :=
    fun i => hT (Function.update vs i (conn X (vs i))) αs
  have hS_vec_sum : td.isSmoothFam
      (fun τ => ∑ i : Fin s, T τ (Function.update vs i (conn X (vs i))) αs) := by
    rw [h_vec]
    exact td.isSmoothFam_sum Finset.univ _ (fun i _ => hS_vec_i i)
  have hS_cov_j : ∀ j : Fin r, td.isSmoothFam
      (fun τ => T τ vs (Function.update αs j
        (nabla_dual emb conn ha hl X (αs j)))) :=
    fun j => hT vs (Function.update αs j (nabla_dual emb conn ha hl X (αs j)))
  have hS_cov_sum : td.isSmoothFam
      (fun τ => ∑ j : Fin r, T τ vs (Function.update αs j
        (nabla_dual emb conn ha hl X (αs j)))) := by
    rw [h_cov]
    exact td.isSmoothFam_sum Finset.univ _ (fun j _ => hS_cov_j j)
  rw [h_eq,
      td.dt_apply_sub _ _ _ (td.isSmoothFam_sub _ _ hS_X hS_vec_sum) hS_cov_sum,
      td.dt_apply_sub _ _ _ hS_X hS_vec_sum]
  -- Leading term: SpatialTemporalComm (requires smoothness of `fun τ => T τ vs αs`)
  rw [h_st X (fun τ => T τ vs αs) t (hT vs αs)]
  rw [h_vec, h_cov,
      td.dt_apply_sum _ _ _ (fun i _ => hS_vec_i i),
      td.dt_apply_sum _ _ _ (fun j _ => hS_cov_j j)]

end FixedConn

-- ============================================================
-- Connection variation tensor
-- ============================================================

section ConnVar

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Connection variation tensor: measures how ∇_X T changes as the connection varies.
    conn_var_tensor(t, X, T) = ∂_t[∇^(s)_X T] with T FIXED (not time-dependent).

    Evaluation: conn_var_tensor(t, X, T)(vs)(αs) =
      - Σᵢ dt_apply(s ↦ T(update vs i (conn(s) X (vs i)))(αs)) at t
      - Σⱼ dt_apply(s ↦ T(vs)(update αs j (∇*^(s)_X αⱼ))) at t

    The leading X(T vs αs) term vanishes because T is constant in time.

    `h_conn_smooth_v` / `h_conn_smooth_c` assert smoothness of the connection-
    dependent scalar families in each vector- and covector-slot respectively. -/
noncomputable def conn_var_tensor
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (T : TensorData R V r s)
    (h_nabla_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T vs αs))
    : TensorData R V r s :=
  dt_tensor td t (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T)
    h_nabla_smooth

/-- Evaluation formula for conn_var_tensor. The leading X-term vanishes
    because T doesn't depend on time. -/
theorem conn_var_tensor_eval
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (T : TensorData R V r s)
    (h_nabla_smooth : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T vs αs))
    (h_conn_smooth_v : ∀ i vs αs, td.isSmoothFam
      (fun τ => T (Function.update vs i (conn_fam τ X (vs i))) αs))
    (h_conn_smooth_c : ∀ j vs αs, td.isSmoothFam
      (fun τ => T vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))))
    (vs αs) :
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X T h_nabla_smooth vs αs =
    - td.dt_apply (fun τ => ∑ i : Fin s,
        T (Function.update vs i (conn_fam τ X (vs i))) αs) t
    - td.dt_apply (fun τ => ∑ j : Fin r,
        T vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) t := by
  simp only [conn_var_tensor, dt_tensor_eval, nabla_tensor_eval]
  -- The leading X(T vs αs) term is constant → dt_apply kills it
  have h_const : td.dt_apply (fun _ => (emb.embed X) (T vs αs)) t = 0 :=
    td.dt_apply_const ((emb.embed X) (T vs αs)) t
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
  have h_vec_sum : (fun τ => ∑ i : Fin s,
      T (Function.update vs i (conn_fam τ X (vs i))) αs) =
      ∑ i : Fin s, (fun τ => T (Function.update vs i (conn_fam τ X (vs i))) αs) := by
    funext τ; simp [Finset.sum_apply]
  have h_cov_sum : (fun τ => ∑ j : Fin r,
      T vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) =
      ∑ j : Fin r, (fun τ => T vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ; simp [Finset.sum_apply]
  -- Smoothness of the three pieces
  have hS_const : td.isSmoothFam (fun _ => (emb.embed X) (T vs αs)) :=
    td.isSmoothFam_const _
  have hS_vec_sum : td.isSmoothFam
      (fun τ => ∑ i : Fin s, T (Function.update vs i (conn_fam τ X (vs i))) αs) := by
    rw [h_vec_sum]
    exact td.isSmoothFam_sum Finset.univ _ (fun i _ => h_conn_smooth_v i vs αs)
  have hS_cov_sum : td.isSmoothFam
      (fun τ => ∑ j : Fin r, T vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    rw [h_cov_sum]
    exact td.isSmoothFam_sum Finset.univ _ (fun j _ => h_conn_smooth_c j vs αs)
  rw [h_eq,
      td.dt_apply_sub _ _ _
        (td.isSmoothFam_sub _ _ hS_const hS_vec_sum) hS_cov_sum,
      td.dt_apply_sub _ _ _ hS_const hS_vec_sum, h_const]; ring

end ConnVar

-- ============================================================
-- Exact evaluation for ∂_t[∇^(s)_X T(s)] (varying conn + varying T)
-- ============================================================

section VaryingConnT

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Exact evaluation formula for ∂_t[∇^(s)_X T(s)] when both connection and tensor
    vary with time. Uses SpatialTemporalComm for the leading term; correction sums
    retain the full time-dependent expressions under dt_apply.

    This generalizes both t_nabla_tensor (conn fixed) and conn_var_tensor (T fixed).

    Smoothness hypotheses distinguish the three kinds of scalar families
    appearing in the evaluation:
    * `hT` / `hXT` are the direct slice and its spatial derivative,
    * `h_conn_smooth_v` / `h_conn_smooth_c` are the connection-dependent
      vector/covector slot families. -/
theorem t_nabla_eval
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time)
    (hT : ∀ vs αs, td.isSmoothFam (fun τ => T τ vs αs))
    (hXT : ∀ vs αs, td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)))
    (h_conn_smooth_v : ∀ i vs αs, td.isSmoothFam
      (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs))
    (h_conn_smooth_c : ∀ j vs αs, td.isSmoothFam
      (fun τ => T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))))
    (hT_nabla : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ) vs αs))
    (vs αs) :
    dt_tensor td t (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T τ))
      hT_nabla vs αs =
    (emb.embed X) (td.dt_apply (fun τ => T τ vs αs) t)
    - td.dt_apply (fun τ => ∑ i : Fin s,
        T τ (Function.update vs i (conn_fam τ X (vs i))) αs) t
    - td.dt_apply (fun τ => ∑ j : Fin r,
        T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) t := by
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
  have h_vec_sum : (fun τ => ∑ i : Fin s,
      T τ (Function.update vs i (conn_fam τ X (vs i))) αs) =
      ∑ i : Fin s, (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs) := by
    funext τ; simp [Finset.sum_apply]
  have h_cov_sum : (fun τ => ∑ j : Fin r,
      T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) =
      ∑ j : Fin r, (fun τ => T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    funext τ; simp [Finset.sum_apply]
  -- Smoothness of the three pieces
  have hS_X : td.isSmoothFam (fun τ => (emb.embed X) (T τ vs αs)) := hXT vs αs
  have hS_vec_sum : td.isSmoothFam
      (fun τ => ∑ i : Fin s, T τ (Function.update vs i (conn_fam τ X (vs i))) αs) := by
    rw [h_vec_sum]
    exact td.isSmoothFam_sum Finset.univ _ (fun i _ => h_conn_smooth_v i vs αs)
  have hS_cov_sum : td.isSmoothFam
      (fun τ => ∑ j : Fin r, T τ vs (Function.update αs j
        (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) := by
    rw [h_cov_sum]
    exact td.isSmoothFam_sum Finset.univ _ (fun j _ => h_conn_smooth_c j vs αs)
  rw [h_eq,
      td.dt_apply_sub _ _ _ (td.isSmoothFam_sub _ _ hS_X hS_vec_sum) hS_cov_sum,
      td.dt_apply_sub _ _ _ hS_X hS_vec_sum]
  -- Leading term: SpatialTemporalComm (requires smoothness of `fun τ => T τ vs αs`)
  rw [h_st X (fun τ => T τ vs αs) t (hT vs αs)]

/-- conn_var_tensor is additive in T. -/
theorem conn_var_tensor_add
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (T₁ T₂ : TensorData R V r s)
    (h₁ : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₁ vs αs))
    (h₂ : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₂ vs αs))
    (h₁₂ : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T₁ + T₂) vs αs)) :
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X (T₁ + T₂) h₁₂ =
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X T₁ h₁ +
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X T₂ h₂ := by
  simp only [conn_var_tensor]
  -- Goal: dt_tensor td t (fun τ => nabla X (T₁ + T₂)) h₁₂ = dt_tensor h₁ + dt_tensor h₂
  have h : (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T₁ + T₂)) =
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₁ +
                nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₂) := by
    funext τ; exact nabla_add emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₁ T₂
  -- Rewrite the argument to dt_tensor; must also rewrite the companion hypothesis.
  -- We argue pointwise instead, which avoids complicated dependent rewriting.
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.add_apply]
  have h_fun : (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T₁ + T₂) vs αs)
      = (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₁ vs αs)
        + (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₂ vs αs) := by
    funext τ
    change nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (T₁ + T₂) vs αs =
        nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₁ vs αs +
        nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₂ vs αs
    rw [nabla_add emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T₁ T₂]
    simp [MultilinearMap.add_apply]
  rw [h_fun, td.dt_apply_add _ _ _ (h₁ vs αs) (h₂ vs αs)]

/-- conn_var_tensor commutes with constant R-scalar multiplication. -/
theorem conn_var_tensor_smul
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (t : Time) (X : V) {r s : ℕ} (c : R) (T : TensorData R V r s)
    (hT_nabla : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T vs αs))
    (h_cT_nabla : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (c • T) vs αs)) :
    conn_var_tensor emb td conn_fam ha_fam hl_fam t X (c • T) h_cT_nabla =
    c • conn_var_tensor emb td conn_fam ha_fam hl_fam t X T hT_nabla := by
  simp only [conn_var_tensor]
  -- Again argue pointwise.
  ext vs αs
  simp only [dt_tensor_eval, MultilinearMap.smul_apply, smul_eq_mul]
  have h_fun :
      (fun τ => nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (c • T) vs αs) =
      (fun _ => (emb.embed X) c * T vs αs) +
      (fun τ => c * nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T vs αs) := by
    funext τ
    change nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (c • T) vs αs =
      (emb.embed X) c * T vs αs + c * nabla_tensor emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X T vs αs
    exact nabla_smul emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X c T vs αs
  rw [h_fun,
      td.dt_apply_add _ _ _
        (td.isSmoothFam_const ((emb.embed X) c * T vs αs))
        (td.isSmoothFam_const_mul c _ (hT_nabla vs αs)),
      td.dt_apply_const, zero_add,
      td.dt_apply_const_mul c _ t (hT_nabla vs αs)]

end VaryingConnT

-- ============================================================
-- Deferred item 1: t_linear_map
-- ∂_t(ω(F(s))) = dt_tensor evaluation at vectorToData(F(s))
-- ============================================================

section TLinearMap

variable {R V : Type*} {A Time : Type*}
variable [CommRing R] [AddCommGroup V] [Module R V]
variable [CommRing A] [Algebra R A]

/-- ∂_t(ω(F(s))) equals the evaluation of dt_tensor on vectorToData(F(s)) at covector ω.
    This is the canonical way to express "∂_t commutes with constant covectors"
    in the transparent tensor framework. Proof by rfl. -/
theorem t_linear_map (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time)
    (ω : V →ₗ[R] R) (F : Time → V)
    (hVF : ∀ vs αs, td.isSmoothFam
      (fun τ => vectorToData (R := R) (F τ) vs αs)) :
    td.dt_apply (fun s => ω (F s)) t =
    dt_tensor td t (fun s => vectorToData (R := R) (F s)) hVF ![] ![ω] :=
  rfl

end TLinearMap

-- ============================================================
-- Deferred item 2: t_conn_apply
-- ∂_t commutes with ∇_X on vectors (fixed connection).
-- The vector-level specialization of t_nabla_tensor.
-- ============================================================

section TConnApply

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- For a FIXED connection, ∂_t commutes with ∇_X on vectors:
    ∂_t[vectorToData(conn X (F τ))] = ∇_X(∂_t[vectorToData(F τ)]).
    Derived from t_nabla_tensor applied to T(τ) = vectorToData(F(τ)),
    using nabla_vector to identify ∇_X(vectorToData v) = vectorToData(conn X v). -/
theorem t_conn_apply
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (h_st : SpatialTemporalComm emb td)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (F : Time → V) (t : Time)
    (hVF : ∀ vs αs, td.isSmoothFam
      (fun τ => vectorToData (R := R) (F τ) vs αs))
    (hXVF : ∀ vs αs, td.isSmoothFam
      (fun τ => (emb.embed X) (vectorToData (R := R) (F τ) vs αs)))
    (hVcF : ∀ vs αs, td.isSmoothFam
      (fun τ => vectorToData (R := R) (conn X (F τ)) vs αs))
    (hN_VF : ∀ vs αs, td.isSmoothFam
      (fun τ => nabla_tensor emb conn ha hl X (vectorToData (R := R) (F τ)) vs αs)) :
    dt_tensor td t (fun τ => vectorToData (R := R) (conn X (F τ))) hVcF =
    nabla_tensor emb conn ha hl X
      (dt_tensor td t (fun τ => vectorToData (R := R) (F τ)) hVF) := by
  -- Step 1: Rewrite LHS using nabla_vector in reverse
  have h_eq : (fun τ => vectorToData (R := R) (conn X (F τ))) =
      (fun τ => nabla_tensor emb conn ha hl X (vectorToData (R := R) (F τ))) := by
    funext τ; exact (nabla_vector emb conn ha hl X (F τ)).symm
  -- We cannot `rw [h_eq]` because the smoothness hypothesis also depends on the
  -- function. Instead argue pointwise via dt_tensor_eval.
  ext vs αs
  simp only [dt_tensor_eval]
  have h_scalar : (fun τ => vectorToData (R := R) (conn X (F τ)) vs αs) =
      (fun τ => nabla_tensor emb conn ha hl X (vectorToData (R := R) (F τ)) vs αs) := by
    funext τ
    have := nabla_vector emb conn ha hl X (F τ)
    -- `nabla_vector` says vectorToData(conn X v) = nabla_tensor X (vectorToData v)
    rw [this]
  rw [h_scalar]
  -- Now the goal is the scalar form of t_nabla_tensor.
  have h_eq_lambda : (fun τ => nabla_tensor emb conn ha hl X
      (vectorToData (R := R) (F τ))) =
      (fun τ => nabla_tensor emb conn ha hl X (vectorToData (R := R) (F τ))) := rfl
  have h_tens := t_nabla_tensor emb td h_st conn ha hl X
    (fun τ => vectorToData (R := R) (F τ)) t hVF hXVF hN_VF
  -- h_tens : dt_tensor td t (fun τ => nabla X (vectorToData F τ)) hN_VF =
  --         nabla X (dt_tensor td t (fun τ => vectorToData F τ) hVF)
  have h_eval := congr_arg (fun (D : TensorData R V 1 0) => D vs αs) h_tens
  simpa [dt_tensor_eval] using h_eval

end TConnApply

-- ============================================================
-- Per-slot Leibniz helpers for NablaTimeProductRule
-- ============================================================

section SlotLeibniz

variable {k R V : Type*} {A Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
variable [CommRing A] [Algebra R A]

/-- Vector-slot Leibniz: given a 2-smooth family in the diagonal pairs
    `(τ, τ)` obtained by substituting a connection-varying vector into the
    `i`-th vector slot of a time-dependent tensor `T τ`, the diagonal time
    derivative splits into the sum of the two single-slot time derivatives
    via `TimeRegularFam2.dt_apply_diag_leibniz`. This is the exact form
    consumed by `concrete_nabla_time_product_rule` when unfolding the
    product rule on a vector slot. -/
theorem TimeDerivativeData.dt_apply_leibniz_slot_vector
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] [TimeRegularFam2 td]
    (conn_fam : Time → V → V → V)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time) (i : Fin s)
    (vs : Fin s → V) (αs : Fin r → V →ₗ[R] R)
    (h_2smooth : TimeRegularFam2.isSmoothFam2 (td := td)
      (fun p : Time × Time =>
        T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs)) :
    td.dt_apply
        (fun τ => T τ (Function.update vs i (conn_fam τ X (vs i))) αs) t
      = td.dt_apply
          (fun τ => T t (Function.update vs i (conn_fam τ X (vs i))) αs) t
        + td.dt_apply
            (fun τ => T τ (Function.update vs i (conn_fam t X (vs i))) αs) t := by
  have h := TimeRegularFam2.dt_apply_diag_leibniz
    (td := td)
    (fun p : Time × Time => T p.1 (Function.update vs i (conn_fam p.2 X (vs i))) αs)
    t h_2smooth
  simp only at h
  rw [add_comm]; exact h

/-- Covector-slot Leibniz: given a 2-smooth family in the diagonal pairs
    `(τ, τ)` obtained by substituting a `nabla_dual`-varying covector into
    the `j`-th covector slot of a time-dependent tensor `T τ`, the diagonal
    time derivative splits into the sum of the two single-slot time
    derivatives via `TimeRegularFam2.dt_apply_diag_leibniz`. This is the
    exact form consumed by `concrete_nabla_time_product_rule` when
    unfolding the product rule on a covector slot. -/
theorem TimeDerivativeData.dt_apply_leibniz_slot_covector
    (emb : DerivationEmbedding k R V)
    (td : TimeDerivativeData R A Time) [TimeRegularFam td] [TimeRegularFam2 td]
    (conn_fam : Time → V → V → V)
    (ha_fam : ∀ τ, ∀ X Y Z, conn_fam τ X (Y + Z) = conn_fam τ X Y + conn_fam τ X Z)
    (hl_fam : ∀ τ, ∀ X (f : R) Y,
      conn_fam τ X (f • Y) = (emb.embed X) f • Y + f • conn_fam τ X Y)
    (X : V) {r s : ℕ} (T : Time → TensorData R V r s) (t : Time) (j : Fin r)
    (vs : Fin s → V) (αs : Fin r → V →ₗ[R] R)
    (h_2smooth : TimeRegularFam2.isSmoothFam2 (td := td)
      (fun p : Time × Time =>
        T p.1 vs (Function.update αs j
          (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j))))) :
    td.dt_apply
        (fun τ => T τ vs (Function.update αs j
          (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) t
      = td.dt_apply
          (fun τ => T t vs (Function.update αs j
            (nabla_dual emb (conn_fam τ) (ha_fam τ) (hl_fam τ) X (αs j)))) t
        + td.dt_apply
            (fun τ => T τ vs (Function.update αs j
              (nabla_dual emb (conn_fam t) (ha_fam t) (hl_fam t) X (αs j)))) t := by
  have h := TimeRegularFam2.dt_apply_diag_leibniz
    (td := td)
    (fun p : Time × Time => T p.1 vs (Function.update αs j
      (nabla_dual emb (conn_fam p.2) (ha_fam p.2) (hl_fam p.2) X (αs j))))
    t h_2smooth
  simp only at h
  rw [add_comm]; exact h

end SlotLeibniz
