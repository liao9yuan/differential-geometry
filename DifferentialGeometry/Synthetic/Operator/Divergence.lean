import DifferentialGeometry.Synthetic.Operator.Hessian
import DifferentialGeometry.Synthetic.Operator.CovariantDerivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Divergence Operator
Algebraic definition of the divergence of a vector field.
-/

open SyntheticTensor

section DivergenceDefs

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Covariant differential of a vector field Z, as a (1,1)-tensor.
    This is just an alias for covariant_differential from Hessian.lean. -/
noncomputable def cov_diff_vec
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (Z : V) : TensorData R V 1 1 :=
  covariant_differential emb conn ha hl conn_add_left conn_smul_left Z

/-- Divergence defined as the metric trace of the lowered covariant differential. -/
noncomputable def divergence
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (X : V) : R :=
  (metric_trace met atr (0 : Fin 2) (0 : Fin 1)
    (lower_index met atr (0 : Fin 1)
      (cov_diff_vec emb conn ha hl conn_add_left conn_smul_left X))) ![] ![]

-- ============================================================
-- Leibniz rule for covariant differential under scalar multiplication
-- ============================================================

/-- The covariant differential of f • Z decomposes via Leibniz:
    (∇_W (f • Z))(α) = W(f) · α(Z) + f · (∇_W Z)(α). -/
lemma covariant_differential_smul_leibniz
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (f : R) (Z W : V) (α : V →ₗ[R] R) :
    (covariant_differential emb conn ha hl conn_add_left conn_smul_left (f • Z)) ![W] ![α] =
    action emb W f * α Z +
    f * (covariant_differential emb conn ha hl conn_add_left conn_smul_left Z) ![W] ![α] := by
  simp only [covariant_differential, MultilinearMap.coe_mk]
  change (nabla_tensor emb conn ha hl W (vectorToData (f • Z))) ![] ![α] = _
  rw [vectorToData_smul]
  exact nabla_smul emb conn ha hl W f (vectorToData Z) ![] ![α]

-- ============================================================
-- Divergence Leibniz rule
-- ============================================================

/-- Helper: the connection endomorphism W ↦ conn W X as a linear map. -/
def conn_endo
    (conn : V → V → V)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (X : V) : V →ₗ[R] V where
  toFun W := conn W X
  map_add' W₁ W₂ := conn_add_left W₁ W₂ X
  map_smul' c W := by simp only [RingHom.id_apply]; exact conn_smul_left c W X

-- ============================================================
-- divergence = tr(conn_endo)
-- ============================================================

/-- The covariant differential of X equals the (1,1)-tensor of conn_endo X. -/
lemma cov_diff_vec_eq_endo
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (X : V) :
    cov_diff_vec emb conn ha hl conn_add_left conn_smul_left X =
    endo_to_tensor (conn_endo conn conn_add_left conn_smul_left X) := by
  ext m n
  simp only [cov_diff_vec, covariant_differential, MultilinearMap.coe_mk]
  have h := nabla_vector emb conn ha hl (m 0) X
  have h2 : (nabla_tensor emb conn ha hl (m 0) (vectorToData X)) ![] n =
      (vectorToData (R := R) (conn (m 0) X)) ![] n := by
    rw [h]
  rw [h2]
  rfl

/-- Auxiliary: the inner swap in raise_index produces a commuted tensor product. -/
private lemma swap_tensor_prod_comm {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (met : MetricDuality R V) (S : TensorData R V 0 2)
    (m' : Fin 2 → V) (n' : Fin 2 → (V →ₗ[R] R)) :
    (swap_covariant (0 : Fin 2) (0 : Fin 2)
      (swap_contravariant (0 : Fin 2) ⟨1, by omega⟩
        (tensor_prod (r₁ := 2) (s₁ := 0) (r₂ := 0) (s₂ := 2) met.g_inv S))) m' n' =
    (tensor_prod (r₁ := 0) (s₁ := 2) (r₂ := 2) (s₂ := 0)
      S (swap_contravariant (0 : Fin 2) 1 met.g_inv)) m' n' := by
  change (tensor_prod met.g_inv S) (m' ∘ Equiv.swap (0 : Fin 2) 0)
      (n' ∘ Equiv.swap (0 : Fin 2) ⟨1, by omega⟩) =
    (tensor_prod S (swap_contravariant (0 : Fin 2) 1 met.g_inv)) m' n'
  simp only [Equiv.swap_self]
  rw [tensor_prod_eval, tensor_prod_eval, swap_contravariant_eval]
  -- Simplify castAdd/natAdd on Fin 0 (empty) and Fin 2 (identity-like)
  have hg1_l : (m' ∘ ⇑(Equiv.refl (Fin 2))) ∘ Fin.castAdd 2 = (fun i : Fin 0 => i.elim0) := by
    ext i; exact i.elim0
  have hg1_r : m' ∘ Fin.natAdd 2 = (fun i : Fin 0 => i.elim0) := by
    ext i; exact i.elim0
  have hg2_l : (n' ∘ ⇑(Equiv.swap (0 : Fin 2) ⟨1, by omega⟩)) ∘ Fin.castAdd 0 =
      n' ∘ Equiv.swap (0 : Fin 2) 1 := by
    ext i; simp [Function.comp, Fin.castAdd]
  have hg2_r : (n' ∘ Fin.natAdd 0) ∘ ⇑(Equiv.swap (0 : Fin 2) 1) =
      n' ∘ Equiv.swap (0 : Fin 2) 1 := by
    ext i; simp [Function.comp, Fin.natAdd]
  have hs1_l : (m' ∘ ⇑(Equiv.refl (Fin 2))) ∘ Fin.natAdd 0 = m' := by
    ext i; simp [Function.comp, Fin.natAdd]
  have hs1_r : m' ∘ Fin.castAdd 0 = m' := by
    ext i; simp [Function.comp, Fin.castAdd]
  have hs2_l : (n' ∘ ⇑(Equiv.swap (0 : Fin 2) ⟨1, by omega⟩)) ∘ Fin.natAdd 2 =
      (fun i : Fin 0 => i.elim0) := by
    ext i; exact i.elim0
  have hs2_r : n' ∘ Fin.castAdd 2 = (fun i : Fin 0 => i.elim0) := by
    ext i; exact i.elim0
  rw [hg1_l, hg2_l, hs1_l, hs2_l, hg1_r, hg2_r, hs1_r, hs2_r]
  exact mul_comm _ _

/-- raise_index ∘ lower_index = id for (1,1)-tensors.
    Uses the dual evaluation axiom and metric inverse. -/
lemma raise_lower_id_11 (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 1 1) :
    raise_index met atr (0 : Fin 2) (lower_index met atr (0 : Fin 1) T) = T := by
  set S := lower_index met atr (0 : Fin 1) T
  have key : ∀ (W : V) (α : V →ₗ[R] R),
      (raise_index met atr (0 : Fin 2) S) ![W] ![α] = T ![W] ![α] := by
    intro W α
    obtain ⟨v, hv⟩ := met.sharp_spec α
    have hα : α = met.flat v := by
      ext Z; simp only [MetricDuality.flat, flat_covector_apply]; exact (hv Z).symm
    subst hα
    -- Unfold raise_index and contract_general
    simp only [raise_index, contract_general]
    -- Rewrite the swapped product as tensor_prod S (swap_contra 0 1 g_inv)
    have h_inner := fun m' n' => swap_tensor_prod_comm met S m' n'
    have h_ext : swap_covariant (0 : Fin 2) (0 : Fin 2)
        (swap_contravariant (0 : Fin 2) ⟨1, by omega⟩
          (tensor_prod (r₁ := 2) (s₁ := 0) (r₂ := 0) (s₂ := 2) met.g_inv S)) =
      tensor_prod (r₁ := 0) (s₁ := 2) (r₂ := 2) (s₂ := 0)
        S (swap_contravariant (0 : Fin 2) 1 met.g_inv) := by
      ext m' n'; exact h_inner m' n'
    rw [h_ext]
    -- Apply data_eval_single_contract_dual
    rw [atr.data_eval_single_contract_dual S
      (swap_contravariant (0 : Fin 2) 1 met.g_inv) ![W] ![met.flat v]]
    -- Simplify index functions: natAdd 1 on Fin 0 is empty, castAdd 0 on Fin 1 is id
    have hnatAdd : (![W] : Fin 1 → V) ∘ Fin.natAdd 1 = (fun i : Fin 0 => i.elim0) := by
      ext i; exact i.elim0
    have hcastAdd : (![W] : Fin 1 → V) ∘ Fin.castAdd 0 = ![W] := by
      ext i; fin_cases i; rfl
    simp only [hnatAdd, hcastAdd]
    -- Simplify Fin.cons
    have hcons : Fin.cons (covector_from_tensor S ![W] ![]) (![met.flat v] : Fin 1 → (V →ₗ[R] R)) =
        ![covector_from_tensor S ![W] ![], met.flat v] := by
      ext i; fin_cases i <;> rfl
    rw [hcons]
    -- Evaluate swap_contravariant on g_inv: swaps the dual (contra) slots
    -- (swap_contra 0 1 g_inv) ![] ![cov, flat v] = g_inv ![] (![cov, flat v] ∘ swap 0 1)
    simp only [swap_contravariant_eval]
    have hswap_n : (![covector_from_tensor S ![W] ![], met.flat v] : Fin 2 → (V →ₗ[R] R)) ∘
        Equiv.swap (0 : Fin 2) 1 = ![met.flat v, covector_from_tensor S ![W] ![]] := by
      ext i; fin_cases i <;> rfl
    rw [hswap_n]
    -- Goal: g_inv ![] ![met.flat v, covector_from_tensor S ![W] ![]] = T ![W] ![met.flat v]
    -- Use sharp_spec on covector_from_tensor S ![W] ![] to write it as met.flat u
    obtain ⟨u, hu⟩ := met.sharp_spec (covector_from_tensor S ![W] ![])
    have hcov_eq : covector_from_tensor S ![W] ![] = met.flat u := by
      ext Z; simp only [MetricDuality.flat, flat_covector_apply]; exact (hu Z).symm
    rw [hcov_eq]
    -- Normalize the empty function to ![] and use inverse_eval'
    change met.g_inv ![] ![met.flat v, met.flat u] = T ![W] ![met.flat v]
    rw [met.inverse_eval' u (met.flat v)]
    -- Goal: met.flat v u = T ![W] ![met.flat v]
    change met.g v u = T ![W] ![met.flat v]
    rw [met.g_symm v u]
    change met.flat u v = T ![W] ![met.flat v]
    rw [← hcov_eq]
    -- Goal: covector_from_tensor S ![W] ![] v = T ![W] ![met.flat v]
    -- covector_from_tensor maps w ↦ S (Fin.cons w m) n, so this is S ![v, W] ![]
    change S (Fin.cons v ![W]) ![] = T ![W] ![met.flat v]
    have hcons2 : Fin.cons v (![W] : Fin 1 → V) = (![v, W] : Fin 2 → V) := by
      ext i; fin_cases i <;> rfl
    rw [hcons2]
    exact lower_index_eval_11 met atr T v W
  -- Conclude: ext equality from pointwise equality
  ext m n
  have hm : m = ![m 0] := by ext i; fin_cases i; rfl
  have hn : n = ![n 0] := by ext i; fin_cases i; rfl
  rw [hm, hn]
  exact key (m 0) (n 0)

/-- Metric-based divergence equals trace of connection endomorphism. -/
theorem divergence_eq_tr_conn_endo
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (X : V) :
    divergence emb met atr conn ha hl conn_add_left conn_smul_left X =
    atr.tr (conn_endo conn conn_add_left conn_smul_left X) := by
  unfold divergence metric_trace
  rw [contract_general_0_0]
  rw [raise_lower_id_11 met atr (cov_diff_vec emb conn ha hl conn_add_left conn_smul_left X)]
  rw [cov_diff_vec_eq_endo]
  exact atr.tensor_contract_endo (conn_endo conn conn_add_left conn_smul_left X)

/-- Divergence Leibniz rule: div(f · X) = f · div(X) + X(f). -/
theorem divergence_smul
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (f : R) (X : V) :
    divergence emb met atr conn ha hl conn_add_left conn_smul_left (f • X) =
    f * divergence emb met atr conn ha hl conn_add_left conn_smul_left X +
    action emb X f := by
  rw [divergence_eq_tr_conn_endo emb met atr conn ha hl conn_add_left conn_smul_left (f • X),
      divergence_eq_tr_conn_endo emb met atr conn ha hl conn_add_left conn_smul_left X]
  have h_endo : conn_endo conn conn_add_left conn_smul_left (f • X) =
      (df_covector emb f).smulRight X + f • conn_endo conn conn_add_left conn_smul_left X := by
    ext W
    simp only [conn_endo, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      LinearMap.smulRight_apply, df_covector, LinearMap.smul_apply]
    change conn W (f • X) = action emb W f • X + f • conn W X
    exact hl W f X
  rw [h_endo, map_add, map_smul]
  simp only [atr.trace_outer X (df_covector emb f), smul_eq_mul]
  exact add_comm _ _

end DivergenceDefs

-- ============================================================
-- Integration and Divergence Theorem
-- ============================================================

section Integration

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Abstract global integration operator. Structure (not class). -/
structure IntegralOperator (R : Type*) [CommRing R] where
  integral : R → R
  integral_add : ∀ f g : R, integral (f + g) = integral f + integral g
  integral_smul : ∀ (c f : R), integral (c * f) = c * integral f

/-- The Divergence Theorem as a proposition: integral of divergence vanishes. -/
def DivergenceTheorem
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (I : IntegralOperator R) : Prop :=
  ∀ X : V, I.integral (divergence emb met atr conn ha hl conn_add_left conn_smul_left X) = 0

/-- Integration by parts (Green's first identity):
    integral(f * div X) + integral(X(f)) = 0.
    Follows from DivergenceTheorem + divergence_smul. -/
theorem integration_by_parts
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (I : IntegralOperator R)
    (h_dt : DivergenceTheorem emb met atr conn ha hl conn_add_left conn_smul_left I)
    (f : R) (X : V) :
    I.integral (f * divergence emb met atr conn ha hl conn_add_left conn_smul_left X) +
    I.integral (action emb X f) = 0 := by
  have h_div_smul := divergence_smul emb met atr conn ha hl conn_add_left conn_smul_left f X
  have h_zero : I.integral (divergence emb met atr conn ha hl conn_add_left conn_smul_left
    (f • X)) = 0 := h_dt (f • X)
  rw [h_div_smul, I.integral_add] at h_zero
  exact h_zero

end Integration
