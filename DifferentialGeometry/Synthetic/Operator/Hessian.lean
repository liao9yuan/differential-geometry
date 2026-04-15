import DifferentialGeometry.Synthetic.Operator.Gradient
import DifferentialGeometry.Synthetic.Operator.CovariantDerivative
import DifferentialGeometry.Synthetic.Geometry.Connection
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Hessian Operator
-/

open SyntheticTensor

section Hessian

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Hessian of a function: `∇²u(X, Y) = X(Y(u)) - (∇_X Y)(u)`. -/
def Hess (emb : DerivationEmbedding k R V) (conn : V → V → V) (u : R) (X Y : V) : R :=
  action emb X (action emb Y u) - action emb (conn X Y) u

theorem hessian_symm
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (h_tf : IsTorsionFree emb conn) (u : R) (X Y : V) :
    Hess emb conn u X Y = Hess emb conn u Y X := by
  have t1 : conn X Y = conn Y X + bracket emb X Y := by
    have h := h_tf X Y
    calc conn X Y = conn X Y - conn Y X + conn Y X := by abel
      _ = bracket emb X Y + conn Y X := by rw [h]
      _ = conn Y X + bracket emb X Y := by abel
  calc Hess emb conn u X Y
    _ = action emb X (action emb Y u) - action emb (conn X Y) u := rfl
    _ = action emb X (action emb Y u) - action emb (conn Y X + bracket emb X Y) u := by rw [t1]
    _ = action emb X (action emb Y u) - (action emb (conn Y X) u + action emb (bracket emb X Y) u) := by rw [action_add_left]
    _ = action emb X (action emb Y u) - (action emb (conn Y X) u + (action emb X (action emb Y u) - action emb Y (action emb X u))) := by rw [action_bracket]
    _ = action emb Y (action emb X u) - action emb (conn Y X) u := by ring
    _ = Hess emb conn u Y X := rfl

/-- Rigorous `(1,1)` tensor representing the covariant differential `∇Z`. -/
noncomputable def covariant_differential
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (Z : V) : TensorData R V 1 1 where
  toFun m :=
    (nabla_tensor emb conn ha hl (m 0) (vectorToData Z)) ![]
  map_update_add' m i X1 X2 := by
    have hz : i = 0 := Subsingleton.elim _ _; subst hz
    simp only [Fin.isValue, Function.update_self]
    ext n; simp only [MultilinearMap.add_apply]
    exact nabla_add_left emb conn ha conn_add_left hl X1 X2 (vectorToData Z) ![] n
  map_update_smul' m i c X := by
    have hz : i = 0 := Subsingleton.elim _ _; subst hz
    simp only [Fin.isValue, Function.update_self]
    ext n; simp only [MultilinearMap.smul_apply, smul_eq_mul]
    exact nabla_smul_left emb conn ha conn_smul_left hl c X (vectorToData Z) ![] n

/-- covariant_differential is additive in Z. -/
lemma covariant_differential_add_vec
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (Z1 Z2 : V) :
    covariant_differential emb conn ha hl conn_add_left conn_smul_left (Z1 + Z2) =
    covariant_differential emb conn ha hl conn_add_left conn_smul_left Z1 +
    covariant_differential emb conn ha hl conn_add_left conn_smul_left Z2 := by
  ext m n; simp only [covariant_differential, MultilinearMap.coe_mk, MultilinearMap.add_apply]
  rw [vectorToData_add, nabla_add emb conn ha hl (m 0)]
  simp [MultilinearMap.add_apply]

/-- covariant_differential respects scalar multiplication for spatial constant c. -/
lemma covariant_differential_smul_vec
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (c : R) (Z : V) (hc : ∀ X : V, action emb X c = 0) :
    covariant_differential emb conn ha hl conn_add_left conn_smul_left (c • Z) =
    c • covariant_differential emb conn ha hl conn_add_left conn_smul_left Z := by
  ext m n; simp only [covariant_differential, MultilinearMap.coe_mk,
    MultilinearMap.smul_apply, smul_eq_mul]
  rw [vectorToData_smul]
  have h := nabla_smul emb conn ha hl (m 0) c (vectorToData Z) ![] n
  unfold action at hc; rw [h, hc (m 0), zero_mul, zero_add]

/-- Hessian form: the (0,2)-tensor obtained by lowering the index of ∇(grad u). -/
noncomputable def hessianForm
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (u : R) : TensorData R V 0 2 :=
  lower_index met atr (0 : Fin 1)
    (covariant_differential emb conn ha hl conn_add_left conn_smul_left (grad emb met u))

-- ============================================================
-- lower_index linearity helpers
-- ============================================================

-- Helper: Eq.mpr transport distributes over addition for TensorData
private lemma mpr_add_td {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {r₁ r₂ s₁ s₂ : ℕ} (hr : r₁ = r₂) (hs : s₁ = s₂)
    (A B : TensorData R V r₁ s₁) :
    (hr ▸ hs ▸ (A + B) : TensorData R V r₂ s₂) =
    (hr ▸ hs ▸ A) + (hr ▸ hs ▸ B) := by
  subst hr; subst hs; rfl

-- Helper: Eq.mpr transport distributes over scalar mult for TensorData
private lemma mpr_smul_td {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {r₁ r₂ s₁ s₂ : ℕ} (hr : r₁ = r₂) (hs : s₁ = s₂)
    (c : R) (A : TensorData R V r₁ s₁) :
    (hr ▸ hs ▸ (c • A) : TensorData R V r₂ s₂) =
    c • (hr ▸ hs ▸ A) := by
  subst hr; subst hs; rfl

private lemma lower_index_add
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx : Fin (r + 1))
    (T₁ T₂ : TensorData R V (r + 1) s) :
    lower_index met atr idx (T₁ + T₂) =
    lower_index met atr idx T₁ + lower_index met atr idx T₂ := by
  simp only [lower_index]
  have h_tp : tensor_prod (r₁ := 0) (s₁ := 2) (r₂ := r + 1) (s₂ := s)
      met.g_tensor (T₁ + T₂) =
      tensor_prod met.g_tensor T₁ + tensor_prod met.g_tensor T₂ := by
    ext vs αs; simp [tensor_prod_eval, MultilinearMap.add_apply, mul_add]
  rw [h_tp, mpr_add_td, contract_general_add]

private lemma lower_index_smul
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx : Fin (r + 1))
    (c : R) (T : TensorData R V (r + 1) s) :
    lower_index met atr idx (c • T) =
    c • lower_index met atr idx T := by
  simp only [lower_index]
  have h_tp : tensor_prod (r₁ := 0) (s₁ := 2) (r₂ := r + 1) (s₂ := s)
      met.g_tensor (c • T) = c • tensor_prod met.g_tensor T := by
    ext vs αs; simp [tensor_prod_eval, MultilinearMap.smul_apply, smul_eq_mul, mul_left_comm]
  rw [h_tp, mpr_smul_td, contract_general_smul]

/-- hessianForm is additive. -/
lemma hessianForm_add
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (f g : R) :
    hessianForm emb met atr conn ha hl conn_add_left conn_smul_left (f + g) =
    hessianForm emb met atr conn ha hl conn_add_left conn_smul_left f +
    hessianForm emb met atr conn ha hl conn_add_left conn_smul_left g := by
  unfold hessianForm
  rw [grad_add, covariant_differential_add_vec, lower_index_add]

/-- grad(c*f) = c • grad(f) for spatial constant c (stated locally). -/
private lemma grad_smul_const_local
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    
    (c f : R) (hc : ∀ X : V, action emb X c = 0) :
    grad emb met (c * f) = c • grad emb met f := by
  apply met.eq_of_forall_g_eq; intro Z
  change met.g (grad emb met (c * f)) Z = met.g (c • grad emb met f) Z
  rw [g_grad, met.g_smul_left, g_grad, action_smul_right, hc Z, zero_mul, zero_add]

/-- hessianForm respects constant scalar multiplication. -/
lemma hessianForm_smul
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (c f : R) (hc : ∀ X : V, action emb X c = 0) :
    hessianForm emb met atr conn ha hl conn_add_left conn_smul_left (c * f) =
    c • hessianForm emb met atr conn ha hl conn_add_left conn_smul_left f := by
  unfold hessianForm
  rw [grad_smul_const_local emb met c f hc,
      covariant_differential_smul_vec emb conn ha hl conn_add_left conn_smul_left c _ hc,
      lower_index_smul]

/-- Evaluating hessianForm at vectors (X, Y) equals Hess u X Y.

    Uses `lower_index_eval_11` to evaluate the index-lowering contraction. -/
theorem hessianForm_eval
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn)
    (u : R) (X Y : V) :
    hessianForm emb met atr conn ha hl conn_add_left conn_smul_left u ![X, Y] ![] =
    Hess emb conn u X Y := by
  -- Step 1: Unfold hessianForm and apply lower_index_eval_11
  unfold hessianForm
  rw [lower_index_eval_11]
  -- Goal: covariant_differential ... (grad u) ![Y] ![met.flat X] = Hess u X Y
  -- Step 2: Evaluate covariant_differential
  simp only [covariant_differential, MultilinearMap.coe_mk]
  -- Goal involves: (nabla_tensor ... (![Y] 0) (vectorToData (grad u))) ![] ![met.flat X]
  -- Normalize ![Y] 0 to Y, then apply nabla_vector
  change (nabla_tensor emb conn ha hl Y (vectorToData (grad emb met u))) ![]
    ![met.flat X] = Hess emb conn u X Y
  rw [nabla_vector emb conn ha hl Y (grad emb met u)]
  -- Goal: vectorToData (conn Y (grad u)) ![] ![met.flat X] = Hess u X Y
  -- vectorToData v ![] ![α] = α v
  simp only [vectorToData, MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton,
    evalLinear]
  -- Goal: met.flat X (conn Y (grad u)) = Hess u X Y
  -- met.flat X (conn Y (grad u)) = met.g X (conn Y (grad u))
  change met.g X (conn Y (grad emb met u)) = Hess emb conn u X Y
  -- Step 3: Use metric compatibility
  -- h_mc Y X (grad u): Y(g(X, grad u)) = g(conn Y X, grad u) + g(X, conn Y (grad u))
  have h_compat := h_mc Y X (grad emb met u)
  -- g(X, grad u) = X(u) by definition of grad
  have h_gX : met.g X (grad emb met u) = action emb X u := by
    rw [met.g_symm]; exact g_grad emb met u X
  have h_gnY : met.g (conn Y X) (grad emb met u) = action emb (conn Y X) u := by
    rw [met.g_symm]; exact g_grad emb met u (conn Y X)
  rw [h_gX, h_gnY] at h_compat
  -- h_compat: Y(X(u)) = (conn Y X)(u) + g(X, conn Y (grad u))
  -- So g(X, conn Y (grad u)) = Y(X(u)) - (conn Y X)(u) = Hess u Y X
  -- From h_compat: Y(X(u)) = (conn Y X)(u) + g(X, conn Y (grad u))
  -- So g(X, conn Y (grad u)) = Y(X(u)) - (conn Y X)(u) = Hess u Y X
  have h3 : met.g X (conn Y (grad emb met u)) = Hess emb conn u Y X := by
    change met.g X (conn Y (grad emb met u)) =
      action emb Y (action emb X u) - action emb (conn Y X) u
    have h := h_compat; rw [add_comm] at h; exact (sub_eq_of_eq_add h).symm
  rw [h3]; exact hessian_symm emb conn h_tf u Y X

/-- grad(c * f) = c • grad(f) for c in algebraMap k R (base field constants). -/
theorem grad_smul_algebraMap
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    
    (c : k) (f : R) :
    grad emb met (algebraMap k R c * f) = algebraMap k R c • grad emb met f := by
  apply met.eq_of_forall_g_eq; intro Z
  change met.g (grad emb met (algebraMap k R c * f)) Z =
       met.g (algebraMap k R c • grad emb met f) Z
  rw [g_grad, met.g_smul_left, g_grad, action_mul_algebraMap emb Z c f]

end Hessian
