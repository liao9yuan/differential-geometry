import DifferentialGeometry.Synthetic.Operator.Hessian
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Laplacian Operator
-/

open SyntheticTensor

section LaplacianHelpers

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

-- Eq.mpr transport helpers (same pattern as Hessian.lean)
private lemma mpr_add_td' {r₁ r₂ s₁ s₂ : ℕ} (hr : r₁ = r₂) (hs : s₁ = s₂)
    (A B : TensorData R V r₁ s₁) :
    (hr ▸ hs ▸ (A + B) : TensorData R V r₂ s₂) =
    (hr ▸ hs ▸ A) + (hr ▸ hs ▸ B) := by subst hr; subst hs; rfl

private lemma mpr_smul_td' {r₁ r₂ s₁ s₂ : ℕ} (hr : r₁ = r₂) (hs : s₁ = s₂)
    (c : R) (A : TensorData R V r₁ s₁) :
    (hr ▸ hs ▸ (c • A) : TensorData R V r₂ s₂) =
    c • (hr ▸ hs ▸ A) := by subst hr; subst hs; rfl

private lemma raise_index_add
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx : Fin (s + 1))
    (T₁ T₂ : TensorData R V r (s + 1)) :
    raise_index met atr idx (T₁ + T₂) =
    raise_index met atr idx T₁ + raise_index met atr idx T₂ := by
  simp only [raise_index]
  have h_tp : tensor_prod (r₁ := 2) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
      met.g_inv (T₁ + T₂) = tensor_prod met.g_inv T₁ + tensor_prod met.g_inv T₂ := by
    ext vs αs; simp [tensor_prod_eval, MultilinearMap.add_apply, mul_add]
  rw [h_tp, mpr_add_td', contract_general_add]

private lemma raise_index_smul
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx : Fin (s + 1))
    (c : R) (T : TensorData R V r (s + 1)) :
    raise_index met atr idx (c • T) =
    c • raise_index met atr idx T := by
  simp only [raise_index]
  have h_tp : tensor_prod (r₁ := 2) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
      met.g_inv (c • T) = c • tensor_prod met.g_inv T := by
    ext vs αs; simp [tensor_prod_eval, MultilinearMap.smul_apply, smul_eq_mul, mul_left_comm]
  rw [h_tp, mpr_smul_td', contract_general_smul]

private lemma metric_trace_add
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx₁ : Fin (s + 2)) (idx₂ : Fin (s + 1))
    (T₁ T₂ : TensorData R V r (s + 2)) :
    metric_trace met atr idx₁ idx₂ (T₁ + T₂) =
    metric_trace met atr idx₁ idx₂ T₁ + metric_trace met atr idx₁ idx₂ T₂ := by
  simp only [metric_trace, raise_index_add, contract_general_add]

private lemma metric_trace_smul
    (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx₁ : Fin (s + 2)) (idx₂ : Fin (s + 1))
    (c : R) (T : TensorData R V r (s + 2)) :
    metric_trace met atr idx₁ idx₂ (c • T) =
    c • metric_trace met atr idx₁ idx₂ T := by
  simp only [metric_trace, raise_index_smul, contract_general_smul]

end LaplacianHelpers

section Laplacian

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Laplacian of a function defined as the metric trace of its Hessian tensor form. -/
noncomputable def laplacian
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (u : R) : R :=
  (metric_trace met atr (0 : Fin 2) (0 : Fin 1)
    (hessianForm emb met atr conn ha hl conn_add_left conn_smul_left u)) ![] ![]

/-- Δ(f+g) = Δf + Δg -/
lemma laplacian_add
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (f g : R) :
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left (f + g) =
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left f +
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left g := by
  simp only [laplacian, hessianForm_add, metric_trace_add, MultilinearMap.add_apply]

/-- Δ(f-g) = Δf - Δg -/
lemma laplacian_sub
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (f g : R) :
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left (f - g) =
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left f -
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left g := by
  have hsub : f - g = f + (-1) * g := by ring
  rw [hsub, laplacian_add]
  have hc : ∀ X : V, action emb X (-1 : R) = 0 := by
    intro X; rw [show (-1 : R) = -1 from rfl, action_neg_right, action_one]; ring
  have hz : laplacian emb met atr conn ha hl conn_add_left conn_smul_left ((-1) * g) =
      (-1) * laplacian emb met atr conn ha hl conn_add_left conn_smul_left g := by
    simp only [laplacian, hessianForm_smul emb met atr conn ha hl conn_add_left conn_smul_left (-1) g hc,
               metric_trace_smul, MultilinearMap.smul_apply, smul_eq_mul]
  rw [hz]; ring

/-- Δ(c*f) = c * Δf for spatial constant c -/
lemma laplacian_smul
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V) 
    (atr : AbstractTrace R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (conn_add_left : ∀ X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : ∀ (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (c f : R) (hc : ∀ X : V, action emb X c = 0) :
    laplacian emb met atr conn ha hl conn_add_left conn_smul_left (c * f) =
    c * laplacian emb met atr conn ha hl conn_add_left conn_smul_left f := by
  simp only [laplacian, hessianForm_smul emb met atr conn ha hl conn_add_left conn_smul_left c f hc,
             metric_trace_smul, MultilinearMap.smul_apply, smul_eq_mul]

/-- Second covariant derivative of tensors. -/
noncomputable def SecondCovDerivTensor
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    {r s : ℕ} (T : TensorData R V r s) (X Y : V) : TensorData R V r s :=
  let nXY_T := nabla_tensor emb conn ha hl (conn X Y) T
  let nY_T := nabla_tensor emb conn ha hl Y T
  let nX_nY_T := nabla_tensor emb conn ha hl X nY_T
  nX_nY_T + (-1 : R) • nXY_T

end Laplacian
