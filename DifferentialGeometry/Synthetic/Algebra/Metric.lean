import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import DifferentialGeometry.Synthetic.Analysis.NablaOnTensors
import DifferentialGeometry.Synthetic.Analysis.TimeOnTensors

/-!
# Metric Infrastructure

MetricDuality structure, sharp/flat operators, and metric compatibility.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open BigOperators
open SyntheticTensor

-- ============================================================
-- flat_covector helper (needed BEFORE MetricDuality)
-- ============================================================

section FlatHelper
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Construct the covector g(Y, ·) from a (0,2)-tensor g and a vector Y. -/
def flat_covector (g : TensorData R V 0 2) (Y : V) : V →ₗ[R] R where
  toFun Z := g ![Y, Z] ![]
  map_add' a b := by
    have h := g.map_update_add ![Y, a] 1 a b
    have hu : ∀ v, Function.update (![Y, a] : Fin 2 → V) 1 v = ![Y, v] := by
      intro v; ext i; fin_cases i <;> simp [Function.update]
    simp only [hu] at h; exact congr_arg (· ![]) h
  map_smul' c a := by
    have h := congr_arg (· ![]) (g.map_update_smul ![Y, a] 1 c a)
    simp only [MultilinearMap.smul_apply, smul_eq_mul] at h
    rwa [show Function.update (![Y, a] : Fin 2 → V) 1 (c • a) = ![Y, c • a] from by
          ext i; fin_cases i <;> simp [Function.update],
         show Function.update (![Y, a] : Fin 2 → V) 1 a = ![Y, a] from by
          ext i; fin_cases i <;> simp [Function.update]] at h

@[simp] theorem flat_covector_apply (g : TensorData R V 0 2) (Y Z : V) :
    flat_covector g Y Z = g ![Y, Z] ![] := rfl

end FlatHelper

-- ============================================================
-- MetricDuality structure
-- ============================================================

/-- Metric duality: a (0,2) symmetric tensor with inverse.

    DATA: g_tensor, g_inv. PROPERTIES: symmetry, non-degeneracy,
    inverse_eval, sharp_spec. -/
structure MetricDuality (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  g_tensor : TensorData R V 0 2
  symm_tensor : swap_covariant 0 1 g_tensor = g_tensor
  g_inv : TensorData R V 2 0
  eq_of_forall_g_eq : ∀ X Y : V,
    (∀ Z : V, g_tensor ![X, Z] ![] = g_tensor ![Y, Z] ![]) → X = Y
  /-- g⁻¹(α, flat(Y)) = α(Y). -/
  inverse_eval : ∀ (Y : V) (α : V →ₗ[R] R),
    g_inv ![] ![α, flat_covector g_tensor Y] = α Y
  /-- Every covector is in the image of flat (surjectivity). -/
  sharp_spec : ∀ (α : V →ₗ[R] R), ∃ v : V, ∀ Z : V, g_tensor ![v, Z] ![] = α Z

-- ============================================================
-- g, flat, sharp, bilinearity
-- ============================================================

section MetricDefs
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def MetricDuality.g (met : MetricDuality R V) (X Y : V) : R :=
  met.g_tensor ![X, Y] ![]

/-- Evaluation of a scalar multiple of the metric tensor. -/
theorem MetricDuality.g_tensor_smul_eval
    (met : MetricDuality R V) (c : R) (X Y : V) :
    (c • met.g_tensor) ![X, Y] ![] = c * met.g X Y := by
  simp [MetricDuality.g, smul_eq_mul]

/-- Flat map: X ↦ g(X, –) as a covector. -/
def MetricDuality.flat (met : MetricDuality R V) (X : V) : V →ₗ[R] R :=
  flat_covector met.g_tensor X

@[simp] theorem MetricDuality.flat_apply (met : MetricDuality R V) (X Y : V) :
    met.flat X Y = met.g X Y := rfl

/-- Inverse evaluation in terms of flat. -/
theorem MetricDuality.inverse_eval' (met : MetricDuality R V)
    (Y : V) (α : V →ₗ[R] R) :
    met.g_inv ![] ![α, met.flat Y] = α Y :=
  met.inverse_eval Y α

theorem MetricDuality.g_symm (met : MetricDuality R V) (X Y : V) :
    met.g X Y = met.g Y X := by
  change met.g_tensor ![X, Y] ![] = met.g_tensor ![Y, X] ![]
  have h := congr_arg (fun T => T ![X, Y] ![]) met.symm_tensor
  simp only [swap_covariant_eval] at h
  rw [show (![X, Y] : Fin 2 → V) ∘ (Equiv.swap (0 : Fin 2) 1) = ![Y, X] from by
    ext i; fin_cases i <;> rfl] at h; exact h.symm

theorem MetricDuality.g_add_left (met : MetricDuality R V) (X Y Z : V) :
    met.g (X + Y) Z = met.g X Z + met.g Y Z := by
  change met.g_tensor ![X + Y, Z] ![] = met.g_tensor ![X, Z] ![] + met.g_tensor ![Y, Z] ![]
  have h := met.g_tensor.map_update_add ![X, Z] 0 X Y
  have hu : ∀ v, Function.update (![X, Z] : Fin 2 → V) 0 v = ![v, Z] := by
    intro v; ext i; fin_cases i <;> simp [Function.update]
  simp only [hu] at h; exact congr_arg (· ![]) h

theorem MetricDuality.g_smul_left (met : MetricDuality R V) (c : R) (X Z : V) :
    met.g (c • X) Z = c * met.g X Z := by
  change met.g_tensor ![c • X, Z] ![] = c * met.g_tensor ![X, Z] ![]
  have h := congr_arg (· ![]) (met.g_tensor.map_update_smul ![X, Z] 0 c X)
  simp only [MultilinearMap.smul_apply, smul_eq_mul] at h
  rwa [show Function.update (![X, Z] : Fin 2 → V) 0 (c • X) = ![c • X, Z] from by
        ext i; fin_cases i <;> simp [Function.update],
       show Function.update (![X, Z] : Fin 2 → V) 0 X = ![X, Z] from by
        ext i; fin_cases i <;> simp [Function.update]] at h

theorem MetricDuality.g_add_right (met : MetricDuality R V) (X Y Z : V) :
    met.g X (Y + Z) = met.g X Y + met.g X Z := by
  rw [met.g_symm X (Y + Z), met.g_add_left, met.g_symm Y, met.g_symm Z]

theorem MetricDuality.g_smul_right (met : MetricDuality R V) (c : R) (X Z : V) :
    met.g X (c • Z) = c * met.g X Z := by
  rw [met.g_symm X (c • Z), met.g_smul_left, met.g_symm Z]

/-- SharpSpec: every covector is in the image of flat. -/
def SharpSpec (met : MetricDuality R V) : Prop :=
  ∀ (α : V →ₗ[R] R), ∃ v : V, ∀ Z : V, met.g v Z = α Z

/-- The `sharp_spec` field implies `SharpSpec`. -/
theorem MetricDuality.sharpSpec (met : MetricDuality R V) : SharpSpec met :=
  fun α => met.sharp_spec α

noncomputable def MetricDuality.sharp (met : MetricDuality R V) (α : V →ₗ[R] R) : V :=
  open Classical in
  if h : ∃ v : V, ∀ Z : V, met.g v Z = α Z then h.choose else (0 : V)

theorem MetricDuality.g_sharp (met : MetricDuality R V)
    (α : V →ₗ[R] R) (Z : V) :
    met.g (met.sharp α) Z = α Z := by
  simp only [MetricDuality.sharp, dif_pos (met.sharpSpec α)]
  exact (met.sharpSpec α).choose_spec Z

theorem MetricDuality.sharp_flat (met : MetricDuality R V)
    (Y : V) :
    met.sharp (met.flat Y) = Y := by
  apply met.eq_of_forall_g_eq; intro Z
  exact met.g_sharp (met.flat Y) Z

theorem MetricDuality.flat_injective (met : MetricDuality R V) :
    Function.Injective met.flat := by
  intro X Y h; apply met.eq_of_forall_g_eq; intro Z
  exact congr_fun (congr_arg DFunLike.coe h) Z

/-- sharp is additive: sharp(α + β) = sharp(α) + sharp(β). -/
theorem MetricDuality.sharp_add (met : MetricDuality R V)
    (α β : V →ₗ[R] R) :
    met.sharp (α + β) = met.sharp α + met.sharp β := by
  apply met.eq_of_forall_g_eq; intro Z
  change met.g (met.sharp (α + β)) Z = met.g (met.sharp α + met.sharp β) Z
  rw [met.g_sharp, met.g_add_left, met.g_sharp, met.g_sharp]
  simp [LinearMap.add_apply]

/-- sharp is R-homogeneous: sharp(c • α) = c • sharp(α). -/
theorem MetricDuality.sharp_smul (met : MetricDuality R V)
    (c : R) (α : V →ₗ[R] R) :
    met.sharp (c • α) = c • met.sharp α := by
  apply met.eq_of_forall_g_eq; intro Z
  change met.g (met.sharp (c • α)) Z = met.g (c • met.sharp α) Z
  rw [met.g_sharp, met.g_smul_left, met.g_sharp]
  simp [LinearMap.smul_apply, smul_eq_mul]

end MetricDefs

-- ============================================================
-- IsMetricCompatible + ∇g = 0
-- ============================================================

section MetricCompat
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

def IsMetricCompatible
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (met : MetricDuality R V) : Prop :=
  ∀ X Y Z : V,
    (emb.embed X) (met.g Y Z) = met.g (conn X Y) Z + met.g Y (conn X Z)

-- Helper: g_tensor f ![] = g(f 0, f 1)
private theorem g_tensor_of (met : MetricDuality R V) (f : Fin 2 → V) :
    met.g_tensor f ![] = met.g (f 0) (f 1) := by
  change met.g_tensor f ![] = met.g_tensor ![f 0, f 1] ![]
  have hf : f = ![f 0, f 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hf]

theorem nabla_g_zero
    (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (X : V) :
    nabla_tensor emb conn ha hl X met.g_tensor = 0 := by
  ext vs αs; simp only [nabla_tensor_eval, MultilinearMap.zero_apply]
  rw [show αs = ![] from by ext i; exact i.elim0,
      Finset.sum_of_isEmpty (f := fun j : Fin 0 => _), sub_zero,
      Fin.sum_univ_two, sub_eq_zero,
      g_tensor_of met (Function.update vs 0 (conn X (vs 0))),
      g_tensor_of met (Function.update vs 1 (conn X (vs 1)))]
  simp only [Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 from by decide),
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 from by decide)]
  conv_lhs => rw [g_tensor_of met vs]
  exact h_mc X (vs 0) (vs 1)

end MetricCompat

-- ============================================================
-- ∇_X(flat Y) = flat(conn X Y)
-- ============================================================

section NablaDualFlat
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

theorem nabla_dual_flat
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (X Y : V) :
    nabla_dual emb conn ha hl X (met.flat Y) = met.flat (conn X Y) := by
  ext Z
  -- (∇*_X(flat Y))(Z) = X(g(Y,Z)) - g(Y, conn X Z) = g(conn X Y, Z) by compat
  -- met.flat A B is definitionally met.g A B
  change (emb.embed X) (met.g Y Z) - met.g Y (conn X Z) = met.g (conn X Y) Z
  -- h_mc : a = b + c, goal : a - c = b
  rw [h_mc X Y Z, add_sub_cancel_right]

end NablaDualFlat

-- ============================================================
-- ∇g⁻¹ = 0
-- ============================================================

section NablaGInv
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

theorem nabla_g_inv_zero
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (X : V) :
    nabla_tensor emb conn ha hl X met.g_inv = 0 := by
  ext vs αs; simp only [nabla_tensor_eval, MultilinearMap.zero_apply]
  -- g_inv is (2,0): s=0 empty vector slots, r=2 two covector slots
  rw [show vs = ![] from by ext i; exact i.elim0,
      Finset.sum_of_isEmpty (f := fun i : Fin 0 => _), sub_zero,
      Fin.sum_univ_two, sub_eq_zero]
  -- Simplify Function.update on Fin 2
  have h_u0 : ∀ v, met.g_inv ![] (Function.update αs 0 v) = met.g_inv ![] ![v, αs 1] := by
    intro v; congr 1; ext i; fin_cases i <;> simp [Function.update]
  have h_u1 : ∀ v, met.g_inv ![] (Function.update αs 1 v) = met.g_inv ![] ![αs 0, v] := by
    intro v; congr 1; ext i; fin_cases i <;> simp [Function.update]
  rw [h_u0, h_u1]
  -- Rewrite g_inv ![] αs to g_inv ![] ![αs 0, αs 1]
  conv_lhs => rw [show αs = ![αs 0, αs 1] from by ext i; fin_cases i <;> rfl]
  -- By SharpSpec: αs 1 = flat Y for some Y
  obtain ⟨Y, hY⟩ := met.sharpSpec (αs 1)
  have h_eq : met.flat Y = αs 1 := by ext Z; exact hY Z
  -- Substitute αs 1 → flat Y
  rw [← h_eq, nabla_dual_flat emb conn ha hl met h_mc X Y,
      met.inverse_eval', met.inverse_eval', met.inverse_eval']
  -- Goal: X(αs 0 Y) = (∇*αs 0)(Y) + αs 0 (conn X Y)
  simp only [nabla_dual, LinearMap.coe_mk, AddHom.coe_mk]; ring

end NablaGInv

-- ============================================================
-- NablaTensorContractComm
-- ============================================================

section NablaContractDef
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- ∇ commutes with tensor_contract. -/
def NablaTensorContractComm
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y) : Prop :=
  ∀ (X : V) {r s : ℕ} (T : TensorData R V (r + 1) (s + 1)),
    nabla_tensor emb conn ha hl X (atr.tensor_contract T) =
    atr.tensor_contract (nabla_tensor emb conn ha hl X T)

end NablaContractDef

-- ============================================================
-- lower_index, raise_index, metric_trace
-- ============================================================

section IndexOps
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def lower_index (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx : Fin (r + 1)) (T : TensorData R V (r + 1) s) : TensorData R V r (s + 1) :=
  contract_general atr idx ⟨1, by omega⟩
    ((show 0 + (r + 1) = r + 1 from by omega) ▸
     (show 2 + s = s + 1 + 1 from by omega) ▸
     tensor_prod (r₁ := 0) (s₁ := 2) (r₂ := r + 1) (s₂ := s) met.g_tensor T)

noncomputable def raise_index (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx : Fin (s + 1)) (T : TensorData R V r (s + 1)) : TensorData R V (r + 1) s :=
  contract_general atr ⟨1, by omega⟩ idx
    ((show 2 + r = r + 1 + 1 from by omega) ▸
     (show 0 + (s + 1) = s + 1 from by omega) ▸
     tensor_prod (r₁ := 2) (s₁ := 0) (r₂ := r) (s₂ := s + 1) met.g_inv T)

noncomputable def metric_trace (met : MetricDuality R V) (atr : AbstractTrace R V)
    {r s : ℕ} (idx₁ : Fin (s + 2)) (idx₂ : Fin (s + 1))
    (T : TensorData R V r (s + 2)) : TensorData R V r s :=
  contract_general atr (0 : Fin (r + 1)) idx₂ (raise_index met atr idx₁ T)

end IndexOps

-- ============================================================
-- lower_index evaluation for (1,1) tensors
-- ============================================================

section LowerIndexEval
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Evaluating lower_index at (0 : Fin 1) for a (1,1)-tensor:
    `lower_index met atr 0 T ![X, Y] ![] = T ![Y] ![met.flat X]`. -/
theorem lower_index_eval_11 (met : MetricDuality R V) (atr : AbstractTrace R V)
    (T : TensorData R V 1 1) (X Y : V) :
    lower_index met atr (0 : Fin 1) T ![X, Y] ![] = T ![Y] ![met.flat X] := by
  -- lower_index unfolds to contract_general atr 0 ⟨1,_⟩ (cast ▸ cast ▸ tensor_prod g T)
  -- = tensor_contract (swap_cov 0 1 (swap_contra 0 0 (cast ▸ cast ▸ tensor_prod g T)))
  -- swap_contra 0 0 = id, swap_cov 0 1 on g⊗T applies metric symmetry → identity
  -- Then data_eval_single_contract_dual gives the result.
  simp only [lower_index, contract_general]
  -- After simp, the goal should still have the tensor_contract of swapped tensor.
  -- We need to show this tensor equals tensor_prod g T extensionally.
  -- Work at the pointwise level: for any m' : Fin 3 → V, n' : Fin 1 → (V→ₗR),
  -- the swapped tensor evaluates the same as tensor_prod g T.
  have h_pw : ∀ (m' : Fin 3 → V) (n' : Fin 1 → (V →ₗ[R] R)),
      (swap_covariant (0 : Fin 3) ⟨1, by omega⟩
        (swap_contravariant (0 : Fin 1) 0
          (tensor_prod (r₁ := 0) (s₁ := 2) (r₂ := 1) (s₂ := 1)
            met.g_tensor T))) m' n' =
      (tensor_prod (r₁ := 0) (s₁ := 2) (r₂ := 1) (s₂ := 1) met.g_tensor T) m' n' := by
    intro m' n'
    simp only [swap_covariant_eval, swap_contravariant_eval, Equiv.swap_self]
    -- LHS: (tensor_prod g T (m' ∘ swap 0 1)) (n' ∘ refl)
    -- RHS: (tensor_prod g T m') n'
    -- Both unfold via tensor_prod_eval to products g(...)*T(...)
    -- Use that swap 0 1 permutes the g part (metric symmetry) and fixes the T part
    -- LHS after simp is: (tensor_prod g T (m' ∘ swap 0 1)) (n' ∘ refl)
    -- RHS is:            (tensor_prod g T m') n'
    -- Expand via tensor_prod_eval:
    -- g (m' ∘ swap ∘ castAdd 1) (n' ∘ refl ∘ castAdd 1) *
    -- T (m' ∘ swap ∘ natAdd 2) (n' ∘ refl ∘ natAdd 0)
    -- = g (m' ∘ castAdd 1) (n' ∘ castAdd 1) * T (m' ∘ natAdd 2) (n' ∘ natAdd 0)
    change met.g_tensor (m' ∘ Equiv.swap (0 : Fin 3) ⟨1, by omega⟩ ∘ Fin.castAdd 1)
             (n' ∘ Equiv.refl _ ∘ Fin.castAdd 1) *
           T (m' ∘ Equiv.swap (0 : Fin 3) ⟨1, by omega⟩ ∘ (Fin.natAdd 2 : Fin 1 → Fin 3))
             (n' ∘ Equiv.refl _ ∘ (Fin.natAdd 0 : Fin 1 → Fin 1)) =
           met.g_tensor (m' ∘ Fin.castAdd 1) (n' ∘ Fin.castAdd 1) *
           T (m' ∘ (Fin.natAdd 2 : Fin 1 → Fin 3)) (n' ∘ (Fin.natAdd 0 : Fin 1 → Fin 1))
    have hnat : m' ∘ Equiv.swap (0 : Fin 3) ⟨1, by omega⟩ ∘ (Fin.natAdd 2 : Fin 1 → Fin 3) =
                m' ∘ (Fin.natAdd 2 : Fin 1 → Fin 3) := by
      ext i; fin_cases i; rfl
    have hcast : m' ∘ Equiv.swap (0 : Fin 3) ⟨1, by omega⟩ ∘ Fin.castAdd 1 =
                 (m' ∘ Fin.castAdd 1) ∘ Equiv.swap (0 : Fin 2) 1 := by
      ext i; fin_cases i <;> rfl
    have hrefl0 : n' ∘ Equiv.refl (Fin 1) ∘ (Fin.natAdd 0 : Fin 1 → Fin 1) =
                  n' ∘ (Fin.natAdd 0 : Fin 1 → Fin 1) := by
      ext i; simp
    have hrefl1 : n' ∘ Equiv.refl (Fin 1) ∘ Fin.castAdd 1 =
                  n' ∘ Fin.castAdd 1 := by
      ext i; simp
    rw [hnat, hcast, hrefl0, hrefl1]
    congr 1
    -- Goal: g ((m' ∘ castAdd 1) ∘ swap 0 1) (n' ∘ castAdd 1) = g (m' ∘ castAdd 1) (n' ∘ castAdd 1)
    rw [show met.g_tensor ((m' ∘ Fin.castAdd 1) ∘ Equiv.swap (0 : Fin 2) 1) (n' ∘ Fin.castAdd 1) =
        swap_covariant 0 1 met.g_tensor (m' ∘ Fin.castAdd 1) (n' ∘ Fin.castAdd 1) from rfl]
    rw [met.symm_tensor]
  have h_ext : swap_covariant (0 : Fin 3) ⟨1, by omega⟩
      (swap_contravariant (0 : Fin 1) 0
        (tensor_prod (r₁ := 0) (s₁ := 2) (r₂ := 1) (s₂ := 1) met.g_tensor T)) =
      tensor_prod (r₁ := 0) (s₁ := 2) (r₂ := 1) (s₂ := 1) met.g_tensor T := by
    ext m' n'; exact h_pw m' n'
  rw [h_ext]
  rw [atr.data_eval_single_contract_dual met.g_tensor T ![X, Y] ![]]
  -- Goal: T (![X,Y] ∘ natAdd 1) (Fin.cons (covector_from_tensor g (![X,Y] ∘ castAdd 1) ![]) ![])
  --     = T ![Y] ![met.flat X]
  -- Need: ![X,Y] ∘ natAdd 1 = ![Y] and the covector = met.flat X
  have hm : (![X, Y] : Fin 2 → V) ∘ Fin.natAdd 1 = ![Y] := by
    ext i; fin_cases i; rfl
  have hcov : covector_from_tensor met.g_tensor ((![X, Y] : Fin 2 → V) ∘ Fin.castAdd 1) ![] =
              met.flat X := by
    ext v
    simp only [covector_from_tensor, LinearMap.coe_mk, AddHom.coe_mk,
               MetricDuality.flat, flat_covector_apply]
    have : Fin.cons v ((![X, Y] : Fin 2 → V) ∘ Fin.castAdd 1) = ![v, X] := by
      ext j; fin_cases j <;> rfl
    rw [this]; exact met.g_symm v X
  have hn : Fin.cons (covector_from_tensor met.g_tensor ((![X, Y] : Fin 2 → V) ∘ Fin.castAdd 1)
              ![]) (![  ] : Fin 0 → (V →ₗ[R] R)) = ![met.flat X] := by
    rw [hcov]; ext i; fin_cases i; rfl
  rw [hm, hn]

end LowerIndexEval

-- ============================================================
-- ∇ commutes with raise_index and metric_trace
-- ============================================================

section NablaMetricTrace
variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

-- Helper: TensorData equality implies pointwise equality
private theorem td_congr {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {r s : ℕ} {T₁ T₂ : TensorData R V r s} (h : T₁ = T₂) (vs αs) :
    T₁ vs αs = T₂ vs αs := by rw [h]

/-- ∇ commutes with raise_index, derived from:
    - NablaTensorContractComm (∇ commutes with tensor_contract)
    - IsMetricCompatible (∇g⁻¹ = 0 via nabla_g_inv_zero)
    - Leibniz rule for tensor products (nabla_tensor_prod)

    raise_index = contract_general ∘ (g⁻¹ ⊗ ·).
    contract_general = tensor_contract ∘ swap_cov ∘ swap_contra. -/
theorem nabla_raise_index_comm
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (atr : AbstractTrace R V)
    (h_ntc : NablaTensorContractComm emb atr conn ha hl)
    (Y : V) {r s : ℕ} (idx : Fin (s + 1)) (T : TensorData R V r (s + 1)) :
    nabla_tensor emb conn ha hl Y (raise_index met atr idx T) =
    raise_index met atr idx (nabla_tensor emb conn ha hl Y T) := by
  -- Key fact: ∇(h▸h▸ g_inv ⊗ S) = h▸h▸ g_inv ⊗ ∇S
  -- Proved at the cast-wrapped type TensorData R V (r+1+1) (s+1).
  have h_tp : nabla_tensor emb conn ha hl Y
      ((show 2 + r = r + 1 + 1 from by omega) ▸
       (show 0 + (s + 1) = s + 1 from by omega) ▸
       tensor_prod (r₁ := 2) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
         met.g_inv T) =
      (show 2 + r = r + 1 + 1 from by omega) ▸
      (show 0 + (s + 1) = s + 1 from by omega) ▸
      tensor_prod (r₁ := 2) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
        met.g_inv (nabla_tensor emb conn ha hl Y T) := by
    -- First prove the un-cast version
    have h_eq : nabla_tensor emb conn ha hl Y (tensor_prod met.g_inv T) =
        tensor_prod met.g_inv (nabla_tensor emb conn ha hl Y T) := by
      ext vs αs
      have := congr_arg (· vs αs) (nabla_tensor_prod emb conn ha hl Y met.g_inv T)
      simp only [MultilinearMap.add_apply] at this
      rw [this]
      have : tensor_prod (nabla_tensor emb conn ha hl Y met.g_inv) T vs αs = 0 := by
        rw [nabla_g_inv_zero emb conn ha hl met h_mc Y]
        simp [tensor_prod_eval, MultilinearMap.zero_apply]
      rw [this, zero_add]
    -- Now transport through the casts
    -- For any h : n = m, nabla(h ▸ T) = h ▸ nabla(T) because nabla_tensor
    -- is parametric in the Fin type indices.
    -- We prove this generically for both casts.
    have cast_nabla : ∀ {r₁ r₂ s₁ s₂ : ℕ} (hr : r₁ = r₂) (hs : s₁ = s₂)
        (S : TensorData R V r₁ s₁),
        nabla_tensor emb conn ha hl Y (hr ▸ hs ▸ S) = hr ▸ hs ▸ nabla_tensor emb conn ha hl Y S := by
      intro r₁ r₂ s₁ s₂ hr hs S; subst hr; subst hs; rfl
    rw [cast_nabla, h_eq]
  -- Step 1: Show ∇ commutes with swap_contravariant (pointwise)
  have h_swap_contra : ∀ {r' s' : ℕ} (i j : Fin r') (S : TensorData R V r' s') vs αs,
      nabla_tensor emb conn ha hl Y (swap_contravariant i j S) vs αs =
      swap_contravariant i j (nabla_tensor emb conn ha hl Y S) vs αs := by
    intro r' s' i j S vs αs
    simp only [nabla_tensor_eval, swap_contravariant_eval]
    -- LHS: X(S vs (αs∘σ)) - Σ_l S(upd vs l ..)(αs∘σ) - Σ_m S vs ((upd αs m (∇*(αs m))) ∘ σ)
    -- RHS: X(S vs (αs∘σ)) - Σ_l S(upd vs l ..)(αs∘σ) - Σ_m S vs (upd (αs∘σ) m (∇*((αs∘σ) m)))
    -- First two terms match. For the covector sums, re-index by σ.
    -- sub_right_inj to reduce to the covector sum equality
    rw [sub_right_inj]
    -- Goal: Σ_m S vs ((upd αs m (∇*(αs m))) ∘ σ) = Σ_m S vs (upd (αs∘σ) m (∇*((αs∘σ) m)))
    refine Finset.sum_equiv (Equiv.swap i j) (fun _ => by simp) (fun l _ => ?_)
    -- Goal: S vs ((upd αs (σ l) (∇*(αs (σ l)))) ∘ σ) = S vs (upd (αs∘σ) l (∇*((αs∘σ) l)))
    -- (upd αs (σ l) v) ∘ σ = upd (αs∘σ) l v  (since σ is injective and σ(σ l) = l)
    congr 1
    ext k
    simp only [Function.comp_apply, Function.update_apply, Equiv.swap_apply_self,
      show ∀ (a b : Fin r'), (Equiv.swap i j) a = b ↔ a = (Equiv.swap i j) b from
        fun a b => ⟨fun h => by rw [← h, Equiv.swap_apply_self],
                    fun h => by rw [h, Equiv.swap_apply_self]⟩]
  -- Step 2: Assemble: unfold raise_index, use h_ntc, nabla_swap, h_swap_contra, h_tp
  simp only [raise_index, contract_general]
  rw [h_ntc]; congr 1
  ext vs αs
  rw [nabla_swap emb conn ha hl Y 0 idx]; simp only [swap_covariant_eval]
  rw [h_swap_contra]; simp only [swap_contravariant_eval]
  -- Goal: ∇(cast ▸ cast ▸ tensor_prod g_inv T) at args = (cast ▸ cast ▸ tensor_prod g_inv (∇T)) at args
  -- The ▸ casts use Eq.mpr on ℕ equalities.
  -- We need to show nabla commutes with these casts and tensor_prod.
  -- Strategy: use h_tp via congr_arg on the cast structure.
  -- Since both sides have the same cast structure h₁ ▸ h₂ ▸ _,
  -- it suffices to show the un-cast parts are equal under nabla.
  -- The key insight: ∇(h₁ ▸ h₂ ▸ P) = h₁ ▸ h₂ ▸ ∇(P) because nabla_tensor
  -- is defined by evaluation, and the casts just reindex Fin types.
  -- We can prove this by showing the cast commutes with nabla.
  have hr : (2 + r) = (r + 1 + 1) := by omega
  have hs : (0 + (s + 1)) = (s + 1) := by omega
  -- Now apply h_tp at the permuted arguments
  exact td_congr h_tp _ _

/-- ∇ commutes with metric_trace, given:
    - NablaTensorContractComm (∇ commutes with tensor_contract)
    - IsMetricCompatible (for nabla_raise_index_comm)

    metric_trace = contract_general ∘ raise_index.
    contract_general = tensor_contract ∘ swap_cov ∘ swap_contra.
    The outer contract_general has swap_contra 0 0 = id (Equiv.swap_self). -/
theorem nabla_metric_trace_comm
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V)
    (h_ntc : NablaTensorContractComm emb atr conn ha hl)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (X : V) {r s : ℕ} (idx₁ : Fin (s + 2)) (idx₂ : Fin (s + 1))
    (T : TensorData R V r (s + 2)) :
    nabla_tensor emb conn ha hl X (metric_trace met atr idx₁ idx₂ T) =
    metric_trace met atr idx₁ idx₂ (nabla_tensor emb conn ha hl X T) := by
  simp only [metric_trace, contract_general]
  -- Pull ∇ through tensor_contract
  rw [h_ntc]
  congr 1
  -- Pull ∇ through swap_covariant 0 idx₂
  ext vs αs
  rw [nabla_swap emb conn ha hl X 0 idx₂]; simp only [swap_covariant_eval]
  -- swap_contravariant 0 0 = id
  have hsc : ∀ (S : TensorData R V (r + 1) (s + 1)),
      swap_contravariant 0 0 S = S := by
    intro S; ext m n; simp [swap_contravariant_eval, Equiv.swap_self]
  simp only [hsc]
  -- Now: ∇(raise_index T) at (vs ∘ σ, αs) = raise_index(∇T) at (vs ∘ σ, αs)
  exact td_congr (nabla_raise_index_comm emb conn ha hl met h_mc atr h_ntc X idx₁ T) _ _

end NablaMetricTrace

-- ============================================================
-- Time derivative properties
-- ============================================================

section TimeDeriv
variable {R V : Type*} {A Time : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [CommRing A] [Algebra R A]

theorem t_const_V (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) (X : V) :
    dt_tensor td t (fun _ => vectorToData (R := R) X)
      (fun vs αs => td.isSmoothFam_const (vectorToData (R := R) X vs αs)) = 0 :=
  dt_tensor_const td t (vectorToData X)

theorem t_const_scalar (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (t : Time) (c : R) :
    dt_tensor td t (fun _ => scalarToData (R := R) (V := V) c)
      (fun vs αs => td.isSmoothFam_const
        (scalarToData (R := R) (V := V) c vs αs)) = 0 :=
  dt_tensor_const td t (scalarToData c)

/-- ∂_t(g(s)(X, Y)) = (∂_t g_tensor)(X, Y) for constant vector arguments. -/
theorem dt_metric_const_args
    (td : TimeDerivativeData R A Time) [TimeRegularFam td]
    (met_fam : Time → MetricDuality R V)
    (h_met : ∀ vs αs, td.isSmoothFam (fun τ => (met_fam τ).g_tensor vs αs))
    (X Y : V) (t : Time) :
    td.dt_apply (fun s => (met_fam s).g X Y) t =
    dt_tensor td t (fun s => (met_fam s).g_tensor) h_met ![X, Y] ![] := by
  rfl

/-- ∂_t of metric with one varying left argument:
    met.g (f s) Y = met.flat Y (f s), so the time derivative is just dt of
    a constant covector applied to a varying vector. -/
theorem t_metric_one_varying_left
    (td : TimeDerivativeData R A Time)
    (met : MetricDuality R V) (f : Time → V) (Y : V) (t : Time) :
    td.dt_apply (fun s => met.g (f s) Y) t =
    td.dt_apply (fun s => met.flat Y (f s)) t := by
  show td.dt_apply (fun s => met.g (f s) Y) t = _
  rw [show (fun s => met.g (f s) Y) = (fun s => met.flat Y (f s)) from
    funext (fun s => met.g_symm (f s) Y)]

/-- ∂_t of metric with one varying right argument:
    met.g X (f s) = met.flat X (f s). -/
theorem t_metric_one_varying_right
    (td : TimeDerivativeData R A Time)
    (met : MetricDuality R V) (X : V) (f : Time → V) (t : Time) :
    td.dt_apply (fun s => met.g X (f s)) t =
    td.dt_apply (fun s => met.flat X (f s)) t := by
  rfl

/-- Full Leibniz expansion for ∂_t(g(s)(X(s), Y(s))) when g, X, Y all vary.
    Expressed as a "diagonal derivative = partial derivatives" identity:

    dt(s ↦ g(s)(X(s), Y(s))) = dt(s ↦ g(s)(X(t), Y(t)))   -- metric varies
                               + dt(s ↦ g(t)(X(s), Y(t)))   -- X varies
                               + dt(s ↦ g(t)(X(t), Y(s)))   -- Y varies

    This is the multilinear Leibniz rule for bilinear evaluation.
    It holds because g(s)(X(s), Y(s)) decomposes additively:

    g(s)(X(s), Y(s)) = g(t)(X(s), Y(s)) + [g(s) - g(t)](X(s), Y(s))
    g(t)(X(s), Y(s)) = g(t)(X(t), Y(s)) + g(t)(X(s) - X(t), Y(s))

    The "cross terms" (involving both (g(s)-g(t)) and (X(s)-X(t))) are second-order
    and vanish under dt (which is a derivation, not a limit).

    For an abstract derivation dt, the identity holds when the cross terms
    dt(s ↦ [g(s)-g(t)](X(s)-X(t), Y(s))) = 0 etc. These require additional
    hypotheses about the derivation's interaction with evaluation.

    We state the most general useful form: dt of each "partial variation". -/
theorem t_metric_partial_variations
    (td : TimeDerivativeData R A Time)
    (met_fam : Time → MetricDuality R V) (X Y : V) (t : Time) :
    td.dt_apply (fun s => (met_fam s).g X Y) t =
    td.dt_apply (fun s => (met_fam s).g_tensor ![X, Y] ![]) t := by
  rfl

/-- When the metric is FIXED and both arguments vary,
    g(f_X(s), f_Y(s)) = flat(f_X(s))(f_Y(s)) where flat varies covector-valued.
    This is useful for Palatini/connection variation contexts where the metric
    is frozen at a time instant but vector arguments change. -/
theorem t_metric_fixed_both_varying
    (td : TimeDerivativeData R A Time)
    (met : MetricDuality R V) (f_X f_Y : Time → V) (t : Time) :
    td.dt_apply (fun s => met.g (f_X s) (f_Y s)) t =
    td.dt_apply (fun s => met.flat (f_X s) (f_Y s)) t := by
  rfl

end TimeDeriv
