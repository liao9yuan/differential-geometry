import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Covariant Derivative on Tensors

∇_X T defined by the evaluation formula.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open BigOperators
open SyntheticTensor

-- ============================================================
-- ∇_X* on covectors
-- ============================================================

section NablaDual

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Dual connection: (∇_X* α)(Y) = X(α(Y)) - α(∇_X Y). -/
def nabla_dual (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (conn_add : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_leibniz : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (α : V →ₗ[R] R) : V →ₗ[R] R where
  toFun Y := (emb.embed X) (α Y) - α (conn X Y)
  map_add' Y Z := by simp only [map_add, conn_add]; ring
  map_smul' c Y := by
    simp only [RingHom.id_apply, smul_eq_mul, map_smul α, smul_eq_mul]
    have h := (emb.embed X).leibniz c (α Y); simp only [smul_eq_mul] at h; rw [h]
    rw [conn_leibniz X c Y, map_add α, map_smul α, map_smul α]
    simp only [smul_eq_mul]; ring

theorem nabla_dual_map_add (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (α₁ α₂ : V →ₗ[R] R) :
    nabla_dual emb conn ha hl X (α₁ + α₂) =
    nabla_dual emb conn ha hl X α₁ + nabla_dual emb conn ha hl X α₂ := by
  ext Y; simp [nabla_dual, map_add]; ring

theorem nabla_dual_leibniz (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (c : R) (α : V →ₗ[R] R) :
    nabla_dual emb conn ha hl X (c • α) =
    c • nabla_dual emb conn ha hl X α + (emb.embed X) c • α := by
  ext Y; simp only [nabla_dual, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    LinearMap.add_apply, smul_eq_mul]
  have h := (emb.embed X).leibniz c (α Y); simp only [smul_eq_mul] at h; rw [h]; ring

end NablaDual

-- ============================================================
-- Finset sum helper
-- ============================================================

section FinsetHelper
variable {R : Type*} [CommRing R]

private lemma finset_sum_correction {n : ℕ} (idx : Fin n) (c extra : R)
    (f g : Fin n → R) (hne : ∀ j, j ≠ idx → f j = c * g j)
    (hk : f idx = extra + c * g idx) :
    ∑ j : Fin n, f j = extra + c * ∑ j : Fin n, g j := by
  rw [Finset.mul_sum]
  have := (Finset.add_sum_erase _ f (Finset.mem_univ idx)).symm
  rw [this, hk]
  have := Finset.sum_congr rfl (fun j (hj : j ∈ Finset.univ.erase idx) =>
    hne j (Finset.ne_of_mem_erase hj))
  rw [this]
  have := (Finset.add_sum_erase _ (fun j => c * g j) (Finset.mem_univ idx)).symm
  rw [this]; ring

end FinsetHelper

-- ============================================================
-- ∇_X on (r,s)-tensors via evaluation formula
-- ============================================================

section NablaTensor

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

private lemma embed_leibniz' (emb : DerivationEmbedding k R V) (X : V) (c f : R) :
    (emb.embed X) (c * f) = (emb.embed X) c * f + c * (emb.embed X) f := by
  have h := (emb.embed X).leibniz c f; simp only [smul_eq_mul] at h; rw [h]; ring

/-- Covariant derivative of (r,s)-tensor T along X, defined by the evaluation formula.

    (∇_X T)(vs)(αs) = X(T vs αs)
      - Σᵢ T(update vs i (∇_X vᵢ))(αs)
      - Σⱼ T(vs)(update αs j (∇_X* αⱼ)) -/
noncomputable def nabla_tensor (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T : TensorData R V r s) : TensorData R V r s where
  toFun vs :=
    -- Inner multilinear map (in covector args αs)
    { toFun := fun αs =>
        (emb.embed X) (T vs αs)
        - ∑ i : Fin s, T (Function.update vs i (conn X (vs i))) αs
        - ∑ j : Fin r, T vs (Function.update αs j
            (nabla_dual emb conn ha hl X (αs j)))
      map_update_add' := by
        intro inst αs idx β₁ β₂
        have : inst = instDecidableEqFin r := Subsingleton.elim _ _; subst this
        have h1 := (T vs).map_update_add αs idx β₁ β₂
        rw [h1, map_add]
        have h2 : ∀ i, T (Function.update vs i (conn X (vs i)))
            (Function.update αs idx (β₁ + β₂)) =
            T (Function.update vs i (conn X (vs i))) (Function.update αs idx β₁) +
            T (Function.update vs i (conn X (vs i))) (Function.update αs idx β₂) :=
          fun i => (T (Function.update vs i (conn X (vs i)))).map_update_add αs idx β₁ β₂
        simp_rw [h2, Finset.sum_add_distrib]
        -- Covector correction: each summand splits at idx
        have h3 : ∀ j,
            T vs (Function.update (Function.update αs idx (β₁ + β₂)) j
              (nabla_dual emb conn ha hl X (Function.update αs idx (β₁ + β₂) j))) =
            T vs (Function.update (Function.update αs idx β₁) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β₁ j))) +
            T vs (Function.update (Function.update αs idx β₂) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β₂ j))) := by
          intro j; by_cases hj : j = idx
          · -- After subst, idx is replaced by j everywhere
            subst hj
            simp only [Function.update_self, Function.update_idem]
            rw [nabla_dual_map_add]; exact (T vs).map_update_add αs j _ _
          · -- idx still exists in this branch (subst didn't fire)
            rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj,
                Function.update_comm (Ne.symm hj) _ _ αs,
                Function.update_comm (Ne.symm hj) _ _ αs,
                Function.update_comm (Ne.symm hj) _ _ αs]
            exact (T vs).map_update_add _ idx β₁ β₂
        have h3' : ∑ j, T vs (Function.update (Function.update αs idx (β₁ + β₂)) j
              (nabla_dual emb conn ha hl X (Function.update αs idx (β₁ + β₂) j))) =
            ∑ j, T vs (Function.update (Function.update αs idx β₁) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β₁ j))) +
            ∑ j, T vs (Function.update (Function.update αs idx β₂) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β₂ j))) := by
          conv_lhs => arg 2; ext j; rw [h3 j]
          exact Finset.sum_add_distrib
        -- Rewrite inside the covector sum using conv, then split and ring
        conv_lhs => arg 2; arg 2; ext j; rw [h3 j]
        rw [Finset.sum_add_distrib]; ring
      map_update_smul' := by
        intro inst αs idx c β
        have : inst = instDecidableEqFin r := Subsingleton.elim _ _; subst this
        simp only [smul_eq_mul]
        have hF : T vs (Function.update αs idx (c • β)) =
            c * T vs (Function.update αs idx β) := by
          have := (T vs).map_update_smul αs idx c β; rwa [smul_eq_mul] at this
        rw [hF, embed_leibniz' emb X]
        -- Vector correction: each term is multilinear in αs at idx
        have h_vec : ∀ i, T (Function.update vs i (conn X (vs i)))
            (Function.update αs idx (c • β)) =
            c * T (Function.update vs i (conn X (vs i))) (Function.update αs idx β) := by
          intro i
          have := (T (Function.update vs i (conn X (vs i)))).map_update_smul αs idx c β
          rwa [smul_eq_mul] at this
        simp_rw [h_vec, ← Finset.mul_sum]
        -- Covector correction sum: use finset_sum_correction
        -- f j = LHS cov term, g j = RHS cov term
        -- For j ≠ idx: f j = c * g j. For j = idx: f idx = extra + c * g idx.
        let f_cov := fun j => T vs (Function.update (Function.update αs idx (c • β)) j
              (nabla_dual emb conn ha hl X (Function.update αs idx (c • β) j)))
        let g_cov := fun j => T vs (Function.update (Function.update αs idx β) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β j)))
        have h_ne : ∀ j, j ≠ idx → f_cov j = c * g_cov j := by
          intro j hj
          change T vs (Function.update (Function.update αs idx (c • β)) j
              (nabla_dual emb conn ha hl X (Function.update αs idx (c • β) j))) =
            c * T vs (Function.update (Function.update αs idx β) j
              (nabla_dual emb conn ha hl X (Function.update αs idx β j)))
          rw [Function.update_of_ne hj, Function.update_of_ne hj,
              Function.update_comm (Ne.symm hj) _ _ αs,
              Function.update_comm (Ne.symm hj) _ _ αs]
          have := (T vs).map_update_smul (Function.update αs j
            (nabla_dual emb conn ha hl X (αs j))) idx c β
          rwa [smul_eq_mul] at this
        have h_eq : f_cov idx =
            (emb.embed X) c * T vs (Function.update αs idx β) +
            c * g_cov idx := by
          change T vs (Function.update (Function.update αs idx (c • β)) idx
              (nabla_dual emb conn ha hl X (Function.update αs idx (c • β) idx))) =
            (emb.embed X) c * T vs (Function.update αs idx β) +
            c * T vs (Function.update (Function.update αs idx β) idx
              (nabla_dual emb conn ha hl X (Function.update αs idx β idx)))
          simp only [Function.update_self, Function.update_idem]
          rw [nabla_dual_leibniz,
              (T vs).map_update_add αs idx (c • nabla_dual emb conn ha hl X β)
                ((emb.embed X) c • β),
              (T vs).map_update_smul αs idx c (nabla_dual emb conn ha hl X β),
              (T vs).map_update_smul αs idx ((emb.embed X) c) β]
          simp [smul_eq_mul]; ring
        have h_sum := finset_sum_correction idx c
          ((emb.embed X) c * T vs (Function.update αs idx β))
          f_cov g_cov h_ne h_eq
        change _ = c * _
        rw [h_sum]; ring }
  map_update_add' := by

    intro inst vs idx v₁ v₂
    have : inst = instDecidableEqFin s := Subsingleton.elim _ _; subst this
    ext αs
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    -- Derivation term: X additive, T multilinear at idx
    rw [(T.map_update_add vs idx v₁ v₂ : T (Function.update vs idx (v₁ + v₂)) =
      T (Function.update vs idx v₁) + T (Function.update vs idx v₂))]
    simp only [MultilinearMap.add_apply, map_add]
    -- Vector correction: splits
    have h_vec : ∀ i,
        T (Function.update (Function.update vs idx (v₁ + v₂)) i
          (conn X (Function.update vs idx (v₁ + v₂) i))) αs =
        T (Function.update (Function.update vs idx v₁) i
          (conn X (Function.update vs idx v₁ i))) αs +
        T (Function.update (Function.update vs idx v₂) i
          (conn X (Function.update vs idx v₂ i))) αs := by
      intro i; by_cases hi : i = idx
      · subst hi; simp only [Function.update_self, Function.update_idem, ha X v₁ v₂]
        exact congr_arg (· αs) (T.map_update_add vs i _ _)
      · rw [Function.update_of_ne hi, Function.update_of_ne hi, Function.update_of_ne hi,
            Function.update_comm (Ne.symm hi) _ _ vs,
            Function.update_comm (Ne.symm hi) _ _ vs,
            Function.update_comm (Ne.symm hi) _ _ vs]
        exact congr_arg (· αs) (T.map_update_add _ idx _ _)
    simp_rw [h_vec, Finset.sum_add_distrib]
    -- Covector correction: T multilinear at vs idx gives additive split
    have h_cov : ∀ j,
        T (Function.update vs idx (v₁ + v₂)) (Function.update αs j
          (nabla_dual emb conn ha hl X (αs j))) =
        T (Function.update vs idx v₁) (Function.update αs j
          (nabla_dual emb conn ha hl X (αs j))) +
        T (Function.update vs idx v₂) (Function.update αs j
          (nabla_dual emb conn ha hl X (αs j))) := by
      intro j
      have := T.map_update_add vs idx v₁ v₂
      change (T (Function.update vs idx (v₁ + v₂))) _ = _
      rw [this]; simp [MultilinearMap.add_apply]
    ring
  map_update_smul' := by
    intro inst vs idx c v
    have : inst = instDecidableEqFin s := Subsingleton.elim _ _; subst this
    ext αs
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    -- T multilinear at vs idx: T(update vs idx (c•v)) = c • T(update vs idx v)
    have hT : T (Function.update vs idx (c • v)) = c • T (Function.update vs idx v) :=
      T.map_update_smul vs idx c v
    rw [hT]; simp only [MultilinearMap.smul_apply, smul_eq_mul]
    -- X Leibniz on the scalar c * T(...)αs
    rw [embed_leibniz' emb X]
    -- Vector correction sum: Leibniz splitting
    -- Need: Σ LHS_i = X(c)*T_v(αs) + c * Σ RHS_i
    -- For i ≠ idx: LHS_i = c * RHS_i (T multilinear at idx)
    -- For i = idx: LHS_idx = X(c)*T_v(αs) + c * RHS_idx (connection Leibniz)
    -- Then Σ LHS = X(c)*T_v(αs) + c * Σ RHS by splitting at idx
    -- Prove via substitution: rewrite each LHS_i in the sum
    -- Use finset_sum_correction for vector sum
    let f_vec := fun i => T (Function.update (Function.update vs idx (c • v)) i
          (conn X (Function.update vs idx (c • v) i))) αs
    let g_vec := fun i => T (Function.update (Function.update vs idx v) i
          (conn X (Function.update vs idx v i))) αs
    have h_ne : ∀ i, i ≠ idx → f_vec i = c * g_vec i := by
      intro i hi
      change T (Function.update (Function.update vs idx (c • v)) i
          (conn X (Function.update vs idx (c • v) i))) αs =
        c * T (Function.update (Function.update vs idx v) i
          (conn X (Function.update vs idx v i))) αs
      rw [Function.update_of_ne hi, Function.update_of_ne hi,
          Function.update_comm (Ne.symm hi) _ _ vs,
          Function.update_comm (Ne.symm hi) _ _ vs]
      exact congr_arg (· αs) (T.map_update_smul _ idx c v)
    have h_eq : f_vec idx =
        (emb.embed X) c * (T (Function.update vs idx v)) αs +
        c * g_vec idx := by
      change T (Function.update (Function.update vs idx (c • v)) idx
          (conn X (Function.update vs idx (c • v) idx))) αs =
        (emb.embed X) c * (T (Function.update vs idx v)) αs +
        c * T (Function.update (Function.update vs idx v) idx
          (conn X (Function.update vs idx v idx))) αs
      simp only [Function.update_self, Function.update_idem, hl X c v]
      have h1 := T.map_update_add vs idx ((emb.embed X) c • v) (c • conn X v)
      have h2 := congr_arg (· αs) h1
      simp only [MultilinearMap.add_apply] at h2; rw [h2]
      have h3 := congr_arg (· αs) (T.map_update_smul vs idx ((emb.embed X) c) v)
      simp only [MultilinearMap.smul_apply, smul_eq_mul] at h3; rw [h3]
      have h4 := congr_arg (· αs) (T.map_update_smul vs idx c (conn X v))
      simp only [MultilinearMap.smul_apply, smul_eq_mul] at h4; rw [h4]
    have h_sum := finset_sum_correction idx c
      ((emb.embed X) c * (T (Function.update vs idx v)) αs)
      f_vec g_vec h_ne h_eq
    -- Covector correction already in the form c * (...) after rw [hT] + smul_eq_mul
    rw [← Finset.mul_sum]
    change _ = c * _
    rw [h_sum]; ring

-- ============================================================
-- Evaluation lemma and derived properties
-- ============================================================

theorem nabla_tensor_eval (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T : TensorData R V r s) (vs αs) :
    nabla_tensor emb conn ha hl X T vs αs =
    (emb.embed X) (T vs αs)
    - ∑ i : Fin s, T (Function.update vs i (conn X (vs i))) αs
    - ∑ j : Fin r, T vs (Function.update αs j
        (nabla_dual emb conn ha hl X (αs j))) := by
  rfl

theorem nabla_scalar (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 0 0) :
    nabla_tensor emb conn ha hl X T ![] ![] = (emb.embed X) (T ![] ![]) := by
  rw [nabla_tensor_eval]; simp

theorem nabla_add (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T₁ T₂ : TensorData R V r s) :
    nabla_tensor emb conn ha hl X (T₁ + T₂) =
    nabla_tensor emb conn ha hl X T₁ + nabla_tensor emb conn ha hl X T₂ := by
  ext vs αs
  simp only [nabla_tensor_eval, MultilinearMap.add_apply, map_add, Finset.sum_add_distrib]; ring

theorem nabla_smul (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (c : R) (T : TensorData R V r s) (vs αs) :
    nabla_tensor emb conn ha hl X (c • T) vs αs =
    (emb.embed X) c * T vs αs + c * nabla_tensor emb conn ha hl X T vs αs := by
  simp only [nabla_tensor_eval, MultilinearMap.smul_apply, smul_eq_mul,
    ← Finset.mul_sum, embed_leibniz']; ring

theorem nabla_smul_left (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (f : R) (X : V) {r s : ℕ} (T : TensorData R V r s) (vs αs) :
    nabla_tensor emb conn ha hl (f • X) T vs αs =
    f * nabla_tensor emb conn ha hl X T vs αs := by
  simp only [nabla_tensor_eval]
  simp only [show ∀ g, (emb.embed (f • X)) g = f * (emb.embed X) g from
    fun g => by simp [map_smul, Derivation.smul_apply, smul_eq_mul]]
  simp only [hsl]
  simp only [show ∀ α, nabla_dual emb conn ha hl (f • X) α =
      f • nabla_dual emb conn ha hl X α from fun α => by
    ext Y; simp [nabla_dual, map_smul, Derivation.smul_apply, smul_eq_mul, hsl]; ring]
  simp only [show ∀ i, T (Function.update vs i (f • conn X (vs i))) αs =
      f * T (Function.update vs i (conn X (vs i))) αs from fun i => by
    have := congr_arg (· αs) (T.map_update_smul vs i f (conn X (vs i)))
    simp [smul_eq_mul]]
  simp only [show ∀ j, T vs (Function.update αs j
      (f • nabla_dual emb conn ha hl X (αs j))) =
      f * T vs (Function.update αs j (nabla_dual emb conn ha hl X (αs j))) from fun j => by
    have := (T vs).map_update_smul αs j f (nabla_dual emb conn ha hl X (αs j))
    simp [smul_eq_mul]]
  rw [← Finset.mul_sum, ← Finset.mul_sum]; ring

-- ============================================================
-- Additional derived properties
-- ============================================================

/-- ∇_X on vectors: ∇_X(vectorToData Y) = vectorToData(conn X Y).
    The (1,0) case: no covariant slots, one contravariant slot. -/
theorem nabla_vector (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) :
    nabla_tensor emb conn ha hl X (vectorToData (R := R) Y) =
    vectorToData (R := R) (conn X Y) := by
  ext vs αs
  rw [nabla_tensor_eval]
  -- s = 0: the vector correction sum over Fin 0 is empty
  have hs : ∑ i : Fin 0, vectorToData (R := R) Y
      (Function.update vs i (conn X (vs i))) αs = 0 := by
    simp [Finset.univ_eq_empty]
  rw [hs, sub_zero]
  -- r = 1: one covector correction (j = 0), vectorToData evals to α(Y)
  have hr : ∑ j : Fin 1, vectorToData (R := R) Y vs
      (Function.update αs j (nabla_dual emb conn ha hl X (αs j))) =
    (nabla_dual emb conn ha hl X (αs 0)) Y := by
    simp [Finset.univ_unique, Finset.sum_singleton, vectorToData, evalLinear,
      MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton]
  rw [hr]
  -- Now goal: X(αs 0 Y) - (X(αs 0 Y) - αs 0 (conn X Y)) = αs 0 (conn X Y)
  simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty,
    MultilinearMap.ofSubsingleton, nabla_dual]

/-- ∇ is additive in X: ∇_{X+Y} T = ∇_X T + ∇_Y T. -/
theorem nabla_add_left (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X Y : V) {r s : ℕ} (T : TensorData R V r s) (vs αs) :
    nabla_tensor emb conn ha hl (X + Y) T vs αs =
    nabla_tensor emb conn ha hl X T vs αs +
    nabla_tensor emb conn ha hl Y T vs αs := by
  simp only [nabla_tensor_eval]
  -- embed(X+Y) = embed X + embed Y
  simp only [show ∀ g, (emb.embed (X + Y)) g = (emb.embed X) g + (emb.embed Y) g from
    fun g => by simp [map_add, Derivation.add_apply]]
  -- conn(X+Y, v) = conn(X, v) + conn(Y, v)
  simp only [conn_add_left]
  -- nabla_dual(X+Y, α) = nabla_dual(X, α) + nabla_dual(Y, α)
  simp only [show ∀ α, nabla_dual emb conn ha hl (X + Y) α =
      nabla_dual emb conn ha hl X α + nabla_dual emb conn ha hl Y α from fun α => by
    ext v; simp [nabla_dual, map_add, Derivation.add_apply, conn_add_left]; ring]
  -- Vector correction: T multilinear in the updated argument
  simp only [show ∀ i, T (Function.update vs i (conn X (vs i) + conn Y (vs i))) αs =
      T (Function.update vs i (conn X (vs i))) αs +
      T (Function.update vs i (conn Y (vs i))) αs from fun i => by
    have := congr_arg (· αs) (T.map_update_add vs i (conn X (vs i)) (conn Y (vs i)))
    simp [MultilinearMap.add_apply]]
  simp only [Finset.sum_add_distrib]
  -- Covector correction: T multilinear in covector argument
  simp only [show ∀ j, T vs (Function.update αs j
      (nabla_dual emb conn ha hl X (αs j) + nabla_dual emb conn ha hl Y (αs j))) =
      T vs (Function.update αs j (nabla_dual emb conn ha hl X (αs j))) +
      T vs (Function.update αs j (nabla_dual emb conn ha hl Y (αs j))) from fun j => by
    have := (T vs).map_update_add αs j
      (nabla_dual emb conn ha hl X (αs j)) (nabla_dual emb conn ha hl Y (αs j))
    simp]
  simp only [Finset.sum_add_distrib]; ring

/-- ∇_X(δ) = 0 — covariant derivative of the identity (1,1)-tensor vanishes. -/
theorem nabla_delta (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) :
    nabla_tensor emb conn ha hl X (delta_tensor : TensorData R V 1 1) = 0 := by
  ext vs αs
  rw [nabla_tensor_eval]
  simp only [MultilinearMap.zero_apply]
  -- delta_tensor eval: δ(m)(n) = n 0 (m 0)
  -- s = 1, r = 1: both sums are singletons over Fin 1
  simp only [Finset.univ_unique, Finset.sum_singleton]
  -- Unfold everything to scalar expressions
  simp [delta_tensor, endo_to_tensor, nabla_dual]

/-- ∇_X commutes with swap_covariant. -/
theorem nabla_swap (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (i j : Fin s) (T : TensorData R V r s) (vs αs) :
    nabla_tensor emb conn ha hl X (swap_covariant i j T) vs αs =
    swap_covariant i j (nabla_tensor emb conn ha hl X T) vs αs := by
  simp only [nabla_tensor_eval, swap_covariant_eval]
  -- Leading X term and covector sum are identical on both sides.
  -- Only the vector correction sum differs.
  -- LHS: Σ_l T((update vs l (conn X (vs l))) ∘ σ)(αs)
  -- RHS: Σ_l T(update (vs ∘ σ) l (conn X ((vs ∘ σ) l)))(αs)
  congr 1; congr 1
  -- Need: Σ_l T((update vs l (conn X (vs l))) ∘ σ)(αs)
  --     = Σ_l T(update (vs∘σ) l (conn X ((vs∘σ) l)))(αs)
  -- Step 1: (update vs l v) ∘ σ = update (vs ∘ σ) (σ l) v  [for injective σ]
  -- Step 2: vs l = (vs ∘ σ)(σ l)  [since σ(σ l) = l for swap]
  -- Step 3: Re-index Σ_l by σ: Σ_l f(σ l) = Σ_l f(l)
  -- Combine: each summand T((update vs l ...) ∘ σ) = T(update (vs∘σ) (σ l) ...)
  -- then after re-indexing l ↦ σ l we get the RHS.
  -- LHS sum: Σ_l T((update vs l (conn X (vs l))) ∘ σ)(αs)
  -- RHS sum: Σ_l T(update (vs∘σ) l (conn X ((vs∘σ) l)))(αs)
  -- Strategy: re-index LHS by σ (bijection on Fin s), then show each term matches.
  -- Finset.sum_equiv σ: Σ_{l∈s} f(l) = Σ_{l∈s} g(l) if f(σ l) = g(l) for all l.
  refine Finset.sum_equiv (Equiv.swap i j) (fun _ => by simp) (fun l _ => ?_)
  -- Goal: T(update vs l (conn X (vs l)) ∘ σ)(αs) = T(update (vs∘σ) (σ l) (conn X ((vs∘σ)(σ l))))(αs)
  -- Suffices to show the Fin s → V arguments are equal pointwise.
  have h_arg : Function.update vs l (conn X (vs l)) ∘ (Equiv.swap i j) =
      Function.update (vs ∘ (Equiv.swap i j)) ((Equiv.swap i j) l)
        (conn X (vs ((Equiv.swap i j) ((Equiv.swap i j) l)))) := by
    ext k
    simp only [Function.update_apply, Function.comp_apply]
    -- σ(k) = l ↔ k = σ(l) since σ is involutive
    by_cases hk : k = (Equiv.swap i j) l
    · simp [hk, Equiv.swap_apply_self]
    · have : (Equiv.swap i j) k ≠ l := by
        intro h; exact hk (by rw [← h, Equiv.swap_apply_self])
      simp [this, hk]
  rw [h_arg]; rfl

/-- ∇_X(T₁ ⊗ T₂) = (∇_X T₁) ⊗ T₂ + T₁ ⊗ (∇_X T₂) — Leibniz rule for ⊗. -/
theorem nabla_tensor_prod (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r₁ s₁ r₂ s₂ : ℕ}
    (T₁ : TensorData R V r₁ s₁) (T₂ : TensorData R V r₂ s₂) :
    nabla_tensor emb conn ha hl X (tensor_prod T₁ T₂) =
    tensor_prod (nabla_tensor emb conn ha hl X T₁) T₂ +
    tensor_prod T₁ (nabla_tensor emb conn ha hl X T₂) := by
  ext vs αs
  simp only [nabla_tensor_eval, tensor_prod_eval, MultilinearMap.add_apply]
  -- Abbreviations
  set vs₁ := vs ∘ Fin.castAdd s₂; set vs₂ := vs ∘ Fin.natAdd s₁
  set ns₁ := αs ∘ Fin.castAdd r₂; set ns₂ := αs ∘ Fin.natAdd r₁
  set a := T₁ vs₁ ns₁; set b := T₂ vs₂ ns₂
  -- A) Leading term: X(a*b) = X(a)*b + a*X(b)
  rw [embed_leibniz' emb X]
  -- B) Vector sum: each summand is tensor_prod_eval of an updated vs.
  -- For i.val < s₁: update hits T₁'s slots, T₂ unchanged → T₁(update)*T₂
  -- For i.val ≥ s₁: update hits T₂'s slots, T₁ unchanged → T₁*T₂(update)
  -- h_vec_lo: for i in the first s₁ slots, the update hits T₁ only
  have h_vec_lo : ∀ (i₁ : Fin s₁),
      T₁ (Function.update vs (Fin.castAdd s₂ i₁) (conn X (vs (Fin.castAdd s₂ i₁))) ∘ Fin.castAdd s₂) ns₁ *
      T₂ (Function.update vs (Fin.castAdd s₂ i₁) (conn X (vs (Fin.castAdd s₂ i₁))) ∘ Fin.natAdd s₁) ns₂ =
      T₁ (Function.update vs₁ i₁ (conn X (vs₁ i₁))) ns₁ * b := by
    intro i₁
    have hc : ∀ v, Function.update vs (Fin.castAdd s₂ i₁) v ∘ Fin.castAdd s₂ =
        Function.update vs₁ i₁ v := fun v =>
      Function.update_comp_eq_of_injective vs (Fin.castAdd_injective s₁ s₂) i₁ v
    have hn : ∀ v, Function.update vs (Fin.castAdd s₂ i₁) v ∘ Fin.natAdd s₁ = vs₂ := fun v =>
      Function.update_comp_eq_of_forall_ne vs v
        (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]; omega)
    simp only [hc, hn]; rfl  -- vs₁ i₁ = vs (castAdd s₂ i₁) definitionally
  -- h_vec_hi: for i in the last s₂ slots, the update hits T₂ only
  have h_vec_hi : ∀ (i₂ : Fin s₂),
      T₁ (Function.update vs (Fin.natAdd s₁ i₂) (conn X (vs (Fin.natAdd s₁ i₂))) ∘ Fin.castAdd s₂) ns₁ *
      T₂ (Function.update vs (Fin.natAdd s₁ i₂) (conn X (vs (Fin.natAdd s₁ i₂))) ∘ Fin.natAdd s₁) ns₂ =
      a * T₂ (Function.update vs₂ i₂ (conn X (vs₂ i₂))) ns₂ := by
    intro i₂
    have hc : ∀ v, Function.update vs (Fin.natAdd s₁ i₂) v ∘ Fin.natAdd s₁ =
        Function.update vs₂ i₂ v := fun v =>
      Function.update_comp_eq_of_injective vs (Fin.natAdd_injective s₂ s₁) i₂ v
    have hn : ∀ v, Function.update vs (Fin.natAdd s₁ i₂) v ∘ Fin.castAdd s₂ = vs₁ := fun v =>
      Function.update_comp_eq_of_forall_ne vs v
        (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]; omega)
    simp only [hc, hn]; rfl  -- vs₂ i₂ = vs (natAdd s₁ i₂) definitionally
  -- C) Covector sum: same lo/hi splitting for Fin(r₁+r₂)
  have h_cov_lo : ∀ (j₁ : Fin r₁),
      T₁ vs₁ (Function.update αs (Fin.castAdd r₂ j₁) (nabla_dual emb conn ha hl X (αs (Fin.castAdd r₂ j₁))) ∘ Fin.castAdd r₂) *
      T₂ vs₂ (Function.update αs (Fin.castAdd r₂ j₁) (nabla_dual emb conn ha hl X (αs (Fin.castAdd r₂ j₁))) ∘ Fin.natAdd r₁) =
      T₁ vs₁ (Function.update ns₁ j₁ (nabla_dual emb conn ha hl X (ns₁ j₁))) * b := by
    intro j₁
    have hc : ∀ v, Function.update αs (Fin.castAdd r₂ j₁) v ∘ Fin.castAdd r₂ =
        Function.update ns₁ j₁ v := fun v =>
      Function.update_comp_eq_of_injective αs (Fin.castAdd_injective r₁ r₂) j₁ v
    have hn : ∀ v, Function.update αs (Fin.castAdd r₂ j₁) v ∘ Fin.natAdd r₁ = ns₂ := fun v =>
      Function.update_comp_eq_of_forall_ne αs v
        (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]; omega)
    simp only [hc, hn]; rfl
  have h_cov_hi : ∀ (j₂ : Fin r₂),
      T₁ vs₁ (Function.update αs (Fin.natAdd r₁ j₂) (nabla_dual emb conn ha hl X (αs (Fin.natAdd r₁ j₂))) ∘ Fin.castAdd r₂) *
      T₂ vs₂ (Function.update αs (Fin.natAdd r₁ j₂) (nabla_dual emb conn ha hl X (αs (Fin.natAdd r₁ j₂))) ∘ Fin.natAdd r₁) =
      a * T₂ vs₂ (Function.update ns₂ j₂ (nabla_dual emb conn ha hl X (ns₂ j₂))) := by
    intro j₂
    have hc : ∀ v, Function.update αs (Fin.natAdd r₁ j₂) v ∘ Fin.natAdd r₁ =
        Function.update ns₂ j₂ v := fun v =>
      Function.update_comp_eq_of_injective αs (Fin.natAdd_injective r₂ r₁) j₂ v
    have hn : ∀ v, Function.update αs (Fin.natAdd r₁ j₂) v ∘ Fin.castAdd r₂ = ns₁ := fun v =>
      Function.update_comp_eq_of_forall_ne αs v
        (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]; omega)
    simp only [hc, hn]; rfl
  -- D) Split each sum: ∑_{Fin(n₁+n₂)} f = ∑_{Fin n₁} f∘castAdd + ∑_{Fin n₂} f∘natAdd
  -- Then rewrite each half via h_vec_lo/hi (or h_cov_lo/hi) and factor constants.
  have h_vec_sum :
      ∑ i : Fin (s₁ + s₂),
        T₁ (Function.update vs i (conn X (vs i)) ∘ Fin.castAdd s₂) ns₁ *
        T₂ (Function.update vs i (conn X (vs i)) ∘ Fin.natAdd s₁) ns₂ =
      (∑ i₁ : Fin s₁, T₁ (Function.update vs₁ i₁ (conn X (vs₁ i₁))) ns₁) * b +
      a * ∑ i₂ : Fin s₂, T₂ (Function.update vs₂ i₂ (conn X (vs₂ i₂))) ns₂ := by
    conv_lhs => rw [show ∑ i : Fin (s₁ + s₂), _ =
        (∑ i₁ : Fin s₁, T₁ (Function.update vs₁ i₁ (conn X (vs₁ i₁))) ns₁ * b) +
        ∑ i₂ : Fin s₂, a * T₂ (Function.update vs₂ i₂ (conn X (vs₂ i₂))) ns₂ from by
      rw [Fin.sum_univ_add]
      exact congr_arg₂ (· + ·)
        (Finset.sum_congr rfl (fun i₁ _ => h_vec_lo i₁))
        (Finset.sum_congr rfl (fun i₂ _ => h_vec_hi i₂))]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have h_cov_sum :
      ∑ j : Fin (r₁ + r₂),
        T₁ vs₁ (Function.update αs j (nabla_dual emb conn ha hl X (αs j)) ∘ Fin.castAdd r₂) *
        T₂ vs₂ (Function.update αs j (nabla_dual emb conn ha hl X (αs j)) ∘ Fin.natAdd r₁) =
      (∑ j₁ : Fin r₁, T₁ vs₁ (Function.update ns₁ j₁ (nabla_dual emb conn ha hl X (ns₁ j₁)))) * b +
      a * ∑ j₂ : Fin r₂, T₂ vs₂ (Function.update ns₂ j₂ (nabla_dual emb conn ha hl X (ns₂ j₂))) := by
    conv_lhs => rw [show ∑ j : Fin (r₁ + r₂), _ =
        (∑ j₁ : Fin r₁, T₁ vs₁ (Function.update ns₁ j₁ (nabla_dual emb conn ha hl X (ns₁ j₁))) * b) +
        ∑ j₂ : Fin r₂, a * T₂ vs₂ (Function.update ns₂ j₂ (nabla_dual emb conn ha hl X (ns₂ j₂))) from by
      rw [Fin.sum_univ_add]
      exact congr_arg₂ (· + ·)
        (Finset.sum_congr rfl (fun j₁ _ => h_cov_lo j₁))
        (Finset.sum_congr rfl (fun j₂ _ => h_cov_hi j₂))]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  -- E) Combine everything
  rw [h_vec_sum, h_cov_sum]; ring

/-- ∇_X commutes with trace: X(tr L) = tr([∇_X, L]).
    This is a DIRECT corollary of the NablaTrComm hypothesis. -/
theorem nabla_contract (emb : DerivationEmbedding k R V)
    (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V)
    (h_ntr : NablaTrComm emb atr conn ha hl)
    (X : V) (L : V →ₗ[R] V) :
    (emb.embed X) (atr.tr L) = atr.tr (commutatorEndo
      (emb.embed X).toFun (conn X) (ha X) (hl X) L) :=
  h_ntr X L

end NablaTensor
