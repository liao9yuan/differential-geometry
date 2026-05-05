import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import DifferentialGeometry.Synthetic.Algebra.VectorFieldAlgebra

/-!
# Tensor Algebra

`TensorData R V r s` is a type alias for `MultilinearMap`.
Contraction uses `AbstractTrace.tr`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SyntheticTensor

-- ============================================================
-- TensorData: the transparent tensor type
-- ============================================================

/-- A (r,s)-tensor is a multilinear map: s vectors → r covectors → scalar. -/
abbrev TensorData (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    (r s : ℕ) :=
  MultilinearMap R (fun _ : Fin s => V)
    (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)

/-- AbstractTensor is definitionally TensorData. -/
abbrev AbstractTensor (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
    (r s : ℕ) := TensorData R V r s

-- ============================================================
-- Basic helpers
-- ============================================================

section Helpers
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Evaluation linear map: evaluates a covector at a vector. -/
def evalLinear (v : V) : (V →ₗ[R] R) →ₗ[R] R where
  toFun α := α v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Scalar as a (0,0)-tensor. -/
def scalarToData (f : R) : TensorData R V 0 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => (V →ₗ[R] R)) f)

/-- Vector as a (1,0)-tensor: v ↦ (α ↦ α(v)). -/
def vectorToData (v : V) : TensorData R V 1 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.ofSubsingleton R (V →ₗ[R] R) R (0 : Fin 1) (evalLinear v))

/-- Covector as a (0,1)-tensor: α ↦ (v ↦ α(v)). -/
def covectorToData (α : V →ₗ[R] R) : TensorData R V 0 1 where
  toFun m := MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => (V →ₗ[R] R)) (α (m 0))
  map_update_add' m i x y := by
    have hi : i = 0 := Subsingleton.elim _ _; subst hi
    simp only [Function.update_self]
    ext n; simp only [MultilinearMap.constOfIsEmpty_apply, MultilinearMap.add_apply]
    exact map_add α x y
  map_update_smul' m i c x := by
    have hi : i = 0 := Subsingleton.elim _ _; subst hi
    simp only [Function.update_self]
    ext n; simp only [MultilinearMap.constOfIsEmpty_apply, MultilinearMap.smul_apply, smul_eq_mul]
    exact α.map_smul c x

@[simp] theorem covectorToData_eval (α : V →ₗ[R] R) (v : V) :
    covectorToData (R := R) α ![v] ![] = α v := rfl

end Helpers

-- ============================================================
-- Tensor evaluation and extensionality
-- ============================================================

section EvalExt
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Evaluate a tensor at vectors and covectors. -/
def tensor_eval {r s : ℕ} (T : TensorData R V r s)
    (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) : R :=
  T vs αs

/-- Tensor extensionality: two tensors are equal iff they agree on all inputs. -/
theorem tensor_ext {r s : ℕ} (T₁ T₂ : TensorData R V r s)
    (h : ∀ vs αs, tensor_eval T₁ vs αs = tensor_eval T₂ vs αs) : T₁ = T₂ := by
  ext vs αs; exact h vs αs

end EvalExt

-- ============================================================
-- Swap operations
-- ============================================================

section Swap
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Swap two covariant (vector) slots. -/
def swap_covariant {r s : ℕ} (i j : Fin s) (T : TensorData R V r s) :
    TensorData R V r s :=
  T.domDomCongr (Equiv.swap i j)

/-- Swap two contravariant (covector) slots. -/
def swap_contravariant {r s : ℕ} (i j : Fin r) (T : TensorData R V r s) :
    TensorData R V r s where
  toFun m := (T m).domDomCongr (Equiv.swap i j)
  map_update_add' := by
    intro _ m k x y; ext n
    change (T (Function.update m k (x + y))) (n ∘ Equiv.swap i j) =
         (T (Function.update m k x)) (n ∘ Equiv.swap i j) +
         (T (Function.update m k y)) (n ∘ Equiv.swap i j)
    rw [T.map_update_add]; rfl
  map_update_smul' := by
    intro _ m k c x; ext n
    change (T (Function.update m k (c • x))) (n ∘ Equiv.swap i j) =
         c • (T (Function.update m k x)) (n ∘ Equiv.swap i j)
    rw [T.map_update_smul]; rfl

theorem swap_covariant_eval {r s : ℕ} (i j : Fin s) (T : TensorData R V r s)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) :
    swap_covariant i j T m n = T (m ∘ Equiv.swap i j) n := rfl

theorem swap_contravariant_eval {r s : ℕ} (i j : Fin r) (T : TensorData R V r s)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) :
    swap_contravariant i j T m n = T m (n ∘ Equiv.swap i j) := rfl

end Swap

-- ============================================================
-- Tensor product
-- ============================================================

section TensorProd
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Tensor product: (T₁ ⊗ T₂)(m₁m₂)(n₁n₂) = T₁(m₁)(n₁) * T₂(m₂)(n₂). -/
noncomputable def tensor_prod {r₁ s₁ r₂ s₂ : ℕ}
    (T₁ : TensorData R V r₁ s₁) (T₂ : TensorData R V r₂ s₂) :
    TensorData R V (r₁ + r₂) (s₁ + s₂) where
  toFun m :=
    { toFun := fun n =>
        T₁ (m ∘ Fin.castAdd s₂) (n ∘ Fin.castAdd r₂) *
        T₂ (m ∘ Fin.natAdd s₁) (n ∘ Fin.natAdd r₁)
      map_update_add' := by
        intro _ n i x y
        by_cases h : i.val < r₁
        · let j : Fin r₁ := ⟨i.val, h⟩
          have hj : Fin.castAdd r₂ j = i := Fin.ext rfl
          have hc : ∀ v, Function.update n i v ∘ Fin.castAdd r₂ =
              Function.update (n ∘ Fin.castAdd r₂) j v := fun v => by
            rw [← hj]; exact Function.update_comp_eq_of_injective n
              (Fin.castAdd_injective r₁ r₂) j v
          have hn : ∀ v, Function.update n i v ∘ Fin.natAdd r₁ = n ∘ Fin.natAdd r₁ := fun v =>
            Function.update_comp_eq_of_forall_ne n v
              (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
          simp only [hc, hn, (T₁ (m ∘ Fin.castAdd s₂)).map_update_add]
          ring
        · push Not at h
          let j : Fin r₂ := ⟨i.val - r₁, by omega⟩
          have hj : Fin.natAdd r₁ j = i := Fin.ext (by change r₁ + (i.val - r₁) = i.val; omega)
          have hc : ∀ v, Function.update n i v ∘ Fin.natAdd r₁ =
              Function.update (n ∘ Fin.natAdd r₁) j v := fun v => by
            rw [← hj]; exact Function.update_comp_eq_of_injective n
              (Fin.natAdd_injective r₂ r₁) j v
          have hn : ∀ v, Function.update n i v ∘ Fin.castAdd r₂ = n ∘ Fin.castAdd r₂ := fun v =>
            Function.update_comp_eq_of_forall_ne n v
              (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
          simp only [hc, hn, (T₂ (m ∘ Fin.natAdd s₁)).map_update_add]
          ring
      map_update_smul' := by
        intro _ n i c x
        by_cases h : i.val < r₁
        · let j : Fin r₁ := ⟨i.val, h⟩
          have hj : Fin.castAdd r₂ j = i := Fin.ext rfl
          have hc : ∀ v, Function.update n i v ∘ Fin.castAdd r₂ =
              Function.update (n ∘ Fin.castAdd r₂) j v := fun v => by
            rw [← hj]; exact Function.update_comp_eq_of_injective n
              (Fin.castAdd_injective r₁ r₂) j v
          have hn : ∀ v, Function.update n i v ∘ Fin.natAdd r₁ = n ∘ Fin.natAdd r₁ := fun v =>
            Function.update_comp_eq_of_forall_ne n v
              (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
          simp only [hc, hn, (T₁ (m ∘ Fin.castAdd s₂)).map_update_smul, smul_eq_mul]
          ring
        · push Not at h
          let j : Fin r₂ := ⟨i.val - r₁, by omega⟩
          have hj : Fin.natAdd r₁ j = i := Fin.ext (by change r₁ + (i.val - r₁) = i.val; omega)
          have hc : ∀ v, Function.update n i v ∘ Fin.natAdd r₁ =
              Function.update (n ∘ Fin.natAdd r₁) j v := fun v => by
            rw [← hj]; exact Function.update_comp_eq_of_injective n
              (Fin.natAdd_injective r₂ r₁) j v
          have hn : ∀ v, Function.update n i v ∘ Fin.castAdd r₂ = n ∘ Fin.castAdd r₂ := fun v =>
            Function.update_comp_eq_of_forall_ne n v
              (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
          simp only [hc, hn, (T₂ (m ∘ Fin.natAdd s₁)).map_update_smul, smul_eq_mul]
          ring }
  map_update_add' := by
    intro _ m i x y; ext n
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    by_cases h : i.val < s₁
    · let j : Fin s₁ := ⟨i.val, h⟩
      have hj : Fin.castAdd s₂ j = i := Fin.ext rfl
      have hc : ∀ v, Function.update m i v ∘ Fin.castAdd s₂ =
          Function.update (m ∘ Fin.castAdd s₂) j v := fun v => by
        rw [← hj]; exact Function.update_comp_eq_of_injective m
          (Fin.castAdd_injective s₁ s₂) j v
      have hn : ∀ v, Function.update m i v ∘ Fin.natAdd s₁ = m ∘ Fin.natAdd s₁ := fun v =>
        Function.update_comp_eq_of_forall_ne m v
          (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
      simp only [hc, hn, T₁.map_update_add, MultilinearMap.add_apply]
      ring
    · push Not at h
      let j : Fin s₂ := ⟨i.val - s₁, by omega⟩
      have hj : Fin.natAdd s₁ j = i := Fin.ext (by change s₁ + (i.val - s₁) = i.val; omega)
      have hc : ∀ v, Function.update m i v ∘ Fin.natAdd s₁ =
          Function.update (m ∘ Fin.natAdd s₁) j v := fun v => by
        rw [← hj]; exact Function.update_comp_eq_of_injective m
          (Fin.natAdd_injective s₂ s₁) j v
      have hn : ∀ v, Function.update m i v ∘ Fin.castAdd s₂ = m ∘ Fin.castAdd s₂ := fun v =>
        Function.update_comp_eq_of_forall_ne m v
          (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
      simp only [hc, hn, T₂.map_update_add, MultilinearMap.add_apply]
      ring
  map_update_smul' := by
    intro _ m i c x; ext n
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    by_cases h : i.val < s₁
    · let j : Fin s₁ := ⟨i.val, h⟩
      have hj : Fin.castAdd s₂ j = i := Fin.ext rfl
      have hc : ∀ v, Function.update m i v ∘ Fin.castAdd s₂ =
          Function.update (m ∘ Fin.castAdd s₂) j v := fun v => by
        rw [← hj]; exact Function.update_comp_eq_of_injective m
          (Fin.castAdd_injective s₁ s₂) j v
      have hn : ∀ v, Function.update m i v ∘ Fin.natAdd s₁ = m ∘ Fin.natAdd s₁ := fun v =>
        Function.update_comp_eq_of_forall_ne m v
          (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
      simp only [hc, hn, T₁.map_update_smul, MultilinearMap.smul_apply, smul_eq_mul]
      ring
    · push Not at h
      let j : Fin s₂ := ⟨i.val - s₁, by omega⟩
      have hj : Fin.natAdd s₁ j = i := Fin.ext (by change s₁ + (i.val - s₁) = i.val; omega)
      have hc : ∀ v, Function.update m i v ∘ Fin.natAdd s₁ =
          Function.update (m ∘ Fin.natAdd s₁) j v := fun v => by
        rw [← hj]; exact Function.update_comp_eq_of_injective m
          (Fin.natAdd_injective s₂ s₁) j v
      have hn : ∀ v, Function.update m i v ∘ Fin.castAdd s₂ = m ∘ Fin.castAdd s₂ := fun v =>
        Function.update_comp_eq_of_forall_ne m v
          (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
      simp only [hc, hn, T₂.map_update_smul, MultilinearMap.smul_apply, smul_eq_mul]
      ring

theorem tensor_prod_eval {r₁ s₁ r₂ s₂ : ℕ}
    (T₁ : TensorData R V r₁ s₁) (T₂ : TensorData R V r₂ s₂)
    (m : Fin (s₁ + s₂) → V) (n : Fin (r₁ + r₂) → (V →ₗ[R] R)) :
    tensor_prod T₁ T₂ m n =
    T₁ (m ∘ Fin.castAdd s₂) (n ∘ Fin.castAdd r₂) *
    T₂ (m ∘ Fin.natAdd s₁) (n ∘ Fin.natAdd r₁) := rfl

end TensorProd

-- ============================================================
-- Covector from tensor (via curryLeft) — needed before AbstractTrace
-- ============================================================

section CovectorFromTensor
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Extract a covector from a tensor by fixing remaining slots.
    φ(w) = D(Fin.cons w m)(n), linear in w via curryLeft. -/
def covector_from_tensor {r s : ℕ} (D : TensorData R V r (s + 1))
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) : V →ₗ[R] R where
  toFun w := D (Fin.cons w m) n
  map_add' x y := by
    change D.curryLeft (x + y) m n = D.curryLeft x m n + D.curryLeft y m n
    rw [D.curryLeft.map_add, MultilinearMap.add_apply, MultilinearMap.add_apply]
  map_smul' c x := by
    change D.curryLeft (c • x) m n = c • (D.curryLeft x m n)
    rw [D.curryLeft.map_smul, MultilinearMap.smul_apply, MultilinearMap.smul_apply]

end CovectorFromTensor

-- ============================================================
-- Endomorphism → (1,1)-tensor (needed before AbstractTrace)
-- ============================================================

section EndoToTensorDef
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Convert an endomorphism to a (1,1)-tensor: T_L(v)(α) = α(L(v)).
    Defined before AbstractTrace so it can appear in the structure. -/
def endo_to_tensor (L : V →ₗ[R] V) : TensorData R V 1 1 where
  toFun m :=
    { toFun := fun n => n 0 (L (m 0))
      map_update_add' := by
        intro _ n i x y
        have hi := Subsingleton.elim i 0; subst hi
        simp [Function.update_self]
      map_update_smul' := by
        intro _ n i c x
        have hi := Subsingleton.elim i 0; subst hi
        simp [Function.update_self, smul_eq_mul] }
  map_update_add' := by
    intro _ m i x y; ext n
    have hi := Subsingleton.elim i 0; subst hi
    simp only [Function.update_self, MultilinearMap.coe_mk, MultilinearMap.add_apply, map_add]
  map_update_smul' := by
    intro _ m i c x; ext n
    have hi := Subsingleton.elim i 0; subst hi
    simp only [Function.update_self, MultilinearMap.coe_mk, MultilinearMap.smul_apply,
      smul_eq_mul, map_smul]

theorem endo_to_tensor_eval (L : V →ₗ[R] V) (v : V) (α : V →ₗ[R] R) :
    endo_to_tensor L ![v] ![α] = α (L v) := rfl

end EndoToTensorDef

-- ============================================================
-- AbstractTrace: trace on End(V) + general tensor contraction
-- ============================================================

/-- Abstract trace on endomorphisms of V, plus general tensor contraction.
    NOT Mathlib's `LinearMap.trace` (which needs `Module.Free` = parallelizable manifold).
    - `tr` : trace on endomorphisms V →ₗ[R] V
    - `tensor_contract` : general (r+1, s+1) → (r, s) contraction
    - `data_eval_single_contract` : connects tensor_contract to evaluation -/
structure AbstractTrace (R V : Type*)
    [CommRing R] [AddCommGroup V] [Module R V] where
  /-- Trace on endomorphisms. -/
  tr : (V →ₗ[R] V) →ₗ[R] R
  /-- tr(α.smulRight v) = α(v) -/
  trace_outer : ∀ (v : V) (α : V →ₗ[R] R), tr (α.smulRight v) = α v
  /-- tr(AB) = tr(BA) -/
  trace_comm : ∀ (A B : V →ₗ[R] V), tr (A * B) = tr (B * A)
  /-- General contraction: (r+1, s+1) → (r, s). Contracts first co/contra pair. -/
  tensor_contract {r s : ℕ} :
    TensorData R V (r + 1) (s + 1) → TensorData R V r s
  /-- tensor_contract is additive. -/
  tensor_contract_add {r s : ℕ} (T₁ T₂ : TensorData R V (r + 1) (s + 1)) :
    tensor_contract (T₁ + T₂) = tensor_contract T₁ + tensor_contract T₂
  /-- tensor_contract is R-linear. -/
  tensor_contract_smul {r s : ℕ} (c : R) (T : TensorData R V (r + 1) (s + 1)) :
    tensor_contract (c • T) = c • tensor_contract T
  /-- Evaluation axiom: contract(vectorToData(v) ⊗ D) = D evaluated with v in first co slot.
      Uses the "vectorToData first" argument order so that the lone contravariant slot from
      `vectorToData v` sits at position 0, matching `tensor_contract`'s first/first pairing. -/
  data_eval_single_contract {r s : ℕ}
    (D : TensorData R V r (s + 1)) (v : V)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) :
    (tensor_contract
      ((show 1 + r = r + 1 from by omega) ▸
       (show 0 + (s + 1) = s + 1 from by omega) ▸
       tensor_prod (r₁ := 1) (s₁ := 0) (r₂ := r) (s₂ := s + 1)
         (vectorToData (R := R) v) D)) m n =
    D (Fin.cons v m) n
  /-- Dual evaluation axiom: contracting a (0, s₁+1)-tensor A with a (r+1, s₂)-tensor B
      pairs A's first covariant slot with B's first contravariant slot.
      The result plugs the covector `v ↦ A(v, m₁)` into B's first contra slot.
      When A = covectorToData(α) (s₁ = 0), this reduces to plugging α directly. -/
  data_eval_single_contract_dual {r s₁ s₂ : ℕ}
    (A : TensorData R V 0 (s₁ + 1)) (B : TensorData R V (r + 1) s₂)
    (m : Fin (s₁ + s₂) → V) (n : Fin r → (V →ₗ[R] R)) :
    (tensor_contract
      ((show 0 + (r + 1) = r + 1 from by omega) ▸
       (show (s₁ + 1) + s₂ = (s₁ + s₂) + 1 from by omega) ▸
       tensor_prod (r₁ := 0) (s₁ := s₁ + 1) (r₂ := r + 1) (s₂ := s₂) A B)) m n =
    B (m ∘ Fin.natAdd s₁) (Fin.cons (covector_from_tensor A (m ∘ Fin.castAdd s₂) ![]) n)
  /-- Consistency: tensor_contract on the (1,1)-tensor representation of an endomorphism
      agrees with tr. In any basis model this is immediate from the coordinate definition. -/
  tensor_contract_endo (L : V →ₗ[R] V) :
    (tensor_contract (endo_to_tensor L)) ![] ![] = tr L

-- ============================================================
-- Scalar and vector operations
-- ============================================================

section ScalarVector
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def toScalar (T : TensorData R V 0 0) : R := T ![] ![]
def fromScalar (f : R) : TensorData R V 0 0 := scalarToData f
def fromVector (v : V) : TensorData R V 1 0 := vectorToData v

theorem toScalar_fromScalar (f : R) : toScalar (fromScalar f : TensorData R V 0 0) = f := rfl

theorem fromVector_eval (v : V) (α : V →ₗ[R] R) :
    vectorToData (R := R) v ![] ![α] = α v := rfl

end ScalarVector

-- ============================================================
-- Delta tensor, outerProduct (endo_to_tensor moved before AbstractTrace)
-- ============================================================

section EndoTensor
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Kronecker delta tensor = identity endomorphism as (1,1)-tensor. -/
def delta_tensor : TensorData R V 1 1 := endo_to_tensor LinearMap.id

theorem delta_tensor_eval (v : V) (α : V →ₗ[R] R) :
    (delta_tensor : TensorData R V 1 1) ![v] ![α] = α v := rfl

/-- Outer product as an endomorphism: (α.smulRight v)(w) = α(w) • v. -/
def outerProduct (v : V) (α : V →ₗ[R] R) : V →ₗ[R] V := α.smulRight v

end EndoTensor

-- ============================================================
-- Contraction via AbstractTrace
-- ============================================================

section Contract
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Contract (trace) an endomorphism using AbstractTrace. -/
def contract (atr : AbstractTrace R V) (L : V →ₗ[R] V) : R := atr.tr L

/-- Contraction of outer product = evaluation (from trace_outer). -/
theorem contract_outerProduct (atr : AbstractTrace R V) (v : V) (α : V →ₗ[R] R) :
    contract atr (outerProduct v α) = α v :=
  atr.trace_outer v α

/-- Contraction commutes: tr(AB) = tr(BA). -/
theorem contract_comm (atr : AbstractTrace R V) (A B : V →ₗ[R] V) :
    contract atr (A * B) = contract atr (B * A) :=
  atr.trace_comm A B

theorem contract_add (atr : AbstractTrace R V) (L₁ L₂ : V →ₗ[R] V) :
    contract atr (L₁ + L₂) = contract atr L₁ + contract atr L₂ :=
  map_add atr.tr L₁ L₂

theorem contract_smul (atr : AbstractTrace R V) (c : R) (L : V →ₗ[R] V) :
    contract atr (c • L) = c * contract atr L := by
  change atr.tr (c • L) = c * atr.tr L
  rw [map_smul]; rfl

end Contract

-- ============================================================
-- Evaluation theorem (uses covector_from_tensor from above)
-- ============================================================

section EvalContract
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Build the endomorphism for data_eval_single_contract:
    w ↦ φ(w) • v where φ(w) = D(Fin.cons w m)(n). -/
def eval_endo {r s : ℕ} (D : TensorData R V r (s + 1)) (v : V)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) : V →ₗ[R] V :=
  outerProduct v (covector_from_tensor D m n)

/-- The key evaluation theorem: contracting the endomorphism built from
    D and v gives D evaluated at v. Uses trace_outer from AbstractTrace. -/
theorem data_eval_single_contract (atr : AbstractTrace R V) {r s : ℕ}
    (D : TensorData R V r (s + 1)) (v : V)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) :
    contract atr (eval_endo D v m n) = D (Fin.cons v m) n := by
  unfold contract eval_endo outerProduct
  rw [atr.trace_outer]
  rfl

end EvalContract

-- ============================================================
-- Bilinearity of tensor operations
-- ============================================================

section Bilinearity
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem tensor_eval_add {r s : ℕ} (T₁ T₂ : TensorData R V r s)
    (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) :
    tensor_eval (T₁ + T₂) vs αs = tensor_eval T₁ vs αs + tensor_eval T₂ vs αs := by
  simp [tensor_eval, MultilinearMap.add_apply]

theorem tensor_eval_smul {r s : ℕ} (c : R) (T : TensorData R V r s)
    (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) :
    tensor_eval (c • T) vs αs = c * tensor_eval T vs αs := by
  simp [tensor_eval, MultilinearMap.smul_apply, smul_eq_mul]

theorem vectorToData_add (X Y : V) :
    vectorToData (R := R) (X + Y) = vectorToData X + vectorToData Y := by
  ext m n
  simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton,
    LinearMap.map_add]

theorem vectorToData_smul (c : R) (X : V) :
    vectorToData (R := R) (c • X) = c • vectorToData X := by
  ext m n
  simp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton,
    smul_eq_mul]

end Bilinearity

-- ============================================================
-- General contraction via index permutation + tensor_contract
-- ============================================================

section GeneralContract
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- General contraction at specified index pair (i, j):
    permute indices so that i→0 (contra) and j→0 (cov), then tensor_contract. -/
def contract_general (atr : AbstractTrace R V) {r s : ℕ}
    (i : Fin (r + 1)) (j : Fin (s + 1))
    (T : TensorData R V (r + 1) (s + 1)) : TensorData R V r s :=
  atr.tensor_contract (swap_covariant 0 j (swap_contravariant 0 i T))

theorem contract_general_add (atr : AbstractTrace R V) {r s : ℕ}
    (i : Fin (r + 1)) (j : Fin (s + 1))
    (T₁ T₂ : TensorData R V (r + 1) (s + 1)) :
    contract_general atr i j (T₁ + T₂) =
    contract_general atr i j T₁ + contract_general atr i j T₂ := by
  unfold contract_general
  -- swap_covariant and swap_contravariant distribute over addition
  have h_contra : swap_contravariant 0 i (T₁ + T₂) =
      swap_contravariant 0 i T₁ + swap_contravariant 0 i T₂ := by
    ext m n; simp [swap_contravariant_eval, MultilinearMap.add_apply]
  have h_cov : swap_covariant 0 j (swap_contravariant 0 i T₁ + swap_contravariant 0 i T₂) =
      swap_covariant 0 j (swap_contravariant 0 i T₁) +
      swap_covariant 0 j (swap_contravariant 0 i T₂) := by
    ext m n; simp [swap_covariant_eval, MultilinearMap.add_apply]
  rw [h_contra, h_cov, atr.tensor_contract_add]

theorem contract_general_smul (atr : AbstractTrace R V) {r s : ℕ}
    (i : Fin (r + 1)) (j : Fin (s + 1))
    (c : R) (T : TensorData R V (r + 1) (s + 1)) :
    contract_general atr i j (c • T) =
    c • contract_general atr i j T := by
  unfold contract_general
  have h_contra : swap_contravariant 0 i (c • T) =
      c • swap_contravariant 0 i T := by
    ext m n; simp [swap_contravariant_eval, MultilinearMap.smul_apply, smul_eq_mul]
  have h_cov : swap_covariant 0 j (c • swap_contravariant 0 i T) =
      c • swap_covariant 0 j (swap_contravariant 0 i T) := by
    ext m n; simp [swap_covariant_eval, MultilinearMap.smul_apply, smul_eq_mul]
  rw [h_contra, h_cov, atr.tensor_contract_smul]

/-- contract_general at (0, 0) is just tensor_contract. -/
theorem contract_general_0_0 (atr : AbstractTrace R V) {r s : ℕ}
    (T : TensorData R V (r + 1) (s + 1)) :
    contract_general atr 0 0 T = atr.tensor_contract T := by
  unfold contract_general
  congr 1; ext m n
  simp [swap_covariant_eval, swap_contravariant_eval, Equiv.swap_self]

/-- Coordinate evaluation law for the Ricci-style middle-slot trace of a
`(1,3)` tensor.

For fixed exterior vector slots `X` and `Y`, if the slice `Z |-> T(X,Z,Y)`
is represented by an endomorphism `L`, then contracting the contravariant slot
against the middle covariant slot evaluates to `tr L`.

This is the reusable theorem-form obligation supplied by concrete coordinate
trace realizations. It is intentionally not built into `AbstractTrace`: the
basic trace structure only knows how to contract the first pair and how to
recognize `(1,1)` endomorphism tensors. -/
def ContractGeneral13MiddleTraceEval (atr : AbstractTrace R V) : Prop :=
  forall (T : TensorData R V 1 3) (X Y : V) (L : V →ₗ[R] V),
    (forall Z (α : V →ₗ[R] R), T ![X, Z, Y] ![α] = α (L Z)) ->
      contract_general atr (0 : Fin 1) (1 : Fin 3) T ![X, Y] ![] = atr.tr L

/-- Projection form of `ContractGeneral13MiddleTraceEval`. -/
theorem contract_general_13_middle_trace_eval
    (atr : AbstractTrace R V) (h_eval : ContractGeneral13MiddleTraceEval atr)
    (T : TensorData R V 1 3) (X Y : V) (L : V →ₗ[R] V)
    (hL : forall Z (α : V →ₗ[R] R), T ![X, Z, Y] ![α] = α (L Z)) :
    contract_general atr (0 : Fin 1) (1 : Fin 3) T ![X, Y] ![] = atr.tr L :=
  h_eval T X Y L hL

end GeneralContract

-- ============================================================
-- Iterated tensor-contraction coherence
-- ============================================================

section TensorContractFubini
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Contract the first contravariant/covariant pair twice. This is the raw
`AbstractTrace.tensor_contract` double contraction, before metric raising or
slot permutations are added by `metric_trace`. -/
noncomputable def tensor_contract_twice (atr : AbstractTrace R V) {r s : ℕ}
    (T : TensorData R V ((r + 1) + 1) ((s + 1) + 1)) : TensorData R V r s :=
  atr.tensor_contract (atr.tensor_contract T)

/-- Fubini/coherence law for two successive `AbstractTrace.tensor_contract`s:
contracting slots `(0,0)` then `(1,1)` agrees with first swapping the first two
contravariant slots and the first two covariant slots, then contracting twice.

This is not derivable from the existing single-contraction evaluation axioms
alone. Concrete trace realizations should prove it from their coordinate
definition of `tensor_contract`. -/
def TensorContractFubini (atr : AbstractTrace R V) : Prop :=
  ∀ {r s : ℕ} (T : TensorData R V ((r + 1) + 1) ((s + 1) + 1)),
    tensor_contract_twice atr T =
      tensor_contract_twice atr
        (swap_covariant (0 : Fin ((s + 1) + 1)) ⟨1, by omega⟩
          (swap_contravariant (0 : Fin ((r + 1) + 1)) ⟨1, by omega⟩ T))

/-- Typeclass form of `TensorContractFubini`, so synthetic theorems can require
the coherence law without changing the core `AbstractTrace` structure. -/
class HasTensorContractFubini (atr : AbstractTrace R V) : Prop where
  tensor_contract_fubini : TensorContractFubini atr

theorem tensor_contract_twice_swap
    (atr : AbstractTrace R V) [HasTensorContractFubini atr]
    {r s : ℕ} (T : TensorData R V ((r + 1) + 1) ((s + 1) + 1)) :
    tensor_contract_twice atr T =
      tensor_contract_twice atr
        (swap_covariant (0 : Fin ((s + 1) + 1)) ⟨1, by omega⟩
          (swap_contravariant (0 : Fin ((r + 1) + 1)) ⟨1, by omega⟩ T)) :=
  HasTensorContractFubini.tensor_contract_fubini T

theorem tensor_contract_twice_swap_of_fubini
    (atr : AbstractTrace R V) (h : TensorContractFubini atr)
    {r s : ℕ} (T : TensorData R V ((r + 1) + 1) ((s + 1) + 1)) :
    tensor_contract_twice atr T =
      tensor_contract_twice atr
        (swap_covariant (0 : Fin ((s + 1) + 1)) ⟨1, by omega⟩
          (swap_contravariant (0 : Fin ((r + 1) + 1)) ⟨1, by omega⟩ T)) :=
  h T

end TensorContractFubini

-- ============================================================
-- Naturality of tensor_contract under swaps of uncontracted slots
-- ============================================================

section TensorContractSwapNaturality
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Naturality law: `AbstractTrace.tensor_contract` always contracts the
*first* contravariant/covariant pair (slot `0`/`0`). Swapping any two
*uncontracted* slots therefore commutes with contraction, after the obvious
`Fin.succ` renumbering of indices.

This is not derivable from `AbstractTrace`'s structural axioms alone — they
only relate `tensor_contract` to evaluation against `vectorToData` /
`covectorToData`. Concrete trace realizations should prove it from their
coordinate definition. -/
def TensorContractSwapNaturality (atr : AbstractTrace R V) : Prop :=
  (∀ {r s : ℕ} (i j : Fin s) (T : TensorData R V (r + 1) (s + 1)),
      atr.tensor_contract (swap_covariant i.succ j.succ T) =
        swap_covariant i j (atr.tensor_contract T)) ∧
  (∀ {r s : ℕ} (i j : Fin r) (T : TensorData R V (r + 1) (s + 1)),
      atr.tensor_contract (swap_contravariant i.succ j.succ T) =
        swap_contravariant i j (atr.tensor_contract T))

/-- Typeclass form of `TensorContractSwapNaturality`, mirroring
`HasTensorContractFubini`. Synthetic theorems can require the naturality law
as a separate hypothesis without changing the core `AbstractTrace`
structure. -/
class HasTensorContractSwapNaturality (atr : AbstractTrace R V) : Prop where
  contract_swap_covariant :
    ∀ {r s : ℕ} (i j : Fin s) (T : TensorData R V (r + 1) (s + 1)),
      atr.tensor_contract (swap_covariant i.succ j.succ T) =
        swap_covariant i j (atr.tensor_contract T)
  contract_swap_contravariant :
    ∀ {r s : ℕ} (i j : Fin r) (T : TensorData R V (r + 1) (s + 1)),
      atr.tensor_contract (swap_contravariant i.succ j.succ T) =
        swap_contravariant i j (atr.tensor_contract T)

/-- Theorem form of covariant-slot naturality for `tensor_contract`, avoiding
typeclass search at call sites that already carry the naturality law. -/
theorem tensor_contract_swap_covariant_succ_of_naturality
    (atr : AbstractTrace R V) (h : TensorContractSwapNaturality atr)
    {r s : ℕ} (i j : Fin s) (T : TensorData R V (r + 1) (s + 1)) :
    atr.tensor_contract (swap_covariant i.succ j.succ T) =
      swap_covariant i j (atr.tensor_contract T) :=
  h.1 i j T

/-- Theorem form of contravariant-slot naturality for `tensor_contract`,
avoiding typeclass search at call sites that already carry the naturality law. -/
theorem tensor_contract_swap_contravariant_succ_of_naturality
    (atr : AbstractTrace R V) (h : TensorContractSwapNaturality atr)
    {r s : ℕ} (i j : Fin r) (T : TensorData R V (r + 1) (s + 1)) :
    atr.tensor_contract (swap_contravariant i.succ j.succ T) =
      swap_contravariant i j (atr.tensor_contract T) :=
  h.2 i j T

theorem tensor_contract_swap_covariant_succ
    (atr : AbstractTrace R V) [HasTensorContractSwapNaturality atr]
    {r s : ℕ} (i j : Fin s) (T : TensorData R V (r + 1) (s + 1)) :
    atr.tensor_contract (swap_covariant i.succ j.succ T) =
      swap_covariant i j (atr.tensor_contract T) :=
  HasTensorContractSwapNaturality.contract_swap_covariant i j T

theorem tensor_contract_swap_contravariant_succ
    (atr : AbstractTrace R V) [HasTensorContractSwapNaturality atr]
    {r s : ℕ} (i j : Fin r) (T : TensorData R V (r + 1) (s + 1)) :
    atr.tensor_contract (swap_contravariant i.succ j.succ T) =
      swap_contravariant i j (atr.tensor_contract T) :=
  HasTensorContractSwapNaturality.contract_swap_contravariant i j T

theorem hasTensorContractSwapNaturality_of_naturality
    (atr : AbstractTrace R V) (h : TensorContractSwapNaturality atr) :
    HasTensorContractSwapNaturality atr where
  contract_swap_covariant := h.1
  contract_swap_contravariant := h.2

end TensorContractSwapNaturality

-- ============================================================
-- Connecting Properties
-- ============================================================

/-- ∇ commutes with trace: X(tr L) = tr([∇_X, L]).
    Uses commutatorEndo for the R-linear commutator. -/
def NablaTrComm {k R V : Type*}
    [Field k] [CommRing R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    (emb : DerivationEmbedding k R V) (atr : AbstractTrace R V)
    (conn_nabla : V → V → V)
    (conn_add : ∀ X Y Z, conn_nabla X (Y + Z) = conn_nabla X Y + conn_nabla X Z)
    (conn_leibniz : ∀ X (f : R) Y, conn_nabla X (f • Y) =
      (emb.embed X) f • Y + f • conn_nabla X Y) : Prop :=
  ∀ (X : V) (L : V →ₗ[R] V),
    (emb.embed X) (atr.tr L) = atr.tr (commutatorEndo
      (emb.embed X).toFun (conn_nabla X)
      (conn_add X) (conn_leibniz X) L)

/-- ∂_t commutes with trace.
    Generalized over an abstract time algebra A with `td.eval` for evaluation.
    For a time-dependent endomorphism L with time derivative dL, if for each v, α
    we have elements `αLv v α ∈ A` representing `s ↦ α(L(s)(v))` and `trL ∈ A`
    representing `s ↦ tr(L(s))`, then eval(dt(trL))(t) = tr(dL). -/
def TimeTrComm {R V : Type*} {A Time : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    [CommRing A] [Algebra R A]
    (atr : AbstractTrace R V) (td : TimeDerivativeData R A Time) : Prop :=
  ∀ (L : Time → V →ₗ[R] V) (dL : V →ₗ[R] V) (t : Time)
    (αLv : V → (V →ₗ[R] R) → A) (trL : A),
    (∀ v α s, td.eval (αLv v α) s = α (L s v)) →
    (∀ s, td.eval trL s = atr.tr (L s)) →
    (∀ (v : V) (α : V →ₗ[R] R), α (dL v) = td.eval (td.dt (αLv v α)) t) →
    td.eval (td.dt trL) t = atr.tr dL

/-- For `A = Time → R` with the identity lift/eval, recover the original direct API.
Requires smoothness of the `α (L s v)` and `tr (L s)` families so that
`eval_lift` applies. -/
theorem TimeTrComm.of_pi {R V Time : Type*}
    [CommRing R] [AddCommGroup V] [Module R V]
    {atr : AbstractTrace R V} {td : TimeDerivativeData R (Time → R) Time}
    [TimeRegularFam td]
    (h : TimeTrComm atr td)
    (L : Time → V →ₗ[R] V) (dL : V →ₗ[R] V) (t : Time)
    (h_αLv_smooth : ∀ (v : V) (α : V →ₗ[R] R),
      td.isSmoothFam (fun s => α (L s v)))
    (h_trL_smooth : td.isSmoothFam (fun s => atr.tr (L s)))
    (h_char : ∀ (v : V) (α : V →ₗ[R] R),
      α (dL v) = td.eval (td.dt (td.lift (fun s => α (L s v)))) t) :
    td.eval (td.dt (td.lift (fun s => atr.tr (L s)))) t = atr.tr dL :=
  h L dL t (fun v α => td.lift (fun s => α (L s v))) (td.lift (fun s => atr.tr (L s)))
    (fun v α s => by rw [td.eval_lift _ (h_αLv_smooth v α)])
    (fun s => by rw [td.eval_lift _ h_trL_smooth])
    h_char

end SyntheticTensor
