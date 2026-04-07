import Mathlib.LinearAlgebra.Multilinear.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

namespace DifferentialGeometry

/-
  ## Tensor Calculus
-/

/-- Pure Tensor Algebra (Layer 1): Depends only on module structure, no geometry or calculus.
This is implemented by the analytic backend using multidimensional arrays. -/

abbrev TensorData (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] (r s : ℕ) :=
  MultilinearMap R (fun _ : Fin s => V) (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)

instance {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {r s : ℕ} : Zero (TensorData R V r s) := inferInstanceAs (Zero (MultilinearMap R (fun _ : Fin s => V) (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)))
instance {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {r s : ℕ} : Add (TensorData R V r s) := inferInstanceAs (Add (MultilinearMap R (fun _ : Fin s => V) (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)))
instance {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {r s : ℕ} : SMul R (TensorData R V r s) := inferInstanceAs (SMul R (MultilinearMap R (fun _ : Fin s => V) (MultilinearMap R (fun _ : Fin r => (V →ₗ[R] R)) R)))
def scalarToData {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (f : R) : TensorData R V 0 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => (V →ₗ[R] R)) f)

def evalLinear {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (v : V) : (V →ₗ[R] R) →ₗ[R] R where
  toFun w := w v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vectorToData {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (v : V) : TensorData R V 1 0 :=
  MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V)
    (MultilinearMap.ofSubsingleton R (V →ₗ[R] R) R (0 : Fin 1) (evalLinear v))

class TensorAlgebra (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] where
  /-- Generic graded tensor type (r: contravariant, s: covariant) -/
  AbstractTensor : ℕ → ℕ → Type

  add {r s : ℕ} : AbstractTensor r s → AbstractTensor r s → AbstractTensor r s -- done
  smul {r s : ℕ} : R → AbstractTensor r s → AbstractTensor r s -- done
  tensor_prod {r1 s1 r2 s2 : ℕ} : AbstractTensor r1 s1 → AbstractTensor r2 s2 → AbstractTensor (r1 + r2) (s1 + s2) -- done

  -- Embedding & Extraction
  fromData {r s : ℕ} : TensorData R V r s → AbstractTensor r s
  toData {r s : ℕ} : AbstractTensor r s → TensorData R V r s

  -- Identity Operator (Kronecker Delta)
  delta_tensor : AbstractTensor 1 1

  -- Extraction
  toScalar : AbstractTensor 0 0 → R

  -- Permutations (Routing Mechanism)
  swap_contravariant {r s : ℕ} (i j : Fin r) : AbstractTensor r s → AbstractTensor r s
  swap_covariant {r s : ℕ} (i j : Fin s) : AbstractTensor r s → AbstractTensor r s

  /-- General contraction between one contravariant and one covariant slot -/
  contract {r s : ℕ} : AbstractTensor (r + 1) (s + 1) → AbstractTensor r s

  -- Multilinear Data Binding Ops
  data_tensor_prod {r1 s1 r2 s2 : ℕ} : TensorData R V r1 s1 → TensorData R V r2 s2 → TensorData R V (r1 + r2) (s1 + s2)
  data_contract {r s : ℕ} : TensorData R V (r + 1) (s + 1) → TensorData R V r s

  --  Axioms:
  -- 1. Linearity of Contraction:
  contract_add {r s : ℕ} : ∀ T1 T2 : AbstractTensor (r + 1) (s + 1), contract (add T1 T2) = add (contract T1) (contract T2)
  contract_smul {r s : ℕ} : ∀ (f : R) (T : AbstractTensor (r + 1) (s + 1)), contract (smul f T) = smul f (contract T)

  -- Evaluation Isomorphism Axioms
  fromData_toData {r s : ℕ} : ∀ (T : AbstractTensor r s), fromData (toData T) = T
  toData_fromData {r s : ℕ} : ∀ (D : TensorData R V r s), toData (fromData D) = D
  toData_add {r s : ℕ} : ∀ T1 T2 : AbstractTensor r s, toData (add T1 T2) = toData T1 + toData T2
  toData_smul {r s : ℕ} : ∀ (c : R) (T : AbstractTensor r s), toData (smul c T) = c • toData T
  toData_swap_covariant {r s : ℕ} : ∀ (i j : Fin s) (T : AbstractTensor r s) (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)),
    toData (swap_covariant i j T) m n = toData T (m ∘ Equiv.swap i j) n
  toData_swap_contravariant {r s : ℕ} : ∀ (i j : Fin r) (T : AbstractTensor r s) (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)),
    toData (swap_contravariant i j T) m n = toData T m (n ∘ Equiv.swap i j)
  toData_tensor_prod {r1 s1 r2 s2 : ℕ} : ∀ T1 : AbstractTensor r1 s1, ∀ T2 : AbstractTensor r2 s2,
    toData (tensor_prod T1 T2) = data_tensor_prod (toData T1) (toData T2)
  toData_contract {r s : ℕ} : ∀ T : AbstractTensor (r + 1) (s + 1),
    toData (contract T) = data_contract (toData T)

  -- Universal Data-Layer Axioms
  
  -- Evaluation of double contraction of any generic D ⊗ X ⊗ Y uniformly evaluates to prepending to parameter array
  data_eval_contract_contract : ∀ {r s : ℕ} (D : TensorData R V r (s + 2)) (X Y : V) (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)),
    (data_contract (r:=r) (s:=s) (data_contract (r:=r+1) (s:=s+1) (data_tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) D (data_tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (vectorToData X) (vectorToData Y))))) m n =
    D (Fin.cons X (Fin.cons Y m)) n

  -- Data-bound swap axiom parametrized generically across ∀ {r s : ℕ}
  data_contract_swap_covariant_eval : ∀ {r s : ℕ} (X Y : V) (D : TensorData R V r (s + 2)),
    data_contract (r:=r) (s:=s) (data_contract (r:=r+1) (s:=s+1) (data_tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) (toData (swap_covariant 0 1 (fromData D))) (data_tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (vectorToData X) (vectorToData Y)))) =
    data_contract (r:=r) (s:=s) (data_contract (r:=r+1) (s:=s+1) (data_tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) D (data_tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (vectorToData Y) (vectorToData X))))

  -- 2. Scalar Definition:
  toScalar_add : ∀ T1 T2 : AbstractTensor 0 0, toScalar (add T1 T2) = toScalar T1 + toScalar T2
  toScalar_smul : ∀ (c : R) (T : AbstractTensor 0 0), toScalar (smul c T) = c * toScalar T
  toScalar_eq_toData : ∀ (T : AbstractTensor 0 0), toScalar T = toData T ![] ![]

  tensor_prod_add_left : ∀ {r1 s1 r2 s2 : ℕ} (T1 T2 : AbstractTensor r1 s1) (T3 : AbstractTensor r2 s2),
    tensor_prod (add T1 T2) T3 = add (tensor_prod T1 T3) (tensor_prod T2 T3)
  tensor_prod_add_right : ∀ {r1 s1 r2 s2 : ℕ} (T1 : AbstractTensor r1 s1) (T2 T3 : AbstractTensor r2 s2),
    tensor_prod T1 (add T2 T3) = add (tensor_prod T1 T2) (tensor_prod T1 T3)
  tensor_prod_smul_left : ∀ {r1 s1 r2 s2 : ℕ} (c : R) (T1 : AbstractTensor r1 s1) (T2 : AbstractTensor r2 s2),
    tensor_prod (smul c T1) T2 = smul c (tensor_prod T1 T2)
  tensor_prod_smul_right : ∀ {r1 s1 r2 s2 : ℕ} (c : R) (T1 : AbstractTensor r1 s1) (T2 : AbstractTensor r2 s2),
    tensor_prod T1 (smul c T2) = smul c (tensor_prod T1 T2)

  -- Rank-1 Outer Product & Evaluation
  outerProduct : V → (V →ₗ[R] R) → AbstractTensor 1 1
  contract_outerProduct : ∀ (X : V) (α : V →ₗ[R] R), toScalar (contract (outerProduct X α)) = α X
  toData_outerProduct : ∀ (X : V) (α : V →ₗ[R] R) (m : Fin 1 → V) (n : Fin 1 → (V →ₗ[R] R)),
    toData (outerProduct X α) m n = α (m 0) * n 0 X

namespace TensorAlgebra

/-
Generalized Contraction.
-/
def contract_general {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
  {r s : ℕ} (i : Fin (r + 1)) (j : Fin (s + 1)) (T : AbstractTensor R V (r + 1) (s + 1)) : AbstractTensor R V r s :=
  contract (swap_covariant 0 j (swap_contravariant 0 i T))

lemma swap_covariant_add {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    {r s : ℕ} (i j : Fin s) (T1 T2 : AbstractTensor R V r s) :
    swap_covariant i j (add T1 T2) = add (swap_covariant i j T1) (swap_covariant i j T2) := by
    have h : toData (swap_covariant i j (add T1 T2)) = toData (add (swap_covariant i j T1) (swap_covariant i j T2)) := by
      ext m n
      have lhs : toData (swap_covariant i j (add T1 T2)) m n = (toData T1 + toData T2) (m ∘ Equiv.swap i j) n := by
        rw [toData_swap_covariant]; rw [toData_add]
      have rhs : toData (add (swap_covariant i j T1) (swap_covariant i j T2)) m n =
        toData (swap_covariant i j T1) m n + toData (swap_covariant i j T2) m n := by
        rw [toData_add]; rfl
      rw [lhs, rhs, toData_swap_covariant, toData_swap_covariant]
      rfl
    rw [← fromData_toData (swap_covariant i j (add T1 T2)), ← fromData_toData (add (swap_covariant i j T1) (swap_covariant i j T2)), h]

lemma swap_covariant_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    {r s : ℕ} (i j : Fin s) (c : R) (T : AbstractTensor R V r s) :
    swap_covariant i j (smul c T) = smul c (swap_covariant i j T) := by
  have h : toData (swap_covariant i j (smul c T)) = toData (smul c (swap_covariant i j T)) := by
    ext m n
    have lhs : toData (swap_covariant i j (smul c T)) m n = (c • toData T) (m ∘ Equiv.swap i j) n := by
      rw [toData_swap_covariant, toData_smul]
    have rhs : toData (smul c (swap_covariant i j T)) m n = c * toData (swap_covariant i j T) m n := by
      rw [toData_smul]; rfl
    rw [lhs, rhs, toData_swap_covariant]
    rfl
  rw [← fromData_toData (swap_covariant i j (smul c T)), ← fromData_toData (smul c (swap_covariant i j T)), h]

lemma contract_general_0_0 {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    {r s : ℕ} (T : AbstractTensor R V (r + 1) (s + 1)) :
    contract_general (0 : Fin (r + 1)) (0 : Fin (s + 1)) T = contract T := by
  unfold contract_general
  have h_cov : swap_covariant (0 : Fin _) (0 : Fin _) (swap_contravariant (0 : Fin _) (0 : Fin _) T) = swap_contravariant (0 : Fin _) (0 : Fin _) T := by
    have hd : toData (swap_covariant (0 : Fin _) (0 : Fin _) (swap_contravariant (0 : Fin _) (0 : Fin _) T)) = toData (swap_contravariant (0 : Fin _) (0 : Fin _) T) := by
      ext m n
      rw [toData_swap_covariant, Equiv.swap_self]
      rfl
    rw [← fromData_toData (swap_covariant (0 : Fin _) (0 : Fin _) (swap_contravariant (0 : Fin _) (0 : Fin _) T))]
    rw [hd, fromData_toData]
  rw [h_cov]
  have h_con : swap_contravariant (0 : Fin _) (0 : Fin _) T = T := by
    have hd : toData (swap_contravariant (0 : Fin _) (0 : Fin _) T) = toData T := by
      ext m n
      rw [toData_swap_contravariant, Equiv.swap_self]
      rfl
    rw [← fromData_toData (swap_contravariant (0 : Fin _) (0 : Fin _) T)]
    rw [hd, fromData_toData]
  rw [h_con]

lemma swap_contravariant_add {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    {r s : ℕ} (i j : Fin r) (T1 T2 : AbstractTensor R V r s) :
    swap_contravariant i j (add T1 T2) = add (swap_contravariant i j T1) (swap_contravariant i j T2) := by
  have h : toData (swap_contravariant i j (add T1 T2)) = toData (add (swap_contravariant i j T1) (swap_contravariant i j T2)) := by
    ext m n
    have lhs : toData (swap_contravariant i j (add T1 T2)) m n = (toData T1 m + toData T2 m) (n ∘ Equiv.swap i j) := by
      rw [toData_swap_contravariant]; rw [toData_add]; rfl
    have rhs : toData (add (swap_contravariant i j T1) (swap_contravariant i j T2)) m n =
      toData (swap_contravariant i j T1) m n + toData (swap_contravariant i j T2) m n := by
      rw [toData_add]; rfl
    rw [lhs, rhs, toData_swap_contravariant, toData_swap_contravariant]
    exact MultilinearMap.add_apply (toData T1 m) (toData T2 m) (n ∘ Equiv.swap i j)
  rw [← fromData_toData (swap_contravariant i j (add T1 T2)), ← fromData_toData (add (swap_contravariant i j T1) (swap_contravariant i j T2)), h]

lemma swap_contravariant_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    {r s : ℕ} (i j : Fin r) (c : R) (T : AbstractTensor R V r s) :
    swap_contravariant i j (smul c T) = smul c (swap_contravariant i j T) := by
  have h : toData (swap_contravariant i j (smul c T)) = toData (smul c (swap_contravariant i j T)) := by
    ext m n
    have lhs : toData (swap_contravariant i j (smul c T)) m n = c • (toData T m (n ∘ Equiv.swap i j)) := by
      rw [toData_swap_contravariant]; rw [toData_smul]; rfl
    have rhs : toData (smul c (swap_contravariant i j T)) m n = c • toData (swap_contravariant i j T) m n := by
      rw [toData_smul]; rfl
    rw [lhs, rhs, toData_swap_contravariant]
  rw [← fromData_toData (swap_contravariant i j (smul c T)), ← fromData_toData (smul c (swap_contravariant i j T)), h]

lemma contract_general_add {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    {r s : ℕ} (i : Fin (r + 1)) (j : Fin (s + 1)) (T1 T2 : AbstractTensor R V (r + 1) (s + 1)) :
    contract_general i j (add T1 T2) = add (contract_general i j T1) (contract_general i j T2) := by
  simp only [contract_general]
  rw [swap_contravariant_add, swap_covariant_add, contract_add]

lemma contract_general_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]
    {r s : ℕ} (i : Fin (r + 1)) (j : Fin (s + 1)) (c : R) (T : AbstractTensor R V (r + 1) (s + 1)) :
    contract_general i j (smul c T) = smul c (contract_general i j T) := by
  simp only [contract_general]
  rw [swap_contravariant_smul, swap_covariant_smul, contract_smul]

end TensorAlgebra


-- The following is used to protect previous structure from failing.

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [TensorAlgebra R V]

def fromScalar (f : R) : TensorAlgebra.AbstractTensor R V 0 0 := TensorAlgebra.fromData (scalarToData f)
def fromVector (X : V) : TensorAlgebra.AbstractTensor R V 1 0 := TensorAlgebra.fromData (vectorToData X)

lemma vectorToData_add {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (X Y : V) :
  vectorToData (R:=R) (V:=V) (X + Y) = vectorToData (R:=R) X + vectorToData (R:=R) Y := by
  ext m n
  dsimp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton]
  rw [LinearMap.map_add]

lemma vectorToData_smul {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] (c : R) (X : V) :
  vectorToData (R:=R) (V:=V) (c • X) = c • vectorToData (R:=R) X := by
  ext m n
  dsimp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton]
  rw [LinearMap.map_smul]
  rfl

lemma fromVector_add (X Y : V) : fromVector (R:=R) (X + Y) = TensorAlgebra.add (fromVector (R:=R) X) (fromVector (R:=R) Y) := by
  dsimp [fromVector]
  rw [vectorToData_add (R:=R) X Y]
  have h_add : TensorAlgebra.toData (TensorAlgebra.add (TensorAlgebra.fromData (vectorToData (R:=R) X)) (TensorAlgebra.fromData (vectorToData (R:=R) Y))) =
    vectorToData (R:=R) X + vectorToData (R:=R) Y := by
    rw [TensorAlgebra.toData_add, TensorAlgebra.toData_fromData, TensorAlgebra.toData_fromData]
  rw [← h_add, TensorAlgebra.fromData_toData]


lemma fromVector_smul (c : R) (X : V) : fromVector (R:=R) (c • X) = TensorAlgebra.smul c (fromVector (R:=R) X) := by
  dsimp [fromVector]
  rw [vectorToData_smul (R:=R) c X]
  have h_smul : TensorAlgebra.toData (TensorAlgebra.smul c (TensorAlgebra.fromData (vectorToData (R:=R) X))) = c • vectorToData (R:=R) X := by
    rw [TensorAlgebra.toData_smul, TensorAlgebra.toData_fromData]
  rw [← h_smul, TensorAlgebra.fromData_toData]

lemma contract_swap_covariant_eval {r s : ℕ} (X Y : V) (T : TensorAlgebra.AbstractTensor R V r (s + 2)) :
    TensorAlgebra.contract (r:=r) (s:=s) (TensorAlgebra.contract (r:=r+1) (s:=s+1) (TensorAlgebra.tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) (TensorAlgebra.swap_covariant 0 1 T) (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector X) (fromVector Y)))) =
    TensorAlgebra.contract (r:=r) (s:=s) (TensorAlgebra.contract (r:=r+1) (s:=s+1) (TensorAlgebra.tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector X)))) := by
  have hz : TensorAlgebra.toData (TensorAlgebra.contract (r:=r) (s:=s) (TensorAlgebra.contract (r:=r+1) (s:=s+1) (TensorAlgebra.tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) (TensorAlgebra.swap_covariant 0 1 T) (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector X) (fromVector Y))))) =
            TensorAlgebra.toData (TensorAlgebra.contract (r:=r) (s:=s) (TensorAlgebra.contract (r:=r+1) (s:=s+1) (TensorAlgebra.tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector X))))) := by
    rw [TensorAlgebra.toData_contract, TensorAlgebra.toData_contract, TensorAlgebra.toData_tensor_prod, TensorAlgebra.toData_contract, TensorAlgebra.toData_contract, TensorAlgebra.toData_tensor_prod]
    rw [TensorAlgebra.toData_tensor_prod, TensorAlgebra.toData_tensor_prod]
    have hx : TensorAlgebra.toData (fromVector (R:=R) X) = vectorToData X := TensorAlgebra.toData_fromData _
    have hy : TensorAlgebra.toData (fromVector (R:=R) Y) = vectorToData Y := TensorAlgebra.toData_fromData _
    rw [hx, hy]
    have h_swap := TensorAlgebra.data_contract_swap_covariant_eval X Y (TensorAlgebra.toData T)
    rw [TensorAlgebra.fromData_toData] at h_swap
    exact h_swap
  have h1 : TensorAlgebra.fromData (TensorAlgebra.toData (TensorAlgebra.contract (r:=r) (s:=s) (TensorAlgebra.contract (r:=r+1) (s:=s+1) (TensorAlgebra.tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) (TensorAlgebra.swap_covariant 0 1 T) (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector X) (fromVector Y)))))) =
            TensorAlgebra.fromData (TensorAlgebra.toData (TensorAlgebra.contract (r:=r) (s:=s) (TensorAlgebra.contract (r:=r+1) (s:=s+1) (TensorAlgebra.tensor_prod (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector Y) (fromVector X)))))) := by
    rw [hz]
  rw [TensorAlgebra.fromData_toData, TensorAlgebra.fromData_toData] at h1
  exact h1

def tensor_eval {r s : ℕ} (T : TensorAlgebra.AbstractTensor R V r s)
  (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) : R :=
  TensorAlgebra.toData T vs αs

lemma tensor_eval_add {r s : ℕ} (T1 T2 : TensorAlgebra.AbstractTensor R V r s)
  (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) :
  tensor_eval (TensorAlgebra.add T1 T2) vs αs = tensor_eval T1 vs αs + tensor_eval T2 vs αs := by
  dsimp [tensor_eval]
  rw [TensorAlgebra.toData_add]
  rfl

lemma tensor_eval_smul {r s : ℕ} (c : R) (T : TensorAlgebra.AbstractTensor R V r s)
  (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) :
  tensor_eval (TensorAlgebra.smul c T) vs αs = c * tensor_eval T vs αs := by
  dsimp [tensor_eval]
  rw [TensorAlgebra.toData_smul]
  rfl



lemma tensor_eval_add_left (T : TensorAlgebra.AbstractTensor R V 0 2) (X Y Z : V) :
  tensor_eval T ![X + Y, Z] ![] = tensor_eval T ![X, Z] ![] + tensor_eval T ![Y, Z] ![] := by
  dsimp [tensor_eval]
  have hz : ![X + Y, Z] = Function.update ![X, Z] 0 (X + Y) := by
    ext i
    fin_cases i <;> rfl
  rw [hz]
  have h_add := MultilinearMap.map_update_add (TensorAlgebra.toData T) ![X, Z] 0 X Y
  rw [h_add]
  have hz_x : Function.update ![X, Z] 0 X = ![X, Z] := by
    ext i
    fin_cases i <;> rfl
  have hz_y : Function.update ![X, Z] 0 Y = ![Y, Z] := by
    ext i
    fin_cases i <;> rfl
  rw [hz_x, hz_y]
  exact MultilinearMap.add_apply _ _ _

lemma tensor_eval_smul_left (T : TensorAlgebra.AbstractTensor R V 0 2) (f : R) (X Y : V) :
  tensor_eval T ![f • X, Y] ![] = f * tensor_eval T ![X, Y] ![] := by
  dsimp [tensor_eval]
  have hz : ![f • X, Y] = Function.update ![X, Y] 0 (f • X) := by
    ext i
    fin_cases i <;> rfl
  rw [hz]
  have h_smul := MultilinearMap.map_update_smul (TensorAlgebra.toData T) ![X, Y] 0 f X
  rw [h_smul]
  have hz_x : Function.update ![X, Y] 0 X = ![X, Y] := by
    ext i
    fin_cases i <;> rfl
  rw [hz_x]
  exact MultilinearMap.smul_apply _ _ _

lemma tensor_eval_add_right (T : TensorAlgebra.AbstractTensor R V 0 2) (X Y Z : V) :
  tensor_eval T ![X, Y + Z] ![] = tensor_eval T ![X, Y] ![] + tensor_eval T ![X, Z] ![] := by
  dsimp [tensor_eval]
  have hz : ![X, Y + Z] = Function.update ![X, Z] 1 (Y + Z) := by
    ext i
    fin_cases i <;> rfl
  rw [hz]
  have h_add := MultilinearMap.map_update_add (TensorAlgebra.toData T) ![X, Z] 1 Y Z
  rw [h_add]
  have hz_x : Function.update ![X, Z] 1 Y = ![X, Y] := by
    ext i
    fin_cases i <;> rfl
  have hz_y : Function.update ![X, Z] 1 Z = ![X, Z] := by
    ext i
    fin_cases i <;> rfl
  rw [hz_x, hz_y]
  exact MultilinearMap.add_apply _ _ _

lemma tensor_eval_smul_right (T : TensorAlgebra.AbstractTensor R V 0 2) (f : R) (X Y : V) :
  tensor_eval T ![X, f • Y] ![] = f * tensor_eval T ![X, Y] ![] := by
  dsimp [tensor_eval]
  have hz : ![X, f • Y] = Function.update ![X, Y] 1 (f • Y) := by
    ext i
    fin_cases i <;> rfl
  rw [hz]
  have h_smul := MultilinearMap.map_update_smul (TensorAlgebra.toData T) ![X, Y] 1 f Y
  rw [h_smul]
  have hz_x : Function.update ![X, Y] 1 Y = ![X, Y] := by
    ext i
    fin_cases i <;> rfl
  rw [hz_x]
  exact MultilinearMap.smul_apply _ _ _



lemma tensor_eval_isomorphism (T : TensorAlgebra.AbstractTensor R V 0 2) (X Y : V) :
  tensor_eval T ![X, Y] ![] = ((TensorAlgebra.toData (TensorAlgebra.contract (R:=R) (r:=0) (s:=0) (TensorAlgebra.contract (R:=R) (r:=1) (s:=1) (TensorAlgebra.tensor_prod (R:=R) (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (R:=R) (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector (R:=R) X) (fromVector (R:=R) Y)))))) ![]) ![] := by
  dsimp [tensor_eval]
  have step1 : TensorAlgebra.toData (TensorAlgebra.contract (R:=R) (r:=0) (s:=0) (TensorAlgebra.contract (R:=R) (r:=1) (s:=1) (TensorAlgebra.tensor_prod (R:=R) (r1:=0) (s1:=2) (r2:=2) (s2:=0) T (TensorAlgebra.tensor_prod (R:=R) (r1:=1) (s1:=0) (r2:=1) (s2:=0) (fromVector (R:=R) X) (fromVector (R:=R) Y))))) = TensorAlgebra.data_contract (r:=0) (s:=0) (TensorAlgebra.data_contract (r:=1) (s:=1) (TensorAlgebra.data_tensor_prod (r1:=0) (s1:=2) (r2:=2) (s2:=0) (TensorAlgebra.toData T) (TensorAlgebra.data_tensor_prod (r1:=1) (s1:=0) (r2:=1) (s2:=0) (vectorToData (R:=R) X) (vectorToData (R:=R) Y)))) := by
    rw [TensorAlgebra.toData_contract]
    rw [TensorAlgebra.toData_contract]
    rw [TensorAlgebra.toData_tensor_prod]
    have h_vec1 : TensorAlgebra.toData (fromVector (R:=R) X) = vectorToData (R:=R) X := TensorAlgebra.toData_fromData (vectorToData (R:=R) X)
    have h_vec2 : TensorAlgebra.toData (fromVector (R:=R) Y) = vectorToData (R:=R) Y := TensorAlgebra.toData_fromData (vectorToData (R:=R) Y)
    rw [TensorAlgebra.toData_tensor_prod]
    rw [h_vec1, h_vec2]
  rw [step1]
  have step2 := TensorAlgebra.data_eval_contract_contract (r:=0) (s:=0) (TensorAlgebra.toData T) X Y ![] ![]
  have h_eq : Fin.cons X (Fin.cons Y ![]) = ![X, Y] := by
    ext i
    fin_cases i <;> rfl
  rw [h_eq] at step2
  exact step2.symm

end DifferentialGeometry
