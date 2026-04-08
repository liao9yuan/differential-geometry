import DifferentialGeometry.Synthetic.Algebra.TensorAlgebra
import DifferentialGeometry.Synthetic.Algebra.DualFrame
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators
open DifferentialGeometry

namespace DifferentialGeometry

/-! ## Part A: Helper Definitions -/

section helpers
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Concrete tensor product: (D1 ⊗ D2)(m₁m₂)(n₁n₂) = D1(m₁)(n₁) * D2(m₂)(n₂) -/
noncomputable def dataTensorProd
    {r1 s1 r2 s2 : ℕ} (D1 : TensorData R V r1 s1) (D2 : TensorData R V r2 s2) :
    TensorData R V (r1 + r2) (s1 + s2) :=
  { toFun := fun m =>
      { toFun := fun n =>
          D1 (m ∘ Fin.castAdd s2) (n ∘ Fin.castAdd r2) *
          D2 (m ∘ Fin.natAdd s1) (n ∘ Fin.natAdd r1)
        map_update_add' := by
          intro decl n i x y
          by_cases h : i.val < r1
          · let j : Fin r1 := ⟨i.val, h⟩
            have hj : Fin.castAdd r2 j = i := Fin.ext rfl
            have hc : ∀ v, Function.update n i v ∘ Fin.castAdd r2 =
                Function.update (n ∘ Fin.castAdd r2) j v := fun v => by
              rw [← hj]; exact Function.update_comp_eq_of_injective n
                (Fin.castAdd_injective r1 r2) j v
            have hn : ∀ v, Function.update n i v ∘ Fin.natAdd r1 = n ∘ Fin.natAdd r1 := fun v =>
              Function.update_comp_eq_of_forall_ne n v
                (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
            simp only [hc, hn, (D1 (m ∘ Fin.castAdd s2)).map_update_add]
            ring
          · push Not at h
            let j : Fin r2 := ⟨i.val - r1, by omega⟩
            have hj : Fin.natAdd r1 j = i := Fin.ext (by change r1 + (i.val - r1) = i.val; omega)
            have hc : ∀ v, Function.update n i v ∘ Fin.natAdd r1 =
                Function.update (n ∘ Fin.natAdd r1) j v := fun v => by
              rw [← hj]; exact Function.update_comp_eq_of_injective n
                (Fin.natAdd_injective r2 r1) j v
            have hn : ∀ v, Function.update n i v ∘ Fin.castAdd r2 = n ∘ Fin.castAdd r2 := fun v =>
              Function.update_comp_eq_of_forall_ne n v
                (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
            simp only [hc, hn, (D2 (m ∘ Fin.natAdd s1)).map_update_add]
            ring
        map_update_smul' := by
          intro decl n i c x
          by_cases h : i.val < r1
          · let j : Fin r1 := ⟨i.val, h⟩
            have hj : Fin.castAdd r2 j = i := Fin.ext rfl
            have hc : ∀ v, Function.update n i v ∘ Fin.castAdd r2 =
                Function.update (n ∘ Fin.castAdd r2) j v := fun v => by
              rw [← hj]; exact Function.update_comp_eq_of_injective n
                (Fin.castAdd_injective r1 r2) j v
            have hn : ∀ v, Function.update n i v ∘ Fin.natAdd r1 = n ∘ Fin.natAdd r1 := fun v =>
              Function.update_comp_eq_of_forall_ne n v
                (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
            simp only [hc, hn, (D1 (m ∘ Fin.castAdd s2)).map_update_smul,
                        smul_eq_mul]
            ring
          · push Not at h
            let j : Fin r2 := ⟨i.val - r1, by omega⟩
            have hj : Fin.natAdd r1 j = i := Fin.ext (by change r1 + (i.val - r1) = i.val; omega)
            have hc : ∀ v, Function.update n i v ∘ Fin.natAdd r1 =
                Function.update (n ∘ Fin.natAdd r1) j v := fun v => by
              rw [← hj]; exact Function.update_comp_eq_of_injective n
                (Fin.natAdd_injective r2 r1) j v
            have hn : ∀ v, Function.update n i v ∘ Fin.castAdd r2 = n ∘ Fin.castAdd r2 := fun v =>
              Function.update_comp_eq_of_forall_ne n v
                (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
            simp only [hc, hn, (D2 (m ∘ Fin.natAdd s1)).map_update_smul,
                        smul_eq_mul]
            ring }
    map_update_add' := by
      intro decl m i x y; ext n; simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
      by_cases h : i.val < s1
      · let j : Fin s1 := ⟨i.val, h⟩
        have hj : Fin.castAdd s2 j = i := Fin.ext rfl
        have hc : ∀ v, Function.update m i v ∘ Fin.castAdd s2 =
            Function.update (m ∘ Fin.castAdd s2) j v := fun v => by
          rw [← hj]; exact Function.update_comp_eq_of_injective m
            (Fin.castAdd_injective s1 s2) j v
        have hn : ∀ v, Function.update m i v ∘ Fin.natAdd s1 = m ∘ Fin.natAdd s1 := fun v =>
          Function.update_comp_eq_of_forall_ne m v
            (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
        simp only [hc, hn, D1.map_update_add, MultilinearMap.add_apply]
        ring
      · push Not at h
        let j : Fin s2 := ⟨i.val - s1, by omega⟩
        have hj : Fin.natAdd s1 j = i := Fin.ext (by change s1 + (i.val - s1) = i.val; omega)
        have hc : ∀ v, Function.update m i v ∘ Fin.natAdd s1 =
            Function.update (m ∘ Fin.natAdd s1) j v := fun v => by
          rw [← hj]; exact Function.update_comp_eq_of_injective m
            (Fin.natAdd_injective s2 s1) j v
        have hn : ∀ v, Function.update m i v ∘ Fin.castAdd s2 = m ∘ Fin.castAdd s2 := fun v =>
          Function.update_comp_eq_of_forall_ne m v
            (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
        simp only [hc, hn, D2.map_update_add, MultilinearMap.add_apply]
        ring
    map_update_smul' := by
      intro decl m i c x; ext n; simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
      by_cases h : i.val < s1
      · let j : Fin s1 := ⟨i.val, h⟩
        have hj : Fin.castAdd s2 j = i := Fin.ext rfl
        have hc : ∀ v, Function.update m i v ∘ Fin.castAdd s2 =
            Function.update (m ∘ Fin.castAdd s2) j v := fun v => by
          rw [← hj]; exact Function.update_comp_eq_of_injective m
            (Fin.castAdd_injective s1 s2) j v
        have hn : ∀ v, Function.update m i v ∘ Fin.natAdd s1 = m ∘ Fin.natAdd s1 := fun v =>
          Function.update_comp_eq_of_forall_ne m v
            (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]; omega)
        simp only [hc, hn, D1.map_update_smul, MultilinearMap.smul_apply, smul_eq_mul]
        ring
      · push Not at h
        let j : Fin s2 := ⟨i.val - s1, by omega⟩
        have hj : Fin.natAdd s1 j = i := Fin.ext (by change s1 + (i.val - s1) = i.val; omega)
        have hc : ∀ v, Function.update m i v ∘ Fin.natAdd s1 =
            Function.update (m ∘ Fin.natAdd s1) j v := fun v => by
          rw [← hj]; exact Function.update_comp_eq_of_injective m
            (Fin.natAdd_injective s2 s1) j v
        have hn : ∀ v, Function.update m i v ∘ Fin.castAdd s2 = m ∘ Fin.castAdd s2 := fun v =>
          Function.update_comp_eq_of_forall_ne m v
            (fun k => by simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]; omega)
        simp only [hc, hn, D2.map_update_smul, MultilinearMap.smul_apply, smul_eq_mul]
        ring }

/-- Concrete contraction using DualFrame: ∑ k, D(basis_k, m)(dual_k, n) -/
noncomputable def dataContract {d : ℕ} [DualFrame R V d]
    {r s : ℕ} (D : TensorData R V (r + 1) (s + 1)) : TensorData R V r s :=
  { toFun := fun m =>
      { toFun := fun n =>
          ∑ k : Fin d, D (Fin.cons (DualFrame.basis (R:=R) (d:=d) k) m)
                          (Fin.snoc n (DualFrame.dual (R:=R) (d:=d) k))
        map_update_add' := by
          intro decl n i x y
          have hdec : decl = instDecidableEqFin _ := Subsingleton.elim _ _; subst hdec
          simp_rw [@Fin.snoc_update r (fun _ => V →ₗ[R] R)]
          simp only [MultilinearMap.map_update_add]
          exact Finset.sum_add_distrib
        map_update_smul' := by
          intro decl n i c x
          have hdec : decl = instDecidableEqFin _ := Subsingleton.elim _ _; subst hdec
          simp_rw [@Fin.snoc_update r (fun _ => V →ₗ[R] R)]
          simp only [MultilinearMap.map_update_smul, smul_eq_mul]
          exact (Finset.mul_sum ..).symm }
    map_update_add' := by
      intro decl m i x y; ext n; simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
      have hdec : decl = instDecidableEqFin _ := Subsingleton.elim _ _; subst hdec
      simp_rw [@Fin.cons_update s (fun _ => V)]
      simp only [MultilinearMap.map_update_add, MultilinearMap.add_apply]
      exact Finset.sum_add_distrib
    map_update_smul' := by
      intro decl m i c x; ext n; simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
      have hdec : decl = instDecidableEqFin _ := Subsingleton.elim _ _; subst hdec
      simp_rw [@Fin.cons_update s (fun _ => V)]
      simp only [MultilinearMap.map_update_smul, MultilinearMap.smul_apply, smul_eq_mul]
      exact (Finset.mul_sum ..).symm }

/-- Kronecker delta tensor: δ(m)(n) = n₀(m₀) -/
noncomputable def deltaTensor : TensorData R V 1 1 :=
  { toFun := fun m =>
      { toFun := fun n => n 0 (m 0)
        map_update_add' := by
          intro _ n i x y
          have hi := Subsingleton.elim i 0; subst hi
          simp [Function.update_self]
        map_update_smul' := by
          intro _ n i c x
          have hi := Subsingleton.elim i 0; subst hi
          simp [Function.update_self, smul_eq_mul] }
    map_update_add' := by
      intro _ m j x y; ext n
      simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
      have hj := Subsingleton.elim j 0; subst hj
      simp [Function.update_self, map_add]
    map_update_smul' := by
      intro _ m j c x; ext n
      simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
      have hj := Subsingleton.elim j 0; subst hj
      simp [Function.update_self, map_smul] }

/-- Outer product: (X ⊗ α)(m)(n) = α(m₀) * n₀(X) -/
noncomputable def outerProductData (X : V) (α : V →ₗ[R] R) : TensorData R V 1 1 :=
  { toFun := fun m =>
      { toFun := fun n => α (m 0) * n 0 X
        map_update_add' := by
          intro _ n i x y
          have hi := Subsingleton.elim i 0; subst hi
          simp [Function.update_self, mul_add]
        map_update_smul' := by
          intro _ n i c x
          have hi := Subsingleton.elim i 0; subst hi
          simp [Function.update_self, smul_eq_mul, mul_left_comm] }
    map_update_add' := by
      intro _ m j x y; ext n
      simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
      have hj := Subsingleton.elim j 0; subst hj
      simp [Function.update_self, map_add, add_mul]
    map_update_smul' := by
      intro _ m j c x; ext n
      simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
      have hj := Subsingleton.elim j 0; subst hj
      simp [Function.update_self, map_smul, smul_eq_mul, mul_assoc] }

/-! ### Helper lemmas for evaluation axioms -/

/-- Weighted sum of multilinear evaluations: ∑ k, c(k) * D(cons(e(k), m))(n)
    = D(cons(∑ k, c(k) • e(k), m))(n), by multilinearity of D in the first slot. -/
lemma multilinear_cons_weighted_sum
    {r s d : ℕ} (D : TensorData R V r (s + 1))
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R))
    (c : Fin d → R) (e : Fin d → V) :
    ∑ k, c k * D (@Fin.cons s (fun _ => V) (e k) m) n =
    D (@Fin.cons s (fun _ => V) (∑ k : Fin d, c k • e k) m) n := by
  have h1 : ∀ k, c k * D (@Fin.cons s (fun _ => V) (e k) m) n =
    D (@Fin.cons s (fun _ => V) (c k • e k) m) n := by
    intro k; rw [D.cons_smul m (c k) (e k), MultilinearMap.smul_apply, smul_eq_mul]
  simp_rw [h1]
  let m₀ := @Fin.cons s (fun _ => V) (0 : V) m
  have hcons : ∀ x, @Fin.cons s (fun _ => V) x m = Function.update m₀ 0 x :=
    fun x => (@Fin.update_cons_zero s (fun _ => V) (0 : V) m x).symm
  conv_lhs => arg 2; ext k; rw [hcons]
  conv_rhs => rw [hcons]
  rw [D.map_update_sum Finset.univ 0 (fun k => c k • e k) m₀, MultilinearMap.sum_apply]

/-- The tensor product D ⊗ (vectorToData v) evaluates as D times a covector application. -/
lemma dataTensorProd_vectorToData_eval
    {r s : ℕ} (D : TensorData R V r (s + 1)) (v : V)
    (m : Fin (s + 1) → V) (n : Fin (r + 1) → (V →ₗ[R] R)) :
    dataTensorProd (r1:=r) (s1:=s+1) (r2:=1) (s2:=0) D (vectorToData v) m n =
    D (m ∘ Fin.castAdd 0) (n ∘ Fin.castAdd 1) * (n (Fin.natAdd r 0) v) := rfl

/-- Composing with castAdd 0 is the identity (up to type cast). -/
lemma comp_castAdd_zero {α : Type*} {n : ℕ} (f : Fin n → α) :
    f ∘ Fin.castAdd 0 = f ∘ Fin.cast (by omega) := by
  ext i; simp [Function.comp, Fin.castAdd, Fin.castLE]

/-- Composing Fin.snoc with castAdd 1 gives the original function. -/
lemma snoc_comp_castAdd_one {α : Type*} {r : ℕ} (n : Fin r → α) (dk : α) :
    @Fin.snoc r (fun _ => α) n dk ∘ Fin.castAdd 1 = n := by
  funext i
  change @Fin.snoc r (fun _ => α) n dk (Fin.castAdd 1 i) = n i
  have : Fin.castAdd 1 i = Fin.castSucc i := Fin.ext (by simp [Fin.castAdd, Fin.castSucc])
  rw [this]; exact Fin.snoc_castSucc ..

/-- Fin.snoc applied at natAdd r 0 (= last r) gives the last element. -/
lemma snoc_natAdd_zero {α : Type*} {r : ℕ} (n : Fin r → α) (dk : α) :
    @Fin.snoc r (fun _ => α) n dk (Fin.natAdd r 0) = dk := by
  have : Fin.natAdd r (0 : Fin 1) = Fin.last r := Fin.ext (by simp [Fin.natAdd, Fin.last])
  rw [this]; exact Fin.snoc_last ..

/-- Core evaluation lemma: contracting D ⊗ v reduces to evaluating D at v. -/
lemma dataContract_dataTensorProd_vectorToData {d : ℕ} [DualFrame R V d]
    {r s : ℕ} (D : TensorData R V r (s + 1)) (v : V)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) :
    (dataContract (d:=d) (r:=r) (s:=s)
      (dataTensorProd (r1:=r) (s1:=s+1) (r2:=1) (s2:=0) D (vectorToData v))) m n =
    D (@Fin.cons s (fun _ => V) v m) n := by
  simp only [dataContract, MultilinearMap.coe_mk, dataTensorProd_vectorToData_eval]
  have hcov : ∀ bk : V, @Fin.cons s (fun _ => V) bk m ∘ Fin.castAdd 0 =
      @Fin.cons s (fun _ => V) bk m := by
    intro bk; funext i; simp [Function.comp, Fin.castAdd, Fin.castLE]
  simp_rw [hcov]
  have h_D : ∀ (k : Fin d), (D (@Fin.cons s (fun _ => V) (DualFrame.basis (R:=R) (d:=d) k) m))
      (@Fin.snoc r (fun _ => V →ₗ[R] R) n (DualFrame.dual (R:=R) (d:=d) k) ∘ Fin.castAdd 1) =
      (D (@Fin.cons s (fun _ => V) (DualFrame.basis (R:=R) (d:=d) k) m)) n := by
    intro k; rw [snoc_comp_castAdd_one]
  simp_rw [h_D]
  simp_rw [snoc_natAdd_zero]
  conv_lhs => arg 2; ext k; rw [mul_comm]
  rw [multilinear_cons_weighted_sum D m n
    (fun k => DualFrame.dual (R:=R) (d:=d) k v)
    (fun k => DualFrame.basis (R:=R) (d:=d) k)]
  conv_rhs => rw [DualFrame.reconstruct (R:=R) (d:=d) v]

/-- Double contraction of D ⊗ X ⊗ Y evaluates to D(cons Y (cons X m))(n).
    The inner contraction pairs the last contra slot (Y) with cov slot 0,
    and the outer contraction pairs the next-to-last contra slot (X) with cov slot 1. -/
lemma dataContract_dataContract_dataTensorProd_vectorToData_vectorToData
    {d : ℕ} [DualFrame R V d]
    {r s : ℕ} (D : TensorData R V r (s + 2)) (X Y : V)
    (m : Fin s → V) (n : Fin r → (V →ₗ[R] R)) :
    (dataContract (d:=d) (r:=r) (s:=s)
      (dataContract (d:=d) (r:=r+1) (s:=s+1)
        (dataTensorProd (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) D
          (dataTensorProd (r1:=1) (s1:=0) (r2:=1) (s2:=0)
            (vectorToData X) (vectorToData Y))))) m n =
    D (Fin.cons Y (Fin.cons X m)) n := by
  -- Unfold everything
  simp only [dataContract, MultilinearMap.coe_mk, dataTensorProd]
  dsimp [vectorToData, evalLinear, MultilinearMap.constOfIsEmpty, MultilinearMap.ofSubsingleton]
  -- covariant: cons bk₁ (cons bk₂ m) ∘ cast ≈ cons bk₁ (cons bk₂ m)
  have hcov : ∀ (k₁ k₂ : Fin d),
      Fin.cons (DualFrame.basis (R:=R) (d:=d) k₁) (Fin.cons (DualFrame.basis (R:=R) (d:=d) k₂) m) ∘
        Fin.cast (show s + 2 + 0 = s + 2 from by omega) =
      Fin.cons (DualFrame.basis (R:=R) (d:=d) k₁) (Fin.cons (DualFrame.basis (R:=R) (d:=d) k₂) m) := by
    intro k₁ k₂; funext i; simp [Function.comp, Fin.cast]
  simp_rw [hcov]
  -- contravariant: snoc (snoc n dk₂) dk₁ ∘ castAdd 2 = n
  have hcontra : ∀ (k₁ k₂ : Fin d),
      Fin.snoc (Fin.snoc n (DualFrame.dual (R:=R) (d:=d) k₂)) (DualFrame.dual (R:=R) (d:=d) k₁) ∘
        Fin.castAdd 2 = n := by
    intro k₁ k₂; funext i; simp only [Function.comp]
    have : Fin.castAdd 2 i = Fin.castSucc (Fin.castSucc i) := by
      ext; simp [Fin.castAdd, Fin.castSucc, Fin.castLE]
    rw [this, Fin.snoc_castSucc, Fin.snoc_castSucc]
  simp_rw [hcontra]
  -- natAdd r 0 → dk₂ (X's weight), natAdd r 1 → dk₁ (Y's weight)
  have hnat0 : ∀ (k₁ k₂ : Fin d),
      @Fin.snoc (r+1) (fun _ => V →ₗ[R] R)
        (@Fin.snoc r (fun _ => V →ₗ[R] R) n (DualFrame.dual (R:=R) (d:=d) k₂))
        (DualFrame.dual (R:=R) (d:=d) k₁) (Fin.natAdd r (0 : Fin 2)) =
      DualFrame.dual (R:=R) (d:=d) k₂ := by
    intro k₁ k₂
    have : Fin.natAdd r (0 : Fin 2) = Fin.castSucc (Fin.last r) := by
      ext; simp [Fin.natAdd, Fin.castSucc, Fin.last]
    rw [this, Fin.snoc_castSucc, Fin.snoc_last]
  simp_rw [hnat0]
  have hnat1 : ∀ (k₁ k₂ : Fin d),
      @Fin.snoc (r+1) (fun _ => V →ₗ[R] R)
        (@Fin.snoc r (fun _ => V →ₗ[R] R) n (DualFrame.dual (R:=R) (d:=d) k₂))
        (DualFrame.dual (R:=R) (d:=d) k₁) (Fin.natAdd r (1 : Fin 2)) =
      DualFrame.dual (R:=R) (d:=d) k₁ := by
    intro k₁ k₂
    have : Fin.natAdd r (1 : Fin 2) = Fin.last (r + 1) := by
      ext; simp [Fin.natAdd, Fin.last]
    rw [this, Fin.snoc_last]
  simp_rw [hnat1]
  -- Goal: ∑ x, ∑ x_1, D(cons bx1 (cons bx m))(n) * (dx(X) * dx1(Y)) = D(cons Y (cons X m))(n)
  -- Rearrange: pull dk₂(X) out, apply multilinearity in slot 0 for inner sum, then slot 1
  have hrearrange : ∀ (k₁ k₂ : Fin d),
      D (Fin.cons (DualFrame.basis (R:=R) (d:=d) k₁) (Fin.cons (DualFrame.basis (R:=R) (d:=d) k₂) m)) n *
        ((DualFrame.dual (R:=R) (d:=d) k₂) X * (DualFrame.dual (R:=R) (d:=d) k₁) Y) =
      (DualFrame.dual (R:=R) (d:=d) k₂) X * ((DualFrame.dual (R:=R) (d:=d) k₁) Y *
        D (Fin.cons (DualFrame.basis (R:=R) (d:=d) k₁) (Fin.cons (DualFrame.basis (R:=R) (d:=d) k₂) m)) n) := by
    intro k₁ k₂; ring
  simp_rw [hrearrange, ← Finset.mul_sum]
  -- Inner sum over k₁: ∑ k₁, dk₁(Y) * D(cons bk₁ (cons bk₂ m))(n) = D(cons Y (cons bk₂ m))(n)
  have hinner : ∀ (k₂ : Fin d),
      ∑ k₁, (DualFrame.dual (R:=R) (d:=d) k₁) Y *
        D (Fin.cons (DualFrame.basis (R:=R) (d:=d) k₁) (Fin.cons (DualFrame.basis (R:=R) (d:=d) k₂) m)) n =
      D (Fin.cons Y (Fin.cons (DualFrame.basis (R:=R) (d:=d) k₂) m)) n := by
    intro k₂
    rw [multilinear_cons_weighted_sum D (Fin.cons (DualFrame.basis (R:=R) (d:=d) k₂) m) n
      (fun k => DualFrame.dual (R:=R) (d:=d) k Y) (fun k => DualFrame.basis (R:=R) (d:=d) k)]
    conv_rhs => rw [DualFrame.reconstruct (R:=R) (d:=d) Y]
  simp_rw [hinner]
  -- Outer sum: ∑ k₂, dk₂(X) * D(cons Y (cons bk₂ m))(n) = D(cons Y (cons X m))(n)
  conv_lhs => arg 2; ext k₂; rw [mul_comm]
  -- This is multilinearity of D in slot 1 (bk₂ in cons Y (cons bk₂ m))
  -- Define D_Y as the tensor D with Y fixed in slot 0
  let D_Y : TensorData R V r (s + 1) :=
    { toFun := fun m' => D (Fin.cons Y m')
      map_update_add' := by
        intro inst m' i x y
        have hdec : inst = instDecidableEqFin _ := Subsingleton.elim _ _; subst hdec
        have heq : ∀ v, @Fin.cons (s+1) (fun _ => V) Y (Function.update m' i v) =
            Function.update (@Fin.cons (s+1) (fun _ => V) Y m') (Fin.succ i) v :=
          fun v => @Fin.cons_update _ (fun _ => V) Y m' i v
        change D (@Fin.cons (s+1) (fun _ => V) Y (Function.update m' i (x + y))) =
          D (@Fin.cons (s+1) (fun _ => V) Y (Function.update m' i x)) +
          D (@Fin.cons (s+1) (fun _ => V) Y (Function.update m' i y))
        rw [heq, heq, heq]; exact D.map_update_add _ _ _ _
      map_update_smul' := by
        intro inst m' i c x
        have hdec : inst = instDecidableEqFin _ := Subsingleton.elim _ _; subst hdec
        have heq : ∀ v, @Fin.cons (s+1) (fun _ => V) Y (Function.update m' i v) =
            Function.update (@Fin.cons (s+1) (fun _ => V) Y m') (Fin.succ i) v :=
          fun v => @Fin.cons_update _ (fun _ => V) Y m' i v
        change D (@Fin.cons (s+1) (fun _ => V) Y (Function.update m' i (c • x))) =
          c • D (@Fin.cons (s+1) (fun _ => V) Y (Function.update m' i x))
        rw [heq, heq]; exact D.map_update_smul _ _ _ _ }
  have hD_Y_eq : ∀ (m' : Fin (s + 1) → V),
      D_Y m' = D (Fin.cons Y m') := fun _ => rfl
  conv_lhs => arg 2; ext k₂; rw [mul_comm, ← hD_Y_eq]
  conv_rhs => rw [← hD_Y_eq]
  rw [multilinear_cons_weighted_sum D_Y m n
    (fun k => DualFrame.dual (R:=R) (d:=d) k X) (fun k => DualFrame.basis (R:=R) (d:=d) k)]
  conv_rhs => rw [DualFrame.reconstruct (R:=R) (d:=d) X]

/-- Swap covariant evaluation: swapping slots 0,1 of D and contracting with X,Y
    equals contracting D with Y,X. -/
lemma dataContract_swap_covariant_eval_helper
    {d : ℕ} [DualFrame R V d]
    {r s : ℕ} (X Y : V) (D : TensorData R V r (s + 2)) :
    dataContract (d:=d) (r:=r) (s:=s) (dataContract (d:=d) (r:=r+1) (s:=s+1)
      (dataTensorProd (r1:=r) (s1:=s+2) (r2:=2) (s2:=0)
        (D.domDomCongr (Equiv.swap (0 : Fin (s+2)) 1))
        (dataTensorProd (r1:=1) (s1:=0) (r2:=1) (s2:=0) (vectorToData X) (vectorToData Y)))) =
    dataContract (d:=d) (r:=r) (s:=s) (dataContract (d:=d) (r:=r+1) (s:=s+1)
      (dataTensorProd (r1:=r) (s1:=s+2) (r2:=2) (s2:=0) D
        (dataTensorProd (r1:=1) (s1:=0) (r2:=1) (s2:=0) (vectorToData Y) (vectorToData X)))) := by
  ext m n
  rw [dataContract_dataContract_dataTensorProd_vectorToData_vectorToData
        (D.domDomCongr (Equiv.swap (0 : Fin (s+2)) 1)) X Y m n]
  rw [dataContract_dataContract_dataTensorProd_vectorToData_vectorToData D Y X m n]
  -- Goal: (D.domDomCongr (swap 0 1))(cons Y (cons X m)) n = D(cons X (cons Y m)) n
  -- Rewrite using D.map_swap to avoid dependent type issues
  -- D.domDomCongr (swap 0 1) v = D (v ∘ swap 0 1)
  -- So LHS = D ((cons Y (cons X m)) ∘ swap 0 1) n
  -- We want to show this = D (cons X (cons Y m)) n
  -- Strategy: show D.domDomCongr (swap 0 1) (cons Y (cons X m)) = D (cons X (cons Y m))
  -- as multilinear maps, then apply to n.
  -- Use the MultilinearMap.map_swap lemma or just directly work with domDomCongr.
  -- Actually simplest: note that domDomCongr_apply gives D(v ∘ σ) definitionally,
  -- and (cons Y (cons X m)) ∘ swap 0 1 is cons X (cons Y m) by a calc proof.
  -- We'll avoid the dependent-type funext by using D.domDomCongr twice.
  -- (D.domDomCongr σ)(cons Y (cons X m)) = D((cons Y (cons X m)) ∘ σ) = D(cons X (cons Y m))
  -- Equivalently: D.domDomCongr σ (cons Y (cons X m)) = D.domDomCongr id (cons X (cons Y m))
  -- Let's just use the fact that both sides are equal when applied to any n.
  -- Unfold and use D.cons_smul/D.map_update tricks
  -- Or: show multilinear map equality: for all n, the values agree.
  -- Actually the simplest: use congrArg₂ with a proof that the functions are equal
  -- at the level of (Fin (s+2) → V).
  -- The key insight: (fun i => cons Y (cons X m) (swap 0 1 i)) and (cons X (cons Y m))
  -- are DEFINITIONALLY EQUAL as functions Fin (s+2) → V for each concrete index,
  -- but Lean can't see this because of dependent types.
  -- Avoid domDomCongr_apply and work directly.
  -- D.domDomCongr σ = the multilinear map that applies σ to the input.
  -- By definition, (D.domDomCongr σ m) = D (m ∘ σ).
  -- So we need: D ((cons Y (cons X m)) ∘ swap) n = D (cons X (cons Y m)) n
  -- Create the equality at the function level using cast
  have hcomp : (Fin.cons Y (Fin.cons X m)) ∘ (⇑(Equiv.swap (0 : Fin (s+2)) 1)) =
      Fin.cons X (Fin.cons Y m) := by
    ext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | i + 2, hi =>
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne
        (show (⟨i+2, hi⟩ : Fin (s+2)) ≠ 0 from by simp [Fin.ext_iff])
        (show (⟨i+2, hi⟩ : Fin (s+2)) ≠ 1 from by simp [Fin.ext_iff])]
      -- Both sides: Fin.cons _ (Fin.cons _ m) ⟨i+2, hi⟩ = m ⟨i, by omega⟩
      rfl
  change D ((Fin.cons Y (Fin.cons X m)) ∘ ⇑(Equiv.swap (0 : Fin (s+2)) 1)) n =
    D (Fin.cons X (Fin.cons Y m)) n
  rw [hcomp]

end helpers

/-! ## Part B: The TensorAlgebra Instance -/

@[reducible]
noncomputable instance dualFrameTensorAlgebra (R V : Type) [CommRing R] [AddCommGroup V] [Module R V]
    {d : ℕ} [DualFrame R V d] : TensorAlgebra R V where
  AbstractTensor r s := TensorData R V r s

  add T1 T2 := T1 + T2
  smul c T := c • T
  tensor_prod T1 T2 := dataTensorProd T1 T2

  fromData D := D
  toData T := T

  delta_tensor := deltaTensor
  toScalar T := T ![] ![]

  swap_covariant i j T := T.domDomCongr (Equiv.swap i j)

  swap_contravariant i j T :=
    { toFun := fun m =>
        (T m).domDomCongr (Equiv.swap i j)
      map_update_add' := by
        intro _ v k x y; ext n
        simp only [MultilinearMap.domDomCongr_apply]
        exact congrFun (congrArg MultilinearMap.toFun (MultilinearMap.map_update_add T v k x y))
          (fun idx => n (Equiv.swap i j idx))
      map_update_smul' := by
        intro _ v k c x; ext n
        simp only [MultilinearMap.domDomCongr_apply]
        exact congrFun (congrArg MultilinearMap.toFun (MultilinearMap.map_update_smul T v k c x))
          (fun idx => n (Equiv.swap i j idx)) }

  contract T := dataContract T
  data_tensor_prod D1 D2 := dataTensorProd D1 D2
  data_contract D := dataContract D

  outerProduct X α := outerProductData X α

  contract_add := by
    intro r s T1 T2; ext m n
    simp only [dataContract, MultilinearMap.coe_mk]
    change ∑ k : Fin d, ((T1 + T2) (Fin.cons (DualFrame.basis R k) m))
      (Fin.snoc n (DualFrame.dual (d:=d) k)) =
      (∑ k : Fin d, (T1 (Fin.cons (DualFrame.basis R k) m))
        (Fin.snoc n (DualFrame.dual (d:=d) k))) +
      (∑ k : Fin d, (T2 (Fin.cons (DualFrame.basis R k) m))
        (Fin.snoc n (DualFrame.dual (d:=d) k)))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; rfl

  contract_smul := by
    intro r s f T; ext m n
    simp only [dataContract, MultilinearMap.coe_mk]
    change ∑ k : Fin d, ((f • T) (Fin.cons (DualFrame.basis R k) m))
      (Fin.snoc n (DualFrame.dual (d:=d) k)) =
      f * (∑ k : Fin d, (T (Fin.cons (DualFrame.basis R k) m))
        (Fin.snoc n (DualFrame.dual (d:=d) k)))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; rfl

  fromData_toData := fun T => rfl
  toData_fromData := fun D => rfl
  toData_add := fun T1 T2 => rfl
  toData_smul := fun c T => rfl

  toData_swap_covariant := by
    intro r s i j T m n
    change (T (m ∘ ⇑(Equiv.swap i j))) n = T (m ∘ ⇑(Equiv.swap i j)) n
    rfl

  toData_swap_contravariant := by intro r s i j T m n; rfl

  toData_tensor_prod := fun T1 T2 => rfl
  toData_contract := fun T => rfl

  toScalar_eq_toData := fun T => rfl
  toScalar_add := by intro T1 T2; rfl
  toScalar_smul := by intro c T; rfl

  tensor_prod_add_left := by
    intro r1 s1 r2 s2 T1 T2 T3; ext m n
    simp only [dataTensorProd, MultilinearMap.coe_mk, MultilinearMap.add_apply]; ring

  tensor_prod_add_right := by
    intro r1 s1 r2 s2 T1 T2 T3; ext m n
    simp only [dataTensorProd, MultilinearMap.coe_mk, MultilinearMap.add_apply]; ring

  tensor_prod_smul_left := by
    intro r1 s1 r2 s2 c T1 T2; ext m n
    simp only [dataTensorProd, MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]; ring

  tensor_prod_smul_right := by
    intro r1 s1 r2 s2 c T1 T2; ext m n
    simp only [dataTensorProd, MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]; ring

  data_eval_single_contract := by
    intro r s D v m n
    exact dataContract_dataTensorProd_vectorToData D v m n

  data_eval_contract_contract := by
    intro r s D X Y m n
    exact dataContract_dataContract_dataTensorProd_vectorToData_vectorToData (d:=d) D Y X m n

  data_contract_swap_covariant_eval := by
    intro r s X Y D
    exact dataContract_swap_covariant_eval_helper (d:=d) X Y D

  contract_outerProduct := by
    intro X α
    simp only [outerProductData, dataContract, MultilinearMap.coe_mk]
    conv_rhs => rw [DualFrame.dual_reconstruct_apply (R:=R) (d:=d) α X]
    apply Finset.sum_congr rfl; intro k _
    simp [Fin.cons, Fin.snoc]; ring

  toData_outerProduct := by
    intro X α m n; rfl

end DifferentialGeometry
