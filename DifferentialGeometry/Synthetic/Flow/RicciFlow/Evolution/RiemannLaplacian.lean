import DifferentialGeometry.Synthetic.Flow.RicciFlow.Basic
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

/-!
# Rough Laplacian of the Riemann Curvature Tensor

ΔRm = g^{pq} ∇²_{p,q} Rm.
-/

open SyntheticTensor

section RoughLaplacian

variable {k R V Time : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- The second covariant derivative ∇²T(P,W) = ∇_P(∇_W T) - ∇_{∇_P W} T.
    Connection correction cancels Leibniz, giving R-bilinearity in (P, W). -/
private noncomputable def second_cov_deriv_covector
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    {r s : ℕ} (T : TensorData R V r s) (W : V)
    (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) : V →ₗ[R] R where
  toFun P :=
    nabla_tensor emb conn ha hl P (nabla_tensor emb conn ha hl W T) vs αs -
    nabla_tensor emb conn ha hl (conn P W) T vs αs
  map_add' P₁ P₂ := by
    rw [nabla_add_left emb conn ha hal hl P₁ P₂ _ vs αs,
      hal P₁ P₂ W, nabla_add_left emb conn ha hal hl _ _ T vs αs]; ring
  map_smul' c P := by
    rw [nabla_smul_left emb conn ha hsl hl c P _ vs αs,
      hsl c P W, nabla_smul_left emb conn ha hsl hl c _ T vs αs]
    simp only [smul_eq_mul, RingHom.id_apply]; ring

/-- Rough Laplacian endomorphism: W ↦ sharp(P ↦ ∇²T(P,W)(vs)(αs)). -/
private noncomputable def rough_laplacian_endo
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (met : MetricDuality R V) 
    {r s : ℕ} (T : TensorData R V r s)
    (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R)) : V →ₗ[R] V where
  toFun W := met.sharp (second_cov_deriv_covector emb conn ha hl hal hsl T W vs αs)
  map_add' W₁ W₂ := by
    have h_cov : second_cov_deriv_covector emb conn ha hl hal hsl T (W₁ + W₂) vs αs =
        second_cov_deriv_covector emb conn ha hl hal hsl T W₁ vs αs +
        second_cov_deriv_covector emb conn ha hl hal hsl T W₂ vs αs := by
      ext P; simp only [second_cov_deriv_covector, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.add_apply]
      have h_dir : nabla_tensor emb conn ha hl (W₁ + W₂) T =
          nabla_tensor emb conn ha hl W₁ T + nabla_tensor emb conn ha hl W₂ T := by
        ext vs' αs'; exact nabla_add_left emb conn ha hal hl W₁ W₂ T vs' αs'
      have h_outer := nabla_add emb conn ha hl P (nabla_tensor emb conn ha hl W₁ T)
        (nabla_tensor emb conn ha hl W₂ T)
      have h_eval : nabla_tensor emb conn ha hl P
          (nabla_tensor emb conn ha hl (W₁ + W₂) T) vs αs =
        nabla_tensor emb conn ha hl P (nabla_tensor emb conn ha hl W₁ T) vs αs +
        nabla_tensor emb conn ha hl P (nabla_tensor emb conn ha hl W₂ T) vs αs := by
        conv_lhs => rw [h_dir]
        have := congr_arg (· vs) h_outer; simp only [MultilinearMap.add_apply] at this
        exact congr_arg (· αs) this
      rw [h_eval, ha P W₁ W₂, nabla_add_left emb conn ha hal hl]; ring
    rw [h_cov]; exact met.sharp_add _ _
  map_smul' c W := by
    have h_cov : second_cov_deriv_covector emb conn ha hl hal hsl T (c • W) vs αs =
        c • second_cov_deriv_covector emb conn ha hl hal hsl T W vs αs := by
      ext P; simp only [second_cov_deriv_covector, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.smul_apply, smul_eq_mul]
      have h_dir : nabla_tensor emb conn ha hl (c • W) T =
          c • nabla_tensor emb conn ha hl W T := by
        ext vs' αs'; rw [nabla_smul_left emb conn ha hsl hl]
        simp [MultilinearMap.smul_apply, smul_eq_mul]
      have h_eval : nabla_tensor emb conn ha hl P
          (nabla_tensor emb conn ha hl (c • W) T) vs αs =
        c * nabla_tensor emb conn ha hl P (nabla_tensor emb conn ha hl W T) vs αs +
        (emb.embed P) c * (nabla_tensor emb conn ha hl W T) vs αs := by
        conv_lhs => rw [h_dir]; rw [nabla_smul emb conn ha hl P c _ vs αs]; rw [add_comm]
      rw [h_eval, show conn P (c • W) = (emb.embed P) c • W + c • conn P W from hl P c W,
        nabla_add_left emb conn ha hal hl _ _ T vs αs,
        nabla_smul_left emb conn ha hsl hl _ _ T vs αs,
        nabla_smul_left emb conn ha hsl hl c (conn P W) T vs αs]; ring
    simp only [RingHom.id_apply]; rw [h_cov]; exact met.sharp_smul c _

-- Factored helper: the covector splits for vs/αs updates
private theorem scd_covector_update_cov_add
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hl hal hsl) {r s : ℕ} (T : TensorData R V r s) (W : V)
    (vs : Fin s → V) (idx : Fin s) (v₁ v₂ : V)
    (αs : Fin r → (V →ₗ[R] R)) :
    second_cov_deriv_covector emb conn ha hl hal hsl T W
        (Function.update vs idx (v₁ + v₂)) αs =
    second_cov_deriv_covector emb conn ha hl hal hsl T W
        (Function.update vs idx v₁) αs +
    second_cov_deriv_covector emb conn ha hl hal hsl T W
        (Function.update vs idx v₂) αs := by
  ext Z; simp only [second_cov_deriv_covector, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.add_apply]
  have h1 := congr_arg (· αs) ((nabla_tensor emb conn ha hl Z
    (nabla_tensor emb conn ha hl W T)).map_update_add vs idx v₁ v₂)
  have h2 := congr_arg (· αs) ((nabla_tensor emb conn ha hl (conn Z W) T).map_update_add
    vs idx v₁ v₂)
  simp only [MultilinearMap.add_apply] at h1 h2; rw [h1, h2]; ring

private theorem scd_covector_update_cov_smul
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hl hal hsl) {r s : ℕ} (T : TensorData R V r s) (W : V)
    (vs : Fin s → V) (idx : Fin s) (c : R) (v : V)
    (αs : Fin r → (V →ₗ[R] R)) :
    second_cov_deriv_covector emb conn ha hl hal hsl T W
        (Function.update vs idx (c • v)) αs =
    c • second_cov_deriv_covector emb conn ha hl hal hsl T W
        (Function.update vs idx v) αs := by
  ext Z; simp only [second_cov_deriv_covector, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.smul_apply, smul_eq_mul]
  have h1 := congr_arg (· αs) ((nabla_tensor emb conn ha hl Z
    (nabla_tensor emb conn ha hl W T)).map_update_smul vs idx c v)
  have h2 := congr_arg (· αs) ((nabla_tensor emb conn ha hl (conn Z W) T).map_update_smul
    vs idx c v)
  simp only [MultilinearMap.smul_apply, smul_eq_mul] at h1 h2; rw [h1, h2]; ring

private theorem scd_covector_update_contra_add
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hl hal hsl) {r s : ℕ} (T : TensorData R V r s) (W : V)
    (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R))
    (idx : Fin r) (β₁ β₂ : V →ₗ[R] R) :
    second_cov_deriv_covector emb conn ha hl hal hsl T W vs
        (Function.update αs idx (β₁ + β₂)) =
    second_cov_deriv_covector emb conn ha hl hal hsl T W vs
        (Function.update αs idx β₁) +
    second_cov_deriv_covector emb conn ha hl hal hsl T W vs
        (Function.update αs idx β₂) := by
  ext Z; simp only [second_cov_deriv_covector, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.add_apply]
  have h1 := (nabla_tensor emb conn ha hl Z (nabla_tensor emb conn ha hl W T) vs).map_update_add
    αs idx β₁ β₂
  have h2 := (nabla_tensor emb conn ha hl (conn Z W) T vs).map_update_add αs idx β₁ β₂
  rw [h1, h2]; ring

private theorem scd_covector_update_contra_smul
    (emb : DerivationEmbedding k R V) (conn : V → V → V) (ha hl hal hsl) {r s : ℕ} (T : TensorData R V r s) (W : V)
    (vs : Fin s → V) (αs : Fin r → (V →ₗ[R] R))
    (idx : Fin r) (c : R) (β : V →ₗ[R] R) :
    second_cov_deriv_covector emb conn ha hl hal hsl T W vs
        (Function.update αs idx (c • β)) =
    c • second_cov_deriv_covector emb conn ha hl hal hsl T W vs
        (Function.update αs idx β) := by
  ext Z; simp only [second_cov_deriv_covector, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.smul_apply, smul_eq_mul]
  have h1 := (nabla_tensor emb conn ha hl Z (nabla_tensor emb conn ha hl W T) vs).map_update_smul
    αs idx c β
  have h2 := (nabla_tensor emb conn ha hl (conn Z W) T vs).map_update_smul αs idx c β
  simp only [smul_eq_mul] at h1 h2; rw [h1, h2]; ring

/-- Δ(T) = g^{pq} ∇²T(e_p, e_q) as a TensorData R V 1 3.
    Uses the second covariant derivative with connection correction. -/
noncomputable def rough_laplacian_Rm_endo
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    (T : TensorData R V 1 3) : TensorData R V 1 3 where
  toFun vs :=
    { toFun := fun αs =>
        atr.tr (rough_laplacian_endo emb conn ha hl hal hsl met T vs αs)
      map_update_add' := by
        intro inst αs idx β₁ β₂
        have : inst = instDecidableEqFin 1 := Subsingleton.elim _ _; subst this
        change _ = _ + _
        have h : rough_laplacian_endo emb conn ha hl hal hsl met T vs
            (Function.update αs idx (β₁ + β₂)) =
          rough_laplacian_endo emb conn ha hl hal hsl met T vs
            (Function.update αs idx β₁) +
          rough_laplacian_endo emb conn ha hl hal hsl met T vs
            (Function.update αs idx β₂) := by
          ext W; simp only [rough_laplacian_endo, LinearMap.coe_mk, AddHom.coe_mk,
            LinearMap.add_apply]
          rw [scd_covector_update_contra_add emb conn ha hl hal hsl T W vs αs idx β₁ β₂]
          exact met.sharp_add _ _
        rw [h, map_add]
      map_update_smul' := by
        intro inst αs idx c β
        have : inst = instDecidableEqFin 1 := Subsingleton.elim _ _; subst this
        simp only [smul_eq_mul]
        have h : rough_laplacian_endo emb conn ha hl hal hsl met T vs
            (Function.update αs idx (c • β)) =
          c • rough_laplacian_endo emb conn ha hl hal hsl met T vs
            (Function.update αs idx β) := by
          ext W; simp only [rough_laplacian_endo, LinearMap.coe_mk, AddHom.coe_mk,
            LinearMap.smul_apply]
          rw [scd_covector_update_contra_smul emb conn ha hl hal hsl T W vs αs idx c β]
          exact met.sharp_smul c _
        rw [h, map_smul, smul_eq_mul] }
  map_update_add' := by
    intro inst vs idx v₁ v₂; ext αs
    have : inst = instDecidableEqFin 3 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.add_apply]
    have h : rough_laplacian_endo emb conn ha hl hal hsl met T
        (Function.update vs idx (v₁ + v₂)) αs =
      rough_laplacian_endo emb conn ha hl hal hsl met T
        (Function.update vs idx v₁) αs +
      rough_laplacian_endo emb conn ha hl hal hsl met T
        (Function.update vs idx v₂) αs := by
      ext W; simp only [rough_laplacian_endo, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.add_apply]
      rw [scd_covector_update_cov_add emb conn ha hl hal hsl T W vs idx v₁ v₂ αs]
      exact met.sharp_add _ _
    rw [h, map_add]
  map_update_smul' := by
    intro inst vs idx c v; ext αs
    have : inst = instDecidableEqFin 3 := Subsingleton.elim _ _; subst this
    simp only [MultilinearMap.coe_mk, MultilinearMap.smul_apply, smul_eq_mul]
    have h : rough_laplacian_endo emb conn ha hl hal hsl met T
        (Function.update vs idx (c • v)) αs =
      c • rough_laplacian_endo emb conn ha hl hal hsl met T
        (Function.update vs idx v) αs := by
      ext W; simp only [rough_laplacian_endo, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.smul_apply]
      rw [scd_covector_update_cov_smul emb conn ha hl hal hsl T W vs idx c v αs]
      exact met.sharp_smul c _
    rw [h, map_smul, smul_eq_mul]

noncomputable def rough_laplacian_Rm
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (hal : ∀ X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : ∀ (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (atr : AbstractTrace R V) (met : MetricDuality R V) 
    : TensorData R V 1 3 :=
  rough_laplacian_Rm_endo emb conn ha hl hal hsl atr met
    (Rm_tensor emb conn ha hal hsl hl)

end RoughLaplacian
