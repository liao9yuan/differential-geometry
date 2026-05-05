import DifferentialGeometry.Synthetic.Algebra.Metric
import DifferentialGeometry.Synthetic.Analysis.NablaOnTensors
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.style.emptyLine false

open SyntheticTensor

/-!
# Covariant Derivative of Tensors
-/

section Helpers02

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

private lemma bilinear_add_left_02 (T : TensorData R V 0 2) (Y₁ Y₂ Z : V) :
    T ![Y₁ + Y₂, Z] ![] = T ![Y₁, Z] ![] + T ![Y₂, Z] ![] := by
  have h := T.map_update_add ![Y₁, Z] 0 Y₁ Y₂
  have h0 : Function.update (![Y₁, Z] : Fin 2 → V) 0 (Y₁ + Y₂) = ![Y₁ + Y₂, Z] := by
    ext i; fin_cases i <;> simp [Function.update]
  have h1 : Function.update (![Y₁, Z] : Fin 2 → V) 0 Y₁ = ![Y₁, Z] := by
    ext i; fin_cases i <;> simp [Function.update]
  have h2 : Function.update (![Y₁, Z] : Fin 2 → V) 0 Y₂ = ![Y₂, Z] := by
    ext i; fin_cases i <;> simp [Function.update]
  rw [h0, h1, h2] at h; exact congr_arg (· ![]) h

private lemma bilinear_smul_left_02 (T : TensorData R V 0 2) (a : R) (Y Z : V) :
    T ![a • Y, Z] ![] = a * T ![Y, Z] ![] := by
  have h := congr_arg (· ![]) (T.map_update_smul ![Y, Z] 0 a Y)
  have h0 : Function.update (![Y, Z] : Fin 2 → V) 0 (a • Y) = ![a • Y, Z] := by
    ext i; fin_cases i <;> simp [Function.update]
  have h1 : Function.update (![Y, Z] : Fin 2 → V) 0 Y = ![Y, Z] := by
    ext i; fin_cases i <;> simp [Function.update]
  rw [h0, h1] at h; simp only [MultilinearMap.smul_apply, smul_eq_mul] at h; exact h

private lemma bilinear_add_right_02 (T : TensorData R V 0 2) (Y Z₁ Z₂ : V) :
    T ![Y, Z₁ + Z₂] ![] = T ![Y, Z₁] ![] + T ![Y, Z₂] ![] := by
  have h := T.map_update_add ![Y, Z₁] 1 Z₁ Z₂
  have h0 : Function.update (![Y, Z₁] : Fin 2 → V) 1 (Z₁ + Z₂) = ![Y, Z₁ + Z₂] := by
    ext i; fin_cases i <;> simp [Function.update]
  have h1 : Function.update (![Y, Z₁] : Fin 2 → V) 1 Z₁ = ![Y, Z₁] := by
    ext i; fin_cases i <;> simp [Function.update]
  have h2 : Function.update (![Y, Z₁] : Fin 2 → V) 1 Z₂ = ![Y, Z₂] := by
    ext i; fin_cases i <;> simp [Function.update]
  rw [h0, h1, h2] at h; exact congr_arg (· ![]) h

private lemma bilinear_smul_right_02 (T : TensorData R V 0 2) (a : R) (Y Z : V) :
    T ![Y, a • Z] ![] = a * T ![Y, Z] ![] := by
  have h := congr_arg (· ![]) (T.map_update_smul ![Y, Z] 1 a Z)
  have h0 : Function.update (![Y, Z] : Fin 2 → V) 1 (a • Z) = ![Y, a • Z] := by
    ext i; fin_cases i <;> simp [Function.update]
  have h1 : Function.update (![Y, Z] : Fin 2 → V) 1 Z = ![Y, Z] := by
    ext i; fin_cases i <;> simp [Function.update]
  rw [h0, h1] at h; simp only [MultilinearMap.smul_apply, smul_eq_mul] at h; exact h

end Helpers02

section RawCovDeriv

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Raw evaluation of the covariant derivative of a (0,2)-tensor T along X. -/
def rawCovDeriv (emb : DerivationEmbedding k R V) (conn : V → V → V) (X : V)
    (T : TensorData R V 0 2) (Y Z : V) : R :=
  (emb.embed X) (T ![Y, Z] ![]) - T ![conn X Y, Z] ![] - T ![Y, conn X Z] ![]

lemma rawCovDeriv_add_left (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (conn_add_right : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (X : V) (T : TensorData R V 0 2) (Y₁ Y₂ Z : V) :
    rawCovDeriv emb conn X T (Y₁ + Y₂) Z =
    rawCovDeriv emb conn X T Y₁ Z + rawCovDeriv emb conn X T Y₂ Z := by
  simp only [rawCovDeriv, bilinear_add_left_02, map_add, conn_add_right,
    bilinear_add_left_02 T (conn X Y₁) (conn X Y₂)]; ring

lemma rawCovDeriv_smul_left (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (conn_leibniz : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 0 2) (a : R) (Y Z : V) :
    rawCovDeriv emb conn X T (a • Y) Z = a * rawCovDeriv emb conn X T Y Z := by
  simp only [rawCovDeriv]
  rw [bilinear_smul_left_02]
  have h := (emb.embed X).leibniz a (T ![Y, Z] ![]); simp only [smul_eq_mul] at h; rw [h]
  rw [conn_leibniz X a Y, bilinear_add_left_02,
      bilinear_smul_left_02 T ((emb.embed X) a),
      bilinear_smul_left_02 T a (conn X Y),
      bilinear_smul_left_02 T a Y]; ring

lemma rawCovDeriv_add_right (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (conn_add_right : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (X : V) (T : TensorData R V 0 2) (Y Z₁ Z₂ : V) :
    rawCovDeriv emb conn X T Y (Z₁ + Z₂) =
    rawCovDeriv emb conn X T Y Z₁ + rawCovDeriv emb conn X T Y Z₂ := by
  simp only [rawCovDeriv, bilinear_add_right_02, map_add, conn_add_right,
    bilinear_add_right_02 T Y (conn X Z₁) (conn X Z₂),
    bilinear_add_right_02 T (conn X Y)]; ring

lemma rawCovDeriv_smul_right (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (conn_leibniz : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 0 2) (a : R) (Y Z : V) :
    rawCovDeriv emb conn X T Y (a • Z) = a * rawCovDeriv emb conn X T Y Z := by
  simp only [rawCovDeriv]
  rw [bilinear_smul_right_02]
  have h := (emb.embed X).leibniz a (T ![Y, Z] ![]); simp only [smul_eq_mul] at h; rw [h]
  rw [conn_leibniz X a Z, bilinear_add_right_02,
      bilinear_smul_right_02 T ((emb.embed X) a) Y,
      bilinear_smul_right_02 T a Y (conn X Z),
      bilinear_smul_right_02 T a (conn X Y)]; ring

end RawCovDeriv

section CovDerivOp

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

noncomputable def covDerivOp
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 0 2) : TensorData R V 0 2 :=
  nabla_tensor emb conn ha hl X T

/-- covDerivOp evaluated at specific vectors equals rawCovDeriv. -/
theorem covDeriv_eval
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 0 2) (Y Z : V) :
    covDerivOp emb conn ha hl X T ![Y, Z] ![] = rawCovDeriv emb conn X T Y Z := by
  unfold covDerivOp rawCovDeriv
  rw [nabla_tensor_eval]
  -- For (0,2)-tensor: r=0, s=2. The sum over Fin 0 (covector slots) is empty.
  rw [Finset.sum_of_isEmpty (f := fun j : Fin 0 => _), sub_zero]
  -- Expand the Fin 2 sum over covariant (vector) slots
  rw [Fin.sum_univ_two]
  have h0 : Function.update (![Y, Z] : Fin 2 → V) 0 (conn X (![Y, Z] 0)) = ![conn X Y, Z] := by
    ext i; fin_cases i <;> simp [Function.update]
  have h1 : Function.update (![Y, Z] : Fin 2 → V) 1 (conn X (![Y, Z] 1)) = ![Y, conn X Z] := by
    ext i; fin_cases i <;> simp [Function.update]
  rw [h0, h1]; ring

theorem metric_covDerivOp_zero
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (X : V) :
    covDerivOp emb conn ha hl X met.g_tensor = 0 :=
  nabla_g_zero emb conn ha hl met h_mc X

end CovDerivOp
