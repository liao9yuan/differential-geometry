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

/-- The metric as a (0,2) bilinear form (alias for g_tensor). -/
def metricToForm (met : MetricDuality R V) : TensorData R V 0 2 := met.g_tensor

theorem metric_covDerivOp_zero
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (X : V) :
    covDerivOp emb conn ha hl X met.g_tensor = 0 :=
  nabla_g_zero emb conn ha hl met h_mc X

end CovDerivOp

section GenericCovDeriv

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

noncomputable def genericCovDeriv
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T : TensorData R V r s) : TensorData R V r s :=
  nabla_tensor emb conn ha hl X T

lemma genericCovDeriv_add
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r s : ℕ} (T1 T2 : TensorData R V r s) :
    genericCovDeriv emb conn ha hl X (T1 + T2) =
    genericCovDeriv emb conn ha hl X T1 + genericCovDeriv emb conn ha hl X T2 :=
  nabla_add emb conn ha hl X T1 T2

lemma genericCovDeriv_smul
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (c : R) {r s : ℕ} (T : TensorData R V r s) (vs αs) :
    genericCovDeriv emb conn ha hl X (c • T) vs αs =
    (emb.embed X) c * T vs αs + c * genericCovDeriv emb conn ha hl X T vs αs :=
  nabla_smul emb conn ha hl X c T vs αs

noncomputable def genericCovDeriv_tensor_prod
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) {r₁ s₁ r₂ s₂ : ℕ}
    (T₁ : TensorData R V r₁ s₁) (T₂ : TensorData R V r₂ s₂) :
    genericCovDeriv emb conn ha hl X (tensor_prod T₁ T₂) =
    tensor_prod (genericCovDeriv emb conn ha hl X T₁) T₂ +
    tensor_prod T₁ (genericCovDeriv emb conn ha hl X T₂) :=
  nabla_tensor_prod emb conn ha hl X T₁ T₂

lemma genericCovDeriv_contract
    (emb : DerivationEmbedding k R V) (conn : V → V → V)
    (ha : ∀ X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : ∀ X (f : R) (Y : V), conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V)
    (h_ntc : NablaTensorContractComm emb atr conn ha hl)
    (X : V) {r s : ℕ} (T : TensorData R V (r + 1) (s + 1)) :
    genericCovDeriv emb conn ha hl X (atr.tensor_contract T) =
    atr.tensor_contract (genericCovDeriv emb conn ha hl X T) :=
  h_ntc X T

end GenericCovDeriv

section TensorDivergence02

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- For fixed derivative direction `X` and trailing argument `Y`, the covector
`Z |-> (nabla_X T)(Z,Y)` for a `(0,2)` tensor `T`. This is the component that
gets traced in the Section 14.2 divergence of a covariant 2-tensor. -/
noncomputable def covDeriv02TraceCovector
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 0 2) (Y : V) : V →ₗ[R] R where
  toFun Z := rawCovDeriv emb conn X T Z Y
  map_add' Z1 Z2 := rawCovDeriv_add_left emb conn ha X T Z1 Z2 Y
  map_smul' c Z := by
    simp only [RingHom.id_apply, smul_eq_mul]
    exact rawCovDeriv_smul_left emb conn hl X T c Z Y

theorem covDeriv02TraceCovector_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (X : V) (T : TensorData R V 0 2) (Y Z : V) :
    covDeriv02TraceCovector emb conn ha hl X T Y Z =
      nabla_tensor emb conn ha hl X T ![Z, Y] ![] := by
  change rawCovDeriv emb conn X T Z Y =
    nabla_tensor emb conn ha hl X T ![Z, Y] ![]
  exact (covDeriv_eval emb conn ha hl X T Z Y).symm

/-- The endomorphism whose abstract trace is the divergence of a `(0,2)` tensor
at `Y`: `X |-> sharp (Z |-> (nabla_X T)(Z,Y))`. -/
noncomputable def covDivergence02Endomorphism
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (T : TensorData R V 0 2) (Y : V) : V →ₗ[R] V where
  toFun X := met.sharp (covDeriv02TraceCovector emb conn ha hl X T Y)
  map_add' X1 X2 := by
    apply met.eq_of_forall_g_eq
    intro Z
    change met.g (met.sharp (covDeriv02TraceCovector emb conn ha hl (X1 + X2) T Y)) Z =
      met.g (met.sharp (covDeriv02TraceCovector emb conn ha hl X1 T Y) +
        met.sharp (covDeriv02TraceCovector emb conn ha hl X2 T Y)) Z
    rw [met.g_sharp, met.g_add_left, met.g_sharp, met.g_sharp]
    rw [covDeriv02TraceCovector_apply emb conn ha hl (X1 + X2) T Y Z,
      covDeriv02TraceCovector_apply emb conn ha hl X1 T Y Z,
      covDeriv02TraceCovector_apply emb conn ha hl X2 T Y Z]
    exact nabla_add_left emb conn ha conn_add_left hl X1 X2 T ![Z, Y] ![]
  map_smul' c X := by
    simp only [RingHom.id_apply]
    apply met.eq_of_forall_g_eq
    intro Z
    change met.g (met.sharp (covDeriv02TraceCovector emb conn ha hl (c • X) T Y)) Z =
      met.g (c • met.sharp (covDeriv02TraceCovector emb conn ha hl X T Y)) Z
    rw [met.g_sharp, met.g_smul_left, met.g_sharp]
    rw [covDeriv02TraceCovector_apply emb conn ha hl (c • X) T Y Z,
      covDeriv02TraceCovector_apply emb conn ha hl X T Y Z]
    exact nabla_smul_left emb conn ha conn_smul_left hl c X T ![Z, Y] ![]

/-- Divergence of a `(0,2)` tensor, evaluated at a vector `Y`. This is the
metric trace of `(X,Z) |-> (nabla_X T)(Z,Y)`, expressed through the existing
abstract trace API. A later realization lemma can identify this with the
`metric_trace` definition from local frames. -/
noncomputable def covariantDivergence02At
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (T : TensorData R V 0 2) (Y : V) : R :=
  atr.tr (covDivergence02Endomorphism emb met conn ha conn_add_left conn_smul_left hl T Y)

theorem covariantDivergence02At_eval
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (T : TensorData R V 0 2) (Y : V) :
    covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl T Y =
      atr.tr (covDivergence02Endomorphism emb met conn ha conn_add_left
        conn_smul_left hl T Y) := by
  rfl

/-- Divergence endomorphism is additive in the `(0,2)` tensor input. -/
theorem covDivergence02Endomorphism_add
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (T S : TensorData R V 0 2) (Y : V) :
    covDivergence02Endomorphism emb met conn ha conn_add_left conn_smul_left hl
        (T + S) Y =
      covDivergence02Endomorphism emb met conn ha conn_add_left conn_smul_left hl T Y +
        covDivergence02Endomorphism emb met conn ha conn_add_left conn_smul_left hl S Y := by
  ext X
  apply met.eq_of_forall_g_eq
  intro Z
  change
    met.g
      (met.sharp
        (covDeriv02TraceCovector emb conn ha hl X (T + S) Y)) Z =
      met.g
        (met.sharp (covDeriv02TraceCovector emb conn ha hl X T Y) +
          met.sharp (covDeriv02TraceCovector emb conn ha hl X S Y)) Z
  rw [met.g_sharp, met.g_add_left, met.g_sharp, met.g_sharp]
  rw [covDeriv02TraceCovector_apply emb conn ha hl X (T + S) Y Z,
    covDeriv02TraceCovector_apply emb conn ha hl X T Y Z,
    covDeriv02TraceCovector_apply emb conn ha hl X S Y Z]
  have h := congr_arg (fun U : TensorData R V 0 2 => U ![Z, Y] ![])
    (nabla_add emb conn ha hl X T S)
  simpa only [MultilinearMap.add_apply] using h

/-- Divergence is additive in the `(0,2)` tensor input. -/
theorem covariantDivergence02At_add
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (T S : TensorData R V 0 2) (Y : V) :
    covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
        (T + S) Y =
      covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl T Y +
        covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl S Y := by
  unfold covariantDivergence02At
  rw [covDivergence02Endomorphism_add emb met conn ha conn_add_left conn_smul_left hl T S Y,
    map_add]

/-- Divergence of the zero `(0,2)` tensor. -/
theorem covariantDivergence02At_zero
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (Y : V) :
    covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
        (0 : TensorData R V 0 2) Y = 0 := by
  let div0 :=
    covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
      (0 : TensorData R V 0 2) Y
  change div0 = 0
  have h : div0 = div0 + div0 := by
    simpa [div0] using
      covariantDivergence02At_add emb met atr conn ha conn_add_left conn_smul_left hl
        (0 : TensorData R V 0 2) (0 : TensorData R V 0 2) Y
  calc
    div0 = (div0 + div0) - div0 := by ring
    _ = div0 - div0 := by rw [h.symm]
    _ = 0 := by ring

/-- If `c` is spatially constant, the divergence endomorphism of `c • T` is
`c` times the divergence endomorphism of `T`. The hypothesis is stated directly
as `forall X, action emb X c = 0` so this core tensor API does not depend on the
`SpatialConstant` module. -/
theorem covDivergence02Endomorphism_const_smul
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (c : R) (hc : forall X : V, action emb X c = 0)
    (T : TensorData R V 0 2) (Y : V) :
    covDivergence02Endomorphism emb met conn ha conn_add_left conn_smul_left hl
        (c • T) Y =
      c • covDivergence02Endomorphism emb met conn ha conn_add_left conn_smul_left hl T Y := by
  ext X
  apply met.eq_of_forall_g_eq
  intro Z
  change
    met.g
      (met.sharp
        (covDeriv02TraceCovector emb conn ha hl X (c • T) Y)) Z =
      met.g
        (c • met.sharp (covDeriv02TraceCovector emb conn ha hl X T Y)) Z
  rw [met.g_sharp, met.g_smul_left, met.g_sharp]
  rw [covDeriv02TraceCovector_apply emb conn ha hl X (c • T) Y Z,
    covDeriv02TraceCovector_apply emb conn ha hl X T Y Z]
  rw [nabla_smul emb conn ha hl X c T ![Z, Y] ![]]
  have hX : (emb.embed X) c = 0 := by
    simpa [action] using hc X
  rw [hX, zero_mul, zero_add]

/-- Divergence of a spatially constant scalar multiple of a `(0,2)` tensor. -/
theorem covariantDivergence02At_const_smul
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (c : R) (hc : forall X : V, action emb X c = 0)
    (T : TensorData R V 0 2) (Y : V) :
    covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
        (c • T) Y =
      c * covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
        T Y := by
  unfold covariantDivergence02At
  rw [covDivergence02Endomorphism_const_smul emb met conn ha conn_add_left
    conn_smul_left hl c hc T Y, map_smul]
  rfl

/-- Divergence of the negative of a `(0,2)` tensor. -/
theorem covariantDivergence02At_neg
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (T : TensorData R V 0 2) (Y : V) :
    covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
        (-T) Y =
      -covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
        T Y := by
  have hneg_const : forall X : V, action emb X (-1 : R) = 0 := by
    intro X
    rw [action_neg_right emb X (1 : R), action_one emb X, neg_zero]
  have hsmul :=
    covariantDivergence02At_const_smul emb met atr conn ha conn_add_left
      conn_smul_left hl (-1 : R) hneg_const T Y
  rw [neg_one_smul R T] at hsmul
  simpa using hsmul

/-- Divergence of a difference of `(0,2)` tensors. -/
theorem covariantDivergence02At_sub
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (T S : TensorData R V 0 2) (Y : V) :
    covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
        (T - S) Y =
      covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
        T Y -
      covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
        S Y := by
  rw [sub_eq_add_neg,
    covariantDivergence02At_add emb met atr conn ha conn_add_left conn_smul_left hl,
    covariantDivergence02At_neg emb met atr conn ha conn_add_left conn_smul_left hl,
    sub_eq_add_neg]

/-- Divergence of a scalar multiple of the metric:
`div(f g)(Y) = Y(f)`. This is the Section 14.2 product-rule calculation
needed to turn an Einstein Ricci formula into a divergence formula. -/
theorem covariantDivergence02At_smul_metric
    (emb : DerivationEmbedding k R V) (met : MetricDuality R V)
    (atr : AbstractTrace R V) (conn : V -> V -> V)
    (ha : forall X Y Z : V, conn X (Y + Z) = conn X Y + conn X Z)
    (conn_add_left : forall X Y Z : V, conn (X + Y) Z = conn X Z + conn Y Z)
    (conn_smul_left : forall (f : R) (X Z : V), conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) (Y : V),
      conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (h_mc : IsMetricCompatible emb conn met)
    (f : R) (Y : V) :
    covariantDivergence02At emb met atr conn ha conn_add_left conn_smul_left hl
      (f • met.g_tensor) Y = action emb Y f := by
  let df : V →ₗ[R] R := {
    toFun X := action emb X f
    map_add' X Z := action_add_left emb X Z f
    map_smul' c X := by
      simp only [RingHom.id_apply, smul_eq_mul]
      exact action_smul_left emb c X f }
  rw [covariantDivergence02At_eval]
  have h_endo :
      covDivergence02Endomorphism emb met conn ha conn_add_left conn_smul_left hl
        (f • met.g_tensor) Y =
        df.smulRight Y := by
    ext X
    apply met.eq_of_forall_g_eq
    intro Z
    change
      met.g
        (met.sharp
          (covDeriv02TraceCovector emb conn ha hl X (f • met.g_tensor) Y)) Z =
        met.g ((df.smulRight Y) X) Z
    rw [met.g_sharp]
    rw [covDeriv02TraceCovector_apply emb conn ha hl X (f • met.g_tensor) Y Z]
    rw [nabla_smul emb conn ha hl X f met.g_tensor ![Z, Y] ![]]
    rw [nabla_g_zero emb conn ha hl met h_mc X]
    simp only [MultilinearMap.zero_apply, mul_zero, add_zero, LinearMap.smulRight_apply]
    change action emb X f * met.g Z Y = met.g (action emb X f • Y) Z
    rw [met.g_smul_left, met.g_symm Z Y]
  rw [h_endo]
  exact atr.trace_outer Y df

end TensorDivergence02
