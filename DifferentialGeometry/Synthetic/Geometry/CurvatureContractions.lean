import DifferentialGeometry.Synthetic.Algebra.MetricTrace
import DifferentialGeometry.Synthetic.Geometry.ConnectionExtended

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open SyntheticTensor

/-!
# Curvature Lowering and Contraction Interfaces

This file connects the general metric-trace infrastructure to curvature. The
scalar lowered curvature forms are concrete and proved from the existing
synthetic `Rm`/`covDerivRm` objects. The final contracted-Bianchi theorem still
needs the general double-trace Fubini/coherence rule for the relevant `(0,5)`
tensor; that rule is named in `Algebra/MetricTrace.lean`.
-/

namespace SyntheticTensor

section LoweredCurvature

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

/-- Lowered Riemann curvature, `Rm_{XYZW} = g(Rm(X,Y)Z, W)`. -/
noncomputable def Rm_lowered
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) (X Y Z W : V) : R :=
  met.g (Rm emb conn X Y Z) W

/-- Interface for a lowered Riemann `(0,4)` tensor. The realization can build
this either from a general `lower_index` evaluation theorem applied to
`Rm_tensor`, or directly from coordinates. Keeping this as a structure avoids
duplicating a large multilinearity proof here. -/
structure LoweredRmTensorData
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) where
  tensor : TensorData R V 0 4
  eval : forall X Y Z W,
    tensor ![X, Y, Z, W] ![] = Rm_lowered emb conn met X Y Z W

/-- The lowered Riemann tensor as an actual `(0,4)` tensor. -/
noncomputable def loweredRmTensor
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) : TensorData R V 0 4 where
  toFun vs := MultilinearMap.constOfIsEmpty _ _
    (Rm_lowered emb conn met (vs 0) (vs 1) (vs 2) (vs 3))
  map_update_add' := by
    intro inst vs idx v₁ v₂
    ext αs
    have : inst = instDecidableEqFin 4 := Subsingleton.elim _ _
    subst this
    simp only [MultilinearMap.constOfIsEmpty, MultilinearMap.add_apply,
      MultilinearMap.coe_mk]
    fin_cases idx
    · simp only [Fin.isValue, Function.update_self, ne_eq, one_ne_zero, OfNat.ofNat_ne_zero,
        not_false_eq_true, Function.update_of_ne, Fin.reduceEq, Function.const_apply]
      change Rm_lowered emb conn met (v₁ + v₂) (vs 1) (vs 2) (vs 3) =
        Rm_lowered emb conn met v₁ (vs 1) (vs 2) (vs 3) +
          Rm_lowered emb conn met v₂ (vs 1) (vs 2) (vs 3)
      unfold Rm_lowered
      rw [Rm_add_X emb conn ha hal, met.g_add_left]
    · simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne,
        Function.update_self, OfNat.ofNat_ne_zero, Fin.reduceEq, Function.const_apply]
      change Rm_lowered emb conn met (vs 0) (v₁ + v₂) (vs 2) (vs 3) =
        Rm_lowered emb conn met (vs 0) v₁ (vs 2) (vs 3) +
          Rm_lowered emb conn met (vs 0) v₂ (vs 2) (vs 3)
      unfold Rm_lowered
      rw [Rm_add_Y emb conn ha hal, met.g_add_left]
    · simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, Function.const_apply]
      change Rm_lowered emb conn met (vs 0) (vs 1) (v₁ + v₂) (vs 3) =
        Rm_lowered emb conn met (vs 0) (vs 1) v₁ (vs 3) +
          Rm_lowered emb conn met (vs 0) (vs 1) v₂ (vs 3)
      unfold Rm_lowered
      rw [Rm_add_Z emb conn ha hal, met.g_add_left]
    · simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, Function.const_apply]
      change Rm_lowered emb conn met (vs 0) (vs 1) (vs 2) (v₁ + v₂) =
        Rm_lowered emb conn met (vs 0) (vs 1) (vs 2) v₁ +
          Rm_lowered emb conn met (vs 0) (vs 1) (vs 2) v₂
      unfold Rm_lowered
      rw [met.g_add_right]
  map_update_smul' := by
    intro inst vs idx c v
    ext αs
    have : inst = instDecidableEqFin 4 := Subsingleton.elim _ _
    subst this
    simp only [MultilinearMap.constOfIsEmpty, MultilinearMap.smul_apply,
      MultilinearMap.coe_mk, smul_eq_mul]
    fin_cases idx
    · simp only [Fin.isValue, Function.update_self, ne_eq, one_ne_zero, OfNat.ofNat_ne_zero,
        not_false_eq_true, Function.update_of_ne, Fin.reduceEq, Function.const_apply]
      change Rm_lowered emb conn met (c • v) (vs 1) (vs 2) (vs 3) =
        c * Rm_lowered emb conn met v (vs 1) (vs 2) (vs 3)
      unfold Rm_lowered
      rw [Rm_smul_X emb conn hal hsl hl, met.g_smul_left]
    · simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne,
        Function.update_self, OfNat.ofNat_ne_zero, Fin.reduceEq, Function.const_apply]
      change Rm_lowered emb conn met (vs 0) (c • v) (vs 2) (vs 3) =
        c * Rm_lowered emb conn met (vs 0) v (vs 2) (vs 3)
      unfold Rm_lowered
      rw [Rm_smul_Y emb conn hal hsl hl, met.g_smul_left]
    · simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, Function.const_apply]
      change Rm_lowered emb conn met (vs 0) (vs 1) (c • v) (vs 3) =
        c * Rm_lowered emb conn met (vs 0) (vs 1) v (vs 3)
      unfold Rm_lowered
      rw [Rm_smul_Z emb conn ha hsl hl, met.g_smul_left]
    · simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, Function.const_apply]
      change Rm_lowered emb conn met (vs 0) (vs 1) (vs 2) (c • v) =
        c * Rm_lowered emb conn met (vs 0) (vs 1) (vs 2) v
      unfold Rm_lowered
      rw [met.g_smul_right]

theorem loweredRmTensor_eval
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (X Y Z W : V) :
    loweredRmTensor emb conn ha hal hsl hl met ![X, Y, Z, W] ![] =
      Rm_lowered emb conn met X Y Z W := by
  rfl

theorem loweredRmTensor_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (vs : Fin 4 -> V) :
    loweredRmTensor emb conn ha hal hsl hl met vs ![] =
      Rm_lowered emb conn met (vs 0) (vs 1) (vs 2) (vs 3) := by
  rfl

/-- The lowered curvature is antisymmetric in its first two arguments. -/
theorem Rm_lowered_antisymm_first_pair
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V) (X Y Z W : V) :
    Rm_lowered emb conn met X Y Z W =
      -Rm_lowered emb conn met Y X Z W := by
  unfold Rm_lowered
  rw [Rm_antisymm emb conn hal X Y Z, met.g_neg_left]

/-- The lowered curvature is antisymmetric in its last two arguments. -/
theorem Rm_lowered_antisymm_second_pair
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) (h_mc : IsMetricCompatible emb conn met)
    (X Y Z W : V) :
    Rm_lowered emb conn met X Y Z W =
      -Rm_lowered emb conn met X Y W Z := by
  unfold Rm_lowered
  exact Rm_metric_antisymm emb conn met h_mc X Y Z W

/-- Block symmetry for the lowered curvature:
`Rm_lowered X Y Z W = Rm_lowered Z W X Y`. -/
theorem Rm_lowered_block_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    [Invertible (2 : R)]
    (_h2 : forall (a : R), 2 * a = 0 -> a = 0)
    (X Y Z W : V) :
    Rm_lowered emb conn met X Y Z W =
      Rm_lowered emb conn met Z W X Y := by
  unfold Rm_lowered
  exact Rm_symm_blocks emb conn ha hal met h_mc h_tf X Y Z W

/-- Algebraic first Bianchi identity for lowered curvature. -/
theorem Rm_lowered_first_bianchi
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V) (h_tf : IsTorsionFree emb conn)
    (X Y Z W : V) :
    Rm_lowered emb conn met X Y Z W +
        Rm_lowered emb conn met Y Z X W +
          Rm_lowered emb conn met Z X Y W = 0 := by
  have h := first_bianchi emb conn ha hal h_tf X Y Z
  have hg := congr_arg (fun U : V => met.g U W) h
  unfold Rm_lowered at *
  have hzero : met.g 0 W = 0 := by
    have hz := met.g_add_left 0 0 W
    simpa using hz.symm
  simpa [met.g_add_left, hzero] using hg

/-- Evaluation-level algebraic first Bianchi identity for the lowered
curvature tensor. -/
theorem loweredRmTensor_first_bianchi
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (h_tf : IsTorsionFree emb conn)
    (X Y Z W : V) :
    loweredRmTensor emb conn ha hal hsl hl met ![X, Y, Z, W] ![] +
        loweredRmTensor emb conn ha hal hsl hl met ![Y, Z, X, W] ![] +
          loweredRmTensor emb conn ha hal hsl hl met ![Z, X, Y, W] ![] = 0 := by
  rw [loweredRmTensor_eval, loweredRmTensor_eval, loweredRmTensor_eval]
  exact Rm_lowered_first_bianchi emb conn ha hal met h_tf X Y Z W

/-- Evaluation-level first-pair antisymmetry for the lowered curvature tensor. -/
theorem loweredRmTensor_antisymm_first_pair
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (X Y Z W : V) :
    loweredRmTensor emb conn ha hal hsl hl met ![X, Y, Z, W] ![] =
      -loweredRmTensor emb conn ha hal hsl hl met ![Y, X, Z, W] ![] := by
  rw [loweredRmTensor_eval, loweredRmTensor_eval]
  exact Rm_lowered_antisymm_first_pair emb conn hal met X Y Z W

/-- Evaluation-level second-pair antisymmetry for the lowered curvature tensor. -/
theorem loweredRmTensor_antisymm_second_pair
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (h_mc : IsMetricCompatible emb conn met)
    (X Y Z W : V) :
    loweredRmTensor emb conn ha hal hsl hl met ![X, Y, Z, W] ![] =
      -loweredRmTensor emb conn ha hal hsl hl met ![X, Y, W, Z] ![] := by
  rw [loweredRmTensor_eval, loweredRmTensor_eval]
  exact Rm_lowered_antisymm_second_pair emb conn met h_mc X Y Z W

/-- Evaluation-level block symmetry for the lowered curvature tensor. -/
theorem loweredRmTensor_block_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    [Invertible (2 : R)]
    (_h2 : forall (a : R), 2 * a = 0 -> a = 0)
    (X Y Z W : V) :
    loweredRmTensor emb conn ha hal hsl hl met ![X, Y, Z, W] ![] =
      loweredRmTensor emb conn ha hal hsl hl met ![Z, W, X, Y] ![] := by
  rw [loweredRmTensor_eval, loweredRmTensor_eval]
  exact Rm_lowered_block_symm emb conn ha hal met h_mc h_tf _h2 X Y Z W

/-- Constructor for the lowered Riemann tensor package. -/
noncomputable def loweredRmTensorData
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) : LoweredRmTensorData emb conn met where
  tensor := loweredRmTensor emb conn ha hal hsl hl met
  eval := loweredRmTensor_eval emb conn ha hal hsl hl met

/-- Lowered covariant derivative of Riemann curvature:
`(∇_A Rm)_{XYZW} = g((∇_A Rm)(X,Y)Z, W)`. -/
noncomputable def covDerivRm_lowered
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) (A X Y Z W : V) : R :=
  met.g (covDerivRm emb conn A X Y Z) W

/-- Interface for the lowered covariant derivative of Riemann as a `(0,5)`
tensor. A concrete realization should build this from a general lower-index
operation applied to the vector-valued `covDerivRm`, or from coordinates.

This is the tensor object whose double metric traces give the contracted
second Bianchi identity. -/
structure LoweredCovDerivRmTensorData
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) where
  tensor : TensorData R V 0 5
  eval : forall A X Y Z W,
    tensor ![A, X, Y, Z, W] ![] =
      covDerivRm_lowered emb conn met A X Y Z W

theorem LoweredCovDerivRmTensorData.eval_apply
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V)
    (lowered : LoweredCovDerivRmTensorData emb conn met)
    (A X Y Z W : V) :
    lowered.tensor ![A, X, Y, Z, W] ![] =
      covDerivRm_lowered emb conn met A X Y Z W :=
  lowered.eval A X Y Z W

/-- Tensorize the covariant derivative of the lowered Riemann tensor.

This is just the general bundled tensor derivative
`covariantDerivativeTensor` applied to the lowered `(0,4)` curvature tensor;
the first covariant slot is the derivative direction. -/
noncomputable def covDerivRmLoweredTensor
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) : TensorData R V 0 5 :=
  covariantDerivativeTensor emb conn ha hal hsl hl
    (loweredRmTensor emb conn ha hal hsl hl met)

set_option linter.flexible false in
theorem covDerivRmLoweredTensor_eval
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (h_mc : IsMetricCompatible emb conn met)
    (A X Y Z W : V) :
    covDerivRmLoweredTensor emb conn ha hal hsl hl met ![A, X, Y, Z, W] ![] =
      covDerivRm_lowered emb conn met A X Y Z W := by
  change nabla_tensor emb conn ha hl A (loweredRmTensor emb conn ha hal hsl hl met)
      ![X, Y, Z, W] ![] =
    met.g (covDerivRm emb conn A X Y Z) W
  rw [nabla_tensor_eval]
  simp only [loweredRmTensor_apply, Finset.sum_of_isEmpty, sub_zero]
  rw [Fin.sum_univ_four]
  simp [Function.update]
  unfold Rm_lowered covDerivRm
  rw [h_mc A (Rm emb conn X Y Z) W]
  rw [MetricDuality.g_sub_left, MetricDuality.g_sub_left, MetricDuality.g_sub_left]
  ring

/-- Algebraic first Bianchi identity for the covariant derivative of
curvature, in the three curvature slots. -/
theorem covDerivRm_first_bianchi
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (h_tf : IsTorsionFree emb conn)
    (A X Y Z : V) :
    covDerivRm emb conn A X Y Z +
        covDerivRm emb conn A Y Z X +
          covDerivRm emb conn A Z X Y = 0 := by
  have h0raw := congr_arg (conn A) (first_bianchi emb conn ha hal h_tf X Y Z)
  have h0 :
      conn A (Rm emb conn X Y Z) +
          conn A (Rm emb conn Y Z X) +
            conn A (Rm emb conn Z X Y) = 0 := by
    simpa [ha, conn_zero_right conn ha] using h0raw
  have hX := first_bianchi emb conn ha hal h_tf (conn A X) Y Z
  have hY := first_bianchi emb conn ha hal h_tf X (conn A Y) Z
  have hZ := first_bianchi emb conn ha hal h_tf X Y (conn A Z)
  unfold covDerivRm
  calc
    (conn A (Rm emb conn X Y Z) - Rm emb conn (conn A X) Y Z -
          Rm emb conn X (conn A Y) Z - Rm emb conn X Y (conn A Z)) +
        (conn A (Rm emb conn Y Z X) - Rm emb conn (conn A Y) Z X -
          Rm emb conn Y (conn A Z) X - Rm emb conn Y Z (conn A X)) +
          (conn A (Rm emb conn Z X Y) - Rm emb conn (conn A Z) X Y -
            Rm emb conn Z (conn A X) Y - Rm emb conn Z X (conn A Y))
        =
      (conn A (Rm emb conn X Y Z) +
          conn A (Rm emb conn Y Z X) +
            conn A (Rm emb conn Z X Y)) -
        (Rm emb conn (conn A X) Y Z +
          Rm emb conn Y Z (conn A X) +
            Rm emb conn Z (conn A X) Y) -
        (Rm emb conn X (conn A Y) Z +
          Rm emb conn (conn A Y) Z X +
            Rm emb conn Z X (conn A Y)) -
        (Rm emb conn X Y (conn A Z) +
          Rm emb conn Y (conn A Z) X +
            Rm emb conn (conn A Z) X Y) := by
        abel
    _ = 0 := by
        rw [h0, hX, hY, hZ]
        abel

/-- Lowered algebraic first Bianchi identity for the covariant derivative of
curvature, in the three curvature slots. -/
theorem covDerivRm_lowered_first_bianchi
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V) (h_tf : IsTorsionFree emb conn)
    (A X Y Z W : V) :
    covDerivRm_lowered emb conn met A X Y Z W +
        covDerivRm_lowered emb conn met A Y Z X W +
          covDerivRm_lowered emb conn met A Z X Y W = 0 := by
  have h := covDerivRm_first_bianchi emb conn ha hal h_tf A X Y Z
  have hg := congr_arg (fun U : V => met.g U W) h
  unfold covDerivRm_lowered at *
  have hzero : met.g 0 W = 0 := by
    have hz := met.g_add_left 0 0 W
    simpa using hz.symm
  simpa [met.g_add_left, hzero] using hg

/-- Evaluation-level algebraic first Bianchi identity for the lowered `∇Rm`
tensor, in slots `(1, 2, 3)` of `T(A, X, Y, Z, W)`. -/
theorem covDerivRmLoweredTensor_first_bianchi
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (h_mc : IsMetricCompatible emb conn met)
    (h_tf : IsTorsionFree emb conn) (A X Y Z W : V) :
    covDerivRmLoweredTensor emb conn ha hal hsl hl met ![A, X, Y, Z, W] ![] +
        covDerivRmLoweredTensor emb conn ha hal hsl hl met ![A, Y, Z, X, W] ![] +
          covDerivRmLoweredTensor emb conn ha hal hsl hl met ![A, Z, X, Y, W] ![] = 0 := by
  rw [covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc,
    covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc,
    covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc]
  exact covDerivRm_lowered_first_bianchi emb conn ha hal met h_tf A X Y Z W

/-- The covariant derivative of curvature is antisymmetric in the two
curvature-operator slots. -/
theorem covDerivRm_antisymm_first_pair
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (A X Y Z : V) :
    covDerivRm emb conn A X Y Z =
      -covDerivRm emb conn A Y X Z := by
  unfold covDerivRm
  rw [Rm_antisymm emb conn hal X Y Z, conn_neg_right conn ha]
  rw [Rm_antisymm emb conn hal (conn A X) Y Z]
  rw [Rm_antisymm emb conn hal X (conn A Y) Z]
  rw [Rm_antisymm emb conn hal Y X (conn A Z)]
  abel

/-- The lowered covariant derivative of curvature is antisymmetric in the two
curvature-operator slots. -/
theorem covDerivRm_lowered_antisymm_first_pair
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V) (A X Y Z W : V) :
    covDerivRm_lowered emb conn met A X Y Z W =
      -covDerivRm_lowered emb conn met A Y X Z W := by
  unfold covDerivRm_lowered
  rw [covDerivRm_antisymm_first_pair emb conn ha hal A X Y Z, met.g_neg_left]

/-- Evaluation-level first-pair antisymmetry for the lowered `∇Rm` tensor. -/
theorem covDerivRmLoweredTensor_antisymm_first_pair
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (h_mc : IsMetricCompatible emb conn met)
    (A X Y Z W : V) :
    covDerivRmLoweredTensor emb conn ha hal hsl hl met ![A, X, Y, Z, W] ![] =
      -covDerivRmLoweredTensor emb conn ha hal hsl hl met ![A, Y, X, Z, W] ![] := by
  rw [covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc]
  rw [covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc]
  exact covDerivRm_lowered_antisymm_first_pair emb conn ha hal met A X Y Z W

/-- The lowered covariant derivative of curvature is antisymmetric in the
last two curvature slots. This is the differentiated form of
`Rm_metric_antisymm`; metric compatibility supplies the differentiated metric
pairing terms. -/
theorem covDerivRm_lowered_antisymm_second_pair
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) (h_mc : IsMetricCompatible emb conn met)
    (A X Y Z W : V) :
    covDerivRm_lowered emb conn met A X Y Z W =
      -covDerivRm_lowered emb conn met A X Y W Z := by
  unfold covDerivRm_lowered covDerivRm
  have h_der := congr_arg (emb.embed A)
    (Rm_metric_antisymm emb conn met h_mc X Y Z W)
  simp only [map_neg] at h_der
  have h_conn :
      met.g (conn A (Rm emb conn X Y Z)) W =
        -met.g (conn A (Rm emb conn X Y W)) Z +
          met.g (Rm emb conn X Y (conn A Z)) W +
            met.g (Rm emb conn X Y (conn A W)) Z := by
    have h1 := h_mc A (Rm emb conn X Y Z) W
    have h2 := h_mc A (Rm emb conn X Y W) Z
    have h1' :
        met.g (conn A (Rm emb conn X Y Z)) W =
          (emb.embed A) (met.g (Rm emb conn X Y Z) W) -
            met.g (Rm emb conn X Y Z) (conn A W) := by
      rw [h1]
      ring
    calc
      met.g (conn A (Rm emb conn X Y Z)) W
          = (emb.embed A) (met.g (Rm emb conn X Y Z) W) -
              met.g (Rm emb conn X Y Z) (conn A W) := h1'
      _ = -(emb.embed A) (met.g (Rm emb conn X Y W) Z) -
              met.g (Rm emb conn X Y Z) (conn A W) := by
            rw [h_der]
      _ = -(met.g (conn A (Rm emb conn X Y W)) Z +
              met.g (Rm emb conn X Y W) (conn A Z)) -
              met.g (Rm emb conn X Y Z) (conn A W) := by
            rw [h2]
      _ = -met.g (conn A (Rm emb conn X Y W)) Z +
            met.g (Rm emb conn X Y (conn A Z)) W +
              met.g (Rm emb conn X Y (conn A W)) Z := by
            rw [Rm_metric_antisymm emb conn met h_mc X Y W (conn A Z)]
            rw [Rm_metric_antisymm emb conn met h_mc X Y Z (conn A W)]
            ring
  simp only [MetricDuality.g_sub_left]
  rw [h_conn]
  rw [Rm_metric_antisymm emb conn met h_mc (conn A X) Y Z W]
  rw [Rm_metric_antisymm emb conn met h_mc X (conn A Y) Z W]
  ring

/-- Evaluation-level second-pair antisymmetry for the lowered `∇Rm` tensor. -/
theorem covDerivRmLoweredTensor_antisymm_second_pair
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (h_mc : IsMetricCompatible emb conn met)
    (A X Y Z W : V) :
    covDerivRmLoweredTensor emb conn ha hal hsl hl met ![A, X, Y, Z, W] ![] =
      -covDerivRmLoweredTensor emb conn ha hal hsl hl met ![A, X, Y, W, Z] ![] := by
  rw [covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc]
  rw [covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc]
  exact covDerivRm_lowered_antisymm_second_pair emb conn met h_mc A X Y Z W

/-- Block symmetry for the lowered covariant derivative of curvature:
`(nabla_A Rm)_{XYZW} = (nabla_A Rm)_{ZWXY}`.

This is the differentiated form of `Rm_symm_blocks`. Metric compatibility is
used to move the derivative through the two metric pairings; the correction
terms are then matched by the ordinary block symmetry. -/
theorem covDerivRm_lowered_block_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    [Invertible (2 : R)]
    (_h2 : forall (a : R), 2 * a = 0 -> a = 0)
    (A X Y Z W : V) :
    covDerivRm_lowered emb conn met A X Y Z W =
      covDerivRm_lowered emb conn met A Z W X Y := by
  unfold covDerivRm_lowered covDerivRm
  have h_der := congr_arg (emb.embed A)
    (Rm_symm_blocks emb conn ha hal met h_mc h_tf X Y Z W)
  have h_conn :
      met.g (conn A (Rm emb conn X Y Z)) W =
        met.g (conn A (Rm emb conn Z W X)) Y +
          met.g (Rm emb conn Z W X) (conn A Y) -
            met.g (Rm emb conn X Y Z) (conn A W) := by
    have h1 := h_mc A (Rm emb conn X Y Z) W
    have h2m := h_mc A (Rm emb conn Z W X) Y
    have h1' :
        met.g (conn A (Rm emb conn X Y Z)) W =
          (emb.embed A) (met.g (Rm emb conn X Y Z) W) -
            met.g (Rm emb conn X Y Z) (conn A W) := by
      rw [h1]
      ring
    calc
      met.g (conn A (Rm emb conn X Y Z)) W
          = (emb.embed A) (met.g (Rm emb conn X Y Z) W) -
              met.g (Rm emb conn X Y Z) (conn A W) := h1'
      _ = (emb.embed A) (met.g (Rm emb conn Z W X) Y) -
              met.g (Rm emb conn X Y Z) (conn A W) := by
            rw [h_der]
      _ = (met.g (conn A (Rm emb conn Z W X)) Y +
              met.g (Rm emb conn Z W X) (conn A Y)) -
              met.g (Rm emb conn X Y Z) (conn A W) := by
            rw [h2m]
      _ = met.g (conn A (Rm emb conn Z W X)) Y +
            met.g (Rm emb conn Z W X) (conn A Y) -
              met.g (Rm emb conn X Y Z) (conn A W) := by
            ring
  simp only [MetricDuality.g_sub_left]
  rw [h_conn]
  rw [Rm_symm_blocks emb conn ha hal met h_mc h_tf (conn A X) Y Z W]
  rw [Rm_symm_blocks emb conn ha hal met h_mc h_tf X (conn A Y) Z W]
  rw [Rm_symm_blocks emb conn ha hal met h_mc h_tf X Y (conn A Z) W]
  rw [Rm_symm_blocks emb conn ha hal met h_mc h_tf X Y Z (conn A W)]
  ring

/-- Evaluation-level block symmetry for the lowered `nabla Rm` tensor. -/
theorem covDerivRmLoweredTensor_block_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    [Invertible (2 : R)]
    (h2 : forall (a : R), 2 * a = 0 -> a = 0)
    (A X Y Z W : V) :
    covDerivRmLoweredTensor emb conn ha hal hsl hl met ![A, X, Y, Z, W] ![] =
      covDerivRmLoweredTensor emb conn ha hal hsl hl met ![A, Z, W, X, Y] ![] := by
  rw [covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc]
  rw [covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc]
  exact covDerivRm_lowered_block_symm emb conn ha hal met h_mc h_tf h2 A X Y Z W

/-- Constructor for the lowered `∇Rm` tensor package. It uses the covariant
derivative of the already-constructed lowered Riemann tensor and metric
compatibility to identify the evaluation with `g((∇Rm)(...), ...)`. -/
noncomputable def loweredCovDerivRmTensorData
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V) (h_mc : IsMetricCompatible emb conn met) :
    LoweredCovDerivRmTensorData emb conn met where
  tensor := covDerivRmLoweredTensor emb conn ha hal hsl hl met
  eval := covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc

/-- The lowered second Bianchi identity, obtained by pairing the vector-level
second Bianchi identity with the metric. -/
theorem covDerivRm_lowered_cyclic_sum
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V)
    (h_tf : IsTorsionFree emb conn) (A X Y Z W : V) :
    covDerivRm_lowered emb conn met A X Y Z W +
        covDerivRm_lowered emb conn met X Y A Z W +
          covDerivRm_lowered emb conn met Y A X Z W = 0 := by
  have h := covDerivRm_sum_endo emb conn ha hal h_tf A X Y Z
  have hg := congr_arg (fun U : V => met.g U W) h
  unfold covDerivRm_lowered at *
  have hg0 :
      met.g (covDerivRm emb conn A X Y Z + covDerivRm emb conn X Y A Z +
        covDerivRm emb conn Y A X Z) W = 0 := by
    have hzero : met.g 0 W = 0 := by
      have hz := met.g_add_left 0 0 W
      simpa using hz.symm
    simpa [hzero] using hg
  rw [met.g_add_left, met.g_add_left] at hg0
  exact hg0

/-- The first cyclic permutation of the first three covariant slots of a
lowered `(0,5)` curvature-derivative tensor:
`T(A, X, Y, Z, W)` becomes `T(X, Y, A, Z, W)`. -/
noncomputable def covariantCycle012Left05
    (T : TensorData R V 0 5) : TensorData R V 0 5 :=
  swap_covariant (0 : Fin 5) 2 (swap_covariant (0 : Fin 5) 1 T)

theorem covariantCycle012Left05_eval
    (T : TensorData R V 0 5) (A X Y Z W : V) :
    covariantCycle012Left05 T ![A, X, Y, Z, W] ![] =
      T ![X, Y, A, Z, W] ![] := by
  unfold covariantCycle012Left05
  simp only [swap_covariant_eval]
  rw [show (((![A, X, Y, Z, W] : Fin 5 -> V) ∘ Equiv.swap (0 : Fin 5) 2) ∘
      Equiv.swap (0 : Fin 5) 1) = ![X, Y, A, Z, W] from by
    ext i
    fin_cases i <;> rfl]

/-- The second cyclic permutation of the first three covariant slots of a
lowered `(0,5)` curvature-derivative tensor:
`T(A, X, Y, Z, W)` becomes `T(Y, A, X, Z, W)`. -/
noncomputable def covariantCycle012Right05
    (T : TensorData R V 0 5) : TensorData R V 0 5 :=
  swap_covariant (0 : Fin 5) 1 (swap_covariant (0 : Fin 5) 2 T)

theorem covariantCycle012Right05_eval
    (T : TensorData R V 0 5) (A X Y Z W : V) :
    covariantCycle012Right05 T ![A, X, Y, Z, W] ![] =
      T ![Y, A, X, Z, W] ![] := by
  unfold covariantCycle012Right05
  simp only [swap_covariant_eval]
  rw [show (((![A, X, Y, Z, W] : Fin 5 -> V) ∘ Equiv.swap (0 : Fin 5) 1) ∘
      Equiv.swap (0 : Fin 5) 2) = ![Y, A, X, Z, W] from by
    ext i
    fin_cases i <;> rfl]

/-- Tensor form of the lowered second Bianchi identity for
`T(A, X, Y, Z, W) = (∇_A Rm)(X,Y,Z,W)`. -/
theorem covDerivRmLoweredTensor_cyclic_sum_tensor
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn) :
    covDerivRmLoweredTensor emb conn ha hal hsl hl met +
        covariantCycle012Left05 (covDerivRmLoweredTensor emb conn ha hal hsl hl met) +
          covariantCycle012Right05 (covDerivRmLoweredTensor emb conn ha hal hsl hl met) =
      0 := by
  ext vs αs
  have hα : αs = ![] := by
    ext i
    exact i.elim0
  rw [hα]
  have hvs : vs = ![vs 0, vs 1, vs 2, vs 3, vs 4] := by
    ext i
    fin_cases i <;> rfl
  rw [hvs]
  simp only [MultilinearMap.add_apply, MultilinearMap.zero_apply]
  rw [covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc]
  rw [covariantCycle012Left05_eval,
    covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc]
  rw [covariantCycle012Right05_eval,
    covDerivRmLoweredTensor_eval emb conn ha hal hsl hl met h_mc]
  exact covDerivRm_lowered_cyclic_sum emb conn ha hal met h_tf
    (vs 0) (vs 1) (vs 2) (vs 3) (vs 4)

/-- Covariant derivative of the lowered Riemann tensor in a fixed derivative
direction. This is the `(0,4)` tensor `∇_A Rm_lowered`. -/
noncomputable def covDerivRmLoweredTensorAt
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (met : MetricDuality R V)
    (lowered : LoweredRmTensorData emb conn met) (A : V) : TensorData R V 0 4 :=
  nabla_tensor emb conn ha hl A lowered.tensor

end LoweredCurvature

end SyntheticTensor
