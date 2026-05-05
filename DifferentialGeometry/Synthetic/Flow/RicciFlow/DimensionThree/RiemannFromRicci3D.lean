import DifferentialGeometry.Synthetic.Flow.RicciFlow.DimensionThree.CurvatureAlgebra
import DifferentialGeometry.Synthetic.Geometry.CurvatureContractions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Multilinear.Basis

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Three-Dimensional Riemann-From-Ricci Calculus Package

This file is the P2 architecture layer. It does not prove the dimension-three
curvature decomposition yet; instead it names the residual calculation that a
synthetic or realization proof must discharge, and turns that residual into the
existing `RiemannFromRicci3DFormula` interface.
-/

open BigOperators
open SyntheticTensor

section RiemannFromRicci3D

variable {k R V : Type*}
variable [Field k] [CommRing R] [Algebra k R]
variable [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]

private theorem tensor02_add_left (T : TensorData R V 0 2) (X₁ X₂ Y : V) :
    T ![X₁ + X₂, Y] ![] = T ![X₁, Y] ![] + T ![X₂, Y] ![] := by
  have h := T.map_update_add ![X₁, Y] (0 : Fin 2) X₁ X₂
  have hu : forall v, Function.update (![X₁, Y] : Fin 2 -> V) 0 v = ![v, Y] := by
    intro v
    ext i
    fin_cases i <;> simp [Function.update]
  simp only [hu] at h
  exact congr_arg (fun S => S ![]) h

private theorem tensor02_add_right (T : TensorData R V 0 2) (X Y₁ Y₂ : V) :
    T ![X, Y₁ + Y₂] ![] = T ![X, Y₁] ![] + T ![X, Y₂] ![] := by
  have h := T.map_update_add ![X, Y₁] (1 : Fin 2) Y₁ Y₂
  have hu : forall v, Function.update (![X, Y₁] : Fin 2 -> V) 1 v = ![X, v] := by
    intro v
    ext i
    fin_cases i <;> simp [Function.update]
  simp only [hu] at h
  exact congr_arg (fun S => S ![]) h

private theorem tensor02_smul_left (T : TensorData R V 0 2) (c : R) (X Y : V) :
    T ![c • X, Y] ![] = c * T ![X, Y] ![] := by
  have h := T.map_update_smul ![X, Y] (0 : Fin 2) c X
  have hu : forall v, Function.update (![X, Y] : Fin 2 -> V) 0 v = ![v, Y] := by
    intro v
    ext i
    fin_cases i <;> simp [Function.update]
  simp only [hu, smul_eq_mul] at h
  exact congr_arg (fun S => S ![]) h

private theorem tensor02_smul_right (T : TensorData R V 0 2) (c : R) (X Y : V) :
    T ![X, c • Y] ![] = c * T ![X, Y] ![] := by
  have h := T.map_update_smul ![X, Y] (1 : Fin 2) c Y
  have hu : forall v, Function.update (![X, Y] : Fin 2 -> V) 1 v = ![X, v] := by
    intro v
    ext i
    fin_cases i <;> simp [Function.update]
  simp only [hu, smul_eq_mul] at h
  exact congr_arg (fun S => S ![]) h

private theorem tensor02_symm_apply (T : TensorData R V 0 2)
    (h_symm : swap_covariant (0 : Fin 2) 1 T = T) (X Y : V) :
    T ![Y, X] ![] = T ![X, Y] ![] := by
  have h := congr_arg (fun S : TensorData R V 0 2 => S ![X, Y] ![]) h_symm
  simp only [swap_covariant_eval] at h
  rw [show ((![X, Y] : Fin 2 -> V) ∘ Equiv.swap (0 : Fin 2) 1) = ![Y, X] from by
    ext i
    fin_cases i <;> rfl] at h
  exact h

/-- The algebraic Riemann-from-Ricci right hand side as a `(0,4)` tensor. -/
noncomputable def riemannFromRicci3DRHSTensor
    (met : MetricDuality R V) (Rc : TensorData R V 0 2) (scalar half : R)
    (h_half : IsHalfCoefficient half) : TensorData R V 0 4 where
  toFun vs := MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => V →ₗ[R] R)
    (riemannFromRicci3DRHS met Rc scalar half h_half (vs 0) (vs 1) (vs 2) (vs 3))
  map_update_add' := by
    intro inst vs idx U₁ U₂
    ext αs
    have : inst = instDecidableEqFin 4 := Subsingleton.elim _ _
    subst this
    have hα : αs = ![] := by ext i; exact i.elim0
    subst hα
    fin_cases idx
    · simp only [Fin.isValue, Function.update_self, ne_eq, one_ne_zero, OfNat.ofNat_ne_zero,
        not_false_eq_true, Function.update_of_ne, Fin.reduceEq, Function.const_apply,
        MultilinearMap.constOfIsEmpty_apply]
      simp [riemannFromRicci3DRHS, tensor02_add_left, tensor02_add_right,
        MetricDuality.g_add_left, MetricDuality.g_add_right]
      ring
    · simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne,
        Function.update_self, OfNat.ofNat_ne_zero, Fin.reduceEq, Function.const_apply,
        MultilinearMap.constOfIsEmpty_apply]
      simp [riemannFromRicci3DRHS, tensor02_add_left, tensor02_add_right,
        MetricDuality.g_add_left, MetricDuality.g_add_right]
      ring
    · simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, Function.const_apply, MultilinearMap.constOfIsEmpty_apply]
      simp [riemannFromRicci3DRHS, tensor02_add_left, tensor02_add_right,
        MetricDuality.g_add_left, MetricDuality.g_add_right]
      ring
    · simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, Function.const_apply, MultilinearMap.constOfIsEmpty_apply]
      simp [riemannFromRicci3DRHS, tensor02_add_left, tensor02_add_right,
        MetricDuality.g_add_left, MetricDuality.g_add_right]
      ring
  map_update_smul' := by
    intro inst vs idx c U
    ext αs
    have : inst = instDecidableEqFin 4 := Subsingleton.elim _ _
    subst this
    have hα : αs = ![] := by ext i; exact i.elim0
    subst hα
    fin_cases idx
    · simp only [Fin.isValue, Function.update_self, ne_eq, one_ne_zero, OfNat.ofNat_ne_zero,
        not_false_eq_true, Function.update_of_ne, Fin.reduceEq, Function.const_apply,
        MultilinearMap.constOfIsEmpty_apply, MultilinearMap.smul_apply, smul_eq_mul]
      simp [riemannFromRicci3DRHS, tensor02_smul_left, tensor02_smul_right,
        MetricDuality.g_smul_left, MetricDuality.g_smul_right]
      ring
    · simp only [Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true, Function.update_of_ne,
        Function.update_self, OfNat.ofNat_ne_zero, Fin.reduceEq, Function.const_apply,
        MultilinearMap.constOfIsEmpty_apply, MultilinearMap.smul_apply, smul_eq_mul]
      simp [riemannFromRicci3DRHS, tensor02_smul_left, tensor02_smul_right,
        MetricDuality.g_smul_left, MetricDuality.g_smul_right]
      ring
    · simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, Function.const_apply, MultilinearMap.constOfIsEmpty_apply,
        MultilinearMap.smul_apply, smul_eq_mul]
      simp [riemannFromRicci3DRHS, tensor02_smul_left, tensor02_smul_right,
        MetricDuality.g_smul_left, MetricDuality.g_smul_right]
      ring
    · simp only [Fin.isValue, ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne,
        Function.update_self, Function.const_apply, MultilinearMap.constOfIsEmpty_apply,
        MultilinearMap.smul_apply, smul_eq_mul]
      simp [riemannFromRicci3DRHS, tensor02_smul_left, tensor02_smul_right,
        MetricDuality.g_smul_left, MetricDuality.g_smul_right]
      ring

theorem riemannFromRicci3DRHSTensor_eval
    (met : MetricDuality R V) (Rc : TensorData R V 0 2) (scalar half : R)
    (h_half : IsHalfCoefficient half) (X Y Z W : V) :
    riemannFromRicci3DRHSTensor met Rc scalar half h_half ![X, Y, Z, W] ![] =
      riemannFromRicci3DRHS met Rc scalar half h_half X Y Z W := by
  rfl

/-- The 3D Ricci/scalar algebraic RHS is skew in the first two curvature slots. -/
theorem riemannFromRicci3DRHS_antisymm_first
    (met : MetricDuality R V) (Rc : TensorData R V 0 2) (scalar half : R)
    (h_half : IsHalfCoefficient half) (X Y Z W : V) :
    riemannFromRicci3DRHS met Rc scalar half h_half Y X Z W =
      -riemannFromRicci3DRHS met Rc scalar half h_half X Y Z W := by
  unfold riemannFromRicci3DRHS
  ring

/-- The 3D Ricci/scalar algebraic RHS is skew in the last two curvature slots. -/
theorem riemannFromRicci3DRHS_antisymm_last
    (met : MetricDuality R V) (Rc : TensorData R V 0 2) (scalar half : R)
    (h_half : IsHalfCoefficient half) (X Y Z W : V) :
    riemannFromRicci3DRHS met Rc scalar half h_half X Y W Z =
      -riemannFromRicci3DRHS met Rc scalar half h_half X Y Z W := by
  unfold riemannFromRicci3DRHS
  ring

/-- If the Ricci tensor is symmetric, the 3D Ricci/scalar RHS has block symmetry. -/
theorem riemannFromRicci3DRHS_block_symm_of_ricci_symm
    (met : MetricDuality R V) (Rc : TensorData R V 0 2) (scalar half : R)
    (h_half : IsHalfCoefficient half)
    (h_Rc_symm : swap_covariant (0 : Fin 2) 1 Rc = Rc) (X Y Z W : V) :
    riemannFromRicci3DRHS met Rc scalar half h_half Z W X Y =
      riemannFromRicci3DRHS met Rc scalar half h_half X Y Z W := by
  have hRc_zx : Rc ![Z, X] ![] = Rc ![X, Z] ![] :=
    tensor02_symm_apply Rc h_Rc_symm X Z
  have hRc_wy : Rc ![W, Y] ![] = Rc ![Y, W] ![] :=
    tensor02_symm_apply Rc h_Rc_symm Y W
  have hRc_zy : Rc ![Z, Y] ![] = Rc ![Y, Z] ![] :=
    tensor02_symm_apply Rc h_Rc_symm Y Z
  have hRc_wx : Rc ![W, X] ![] = Rc ![X, W] ![] :=
    tensor02_symm_apply Rc h_Rc_symm X W
  have hg_wy : met.g W Y = met.g Y W := met.g_symm W Y
  have hg_zx : met.g Z X = met.g X Z := met.g_symm Z X
  have hg_wx : met.g W X = met.g X W := met.g_symm W X
  have hg_zy : met.g Z Y = met.g Y Z := met.g_symm Z Y
  unfold riemannFromRicci3DRHS
  rw [hRc_zx, hRc_wy, hRc_zy, hRc_wx, hg_wy, hg_zx, hg_wx, hg_zy]
  ring

/-- If the Ricci tensor is symmetric, the 3D Ricci/scalar RHS satisfies the
first Bianchi cyclic identity. -/
theorem riemannFromRicci3DRHS_first_bianchi_of_ricci_symm
    (met : MetricDuality R V) (Rc : TensorData R V 0 2) (scalar half : R)
    (h_half : IsHalfCoefficient half)
    (h_Rc_symm : swap_covariant (0 : Fin 2) 1 Rc = Rc) (X Y Z W : V) :
    riemannFromRicci3DRHS met Rc scalar half h_half X Y Z W +
        riemannFromRicci3DRHS met Rc scalar half h_half Y Z X W +
          riemannFromRicci3DRHS met Rc scalar half h_half Z X Y W = 0 := by
  have hRc_yx : Rc ![Y, X] ![] = Rc ![X, Y] ![] :=
    tensor02_symm_apply Rc h_Rc_symm X Y
  have hRc_zx : Rc ![Z, X] ![] = Rc ![X, Z] ![] :=
    tensor02_symm_apply Rc h_Rc_symm X Z
  have hRc_zy : Rc ![Z, Y] ![] = Rc ![Y, Z] ![] :=
    tensor02_symm_apply Rc h_Rc_symm Y Z
  have hg_yx : met.g Y X = met.g X Y := met.g_symm Y X
  have hg_zx : met.g Z X = met.g X Z := met.g_symm Z X
  have hg_zy : met.g Z Y = met.g Y Z := met.g_symm Z Y
  unfold riemannFromRicci3DRHS
  rw [hRc_yx, hRc_zx, hRc_zy, hg_yx, hg_zx, hg_zy]
  ring

/-- Residual form of the dimension-three Riemann-from-Ricci identity.

The intended future proof is Weyl-vanishing/dimension-three algebra: show this
residual is zero from `IsDimensionThree atr` plus the algebraic curvature
symmetries. -/
noncomputable def riemannFromRicci3DResidual
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (half : R) (h_half : IsHalfCoefficient half)
    (X Y Z W : V) : R :=
  Rm_lowered emb conn met X Y Z W -
    riemannFromRicci3DRHS met
      (ricciForm_tensor emb conn ha hal hsl hl atr)
      (ScalarCurvature emb conn ha hal hsl hl atr met) half h_half X Y Z W

/-- Tensor form of the P2 residual. This is the object component and basis
arguments should target. -/
noncomputable def riemannFromRicci3DResidualTensor
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (half : R) (h_half : IsHalfCoefficient half) : TensorData R V 0 4 :=
  loweredRmTensor emb conn ha hal hsl hl met -
    riemannFromRicci3DRHSTensor met
      (ricciForm_tensor emb conn ha hal hsl hl atr)
      (ScalarCurvature emb conn ha hal hsl hl atr met) half h_half

theorem riemannFromRicci3DResidualTensor_eval
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (half : R) (h_half : IsHalfCoefficient half) (X Y Z W : V) :
    riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half h_half
        ![X, Y, Z, W] ![] =
      riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half X Y Z W := by
  simp [riemannFromRicci3DResidualTensor, riemannFromRicci3DResidual,
    loweredRmTensor_eval, riemannFromRicci3DRHSTensor_eval]

/-- The P2 residual is skew in the first two curvature slots. -/
theorem riemannFromRicci3DResidual_antisymm_first
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (half : R) (h_half : IsHalfCoefficient half) (X Y Z W : V) :
    riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half Y X Z W =
      -riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half X Y Z W := by
  have hRm :
      Rm_lowered emb conn met Y X Z W = -Rm_lowered emb conn met X Y Z W := by
    unfold Rm_lowered
    rw [Rm_antisymm emb conn hal Y X Z, met.g_neg_left]
  have hRhs :=
    riemannFromRicci3DRHS_antisymm_first met
      (ricciForm_tensor emb conn ha hal hsl hl atr)
      (ScalarCurvature emb conn ha hal hsl hl atr met) half h_half X Y Z W
  unfold riemannFromRicci3DResidual
  rw [hRm, hRhs]
  ring

/-- The P2 residual is skew in the last two curvature slots. -/
theorem riemannFromRicci3DResidual_antisymm_last
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (half : R) (h_half : IsHalfCoefficient half) (X Y Z W : V) :
    riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half X Y W Z =
      -riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half X Y Z W := by
  have hRm :
      Rm_lowered emb conn met X Y W Z = -Rm_lowered emb conn met X Y Z W := by
    unfold Rm_lowered
    exact Rm_metric_antisymm emb conn met h_mc X Y W Z
  have hRhs :=
    riemannFromRicci3DRHS_antisymm_last met
      (ricciForm_tensor emb conn ha hal hsl hl atr)
      (ScalarCurvature emb conn ha hal hsl hl atr met) half h_half X Y Z W
  unfold riemannFromRicci3DResidual
  rw [hRm, hRhs]
  ring

/-- Under Ricci symmetry, the P2 residual has block symmetry. -/
theorem riemannFromRicci3DResidual_block_symm_of_ricci_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h_Rc_symm : swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr) =
      ricciForm_tensor emb conn ha hal hsl hl atr)
    (half : R) (h_half : IsHalfCoefficient half) (X Y Z W : V) :
    riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half Z W X Y =
      riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half X Y Z W := by
  have hRm :
      Rm_lowered emb conn met Z W X Y = Rm_lowered emb conn met X Y Z W := by
    unfold Rm_lowered
    exact Rm_symm_blocks emb conn ha hal met h_mc h_tf h2 Z W X Y
  have hRhs :=
    riemannFromRicci3DRHS_block_symm_of_ricci_symm met
      (ricciForm_tensor emb conn ha hal hsl hl atr)
      (ScalarCurvature emb conn ha hal hsl hl atr met) half h_half h_Rc_symm X Y Z W
  unfold riemannFromRicci3DResidual
  rw [hRm, hRhs]

/-- Under Ricci symmetry, the P2 residual satisfies the first Bianchi cyclic identity. -/
theorem riemannFromRicci3DResidual_first_bianchi_of_ricci_symm
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_tf : IsTorsionFree emb conn)
    (h_Rc_symm : swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr) =
      ricciForm_tensor emb conn ha hal hsl hl atr)
    (half : R) (h_half : IsHalfCoefficient half) (X Y Z W : V) :
    riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half X Y Z W +
        riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half Y Z X W +
          riemannFromRicci3DResidual emb conn ha hal hsl hl atr met half h_half Z X Y W = 0 := by
  have hRm :
      Rm_lowered emb conn met X Y Z W +
          Rm_lowered emb conn met Y Z X W +
            Rm_lowered emb conn met Z X Y W = 0 := by
    have h := first_bianchi emb conn ha hal h_tf X Y Z
    have hg := congr_arg (fun U : V => met.g U W) h
    change met.g (Rm emb conn X Y Z + Rm emb conn Y Z X + Rm emb conn Z X Y) W =
      met.g (0 : V) W at hg
    have h0 : met.g (0 : V) W = 0 := by
      simpa using met.g_smul_left (0 : R) (0 : V) W
    unfold Rm_lowered
    rw [met.g_add_left, met.g_add_left, h0] at hg
    exact hg
  have hRhs :=
    riemannFromRicci3DRHS_first_bianchi_of_ricci_symm met
      (ricciForm_tensor emb conn ha hal hsl hl atr)
      (ScalarCurvature emb conn ha hal hsl hl atr met) half h_half h_Rc_symm X Y Z W
  unfold riemannFromRicci3DResidual
  linear_combination hRm - hRhs

/-- Lowered Riemann data plus the pointwise 3D Ricci decomposition. -/
structure RiemannFromRicci3DDataPackage
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R) where
  h_half : IsHalfCoefficient half
  lowered : LoweredRmTensorData emb conn met
  formula : forall X Y Z W,
    lowered.tensor ![X, Y, Z, W] ![] =
      riemannFromRicci3DRHS met
        (ricciForm_tensor emb conn ha hal hsl hl atr)
        (ScalarCurvature emb conn ha hal hsl hl atr met) half h_half X Y Z W

/-- Named P2 calculation target.

Instances of this class should prove the residual vanishes from
`IsDimensionThree atr`. The public P2 API stays abstract-trace based; any
finite-rank or component proof should be hidden behind an instance of this
class. -/
class HasRiemannFromRicci3DCalculus
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) : Prop where
  residual_zero :
    IsDimensionThree atr ->
      forall (half : R) (h_half : IsHalfCoefficient half) (X Y Z W : V),
        riemannFromRicci3DResidual emb conn ha hal hsl hl atr met
          half h_half X Y Z W = 0

/-- Algebraic orthonormality for a `Fin 3` basis against a `MetricDuality`.

This is deliberately weaker than a Mathlib inner-product `OrthonormalBasis`:
it is the synthetic component condition needed by the P2 finite-frame route.
Concrete realization layers can bridge this from pointwise orthonormal frames
or from Mathlib's inner-product-space API. -/
def IsMetricOrthonormalBasis3
    (met : MetricDuality R V) (basis : Module.Basis (Fin 3) R V) : Prop :=
  forall i j : Fin 3,
    met.g (basis i) (basis j) = if i = j then (1 : R) else 0

/-- Trace formula in a synthetic `Fin 3` orthonormal basis.

This is the P2-specific form of the missing trace bridge: for an orthonormal
basis, the abstract trace of an endomorphism is the sum of its diagonal metric
pairings. It is stronger than `HasMetricAdjointTraceInvariant`; the latter
only compares traces of metric adjoints, while this exposes the trace as a
finite component sum. -/
class HasOrthonormalBasisTraceFormula3
    (atr : AbstractTrace R V) (met : MetricDuality R V) : Prop where
  tr_eq_sum_orthonormal3 :
    forall (basis : Module.Basis (Fin 3) R V),
      IsMetricOrthonormalBasis3 met basis ->
        forall L : (V →ₗ[R] V),
          atr.tr L = ∑ i : Fin 3, met.g (basis i) (L (basis i))

/-- Ricci diagonalization data in a synthetic `Fin 3` orthonormal frame.

This names the M1 bridge for P2. It should eventually be produced from the
spectral theorem applied to the metric-self-adjoint Ricci endomorphism. The
current synthetic layer only records the output needed by component proofs. -/
structure RicciDiagonalization3D
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) where
  basis : Module.Basis (Fin 3) R V
  orthonormal : IsMetricOrthonormalBasis3 met basis
  lambda : Fin 3 -> R
  ricci_diagonal :
    forall i j : Fin 3,
      ricciForm_tensor emb conn ha hal hsl hl atr ![basis i, basis j] ![] =
        if i = j then lambda i else 0

section SpectralDiagonalization

variable {𝕜 E : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- Finite-dimensional spectral-theorem eigenbasis in dimension three.

This works over both `ℝ` and `ℂ`. The eigenvalues are Mathlib's real-valued
eigenvalue list, coerced back to `𝕜` when used in the eigenvector equation. -/
noncomputable def symmetricEigenbasis3
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (hfin : Module.finrank 𝕜 E = 3) :
    OrthonormalBasis (Fin 3) 𝕜 E :=
  hT.eigenvectorBasis hfin

/-- The real eigenvalues associated to `symmetricEigenbasis3`. -/
noncomputable def symmetricEigenvalues3
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (hfin : Module.finrank 𝕜 E = 3) :
    Fin 3 -> ℝ :=
  hT.eigenvalues hfin

theorem symmetricEigenbasis3_apply
    (T : E →ₗ[𝕜] E) (hT : T.IsSymmetric)
    (hfin : Module.finrank 𝕜 E = 3) (i : Fin 3) :
    T (symmetricEigenbasis3 T hT hfin i) =
      (symmetricEigenvalues3 T hT hfin i : 𝕜) •
        symmetricEigenbasis3 T hT hfin i := by
  exact hT.apply_eigenvectorBasis hfin i

end SpectralDiagonalization

section RealRicciDiagonalization

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- If the synthetic metric agrees with the real inner product and Ricci is
symmetric as a bilinear form, then the Ricci endomorphism is a Mathlib
symmetric operator. -/
theorem ricciEndomorphism_isSymmetric_of_metric_eq_inner_and_Rc_symm
    (emb : DerivationEmbedding ℝ ℝ E) (conn : E -> E -> E)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : ℝ) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : ℝ) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace ℝ E) (met : MetricDuality ℝ E)
    (h_met_inner : forall X Y, met.g X Y = inner ℝ X Y)
    (h_Rc_symm : forall X Y,
      Rc emb conn ha hal hsl hl atr X Y =
        Rc emb conn ha hal hsl hl atr Y X) :
    (RicciEndomorphism emb conn ha hal hsl hl atr met).IsSymmetric := by
  intro X Y
  rw [← h_met_inner (RicciEndomorphism emb conn ha hal hsl hl atr met X) Y,
    ← h_met_inner X (RicciEndomorphism emb conn ha hal hsl hl atr met Y)]
  rw [met.g_symm X (RicciEndomorphism emb conn ha hal hsl hl atr met Y)]
  rw [RicciEndomorphism_spec emb conn ha hal hsl hl atr met X Y,
    RicciEndomorphism_spec emb conn ha hal hsl hl atr met Y X]
  exact h_Rc_symm X Y

/-- Real finite-dimensional Ricci diagonalization in dimension three.

This is the M1 bridge for the current synthetic P2 route: Mathlib's spectral
theorem supplies an orthonormal `Fin 3` eigenbasis for the Ricci endomorphism,
and the compatibility `met.g = inner ℝ` turns that basis into the synthetic
`IsMetricOrthonormalBasis3` package.

The complex spectral helper above is available, but the current synthetic
`MetricDuality` is bilinear rather than Hermitian, so the Ricci-flow-facing
diagonalization theorem is real-valued. -/
noncomputable def ricciDiagonalization3D_of_real_inner_product
    (emb : DerivationEmbedding ℝ ℝ E) (conn : E -> E -> E)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : ℝ) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : ℝ) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace ℝ E) (met : MetricDuality ℝ E)
    (hfin : Module.finrank ℝ E = 3)
    (h_met_inner : forall X Y, met.g X Y = inner ℝ X Y)
    (hRic_symm :
      (RicciEndomorphism emb conn ha hal hsl hl atr met).IsSymmetric) :
    RicciDiagonalization3D emb conn ha hal hsl hl atr met := by
  let T : E →ₗ[ℝ] E := RicciEndomorphism emb conn ha hal hsl hl atr met
  let b : OrthonormalBasis (Fin 3) ℝ E := hRic_symm.eigenvectorBasis hfin
  refine
    { basis := b.toBasis
      orthonormal := ?_
      lambda := hRic_symm.eigenvalues hfin
      ricci_diagonal := ?_ }
  · intro i j
    change met.g (b i) (b j) = if i = j then 1 else 0
    rw [h_met_inner]
    exact b.inner_eq_ite i j
  · intro i j
    change
      ricciForm_tensor emb conn ha hal hsl hl atr ![b i, b j] ![] =
        if i = j then hRic_symm.eigenvalues hfin i else 0
    have heig : T (b i) = (hRic_symm.eigenvalues hfin i : ℝ) • b i := by
      exact hRic_symm.apply_eigenvectorBasis hfin i
    rw [ricciForm_tensor_eval]
    rw [← RicciEndomorphism_spec emb conn ha hal hsl hl atr met (b i) (b j)]
    change met.g (T (b i)) (b j) = if i = j then hRic_symm.eigenvalues hfin i else 0
    rw [heig, met.g_smul_left]
    have hortho : met.g (b i) (b j) = if i = j then 1 else 0 := by
      rw [h_met_inner]
      exact b.inner_eq_ite i j
    rw [hortho]
    by_cases hij : i = j
    · simp only [hij, if_true, mul_one]
    · simp only [hij, if_false, mul_zero]

/-- Convenience constructor from Ricci symmetry as a bilinear form. -/
noncomputable def ricciDiagonalization3D_of_real_inner_product_and_Rc_symm
    (emb : DerivationEmbedding ℝ ℝ E) (conn : E -> E -> E)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : ℝ) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : ℝ) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace ℝ E) (met : MetricDuality ℝ E)
    (hfin : Module.finrank ℝ E = 3)
    (h_met_inner : forall X Y, met.g X Y = inner ℝ X Y)
    (h_Rc_symm : forall X Y,
      Rc emb conn ha hal hsl hl atr X Y =
        Rc emb conn ha hal hsl hl atr Y X) :
    RicciDiagonalization3D emb conn ha hal hsl hl atr met :=
  ricciDiagonalization3D_of_real_inner_product emb conn ha hal hsl hl atr met
    hfin h_met_inner
    (ricciEndomorphism_isSymmetric_of_metric_eq_inner_and_Rc_symm
      emb conn ha hal hsl hl atr met h_met_inner h_Rc_symm)

end RealRicciDiagonalization

section RealTraceBridge

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A real finite-dimensional standard trace gives the P2 orthonormal-basis
trace formula whenever the synthetic metric is the real inner product.

This is the local finite-dimensional model for the realization theorem:
`atr.tr` is identified with Mathlib's ordinary trace, and an orthonormal
`Fin 3` synthetic basis is turned into a Mathlib `OrthonormalBasis`. -/
theorem realTrace_hasOrthonormalBasisTraceFormula3
    (atr : AbstractTrace ℝ E) (met : MetricDuality ℝ E)
    (htr : forall L : E →ₗ[ℝ] E, atr.tr L = LinearMap.trace ℝ E L)
    (h_met_inner : forall X Y : E, met.g X Y = inner ℝ X Y) :
    HasOrthonormalBasisTraceFormula3 atr met where
  tr_eq_sum_orthonormal3 basis hortho L := by
    have hinner : forall i j : Fin 3,
        inner ℝ (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
      intro i j
      rw [← h_met_inner]
      exact hortho i j
    let hon : Orthonormal ℝ (fun i : Fin 3 => basis i) := by
      rw [orthonormal_iff_ite]
      exact hinner
    let ob : OrthonormalBasis (Fin 3) ℝ E :=
      OrthonormalBasis.mk (v := fun i => basis i) hon (by
        rw [basis.span_eq])
    have hob : forall i : Fin 3, ob i = basis i := by
      intro i
      exact congrFun (OrthonormalBasis.coe_mk hon (by rw [basis.span_eq])) i
    calc
      atr.tr L = LinearMap.trace ℝ E L := htr L
      _ = ∑ i : Fin 3, inner ℝ (ob i) (L (ob i)) :=
        LinearMap.trace_eq_sum_inner L ob
      _ = ∑ i : Fin 3, inner ℝ (basis i) (L (basis i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hob i]
      _ = ∑ i : Fin 3, met.g (basis i) (L (basis i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [h_met_inner]

variable [FiniteDimensional ℝ E]

/-- A real finite-dimensional standard trace is invariant under metric
adjoints when the synthetic metric is the real inner product. -/
theorem realTrace_hasMetricAdjointTraceInvariant
    (atr : AbstractTrace ℝ E) (met : MetricDuality ℝ E)
    (htr : forall L : E →ₗ[ℝ] E, atr.tr L = LinearMap.trace ℝ E L)
    (h_met_inner : forall X Y : E, met.g X Y = inner ℝ X Y) :
    HasMetricAdjointTraceInvariant atr met where
  trace_eq_of_metric_adjoint A B h_adj := by
    let b := stdOrthonormalBasis ℝ E
    calc
      atr.tr A = LinearMap.trace ℝ E A := htr A
      _ = ∑ i, inner ℝ (b i) (A (b i)) := LinearMap.trace_eq_sum_inner A b
      _ = ∑ i, inner ℝ (A (b i)) (b i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact real_inner_comm (A (b i)) (b i)
      _ = ∑ i, inner ℝ (b i) (B (b i)) := by
        apply Finset.sum_congr rfl
        intro i _
        have h := h_adj (b i) (b i)
        rw [h_met_inner, h_met_inner] at h
        exact h
      _ = LinearMap.trace ℝ E B := (LinearMap.trace_eq_sum_inner B b).symm
      _ = atr.tr B := (htr B).symm

end RealTraceBridge

/-- Sectional curvature numerator in a synthetic `Fin 3` frame.

The sign convention is the literal lowered curvature component
`Rm_lowered(e_i,e_j,e_i,e_j)`. If a later convention chooses
`Rm_lowered(e_i,e_j,e_j,e_i)`, add a separate accessor rather than silently
rewriting this one. -/
noncomputable def sectionalComponent3D
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) (basis : Module.Basis (Fin 3) R V)
    (i j : Fin 3) : R :=
  Rm_lowered emb conn met (basis i) (basis j) (basis i) (basis j)

/-- Sectional components are symmetric in the two selected frame vectors.

This is the precise curvature-symmetry input needed when solving the
three-dimensional Ricci trace equations: the trace equation for `lambda 1`
contains `K_10`, while the independent component package uses `K_01`. -/
theorem sectionalComponent3D_swap
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V) (h_mc : IsMetricCompatible emb conn met)
    (basis : Module.Basis (Fin 3) R V) (i j : Fin 3) :
    sectionalComponent3D emb conn met basis j i =
      sectionalComponent3D emb conn met basis i j := by
  unfold sectionalComponent3D
  rw [Rm_lowered_antisymm_first_pair emb conn hal met (basis j) (basis i)
    (basis j) (basis i)]
  rw [Rm_lowered_antisymm_second_pair emb conn met h_mc (basis i) (basis j)
    (basis j) (basis i)]
  simp only [neg_neg]

private theorem fin3_sum_filter_ne_zero (F : Fin 3 -> R) :
    Finset.sum (Finset.univ.filter (fun j : Fin 3 => j ≠ 0)) F =
      F 1 + F 2 := by
  rw [show Finset.univ.filter (fun j : Fin 3 => j ≠ 0) =
      ({1, 2} : Finset (Fin 3)) from by
    ext j
    fin_cases j <;> decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, Fin.reduceEq, not_false_eq_true,
    Finset.sum_singleton]

private theorem fin3_sum_filter_ne_one (F : Fin 3 -> R) :
    Finset.sum (Finset.univ.filter (fun j : Fin 3 => j ≠ 1)) F =
      F 0 + F 2 := by
  rw [show Finset.univ.filter (fun j : Fin 3 => j ≠ 1) =
      ({0, 2} : Finset (Fin 3)) from by
    ext j
    fin_cases j <;> decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, Fin.reduceEq, not_false_eq_true,
    Finset.sum_singleton]

private theorem fin3_sum_filter_ne_two (F : Fin 3 -> R) :
    Finset.sum (Finset.univ.filter (fun j : Fin 3 => j ≠ 2)) F =
      F 0 + F 1 := by
  rw [show Finset.univ.filter (fun j : Fin 3 => j ≠ 2) =
      ({0, 1} : Finset (Fin 3)) from by
    ext j
    fin_cases j <;> decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, Fin.reduceEq, not_false_eq_true,
    Finset.sum_singleton]

/-- Ricci evaluated in an orthonormal `Fin 3` basis as the trace sum of the
curvature endomorphism.

This is the raw component bridge supplied by `HasOrthonormalBasisTraceFormula3`;
the sectional-component projection is handled below. -/
theorem ricciForm_tensor_eq_sum_Rm_lowered_of_orthonormal_trace3
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (basis : Module.Basis (Fin 3) R V) (hortho : IsMetricOrthonormalBasis3 met basis)
    (X Z : V) :
    ricciForm_tensor emb conn ha hal hsl hl atr ![X, Z] ![] =
      ∑ j : Fin 3, Rm_lowered emb conn met X (basis j) Z (basis j) := by
  rw [ricciForm_tensor_eval]
  unfold Rc
  rw [HasOrthonormalBasisTraceFormula3.tr_eq_sum_orthonormal3 basis hortho]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp only [RcEndo, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Rm_lowered, met.g_symm]

/-- A repeated first curvature slot gives zero when multiplication by `2` is
cancellative. -/
theorem Rm_lowered_self_first_pair_eq_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (met : MetricDuality R V) (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (X Z W : V) :
    Rm_lowered emb conn met X X Z W = 0 := by
  have hanti := Rm_lowered_antisymm_first_pair emb conn hal met X X Z W
  apply h2
  linear_combination hanti

/-- A repeated second curvature pair gives zero when multiplication by `2` is
cancellative. -/
theorem Rm_lowered_self_second_pair_eq_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0) (X Y Z : V) :
    Rm_lowered emb conn met X Y Z Z = 0 := by
  have hanti := Rm_lowered_antisymm_second_pair emb conn met h_mc X Y Z Z
  apply h2
  linear_combination hanti

/-- Each diagonal Ricci trace term is the selected sectional component
`K_ij = Rm(e_i,e_j,e_i,e_j)` under the convention
`RcEndo X Z = (Y ↦ Rm X Y Z)`. -/
theorem Rm_lowered_trace_term_eq_sectionalComponent3D
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (met : MetricDuality R V) (basis : Module.Basis (Fin 3) R V) (i j : Fin 3) :
    Rm_lowered emb conn met (basis i) (basis j) (basis i) (basis j) =
      sectionalComponent3D emb conn met basis i j := by
  rfl

/-- The trace formula gives the diagonal Ricci components as the selected
sectional sum with the convention `RcEndo X Z = (Y ↦ Rm X Y Z)`. -/
theorem ricciForm_tensor_eq_sectional_sum_of_orthonormal_trace3
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (basis : Module.Basis (Fin 3) R V) (hortho : IsMetricOrthonormalBasis3 met basis)
    (h2 : forall a : R, 2 * a = 0 -> a = 0) (i : Fin 3) :
    ricciForm_tensor emb conn ha hal hsl hl atr ![basis i, basis i] ![] =
      Finset.sum (Finset.univ.filter (fun j : Fin 3 => j ≠ i))
        (fun j => sectionalComponent3D emb conn met basis i j) := by
  rw [ricciForm_tensor_eq_sum_Rm_lowered_of_orthonormal_trace3 emb conn ha hal hsl hl
    atr met basis hortho]
  fin_cases i
  · change (∑ j : Fin 3, Rm_lowered emb conn met (basis 0) (basis j) (basis 0)
        (basis j)) =
      Finset.sum (Finset.univ.filter (fun j : Fin 3 => j ≠ 0))
        (fun j => sectionalComponent3D emb conn met basis 0 j)
    rw [Fin.sum_univ_three, fin3_sum_filter_ne_zero]
    rw [Rm_lowered_self_first_pair_eq_zero emb conn hal met h2 (basis 0) (basis 0)
      (basis 0)]
    rw [Rm_lowered_trace_term_eq_sectionalComponent3D emb conn met basis
      (0 : Fin 3) 1]
    rw [Rm_lowered_trace_term_eq_sectionalComponent3D emb conn met basis
      (0 : Fin 3) 2]
    ring
  · change (∑ j : Fin 3, Rm_lowered emb conn met (basis 1) (basis j) (basis 1)
        (basis j)) =
      Finset.sum (Finset.univ.filter (fun j : Fin 3 => j ≠ 1))
        (fun j => sectionalComponent3D emb conn met basis 1 j)
    rw [Fin.sum_univ_three, fin3_sum_filter_ne_one]
    rw [Rm_lowered_trace_term_eq_sectionalComponent3D emb conn met basis
      (1 : Fin 3) 0]
    rw [Rm_lowered_self_first_pair_eq_zero emb conn hal met h2 (basis 1) (basis 1)
      (basis 1)]
    rw [Rm_lowered_trace_term_eq_sectionalComponent3D emb conn met basis
      (1 : Fin 3) 2]
    ring
  · change (∑ j : Fin 3, Rm_lowered emb conn met (basis 2) (basis j) (basis 2)
        (basis j)) =
      Finset.sum (Finset.univ.filter (fun j : Fin 3 => j ≠ 2))
        (fun j => sectionalComponent3D emb conn met basis 2 j)
    rw [Fin.sum_univ_three, fin3_sum_filter_ne_two]
    rw [Rm_lowered_trace_term_eq_sectionalComponent3D emb conn met basis
      (2 : Fin 3) 0]
    rw [Rm_lowered_trace_term_eq_sectionalComponent3D emb conn met basis
      (2 : Fin 3) 1]
    rw [Rm_lowered_self_first_pair_eq_zero emb conn hal met h2 (basis 2) (basis 2)
      (basis 2)]
    ring

/-- Scalar curvature is the sum of the Ricci eigenvalues in an orthonormal
Ricci eigenbasis, provided the abstract trace has the corresponding finite
orthonormal-basis formula. -/
theorem scalarCurvature_eq_sum_lambda_of_orthonormal_trace3
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met) :
    ScalarCurvature emb conn ha hal hsl hl atr met =
      ∑ i : Fin 3, diag.lambda i := by
  unfold ScalarCurvature
  rw [HasOrthonormalBasisTraceFormula3.tr_eq_sum_orthonormal3 diag.basis diag.orthonormal]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [met.g_symm (diag.basis i)
    ((RicciEndomorphism emb conn ha hal hsl hl atr met) (diag.basis i))]
  rw [RicciEndomorphism_spec emb conn ha hal hsl hl atr met (diag.basis i) (diag.basis i)]
  rw [← ricciForm_tensor_eval emb conn ha hal hsl hl atr (diag.basis i) (diag.basis i)]
  rw [diag.ricci_diagonal i i]
  simp only [if_true]

/-- Ricci trace and solved sectional-component identities in a Ricci
eigenbasis.

This names the M2 bridge for P2. The first field is the trace expansion
`Ric(e_i,e_i) = sum_{j != i} K_ij` in the selected convention. The remaining
fields are the dimension-three linear solve for the three independent
sectional components. -/
structure RicciSectionalTraceFormula3D
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R) where
  h_half : IsHalfCoefficient half
  scalar_eq_sum_lambda :
    ScalarCurvature emb conn ha hal hsl hl atr met =
      ∑ i : Fin 3, diag.lambda i
  ricci_eq_sectional_sum :
    forall i : Fin 3,
      ricciForm_tensor emb conn ha hal hsl hl atr ![diag.basis i, diag.basis i] ![] =
        Finset.sum (Finset.univ.filter (fun j : Fin 3 => j ≠ i))
          (fun j => sectionalComponent3D emb conn met diag.basis i j)
  sectional_01 :
    sectionalComponent3D emb conn met diag.basis 0 1 =
      half * (diag.lambda 0 + diag.lambda 1 - diag.lambda 2)
  sectional_02 :
    sectionalComponent3D emb conn met diag.basis 0 2 =
      half * (diag.lambda 0 + diag.lambda 2 - diag.lambda 1)
  sectional_12 :
    sectionalComponent3D emb conn met diag.basis 1 2 =
      half * (diag.lambda 1 + diag.lambda 2 - diag.lambda 0)

/-- Build the sectional formula package from the diagonal Ricci trace
equations.

The only geometry used after the trace equations is `K_ij = K_ji`, supplied by
`sectionalComponent3D_swap`. This is the part of P2 where the sectional
curvatures are solved from
`lambda_0 = K_01 + K_02`, `lambda_1 = K_01 + K_12`,
`lambda_2 = K_02 + K_12`. -/
noncomputable def ricciSectionalTraceFormula3D_of_trace_equations
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (h_mc : IsMetricCompatible emb conn met)
    (half : R) (h_half : IsHalfCoefficient half)
    (h_scalar :
      ScalarCurvature emb conn ha hal hsl hl atr met =
        ∑ i : Fin 3, diag.lambda i)
    (h_trace :
      forall i : Fin 3,
        ricciForm_tensor emb conn ha hal hsl hl atr ![diag.basis i, diag.basis i] ![] =
          Finset.sum (Finset.univ.filter (fun j : Fin 3 => j ≠ i))
            (fun j => sectionalComponent3D emb conn met diag.basis i j)) :
    RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half where
  h_half := h_half
  scalar_eq_sum_lambda := h_scalar
  ricci_eq_sectional_sum := h_trace
  sectional_01 := by
    have h0 := h_trace (0 : Fin 3)
    have h1 := h_trace (1 : Fin 3)
    have h2 := h_trace (2 : Fin 3)
    have hRc00 := diag.ricci_diagonal (0 : Fin 3) (0 : Fin 3)
    have hRc11 := diag.ricci_diagonal (1 : Fin 3) (1 : Fin 3)
    have hRc22 := diag.ricci_diagonal (2 : Fin 3) (2 : Fin 3)
    simp only [if_true] at hRc00 hRc11 hRc22
    rw [hRc00, fin3_sum_filter_ne_zero] at h0
    rw [hRc11, fin3_sum_filter_ne_one] at h1
    rw [hRc22, fin3_sum_filter_ne_two] at h2
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (0 : Fin 3) 1] at h1
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (0 : Fin 3) 2] at h2
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (1 : Fin 3) 2] at h2
    have hsum :
        diag.lambda 0 + diag.lambda 1 - diag.lambda 2 =
          2 * sectionalComponent3D emb conn met diag.basis 0 1 := by
      rw [h0, h1, h2]
      ring
    calc
      sectionalComponent3D emb conn met diag.basis 0 1 =
          (2 * half) * sectionalComponent3D emb conn met diag.basis 0 1 := by
            rw [h_half]
            ring
      _ = half * (2 * sectionalComponent3D emb conn met diag.basis 0 1) := by
            ring
      _ = half * (diag.lambda 0 + diag.lambda 1 - diag.lambda 2) := by
            rw [hsum]
  sectional_02 := by
    have h0 := h_trace (0 : Fin 3)
    have h1 := h_trace (1 : Fin 3)
    have h2 := h_trace (2 : Fin 3)
    have hRc00 := diag.ricci_diagonal (0 : Fin 3) (0 : Fin 3)
    have hRc11 := diag.ricci_diagonal (1 : Fin 3) (1 : Fin 3)
    have hRc22 := diag.ricci_diagonal (2 : Fin 3) (2 : Fin 3)
    simp only [if_true] at hRc00 hRc11 hRc22
    rw [hRc00, fin3_sum_filter_ne_zero] at h0
    rw [hRc11, fin3_sum_filter_ne_one] at h1
    rw [hRc22, fin3_sum_filter_ne_two] at h2
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (0 : Fin 3) 1] at h1
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (0 : Fin 3) 2] at h2
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (1 : Fin 3) 2] at h2
    have hsum :
        diag.lambda 0 + diag.lambda 2 - diag.lambda 1 =
          2 * sectionalComponent3D emb conn met diag.basis 0 2 := by
      rw [h0, h1, h2]
      ring
    calc
      sectionalComponent3D emb conn met diag.basis 0 2 =
          (2 * half) * sectionalComponent3D emb conn met diag.basis 0 2 := by
            rw [h_half]
            ring
      _ = half * (2 * sectionalComponent3D emb conn met diag.basis 0 2) := by
            ring
      _ = half * (diag.lambda 0 + diag.lambda 2 - diag.lambda 1) := by
            rw [hsum]
  sectional_12 := by
    have h0 := h_trace (0 : Fin 3)
    have h1 := h_trace (1 : Fin 3)
    have h2 := h_trace (2 : Fin 3)
    have hRc00 := diag.ricci_diagonal (0 : Fin 3) (0 : Fin 3)
    have hRc11 := diag.ricci_diagonal (1 : Fin 3) (1 : Fin 3)
    have hRc22 := diag.ricci_diagonal (2 : Fin 3) (2 : Fin 3)
    simp only [if_true] at hRc00 hRc11 hRc22
    rw [hRc00, fin3_sum_filter_ne_zero] at h0
    rw [hRc11, fin3_sum_filter_ne_one] at h1
    rw [hRc22, fin3_sum_filter_ne_two] at h2
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (0 : Fin 3) 1] at h1
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (0 : Fin 3) 2] at h2
    rw [sectionalComponent3D_swap emb conn hal met h_mc diag.basis (1 : Fin 3) 2] at h2
    have hsum :
        diag.lambda 1 + diag.lambda 2 - diag.lambda 0 =
          2 * sectionalComponent3D emb conn met diag.basis 1 2 := by
      rw [h0, h1, h2]
      ring
    calc
      sectionalComponent3D emb conn met diag.basis 1 2 =
          (2 * half) * sectionalComponent3D emb conn met diag.basis 1 2 := by
            rw [h_half]
            ring
      _ = half * (2 * sectionalComponent3D emb conn met diag.basis 1 2) := by
            ring
      _ = half * (diag.lambda 1 + diag.lambda 2 - diag.lambda 0) := by
            rw [hsum]

/-- Mixed curvature components in a Ricci eigenbasis.

This is the M3 bridge for the finite-frame P2 route. The three fields are the
off-diagonal upper-triangular residual components that remain after M2 has
identified the sectional components. They should be derived from the
off-diagonal Ricci trace formula in an orthonormal basis plus the curvature
symmetries and first Bianchi sign convention. -/
structure RicciMixedCurvatureFormula3D
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met) where
  mixed_01_02_zero :
    Rm_lowered emb conn met (diag.basis 0) (diag.basis 1) (diag.basis 0)
      (diag.basis 2) = 0
  mixed_01_12_zero :
    Rm_lowered emb conn met (diag.basis 0) (diag.basis 1) (diag.basis 1)
      (diag.basis 2) = 0
  mixed_02_12_zero :
    Rm_lowered emb conn met (diag.basis 0) (diag.basis 2) (diag.basis 1)
      (diag.basis 2) = 0

/-- Off-diagonal Ricci trace equations in a Ricci eigenbasis.

These are the precise trace identities behind the mixed-curvature vanishings.
The middle field records the sign convention: in the current lowered-curvature
ordering, `Ric(e_0,e_2)` traces to `- Rm(e_0,e_1,e_1,e_2)`. -/
structure RicciOffDiagonalTraceFormula3D
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met) where
  ricci_12_eq_mixed_01_02 :
    ricciForm_tensor emb conn ha hal hsl hl atr ![diag.basis 1, diag.basis 2] ![] =
      Rm_lowered emb conn met (diag.basis 0) (diag.basis 1) (diag.basis 0)
        (diag.basis 2)
  ricci_02_eq_neg_mixed_01_12 :
    ricciForm_tensor emb conn ha hal hsl hl atr ![diag.basis 0, diag.basis 2] ![] =
      -Rm_lowered emb conn met (diag.basis 0) (diag.basis 1) (diag.basis 1)
        (diag.basis 2)
  ricci_01_eq_mixed_02_12 :
    ricciForm_tensor emb conn ha hal hsl hl atr ![diag.basis 0, diag.basis 1] ![] =
      Rm_lowered emb conn met (diag.basis 0) (diag.basis 2) (diag.basis 1)
        (diag.basis 2)

/-- Build the off-diagonal Ricci trace equations from the orthonormal trace
formula.

For example,
`Ric(e_1,e_2) = sum_j Rm(e_1,e_j,e_2,e_j)`. In a three-dimensional
orthonormal frame the `j = 1` and `j = 2` terms vanish by skew-symmetry in the
two curvature pairs, while the `j = 0` term becomes
`Rm(e_0,e_1,e_0,e_2)` after two antisymmetry rewrites. The other two
off-diagonal equations are the same calculation with the relevant sign. -/
noncomputable def ricciOffDiagonalTraceFormula3D_of_orthonormal_trace3
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met) :
    RicciOffDiagonalTraceFormula3D emb conn ha hal hsl hl atr met diag where
  ricci_12_eq_mixed_01_02 := by
    have htrace :=
      ricciForm_tensor_eq_sum_Rm_lowered_of_orthonormal_trace3
        emb conn ha hal hsl hl atr met diag.basis diag.orthonormal
          (diag.basis 1) (diag.basis 2)
    rw [htrace, Fin.sum_univ_three]
    rw [Rm_lowered_antisymm_first_pair emb conn hal met (diag.basis 1)
      (diag.basis 0) (diag.basis 2) (diag.basis 0)]
    rw [Rm_lowered_antisymm_second_pair emb conn met h_mc (diag.basis 0)
      (diag.basis 1) (diag.basis 2) (diag.basis 0)]
    rw [Rm_lowered_self_first_pair_eq_zero emb conn hal met h2 (diag.basis 1)
      (diag.basis 2) (diag.basis 1)]
    rw [Rm_lowered_self_second_pair_eq_zero emb conn met h_mc h2 (diag.basis 1)
      (diag.basis 2) (diag.basis 2)]
    ring
  ricci_02_eq_neg_mixed_01_12 := by
    have htrace :=
      ricciForm_tensor_eq_sum_Rm_lowered_of_orthonormal_trace3
        emb conn ha hal hsl hl atr met diag.basis diag.orthonormal
          (diag.basis 0) (diag.basis 2)
    rw [htrace, Fin.sum_univ_three]
    rw [Rm_lowered_self_first_pair_eq_zero emb conn hal met h2 (diag.basis 0)
      (diag.basis 2) (diag.basis 0)]
    rw [Rm_lowered_antisymm_second_pair emb conn met h_mc (diag.basis 0)
      (diag.basis 1) (diag.basis 2) (diag.basis 1)]
    rw [Rm_lowered_self_second_pair_eq_zero emb conn met h_mc h2 (diag.basis 0)
      (diag.basis 2) (diag.basis 2)]
    ring
  ricci_01_eq_mixed_02_12 := by
    have htrace :=
      ricciForm_tensor_eq_sum_Rm_lowered_of_orthonormal_trace3
        emb conn ha hal hsl hl atr met diag.basis diag.orthonormal
          (diag.basis 0) (diag.basis 1)
    rw [htrace, Fin.sum_univ_three]
    rw [Rm_lowered_self_first_pair_eq_zero emb conn hal met h2 (diag.basis 0)
      (diag.basis 1) (diag.basis 0)]
    rw [Rm_lowered_self_second_pair_eq_zero emb conn met h_mc h2 (diag.basis 0)
      (diag.basis 1) (diag.basis 1)]
    ring

/-!
The following constructor is the algebraic endpoint of the mixed-curvature
trace calculation. A realization proof should build `RicciOffDiagonalTraceFormula3D`
from the orthonormal trace formula plus curvature antisymmetries/first Bianchi;
this constructor then uses only Ricci diagonalization.
-/
noncomputable def ricciMixedCurvatureFormula3D_of_offDiagonal_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (off : RicciOffDiagonalTraceFormula3D emb conn ha hal hsl hl atr met diag) :
    RicciMixedCurvatureFormula3D emb conn ha hal hsl hl atr met diag where
  mixed_01_02_zero := by
    have hRc12 := diag.ricci_diagonal (1 : Fin 3) (2 : Fin 3)
    simp only [Fin.reduceEq, if_false] at hRc12
    rw [← off.ricci_12_eq_mixed_01_02]
    exact hRc12
  mixed_01_12_zero := by
    have hRc02 := diag.ricci_diagonal (0 : Fin 3) (2 : Fin 3)
    simp only [Fin.reduceEq, if_false] at hRc02
    have hneg :
        -Rm_lowered emb conn met (diag.basis 0) (diag.basis 1) (diag.basis 1)
          (diag.basis 2) = 0 := by
      rw [← off.ricci_02_eq_neg_mixed_01_12]
      exact hRc02
    exact neg_eq_zero.mp hneg
  mixed_02_12_zero := by
    have hRc01 := diag.ricci_diagonal (0 : Fin 3) (1 : Fin 3)
    simp only [Fin.reduceEq, if_false] at hRc01
    rw [← off.ricci_01_eq_mixed_02_12]
    exact hRc01

theorem riemannFromRicci3DResidualTensor_01_01_of_sectional_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R) (sec : RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half) :
    riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half sec.h_half
        ![diag.basis 0, diag.basis 1, diag.basis 0, diag.basis 1] ![] = 0 := by
  have hRc00 := diag.ricci_diagonal 0 0
  have hRc11 := diag.ricci_diagonal 1 1
  have hRc01 := diag.ricci_diagonal 0 1
  have hRc10 := diag.ricci_diagonal 1 0
  have hg00 := diag.orthonormal 0 0
  have hg11 := diag.orthonormal 1 1
  have hg01 := diag.orthonormal 0 1
  have hg10 := diag.orthonormal 1 0
  simp only [if_true, Fin.reduceEq, if_false] at hRc00 hRc11 hRc01 hRc10 hg00 hg11 hg01 hg10
  have hsec :
      Rm_lowered emb conn met (diag.basis 0) (diag.basis 1) (diag.basis 0)
          (diag.basis 1) =
        half * (diag.lambda 0 + diag.lambda 1 - diag.lambda 2) := by
    simpa [sectionalComponent3D] using sec.sectional_01
  rw [riemannFromRicci3DResidualTensor_eval, riemannFromRicci3DResidual, hsec]
  unfold riemannFromRicci3DRHS
  rw [hRc00, hRc11, hRc01, hRc10, hg11, hg00, hg10, hg01, sec.scalar_eq_sum_lambda]
  rw [Fin.sum_univ_three]
  have hhalf0 := sec.h_half
  unfold IsHalfCoefficient at hhalf0
  have hhalf : half * 2 = 1 := by
    rw [mul_comm]
    exact hhalf0
  linear_combination (diag.lambda 0 + diag.lambda 1) * hhalf

theorem riemannFromRicci3DResidualTensor_02_02_of_sectional_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R) (sec : RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half) :
    riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half sec.h_half
        ![diag.basis 0, diag.basis 2, diag.basis 0, diag.basis 2] ![] = 0 := by
  have hRc00 := diag.ricci_diagonal 0 0
  have hRc22 := diag.ricci_diagonal 2 2
  have hRc02 := diag.ricci_diagonal 0 2
  have hRc20 := diag.ricci_diagonal 2 0
  have hg00 := diag.orthonormal 0 0
  have hg22 := diag.orthonormal 2 2
  have hg02 := diag.orthonormal 0 2
  have hg20 := diag.orthonormal 2 0
  simp only [if_true, Fin.reduceEq, if_false] at hRc00 hRc22 hRc02 hRc20 hg00 hg22 hg02 hg20
  have hsec :
      Rm_lowered emb conn met (diag.basis 0) (diag.basis 2) (diag.basis 0)
          (diag.basis 2) =
        half * (diag.lambda 0 + diag.lambda 2 - diag.lambda 1) := by
    simpa [sectionalComponent3D] using sec.sectional_02
  rw [riemannFromRicci3DResidualTensor_eval, riemannFromRicci3DResidual, hsec]
  unfold riemannFromRicci3DRHS
  rw [hRc00, hRc22, hRc02, hRc20, hg22, hg00, hg20, hg02, sec.scalar_eq_sum_lambda]
  rw [Fin.sum_univ_three]
  have hhalf0 := sec.h_half
  unfold IsHalfCoefficient at hhalf0
  have hhalf : half * 2 = 1 := by
    rw [mul_comm]
    exact hhalf0
  linear_combination (diag.lambda 0 + diag.lambda 2) * hhalf

theorem riemannFromRicci3DResidualTensor_12_12_of_sectional_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R) (sec : RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half) :
    riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half sec.h_half
        ![diag.basis 1, diag.basis 2, diag.basis 1, diag.basis 2] ![] = 0 := by
  have hRc11 := diag.ricci_diagonal 1 1
  have hRc22 := diag.ricci_diagonal 2 2
  have hRc12 := diag.ricci_diagonal 1 2
  have hRc21 := diag.ricci_diagonal 2 1
  have hg11 := diag.orthonormal 1 1
  have hg22 := diag.orthonormal 2 2
  have hg12 := diag.orthonormal 1 2
  have hg21 := diag.orthonormal 2 1
  simp only [if_true, Fin.reduceEq, if_false] at hRc11 hRc22 hRc12 hRc21 hg11 hg22 hg12 hg21
  have hsec :
      Rm_lowered emb conn met (diag.basis 1) (diag.basis 2) (diag.basis 1)
          (diag.basis 2) =
        half * (diag.lambda 1 + diag.lambda 2 - diag.lambda 0) := by
    simpa [sectionalComponent3D] using sec.sectional_12
  rw [riemannFromRicci3DResidualTensor_eval, riemannFromRicci3DResidual, hsec]
  unfold riemannFromRicci3DRHS
  rw [hRc11, hRc22, hRc12, hRc21, hg22, hg11, hg21, hg12, sec.scalar_eq_sum_lambda]
  rw [Fin.sum_univ_three]
  have hhalf0 := sec.h_half
  unfold IsHalfCoefficient at hhalf0
  have hhalf : half * 2 = 1 := by
    rw [mul_comm]
    exact hhalf0
  linear_combination (diag.lambda 1 + diag.lambda 2) * hhalf

theorem isHalfCoefficient_eq_of_two_cancel
    (half half' : R)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h_half : IsHalfCoefficient half) (h_half' : IsHalfCoefficient half') :
    half' = half := by
  have h0 := h_half
  have h1 := h_half'
  unfold IsHalfCoefficient at h0 h1
  have hdiff : (2 : R) * (half' - half) = 0 := by
    linear_combination h1 - h0
  exact sub_eq_zero.mp (h2 (half' - half) hdiff)

theorem riemannFromRicci3DResidualTensor_01_02_of_mixed_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (mixed : RicciMixedCurvatureFormula3D emb conn ha hal hsl hl atr met diag)
    (half : R) (h_half : IsHalfCoefficient half) :
    riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half h_half
        ![diag.basis 0, diag.basis 1, diag.basis 0, diag.basis 2] ![] = 0 := by
  have hRc00 := diag.ricci_diagonal 0 0
  have hRc12 := diag.ricci_diagonal 1 2
  have hRc02 := diag.ricci_diagonal 0 2
  have hRc10 := diag.ricci_diagonal 1 0
  have hg00 := diag.orthonormal 0 0
  have hg12 := diag.orthonormal 1 2
  have hg10 := diag.orthonormal 1 0
  have hg02 := diag.orthonormal 0 2
  simp only [if_true, Fin.reduceEq, if_false] at hRc00 hRc12 hRc02 hRc10 hg00 hg12 hg10 hg02
  rw [riemannFromRicci3DResidualTensor_eval, riemannFromRicci3DResidual,
    mixed.mixed_01_02_zero]
  unfold riemannFromRicci3DRHS
  rw [hRc00, hRc12, hRc02, hRc10, hg12, hg00, hg10, hg02]
  ring

theorem riemannFromRicci3DResidualTensor_01_12_of_mixed_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (mixed : RicciMixedCurvatureFormula3D emb conn ha hal hsl hl atr met diag)
    (half : R) (h_half : IsHalfCoefficient half) :
    riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half h_half
        ![diag.basis 0, diag.basis 1, diag.basis 1, diag.basis 2] ![] = 0 := by
  have hRc01 := diag.ricci_diagonal 0 1
  have hRc12 := diag.ricci_diagonal 1 2
  have hRc02 := diag.ricci_diagonal 0 2
  have hRc11 := diag.ricci_diagonal 1 1
  have hg12 := diag.orthonormal 1 2
  have hg01 := diag.orthonormal 0 1
  have hg11 := diag.orthonormal 1 1
  have hg02 := diag.orthonormal 0 2
  simp only [if_true, Fin.reduceEq, if_false] at hRc01 hRc12 hRc02 hRc11 hg12 hg01 hg11 hg02
  rw [riemannFromRicci3DResidualTensor_eval, riemannFromRicci3DResidual,
    mixed.mixed_01_12_zero]
  unfold riemannFromRicci3DRHS
  rw [hRc01, hRc12, hRc02, hRc11, hg12, hg01, hg11, hg02]
  ring

theorem riemannFromRicci3DResidualTensor_02_12_of_mixed_trace
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (mixed : RicciMixedCurvatureFormula3D emb conn ha hal hsl hl atr met diag)
    (half : R) (h_half : IsHalfCoefficient half) :
    riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half h_half
        ![diag.basis 0, diag.basis 2, diag.basis 1, diag.basis 2] ![] = 0 := by
  have hRc01 := diag.ricci_diagonal 0 1
  have hRc22 := diag.ricci_diagonal 2 2
  have hRc02 := diag.ricci_diagonal 0 2
  have hRc21 := diag.ricci_diagonal 2 1
  have hg22 := diag.orthonormal 2 2
  have hg01 := diag.orthonormal 0 1
  have hg21 := diag.orthonormal 2 1
  have hg02 := diag.orthonormal 0 2
  simp only [if_true, Fin.reduceEq, if_false] at hRc01 hRc22 hRc02 hRc21 hg22 hg01 hg21 hg02
  rw [riemannFromRicci3DResidualTensor_eval, riemannFromRicci3DResidual,
    mixed.mixed_02_12_zero]
  unfold riemannFromRicci3DRHS
  rw [hRc01, hRc22, hRc02, hRc21, hg22, hg01, hg21, hg02]
  ring

/-- Constructor for the named P2 calculus class from the residual equation. -/
theorem hasRiemannFromRicci3DCalculus_of_residual_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_residual :
      IsDimensionThree atr ->
        forall (half : R) (h_half : IsHalfCoefficient half) (X Y Z W : V),
          riemannFromRicci3DResidual emb conn ha hal hsl hl atr met
            half h_half X Y Z W = 0) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met :=
  ⟨h_residual⟩

/-- Constructor for the named P2 calculus class from tensor-level residual
vanishing. -/
theorem hasRiemannFromRicci3DCalculus_of_residual_tensor_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_zero :
      IsDimensionThree atr ->
        forall (half : R) (h_half : IsHalfCoefficient half),
          riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
            half h_half = 0) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met := by
  refine hasRiemannFromRicci3DCalculus_of_residual_zero emb conn ha hal hsl hl atr met ?_
  intro h_dim half h_half X Y Z W
  have h := congr_arg (fun T : TensorData R V 0 4 => T ![X, Y, Z, W] ![])
    (h_zero h_dim half h_half)
  simpa [riemannFromRicci3DResidualTensor_eval] using h

/-- A `(0,4)` tensor is zero if all of its components in a basis vanish. -/
theorem tensor04_eq_zero_of_basis_components
    {ι : Type*} [Finite ι] (basis : Module.Basis ι R V) (T : TensorData R V 0 4)
    (h_components : forall idx : Fin 4 -> ι, T (fun i => basis (idx i)) ![] = 0) :
    T = 0 := by
  apply Module.Basis.ext_multilinear (fun _ : Fin 4 => basis)
  intro idx
  ext αs
  have hα : αs = ![] := by ext i; exact i.elim0
  subst hα
  simpa using h_components idx

/-- A skew-in-each-curvature-pair `(0,4)` tensor is zero if all components with
distinct entries in both slot-pairs vanish. This is a smaller component target
for algebraic-curvature residuals than checking every basis component. -/
theorem tensor04_eq_zero_of_basis_distinct_pair_components
    {ι : Type*} [Finite ι] (basis : Module.Basis ι R V)
    (T : TensorData R V 0 4)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h_anti_first : forall X Y Z W : V,
      T ![Y, X, Z, W] ![] = -T ![X, Y, Z, W] ![])
    (h_anti_last : forall X Y Z W : V,
      T ![X, Y, W, Z] ![] = -T ![X, Y, Z, W] ![])
    (h_components : forall i j k l : ι, i ≠ j -> k ≠ l ->
      T ![basis i, basis j, basis k, basis l] ![] = 0) :
    T = 0 := by
  classical
  refine tensor04_eq_zero_of_basis_components basis T ?_
  intro idx
  have hvec :
      (fun i : Fin 4 => basis (idx i)) =
        ![basis (idx 0), basis (idx 1), basis (idx 2), basis (idx 3)] := by
    ext i
    fin_cases i <;> rfl
  by_cases hij : idx 0 = idx 1
  · have hsame :
        T ![basis (idx 0), basis (idx 1), basis (idx 2), basis (idx 3)] ![] =
          -T ![basis (idx 0), basis (idx 1), basis (idx 2), basis (idx 3)] ![] := by
      simpa [hij] using
        h_anti_first (basis (idx 0)) (basis (idx 1)) (basis (idx 2)) (basis (idx 3))
    have hzero :
        T ![basis (idx 0), basis (idx 1), basis (idx 2), basis (idx 3)] ![] = 0 := by
      apply h2
      linear_combination hsame
    rw [hvec]
    exact hzero
  · by_cases hkl : idx 2 = idx 3
    · have hsame :
          T ![basis (idx 0), basis (idx 1), basis (idx 2), basis (idx 3)] ![] =
            -T ![basis (idx 0), basis (idx 1), basis (idx 2), basis (idx 3)] ![] := by
        simpa [hkl] using
          h_anti_last (basis (idx 0)) (basis (idx 1)) (basis (idx 2)) (basis (idx 3))
      have hzero :
          T ![basis (idx 0), basis (idx 1), basis (idx 2), basis (idx 3)] ![] = 0 := by
        apply h2
        linear_combination hsame
      rw [hvec]
      exact hzero
    · rw [hvec]
      exact h_components (idx 0) (idx 1) (idx 2) (idx 3) hij hkl

/-- A skew-in-each-curvature-pair `(0,4)` tensor is zero if all components with
strictly ordered entries in both slot-pairs vanish. For a three-element ordered
basis, this leaves the nine pair-pair components. -/
theorem tensor04_eq_zero_of_basis_ordered_pair_components
    {ι : Type*} [Finite ι] [LinearOrder ι] (basis : Module.Basis ι R V)
    (T : TensorData R V 0 4)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h_anti_first : forall X Y Z W : V,
      T ![Y, X, Z, W] ![] = -T ![X, Y, Z, W] ![])
    (h_anti_last : forall X Y Z W : V,
      T ![X, Y, W, Z] ![] = -T ![X, Y, Z, W] ![])
    (h_components : forall i j k l : ι, i < j -> k < l ->
      T ![basis i, basis j, basis k, basis l] ![] = 0) :
    T = 0 := by
  refine tensor04_eq_zero_of_basis_distinct_pair_components basis T h2
    h_anti_first h_anti_last ?_
  intro i j k l hij hkl
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · rcases lt_or_gt_of_ne hkl with hkl_lt | hlk_lt
    · exact h_components i j k l hij_lt hkl_lt
    · have hlast := h_anti_last (basis i) (basis j) (basis l) (basis k)
      rw [h_components i j l k hij_lt hlk_lt, neg_zero] at hlast
      exact hlast
  · rcases lt_or_gt_of_ne hkl with hkl_lt | hlk_lt
    · have hfirst := h_anti_first (basis j) (basis i) (basis k) (basis l)
      rw [h_components j i k l hji_lt hkl_lt, neg_zero] at hfirst
      exact hfirst
    · calc
        T ![basis i, basis j, basis k, basis l] ![] =
            -T ![basis j, basis i, basis k, basis l] ![] := by
          exact h_anti_first (basis j) (basis i) (basis k) (basis l)
        _ = -(-T ![basis j, basis i, basis l, basis k] ![]) := by
          rw [h_anti_last (basis j) (basis i) (basis l) (basis k)]
        _ = 0 := by
          rw [h_components j i l k hji_lt hlk_lt]
          ring

/-- A skew pair-pair tensor with block symmetry is zero if the lexicographic
upper-triangular ordered-pair components vanish. For a three-element ordered
basis, this is the six independent algebraic-curvature entries. -/
theorem tensor04_eq_zero_of_basis_ordered_block_components
    {ι : Type*} [Finite ι] [LinearOrder ι] (basis : Module.Basis ι R V)
    (T : TensorData R V 0 4)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h_anti_first : forall X Y Z W : V,
      T ![Y, X, Z, W] ![] = -T ![X, Y, Z, W] ![])
    (h_anti_last : forall X Y Z W : V,
      T ![X, Y, W, Z] ![] = -T ![X, Y, Z, W] ![])
    (h_block : forall X Y Z W : V,
      T ![Z, W, X, Y] ![] = T ![X, Y, Z, W] ![])
    (h_components : forall i j k l : ι, i < j -> k < l ->
      (i < k ∨ (i = k ∧ j ≤ l)) ->
        T ![basis i, basis j, basis k, basis l] ![] = 0) :
    T = 0 := by
  refine tensor04_eq_zero_of_basis_ordered_pair_components basis T h2
    h_anti_first h_anti_last ?_
  intro i j k l hij hkl
  by_cases hlex : i < k ∨ (i = k ∧ j ≤ l)
  · exact h_components i j k l hij hkl hlex
  · have hswap_lex : k < i ∨ (k = i ∧ l ≤ j) := by
      have h_not_i_lt_k : ¬ i < k := by
        intro hik
        exact hlex (Or.inl hik)
      have hki : k ≤ i := le_of_not_gt h_not_i_lt_k
      rcases lt_or_eq_of_le hki with hki_lt | hki_eq
      · exact Or.inl hki_lt
      · have hik_eq : i = k := hki_eq.symm
        have h_not_j_le_l : ¬ j ≤ l := by
          intro hjl
          exact hlex (Or.inr ⟨hik_eq, hjl⟩)
        have hlj : l ≤ j := le_of_not_ge h_not_j_le_l
        exact Or.inr ⟨hki_eq, hlj⟩
    have hswap := h_block (basis k) (basis l) (basis i) (basis j)
    rw [hswap]
    exact h_components k l i j hkl hij hswap_lex

/-- Component fallback for P2. A realization may prove the residual vanishes
on a chosen finite basis; this packages that component calculation into the
same public `HasRiemannFromRicci3DCalculus` target. -/
theorem hasRiemannFromRicci3DCalculus_of_basis_components
    {ι : Type*} [Finite ι] (basis : Module.Basis ι R V)
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_components :
      IsDimensionThree atr ->
        forall (half : R) (h_half : IsHalfCoefficient half) (idx : Fin 4 -> ι),
          riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
            half h_half (fun i => basis (idx i)) ![] = 0) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met := by
  refine hasRiemannFromRicci3DCalculus_of_residual_tensor_zero
    emb conn ha hal hsl hl atr met ?_
  intro h_dim half h_half
  exact tensor04_eq_zero_of_basis_components basis
    (riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half h_half)
    (h_components h_dim half h_half)

/-- Reduced component fallback for P2. If the realization proves the residual
only on basis components whose two curvature slot-pairs are distinct, the
skew symmetries fill in the repeated-pair components. -/
theorem hasRiemannFromRicci3DCalculus_of_distinct_pair_basis_components
    {ι : Type*} [Finite ι] (basis : Module.Basis ι R V)
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h_components :
      IsDimensionThree atr ->
        forall (half : R) (h_half : IsHalfCoefficient half) (i j k l : ι),
          i ≠ j -> k ≠ l ->
            riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
              half h_half ![basis i, basis j, basis k, basis l] ![] = 0) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met := by
  refine hasRiemannFromRicci3DCalculus_of_residual_tensor_zero
    emb conn ha hal hsl hl atr met ?_
  intro h_dim half h_half
  refine tensor04_eq_zero_of_basis_distinct_pair_components basis
    (riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half h_half)
    h2 ?_ ?_ ?_
  · intro X Y Z W
    simpa [riemannFromRicci3DResidualTensor_eval] using
      riemannFromRicci3DResidual_antisymm_first emb conn ha hal hsl hl atr met
        half h_half X Y Z W
  · intro X Y Z W
    simpa [riemannFromRicci3DResidualTensor_eval] using
      riemannFromRicci3DResidual_antisymm_last emb conn ha hal hsl hl atr met
        h_mc half h_half X Y Z W
  · intro i j k l hij hkl
    exact h_components h_dim half h_half i j k l hij hkl

/-- Ordered-pair component fallback for P2. With an ordered basis, skewness
reduces the realization target to components `i < j` and `k < l`. -/
theorem hasRiemannFromRicci3DCalculus_of_ordered_pair_basis_components
    {ι : Type*} [Finite ι] [LinearOrder ι] (basis : Module.Basis ι R V)
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h_components :
      IsDimensionThree atr ->
        forall (half : R) (h_half : IsHalfCoefficient half) (i j k l : ι),
          i < j -> k < l ->
            riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
              half h_half ![basis i, basis j, basis k, basis l] ![] = 0) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met := by
  refine hasRiemannFromRicci3DCalculus_of_residual_tensor_zero
    emb conn ha hal hsl hl atr met ?_
  intro h_dim half h_half
  refine tensor04_eq_zero_of_basis_ordered_pair_components basis
    (riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half h_half)
    h2 ?_ ?_ ?_
  · intro X Y Z W
    simpa [riemannFromRicci3DResidualTensor_eval] using
      riemannFromRicci3DResidual_antisymm_first emb conn ha hal hsl hl atr met
        half h_half X Y Z W
  · intro X Y Z W
    simpa [riemannFromRicci3DResidualTensor_eval] using
      riemannFromRicci3DResidual_antisymm_last emb conn ha hal hsl hl atr met
        h_mc half h_half X Y Z W
  · intro i j k l hij hkl
    exact h_components h_dim half h_half i j k l hij hkl

/-- Ordered block-symmetric component fallback for P2. With an ordered basis
and Ricci symmetry, the residual target reduces to the lexicographic
upper-triangular pair-pair components. In dimension three this is six scalar
component identities for each coherent half coefficient. -/
theorem hasRiemannFromRicci3DCalculus_of_ordered_block_basis_components
    {ι : Type*} [Finite ι] [LinearOrder ι] (basis : Module.Basis ι R V)
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h_Rc_symm : swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr) =
      ricciForm_tensor emb conn ha hal hsl hl atr)
    (h_components :
      IsDimensionThree atr ->
        forall (half : R) (h_half : IsHalfCoefficient half) (i j k l : ι),
          i < j -> k < l -> (i < k ∨ (i = k ∧ j ≤ l)) ->
            riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
              half h_half ![basis i, basis j, basis k, basis l] ![] = 0) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met := by
  refine hasRiemannFromRicci3DCalculus_of_residual_tensor_zero
    emb conn ha hal hsl hl atr met ?_
  intro h_dim half h_half
  refine tensor04_eq_zero_of_basis_ordered_block_components basis
    (riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met half h_half)
    h2 ?_ ?_ ?_ ?_
  · intro X Y Z W
    simpa [riemannFromRicci3DResidualTensor_eval] using
      riemannFromRicci3DResidual_antisymm_first emb conn ha hal hsl hl atr met
        half h_half X Y Z W
  · intro X Y Z W
    simpa [riemannFromRicci3DResidualTensor_eval] using
      riemannFromRicci3DResidual_antisymm_last emb conn ha hal hsl hl atr met
        h_mc half h_half X Y Z W
  · intro X Y Z W
    simpa [riemannFromRicci3DResidualTensor_eval] using
      riemannFromRicci3DResidual_block_symm_of_ricci_symm emb conn ha hal hsl hl
        atr met h_mc h_tf h2 h_Rc_symm half h_half X Y Z W
  · intro i j k l hij hkl hlex
    exact h_components h_dim half h_half i j k l hij hkl hlex

/-- `Fin 3` specialization of the ordered-block component fallback. The six
hypotheses are the independent upper-triangular components for the ordered
pairs `(0,1)`, `(0,2)`, and `(1,2)`. -/
theorem hasRiemannFromRicci3DCalculus_of_fin_three_ordered_block_components
    (basis : Module.Basis (Fin 3) R V)
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h_Rc_symm : swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr) =
      ricciForm_tensor emb conn ha hal hsl hl atr)
    (h01_01 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 0, basis 1, basis 0, basis 1] ![] = 0)
    (h01_02 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 0, basis 1, basis 0, basis 2] ![] = 0)
    (h01_12 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 0, basis 1, basis 1, basis 2] ![] = 0)
    (h02_02 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 0, basis 2, basis 0, basis 2] ![] = 0)
    (h02_12 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 0, basis 2, basis 1, basis 2] ![] = 0)
    (h12_12 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 1, basis 2, basis 1, basis 2] ![] = 0) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met := by
  refine hasRiemannFromRicci3DCalculus_of_ordered_block_basis_components basis
    emb conn ha hal hsl hl atr met h_mc h_tf h2 h_Rc_symm ?_
  intro h_dim half h_half i j k l hij hkl hlex
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
    <;> simp at hij hkl hlex
    <;> first
      | exact h01_01 h_dim half h_half
      | exact h01_02 h_dim half h_half
      | exact h01_12 h_dim half h_half
      | exact h02_02 h_dim half h_half
      | exact h02_12 h_dim half h_half
      | exact h12_12 h_dim half h_half

/-- `Fin 3` six-component P2 constructor with Ricci symmetry derived from
metric-adjoint trace invariance. This is the preferred finite-frame entry point
when the realization has a concrete trace model. -/
theorem hasRiemannFromRicci3DCalculus_of_fin_three_components_trace_adjoint
    (basis : Module.Basis (Fin 3) R V)
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasMetricAdjointTraceInvariant atr met]
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h01_01 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 0, basis 1, basis 0, basis 1] ![] = 0)
    (h01_02 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 0, basis 1, basis 0, basis 2] ![] = 0)
    (h01_12 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 0, basis 1, basis 1, basis 2] ![] = 0)
    (h02_02 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 0, basis 2, basis 0, basis 2] ![] = 0)
    (h02_12 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 0, basis 2, basis 1, basis 2] ![] = 0)
    (h12_12 :
      IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
        riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
          half h_half ![basis 1, basis 2, basis 1, basis 2] ![] = 0) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met :=
  hasRiemannFromRicci3DCalculus_of_fin_three_ordered_block_components
    basis emb conn ha hal hsl hl atr met h_mc h_tf h2
    (_root_.ricciForm_tensor_symm_of_metric_adjoint_trace_invariant
      emb conn ha hal hsl hl atr met h_mc h_tf h2)
    h01_01 h01_02 h01_12 h02_02 h02_12 h12_12

/-- Finite-frame P2 component package.

This is the realization-facing version of the six-component route: provide a
`Fin 3` frame, the curvature symmetry side conditions, and the six independent
upper-triangular residual components. The constructor below turns this package
into the public `HasRiemannFromRicci3DCalculus` target. -/
structure RiemannFromRicci3DFinThreeComponentPackage
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) where
  basis : Module.Basis (Fin 3) R V
  metric_compatible : IsMetricCompatible emb conn met
  torsion_free : IsTorsionFree emb conn
  two_cancel : forall a : R, 2 * a = 0 -> a = 0
  ricci_symm : swap_covariant (0 : Fin 2) 1
      (ricciForm_tensor emb conn ha hal hsl hl atr) =
    ricciForm_tensor emb conn ha hal hsl hl atr
  residual_01_01 :
    IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
      riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
        half h_half ![basis 0, basis 1, basis 0, basis 1] ![] = 0
  residual_01_02 :
    IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
      riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
        half h_half ![basis 0, basis 1, basis 0, basis 2] ![] = 0
  residual_01_12 :
    IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
      riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
        half h_half ![basis 0, basis 1, basis 1, basis 2] ![] = 0
  residual_02_02 :
    IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
      riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
        half h_half ![basis 0, basis 2, basis 0, basis 2] ![] = 0
  residual_02_12 :
    IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
      riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
        half h_half ![basis 0, basis 2, basis 1, basis 2] ![] = 0
  residual_12_12 :
    IsDimensionThree atr -> forall (half : R) (h_half : IsHalfCoefficient half),
      riemannFromRicci3DResidualTensor emb conn ha hal hsl hl atr met
        half h_half ![basis 1, basis 2, basis 1, basis 2] ![] = 0

/-- Realization-facing P2 package at the trace/eigenframe level.

This is the preferred P2 input after the convention fix. It asks for the data
that are geometrically natural at one tangent space: an orthonormal trace
formula, a Ricci eigenframe, and the off-diagonal Ricci trace equations. The
constructor below derives the older six-component residual package. -/
structure RiemannFromRicci3DTraceEigenframePackage
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) where
  trace_formula : HasOrthonormalBasisTraceFormula3 atr met
  metric_compatible : IsMetricCompatible emb conn met
  torsion_free : IsTorsionFree emb conn
  two_cancel : forall a : R, 2 * a = 0 -> a = 0
  half : R
  half_coeff : IsHalfCoefficient half
  ricci_symm : swap_covariant (0 : Fin 2) 1
      (ricciForm_tensor emb conn ha hal hsl hl atr) =
    ricciForm_tensor emb conn ha hal hsl hl atr
  diagonalization : RicciDiagonalization3D emb conn ha hal hsl hl atr met
  off_diagonal_trace :
    RicciOffDiagonalTraceFormula3D emb conn ha hal hsl hl atr met diagonalization

/-- Build the trace/eigenframe P2 package from a Ricci diagonalization.

This is the main per-slice producer once a realization has already supplied
the orthonormal trace formula and the Ricci eigenframe. The off-diagonal trace
equations are no longer separate inputs: they are derived from the trace formula
and the curvature-pair antisymmetries. -/
noncomputable def riemannFromRicci3DTraceEigenframePackage_of_diagonalization
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (half : R) (h_half : IsHalfCoefficient half)
    (h_Rc_symm : swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr) =
      ricciForm_tensor emb conn ha hal hsl hl atr)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met) :
    RiemannFromRicci3DTraceEigenframePackage emb conn ha hal hsl hl atr met where
  trace_formula := inferInstance
  metric_compatible := h_mc
  torsion_free := h_tf
  two_cancel := h2
  half := half
  half_coeff := h_half
  ricci_symm := h_Rc_symm
  diagonalization := diag
  off_diagonal_trace :=
    ricciOffDiagonalTraceFormula3D_of_orthonormal_trace3
      emb conn ha hal hsl hl atr met h_mc h2 diag

/-- Real inner-product per-slice P2 producer.

Mathematically this is the standard argument:

1. metric-adjoint trace invariance plus curvature block symmetry gives Ricci
   symmetry;
2. with `met.g = inner`, Ricci symmetry makes the Ricci endomorphism a
   symmetric real operator;
3. the spectral theorem gives an orthonormal Ricci eigenbasis;
4. the orthonormal trace formula gives the sectional and off-diagonal Ricci
   trace equations.

The downstream constructors then turn this package into
`RiemannFromRicci3DFormula`. -/
noncomputable def riemannFromRicci3DTraceEigenframePackage_of_real_inner_product
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (emb : DerivationEmbedding ℝ ℝ E) (conn : E -> E -> E)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : ℝ) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : ℝ) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace ℝ E) (met : MetricDuality ℝ E)
    [HasMetricAdjointTraceInvariant atr met]
    [HasOrthonormalBasisTraceFormula3 atr met]
    (hfin : Module.finrank ℝ E = 3)
    (h_met_inner : forall X Y, met.g X Y = inner ℝ X Y)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : ℝ, 2 * a = 0 -> a = 0)
    (half : ℝ) (h_half : IsHalfCoefficient half) :
    RiemannFromRicci3DTraceEigenframePackage emb conn ha hal hsl hl atr met :=
  let h_Rc_symm_point :
      forall X Y,
        Rc emb conn ha hal hsl hl atr X Y =
          Rc emb conn ha hal hsl hl atr Y X :=
    _root_.Rc_symm_of_metric_adjoint_trace_invariant
      emb conn ha hal hsl hl atr met h_mc h_tf h2
  let h_Rc_symm_tensor :
      swap_covariant (0 : Fin 2) 1
          (ricciForm_tensor emb conn ha hal hsl hl atr) =
        ricciForm_tensor emb conn ha hal hsl hl atr :=
    _root_.ricciForm_tensor_symm_of_Rc_symm
      emb conn ha hal hsl hl atr h_Rc_symm_point
  let diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met :=
    ricciDiagonalization3D_of_real_inner_product_and_Rc_symm
      emb conn ha hal hsl hl atr met hfin h_met_inner h_Rc_symm_point
  riemannFromRicci3DTraceEigenframePackage_of_diagonalization
    emb conn ha hal hsl hl atr met h_mc h_tf h2 half h_half
      h_Rc_symm_tensor diag

/-- Real finite-dimensional per-slice P2 producer from the standard trace.

This is the compact local route for P2: identify `atr.tr` with Mathlib's
finite-dimensional trace and `met.g` with the real inner product. The theorem
then supplies both trace bridges internally and calls the real inner-product
eigenframe constructor. -/
noncomputable def riemannFromRicci3DTraceEigenframePackage_of_real_trace_inner_product
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (emb : DerivationEmbedding ℝ ℝ E) (conn : E -> E -> E)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : ℝ) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : ℝ) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace ℝ E) (met : MetricDuality ℝ E)
    (htr : forall L : E →ₗ[ℝ] E, atr.tr L = LinearMap.trace ℝ E L)
    (hfin : Module.finrank ℝ E = 3)
    (h_met_inner : forall X Y : E, met.g X Y = inner ℝ X Y)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : ℝ, 2 * a = 0 -> a = 0)
    (half : ℝ) (h_half : IsHalfCoefficient half) :
    RiemannFromRicci3DTraceEigenframePackage emb conn ha hal hsl hl atr met := by
  haveI : HasMetricAdjointTraceInvariant atr met :=
    realTrace_hasMetricAdjointTraceInvariant atr met htr h_met_inner
  haveI : HasOrthonormalBasisTraceFormula3 atr met :=
    realTrace_hasOrthonormalBasisTraceFormula3 atr met htr h_met_inner
  exact riemannFromRicci3DTraceEigenframePackage_of_real_inner_product
    emb conn ha hal hsl hl atr met hfin h_met_inner h_mc h_tf h2 half h_half

/-- Convert the finite-frame six-component package into the named P2 calculus
class consumed by the stable Riemann-from-Ricci theorem. -/
theorem hasRiemannFromRicci3DCalculus_of_fin_three_component_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (pkg : RiemannFromRicci3DFinThreeComponentPackage
      emb conn ha hal hsl hl atr met) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met :=
  hasRiemannFromRicci3DCalculus_of_fin_three_ordered_block_components
    pkg.basis emb conn ha hal hsl hl atr met pkg.metric_compatible
    pkg.torsion_free pkg.two_cancel pkg.ricci_symm
    pkg.residual_01_01 pkg.residual_01_02 pkg.residual_01_12
    pkg.residual_02_02 pkg.residual_02_12 pkg.residual_12_12

/-- Build the sectional trace package directly from an orthonormal trace
formula and a Ricci eigenframe. -/
noncomputable def ricciSectionalTraceFormula3D_of_orthonormal_trace3
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasOrthonormalBasisTraceFormula3 atr met]
    (h_mc : IsMetricCompatible emb conn met)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R) (h_half : IsHalfCoefficient half) :
    RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half :=
  ricciSectionalTraceFormula3D_of_trace_equations emb conn ha hal hsl hl atr met
    diag h_mc half h_half
    (scalarCurvature_eq_sum_lambda_of_orthonormal_trace3
      emb conn ha hal hsl hl atr met diag)
    (ricciForm_tensor_eq_sectional_sum_of_orthonormal_trace3
      emb conn ha hal hsl hl atr met diag.basis diag.orthonormal h2)

/-- Build the six-component finite-frame package from one orthonormal Ricci
eigenframe, the three solved sectional components, and the three mixed
component vanishings.

This is the concrete P2 bridge after M1/M2/M3 have been discharged. It leaves
the spectral theorem and trace expansion outside the synthetic core, but the
six residual fields are no longer caller-supplied by hand. -/
noncomputable def riemannFromRicci3DFinThreeComponentPackage_of_eigenframe
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_mc : IsMetricCompatible emb conn met) (h_tf : IsTorsionFree emb conn)
    (h2 : forall a : R, 2 * a = 0 -> a = 0)
    (h_Rc_symm : swap_covariant (0 : Fin 2) 1
        (ricciForm_tensor emb conn ha hal hsl hl atr) =
      ricciForm_tensor emb conn ha hal hsl hl atr)
    (diag : RicciDiagonalization3D emb conn ha hal hsl hl atr met)
    (half : R)
    (sec : RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met diag half)
    (mixed : RicciMixedCurvatureFormula3D emb conn ha hal hsl hl atr met diag) :
    RiemannFromRicci3DFinThreeComponentPackage emb conn ha hal hsl hl atr met where
  basis := diag.basis
  metric_compatible := h_mc
  torsion_free := h_tf
  two_cancel := h2
  ricci_symm := h_Rc_symm
  residual_01_01 := by
    intro _ half' h_half'
    have hhalf : half' = half :=
      isHalfCoefficient_eq_of_two_cancel half half' h2 sec.h_half h_half'
    subst half'
    exact riemannFromRicci3DResidualTensor_01_01_of_sectional_trace
      emb conn ha hal hsl hl atr met diag half sec
  residual_01_02 := by
    intro _ half' h_half'
    exact riemannFromRicci3DResidualTensor_01_02_of_mixed_trace
      emb conn ha hal hsl hl atr met diag mixed half' h_half'
  residual_01_12 := by
    intro _ half' h_half'
    exact riemannFromRicci3DResidualTensor_01_12_of_mixed_trace
      emb conn ha hal hsl hl atr met diag mixed half' h_half'
  residual_02_02 := by
    intro _ half' h_half'
    have hhalf : half' = half :=
      isHalfCoefficient_eq_of_two_cancel half half' h2 sec.h_half h_half'
    subst half'
    exact riemannFromRicci3DResidualTensor_02_02_of_sectional_trace
      emb conn ha hal hsl hl atr met diag half sec
  residual_02_12 := by
    intro _ half' h_half'
    exact riemannFromRicci3DResidualTensor_02_12_of_mixed_trace
      emb conn ha hal hsl hl atr met diag mixed half' h_half'
  residual_12_12 := by
    intro _ half' h_half'
    have hhalf : half' = half :=
      isHalfCoefficient_eq_of_two_cancel half half' h2 sec.h_half h_half'
    subst half'
    exact riemannFromRicci3DResidualTensor_12_12_of_sectional_trace
      emb conn ha hal hsl hl atr met diag half sec

/-- Build the six-component package from the trace/eigenframe P2 package. -/
noncomputable def riemannFromRicci3DFinThreeComponentPackage_of_trace_eigenframe_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (pkg : RiemannFromRicci3DTraceEigenframePackage
      emb conn ha hal hsl hl atr met) :
    RiemannFromRicci3DFinThreeComponentPackage emb conn ha hal hsl hl atr met := by
  haveI : HasOrthonormalBasisTraceFormula3 atr met := pkg.trace_formula
  let sec : RicciSectionalTraceFormula3D emb conn ha hal hsl hl atr met
      pkg.diagonalization pkg.half :=
    ricciSectionalTraceFormula3D_of_orthonormal_trace3
      emb conn ha hal hsl hl atr met pkg.metric_compatible pkg.two_cancel
      pkg.diagonalization pkg.half pkg.half_coeff
  let mixed : RicciMixedCurvatureFormula3D emb conn ha hal hsl hl atr met
      pkg.diagonalization :=
    ricciMixedCurvatureFormula3D_of_offDiagonal_trace
      emb conn ha hal hsl hl atr met pkg.diagonalization pkg.off_diagonal_trace
  exact riemannFromRicci3DFinThreeComponentPackage_of_eigenframe
    emb conn ha hal hsl hl atr met pkg.metric_compatible pkg.torsion_free
    pkg.two_cancel pkg.ricci_symm pkg.diagonalization pkg.half sec mixed

/-- Convert the trace/eigenframe P2 package into the named P2 calculus class. -/
theorem hasRiemannFromRicci3DCalculus_of_trace_eigenframe_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (pkg : RiemannFromRicci3DTraceEigenframePackage
      emb conn ha hal hsl hl atr met) :
    HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met :=
  hasRiemannFromRicci3DCalculus_of_fin_three_component_package
    emb conn ha hal hsl hl atr met
    (riemannFromRicci3DFinThreeComponentPackage_of_trace_eigenframe_package
      emb conn ha hal hsl hl atr met pkg)

/-- Projection for the residual equation supplied by the named P2 calculus. -/
theorem riemannFromRicci3DResidual_eq_zero
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met]
    (h_dim : IsDimensionThree atr) (half : R) (h_half : IsHalfCoefficient half)
    (X Y Z W : V) :
    riemannFromRicci3DResidual emb conn ha hal hsl hl atr met
      half h_half X Y Z W = 0 :=
  HasRiemannFromRicci3DCalculus.residual_zero h_dim half h_half X Y Z W

/-- Build the pointwise lowered-Riemann package from the named P2 calculus. -/
noncomputable def riemannFromRicci3DDataPackage_from_dim3_calculus
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met]
    (h_dim : IsDimensionThree atr) (half : R) (h_half : IsHalfCoefficient half) :
    RiemannFromRicci3DDataPackage emb conn ha hal hsl hl atr met half where
  h_half := h_half
  lowered := loweredRmTensorData emb conn ha hal hsl hl met
  formula := by
    intro X Y Z W
    change loweredRmTensor emb conn ha hal hsl hl met ![X, Y, Z, W] ![] =
      riemannFromRicci3DRHS met
        (ricciForm_tensor emb conn ha hal hsl hl atr)
        (ScalarCurvature emb conn ha hal hsl hl atr met) half h_half X Y Z W
    rw [loweredRmTensor_eval]
    have h_residual :=
      riemannFromRicci3DResidual_eq_zero emb conn ha hal hsl hl atr met
        h_dim half h_half X Y Z W
    unfold riemannFromRicci3DResidual at h_residual
    exact sub_eq_zero.mp h_residual

/-- Convert a lowered-Riemann data package into the existing P2 formula
interface. -/
theorem riemannFromRicci3DFormula_from_data_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V) (half : R)
    (data : RiemannFromRicci3DDataPackage emb conn ha hal hsl hl atr met half) :
    RiemannFromRicci3DFormula emb conn ha hal hsl hl atr met half := by
  refine riemannFromRicci3DFormula_of_formula emb conn ha hal hsl hl atr met
    half data.h_half ?_
  intro X Y Z W
  calc
    met.g (Rm emb conn X Y Z) W = Rm_lowered emb conn met X Y Z W := by rfl
    _ = data.lowered.tensor ![X, Y, Z, W] ![] := by
      exact (data.lowered.eval X Y Z W).symm
    _ = riemannFromRicci3DRHS met
        (ricciForm_tensor emb conn ha hal hsl hl atr)
        (ScalarCurvature emb conn ha hal hsl hl atr met)
        half data.h_half X Y Z W := by
      exact data.formula X Y Z W

/-- Stable P2 entry theorem: the named calculus package plus
`IsDimensionThree` produces the existing Riemann-from-Ricci interface. -/
theorem riemannFromRicci3DFormula_from_dim3_calculus
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    [HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met]
    (h_dim : IsDimensionThree atr) (half : R) (h_half : IsHalfCoefficient half) :
    RiemannFromRicci3DFormula emb conn ha hal hsl hl atr met half :=
  riemannFromRicci3DFormula_from_data_package emb conn ha hal hsl hl atr met half
    (riemannFromRicci3DDataPackage_from_dim3_calculus
      emb conn ha hal hsl hl atr met h_dim half h_half)

/-- Stable P2 theorem from the finite-frame component package. This is the
lowest-friction entry point for a coordinate realization that has already
checked the six independent residual components. -/
theorem riemannFromRicci3DFormula_from_fin_three_component_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_dim : IsDimensionThree atr) (half : R) (h_half : IsHalfCoefficient half)
    (pkg : RiemannFromRicci3DFinThreeComponentPackage
      emb conn ha hal hsl hl atr met) :
    RiemannFromRicci3DFormula emb conn ha hal hsl hl atr met half := by
  haveI : HasRiemannFromRicci3DCalculus emb conn ha hal hsl hl atr met :=
    hasRiemannFromRicci3DCalculus_of_fin_three_component_package
      emb conn ha hal hsl hl atr met pkg
  exact riemannFromRicci3DFormula_from_dim3_calculus emb conn ha hal hsl hl atr met
    h_dim half h_half

/-- Stable P2 theorem from the trace/eigenframe package. This is the preferred
entry point after the orthonormal trace and eigenframe bridges have been
realized. -/
theorem riemannFromRicci3DFormula_from_trace_eigenframe_package
    (emb : DerivationEmbedding k R V) (conn : V -> V -> V)
    (ha : forall X Y Z, conn X (Y + Z) = conn X Y + conn X Z)
    (hal : forall X Y Z, conn (X + Y) Z = conn X Z + conn Y Z)
    (hsl : forall (f : R) X Z, conn (f • X) Z = f • conn X Z)
    (hl : forall X (f : R) Y, conn X (f • Y) = (emb.embed X) f • Y + f • conn X Y)
    (atr : AbstractTrace R V) (met : MetricDuality R V)
    (h_dim : IsDimensionThree atr) (half : R) (h_half : IsHalfCoefficient half)
    (pkg : RiemannFromRicci3DTraceEigenframePackage
      emb conn ha hal hsl hl atr met) :
    RiemannFromRicci3DFormula emb conn ha hal hsl hl atr met half :=
  riemannFromRicci3DFormula_from_fin_three_component_package
    emb conn ha hal hsl hl atr met h_dim half h_half
    (riemannFromRicci3DFinThreeComponentPackage_of_trace_eigenframe_package
      emb conn ha hal hsl hl atr met pkg)

end RiemannFromRicci3D
