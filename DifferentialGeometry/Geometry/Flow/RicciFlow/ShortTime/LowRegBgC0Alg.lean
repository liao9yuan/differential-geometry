import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseC2Lip
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseH2Pair

/-!
# Order-zero refold algebra

Internal implementation layer for the low-regularity order-zero refold.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace LowRegBgC0Core

theorem ricciDA_self
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 2
        (LowBaseInternal.ricciDALow (I := I) (M := M) g gm T) T =
      appCc (I := I) (M := M) g 3 2
        (LowBaseInternal.ricciDAOne (I := I) (M := M) g gm T)
        (iteratedCovGrad (I := I) g 0 2 1 T) := by
  rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  exact LowBaseInternal.ricciDA_one (I := I) (M := M) g gm T T

theorem ipLow_swap
    (g : SmoothRiemannianMetric I M) (om : SmoothCcTensor g 0 1)
    (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 1
        (ipLowCc (I := I) (M := M) g om) W =
      appCc (I := I) (M := M) g 1 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W) om := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  let alpha : Tensor0SSpace 1 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from om.toSection x)
      (unitTensor (I := I) (M := M) x)
  have hflat : ∀ z : TangentSpace I x,
      unitModel (I := I) (M := M) g 1 om x (fun _ : Fin 1 => z) =
        g.inner x (inverseMetricSharpFib (I := I) g x alpha) z := by
    intro z
    rw [inverseMetricSharpFib_inner]
    change Tensor0SSpace.toModel alpha (fun _ : Fin 1 => (z : E)) =
      cotangentToDualLinear (I := I) (x := x) alpha z
    rw [show cotangentToDualLinear (I := I) (x := x) alpha z =
      cotangentToDual (I := I) (x := x) alpha z from rfl]
    rw [cotangentToDual_apply]
    rfl
  apply ContinuousMultilinearMap.ext
  intro m
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ipLowCc_toSec_ip (I := I) (M := M) g om x
    (inverseMetricSharpFib (I := I) g x alpha) hflat]
  rw [cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Fib_clm_apply]

set_option linter.unusedSectionVars false in
lemma unitModel0 (x : M) (m : Fin 0 → E) :
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) m = 1 := by
  rw [unitTensor, Tensor0SSpace.toModel_ofModel]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem unit_add
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2 (A + B) x v =
      unitModel (I := I) (M := M) g 2 A x v +
        unitModel (I := I) (M := M) g 2 B x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

lemma curry0 (x : M) (D : Tensor0SSpace 1 I x) (v₀ : E) :
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v₀ =
      Tensor0SSpace.toModel D (fun _ : Fin 1 => v₀) •
        unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have h₁ : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v₀) m =
      Tensor0SSpace.toModel D (Fin.cons v₀ m) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := D) (v0 := v₀) (vs := m)
  rw [h₁, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, unitModel0 (I := I) (M := M) x m,
    smul_eq_mul, mul_one]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => j.elim0) k
  rfl

set_option linter.unusedSectionVars false in
lemma clm_smul (x : M) (s : ℕ)
    (A : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (c : ℝ) :
    A (c • unitTensor (I := I) (M := M) x) =
      c • A (unitTensor (I := I) (M := M) x) := A.map_smul c _

lemma slotLift23 (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 3) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel kappa (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) g 1 4 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
              (slotExtendIter (I := I) (M := M) g 0 3 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g 1 4 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g 0 3 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) g 0 3 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
              K.toSection x) D₁ from rfl]
    rw [show (Fin.tail m : Fin 4 → E) =
        Fin.cons (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g 0 3 x _ D₁
      (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j))]
    rw [curry0 (I := I) (M := M) x D₁ (m 1)]
    rw [clm_smul (I := I) (M := M) x 3 _ _]
    rw [← hkappa, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

lemma slotLift24 (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 4) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g 0 4 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 4 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g 0 4 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel kappa (fun j : Fin 4 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g 0 4 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) g 1 5 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
              (slotExtendIter (I := I) (M := M) g 0 4 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g 1 5 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g 0 4 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) g 0 4 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              K.toSection x) D₁ from rfl]
    rw [show (Fin.tail m : Fin 5 → E) =
        Fin.cons (m 1) (fun j : Fin 4 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g 0 4 x _ D₁
      (m 1) (fun j : Fin 4 => m (Fin.natAdd 2 j))]
    rw [curry0 (I := I) (M := M) x D₁ (m 1)]
    rw [clm_smul (I := I) (M := M) x 4 _ _]
    rw [← hkappa, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

lemma slotLift22 (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 2) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 2) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel kappa (fun j : Fin 2 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) g 1 3 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
              (slotExtendIter (I := I) (M := M) g 0 2 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g 1 3 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) g 0 2 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              K.toSection x) D₁ from rfl]
    rw [show (Fin.tail m : Fin 3 → E) =
        Fin.cons (m 1) (fun j : Fin 2 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g 0 2 x _ D₁
      (m 1) (fun j : Fin 2 => m (Fin.natAdd 2 j))]
    rw [curry0 (I := I) (M := M) x D₁ (m 1)]
    rw [clm_smul (I := I) (M := M) x 2 _ _]
    rw [← hkappa, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

lemma slotLift32 (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 2) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g 0 2 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 2) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g 0 2 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel kappa (fun j : Fin 2 => m (Fin.natAdd 3 j)) := by
    rw [show
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 3 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) g 2 4 x
            (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
              (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g 2 4 x _ D
      (m 0) (Fin.tail m)]
    set D₂ : Tensor0SSpace 2 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (m 0) with hD₂
    rw [slotLift22 (I := I) (M := M) g K x D₂, ← hkappa,
      tensor0SProdKappaFib_apply (I := I) x kappa D₂,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD₂val : Tensor0SSpace.toModel D₂
        ((Fin.tail m : Fin 4 → E) ∘ Fin.castAdd 2) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD₂, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 2) (T := D) (v0 := m 0)
        (vs := (Fin.tail m : Fin 4 → E) ∘ Fin.castAdd 2)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₂val]
    first
      | rfl
      | (congr 2; funext j; fin_cases j <;> rfl)
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

lemma slotLift33 (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 3) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g 0 3 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g 0 3 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel kappa (fun j : Fin 3 => m (Fin.natAdd 3 j)) := by
    rw [show
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g 0 3 3 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) g 2 5 x
            (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
              (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g 2 5 x _ D
      (m 0) (Fin.tail m)]
    set D₂ : Tensor0SSpace 2 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (m 0) with hD₂
    rw [slotLift23 (I := I) (M := M) g K x D₂, ← hkappa,
      tensor0SProdKappaFib_apply (I := I) x kappa D₂,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD₂val : Tensor0SSpace.toModel D₂
        ((Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD₂, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 2) (T := D) (v0 := m 0)
        (vs := (Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₂val]
    first
      | rfl
      | (congr 2; funext j; fin_cases j <;> rfl)
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

theorem perm_app
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (S : SmoothCcTensor g 0 d) :
    appCcRS (I := I) (M := M) g 0 d d
        (permCoeff (I := I) (M := M) g ρ) S =
      domDomCongrSection (I := I) g ρ S := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [domDomCongrSection_unitModel]
  rw [unitModel, appCcRS_toSection, ContinuousLinearMap.comp_apply]
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) ρ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace d I x from
          S.toSection x) (unitTensor (I := I) (M := M) x))) = _
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]
  rfl

theorem perm_rs
    (g : SmoothRiemannianMetric I M) {a d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (S : SmoothCcTensor g a d) :
    appCcRS (I := I) (M := M) g a d d
        (permCoeff (I := I) (M := M) g ρ) S =
      rsDomDomCongrSection (I := I) (M := M) g a d ρ S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection, rsDomDomCongrSection_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.comp_apply]
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) ρ x
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace d I x from
          S.toSection x) D)) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace d I x from
        rsDomDomCongr ρ (S.toSection x)) D)
  rw [toModel_rsDomDomCongr_apply, slotPermCLM_apply,
    Tensor0SSpace.toModel_ofModel]

theorem slot_comp
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (A : SmoothCcTensor g b c) (B : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g (a + 1) (b + 1) (c + 1)
        (slotExtend (I := I) (M := M) g b c A)
        (slotExtend (I := I) (M := M) g a b B) =
      slotExtend (I := I) (M := M) g a c
        (appCcRS (I := I) (M := M) g a b c A B) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [appCcRS_toSection, slotExtend_toSection, slotExtend_toSection,
    slotExtend_toSection, appCcRS_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.comp_apply]
  rw [slotExtendFib_apply, slotExtendFib_apply, slotExtendFib_apply]
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [ContinuousLinearMap.comp_assoc]

theorem slot_comp2
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (A : SmoothCcTensor g b c) (B : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g (a + 2) (b + 2) (c + 2)
        (slotExtendIter (I := I) (M := M) g b c 2 A)
        (slotExtendIter (I := I) (M := M) g a b 2 B) =
      slotExtendIter (I := I) (M := M) g a c 2
        (appCcRS (I := I) (M := M) g a b c A B) := by
  change appCcRS (I := I) (M := M) g ((a + 1) + 1) ((b + 1) + 1) ((c + 1) + 1)
      (slotExtend (I := I) (M := M) g (b + 1) (c + 1)
        (slotExtend (I := I) (M := M) g b c A))
      (slotExtend (I := I) (M := M) g (a + 1) (b + 1)
        (slotExtend (I := I) (M := M) g a b B)) =
    slotExtend (I := I) (M := M) g (a + 1) (c + 1)
      (slotExtend (I := I) (M := M) g a c
        (appCcRS (I := I) (M := M) g a b c A B))
  rw [slot_comp (I := I) (M := M) g (a + 1) (b + 1) (c + 1)]
  rw [slot_comp (I := I) (M := M) g a b c]

noncomputable def koszulOne
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  (1 / 2 : ℝ) •
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
      permCoeff (I := I) (M := M) g (finRotate 3) -
      permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2))

theorem koszul_one_app
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u) :
    appCcRS (I := I) (M := M) g 0 3 3
        (koszulOne (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      koszulCovecCc (I := I) g T := by
  have hs := symmS_eq_self_of_ccTensorBilin_symm
    (I := I) (M := M) g T hT
  have hp (ρ : Equiv.Perm (Fin 3)) :
      appCc (I := I) (M := M) g 3 3
          (permCoeff (I := I) (M := M) g ρ)
          (covGrad (I := I) (M := M) g 0 2 T) =
        domDomCongrSection (I := I) g ρ
          (covGrad (I := I) (M := M) g 0 2 T) := by
    simpa only [appCcRS_zero_eq_appCc] using
      perm_app (I := I) (M := M) g ρ
        (covGrad (I := I) (M := M) g 0 2 T)
  rw [appCcRS_zero_eq_appCc, koszulOne, appCc_smul_left,
    appCc_sub_left, appCc_add_left, hp, hp, hp]
  rw [koszulCovecCc, symmSCovGrad3, hs]

noncomputable def mcdOne
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  appCcRS (I := I) (M := M) g 3 3 3
    (permCoeff (I := I) (M := M) g (finRotate 3).symm)
    (koszulOne (I := I) (M := M) g)

theorem mcd_one_app
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    appCcRS (I := I) (M := M) g 0 3 3
        (mcdOne (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      lc0Kappa (I := I) (M := M) g gm g := by
  rw [appCcRS_zero_eq_appCc, mcdOne, ← appCc_assoc]
  rw [show appCc (I := I) (M := M) g 3 3
      (koszulOne (I := I) (M := M) g)
      (covGrad (I := I) (M := M) g 0 2 T) =
        koszulCovecCc (I := I) g T by
      rw [← appCcRS_zero_eq_appCc]
      exact koszul_one_app (I := I) (M := M) g T hT]
  rw [← appCcRS_zero_eq_appCc, perm_app]
  exact (kappa_self (I := I) (M := M) g gm T htie).symm

def block23 : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 4, 0, 1], ![3, 4, 0, 1, 2], by decide, by decide⟩

noncomputable def prod23
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 5 :=
  appCcRS (I := I) (M := M) g 3 5 5
    (permCoeff (I := I) (M := M) g block23)
    (slotExtendIter (I := I) (M := M) g 0 2 3 W)

theorem prod23_app
    (g : SmoothRiemannianMetric I M) (K : SmoothCcTensor g 0 3)
    (W : SmoothCcTensor g 0 2) :
    appCcRS (I := I) (M := M) g 0 3 5
        (prod23 (I := I) (M := M) g W) K =
      appCcRS (I := I) (M := M) g 0 2 5
        (slotExtendIter (I := I) (M := M) g 0 3 2 K) W := by
  rw [appCcRS_zero_eq_appCc, appCcRS_zero_eq_appCc, prod23,
    ← appCc_assoc, ← appCcRS_zero_eq_appCc, perm_app]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [slotLift32 (I := I) (M := M) g W x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        K.toSection x) (unitTensor (I := I) (M := M) x)),
    slotLift23 (I := I) (M := M) g K x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x))]
  rw [tensor0SProdKappaFib_apply, tensor0SProdKappaFib_apply,
    Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  have hK :
      ((fun i => m (block23 i)) ∘ Fin.castAdd 2) =
        (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    funext j
    fin_cases j <;> rfl
  have hW :
      ((fun i => m (block23 i)) ∘ Fin.natAdd 3) =
        (![m 0, m 1] : Fin 2 → E) := by
    funext j
    fin_cases j <;> rfl
  have hK₀ :
      (m ∘ Fin.natAdd 2) =
        (fun j : Fin 3 => m (Fin.natAdd 2 j)) := rfl
  have hW₀ :
      (m ∘ Fin.castAdd 3) = (![m 0, m 1] : Fin 2 → E) := by
    funext j
    fin_cases j <;> rfl
  rw [hK, hW, hK₀, hW₀]
  exact mul_comm _ _

noncomputable def amixHalfOne
    (g gm gB : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (σlast : Equiv.Perm (Fin 4)) : SmoothCcTensor g 3 2 :=
  appCcRS (I := I) (M := M) g 3 4 2
    (lc0TraceRF (I := I) (M := M) g gm 2 σlast)
    (appCcRS (I := I) (M := M) g 3 6 4
      (lc0TraceRF (I := I) (M := M) g gm 4
        LieCorr0Core.lieCorr0AMixPerm1)
      (appCcRS (I := I) (M := M) g 3 3 6
        (slotExtendIter (I := I) (M := M) g 0 3 3
          (metricConnDiffLoweredCc (I := I) (M := M) g gm gB))
        (appCcRS (I := I) (M := M) g 3 5 3
          (lc0TraceRF (I := I) (M := M) g gm 3
            LieCorr0Core.lieCorr0AMixPermQ)
          (appCcRS (I := I) (M := M) g 3 3 5
            (prod23 (I := I) (M := M) g W)
            (mcdOne (I := I) (M := M) g)))))

theorem amix_half_one
    (g gm gB : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (σlast : Equiv.Perm (Fin 4))
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 2
        (lc0AMixHalfRF (I := I) (M := M) g gm gB σlast) W =
      appCc (I := I) (M := M) g 3 2
        (amixHalfOne (I := I) (M := M) g gm gB W σlast)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hprod :
      appCc (I := I) (M := M) g 2 5
          (slotExtendIter (I := I) (M := M) g 0 3 2
            (metricConnDiffLoweredCc (I := I) (M := M) g gm g)) W =
        appCc (I := I) (M := M) g 3 5
          (prod23 (I := I) (M := M) g W)
          (metricConnDiffLoweredCc (I := I) (M := M) g gm g) := by
    simpa only [appCcRS_zero_eq_appCc] using
      (prod23_app (I := I) (M := M) g
        (metricConnDiffLoweredCc (I := I) (M := M) g gm g) W).symm
  have hconn :
      appCc (I := I) (M := M) g 3 3
          (mcdOne (I := I) (M := M) g)
          (covGrad (I := I) (M := M) g 0 2 P) =
        metricConnDiffLoweredCc (I := I) (M := M) g gm g := by
    change appCc (I := I) (M := M) g 3 3
        (mcdOne (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 P) =
      lc0Kappa (I := I) (M := M) g gm g
    simpa only [appCcRS_zero_eq_appCc] using
      mcd_one_app (I := I) (M := M) g gm P hP htie
  rw [lc0AMixHalfRF]
  conv_lhs =>
    rw [← appCc_assoc, ← appCc_assoc, ← appCc_assoc, ← appCc_assoc]
  rw [hprod, ← hconn]
  rw [amixHalfOne]
  conv_rhs =>
    rw [← appCc_assoc, ← appCc_assoc, ← appCc_assoc, ← appCc_assoc,
      ← appCc_assoc]

noncomputable def amixOne
    (g gm gB : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  (2 : ℝ) •
    (amixHalfOne (I := I) (M := M) g gm gB W
        LieCorr0Core.lieCorr0AMixPerm2 +
      amixHalfOne (I := I) (M := M) g gm gB W
        (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2))

theorem amix_one
    (g gm gB : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 2
        (lc0AMixFormRF (I := I) (M := M) g gm gB) W =
      appCc (I := I) (M := M) g 3 2
        (amixOne (I := I) (M := M) g gm gB W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [lc0AMixFormRF, appCc_smul_left, appCc_add_left]
  rw [amix_half_one (I := I) (M := M) g gm gB P W
      LieCorr0Core.lieCorr0AMixPerm2 hP htie]
  rw [amix_half_one (I := I) (M := M) g gm gB P W
      (lc0SwapPermRF * LieCorr0Core.lieCorr0AMixPerm2) hP htie]
  rw [amixOne, appCc_smul_left, appCc_add_left]

noncomputable def vbCore
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  appCcRS (I := I) (M := M) g 3 4 2
    (lc0RiemLive (I := I) (M := M) g gm)
    (appCcRS (I := I) (M := M) g 3 1 4
      (vbMcdArm (I := I) (M := M) g gm)
      (appCcRS (I := I) (M := M) g 3 1 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W)
        (appCcRS (I := I) (M := M) g 3 3 1
          (lc0TraceRF (I := I) (M := M) g gm 1 (Equiv.refl _))
          (LowBaseInternal.connLowOp (I := I) (M := M) g gm))))

noncomputable def vbOne
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  (2 : ℝ) • vbCore (I := I) (M := M) g gm W

theorem vb_one
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 2
        (lc0VBFormRF (I := I) (M := M) g gm) W =
      appCc (I := I) (M := M) g 3 2
        (vbOne (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [lc0VBFormRF, appCc_smul_left]
  rw [← appCc_assoc, ← appCc_assoc]
  rw [ipLow_swap]
  rw [wOmega_refold, appCcRS_zero_eq_appCc]
  rw [← LowBaseInternal.connLow_app (I := I) (M := M) g gm P hP htie]
  rw [appCcRS_zero_eq_appCc]
  rw [vbOne, vbCore, appCc_smul_left]
  conv_rhs =>
    rw [← appCc_assoc, ← appCc_assoc, ← appCc_assoc, ← appCc_assoc]

noncomputable def innerOne
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 3 :=
  appCcRS (I := I) (M := M) g 3 3 3
    (slotInsertEndoCc (I := I) (M := M) g 2
      (symmRaiseEndo (I := I) (M := M) g W))
    (permCoeff (I := I) (M := M) g (finRotate 3))

theorem inner_one
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 3
        (connDiffContrInsertionInnerField (I := I) g gm)
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 3
        (innerOne (I := I) (M := M) g W)
        (connDiffLoweredCc (I := I) g gm) := by
  rw [innerOne, ← appCc_assoc]
  rw [show appCc (I := I) (M := M) g 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (connDiffLoweredCc (I := I) g gm) =
        domDomCongrSection (I := I) g (finRotate 3)
          (connDiffLoweredCc (I := I) g gm) by
    rw [← appCcRS_zero_eq_appCc]
    exact perm_app (I := I) (M := M) g (finRotate 3)
      (connDiffLoweredCc (I := I) g gm)]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = ![m 0, m 1, m 2] := by
    funext j
    fin_cases j <;> rfl
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [connDiffContrInsertionInnerField_toSection]
  conv_lhs => rw [hm]
  rw [connContr11_insert']
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (symmS (I := I) (M := M) g W).toSection x)
        (unitTensor (I := I) (M := M) x))
      ![PDE.DeTurck.connDiff (I := I) gm g x (m 1) (m 2), m 0] =
        ccTensorBilin (I := I) g (symmS (I := I) (M := M) g W) x
          (PDE.DeTurck.connDiff (I := I) gm g x (m 1) (m 2)) (m 0) by
    rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g]
    rfl]
  rw [ccTensorBilin_symmS]
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (domDomCongrSection (I := I) g (finRotate 3)
          (connDiffLoweredCc (I := I) g gm)).toSection x)
        (unitTensor (I := I) (M := M) x))
      (Function.update m 0
        (symmRaiseEndo (I := I) (M := M) g W x (m 0))) =
        unitModel (I := I) (M := M) g 3
          (domDomCongrSection (I := I) g (finRotate 3)
            (connDiffLoweredCc (I := I) g gm)) x
          (Function.update m 0
            (symmRaiseEndo (I := I) (M := M) g W x (m 0))) from rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i =>
      Function.update m 0
        (symmRaiseEndo (I := I) (M := M) g W x (m 0)) ((finRotate 3) i)) =
        ![m 1, m 2, symmRaiseEndo (I := I) (M := M) g W x (m 0)] by
    funext j
    fin_cases j <;> rfl]
  rw [connDiffLoweredCc_unitModel_apply']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [g.symm, symmRaiseEndo_apply, inner_symmRaiseEndo]
  exact ccTensorBilinSymm_symm (I := I) g W x _ _

noncomputable def innerAct
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 3 :=
  appCcRS (I := I) (M := M) g 3 3 3
    (innerOne (I := I) (M := M) g W)
    (LowBaseInternal.connLowOp (I := I) (M := M) g gm)

theorem inner_act
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 3
        (connDiffContrInsertionInnerField (I := I) g gm)
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 3
        (innerAct (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [inner_one (I := I) (M := M) g gm W]
  rw [← LowBaseInternal.connLow_app (I := I) (M := M) g gm P hP htie]
  rw [innerAct, ← appCc_assoc]
  rw [appCcRS_zero_eq_appCc]

theorem reindex_symm
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (R : SmoothCcTensor g 2 s) (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 s
        (reindexCoeffGen (I := I) (M := M) g 2 s R innerCoreInPerm10)
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 2 s R
        (symmS (I := I) (M := M) g W) := by
  have hperm : innerCoreInPerm10 = Equiv.swap (0 : Fin 2) 1 := by
    ext j
    fin_cases j <;> rfl
  rw [hperm]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [unitModel, unitModel, appCc_toSection, appCc_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply]
  have hu : Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g W).toSection x)
            (unitTensor (I := I) (M := M) x)))) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (symmS (I := I) (M := M) g W).toSection x)
        (unitTensor (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    change ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g W).toSection x)
            (unitTensor (I := I) (M := M) x))) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (symmS (I := I) (M := M) g W).toSection x)
          (unitTensor (I := I) (M := M) x))
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext j
      fin_cases j <;> rfl
    have hv' : v = ![v 0, v 1] := by
      funext j
      fin_cases j <;> rfl
    rw [hv]
    conv_rhs => rw [hv']
    change unitModel (I := I) (M := M) g 2
        (symmS (I := I) (M := M) g W) x ![v 1, v 0] =
      unitModel (I := I) (M := M) g 2
        (symmS (I := I) (M := M) g W) x ![v 0, v 1]
    rw [unitModel_eq_ccTensorBilin_local,
      unitModel_eq_ccTensorBilin_local, ccTensorBilin_symmS,
      ccTensorBilin_symmS]
    exact ccTensorBilinSymm_symm (I := I) g W x (v 1) (v 0)
  rw [hu]

def ricPerm3201 : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

def ricPerm2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

def ricPerm3102 : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

def ricPerm1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

def ricPerm1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

def ricPerm2103 : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

def ricPerm102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

def ricPerm120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

noncomputable def aa0
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm3201)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (appCcRS (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricPerm102)
        (connDiffContrInsertionInnerField (I := I) g gm)))

noncomputable def aaMidOne
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 3 4 :=
  appCcRS (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g out)
    (appCcRS (I := I) (M := M) g 3 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (appCcRS (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g mid)
        (innerAct (I := I) (M := M) g gm W)))

theorem aa_mid_act
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4))
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 4
        (appCcRS (I := I) (M := M) g 2 4 4
          (permCoeff (I := I) (M := M) g out)
          (appCcRS (I := I) (M := M) g 2 3 4
            (connDiffContrInsertionField (I := I) g gm)
            (appCcRS (I := I) (M := M) g 2 3 3
              (permCoeff (I := I) (M := M) g mid)
              (connDiffContrInsertionInnerField (I := I) g gm))))
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 4
        (aaMidOne (I := I) (M := M) g gm W mid out)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  conv_lhs =>
    rw [← appCc_assoc, ← appCc_assoc, ← appCc_assoc]
  rw [inner_act (I := I) (M := M) g gm P W hP htie]
  rw [aaMidOne]
  conv_rhs =>
    rw [← appCc_assoc, ← appCc_assoc, ← appCc_assoc]

theorem aa0_act
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 4 (aa0 (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 4
        (aaMidOne (I := I) (M := M) g gm W ricPerm102 ricPerm3201)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [aa0]
  exact aa_mid_act (I := I) (M := M) g gm P W
    ricPerm102 ricPerm3201 hP htie

noncomputable def aa1
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm2301)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gm)
        (appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricPerm102)
          (connDiffContrInsertionInnerField (I := I) g gm))))
    innerCoreInPerm10

noncomputable def aa2
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm3102)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (appCcRS (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricPerm120)
        (connDiffContrInsertionInnerField (I := I) g gm)))

noncomputable def aa3
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm1302)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gm)
        (connDiffContrInsertionInnerField (I := I) g gm)))
    innerCoreInPerm10

noncomputable def aa4
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm1203)
    (appCcRS (I := I) (M := M) g 2 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (connDiffContrInsertionInnerField (I := I) g gm))

noncomputable def aa5
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (appCcRS (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricPerm2103)
      (appCcRS (I := I) (M := M) g 2 3 4
        (connDiffContrInsertionField (I := I) g gm)
        (appCcRS (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricPerm120)
          (connDiffContrInsertionInnerField (I := I) g gm))))
    innerCoreInPerm10

theorem aaKer_eq
    (g gm : SmoothRiemannianMetric I M) :
    ricciAAKer (I := I) (M := M) g gm =
      aa0 (I := I) (M := M) g gm +
      aa1 (I := I) (M := M) g gm +
      aa2 (I := I) (M := M) g gm +
      aa3 (I := I) (M := M) g gm +
      aa4 (I := I) (M := M) g gm +
      aa5 (I := I) (M := M) g gm := by
  rfl

noncomputable def aaBareOne
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (out : Equiv.Perm (Fin 4)) : SmoothCcTensor g 3 4 :=
  appCcRS (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g out)
    (appCcRS (I := I) (M := M) g 3 3 4
      (connDiffContrInsertionField (I := I) g gm)
      (innerAct (I := I) (M := M) g gm W))

theorem aa_bare_act
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (out : Equiv.Perm (Fin 4))
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 4
        (appCcRS (I := I) (M := M) g 2 4 4
          (permCoeff (I := I) (M := M) g out)
          (appCcRS (I := I) (M := M) g 2 3 4
            (connDiffContrInsertionField (I := I) g gm)
            (connDiffContrInsertionInnerField (I := I) g gm)))
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 4
        (aaBareOne (I := I) (M := M) g gm W out)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  conv_lhs =>
    rw [← appCc_assoc, ← appCc_assoc]
  rw [inner_act (I := I) (M := M) g gm P W hP htie]
  rw [aaBareOne]
  conv_rhs =>
    rw [← appCc_assoc, ← appCc_assoc]

theorem aa1_act
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 4 (aa1 (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 4
        (aaMidOne (I := I) (M := M) g gm W ricPerm102 ricPerm2301)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [aa1, reindex_symm]
  exact aa_mid_act (I := I) (M := M) g gm P W
    ricPerm102 ricPerm2301 hP htie

theorem aa2_act
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 4 (aa2 (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 4
        (aaMidOne (I := I) (M := M) g gm W ricPerm120 ricPerm3102)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [aa2]
  exact aa_mid_act (I := I) (M := M) g gm P W
    ricPerm120 ricPerm3102 hP htie

theorem aa3_act
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 4 (aa3 (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 4
        (aaBareOne (I := I) (M := M) g gm W ricPerm1302)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [aa3, reindex_symm]
  exact aa_bare_act (I := I) (M := M) g gm P W ricPerm1302 hP htie

theorem aa4_act
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 4 (aa4 (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 4
        (aaBareOne (I := I) (M := M) g gm W ricPerm1203)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [aa4]
  exact aa_bare_act (I := I) (M := M) g gm P W ricPerm1203 hP htie

theorem aa5_act
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 4 (aa5 (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 4
        (aaMidOne (I := I) (M := M) g gm W ricPerm120 ricPerm2103)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [aa5, reindex_symm]
  exact aa_mid_act (I := I) (M := M) g gm P W
    ricPerm120 ricPerm2103 hP htie

noncomputable def aaKerOne
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 4 :=
  aaMidOne (I := I) (M := M) g gm W ricPerm102 ricPerm3201 +
    aaMidOne (I := I) (M := M) g gm W ricPerm102 ricPerm2301 +
    aaMidOne (I := I) (M := M) g gm W ricPerm120 ricPerm3102 +
    aaBareOne (I := I) (M := M) g gm W ricPerm1302 +
    aaBareOne (I := I) (M := M) g gm W ricPerm1203 +
    aaMidOne (I := I) (M := M) g gm W ricPerm120 ricPerm2103

noncomputable def aaOne
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  appCcRS (I := I) (M := M) g 3 4 2
    (ricciCometricFourTraceCastG0 (I := I) g gm)
    (aaKerOne (I := I) (M := M) g gm W)

theorem aa_one
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 2
        (ricciAAArm (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      appCc (I := I) (M := M) g 3 2
        (aaOne (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [ricciAAArm, ← appCc_assoc, aaKer_eq]
  simp only [appCc_add_left]
  rw [aa0_act (I := I) (M := M) g gm P W hP htie,
    aa1_act (I := I) (M := M) g gm P W hP htie,
    aa2_act (I := I) (M := M) g gm P W hP htie,
    aa3_act (I := I) (M := M) g gm P W hP htie,
    aa4_act (I := I) (M := M) g gm P W hP htie,
    aa5_act (I := I) (M := M) g gm P W hP htie]
  rw [aaOne, ← appCc_assoc, aaKerOne]
  simp only [appCc_add_left]

theorem cc_swap_app
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 2
        (ccSlotSwapField (I := I) (M := M) g) W =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) W := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel, appCc_toSection, ContinuousLinearMap.comp_apply,
    ccSlotSwapField_toSection]
  change Tensor0SSpace.toModel
      (slotSwapFib (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) v =
    (ContinuousMultilinearMap.domDomCongr
      (Equiv.swap (0 : Fin 2) 1)
      (unitModel (I := I) (M := M) g 2 W x)) v
  rw [slotSwapFib_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

theorem symm_input
    (g : SmoothRiemannianMetric I M) (C : SmoothCcTensor g 2 2)
    (W : SmoothCcTensor g 0 2) :
    appCc (I := I) (M := M) g 2 2
        (ccInputSymm (I := I) (M := M) g C) W =
      appCc (I := I) (M := M) g 2 2 C
        (symmS (I := I) (M := M) g W) := by
  rw [ccInputSymm, appCc_smul_left, appCc_add_left, ← appCc_assoc,
    cc_swap_app (I := I) (M := M) g W]
  rw [symmS, appCc_smul_right, appCc_add_right]

noncomputable def ricciOne
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  aaOne (I := I) (M := M) g gm W +
    LowBaseInternal.ricciDAOne (I := I) (M := M) g gm
      (symmS (I := I) (M := M) g W)

theorem ricci_one
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    appCc (I := I) (M := M) g 2 2
        (LowBaseInternal.ricciGoodLow (I := I) (M := M) g gm P) W =
      appCc (I := I) (M := M) g 3 2
        (ricciOne (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [LowBaseInternal.ricciGoodLow, symm_input,
    LowBaseInternal.ricciLow, appCc_add_left]
  rw [aa_one (I := I) (M := M) g gm P W hP htie]
  rw [LowBaseInternal.ricciDA_one (I := I) (M := M) g gm P
    (symmS (I := I) (M := M) g W)]
  rw [ricciOne, appCc_add_left]

theorem self_decomp
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    LowBaseInternal.rhsSelfLow (I := I) (M := M) g g T hδ hδZ s =
      let gm := realizedFam (I := I) g T 0 hδ hδZ s
      ((((-2 : ℝ) •
            LowBaseInternal.ricciGoodLow (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovDerivArmField (I := I) (M := M) g gm g -
            edgeLiePairFam (I := I) (M := M) g T hδ hδZ
              lieRefoldQ lieRefoldEps s)) +
        lc0VB (I := I) (M := M) g gm) +
        lc0AMix (I := I) (M := M) g gm g) +
        lc0Riem (I := I) (M := M) g gm := by
  rw [LowBaseInternal.selfLow_good (I := I) (M := M)
    g g T hT hδ_lt hδ hδZ hs]
  let gm := realizedFam (I := I) g T 0 hδ hδZ s
  let Q := edgeLiePairFam (I := I) (M := M) g T hδ hδZ
    lieRefoldQ lieRefoldEps s
  have hlie :
      deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorr0Field (I := I) (M := M) g gm g - Q =
        (deTurckLieCovDerivArmField (I := I) (M := M) g gm g - Q) +
          lc0VB (I := I) (M := M) g gm +
          lc0AMix (I := I) (M := M) g gm g +
          lc0Riem (I := I) (M := M) g gm := by
    calc
      _ = (deTurckLieCovDerivArmField (I := I) (M := M) g gm g - Q) +
          (lieCorr0Field (I := I) (M := M) g gm g +
            deTurckLieEndoArmField (I := I) (M := M) g gm g) := by
        rw [deTurckLieCoeffField_eq_covDerivArm_add_endoArm]
        abel
      _ = _ := by
        rw [tail_base_split (I := I) (M := M) g gm g]
        simp only [sub_self, zero_add]
        abel
  calc
    _ = (-2 : ℝ) •
          LowBaseInternal.ricciGoodLow (I := I) (M := M) g gm (s • T) +
        (deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorr0Field (I := I) (M := M) g gm g - Q) := by
      simp only [gm, Q]
      abel
    _ = _ := by
      rw [hlie]
      simp only [gm, Q]
      abel

end LowRegBgC0Core
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
