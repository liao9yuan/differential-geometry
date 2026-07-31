import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegSymmPreserve
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegSmoothBridge
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRHSSectionRealizeUnitModel
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ExponentCongr

/-!
# The Ricci–DeTurck smooth remainder is slot-symmetric

The forcing-side symmetry brick of the low-regularity Ricci–DeTurck lane, and
the missing input of `lowreg_sol_symm` (`LowRegSymmPreserve.lean`).

`deTurckSmoothRemainder g₀ g_bg T = deTurckRHSArmG0 g₀ g_bg T − Δ_∇ T` has two
summands with *different* symmetry mechanisms:

* the Ricci–DeTurck arm is symmetric for **every** `T`: its unit-model value is
  the bilinear form `deTurckRicciRHS g_bg (g₀ + T)`, which is symmetric because
  the Ricci tensor and the metric Lie derivative are
  (`deTurckRicciRHS_symm`, in `DeTurckRicciRHSSymmetric.lean`);
* the rough connection Laplacian is only symmetric on symmetric `T`, and there
  the mechanism is slot-swap **equivariance**,
  `rawTensorConnLapSmooth_domDomCongrSection` (`SlotSwapEquivariance.lean`).

So the bridge from the known *bilinear-form* symmetry to the *tensor*-level
statement `symmS g₀ R = R` is exactly: transport the bilinear symmetry through
`unitModel`-extensionality on the arm, and use equivariance on the Laplacian.

Main results:

* `swap_deTurckRHSArm` — the slot swap fixes the Ricci–DeTurck arm, for every
  smooth fibre-small `T`.
* `swap_smoothRem`, `symmS_smoothRem` — the smooth Ricci–DeTurck remainder of a
  slot-symmetric `T` is slot-symmetric, in swap form and in `symmS`-fixed-point
  form.
* `symmS_remSymmS` — the shape the low-regularity nonlinearity uses:
  `symmS g₀ (deTurckSmoothRemainder g₀ g_bg (symmS g₀ T) …) =
   deTurckSmoothRemainder g₀ g_bg (symmS g₀ T) …`.
* `symmHs_smoothN`, `symmHs_coreN`, `symmHs_lowRegN` — the spectral lifts:
  the smooth nonlinearity, the core nonlinearity and its dense extension all
  land in the fixed-point set of `symmHs`.
* `lowreg_force_symm`, `lowreg_sol_symm_rhs` — the `hf` hypothesis of
  `lowreg_sol_symm` discharged for the genuine Ricci–DeTurck forcing.
* `symmHs_congr`, `lowreg_sol_symm_h3` — the same statement transported to the
  literal exponent `(3 : ℝ)` that `lowRadial_eq_self_along_sol` consumes.

Two reusable rank-two bridges fall out on the way: `ccTensor_ext_bilin` (a
smooth `(0, 2)`-tensor is determined by its extracted bilinear form) and
`bilin_ddc_swap` (the slot swap transposes that form).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-! ## Bilinear-form extensionality and the slot swap

A smooth `(0, 2)`-tensor is determined by its extracted bilinear form, and the
slot swap transposes that form.  Together these turn every rank-two slot-swap
identity into a bilinear-form computation. -/

/-- **A smooth `(0, 2)`-tensor is determined by its extracted bilinear form.**
`unitModel`-extensionality (`smoothCcTensor_ext_of_unitModel`) composed with the
`unitModel` ↔ `ccTensorBilin` dictionary. -/
theorem ccTensor_ext_bilin (g : SmoothRiemannianMetric I M)
    {S S' : SmoothCcTensor g 0 2}
    (h : ∀ (x : M) (u w : TangentSpace I x),
      ccTensorBilin (I := I) g S x u w = ccTensorBilin (I := I) g S' x u w) :
    S = S' := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g (fun x => ?_)
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have key : ∀ W : SmoothCcTensor g 0 2,
      unitModel (I := I) (M := M) g 2 W x v =
        ccTensorBilin (I := I) g W x (v 0) (v 1) := by
    intro W
    rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g W x (v 0) (v 1)]
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [key S, key S']
  exact h x (v 0) (v 1)

/-- **The slot swap transposes the extracted bilinear form.** -/
theorem bilin_ddc_swap (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) (b : M) (u w : TangentSpace I b) :
    ccTensorBilin (I := I) g
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) b u w =
      ccTensorBilin (I := I) g T b w u := by
  rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) b u w,
    ← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g T b w u,
    domDomCongrSection_unitModel (I := I) g (Equiv.swap (0 : Fin 2) 1) T b,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  fin_cases k <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- The slot swap of a `(0, 2)`-tensor is an involution. -/
theorem ddc_swap_swap (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) T) = T := by
  refine ccTensor_ext_bilin (I := I) (M := M) g (fun x u w => ?_)
  rw [bilin_ddc_swap (I := I) (M := M) g, bilin_ddc_swap (I := I) (M := M) g]

/-- The slot swap commutes with subtraction of `(0, 2)`-tensors. -/
theorem ddc_swap_sub (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) :
    domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) (A - B) =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) A -
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) B := by
  refine ccTensor_ext_bilin (I := I) (M := M) g (fun x u w => ?_)
  simp only [bilin_ddc_swap (I := I) (M := M) g,
    ccTensorBilin_sub (I := I) (M := M) g]

/-! ## `symmS` as the slot-swap fixed-point projection -/

/-- A swap-invariant smooth `(0, 2)`-tensor is a fixed point of `symmS`. -/
theorem symmS_of_swap (g₀ : SmoothRiemannianMetric I M) {X : SmoothCcTensor g₀ 0 2}
    (h : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) X = X) :
    symmS (I := I) (M := M) g₀ X = X := by
  rw [symmS, h, ← two_smul ℝ X, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

/-- The slot swap fixes every symmetrized tensor. -/
theorem swap_symmS (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (symmS (I := I) (M := M) g₀ T) =
      symmS (I := I) (M := M) g₀ T := by
  refine ccTensor_ext_bilin (I := I) (M := M) g₀ (fun x u w => ?_)
  rw [bilin_ddc_swap (I := I) (M := M) g₀]
  simp only [ccTensorBilin_symmS (I := I) (M := M) g₀]
  exact ccTensorBilinSymm_symm (I := I) g₀ T x w u

/-- **Slot symmetrization is idempotent.** -/
theorem symmS_idem (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    symmS (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ T) =
      symmS (I := I) (M := M) g₀ T :=
  symmS_of_swap (I := I) (M := M) g₀ (swap_symmS (I := I) (M := M) g₀ T)

/-- A `symmS`-fixed smooth `(0, 2)`-tensor is swap-invariant. -/
theorem swap_of_symmS (g₀ : SmoothRiemannianMetric I M) {X : SmoothCcTensor g₀ 0 2}
    (h : symmS (I := I) (M := M) g₀ X = X) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) X = X := by
  conv_lhs => rw [← h]
  rw [swap_symmS (I := I) (M := M) g₀, h]

/-- **A `symmS`-fixed smooth `(0, 2)`-tensor has a symmetric extracted bilinear
form.**  This is the tensor-level ⟹ bilinear-form direction of the dictionary
used throughout the DeTurck layer. -/
theorem bilin_symm_of_symmS (g₀ : SmoothRiemannianMetric I M)
    {X : SmoothCcTensor g₀ 0 2} (h : symmS (I := I) (M := M) g₀ X = X)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ X x v w = ccTensorBilin (I := I) g₀ X x w v := by
  conv_lhs => rw [← h]
  conv_rhs => rw [← h]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ X x v w,
    ccTensorBilin_symmS (I := I) (M := M) g₀ X x w v,
    ccTensorBilinSymm_symm (I := I) g₀ X x v w]

/-! ## The Ricci–DeTurck arm is slot-symmetric -/

/-- **The Ricci–DeTurck right-hand-side arm is slot-symmetric.**

For every smooth fibre-small `T`, the arm
`deTurckRHSArmG0 g₀ g_bg T = deTurckRHSSection g_bg (g₀ + T)` (re-tagged to `g₀`)
is fixed by the slot swap.  This is the tensor-level form of the bilinear
symmetry `deTurckRicciRHS_symm`: the unit-model value of the arm at `x` on a
tangent pair is `deTurckRicciRHS g_bg (g₀ + T) x (v 0) (v 1)`
(`unitModel_of_deTurckRHSSection_realize`), and that bilinear form is symmetric,
so `unitModel`-extensionality upgrades it to a `SmoothCcTensor` identity. -/
theorem swap_deTurckRHSArm (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) =
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) x]
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have h1 := unitModel_of_deTurckRHSSection_realize (I := I) (M := M) g₀ g_bg T
    hδ_lt hδ (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) rfl x
    (fun i => v ((Equiv.swap (0 : Fin 2) 1) i))
  have h2 := unitModel_of_deTurckRHSSection_realize (I := I) (M := M) g₀ g_bg T
    hδ_lt hδ (deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ) rfl x v
  rw [h1, h2]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact deTurckRicciRHS_symm (I := I) g_bg
    (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) x (v 1) (v 0)

/-! ## The smooth Ricci–DeTurck remainder is slot-symmetric -/

private theorem smoothRem_eq_arm_sub (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ =
      deTurckRHSArmG0 (I := I) g₀ g_bg T hδ_lt hδ -
        rawTensorConnLapSmooth (I := I) g₀ 0 2 T :=
  rfl

/-- **The smooth Ricci–DeTurck remainder of a swap-invariant tensor is
swap-invariant.**  The Ricci–DeTurck arm is symmetric unconditionally
(`swap_deTurckRHSArm`); the rough connection Laplacian is slot-swap equivariant
(`rawTensorConnLapSmooth_domDomCongrSection`), so it preserves the symmetry of
`T`. -/
theorem swap_smoothRem (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hT : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T = T) :
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) =
      deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ := by
  rw [smoothRem_eq_arm_sub (I := I) (M := M) g₀ g_bg T hδ_lt hδ,
    ddc_swap_sub (I := I) (M := M) g₀,
    swap_deTurckRHSArm (I := I) (M := M) g₀ g_bg T hδ_lt hδ,
    ← rawTensorConnLapSmooth_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) T,
    hT]

/-- **The smooth Ricci–DeTurck remainder of a slot-symmetric tensor is
slot-symmetric**, in `symmS`-fixed-point form.  This is the smooth-tensor
statement consumed by `symmHs_smoothCc_eq_self`. -/
theorem symmS_smoothRem (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hT : symmS (I := I) (M := M) g₀ T = T) :
    symmS (I := I) (M := M) g₀
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) =
      deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ :=
  symmS_of_swap (I := I) (M := M) g₀
    (swap_smoothRem (I := I) (M := M) g₀ g_bg T hδ_lt hδ
      (swap_of_symmS (I := I) (M := M) g₀ hT))

/-- **The shape the low-regularity nonlinearity uses.**  `coreN` and
`lowRegN` always feed the *symmetrized* representative `symmS g₀ T` to
`deTurckSmoothRemainder`, and `symmS` is idempotent, so the remainder is
slot-symmetric with no hypothesis on `T`. -/
theorem symmS_remSymmS (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T)) δ) :
    symmS (I := I) (M := M) g₀
        (deTurckSmoothRemainder (I := I) g₀ g_bg
          (symmS (I := I) (M := M) g₀ T) hδ_lt hδ) =
      deTurckSmoothRemainder (I := I) g₀ g_bg
        (symmS (I := I) (M := M) g₀ T) hδ_lt hδ :=
  symmS_smoothRem (I := I) (M := M) g₀ g_bg _ hδ_lt hδ
    (symmS_idem (I := I) (M := M) g₀ T)

/-- **The extracted bilinear form of the smooth Ricci–DeTurck remainder of a
slot-symmetric tensor is symmetric.** -/
theorem bilin_smoothRem_symm (g₀ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hT : symmS (I := I) (M := M) g₀ T = T)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) x v w =
      ccTensorBilin (I := I) g₀
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) x w v :=
  bilin_symm_of_symmS (I := I) (M := M) g₀
    (symmS_smoothRem (I := I) (M := M) g₀ g_bg T hδ_lt hδ hT) x v w

/-! ## The spectral lift -/

/-- The smooth Ricci–DeTurck nonlinearity is the spectral embedding of the
smooth Ricci–DeTurck remainder. -/
theorem smoothN_eq_embed (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) := by
  ext i
  rfl

/-- **The smooth Ricci–DeTurck nonlinearity of a slot-symmetric tensor is
spectrally symmetric.** -/
theorem symmHs_smoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (hσ : (0 : ℝ) ≤ (a : ℝ)) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hT : symmS (I := I) (M := M) g₀ T = T) :
    symmHs (I := I) (M := M) g₀ hσ
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ := by
  rw [smoothN_eq_embed (I := I) (M := M) g₀ g_bg a T hδ_lt hδ]
  exact symmHs_smoothCc_eq_self (I := I) (M := M) g₀ hσ _
    (symmS_smoothRem (I := I) (M := M) g₀ g_bg T hδ_lt hδ hT)

/-- **The genuine core Ricci–DeTurck nonlinearity is spectrally symmetric.** -/
theorem symmHs_coreN (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hσ : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    (x : smoothCore (I := I) (M := M) g₀ R) :
    symmHs (I := I) (M := M) g₀ hσ
        (coreN (I := I) (M := M) g₀ g_bg hδ hreal x) =
      coreN (I := I) (M := M) g₀ g_bg hδ hreal x :=
  symmHs_smoothN (I := I) (M := M) g₀ g_bg 1 hσ
    (symmS (I := I) (M := M) g₀ (coreRep g₀ x)) hδ
    (hreal _ (coreSymm_h2 (I := I) (M := M) g₀ x))
    (symmS_idem (I := I) (M := M) g₀ (coreRep g₀ x))

/-- **The genuine low-regularity Ricci–DeTurck nonlinearity is spectrally
symmetric.**  Spectral symmetry holds on the dense smooth core
(`symmHs_coreN` together with `lowRegN_on_core`), the symmetric states are
closed (`isClosed_symmFixed`), and `lowRegN` is continuous, so symmetry
propagates to the whole lower-state ball. -/
theorem symmHs_lowRegN (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcont : Continuous (lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal))
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (hσ : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    (u : lowerState (I := I) (M := M) g₀ 1 R) :
    symmHs (I := I) (M := M) g₀ hσ
        (lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal u) =
      lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal u := by
  set C : Set (lowerState (I := I) (M := M) g₀ 1 R) :=
    {w | symmHs (I := I) (M := M) g₀ hσ
        (lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal w) =
      lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal w} with hC_def
  have hclosed : IsClosed C :=
    isClosed_eq ((symmHs (I := I) (M := M) g₀ hσ).continuous.comp hcont) hcont
  have hsub : smoothCore (I := I) (M := M) g₀ R ⊆ C := by
    intro w hw
    have hx := lowRegN_on_core (I := I) (M := M) g₀ g_bg hR hδ hreal hcore ⟨w, hw⟩
    change symmHs (I := I) (M := M) g₀ hσ
        (lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal w) =
      lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal w
    rw [hx]
    exact symmHs_coreN (I := I) (M := M) g₀ g_bg hδ hreal hσ ⟨w, hw⟩
  have hCuniv : C = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← (smoothCore_dense (I := I) (M := M) g₀ hR).closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  have hu : u ∈ C := by rw [hCuniv]; trivial
  exact hu

/-! ## The symmetry input of `lowreg_sol_symm`, discharged -/

/-- **The genuine Ricci–DeTurck forcing is spectrally symmetric almost
everywhere.**  This is the `hf` hypothesis of `lowreg_sol_symm`, discharged for
the concrete forcing `lowRegN ∘ (state path)` produced by
`lowreg_partial_sol`. -/
theorem lowreg_force_symm (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcont : Continuous (lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal))
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (hσ : (0 : ℝ) ≤ ((1 : ℕ) : ℝ))
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal (u t)) :
    ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g₀ hσ (gforce t) = gforce t := by
  filter_upwards [hforce] with t ht
  rw [ht]
  exact symmHs_lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal hcont hcore hσ (u t)

/-- **The rough low-regularity Ricci–DeTurck solution field is spectrally
symmetric almost everywhere.**  `lowreg_sol_symm` with its forcing-symmetry
hypothesis discharged: the only remaining inputs are the two continuity facts
exported by `lowreg_partial_sol` and the identification of the forcing with the
genuine nonlinearity along the state path. -/
theorem lowreg_sol_symm_rhs (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcont : Continuous (lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal))
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (ha : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)) (h2 : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal (u t)) :
    ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g₀ h2
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce t) =
        maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
          (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce t :=
  lowreg_sol_symm (I := I) (M := M) g₀ ha h2 hT hT1 gforce
    (lowreg_force_symm (I := I) (M := M) g₀ g_bg hR hδ hreal hcont hcore ha u
      gforce hforce)

/-! ## Exponent normalization

`lowRadial_eq_self_along_sol` states its symmetry input at the *literal*
exponent `(3 : ℝ)`, while the solver's field lives at `((1 : ℕ) : ℝ) + 2`.  The
two are equal but not definitionally equal, so an explicit transport
(`tensorHsCongr`) is needed; spectral symmetrization is natural for it. -/

/-- **Spectral symmetrization is natural for the exponent transport.**  Both
sides reduce to the same term once the exponent equality is destructed:
`tensorHsCongr` becomes the identity and the two nonnegativity proofs are
propositionally irrelevant. -/
theorem symmHs_congr (g : SmoothRiemannianMetric I M) {a b : ℝ} (hab : a = b)
    (ha : (0 : ℝ) ≤ a) (hb : (0 : ℝ) ≤ b)
    (u : tensorHs (I := I) (M := M) g 0 2 a) :
    symmHs (I := I) (M := M) g hb
        (tensorHsCongr (I := I) (M := M) g 0 2 hab u) =
      tensorHsCongr (I := I) (M := M) g 0 2 hab
        (symmHs (I := I) (M := M) g ha u) := by
  cases hab
  rfl

/-- **The rough low-regularity solution field is spectrally symmetric at the
literal exponent `3`.**  This is exactly the `hsymm` input of
`lowRadial_eq_self_along_sol`, for the transported solver path
`t ↦ tensorHsCongr g₀ 0 2 h₃ (maxRegDuhamelSolField … t)`. -/
theorem lowreg_sol_symm_h3 (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcont : Continuous (lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal))
    (hcore : Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hreal))
    (ha : (0 : ℝ) ≤ ((1 : ℕ) : ℝ)) (h2 : (0 : ℝ) ≤ ((1 : ℕ) : ℝ) + 2)
    (h3 : (0 : ℝ) ≤ (3 : ℝ)) (hex : ((1 : ℕ) : ℝ) + 2 = (3 : ℝ))
    (hT : 0 < T) (hT1 : T ≤ 1)
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      fun t => lowRegN (I := I) (M := M) g₀ g_bg hR hδ hreal (u t)) :
    ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g₀ h3
          (tensorHsCongr (I := I) (M := M) g₀ 0 2 hex
            (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              gforce t)) =
        tensorHsCongr (I := I) (M := M) g₀ 0 2 hex
          (maxRegDuhamelSolField (I := I) (M := M) ((1 : ℕ) : ℝ) hT hT1
            (0 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            gforce t) := by
  filter_upwards [lowreg_sol_symm_rhs (I := I) (M := M) g₀ g_bg hR hδ hreal
    hcont hcore ha h2 hT hT1 u gforce hforce] with t ht
  rw [symmHs_congr (I := I) (M := M) g₀ hex h2 h3, ht]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
