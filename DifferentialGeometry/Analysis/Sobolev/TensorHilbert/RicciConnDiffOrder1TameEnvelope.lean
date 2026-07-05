import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmOrder1KoszulTameEnvelope

/-!
# Per-order L² tame envelopes for the order-one connection-difference coefficient

The four-trace `appCcRS` refold of the order-one connection-difference Ricci-linearization
coefficient field: `linearizedRicciConnDiffOrder1CoeffField g₀ g₁` factors as the four-trace
cometric cast field (rank `(4,2)`) applied against the order-one connection-difference Leibniz
kernel field (rank `(3,4)`), mirroring `ricciArmOrder1KoszulCoeff_eq_appCcRS`. On top of the
refold, the generic ball-uniform order-0 sup bounds and all-order per-order L² tame jet
envelopes for the two arms feed the diagonal-product-grid calculus exactly as in
`ricciArmOrder1KoszulCoeff_perOrder_l2_tameEnvelope_generic`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- Smoothness of the four-trace cometric fiber family `x ↦ ricciCometricFourTraceCLM g₁ x`
viewed as a rank-`(4,2)` tensor section. -/
theorem ricciCometricFourTraceCastG0Fib_contMDiff (g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) x
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from
          ricciCometricFourTraceCLM (I := I) g₁ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
    (φ := fun x : M => ricciCometricFourTraceCLM (I := I) g₁ x)
  intro Y
  have hCK := ricciCometricFourTraceCLM_field_contMDiff (I := I) g₁ (fun x => Y x) Y.contMDiff
  refine hCK.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) x t) rfl

set_option linter.unusedSectionVars false in
/-- Smoothness of the order-one connection-difference Leibniz kernel fiber family
`x ↦ linearizedRicciConnDiffOrder1CLM x (A x)`, `A = connDiffSection g₁ g₀`, viewed as a
rank-`(3,4)` tensor section. -/
theorem linearizedRicciConnDiffOrder1KernelFib_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 4 I z) x
        (show Tensor0SBundle.TensorRSSpace 3 4 I x from
          linearizedRicciConnDiffOrder1CLM (I := I) x
            ((connDiffSection (I := I) g₁ g₀).toSection x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z)
    (φ := fun x : M => linearizedRicciConnDiffOrder1CLM (I := I) x
      ((connDiffSection (I := I) g₁ g₀).toSection x))
  intro Y
  have hE1 := linearizedRicciConnDiffOrder1CLM_field_contMDiff (I := I) g₀ g₁
    (fun x => Y x) Y.contMDiff
  refine hE1.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x t) rfl

/-- The four-trace cometric cast field: the fiber family `ricciCometricFourTraceCLM g₁` of the
perturbed metric `g₁`, cast as a rank-`(4,2)` smooth compactly supported tensor over the base
metric `g₀`. The `p = 2` four-trace analogue of `cometricCastG0`. -/
def ricciCometricFourTraceCastG0 (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 4 2 I x from
          ricciCometricFourTraceCLM (I := I) g₁ x)
      contMDiff_toFun := ricciCometricFourTraceCastG0Fib_contMDiff (I := I) g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

/-- The order-one connection-difference Leibniz kernel field: the fiber family
`x ↦ linearizedRicciConnDiffOrder1CLM x (A x)` with `A = connDiffSection g₁ g₀`, as a
rank-`(3,4)` smooth compactly supported tensor over `g₀`. -/
def linearizedRicciConnDiffOrder1KernelField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 4 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 4 I x from
          linearizedRicciConnDiffOrder1CLM (I := I) x
            ((connDiffSection (I := I) g₁ g₀).toSection x))
      contMDiff_toFun := linearizedRicciConnDiffOrder1KernelFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem ricciCometricFourTraceCastG0_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciCometricFourTraceCastG0 (I := I) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 4 2 I x from
        ricciCometricFourTraceCLM (I := I) g₁ x) := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem linearizedRicciConnDiffOrder1KernelField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 4 I x from
        linearizedRicciConnDiffOrder1CLM (I := I) x
          ((connDiffSection (I := I) g₁ g₀).toSection x)) := rfl

set_option linter.unusedSectionVars false in
/-- The four-trace `appCcRS` refold: the order-one connection-difference coefficient field is
the composition of the four-trace cometric cast field against the order-one Leibniz kernel
field, mirroring `ricciArmOrder1KoszulCoeff_eq_appCcRS`. -/
theorem linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀ g₁ =
      appCcRS (I := I) (M := M) g₀ 3 4 2
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
        (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private def fourTraceArgPerm0231 : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 3, 1], ![0, 3, 1, 2], by decide, by decide⟩

private def fourTraceArgPerm0321 : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 2, 1], ![0, 3, 2, 1], by decide, by decide⟩

private def fourTraceArgPerm2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

set_option linter.unusedSectionVars false in
private theorem ricciCometricFourTraceCastG0_eq_reindex_combination
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciCometricFourTraceCastG0 (I := I) g₀ g₁ =
      ((1 : ℝ) / 2) •
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2
            (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) fourTraceArgPerm0231
          + reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) fourTraceArgPerm0321
          - ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁
          - reindexCoeffGen (I := I) (M := M) g₀ 4 2
              (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁) fourTraceArgPerm2301) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  rfl

set_option linter.unusedSectionVars false in
private lemma ricciArmPrincipalCoeffPure_sub_doubleTrace_clm
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁
          - cometricDoubleTraceField (I := I) g₀ 2).toSection x) =
      cometricDoubleTraceFib (I := I) g₁ 2 x - cometricDoubleTraceFib (I := I) g₀ 2 x := by
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  have hcast : (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁).toSection x
      = (cometricDoubleTraceField (I := I) g₁ 2).toSection x := rfl
  rw [hcast, cometricDoubleTraceField_toSection, cometricDoubleTraceField_toSection]

set_option linter.unusedSectionVars false in
/-- The `p = 2` cometric cast decomposition: the pure `g₁` double-trace coefficient over the
`g₀` base splits as the `g₀` background double-trace plus the slot-insert
`gInvDiffRaisedEndoField` correction, mirroring `cometricCastG0_eq_doubleTrace_add_appCcRS`. -/
theorem ricciArmPrincipalCoeffPure_eq_doubleTrace_add_appCcRS
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁ =
      cometricDoubleTraceField (I := I) g₀ 2 +
        appCcRS (I := I) (M := M) g₀ 4 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  classical
  have hsub : ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁
      - cometricDoubleTraceField (I := I) g₀ 2 =
      appCcRS (I := I) (M := M) g₀ 4 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    refine tensorRSSpace_ext 4 2 x (fun w => ?_)
    apply Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun m => ?_)
    beta_reduce
    rw [ricciArmPrincipalCoeffPure_sub_doubleTrace_clm (I := I) g₀ g₁ x,
      cometricDoubleTraceFib_sub_toModel_eq (I := I) g₀ g₁ 2 x w m,
      appCcRS_toSection, ContinuousLinearMap.comp_apply,
      cometricDoubleTraceField_toSection, cometricDoubleTraceFib_toModel,
      modelDoubleTrace_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval, Fin.cons_zero,
      Fin.update_cons_zero]
    rfl
  rw [← hsub]; abel

set_option linter.unusedSectionVars false in
private lemma fourTrace_iteratedCovGrad_smul (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

set_option linter.unusedSectionVars false in
private lemma fourTrace_rfns_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedVariables false in
/-- Ball-uniform order-0 sup bound and all-order per-order L² tame jet envelope for the
four-trace cometric cast field, generic in a perturbed metric `g₁ = g₀ + P`: the four-trace
combination collapses onto argument-slot reindexings of the pure `g₁` double-trace
coefficient, which splits as the `g₀` background double-trace plus the slot-insert
`gInvDiffRaisedEndoField` correction whose jets are tamed by the antidiagonal grid engine. -/
theorem ricciCometricFourTraceCastG0_order0sup_perOrder_l2_tameEnvelope_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ q, 0 ≤ K q) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((ricciCometricFourTraceCastG0 (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (q : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 4 2 q
              (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
            K q * (1 + ∑ j ∈ Finset.range (q + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  set Φ : SmoothCcTensor g₀ 4 2 := cometricDoubleTraceField (I := I) g₀ 2 with hΦ_def
  obtain ⟨C_base, hC_base_nn, hC_base⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K_t, hK_t_nn, hK_t⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  have hSΦ_ex : ∀ i : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 4 2 i Φ).toSection x) ≤ K :=
    fun i => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 (2 + i)
      (iteratedCovGrad (I := I) g₀ 4 2 i Φ)
  choose SΦ hSΦ_nn hSΦ using hSΦ_ex
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : (0 : ℝ) ≤ fr := by rw [hfr_def]; exact Nat.cast_nonneg _
  have hfr3_nn : (0 : ℝ) ≤ fr ^ 3 := pow_nonneg hfr_nn 3
  set KW : ℕ → ℝ := fun q => fr ^ 3 * C_base q * K_t q with hKW_def
  have hKW_nn : ∀ q, 0 ≤ KW q := by
    intro q
    simp only [hKW_def]
    exact mul_nonneg (mul_nonneg hfr3_nn (hC_base_nn q)) (hK_t_nn q)
  set KD : ℕ → ℝ := fun l => appCcGdiag (E := E) l *
    (∑ i' ∈ Finset.range (l + 1), SΦ i') * (∑ q ∈ Finset.range (l + 1), KW q) with hKD_def
  have hKD_nn : ∀ l, 0 ≤ KD l := by
    intro l
    simp only [hKD_def]
    exact mul_nonneg (mul_nonneg (appCcGdiag_nonneg _)
      (Finset.sum_nonneg (fun i' _ => hSΦ_nn i'))) (Finset.sum_nonneg (fun q _ => hKW_nn q))
  set aL : ℕ → ℝ := fun l => ‖iteratedCovGrad (I := I) g₀ 4 2 l Φ‖ ^ 2 with haL_def
  have haL_nn : ∀ l, 0 ≤ aL l := by
    intro l; simp only [haL_def]; positivity
  set ΛT2 : ℝ := fr ^ 3 * C_base 0 with hΛT2_def
  have hΛT2_nn : 0 ≤ ΛT2 := by
    simp only [hΛT2_def]; exact mul_nonneg hfr3_nn (hC_base_nn 0)
  set Spure : ℝ := 2 * SΦ 0 + 2 * (SΦ 0 * ΛT2) with hSpure_def
  have hSpure_nn : 0 ≤ Spure := by
    simp only [hSpure_def]
    have h1 := hSΦ_nn 0
    have h2 : 0 ≤ SΦ 0 * ΛT2 := mul_nonneg (hSΦ_nn 0) hΛT2_nn
    linarith
  have h22nn : (0 : ℝ) ≤ 22 * Spure := by linarith
  refine ⟨Real.sqrt (22 * Spure), fun q => 4 * (2 * aL q + 2 * KD q),
    Real.sqrt_nonneg _, fun q => by linarith [haL_nn q, hKD_nn q], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball
  have hwin1_nn : ∀ q : ℕ, 0 ≤ ∑ j ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    fun q => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hwin2_nn : ∀ q : ℕ, 0 ≤ ∑ j ∈ Finset.range (q + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    fun q => Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hwmono : ∀ q : ℕ, (∑ j ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
      ∑ j ∈ Finset.range (q + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    fun q => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun j _ _ => sq_nonneg _)
  set pureF : SmoothCcTensor g₀ 4 2 :=
    ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁ with hpureF_def
  set R1 : SmoothCcTensor g₀ 4 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF fourTraceArgPerm0231 with hR1_def
  set R2 : SmoothCcTensor g₀ 4 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF fourTraceArgPerm0321 with hR2_def
  set R3 : SmoothCcTensor g₀ 4 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF fourTraceArgPerm2301 with hR3_def
  have hcomb : ricciCometricFourTraceCastG0 (I := I) g₀ g₁ =
      ((1 : ℝ) / 2) • (R1 + R2 - pureF - R3) := by
    have h := ricciCometricFourTraceCastG0_eq_reindex_combination (I := I) g₀ g₁
    rw [← hpureF_def, ← hR1_def, ← hR2_def, ← hR3_def] at h
    exact h
  have hR1n : ∀ q : ℕ, ‖iteratedCovGrad (I := I) g₀ 4 2 q R1‖ =
      ‖iteratedCovGrad (I := I) g₀ 4 2 q pureF‖ := by
    intro q
    rw [hR1_def, iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF
      fourTraceArgPerm0231 q]
    exact norm_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 (2 + q)
      (iteratedCovGrad (I := I) g₀ 4 2 q pureF) fourTraceArgPerm0231
  have hR2n : ∀ q : ℕ, ‖iteratedCovGrad (I := I) g₀ 4 2 q R2‖ =
      ‖iteratedCovGrad (I := I) g₀ 4 2 q pureF‖ := by
    intro q
    rw [hR2_def, iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF
      fourTraceArgPerm0321 q]
    exact norm_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 (2 + q)
      (iteratedCovGrad (I := I) g₀ 4 2 q pureF) fourTraceArgPerm0321
  have hR3n : ∀ q : ℕ, ‖iteratedCovGrad (I := I) g₀ 4 2 q R3‖ =
      ‖iteratedCovGrad (I := I) g₀ 4 2 q pureF‖ := by
    intro q
    rw [hR3_def, iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF
      fourTraceArgPerm2301 q]
    exact norm_reindexCoeffGen_eq (I := I) (M := M) g₀ 4 (2 + q)
      (iteratedCovGrad (I := I) g₀ 4 2 q pureF) fourTraceArgPerm2301
  have hcast_norm : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 4 2 q (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ≤
        2 * ‖iteratedCovGrad (I := I) g₀ 4 2 q pureF‖ := by
    intro q
    rw [hcomb, fourTrace_iteratedCovGrad_smul (I := I) g₀ 4 2 q,
      iteratedCovGrad_sub, iteratedCovGrad_sub, iteratedCovGrad_add,
      norm_smul, Real.norm_eq_abs, show |(1 : ℝ) / 2| = 1 / 2 from by norm_num]
    have ha := norm_add_le (iteratedCovGrad (I := I) g₀ 4 2 q R1)
      (iteratedCovGrad (I := I) g₀ 4 2 q R2)
    have hb := norm_sub_le (iteratedCovGrad (I := I) g₀ 4 2 q R1
      + iteratedCovGrad (I := I) g₀ 4 2 q R2) (iteratedCovGrad (I := I) g₀ 4 2 q pureF)
    have hc := norm_sub_le (iteratedCovGrad (I := I) g₀ 4 2 q R1
      + iteratedCovGrad (I := I) g₀ 4 2 q R2 - iteratedCovGrad (I := I) g₀ 4 2 q pureF)
      (iteratedCovGrad (I := I) g₀ 4 2 q R3)
    rw [hR1n q, hR2n q] at ha
    rw [hR3n q] at hc
    linarith [ha, hb, hc, norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 q pureF)]
  by_cases hMne : Nonempty M
  · obtain ⟨x₀⟩ := hMne
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr' : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr'
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    set W : SmoothCcTensor g₀ 4 4 :=
      slotInsertEndoCc (I := I) (M := M) g₀ 3 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
      with hW_def
    have hid : pureF = Φ + appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W := by
      have h := ricciArmPrincipalCoeffPure_eq_doubleTrace_add_appCcRS (I := I) g₀ g₁
      rw [← hpureF_def, ← hΦ_def, ← hW_def] at h
      exact h
    have hΛT : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 4 x (W.toSection x) ≤ ΛT2 := by
      intro x
      have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 3
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) 0 x
      simp only [iteratedCovGrad_zero] at h1
      rw [← hW_def, ← hfr_def] at h1
      have h2 := hC_base g₁ P htie hδ_le hδ0 hδ 0 x
      simp only [iteratedCovGrad_zero] at h2
      have hgrid0 : (∑ n ∈ Finset.range (0 + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n 0,
          ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = 1 := by
        simp
      rw [hgrid0, mul_one] at h2
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 4 x (W.toSection x)
          ≤ fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
              ((slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁)).toSection x) := h1
        _ ≤ fr ^ 3 * C_base 0 := mul_le_mul_of_nonneg_left h2 hfr3_nn
        _ = ΛT2 := hΛT2_def.symm
    have hstep2 : ∀ q : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 4 4 q W‖ ^ 2 ≤
          KW q * (1 + ∑ j ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      intro q
      obtain ⟨hgi, hgb⟩ := hK_t P hPball q
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) x
              ((iteratedCovGrad (I := I) g₀ 4 4 q W).toSection x) ≤
            fr ^ 3 * C_base q *
              (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
        intro x
        have h1 := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) g₀ 3
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) q x
        rw [← hW_def, ← hfr_def] at h1
        have h2 := hC_base g₁ P htie hδ_le hδ0 hδ q x
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) x
              ((iteratedCovGrad (I := I) g₀ 4 4 q W).toSection x)
            ≤ fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + q) x
                ((iteratedCovGrad (I := I) g₀ 1 1 q
                  (slotInsertEndoCc (I := I) (M := M) g₀ 0
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := h1
          _ ≤ fr ^ 3 * (C_base q *
                (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                  ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))) :=
              mul_le_mul_of_nonneg_left h2 hfr3_nn
          _ = fr ^ 3 * C_base q *
                (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                  ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by ring
      have hint : MeasureTheory.Integrable
          (fun x => fr ^ 3 * C_base q *
            (∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
              ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hgi.const_mul _
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (4 + q)
        (iteratedCovGrad (I := I) g₀ 4 4 q W) _ hint hpt
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul]
      calc fr ^ 3 * C_base q *
              (∫ x, ∑ n ∈ Finset.range (q + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n q,
                ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
          ≤ fr ^ 3 * C_base q * (K_t q * (1 + ∑ j ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hgb (mul_nonneg hfr3_nn (hC_base_nn q))
        _ = KW q * (1 + ∑ j ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
            simp only [hKW_def]; ring
    have hstep3 : ∀ l : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 4 2 l (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W)‖ ^ 2 ≤
          KD l * (1 + ∑ j ∈ Finset.range (l + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      intro l
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 4 2 l
                (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W)).toSection x) ≤
            (appCcGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              (∑ q ∈ Finset.range (l + 1),
                riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) x
                  ((iteratedCovGrad (I := I) g₀ 4 4 q W).toSection x)) := by
        intro x
        refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
          (I := I) (M := M) g₀ l 4 4 2 Φ W x) ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg _)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun i' _ => ?_)
        refine mul_le_mul (hSΦ i' x) ?_
          (Finset.sum_nonneg (fun q _ => riemannianFiberNormSq_nonneg _ _ _ _ _)) (hSΦ_nn i')
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun q _ _ => riemannianFiberNormSq_nonneg _ _ _ _ _)
        intro q hq
        rw [Finset.mem_range] at hq ⊢
        omega
      have hint : MeasureTheory.Integrable
          (fun x => (appCcGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
            (∑ q ∈ Finset.range (l + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) x
                ((iteratedCovGrad (I := I) g₀ 4 4 q W).toSection x)))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        apply MeasureTheory.Integrable.const_mul
        apply MeasureTheory.integrable_finset_sum
        intro q _
        exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 4 (4 + q)
          (iteratedCovGrad (I := I) g₀ 4 4 q W)
      have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + l)
        (iteratedCovGrad (I := I) g₀ 4 2 l (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W)) _ hint hpt
      refine le_trans hkey ?_
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_finset_sum _ (fun q _ =>
          integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 4 (4 + q)
            (iteratedCovGrad (I := I) g₀ 4 4 q W))]
      have hconv : ∀ q ∈ Finset.range (l + 1),
          (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + q) x
              ((iteratedCovGrad (I := I) g₀ 4 4 q W).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 4 4 q W‖ ^ 2 := by
        intro q _
        rw [SmoothCcTensor.norm_def,
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 4 (4 + q)
            (iteratedCovGrad (I := I) g₀ 4 4 q W)]
      rw [Finset.sum_congr rfl hconv]
      have hWsum : ∑ q ∈ Finset.range (l + 1), ‖iteratedCovGrad (I := I) g₀ 4 4 q W‖ ^ 2 ≤
          (∑ q ∈ Finset.range (l + 1), KW q) *
            (1 + ∑ j ∈ Finset.range (l + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum (fun q hq => ?_)
        refine le_trans (hstep2 q) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKW_nn q)
        have hsub : ∑ j ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
            ∑ j ∈ Finset.range (l + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
          rw [Finset.mem_range] at hq
          omega
        linarith
      calc (appCcGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              (∑ q ∈ Finset.range (l + 1), ‖iteratedCovGrad (I := I) g₀ 4 4 q W‖ ^ 2)
          ≤ (appCcGdiag (E := E) l * (∑ i' ∈ Finset.range (l + 1), SΦ i')) *
              ((∑ q ∈ Finset.range (l + 1), KW q) *
                (1 + ∑ j ∈ Finset.range (l + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hWsum
              (mul_nonneg (appCcGdiag_nonneg _) (Finset.sum_nonneg (fun i' _ => hSΦ_nn i')))
        _ = KD l * (1 + ∑ j ∈ Finset.range (l + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
            simp only [hKD_def]; ring
    have hpure_tame : ∀ l : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 4 2 l pureF‖ ^ 2 ≤
          (2 * aL l + 2 * KD l) * (1 + ∑ j ∈ Finset.range (l + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      intro l
      rw [hid, iteratedCovGrad_add (I := I) g₀ 4 2 l Φ (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W)]
      have haLl : ‖iteratedCovGrad (I := I) g₀ 4 2 l Φ‖ ^ 2 ≤
          aL l * (1 + ∑ j ∈ Finset.range (l + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        have h1 : aL l = ‖iteratedCovGrad (I := I) g₀ 4 2 l Φ‖ ^ 2 := by simp only [haL_def]
        nlinarith [haL_nn l, hwin1_nn l]
      have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 l Φ +
          iteratedCovGrad (I := I) g₀ 4 2 l (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W)))
        (norm_add_le (iteratedCovGrad (I := I) g₀ 4 2 l Φ)
          (iteratedCovGrad (I := I) g₀ 4 2 l (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W))) 2
      nlinarith [hsq, hstep3 l, haLl,
        sq_nonneg (‖iteratedCovGrad (I := I) g₀ 4 2 l Φ‖ -
          ‖iteratedCovGrad (I := I) g₀ 4 2 l (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W)‖)]
    refine ⟨?_, ?_⟩
    · intro x
      rw [Real.sq_sqrt h22nn]
      have hpure0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          (pureF.toSection x) ≤ Spure := by
        have hxid : pureF.toSection x = Φ.toSection x
            + (appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W).toSection x := by
          rw [hid, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
        rw [hxid]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 2 x
          (Φ.toSection x) ((appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W).toSection x)) ?_
        have hΦ0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Φ.toSection x) ≤ SΦ 0 := by
          have h := hSΦ 0 x
          simp only [iteratedCovGrad_zero] at h
          exact h
        have hD0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((appCcRS (I := I) (M := M) g₀ 4 4 2 Φ W).toSection x) ≤ SΦ 0 * ΛT2 := by
          refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 4 4 2 x
            (Φ.toSection x) (W.toSection x)) ?_
          exact mul_le_mul hΦ0 (hΛT x) (riemannianFiberNormSq_nonneg _ _ _ _ _) (hSΦ_nn 0)
        simp only [hSpure_def]
        linarith
      have hxcomb : (ricciCometricFourTraceCastG0 (I := I) g₀ g₁).toSection x =
          ((1 : ℝ) / 2) • (R1.toSection x + R2.toSection x
            - pureF.toSection x - R3.toSection x) := by
        rw [hcomb, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
          SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
          SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
          SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
      rw [hxcomb, fourTrace_rfns_smul (I := I) (M := M) g₀ 4 2 x,
        show ((1 : ℝ) / 2) ^ 2 = 1 / 4 from by norm_num]
      have hR1x : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R1.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (pureF.toSection x) := by
        rw [hR1_def, reindexCoeffGen_toSection]
        exact riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ 4 2 x
          fourTraceArgPerm0231 (pureF.toSection x)
      have hR2x : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R2.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (pureF.toSection x) := by
        rw [hR2_def, reindexCoeffGen_toSection]
        exact riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ 4 2 x
          fourTraceArgPerm0321 (pureF.toSection x)
      have hR3x : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R3.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (pureF.toSection x) := by
        rw [hR3_def, reindexCoeffGen_toSection]
        exact riemannianFiberNormSq_reindexCoeffFibGen (I := I) (M := M) g₀ 4 2 x
          fourTraceArgPerm2301 (pureF.toSection x)
      have hA := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 4 2 x
        (R1.toSection x) (R2.toSection x)
      have hB := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 4 2 x
        (R1.toSection x + R2.toSection x) (pureF.toSection x)
      have hC := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 4 2 x
        (R1.toSection x + R2.toSection x - pureF.toSection x) (R3.toSection x)
      have hp_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 2 x (pureF.toSection x)
      rw [hR1x, hR2x] at hA
      rw [hR3x] at hC
      linarith [hA, hB, hC, hpure0, hSpure_nn, hp_nn]
    · intro q
      have hc := hcast_norm q
      have hp := hpure_tame q
      have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 4 2 q
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁))) hc 2
      have h4 : (2 * ‖iteratedCovGrad (I := I) g₀ 4 2 q pureF‖) ^ 2 =
          4 * ‖iteratedCovGrad (I := I) g₀ 4 2 q pureF‖ ^ 2 := by ring
      have hKq_nn : 0 ≤ 2 * aL q + 2 * KD q := by linarith [haL_nn q, hKD_nn q]
      have hmono : (1 + ∑ j ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
          1 + ∑ j ∈ Finset.range (q + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        linarith [hwmono q]
      calc ‖iteratedCovGrad (I := I) g₀ 4 2 q
              (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2
          ≤ 4 * ‖iteratedCovGrad (I := I) g₀ 4 2 q pureF‖ ^ 2 := by rw [← h4]; exact hsq
        _ ≤ 4 * ((2 * aL q + 2 * KD q) * (1 + ∑ j ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by linarith [hp]
        _ ≤ 4 * ((2 * aL q + 2 * KD q) * (1 + ∑ j ∈ Finset.range (q + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
            have := mul_le_mul_of_nonneg_left hmono hKq_nn
            linarith
        _ = 4 * (2 * aL q + 2 * KD q) * (1 + ∑ j ∈ Finset.range (q + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
  · haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
    refine ⟨fun x => (hem.false x).elim, ?_⟩
    intro q
    have hz : ‖iteratedCovGrad (I := I) g₀ 4 2 q
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    have hKq_nn : 0 ≤ 4 * (2 * aL q + 2 * KD q) := by linarith [haL_nn q, hKD_nn q]
    have hprod : 0 ≤ 4 * (2 * aL q + 2 * KD q) * (1 + ∑ j ∈ Finset.range (q + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
      mul_nonneg hKq_nn (by linarith [hwin2_nn q])
    calc ‖iteratedCovGrad (I := I) g₀ 4 2 q
            (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2
        = 0 := by rw [hz]; norm_num
      _ ≤ 4 * (2 * aL q + 2 * KD q) * (1 + ∑ j ∈ Finset.range (q + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := hprod

private def kOutPerm0312 : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩

private def kOutPerm0213 : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩

private def kOutPerm2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def kOutPerm1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def kOutPerm1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def kInPerm102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def kInPerm120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem slotPermCcFib_contMDiff (g₀ : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel d d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel d d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace d d I z) x
        (show Tensor0SBundle.TensorRSSpace d d I x from slotPermCLM (I := I) ρ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (φ := fun x : M => slotPermCLM (I := I) ρ x)
  intro Y
  have h := slotPermCLM_field_contMDiff (I := I) ρ (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) rfl

private def slotPermCc (g₀ : SmoothRiemannianMetric I M) {d : ℕ} (ρ : Equiv.Perm (Fin d)) :
    SmoothCcTensor g₀ d d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace d d I x from slotPermCLM (I := I) ρ x)
      contMDiff_toFun := slotPermCcFib_contMDiff (I := I) (M := M) g₀ ρ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
private theorem connDiffContrInsertionFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 3 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 3 4 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 3 4 I z) x
        (show Tensor0SBundle.TensorRSSpace 3 4 I x from
          connContrCLM (I := I) 2 1 x ((connDiffSection (I := I) g₁ g₀).toSection x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel 3 ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 3 I z)
    (F₂ := Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z)
    (φ := fun x : M => connContrCLM (I := I) 2 1 x
      ((connDiffSection (I := I) g₁ g₀).toSection x))
  intro Y
  have h := connContrCLM_field_contMDiff (I := I) 2 1
    (fun x => (connDiffSection (I := I) g₁ g₀).toSection x)
    (connDiffSection (I := I) g₁ g₀).toSection.contMDiff
    (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace 4 I z) x t) rfl

/-- The connection-contraction insertion core field: the fiber family
`x ↦ connContrCLM 2 1 x (A x)` with `A = connDiffSection g₁ g₀`, as a rank-`(3,4)` smooth
compactly supported tensor over `g₀`. The five arms of the order-one Leibniz kernel are
two-sided slot-permutation images of this single core. -/
def connDiffContrInsertionField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 3 4 where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace 3 4 I x from
          connContrCLM (I := I) 2 1 x ((connDiffSection (I := I) g₁ g₀).toSection x))
      contMDiff_toFun := connDiffContrInsertionFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem connDiffContrInsertionField_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connDiffContrInsertionField (I := I) g₀ g₁).toSection x =
      (show Tensor0SBundle.TensorRSSpace 3 4 I x from
        connContrCLM (I := I) 2 1 x ((connDiffSection (I := I) g₁ g₀).toSection x)) := rfl

set_option linter.unusedSectionVars false in
private theorem kernelField_eq_neg_arm_combination (g₀ g₁ : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁ =
      -(reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm0312)
            (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm102
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm0213)
              (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm120
        + appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm2301)
            (connDiffContrInsertionField (I := I) g₀ g₁)
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm1302)
              (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm102
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm1203)
              (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm120) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option linter.unusedSectionVars false in
private theorem armOuter_rfns_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) := by
  refine rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 3 4 σ
    (connDiffContrInsertionField (I := I) g₀ g₁)
    (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
      (connDiffContrInsertionField (I := I) g₀ g₁))
    (fun y d => ?_) q x
  have hy : (show Tensor0SBundle.Tensor0SSpace 3 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I y from
      (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
        (connDiffContrInsertionField (I := I) g₀ g₁)).toSection y) d =
      slotPermCLM (I := I) σ y
        ((show Tensor0SBundle.Tensor0SSpace 3 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I y from
          (connDiffContrInsertionField (I := I) g₀ g₁).toSection y) d) := rfl
  rw [hy, slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

set_option linter.unusedSectionVars false in
private theorem armFull_rfns_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
              (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) := by
  rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 4
    (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
      (connDiffContrInsertionField (I := I) g₀ g₁)) ρ q x]
  exact armOuter_rfns_eq (I := I) (M := M) g₀ g₁ σ q x

set_option linter.unusedSectionVars false in
private theorem armOuter_rfns0_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
        ((appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
        ((connDiffContrInsertionField (I := I) g₀ g₁).toSection x) := by
  have h := armOuter_rfns_eq (I := I) (M := M) g₀ g₁ σ 0 x
  simpa only [iteratedCovGrad_zero] using h

set_option linter.unusedSectionVars false in
private theorem armFull_rfns0_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
        ((reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁)) ρ).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
        ((connDiffContrInsertionField (I := I) g₀ g₁).toSection x) := by
  have h := armFull_rfns_eq (I := I) (M := M) g₀ g₁ σ ρ 0 x
  simpa only [iteratedCovGrad_zero] using h

private lemma c3_norm_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have hs := congrArg Real.sqrt h
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at hs

set_option linter.unusedSectionVars false in
private theorem armOuter_norm_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 q
        (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
          (connDiffContrInsertionField (I := I) g₀ g₁))‖ =
      ‖iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
  refine c3_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q
        (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
          (connDiffContrInsertionField (I := I) g₀ g₁))),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁))]
  have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁))).toSection x)) =
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x)) :=
    funext fun x => armOuter_rfns_eq (I := I) (M := M) g₀ g₁ σ q x
  rw [hpt]

set_option linter.unusedSectionVars false in
private theorem armFull_norm_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 q
        (reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)‖ =
      ‖iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
  refine c3_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q
        (reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁))]
  have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
              (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)).toSection x)) =
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x)) :=
    funext fun x => armFull_rfns_eq (I := I) (M := M) g₀ g₁ σ ρ q x
  rw [hpt]

private lemma c3_norm_five_le {V : Type*} [SeminormedAddCommGroup V] {a b c d e : V} {n : ℝ}
    (ha : ‖a‖ = n) (hb : ‖b‖ = n) (hc : ‖c‖ = n) (hd : ‖d‖ = n) (he : ‖e‖ = n) :
    ‖a + b + c + d + e‖ ≤ 5 * n := by
  have t1 := norm_add_le (a + b + c + d) e
  have t2 := norm_add_le (a + b + c) d
  have t3 := norm_add_le (a + b) c
  have t4 := norm_add_le a b
  linarith

set_option linter.unusedVariables false in
/-- Ball-uniform order-0 sup bound and all-order per-order L² tame jet envelope for the
connection-contraction insertion core field, generic in `g₁ = g₀ + P`.

POSITED CHILD (`sorry`): the covariant-Leibniz calculus for the `connContrCLM` insertion
against the connection-difference jets (the `armSlotFib`-shaped engine); the five arms of the
order-one Leibniz kernel reduce to this single core by the slot-permutation jet invariances.
Consumers transitively depend on `sorryAx` until this lands. -/
theorem connDiffContrInsertionField_order0sup_perOrder_l2_tameEnvelope_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ l, 0 ≤ K l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
            ((connDiffContrInsertionField (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (l : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
              (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 ≤
            K l * (1 + ∑ j ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := sorry

set_option linter.unusedVariables false in
/-- Ball-uniform order-0 sup bound and all-order per-order L² tame jet envelope for the
order-one connection-difference Leibniz kernel field, generic in `g₁ = g₀ + P`.

Proven by the five-arm reduction `kernelField_eq_neg_arm_combination` and the slot-permutation
jet invariances onto the single connection-contraction core. TRANSIT: the core envelope
(`connDiffContrInsertionField_order0sup_perOrder_l2_tameEnvelope_generic`) is a posited
`sorry` child; consumers transitively depend on `sorryAx` until it lands. -/
theorem linearizedRicciConnDiffOrder1KernelField_order0sup_perOrder_l2_tameEnvelope_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (K : ℕ → ℝ), 0 ≤ Λ ∧ (∀ l, 0 ≤ K l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
            ((linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁).toSection x) ≤ Λ ^ 2) ∧
        ∀ (l : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 3 4 l
              (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2 ≤
            K l * (1 + ∑ j ∈ Finset.range (l + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Λc, Kc, hΛc, hKc_nn, hcfeed⟩ :=
    connDiffContrInsertionField_order0sup_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨Real.sqrt 46 * Λc, fun l => 25 * Kc l,
    mul_nonneg (Real.sqrt_nonneg _) hΛc, fun l => by linarith [hKc_nn l], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball
  obtain ⟨hcsup, hctame⟩ := hcfeed g₁ P hδ_le hδ htie hPball
  have hcomb := kernelField_eq_neg_arm_combination (I := I) g₀ g₁
  refine ⟨?_, ?_⟩
  · intro x
    have hL2 : (Real.sqrt 46 * Λc) ^ 2 = 46 * Λc ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 46)]
    rw [hL2]
    have hx : (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁).toSection x =
        -((reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm0312)
              (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm102).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 3 4
              (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm0213)
                (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm120).toSection x
          + (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm2301)
              (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 3 4
              (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm1302)
                (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm102).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 3 4
              (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm1203)
                (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm120).toSection x) := by
      rw [hcomb]
      rfl
    rw [hx]
    set b1 := (reindexCoeffGen (I := I) (M := M) g₀ 3 4
      (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm0312)
        (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm102).toSection x with hb1
    set b2 := (reindexCoeffGen (I := I) (M := M) g₀ 3 4
      (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm0213)
        (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm120).toSection x with hb2
    set b3 := (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm2301)
      (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x with hb3
    set b4 := (reindexCoeffGen (I := I) (M := M) g₀ 3 4
      (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm1302)
        (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm102).toSection x with hb4
    set b5 := (reindexCoeffGen (I := I) (M := M) g₀ 3 4
      (appCcRS (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ kOutPerm1203)
        (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm120).toSection x with hb5
    have hneg : riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
        (-(b1 + b2 + b3 + b4 + b5)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x (b1 + b2 + b3 + b4 + b5) := by
      rw [show -(b1 + b2 + b3 + b4 + b5) = ((-1 : ℝ)) • (b1 + b2 + b3 + b4 + b5) from
        (neg_one_smul ℝ _).symm, fourTrace_rfns_smul]
      norm_num
    rw [hneg]
    have e1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x b1 =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((connDiffContrInsertionField (I := I) g₀ g₁).toSection x) := by
      rw [hb1]; exact armFull_rfns0_eq (I := I) (M := M) g₀ g₁ kOutPerm0312 kInPerm102 x
    have e2 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x b2 =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((connDiffContrInsertionField (I := I) g₀ g₁).toSection x) := by
      rw [hb2]; exact armFull_rfns0_eq (I := I) (M := M) g₀ g₁ kOutPerm0213 kInPerm120 x
    have e3 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x b3 =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((connDiffContrInsertionField (I := I) g₀ g₁).toSection x) := by
      rw [hb3]; exact armOuter_rfns0_eq (I := I) (M := M) g₀ g₁ kOutPerm2301 x
    have e4 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x b4 =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((connDiffContrInsertionField (I := I) g₀ g₁).toSection x) := by
      rw [hb4]; exact armFull_rfns0_eq (I := I) (M := M) g₀ g₁ kOutPerm1302 kInPerm102 x
    have e5 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x b5 =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 4 x
          ((connDiffContrInsertionField (I := I) g₀ g₁).toSection x) := by
      rw [hb5]; exact armFull_rfns0_eq (I := I) (M := M) g₀ g₁ kOutPerm1203 kInPerm120 x
    have hA1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 4 x b1 b2
    have hA2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 4 x (b1 + b2) b3
    have hA3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 4 x (b1 + b2 + b3) b4
    have hA4 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 3 4 x (b1 + b2 + b3 + b4) b5
    have hcore0 := hcsup x
    have hc_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 4 x
      ((connDiffContrInsertionField (I := I) g₀ g₁).toSection x)
    linarith [hA1, hA2, hA3, hA4, e1, e2, e3, e4, e5, hcore0, hc_nn]
  · intro l
    have h5 : ‖iteratedCovGrad (I := I) g₀ 3 4 l
        (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ≤
        5 * ‖iteratedCovGrad (I := I) g₀ 3 4 l
          (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
      rw [hcomb, iteratedCovGrad_neg, norm_neg, iteratedCovGrad_add, iteratedCovGrad_add,
        iteratedCovGrad_add, iteratedCovGrad_add]
      exact c3_norm_five_le
        (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm0312 kInPerm102 l)
        (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm0213 kInPerm120 l)
        (armOuter_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm2301 l)
        (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm1302 kInPerm102 l)
        (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm1203 kInPerm120 l)
    have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 3 4 l
      (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁))) h5 2
    have h25 : (5 * ‖iteratedCovGrad (I := I) g₀ 3 4 l
        (connDiffContrInsertionField (I := I) g₀ g₁)‖) ^ 2 =
        25 * ‖iteratedCovGrad (I := I) g₀ 3 4 l
          (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 := by ring
    have hct := hctame l
    calc ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2
        ≤ 25 * ‖iteratedCovGrad (I := I) g₀ 3 4 l
            (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 := by rw [← h25]; exact hsq
      _ ≤ 25 * (Kc l * (1 + ∑ j ∈ Finset.range (l + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by linarith
      _ = 25 * Kc l * (1 + ∑ j ∈ Finset.range (l + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
