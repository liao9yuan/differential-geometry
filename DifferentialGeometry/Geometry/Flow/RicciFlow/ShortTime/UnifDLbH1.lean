import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifInsertH1

/-!
# Class-first DLb background-difference H1 bound

This module gives the dimension-three class-first estimate for the `DLb`
coefficient difference between one fixed DeTurck background and the frozen
background.  The cancellation is taken before estimating, so the perturbation
is consumed only through its `H2` jet.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem connLow_self_zero
    (g : SmoothRiemannianMetric I M) :
    connDiffLoweredCc (I := I) g g = 0 := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  change unitModel (I := I) (M := M) g 3
      (connDiffLoweredCc (I := I) g g) x m = 0
  rw [connDiffLoweredCc_unitModel_apply']
  rw [PDE.DeTurck.connDiff_self]
  simp

private theorem norm_add_sq_le
    {V : Type*} [SeminormedAddCommGroup V] (u v : V) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have htri : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [hsq, sq_nonneg (‖u‖ - ‖v‖)]

private theorem dom_h1_eq
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    (∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 s q
          (domDomCongrSection (I := I) g σ S)‖ ^ 2) =
      ∑ q ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g 0 s q S‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

private theorem raise_sub
    (g : SmoothRiemannianMetric I M) (W W' : SmoothCcTensor g 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g 0 (W - W') =
      cometricRaiseSlot0Field (I := I) (M := M) g 0 W -
        cometricRaiseSlot0Field (I := I) (M := M) g 0 W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply]
  simp only [cometricRaiseSlot0Field_toSection]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply]
  rfl

/-- **Dimension-three class-first `DLb` background-difference `H1` bound.**

One nonnegative radius function is selected from `(gBase, Λ, δ₀)` before the
class metric, moving metric, and perturbation vary.  The class consumes metric
jets through order three, while the perturbation consumes only its `H2` jet. -/
theorem dlbDiff_h1_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ P y v w) →
          ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
          gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ P) δ →
          ∀ R : ℝ, 0 ≤ R →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ gBase -
                deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
            (B R) ^ 2 := by
  classical
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨Bt, hBt, htr⟩ := trace_h2_unif
    (I := I) (M := M) 1 hDim gBase hΛ0 hδ₀
  obtain ⟨CO, hCO, hoprod⟩ := appRS_h22_unif
    (I := I) (M := M) hDim gBase hΛ 0 3 1
  obtain ⟨BC, hBC, hc⟩ := connSec_h1_unif
    (I := I) (M := M) hDim gBase hΛ0 hδ₀
  obtain ⟨CA, hCA, haprod⟩ := appRS_h1_unif
    (I := I) (M := M) hDim gBase hΛ 0 1 2
  obtain ⟨F, hF, hfix⟩ := connFix_h2_unif
    (I := I) (M := M) hDim gBase hΛ
  let BO : ℝ → ℝ := fun R => CO * Bt R * F
  let BAB : ℝ → ℝ := fun R => CA * BC R * BO R
  let Q : ℝ → ℝ := fun R =>
    4 * (Module.finrank ℝ E : ℝ) *
      (2 * ((BO R) ^ 2 + (BAB R) ^ 2))
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hBO : ∀ R : ℝ, 0 ≤ R → 0 ≤ BO R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCO (hBt R hR)) hF
  have hBAB : ∀ R : ℝ, 0 ≤ R → 0 ≤ BAB R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCA (hBC R hR)) (hBO R hR)
  have hQ : ∀ R : ℝ, 0 ≤ Q R := by
    intro R
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₀ hEq hjet1 hjet2 hjet3 g₁ P htie δ hδ_le hδ_nonneg hbound
    R hR hP
  let Tr : SmoothCcTensor g₀ 3 1 :=
    lc0TraceRF (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let Fix : SmoothCcTensor g₀ 0 3 :=
    connDiffLoweredCc (I := I) g₀ g₀ -
      connDiffLoweredCc (I := I) g₀ gBase
  let OD : SmoothCcTensor g₀ 0 1 :=
    wOmega (I := I) (M := M) g₀ g₁ gBase -
      wOmega (I := I) (M := M) g₀ g₁ g₀
  let AA : SmoothCcTensor g₀ 0 2 :=
    wAlphaA (I := I) (M := M) g₀ g₁ gBase -
      wAlphaA (I := I) (M := M) g₀ g₁ g₀
  let AB : SmoothCcTensor g₀ 0 2 :=
    wAlphaB (I := I) (M := M) g₀ g₁ gBase -
      wAlphaB (I := I) (M := M) g₀ g₁ g₀
  let AD : SmoothCcTensor g₀ 0 2 :=
    wAlpha (I := I) (M := M) g₀ g₁ gBase -
      wAlpha (I := I) (M := M) g₀ g₁ g₀
  let WD : SmoothCcTensor g₀ 1 1 :=
    deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ gBase -
      deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀
  have hTr : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i Tr‖ ^ 2) ≤ (Bt R) ^ 2 := by
    simpa only [Tr] using
      htr g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound
        (Equiv.refl _) R hR hP
  have hFixEq : Fix = -connDiffLoweredCc (I := I) g₀ gBase := by
    dsimp only [Fix]
    rw [connLow_self_zero (I := I) g₀, zero_sub]
  have hFix : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i Fix‖ ^ 2) ≤ F ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (connDiffLoweredCc (I := I) g₀ gBase)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hFixEq, iteratedCovGrad_neg, norm_neg]
      _ = ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 1 2 i
            (connDiffSection (I := I) gBase g₀)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iCG_connDiffLoweredCc_eq_connDiffSection
          (I := I) (M := M) g₀ gBase i]
      _ ≤ F ^ 2 := hfix g₀ hEq hjet1 hjet2 hjet3
  have hODform :
      OD = appCcRS (I := I) (M := M) g₀ 0 3 1 Tr Fix := by
    simpa only [OD, Tr, Fix] using
      wOmega_sub_refold (I := I) (M := M) g₀ g₁ gBase g₀
  have hOD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 1 i OD‖ ^ 2) ≤ (BO R) ^ 2 := by
    rw [hODform]
    simpa only [BO] using
      hoprod g₀ hEq hjet1 hjet2 Tr Fix (Bt R) F
        (hBt R hR) hF hTr hFix
  have hCAjet : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 2 i
        (wCA (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ (BC R) ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 1 2 i
            (connDiffSection (I := I) g₁ g₀)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ i]
      _ ≤ (BC R) ^ 2 :=
        hc g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound R hR hP
  have hAAform :
      AA = domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
        (covGrad (I := I) (M := M) g₀ 0 1 OD) := by
    dsimp only [AA, OD]
    unfold wAlphaA
    rw [← DifferentialGeometry.Analysis.Parabolic.TensorSpectral.domDomCongr_sub,
      ← covGrad_sub]
  have hAA : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 i AA‖ ^ 2) ≤ (BO R) ^ 2 := by
    rw [hAAform, dom_h1_eq]
    calc
      _ ≤ ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 1 i OD‖ ^ 2 := by
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
          iteratedCovGrad_zero, iteratedCovGrad_succ]
        nlinarith [sq_nonneg ‖OD‖]
      _ ≤ (BO R) ^ 2 := hOD
  have hABform :
      AB = appCcRS (I := I) (M := M) g₀ 0 1 2
        (wCA (I := I) (M := M) g₀ g₁) OD := by
    dsimp only [AB, OD]
    unfold wAlphaB
    rw [← appCcRS_zero_eq_appCc, ← appCcRS_zero_eq_appCc,
      ← appCcRS_sub_right]
  have hAB : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 i AB‖ ^ 2) ≤ (BAB R) ^ 2 := by
    rw [hABform]
    have hnorm := haprod g₀ hEq hjet1 hjet2
      (wCA (I := I) (M := M) g₀ g₁) OD
      (BC R) (BO R) (hBC R hR) (hBO R hR) hCAjet hOD
    have hsquare := pow_le_pow_left₀
      (norm_nonneg
        (⟨appCcRS (I := I) (M := M) g₀ 0 1 2
          (wCA (I := I) (M := M) g₀ g₁) OD⟩ :
            SmoothCcTensorH1 g₀ 0 2))
      hnorm 2
    rw [h1_jet_sq (I := I) (M := M) g₀ 0 2
      (appCcRS (I := I) (M := M) g₀ 0 1 2
        (wCA (I := I) (M := M) g₀ g₁) OD)] at hsquare
    simpa only [BAB, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare
  have hADform : AD = AA + AB := by
    dsimp only [AD, AA, AB]
    unfold wAlpha
    abel
  have hAD : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2) ≤
        2 * ((BO R) ^ 2 + (BAB R) ^ 2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2,
          (2 * ‖iteratedCovGrad (I := I) g₀ 0 2 i AA‖ ^ 2 +
            2 * ‖iteratedCovGrad (I := I) g₀ 0 2 i AB‖ ^ 2) := by
        rw [hADform]
        apply Finset.sum_le_sum
        intro i _
        rw [iteratedCovGrad_add]
        exact norm_add_sq_le _ _
      _ = 2 * (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 0 2 i AA‖ ^ 2) +
          2 * (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 0 2 i AB‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * (BO R) ^ 2 + 2 * (BAB R) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hAA (by norm_num))
          (mul_le_mul_of_nonneg_left hAB (by norm_num))
      _ = 2 * ((BO R) ^ 2 + (BAB R) ^ 2) := by ring
  have hWDform :
      WD = cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 AD := by
    dsimp only [WD, AD]
    rw [deTurckLieWEndoInsert_eq_cometricRaise_wAlpha,
      deTurckLieWEndoInsert_eq_cometricRaise_wAlpha, ← raise_sub]
  have hWD : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 1 i WD‖ ^ 2) ≤
        2 * ((BO R) ^ 2 + (BAB R) ^ 2) := by
    rw [hWDform]
    calc
      _ = ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iCG_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g₀ 0 AD i]
      _ ≤ 2 * ((BO R) ^ 2 + (BAB R) ^ 2) := hAD
  have hraw :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ gBase -
            deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i WD‖ ^ 2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2,
          4 * (Module.finrank ℝ E : ℝ) *
            ‖iteratedCovGrad (I := I) g₀ 1 1 i WD‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [WD] using
          dlbDiff_jet_le (I := I) (M := M) g₀ g₁ gBase g₀ i
      _ = 4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i WD‖ ^ 2) := by
        rw [Finset.mul_sum]
  calc
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 1 1 i WD‖ ^ 2) := hraw
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
        (2 * ((BO R) ^ 2 + (BAB R) ^ 2)) :=
      mul_le_mul_of_nonneg_left hWD
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = (B R) ^ 2 := by
      symm
      simp only [B, Real.sq_sqrt (hQ R), Q]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
