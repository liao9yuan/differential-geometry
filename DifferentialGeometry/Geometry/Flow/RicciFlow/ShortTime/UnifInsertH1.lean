import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegInsertH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifAppH12
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifAppH22
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifCoeffH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifFixedConnH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifGridH1

/-!
# Class-first insertion-difference H1 bound

This module upgrades the cancellation-preserving insertion estimate to a
dimension-three class-first statement.  Every coefficient is selected from a
fixed background metric, the order-three class parameter, and the fibre
smallness ceiling before the class metric and perturbation vary.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
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

/-- **Dimension-three class-first connection-difference `H1` bound.**

One coefficient is selected from `(gBase, Λ, δ₀)` before the class metric,
moving metric, and perturbation vary.  The proof integrates the public
connection-difference pointwise grid with `h1_low_unif`, so it consumes only
the first two class metric jets. -/
theorem connSec_h1_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
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
            ‖iteratedCovGrad (I := I) g₀ 1 2 i
              (connDiffSection (I := I) g₁ g₀)‖ ^ 2) ≤ (B R) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ := connDiff_grid_unif (I := I) (M := M) hδ₀
  obtain ⟨B, hB, hlow⟩ := h1_low_unif
    (I := I) (M := M) hDim gBase hΛ (r := 1) (s := 2) C hC
  refine ⟨B, hB, ?_⟩
  intro g₀ hEq hjet1 hjet2 g₁ P htie δ hδ_le hδ_nonneg hbound R hR hP
  refine hlow g₀ hEq hjet1 hjet2 P
    (connDiffSection (I := I) g₁ g₀) R hR hP ?_
  intro i _ x
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
    hpt g₀ g₁ P htie hδ_le hδ_nonneg hbound i x

/-- **Dimension-three class-first insertion-difference `H1` bound.**

For the complete two-slot `lieCorr0` insertion background difference, one
nonnegative radius function is fixed from `(gBase, Λ, δ₀)` before the class
metric and perturbation vary.  The moving terms use only order-two metric
jets; the order-three class jet is used solely for the fixed-background
connection coefficient. -/
theorem insert_h1_unif
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
              (lc0Insert (I := I) (M := M) g₀ g₁ gBase -
                lc0Insert (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
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
  let BA : ℝ → ℝ := fun R => CA * BC R * BO R
  let Q : ℝ → ℝ := fun R =>
    4 * (Module.finrank ℝ E : ℝ) * (BA R) ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hBO : ∀ R : ℝ, 0 ≤ R → 0 ≤ BO R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCO (hBt R hR)) hF
  have hBA : ∀ R : ℝ, 0 ≤ R → 0 ≤ BA R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCA (hBC R hR)) (hBO R hR)
  have hQ : ∀ R : ℝ, 0 ≤ Q R := by
    intro R
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₀ hEq hjet1 hjet2 hjet3 g₁ P htie δ hδ_le hδ_nonneg hbound
    R hR hP
  let Tr : SmoothCcTensor g₀ 3 1 :=
    lc0TraceRF (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let Fix : SmoothCcTensor g₀ 0 3 :=
    connDiffLoweredCc (I := I) g₀ gBase -
      connDiffLoweredCc (I := I) g₀ g₀
  let OD : SmoothCcTensor g₀ 0 1 :=
    wOmega (I := I) (M := M) g₀ g₁ g₀ -
      wOmega (I := I) (M := M) g₀ g₁ gBase
  let AD : SmoothCcTensor g₀ 0 2 :=
    wAlphaB (I := I) (M := M) g₀ g₁ g₀ -
      wAlphaB (I := I) (M := M) g₀ g₁ gBase
  let SD : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (endoDiffSection (I := I) (M := M) g₀ g₁ gBase)
  have hTr : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i Tr‖ ^ 2) ≤ (Bt R) ^ 2 := by
    simpa only [Tr] using
      htr g₀ hEq hjet1 hjet2 g₁ P htie hδ_le hδ_nonneg hbound
        (Equiv.refl _) R hR hP
  have hFixEq : Fix = connDiffLoweredCc (I := I) g₀ gBase := by
    dsimp only [Fix]
    rw [connLow_self_zero (I := I) g₀, sub_zero]
  have hFix : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i Fix‖ ^ 2) ≤ F ^ 2 := by
    rw [hFixEq]
    calc
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
      wOmega_sub_refold (I := I) (M := M) g₀ g₁ g₀ gBase
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
  have hADform :
      AD = appCcRS (I := I) (M := M) g₀ 0 1 2
        (wCA (I := I) (M := M) g₀ g₁) OD := by
    dsimp only [AD, OD]
    unfold wAlphaB
    rw [← appCcRS_zero_eq_appCc, ← appCcRS_zero_eq_appCc,
      ← appCcRS_sub_right]
  have hAD : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2) ≤ (BA R) ^ 2 := by
    rw [hADform]
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
    simpa only [BA, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.zero_add] using hsquare
  have hraise_sub :
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (wAlphaB (I := I) (M := M) g₀ g₁ g₀ -
            wAlphaB (I := I) (M := M) g₀ g₁ gBase) =
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (wAlphaB (I := I) (M := M) g₀ g₁ g₀) -
          cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (wAlphaB (I := I) (M := M) g₀ g₁ gBase) := by
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
  have hSDform :
      SD = cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 AD := by
    dsimp only [SD, AD, endoDiffSection]
    rw [slotInsertEndoCc_sub, connDiffDVFInsert_eq_cometricRaise,
      connDiffDVFInsert_eq_cometricRaise, ← hraise_sub]
  have hSD : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) ≤ (BA R) ^ 2 := by
    rw [hSDform]
    calc
      _ = ∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iCG_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g₀ 0 AD i]
      _ ≤ (BA R) ^ 2 := hAD
  have hraw :
      (∑ i ∈ Finset.range 2,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lc0Insert (I := I) (M := M) g₀ g₁ gBase -
            lc0Insert (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 2,
          4 * (Module.finrank ℝ E : ℝ) *
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [SD] using
          normSq_iCG_lc0InsertDiff_le
            (I := I) (M := M) g₀ g₁ gBase i
      _ = 4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := by
        rw [Finset.mul_sum]
  calc
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := hraw
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) * (BA R) ^ 2 :=
      mul_le_mul_of_nonneg_left hSD
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = (B R) ^ 2 := by
      symm
      simp only [B, Real.sq_sqrt (hQ R), Q]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
