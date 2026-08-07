import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoeffJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifDLbH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifInsertH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifVBH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifAMixH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifRiemH1

/-!
# Class-first order-zero tail bound

This module assembles the five cancellation-preserving order-zero leaves into
one dimension-three class-first affine `H1` cap.  Every coefficient is chosen
before the class metric varies, and class metric jets are used only through
order three.
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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma sum5_sq_le_sq {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 ≤
      (a + b + c + d + e) ^ 2 := by
  nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg ha hd,
    mul_nonneg ha he, mul_nonneg hb hc, mul_nonneg hb hd,
    mul_nonneg hb he, mul_nonneg hc hd, mul_nonneg hc he,
    mul_nonneg hd he]

/-- On a closed three-manifold, the cancellation-preserving
`DLb + lieCorr0` tail has a class-first affine intrinsic `H1` cap. -/
theorem tail_h1_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g₀ gBase Λ) →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ P y v w) →
          ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
          gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ P) δ →
          ∀ (R A : ℝ), 0 ≤ R → 0 ≤ A →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ gBase +
                lieCorr0Field (I := I) (M := M) g₀ g₁ gBase)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨BD, hBD, hD⟩ :=
    dlbDiff_h1_unif (I := I) (M := M) hDim gBase hΛ hδ₀
  obtain ⟨BI, hBI, hI⟩ :=
    insert_h1_unif (I := I) (M := M) hDim gBase hΛ hδ₀
  obtain ⟨BV0, BV1, hBV0, hBV1, hV⟩ :=
    vb_h1_unif (I := I) (M := M) hDim gBase hΛ hδ₀
  obtain ⟨BA0, BA1, hBA0, hBA1, hA⟩ :=
    amix_h1_unif (I := I) (M := M) hDim gBase hΛ hδ₀
  obtain ⟨BR0, BR1, hBR0, hBR1, hRiem⟩ :=
    riem_h1_unif (I := I) (M := M) hDim gBase hΛ hδ₀
  let base : ℝ → ℝ := fun R =>
    BD R + BI R + BV0 R + BA0 R + BR0 R
  let slope : ℝ → ℝ := fun R => BV1 R + BA1 R + BR1 R
  let B0 : ℝ → ℝ := fun R => 5 * base R
  let B1 : ℝ → ℝ := fun R => 5 * slope R
  have hbase : ∀ R : ℝ, 0 ≤ R → 0 ≤ base R := by
    intro R hR
    dsimp only [base]
    exact add_nonneg
      (add_nonneg
        (add_nonneg (add_nonneg (hBD R hR) (hBI R hR)) (hBV0 R hR))
        (hBA0 R hR))
      (hBR0 R hR)
  have hslope : ∀ R : ℝ, 0 ≤ R → 0 ≤ slope R := by
    intro R hR
    dsimp only [slope]
    exact add_nonneg (add_nonneg (hBV1 R hR) (hBA1 R hR)) (hBR1 R hR)
  refine ⟨B0, B1,
    fun R hR => mul_nonneg (by norm_num) (hbase R hR),
    fun R hR => mul_nonneg (by norm_num) (hslope R hR), ?_⟩
  intro g₀ hEq hjet g₁ P htie δ hδ_le hδ_nonneg hbound
    R A hR hA_nonneg hP htop
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hjet3 := hjet 3 (by norm_num)
  have hDf := hD g₀ hEq hjet1 hjet2 hjet3 g₁ P htie
    (δ := δ) hδ_le hδ_nonneg hbound R hR hP
  have hIf := hI g₀ hEq hjet1 hjet2 hjet3 g₁ P htie
    (δ := δ) hδ_le hδ_nonneg hbound R hR hP
  have hVf := hV g₀ hEq hjet1 hjet2 g₁ P htie
    (δ := δ) hδ_le hδ_nonneg hbound R A hR hA_nonneg hP htop
  have hAf := hA g₀ hEq hjet1 hjet2 hjet3 g₁ P htie
    (δ := δ) hδ_le hδ_nonneg hbound R A hR hA_nonneg hP htop
  have hRf := hRiem g₀ hEq hjet g₁ P htie
    (δ := δ) hδ_le hδ_nonneg hbound R A hR hA_nonneg hP htop
  let dR : ℝ := BD R
  let iR : ℝ := BI R
  let vR : ℝ := BV0 R + BV1 R * A
  let aR : ℝ := BA0 R + BA1 R * A
  let rR : ℝ := BR0 R + BR1 R * A
  have hdR : 0 ≤ dR := by simpa only [dR] using hBD R hR
  have hiR : 0 ≤ iR := by simpa only [iR] using hBI R hR
  have hvR : 0 ≤ vR := by
    dsimp only [vR]
    exact add_nonneg (hBV0 R hR) (mul_nonneg (hBV1 R hR) hA_nonneg)
  have haR : 0 ≤ aR := by
    dsimp only [aR]
    exact add_nonneg (hBA0 R hR) (mul_nonneg (hBA1 R hR) hA_nonneg)
  have hrR : 0 ≤ rR := by
    dsimp only [rR]
    exact add_nonneg (hBR0 R hR) (mul_nonneg (hBR1 R hR) hA_nonneg)
  have htail := tail_h1_parts (I := I) (M := M) g₀ g₁ gBase
    dR iR vR aR rR
    (by simpa only [dR] using hDf)
    (by simpa only [iR] using hIf)
    (by simpa only [vR] using hVf)
    (by simpa only [aR] using hAf)
    (by simpa only [rR] using hRf)
  have hinside :
      0 ≤ 5 * (dR ^ 2 + iR ^ 2 + vR ^ 2 + aR ^ 2 + rR ^ 2) := by
    positivity
  rw [Real.sq_sqrt hinside] at htail
  have hfive := sum5_sq_le_sq hdR hiR hvR haR hrR
  have hB : B0 R + B1 R * A = 5 * (dR + iR + vR + aR + rR) := by
    dsimp only [B0, B1, base, slope, dR, iR, vR, aR, rR]
    ring
  refine htail.trans ?_
  rw [hB]
  nlinarith [hfive, sq_nonneg (dR + iR + vR + aR + rR)]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
