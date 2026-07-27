import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoeffJets
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVFEndoInsertTopSep

/-!
# Low-regularity insertion-difference coefficient

This file bounds the cancellation-preserving background difference of the
two-slot `lieCorr0` insertion coefficient.  The exact refolds in
`LieCorr0VBRefold` remove the common moving-connection term before any norm
estimate is taken. Consequently the complete `H1` bound depends only on the
metric `H2` radius.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem jet_sub
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (A B : SmoothCcTensor g r s) (a b : ℝ)
    (hA : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) ≤ a ^ 2)
    (hB : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) ≤ b ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (A - B)‖ ^ 2) ≤
      2 * (a ^ 2 + b ^ 2) := by
  classical
  have hper : ∀ j : ℕ,
      ‖iteratedCovGrad (I := I) g r s j (A - B)‖ ^ 2 ≤
        2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
    intro j
    rw [iteratedCovGrad_sub]
    have htri := norm_sub_le (iteratedCovGrad (I := I) g r s j A)
      (iteratedCovGrad (I := I) g r s j B)
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsquare,
      sq_nonneg (‖iteratedCovGrad (I := I) g r s j A‖ -
        ‖iteratedCovGrad (I := I) g r s j B‖)]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) :=
      Finset.sum_le_sum fun j _ => hper j
    _ = 2 * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (a ^ 2 + b ^ 2) := by gcongr

private theorem grid_h1_low
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (P : SmoothCcTensor g 0 2)
    (K C : ℕ → ℝ)
    (hgrid : ∀ k : ℕ, k ≤ 2 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ K k)
    (hC : ∀ i, 0 ≤ C i)
    (Φ : SmoothCcTensor g r s)
    (hΦ : ∀ (i : ℕ), i < 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 2),
          lowJetGrid (I := I) (M := M) g P k x) :
    (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤
      ∑ i ∈ Finset.range 2,
        C i * ∑ k ∈ Finset.range (i + 2), K k := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  have hi2 : i < 2 := Finset.mem_range.mp hi
  have hsumInt : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 2),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply MeasureTheory.integrable_finset_sum
    intro k hk
    exact (hgrid k (by have := Finset.mem_range.mp hk; omega)).1
  have hscaled : MeasureTheory.Integrable
      (fun x => C i * ∑ k ∈ Finset.range (i + 2),
        lowJetGrid (I := I) (M := M) g P k x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hsumInt.const_mul (C i)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g r (s + i)
    (iteratedCovGrad (I := I) g r s i Φ)
    (fun x => C i * ∑ k ∈ Finset.range (i + 2),
      lowJetGrid (I := I) (M := M) g P k x)
    hscaled (hΦ i hi2)
  refine hnorm.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (hC i)
  rw [MeasureTheory.integral_finset_sum _
    (fun k hk => (hgrid k (by have := Finset.mem_range.mp hk; omega)).1)]
  exact Finset.sum_le_sum fun k hk =>
    (hgrid k (by have := Finset.mem_range.mp hk; omega)).2

/-- The moving-to-frozen connection-difference section has an `H1` bound
from only the metric `H2` jet. -/
theorem connSec_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R : ℝ), 0 ≤ R →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 1 2 i
            (connDiffSection (I := I) g₁ g₀)‖ ^ 2) ≤ (B R) ^ 2 := by
  classical
  obtain ⟨C, hC, hpt⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨K, hK, hgrid⟩ := h2_grid_int (I := I) (M := M) hDim g₀
  let Q : ℝ → ℝ := fun R => ∑ i ∈ Finset.range 2,
    C i * ∑ k ∈ Finset.range (i + 2), K R k
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hC i)
      (Finset.sum_nonneg fun k _ => hK R hR k)
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R hR hP
  have hgr : ∀ k : ℕ, k ≤ 2 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g₀ P k)
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g₀ P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K R k := by
    intro k hk
    simpa only [lowJetGrid] using hgrid P R hR hP k hk
  have hle := grid_h1_low (I := I) (M := M) g₀ P (K R) C
    hgr hC (connDiffSection (I := I) g₁ g₀) (by
      intro i hi x
      simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
        hpt g₁ P htie hδ_le hδ_nonneg hbound i x)
  change _ ≤ (B R) ^ 2
  rw [show (B R) ^ 2 = Q R by
    simp only [B, Real.sq_sqrt (hQ R hR)]]
  exact hle

/-- The common self-background lowered connection difference cancels before
the background difference is estimated. -/
private theorem kappa_sub_bg
    (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀ -
        lc0Kappa (I := I) (M := M) g₀ g₁ gB =
      connDiffLoweredCc (I := I) g₀ gB -
        lc0PbLow (I := I) (M := M) g₀ P g₀ gB := by
  rw [kappa_bg (I := I) (M := M) g₀ g₁ gB P htie,
    kappa_base_neg (I := I) (M := M) g₀ gB]
  abel

/-- The lowered-connection background difference is `H2`-controlled by only
the metric `H2` radius. -/
theorem kappaDiff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        (R : ℝ), 0 ≤ R →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (lc0Kappa (I := I) (M := M) g₀ g₁ g₀ -
              lc0Kappa (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤
          (B R) ^ 2 := by
  classical
  obtain ⟨BP, hBP, hp⟩ := pbLow_h2 (I := I) (M := M) hDim g₀ gB
  let SF : ℝ := ∑ i ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 3 i
      (connDiffLoweredCc (I := I) g₀ gB)‖ ^ 2
  have hSF : 0 ≤ SF := Finset.sum_nonneg fun i _ => sq_nonneg _
  let AF : ℝ := Real.sqrt SF
  let Q : ℝ → ℝ := fun R => 2 * (SF + (BP R) ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hQ : ∀ R : ℝ, 0 ≤ Q R := by
    intro R
    exact mul_nonneg (by norm_num) (add_nonneg hSF (sq_nonneg _))
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie R hR hP
  have hfix : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (connDiffLoweredCc (I := I) g₀ gB)‖ ^ 2) ≤ AF ^ 2 := by
    change SF ≤ AF ^ 2
    rw [show AF ^ 2 = SF by simp only [AF, Real.sq_sqrt hSF]]
  have hp' := hp P R hR hP
  rw [kappa_sub_bg (I := I) (M := M) g₀ g₁ gB P htie]
  have hle := jet_sub (I := I) (M := M) g₀ 0 3 3
    (connDiffLoweredCc (I := I) g₀ gB)
    (lc0PbLow (I := I) (M := M) g₀ P g₀ gB) AF (BP R) hfix hp'
  change _ ≤ (B R) ^ 2
  rw [show (B R) ^ 2 = Q R by
    simp only [B, Real.sq_sqrt (hQ R)]]
  simpa only [Q, AF, Real.sq_sqrt hSF] using hle

/-- The complete insertion background difference has a uniform intrinsic
`H1` bound depending only on the perturbation `H2` radius. -/
theorem insert_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R : ℝ), 0 ≤ R →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0Insert (I := I) (M := M) g₀ g₁ gB -
              lc0Insert (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B R) ^ 2 := by
  classical
  obtain ⟨Bt, hBt, htr⟩ := trace_h2 (I := I) (M := M) 1 hDim g₀ hδ₀
  obtain ⟨CO, hCO, hoprod⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 0 3 1
  obtain ⟨BC, hBC, hc⟩ := connSec_h1 (I := I) (M := M) hDim g₀ hδ₀
  obtain ⟨CA, hCA, haprod⟩ :=
    appRS_h1_h2_h1 (I := I) (M := M) hDim g₀ 0 1 2
  let Fix : SmoothCcTensor g₀ 0 3 :=
    connDiffLoweredCc (I := I) g₀ gB -
      connDiffLoweredCc (I := I) g₀ g₀
  let SF : ℝ := ∑ i ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 3 i Fix‖ ^ 2
  let AF : ℝ := Real.sqrt SF
  let BO : ℝ → ℝ := fun R => CO * Bt R * AF
  let BA : ℝ → ℝ := fun R => CA * BC R * BO R
  let Q : ℝ → ℝ := fun R =>
    4 * (Module.finrank ℝ E : ℝ) * (BA R) ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hSF : 0 ≤ SF := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAF : 0 ≤ AF := Real.sqrt_nonneg _
  have hBO : ∀ R : ℝ, 0 ≤ R → 0 ≤ BO R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCO (hBt R hR)) hAF
  have hBA : ∀ R : ℝ, 0 ≤ R → 0 ≤ BA R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCA (hBC R hR)) (hBO R hR)
  have hQ : ∀ R : ℝ, 0 ≤ Q R := by
    intro R
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R hR hP
  let Tr : SmoothCcTensor g₀ 3 1 :=
    lc0TraceRF (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let OD : SmoothCcTensor g₀ 0 1 :=
    wOmega (I := I) (M := M) g₀ g₁ g₀ -
      wOmega (I := I) (M := M) g₀ g₁ gB
  let AD : SmoothCcTensor g₀ 0 2 :=
    wAlphaB (I := I) (M := M) g₀ g₁ g₀ -
      wAlphaB (I := I) (M := M) g₀ g₁ gB
  let SD : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (endoDiffSection (I := I) (M := M) g₀ g₁ gB)
  have hTr : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i Tr‖ ^ 2) ≤ (Bt R) ^ 2 := by
    simpa only [Tr] using htr g₁ P htie hδ_le hδ_nonneg hbound
      (Equiv.refl _) R hR hP
  have hFix : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i Fix‖ ^ 2) ≤ AF ^ 2 := by
    change SF ≤ AF ^ 2
    rw [show AF ^ 2 = SF by simp only [AF, Real.sq_sqrt hSF]]
  have hODform :
      OD = appCcRS (I := I) (M := M) g₀ 0 3 1 Tr Fix := by
    simpa only [OD, Tr, Fix] using
      wOmega_sub_refold (I := I) (M := M) g₀ g₁ g₀ gB
  have hOD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 1 i OD‖ ^ 2) ≤ (BO R) ^ 2 := by
    rw [hODform]
    simpa only [BO] using
      hoprod Tr Fix (Bt R) AF (hBt R hR) hAF hTr hFix
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
      _ ≤ (BC R) ^ 2 := hc g₁ P htie hδ_le hδ_nonneg hbound R hR hP
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
    have hnorm := haprod (wCA (I := I) (M := M) g₀ g₁) OD
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
            wAlphaB (I := I) (M := M) g₀ g₁ gB) =
        cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (wAlphaB (I := I) (M := M) g₀ g₁ g₀) -
          cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (wAlphaB (I := I) (M := M) g₀ g₁ gB) := by
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
          (lc0Insert (I := I) (M := M) g₀ g₁ gB -
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
            (I := I) (M := M) g₀ g₁ gB i
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
