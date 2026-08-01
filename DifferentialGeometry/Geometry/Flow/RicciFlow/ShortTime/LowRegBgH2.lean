import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegInsertH1
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRhsOne
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderLowBaseAction

/-!
# Fixed-background low-base coefficient bounds

This module isolates the first-order correction caused by changing the fixed
DeTurck background away from the frozen spectral metric.  The Ricci refold and
the small second-order coefficient are unchanged; only the background-dependent
Lie coefficients are estimated here.
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
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open LieCorr0Core

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem h2Jet_smul
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (a : ℝ) (W : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (a • W)‖ ^ 2) =
      a ^ 2 * ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

omit [BoundarylessManifold I M] in
private theorem lowJetSq_nonneg
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (W : SmoothCcTensor g r s) :
    0 ≤ lowJetSq (I := I) (M := M) g m W := by
  unfold lowJetSq
  exact Finset.sum_nonneg fun q _ => sq_nonneg _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem gBound_mono
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ δ' : ℝ} (hδδ' : δ ≤ δ')
    (hb : gFibreOpBound (I := I) (M := M) g h δ) :
    gFibreOpBound (I := I) (M := M) g h δ' := by
  intro x v w
  refine (hb x v w).trans ?_
  have hnn : 0 ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) =
        δ * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) := by ring
    _ ≤ δ' * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) :=
      mul_le_mul_of_nonneg_right hδδ' hnn
    _ = δ' * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by ring

private theorem hs3_of_jet3
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (T : SmoothCcTensor g 0 2) (A : ℝ), 0 ≤ A →
        lowJetSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ D * A := by
  obtain ⟨C, hC, hhs⟩ := hs_le_jet (I := I) (M := M) g 2 3
  let D : ℝ := 2 * C
  refine ⟨D, mul_nonneg (by norm_num) hC, ?_⟩
  intro T A hA hTA
  let J : ℝ := ∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 2 j T‖
  have hJ0 : 0 ≤ J := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hJ2 : J ^ 2 ≤ 4 * lowJetSq (I := I) (M := M) g 3 T := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.range 4)
      (f := fun j => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
    simpa only [J, Finset.card_range, Nat.cast_ofNat, lowJetSq,
      Nat.reduceAdd] using h
  have hJ2A : J ^ 2 ≤ 4 * A ^ 2 :=
    hJ2.trans (mul_le_mul_of_nonneg_left hTA (by norm_num))
  have hJ : J ≤ 2 * A := by
    nlinarith
  calc
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ C * J := by
      simpa only [J, Nat.reduceAdd] using hhs T
    _ ≤ C * (2 * A) := mul_le_mul_of_nonneg_left hJ hC
    _ = D * A := by simp only [D]; ring

private theorem h2Jet_two
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j ((2 : ℝ) • W)‖ ^ 2) =
      4 * ∑ j ∈ Finset.range n,
        ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs]
  norm_num
  ring

private theorem h2Jet_sum2
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W Z : SmoothCcTensor g r s) (A B : ℝ)
    (hW : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) ≤ A ^ 2)
    (hZ : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) ≤ B ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (W + Z)‖ ^ 2) ≤
      2 * (A ^ 2 + B ^ 2) := by
  have hterm : ∀ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (W + Z)‖ ^ 2 ≤
        2 * (‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) := by
    intro j hj
    rw [iteratedCovGrad_add]
    have htri := norm_add_le
      (iteratedCovGrad (I := I) g r s j W)
      (iteratedCovGrad (I := I) g r s j Z)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg
      (‖iteratedCovGrad (I := I) g r s j W‖ -
        ‖iteratedCovGrad (I := I) g r s j Z‖)]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        2 * (‖iteratedCovGrad (I := I) g r s j W‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) :=
      Finset.sum_le_sum hterm
    _ = 2 * ((∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) +
        (∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 2 * (A ^ 2 + B ^ 2) := by gcongr

private theorem h2Jet_sub
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W Z : SmoothCcTensor g r s) (A B : ℝ)
    (hW : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) ≤ A ^ 2)
    (hZ : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) ≤ B ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (W - Z)‖ ^ 2) ≤
      2 * (A ^ 2 + B ^ 2) := by
  have hZneg : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j (-Z)‖ ^ 2) ≤ B ^ 2 := by
    simpa only [iteratedCovGrad_neg, norm_neg] using hZ
  simpa only [sub_eq_add_neg] using
    h2Jet_sum2 (I := I) (M := M) g r s n W (-Z) A B hW hZneg

private theorem h2Jet_sum4
    (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (W X Y Z : SmoothCcTensor g r s) (A B C D : ℝ)
    (hW : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j W‖ ^ 2) ≤ A ^ 2)
    (hX : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j X‖ ^ 2) ≤ B ^ 2)
    (hY : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Y‖ ^ 2) ≤ C ^ 2)
    (hZ : (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j Z‖ ^ 2) ≤ D ^ 2) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g r s j ((W + X) + (Y + Z))‖ ^ 2) ≤
      4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
  let AB : ℝ := Real.sqrt (2 * (A ^ 2 + B ^ 2))
  let CD : ℝ := Real.sqrt (2 * (C ^ 2 + D ^ 2))
  have hAB0 : 0 ≤ 2 * (A ^ 2 + B ^ 2) := by positivity
  have hCD0 : 0 ≤ 2 * (C ^ 2 + D ^ 2) := by positivity
  have hAB := h2Jet_sum2 (I := I) (M := M)
    g r s n W X A B hW hX
  have hCD := h2Jet_sum2 (I := I) (M := M)
    g r s n Y Z C D hY hZ
  have hsum := h2Jet_sum2 (I := I) (M := M)
    g r s n (W + X) (Y + Z) AB CD
    (by simpa only [AB, Real.sq_sqrt hAB0] using hAB)
    (by simpa only [CD, Real.sq_sqrt hCD0] using hCD)
  have hABsq : AB ^ 2 = 2 * (A ^ 2 + B ^ 2) := by
    simpa only [AB] using Real.sq_sqrt hAB0
  have hCDsq : CD ^ 2 = 2 * (C ^ 2 + D ^ 2) := by
    simpa only [CD] using Real.sq_sqrt hCD0
  calc
    _ ≤ 2 * (AB ^ 2 + CD ^ 2) := hsum
    _ = 4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
      rw [hABsq, hCDsq]
      ring

set_option linter.unusedVariables false in
/-- Changing the fixed DeTurck background in the `DLa` coefficient has an
intrinsic `H2` bound controlled by the perturbation through order three. -/
theorem dlaDiff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ gB -
              deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B A) ^ 2 := by
  obtain ⟨C, hC, hpt⟩ := dlaBg_grid (I := I) (M := M) g₀ gB hδ₀
  obtain ⟨B, hB, hgrid⟩ :=
    h2_of_grid (I := I) (M := M) hDim g₀ C hC
  refine ⟨B, hB, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP
  apply hgrid P
    (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ gB -
      deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g₀)
    A hA hP
  intro i hi x
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGridWindow,
    Combinatorics.antidiagonalTupleGrid] using
      hpt g₁ P htie hδ_le hδ_nonneg hbound i x

set_option linter.unusedVariables false in
/-- Changing the fixed DeTurck background in the `DLb` coefficient has an
intrinsic `H2` bound controlled by the perturbation through order three. -/
theorem dlbDiff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ gB -
              deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B A) ^ 2 := by
  obtain ⟨C, hC, hpt⟩ := dlbDiff_grid (I := I) (M := M) g₀ gB hδ₀
  obtain ⟨B, hB, hgrid⟩ :=
    h2_of_grid (I := I) (M := M) hDim g₀ C hC
  refine ⟨B, hB, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP
  apply hgrid P
    (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ gB -
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)
    A hA hP
  intro i hi x
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGridWindow,
    Combinatorics.antidiagonalTupleGrid] using
      hpt g₁ P htie hδ_le hδ_nonneg hbound i x

set_option linter.unusedVariables false in
/-- The insertion background difference has an intrinsic `H2` bound controlled
by the perturbation through order three. -/
theorem insert_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0Insert (I := I) (M := M) g₀ g₁ gB -
              lc0Insert (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B A) ^ 2 := by
  classical
  obtain ⟨Bt, hBt, htr⟩ := trace_h2 (I := I) (M := M) 1 hDim g₀ hδ₀
  obtain ⟨CO, hCO, hoprod⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 0 3 1
  obtain ⟨BC, hBC, hc⟩ := connLow_h2 (I := I) (M := M) hDim g₀ hδ₀
  obtain ⟨CA, hCA, haprod⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 0 1 2
  let Fix : SmoothCcTensor g₀ 0 3 :=
    connDiffLoweredCc (I := I) g₀ gB -
      connDiffLoweredCc (I := I) g₀ g₀
  let SF : ℝ := ∑ i ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 0 3 i Fix‖ ^ 2
  let AF : ℝ := Real.sqrt SF
  let BO : ℝ → ℝ := fun A => CO * Bt A * AF
  let BA : ℝ → ℝ := fun A => CA * BC A * BO A
  let Q : ℝ → ℝ := fun A =>
    4 * (Module.finrank ℝ E : ℝ) * (BA A) ^ 2
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hSF : 0 ≤ SF := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAF : 0 ≤ AF := Real.sqrt_nonneg _
  have hBO : ∀ A : ℝ, 0 ≤ A → 0 ≤ BO A := by
    intro A hA
    exact mul_nonneg (mul_nonneg hCO (hBt A hA)) hAF
  have hBA : ∀ A : ℝ, 0 ≤ A → 0 ≤ BA A := by
    intro A hA
    exact mul_nonneg (mul_nonneg hCA (hBC A hA)) (hBO A hA)
  have hQ : ∀ A : ℝ, 0 ≤ Q A := by
    intro A
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)
  refine ⟨B, fun A _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun j _ _ => sq_nonneg _)).trans hP
  let Tr : SmoothCcTensor g₀ 3 1 :=
    lc0TraceRF (I := I) (M := M) g₀ g₁ 1 (Equiv.refl _)
  let OD : SmoothCcTensor g₀ 0 1 :=
    wOmega (I := I) (M := M) g₀ g₁ g₀ -
      wOmega (I := I) (M := M) g₀ g₁ gB
  have hTr : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 1 i Tr‖ ^ 2) ≤ (Bt A) ^ 2 := by
    simpa only [Tr] using htr g₁ P htie hδ_le hδ_nonneg hbound
      (Equiv.refl _) A hA hP2
  have hFix : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i Fix‖ ^ 2) ≤ AF ^ 2 := by
    change SF ≤ AF ^ 2
    rw [show AF ^ 2 = SF by simp only [AF, Real.sq_sqrt hSF]]
  have hODform :
      OD = appCcRS (I := I) (M := M) g₀ 0 3 1 Tr Fix := by
    simpa only [OD, Tr, Fix] using
      wOmega_sub_refold (I := I) (M := M) g₀ g₁ g₀ gB
  have hOD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 1 i OD‖ ^ 2) ≤ (BO A) ^ 2 := by
    rw [hODform]
    simpa only [BO] using
      hoprod Tr Fix (Bt A) AF (hBt A hA) hAF hTr hFix
  have hCAjet : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 1 2 i
        (wCA (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ (BC A) ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 3 i
            (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ i,
          ← norm_iCG_connDiffLoweredCc_eq_connDiffSection
            (I := I) (M := M) g₀ g₁ i]
      _ ≤ (BC A) ^ 2 :=
        hc g₁ P htie hδ_le hδ_nonneg hbound A hA hP
  let AD : SmoothCcTensor g₀ 0 2 :=
    wAlphaB (I := I) (M := M) g₀ g₁ g₀ -
      wAlphaB (I := I) (M := M) g₀ g₁ gB
  have hADform :
      AD = appCcRS (I := I) (M := M) g₀ 0 1 2
        (wCA (I := I) (M := M) g₀ g₁) OD := by
    dsimp only [AD, OD]
    unfold wAlphaB
    rw [← appCcRS_zero_eq_appCc, ← appCcRS_zero_eq_appCc,
      ← appCcRS_sub_right]
  have hAD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2) ≤ (BA A) ^ 2 := by
    rw [hADform]
    simpa only [BA] using
      haprod (wCA (I := I) (M := M) g₀ g₁) OD
        (BC A) (BO A) (hBC A hA) (hBO A hA) hCAjet hOD
  let SD : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0
      (endoDiffSection (I := I) (M := M) g₀ g₁ gB)
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
  have hSD : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) ≤ (BA A) ^ 2 := by
    rw [hSDform]
    calc
      _ = ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 i AD‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_iCG_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g₀ 0 AD i]
      _ ≤ (BA A) ^ 2 := hAD
  have hraw :
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (lc0Insert (I := I) (M := M) g₀ g₁ gB -
            lc0Insert (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := by
    calc
      _ ≤ ∑ i ∈ Finset.range 3,
          4 * (Module.finrank ℝ E : ℝ) *
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [SD] using
          normSq_iCG_lc0InsertDiff_le
            (I := I) (M := M) g₀ g₁ gB i
      _ = 4 * (Module.finrank ℝ E : ℝ) *
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := by
        rw [Finset.mul_sum]
  calc
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) *
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 1 1 i SD‖ ^ 2) := hraw
    _ ≤ 4 * (Module.finrank ℝ E : ℝ) * (BA A) ^ 2 :=
      mul_le_mul_of_nonneg_left hSD
        (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = (B A) ^ 2 := by
      symm
      simp only [B, Real.sq_sqrt (hQ A), Q]

set_option linter.unusedVariables false in
/-- The mixed correction normal form is `H2`-controlled by the metric through
order three, for an arbitrary fixed DeTurck background. -/
private theorem amixForm_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0AMixFormRF (I := I) (M := M) g₀ g₁ gB)‖ ^ 2) ≤
          (B A) ^ 2 := by
  classical
  obtain ⟨Bt2, hBt2, htr2⟩ := trace_h2 (I := I) (M := M) 2 hDim g₀ hδ₀
  obtain ⟨Bt3, hBt3, htr3⟩ := trace_h2 (I := I) (M := M) 3 hDim g₀ hδ₀
  obtain ⟨Bt4, hBt4, htr4⟩ := trace_h2 (I := I) (M := M) 4 hDim g₀ hδ₀
  obtain ⟨BK, hBK, hkbg⟩ := kappaBg_h2 (I := I) (M := M) hDim g₀ gB
  obtain ⟨Cq, hCq, hqprod⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 2 5 3
  obtain ⟨Cn, hCn, hnprod⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 2 3 6
  obtain ⟨Cm, hCm, hmprod⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 2 6 4
  obtain ⟨Co, hCo, hoprod⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 2 4 2
  let sf : ℕ → ℝ := fun w => Real.sqrt ((Module.finrank ℝ E : ℝ) ^ w)
  let Qb : ℝ → ℝ := fun A => Cq * Bt3 A * (sf 2 * (4 * A))
  let Nb : ℝ → ℝ := fun A => Cn * (sf 3 * BK A) * Qb A
  let Mb : ℝ → ℝ := fun A => Cm * Bt4 A * Nb A
  let Ob : ℝ → ℝ := fun A => Co * Bt2 A * Mb A
  let B : ℝ → ℝ := fun A => 4 * Ob A
  have hsf : ∀ w : ℕ, 0 ≤ sf w := fun w => Real.sqrt_nonneg _
  have hQb : ∀ A : ℝ, 0 ≤ A → 0 ≤ Qb A := by
    intro A hA
    exact mul_nonneg (mul_nonneg hCq (hBt3 A hA))
      (mul_nonneg (hsf 2) (mul_nonneg (by norm_num) hA))
  have hNb : ∀ A : ℝ, 0 ≤ A → 0 ≤ Nb A := by
    intro A hA
    exact mul_nonneg (mul_nonneg hCn (mul_nonneg (hsf 3) (hBK A hA)))
      (hQb A hA)
  have hMb : ∀ A : ℝ, 0 ≤ A → 0 ≤ Mb A := by
    intro A hA
    exact mul_nonneg (mul_nonneg hCm (hBt4 A hA)) (hNb A hA)
  have hOb : ∀ A : ℝ, 0 ≤ A → 0 ≤ Ob A := by
    intro A hA
    exact mul_nonneg (mul_nonneg hCo (hBt2 A hA)) (hMb A hA)
  refine ⟨B, fun A hA => mul_nonneg (by norm_num) (hOb A hA), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun j _ _ => sq_nonneg _)).trans hP
  let T2a : SmoothCcTensor g₀ 4 2 :=
    lc0TraceRF (I := I) (M := M) g₀ g₁ 2 lieCorr0AMixPerm2
  let T2b : SmoothCcTensor g₀ 4 2 :=
    lc0TraceRF (I := I) (M := M) g₀ g₁ 2
      (lc0SwapPermRF * lieCorr0AMixPerm2)
  let T3 : SmoothCcTensor g₀ 5 3 :=
    lc0TraceRF (I := I) (M := M) g₀ g₁ 3 lieCorr0AMixPermQ
  let T4 : SmoothCcTensor g₀ 6 4 :=
    lc0TraceRF (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1
  let K0 : SmoothCcTensor g₀ 0 3 :=
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀
  let KB : SmoothCcTensor g₀ 0 3 :=
    lc0Kappa (I := I) (M := M) g₀ g₁ gB
  let K0s : SmoothCcTensor g₀ 2 5 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 2 K0
  let Qf : SmoothCcTensor g₀ 2 3 :=
    appCcRS (I := I) (M := M) g₀ 2 5 3 T3 K0s
  let KBs : SmoothCcTensor g₀ 3 6 :=
    slotExtendIter (I := I) (M := M) g₀ 0 3 3 KB
  let Nf : SmoothCcTensor g₀ 2 6 :=
    appCcRS (I := I) (M := M) g₀ 2 3 6 KBs Qf
  let Mid : SmoothCcTensor g₀ 2 4 :=
    appCcRS (I := I) (M := M) g₀ 2 6 4 T4 Nf
  let Oa : SmoothCcTensor g₀ 2 2 :=
    appCcRS (I := I) (M := M) g₀ 2 4 2 T2a Mid
  let Ob' : SmoothCcTensor g₀ 2 2 :=
    appCcRS (I := I) (M := M) g₀ 2 4 2 T2b Mid
  have hT2a : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i T2a‖ ^ 2) ≤ (Bt2 A) ^ 2 := by
    simpa only [T2a] using htr2 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0AMixPerm2 A hA hP2
  have hT2b : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i T2b‖ ^ 2) ≤ (Bt2 A) ^ 2 := by
    simpa only [T2b] using htr2 g₁ P htie hδ_le hδ_nonneg hbound
      (lc0SwapPermRF * lieCorr0AMixPerm2) A hA hP2
  have hT3 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 5 3 i T3‖ ^ 2) ≤ (Bt3 A) ^ 2 := by
    simpa only [T3] using htr3 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0AMixPermQ A hA hP2
  have hT4 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 6 4 i T4‖ ^ 2) ≤ (Bt4 A) ^ 2 := by
    simpa only [T4] using htr4 g₁ P htie hδ_le hδ_nonneg hbound
      lieCorr0AMixPerm1 A hA hP2
  have hK0 : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i K0‖ ^ 2) ≤ (4 * A) ^ 2 := by
    simpa only [K0] using kappaSelf_h2
      (I := I) (M := M) g₀ g₁ P htie A hA hP
  have hKB : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i KB‖ ^ 2) ≤ (BK A) ^ 2 := by
    simpa only [KB] using hkbg g₁ P htie A hA hP
  have hK0s : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 5 i K0s‖ ^ 2) ≤
        (sf 2 * (4 * A)) ^ 2 := by
    simpa only [K0s, sf] using slotIter_h2b
      (I := I) (M := M) g₀ 0 3 2 K0 (4 * A) hK0
  have hQf : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 3 i Qf‖ ^ 2) ≤ (Qb A) ^ 2 := by
    simpa only [Qf, Qb] using hqprod T3 K0s (Bt3 A) (sf 2 * (4 * A))
      (hBt3 A hA) (mul_nonneg (hsf 2) (mul_nonneg (by norm_num) hA)) hT3 hK0s
  have hKBs : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 6 i KBs‖ ^ 2) ≤
        (sf 3 * BK A) ^ 2 := by
    simpa only [KBs, sf] using slotIter_h2b
      (I := I) (M := M) g₀ 0 3 3 KB (BK A) hKB
  have hNf : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 6 i Nf‖ ^ 2) ≤ (Nb A) ^ 2 := by
    simpa only [Nf, Nb] using hnprod KBs Qf (sf 3 * BK A) (Qb A)
      (mul_nonneg (hsf 3) (hBK A hA)) (hQb A hA) hKBs hQf
  have hMid : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 4 i Mid‖ ^ 2) ≤ (Mb A) ^ 2 := by
    simpa only [Mid, Mb] using hmprod T4 Nf (Bt4 A) (Nb A)
      (hBt4 A hA) (hNb A hA) hT4 hNf
  have hOa : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Oa‖ ^ 2) ≤ (Ob A) ^ 2 := by
    simpa only [Oa, Ob] using hoprod T2a Mid (Bt2 A) (Mb A)
      (hBt2 A hA) (hMb A hA) hT2a hMid
  have hOb' : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i Ob'‖ ^ 2) ≤ (Ob A) ^ 2 := by
    simpa only [Ob', Ob] using hoprod T2b Mid (Bt2 A) (Mb A)
      (hBt2 A hA) (hMb A hA) hT2b hMid
  have hsum := h2Jet_sum2 (I := I) (M := M) g₀ 2 2 3 Oa Ob'
    (Ob A) (Ob A) hOa hOb'
  have htwo := h2Jet_two (I := I) (M := M) g₀ 2 2 3 (Oa + Ob')
  rw [show lc0AMixFormRF (I := I) (M := M) g₀ g₁ gB =
      (2 : ℝ) • (Oa + Ob') by rfl, htwo]
  change 4 * (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i (Oa + Ob')‖ ^ 2) ≤
    (B A) ^ 2
  calc
    _ ≤ 4 * (2 * ((Ob A) ^ 2 + (Ob A) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (B A) ^ 2 := by
      dsimp only [B]
      ring

set_option linter.unusedVariables false in
/-- Changing the fixed background in the genuine mixed Lie correction has an
intrinsic `H2` bound controlled by the perturbation through order three. -/
theorem amixDiff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (lc0AMix (I := I) (M := M) g₀ g₁ gB -
              lc0AMix (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2) ≤
          (B A) ^ 2 := by
  obtain ⟨BB, hBB, hbg⟩ := amixForm_h2 (I := I) (M := M) hDim g₀ gB hδ₀
  obtain ⟨B0, hB0, hbase⟩ := amixForm_h2 (I := I) (M := M) hDim g₀ g₀ hδ₀
  let Q : ℝ → ℝ := fun A => 2 * ((BB A) ^ 2 + (B0 A) ^ 2)
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hQ : ∀ A : ℝ, 0 ≤ Q A := by
    intro A
    exact mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  refine ⟨B, fun A _ => Real.sqrt_nonneg _, ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP
  have hbg' := hbg g₁ P htie hδ_le hδ_nonneg hbound A hA hP
  have hbase' := hbase g₁ P htie hδ_le hδ_nonneg hbound A hA hP
  rw [amix_refold_rf (I := I) (M := M) g₀ g₁ gB,
    amix_refold_rf (I := I) (M := M) g₀ g₁ g₀]
  have hdiff := h2Jet_sub (I := I) (M := M) g₀ 2 2 3
    (lc0AMixFormRF (I := I) (M := M) g₀ g₁ gB)
    (lc0AMixFormRF (I := I) (M := M) g₀ g₁ g₀)
    (BB A) (B0 A) hbg' hbase'
  calc
    _ ≤ Q A := by simpa only [Q] using hdiff
    _ = (B A) ^ 2 := by
      symm
      simp only [B, Real.sq_sqrt (hQ A)]

private noncomputable def bgCorrFam
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  LowBaseInternal.rhsSelfLow (I := I) (M := M)
      g₀ gB T hδ hδZ s -
    LowBaseInternal.rhsSelfLow (I := I) (M := M)
      g₀ g₀ T hδ hδZ s

private theorem bgCorr_eq
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ)
    (s : ℝ) :
    bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ s =
      let g₁ := realizedFam (I := I) g₀ T 0 hδ hδZ s
      ((deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ gB -
          deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g₀) +
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ gB -
          deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)) +
      ((lc0Insert (I := I) (M := M) g₀ g₁ gB -
          lc0Insert (I := I) (M := M) g₀ g₁ g₀) +
        (lc0AMix (I := I) (M := M) g₀ g₁ gB -
          lc0AMix (I := I) (M := M) g₀ g₁ g₀)) := by
  simp only [bgCorrFam, LowBaseInternal.rhsSelfLow]
  rw [← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField,
    ← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField,
    lc0_decomp, lc0_decomp]
  abel

set_option linter.unusedVariables false in
private theorem bgCorrFam_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ A ^ 2 →
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ s)‖ ^ 2) ≤
            (B A) ^ 2 := by
  obtain ⟨Ba, hBa, hDla⟩ :=
    dlaDiff_h2 (I := I) (M := M) hDim g₀ gB hδ₀
  obtain ⟨Bb, hBb, hDlb⟩ :=
    dlbDiff_h2 (I := I) (M := M) hDim g₀ gB hδ₀
  obtain ⟨Bi, hBi, hIns⟩ :=
    insert_h2 (I := I) (M := M) hDim g₀ gB hδ₀
  obtain ⟨Bm, hBm, hMix⟩ :=
    amixDiff_h2 (I := I) (M := M) hDim g₀ gB hδ₀
  let Q : ℝ → ℝ := fun A =>
    (Ba A) ^ 2 + (Bb A) ^ 2 + (Bi A) ^ 2 + (Bm A) ^ 2
  let B : ℝ → ℝ := fun A => 2 * Real.sqrt (Q A)
  have hQ : ∀ A : ℝ, 0 ≤ Q A := by
    intro A
    exact add_nonneg (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (sq_nonneg _)) (sq_nonneg _)
  refine ⟨B, fun A hA => mul_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
  intro T δ hδ_le hδ_nonneg hδ hδZ A hA hT s hs
  let P : SmoothCcTensor g₀ 0 2 :=
    convexPerturbation (I := I) g₀ T 0 s
  let g₁ : SmoothRiemannianMetric I M :=
    realizedFam (I := I) g₀ T 0 hδ hδZ s
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    simpa only [g₁, P] using realizedFam_inner_of_mem
      (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  have hPbound : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δ := by
    have h := convexPerturbation_gFibreOpBound
      (I := I) (M := M) g₀ T 0 hδ hδZ hs.1 hs.2
    have hscalar : (1 - s) * δ + s * δ = δ := by ring
    rw [hscalar] at h
    simpa only [P] using h
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPjet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 := by
    rw [show P = s • T by
      simp only [P, convexPerturbation, smul_zero, zero_add],
      h2Jet_smul]
    calc
      s ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤
          1 * (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hs2
          (Finset.sum_nonneg fun j _ => sq_nonneg _)
      _ ≤ A ^ 2 := by simpa only [one_mul] using hT
  have hDa := hDla g₁ P htie hδ_le hδ_nonneg hPbound A hA hPjet
  have hDb := hDlb g₁ P htie hδ_le hδ_nonneg hPbound A hA hPjet
  have hIn := hIns g₁ P htie hδ_le hδ_nonneg hPbound A hA hPjet
  have hMx := hMix g₁ P htie hδ_le hδ_nonneg hPbound A hA hPjet
  have hsum := h2Jet_sum4 (I := I) (M := M) g₀ 2 2 3
    (deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ gB -
      deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g₀)
    (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ gB -
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)
    (lc0Insert (I := I) (M := M) g₀ g₁ gB -
      lc0Insert (I := I) (M := M) g₀ g₁ g₀)
    (lc0AMix (I := I) (M := M) g₀ g₁ gB -
      lc0AMix (I := I) (M := M) g₀ g₁ g₀)
    (Ba A) (Bb A) (Bi A) (Bm A) hDa hDb hIn hMx
  rw [bgCorr_eq]
  dsimp only
  calc
    _ ≤ 4 * ((Ba A) ^ 2 + (Bb A) ^ 2 + (Bi A) ^ 2 + (Bm A) ^ 2) := by
      simpa only [g₁] using hsum
    _ = (B A) ^ 2 := by
      rw [show (Ba A) ^ 2 + (Bb A) ^ 2 + (Bi A) ^ 2 + (Bm A) ^ 2 = Q A from rfl]
      symm
      simp only [B, mul_pow, Real.sq_sqrt (hQ A)]
      norm_num

private noncomputable def bgCorrInt
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ) :
    SmoothCcTensor g₀ 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g₀ 2 2
    (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt)
    (threeArmJoint_sub (I := I) (M := M) g₀ _ _
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g₀ gB T hδ hδZ)
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g₀ g₀ T hδ hδZ))

private theorem selfLow_bg_sub
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ) :
    LowBaseInternal.selfLowInt (I := I) (M := M)
          g₀ gB T hδ_lt hδ hδZ -
        LowBaseInternal.selfLowInt (I := I) (M := M)
          g₀ g₀ T hδ_lt hδ hδZ =
      bgCorrInt (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ := by
  classical
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hBcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g₀ 2 2
      (LowBaseInternal.rhsSelfLow
        (I := I) (M := M) g₀ gB T hδ hδZ)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g₀ gB T hδ hδZ)
  have h0cont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g₀ 2 2
      (LowBaseInternal.rhsSelfLow
        (I := I) (M := M) g₀ g₀ T hδ hδZ)
      (realizedSmallSet (δ := δ) (δ' := δ))
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g₀ g₀ T hδ hδZ)
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hBint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((LowBaseInternal.rhsSelfLow
          (I := I) (M := M) g₀ gB T hδ hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    ((hBcont x).mono hSI).intervalIntegrable
  have h0int : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((LowBaseInternal.rhsSelfLow
          (I := I) (M := M) g₀ g₀ T hδ hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    ((h0cont x).mono hSI).intervalIntegrable
  simp only [LowBaseInternal.selfLowInt, bgCorrInt, bgCorrFam,
    pathIntegralCoeffField_toModel, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hBint h0int]

private theorem lowC0_bg_eq
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ) :
    (lowBaseData (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ).C0 =
      (lowBaseData (I := I) (M := M) g₀ g₀ T hδ_lt hδ hδZ).C0 +
        bgCorrInt (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ +
        (phiMetCurvCoeff (I := I) g₀ gB g₀ -
          phiMetCurvCoeff (I := I) g₀ g₀ g₀) := by
  have hself := selfLow_bg_sub (I := I) (M := M)
    g₀ gB T hδ_lt hδ hδZ
  rw [LowBaseInternal.c0_eq, LowBaseInternal.c0_eq]
  rw [sub_eq_iff_eq_add] at hself
  rw [hself]
  abel

private theorem bgCorrInt_h2
    (g₀ gB : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀
        (0 : SmoothCcTensor g₀ 0 2)) δ)
    (B : ℝ) (hB : 0 ≤ B)
    (hcoeff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ s)‖ ^ 2) ≤
        B ^ 2) :
    (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (bgCorrInt (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ)‖ ^ 2) ≤
      B ^ 2 := by
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      realizedSmallSet (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g₀ 2 2 2
    (bgCorrFam (I := I) (M := M) g₀ gB T hδ hδZ)
    (realizedSmallSet (δ := δ) (δ' := δ))
    realizedSmallSet_isOpen hSI
    (threeArmJoint_sub (I := I) (M := M) g₀ _ _
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g₀ gB T hδ hδZ)
      (LowBaseInternal.selfLow_joint
        (I := I) (M := M) g₀ g₀ T hδ hδZ))
    hB hcoeff
  simpa only [bgCorrInt] using hpath

set_option linter.unusedVariables false in
/-- The complete fixed-background correction to the zero-order coefficient has
an intrinsic `H2` bound controlled only by the state through order three. -/
theorem bgCorr_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (bgCorrInt (I := I) (M := M) g₀ gB T
              (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ)‖ ^ 2) ≤
          (B A) ^ 2 := by
  obtain ⟨B, hB, hfam⟩ :=
    bgCorrFam_h2 (I := I) (M := M) hDim g₀ gB hδ₀
  refine ⟨B, hB, ?_⟩
  intro T δ hδ_le hδ_nonneg hδ hδZ A hA hT
  apply bgCorrInt_h2 (I := I) (M := M) g₀ gB T
    (lt_of_le_of_lt hδ_le hδ₀) hδ hδZ (B A) (hB A hA)
  intro s hs
  exact hfam T hδ_le hδ_nonneg hδ hδZ A hA hT s hs

private theorem fixedBg_h2
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (phiMetCurvCoeff (I := I) g₀ gB g₀ -
            phiMetCurvCoeff (I := I) g₀ g₀ g₀)‖ ^ 2) ≤ B ^ 2 := by
  let Q : ℝ := ∑ i ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (phiMetCurvCoeff (I := I) g₀ gB g₀ -
        phiMetCurvCoeff (I := I) g₀ g₀ g₀)‖ ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨Real.sqrt Q, Real.sqrt_nonneg _, ?_⟩
  rw [Real.sq_sqrt hQ]

/-- The general fixed-background zero-order coefficient has an intrinsic `H2`
bound depending only on the state through order three. -/
theorem lowC0_bg_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ_nonneg : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ)
        (A : ℝ), 0 ≤ A →
        lowJetSq (I := I) (M := M) g₀ 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g₀ 2
          (lowBaseData (I := I) (M := M) g₀ gB T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδ hδZ).C0 ≤
          (B A) ^ 2 := by
  obtain ⟨K, hK, hsame⟩ :=
    lowData_a1_coeff (I := I) (M := M) hDim g₀
  obtain ⟨Bc, hBc, hcorr⟩ :=
    bgCorr_h2 (I := I) (M := M) hDim g₀ gB
      (δ₀ := (1 : ℝ) / 3) (by norm_num)
  obtain ⟨Bf, hBf, hfixed⟩ := fixedBg_h2 (I := I) (M := M) g₀ gB
  let S : ℝ → ℝ := fun A => Real.sqrt (K * (1 + A ^ 2) ^ 6)
  let Q : ℝ → ℝ := fun A => (S A) ^ 2 + (Bc A) ^ 2 + Bf ^ 2
  let B : ℝ → ℝ := fun A => 2 * Real.sqrt (Q A)
  have hSarg : ∀ A : ℝ, 0 ≤ K * (1 + A ^ 2) ^ 6 := by
    intro A
    exact mul_nonneg hK (pow_nonneg (by positivity) 6)
  have hQ : ∀ A : ℝ, 0 ≤ Q A := by
    intro A
    exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  refine ⟨B, fun A hA => mul_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
  intro T hT δ hδ_le hδ_nonneg hδ hδZ A hA hTA
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let C0 : SmoothCcTensor g₀ 2 2 :=
    (lowBaseData (I := I) (M := M) g₀ g₀ T hδ_lt hδ hδZ).C0
  let C1 : SmoothCcTensor g₀ 3 2 :=
    (lowBaseData (I := I) (M := M) g₀ g₀ T hδ_lt hδ hδZ).C1
  let Cb : SmoothCcTensor g₀ 2 2 :=
    bgCorrInt (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ
  let F : SmoothCcTensor g₀ 2 2 :=
    phiMetCurvCoeff (I := I) g₀ gB g₀ -
      phiMetCurvCoeff (I := I) g₀ g₀ g₀
  have hsameAll := hsame T hT hδ_le hδ_nonneg hδ hδZ
  dsimp only at hsameAll
  have hsame0 : lowJetSq (I := I) (M := M) g₀ 2 C0 ≤
      K * (1 + lowJetSq (I := I) (M := M) g₀ 3 T) ^ 6 := by
    exact (le_add_of_nonneg_right
      (lowJetSq_nonneg (I := I) (M := M) g₀ 2 C1)).trans
      (by simpa only [C0, C1] using hsameAll)
  have hbase : 1 + lowJetSq (I := I) (M := M) g₀ 3 T ≤
      1 + A ^ 2 := by
    linarith
  have hpow : (1 + lowJetSq (I := I) (M := M) g₀ 3 T) ^ 6 ≤
      (1 + A ^ 2) ^ 6 :=
    pow_le_pow_left₀
      (by linarith [lowJetSq_nonneg (I := I) (M := M) g₀ 3 T])
      hbase 6
  have hsameS : lowJetSq (I := I) (M := M) g₀ 2 C0 ≤
      (S A) ^ 2 := by
    calc
      _ ≤ K * (1 + lowJetSq (I := I) (M := M) g₀ 3 T) ^ 6 := hsame0
      _ ≤ K * (1 + A ^ 2) ^ 6 := mul_le_mul_of_nonneg_left hpow hK
      _ = (S A) ^ 2 := by
        symm
        simp only [S, Real.sq_sqrt (hSarg A)]
  have hcorr' : lowJetSq (I := I) (M := M) g₀ 2 Cb ≤
      (Bc A) ^ 2 := by
    simpa only [lowJetSq, Cb] using
      hcorr T hδ_le hδ_nonneg hδ hδZ A hA
        (by simpa only [lowJetSq] using hTA)
  have hfixed' : lowJetSq (I := I) (M := M) g₀ 2 F ≤ Bf ^ 2 := by
    simpa only [lowJetSq, F] using hfixed
  have hzero : lowJetSq (I := I) (M := M) g₀ 2
      (0 : SmoothCcTensor g₀ 2 2) ≤ (0 : ℝ) ^ 2 := by
    have hz := h2Jet_smul (I := I) (M := M) g₀ 2 2 3
      (0 : ℝ) (0 : SmoothCcTensor g₀ 2 2)
    have hz' : (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 2 2 j
          (0 : SmoothCcTensor g₀ 2 2)‖ ^ 2) = 0 := by
      simpa only [zero_smul, pow_two, zero_mul] using hz
    change (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 j
        (0 : SmoothCcTensor g₀ 2 2)‖ ^ 2) ≤ (0 : ℝ) ^ 2
    rw [hz']
    norm_num
  have hsum := h2Jet_sum4 (I := I) (M := M) g₀ 2 2 3
    C0 Cb F (0 : SmoothCcTensor g₀ 2 2)
    (S A) (Bc A) Bf 0
    (by simpa only [lowJetSq] using hsameS)
    (by simpa only [lowJetSq] using hcorr')
    (by simpa only [lowJetSq] using hfixed')
    (by simpa only [lowJetSq] using hzero)
  have hsum' : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 2 2 j (C0 + Cb + F)‖ ^ 2) ≤
      4 * ((S A) ^ 2 + (Bc A) ^ 2 + Bf ^ 2) := by
    simpa only [add_zero,
      zero_pow (show (2 : ℕ) ≠ 0 by norm_num)] using hsum
  rw [lowC0_bg_eq (I := I) (M := M) g₀ gB T hδ_lt hδ hδZ]
  calc
    _ ≤ 4 * ((S A) ^ 2 + (Bc A) ^ 2 + Bf ^ 2) := by
      simpa only [lowJetSq, Nat.reduceAdd, C0, Cb, F] using hsum'
    _ = (B A) ^ 2 := by
      rw [show (S A) ^ 2 + (Bc A) ^ 2 + Bf ^ 2 = Q A from rfl]
      symm
      simp only [B, mul_pow, Real.sq_sqrt (hQ A)]
      norm_num

/-- The general fixed-background order-one coefficient has an intrinsic `H2`
bound depending only on the state through order three. -/
theorem lowC1_bg_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) (1 / 3))
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) (1 / 3))
        (A : ℝ), 0 ≤ A →
        lowJetSq (I := I) (M := M) g₀ 3 T ≤ A ^ 2 →
        lowJetSq (I := I) (M := M) g₀ 2
          (lowBaseData (I := I) (M := M) g₀ gB T
            (by norm_num) hδ hδZ).C1 ≤
          (B A) ^ 2 := by
  obtain ⟨D, hD, hhs3⟩ := hs3_of_jet3 (I := I) (M := M) g₀
  obtain ⟨B0, B1, hB0, hB1, hpath⟩ :=
    rhs1_path_tame (I := I) (M := M) hDim g₀ gB
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let B : ℝ → ℝ := fun A =>
    B0 (D * A) + B1 (D * A) * (D * A)
  refine ⟨B, ?_, ?_⟩
  · intro A hA
    have hDA : 0 ≤ D * A := mul_nonneg hD hA
    exact add_nonneg (hB0 (D * A) hDA)
      (mul_nonneg (hB1 (D * A) hDA) hDA)
  · intro T hδ hδZ A hA hTA
    have hDA : 0 ≤ D * A := mul_nonneg hD hA
    have hT3 :
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ D * A :=
      hhs3 T A hA hTA
    have hT2 :
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ D * A :=
      (ccToHs_norm_mono (I := I) (M := M) g₀ 2 (by norm_num) T).trans hT3
    have hZ2 : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (0 : SmoothCcTensor g₀ 0 2)‖ ≤ D * A := by
      rw [show ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
          (0 : SmoothCcTensor g₀ 0 2) = 0 by
        have hz := ccTensorToHs_smul (I := I) (M := M) g₀ 2 (2 : ℝ)
          (0 : ℝ) (0 : SmoothCcTensor g₀ 0 2)
        simpa only [zero_smul] using hz]
      simpa only [norm_zero] using hDA
    have hZ3 : ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ)
        (0 : SmoothCcTensor g₀ 0 2)‖ ≤ D * A := by
      rw [show ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ)
          (0 : SmoothCcTensor g₀ 0 2) = 0 by
        have hz := ccTensorToHs_smul (I := I) (M := M) g₀ 2 (3 : ℝ)
          (0 : ℝ) (0 : SmoothCcTensor g₀ 0 2)
        simpa only [zero_smul] using hz]
      simpa only [norm_zero] using hDA
    have hraw := hpath T (0 : SmoothCcTensor g₀ 0 2)
      hδ hδZ (D * A) (D * A) hDA hDA hT2 hZ2 hT3 hZ3
    rw [LowBaseInternal.c1_eq (I := I) (M := M)
      g₀ gB T (by norm_num) hδ hδZ]
    simpa only [lowJetSq, Nat.reduceAdd, B] using hraw

/-- The two genuinely first-order coefficients at a fixed DeTurck background
share one intrinsic `H2` envelope on every bounded state `H3` jet. -/
theorem lowData_bg_coeff
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) (1 / 3))
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) (1 / 3))
        (A : ℝ), 0 ≤ A →
        lowJetSq (I := I) (M := M) g₀ 3 T ≤ A ^ 2 →
        let L : LowBaseActionData g₀ :=
          lowBaseData (I := I) (M := M) g₀ gB T
            (by norm_num) hδ hδZ
        lowJetSq (I := I) (M := M) g₀ 2 L.C0 +
            lowJetSq (I := I) (M := M) g₀ 2 L.C1 ≤
          (B A) ^ 2 := by
  obtain ⟨B0, hB0, hC0⟩ := lowC0_bg_h2 (I := I) (M := M) hDim g₀ gB
  obtain ⟨B1, hB1, hC1⟩ := lowC1_bg_h2 (I := I) (M := M) hDim g₀ gB
  let Q : ℝ → ℝ := fun A => (B0 A) ^ 2 + (B1 A) ^ 2
  let B : ℝ → ℝ := fun A => Real.sqrt (Q A)
  have hQ : ∀ A : ℝ, 0 ≤ Q A := fun A => add_nonneg (sq_nonneg _) (sq_nonneg _)
  refine ⟨B, fun A hA => Real.sqrt_nonneg _, ?_⟩
  intro T hT hδ hδZ A hA hTA
  let L : LowBaseActionData g₀ :=
    lowBaseData (I := I) (M := M) g₀ gB T (by norm_num) hδ hδZ
  have h0 : lowJetSq (I := I) (M := M) g₀ 2 L.C0 ≤ (B0 A) ^ 2 := by
    simpa only [L] using
      hC0 T hT (δ := (1 : ℝ) / 3) le_rfl (by norm_num)
        hδ hδZ A hA hTA
  have h1 : lowJetSq (I := I) (M := M) g₀ 2 L.C1 ≤ (B1 A) ^ 2 := by
    simpa only [L] using hC1 T hδ hδZ A hA hTA
  dsimp only
  calc
    lowJetSq (I := I) (M := M) g₀ 2 L.C0 +
        lowJetSq (I := I) (M := M) g₀ 2 L.C1 ≤
      (B0 A) ^ 2 + (B1 A) ^ 2 := add_le_add h0 h1
    _ = (B A) ^ 2 := by
      symm
      simpa only [B, Q] using Real.sq_sqrt (hQ A)

/-- The fixed-background first-order action obeys compatible smooth-core
`H3 → H2` and `H2 → H1` estimates under one coefficient envelope. -/
theorem lowA1_bg_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g₀ gB : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, ∃ C3 C2 : ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧ 0 ≤ C3 ∧ 0 ≤ C2 ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) (1 / 3))
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) (1 / 3))
        (A : ℝ), 0 ≤ A →
        lowJetSq (I := I) (M := M) g₀ 3 T ≤ A ^ 2 →
        let L : LowBaseActionData g₀ :=
          lowBaseData (I := I) (M := M) g₀ gB T
            (by norm_num) hδ hδZ
        (∀ (W : SmoothCcTensor g₀ 0 2) (D : ℝ), 0 ≤ D →
          lowJetSq (I := I) (M := M) g₀ 3 W ≤ D ^ 2 →
          lowJetSq (I := I) (M := M) g₀ 2
              (L.a1 (I := I) (M := M) W) ≤
            (C3 * B A * D) ^ 2) ∧
        ∀ (W : SmoothCcTensor g₀ 0 2) (D : ℝ), 0 ≤ D →
          lowJetSq (I := I) (M := M) g₀ 2 W ≤ D ^ 2 →
          lowJetSq (I := I) (M := M) g₀ 1
              (L.a1 (I := I) (M := M) W) ≤
            (C2 * B A * D) ^ 2 := by
  obtain ⟨B, hB, hcoeff⟩ :=
    lowData_bg_coeff (I := I) (M := M) hDim g₀ gB
  obtain ⟨C3, hC3, hhigh⟩ := a1_h3_h2 (I := I) (M := M) hDim g₀
  obtain ⟨C2, hC2, hlow⟩ := a1_h2_h1 (I := I) (M := M) hDim g₀
  refine ⟨B, C3, C2, hB, hC3, hC2, ?_⟩
  intro T hT hδ hδZ A hA hTA
  let L : LowBaseActionData g₀ :=
    lowBaseData (I := I) (M := M) g₀ gB T (by norm_num) hδ hδZ
  have hL : lowJetSq (I := I) (M := M) g₀ 2 L.C0 +
      lowJetSq (I := I) (M := M) g₀ 2 L.C1 ≤ (B A) ^ 2 := by
    simpa only [L] using hcoeff T hT hδ hδZ A hA hTA
  have hBA : 0 ≤ B A := hB A hA
  dsimp only
  constructor
  · intro W D hD hW
    exact hhigh L W (B A) D hBA hD hL hW
  · intro W D hD hW
    exact hlow L W (B A) D hBA hD hL hW

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
