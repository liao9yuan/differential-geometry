import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnDiffCovariantJetTower

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound
    ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma succ_le_two_pow_riccati (j : ℕ) : j + 1 ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ k ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    calc k + 1 + 1 ≤ 2 ^ (k + 1) + 1 := by omega
      _ ≤ 2 ^ (k + 1) + 2 ^ (k + 1) := by omega
      _ = 2 ^ (k + 1 + 1) := by rw [pow_succ]; ring

private lemma nat_sq_le_four_pow (i : ℕ) : i ^ 2 ≤ 4 ^ i := by
  cases i with
  | zero => norm_num
  | succ k =>
    have h := succ_le_two_pow_riccati k
    calc (k + 1) ^ 2 ≤ (2 ^ (k + 1)) ^ 2 := Nat.pow_le_pow_left h 2
      _ = 2 ^ ((k + 1) * 2) := by rw [← pow_mul]
      _ = 2 ^ (2 * (k + 1)) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ (k + 1) := by rw [pow_mul]
      _ = 4 ^ (k + 1) := by norm_num

set_option linter.unusedSectionVars false in
private lemma riccati_closure (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (i : ℕ) (Q : ℕ → ℝ) (hQnn : ∀ k, 0 ≤ Q k)
    (hIH : ∀ l, l < i → Q l ≤ connDiffJetBound (E := E) R δ l)
    (hrec : Q i ≤ inverseEndoBase (E := E) R δ ^ 11
              + appCcGdiag (E := E) i *
                  ∑ p ∈ Finset.range i, (100 * R ^ 2) *
                    ∑ l ∈ Finset.range (i - p), Q l) :
    Q i ≤ connDiffJetBound (E := E) R δ i := by
  set B := inverseEndoBase (E := E) R δ with hBdef
  have hB4 : (4 : ℝ) ≤ B := four_le_inverseEndoBase R δ hR hδ0 hδ1
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hBnn : (0 : ℝ) ≤ B := by linarith
  have hfin : 2 * ((Module.finrank ℝ E : ℝ) + 1) ≤ B :=
    finrankFactor_le_inverseEndoBase R δ hR hδ0 hδ1
  have hRB : R ≤ B := by
    rw [hBdef]
    unfold inverseEndoBase
    have hr_pos : 0 < 1 - δ := by linarith
    have hfr : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      have hne : Module.finrank ℝ E ≠ 0 := NeZero.ne _
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have hr1 : (1 : ℝ) ≤ 1 / (1 - δ) := by rw [le_div_iff₀ hr_pos]; linarith
    have h2n1 : (1 : ℝ) ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) := by linarith [hfr]
    have hbase_nn : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) := by positivity
    calc R ≤ 1 + R := by linarith
      _ = 1 * (1 + R) := by ring
      _ ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) :=
          mul_le_mul_of_nonneg_right h2n1 (by linarith [hR])
      _ = 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * 1 := by ring
      _ ≤ 2 * ((Module.finrank ℝ E : ℝ) + 1) * (1 + R) * (1 / (1 - δ)) :=
          mul_le_mul_of_nonneg_left hr1 hbase_nn
  have hR2B2 : R ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hR hRB 2
  have hgdiag : appCcGdiag (E := E) i ≤ B ^ i := by
    rw [appCcGdiag]
    exact pow_le_pow_left₀ (by positivity) hfin i
  have hQbound : ∀ l, l < i → Q l ≤ B ^ (8 * i ^ 2 + 3) := by
    intro l hl
    have h1 : Q l ≤ connDiffJetBound (E := E) R δ l := hIH l hl
    have h2 : connDiffJetBound (E := E) R δ l = B ^ (8 * (l + 1) ^ 2 + 3) := by
      simp only [connDiffJetBound, hBdef]
    rw [h2] at h1
    refine h1.trans (pow_le_pow_right₀ hB1 ?_)
    have hle : (l + 1) ^ 2 ≤ i ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hinner : ∀ p ∈ Finset.range i,
      ∑ l ∈ Finset.range (i - p), Q l ≤ (i : ℝ) * B ^ (8 * i ^ 2 + 3) := by
    intro p hp
    have hterm : ∀ l ∈ Finset.range (i - p), Q l ≤ B ^ (8 * i ^ 2 + 3) := by
      intro l hl
      rw [Finset.mem_range] at hl
      exact hQbound l (by omega)
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    rw [Finset.card_range, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hBnn _)
    have hcard : (i - p : ℕ) ≤ i := Nat.sub_le i p
    exact_mod_cast hcard
  have hbigsum : ∑ p ∈ Finset.range i, (100 * R ^ 2) * ∑ l ∈ Finset.range (i - p), Q l
      ≤ (i : ℝ) * (100 * R ^ 2 * ((i : ℝ) * B ^ (8 * i ^ 2 + 3))) := by
    have hstep : ∑ p ∈ Finset.range i, (100 * R ^ 2) * ∑ l ∈ Finset.range (i - p), Q l
        ≤ ∑ p ∈ Finset.range i, (100 * R ^ 2) * ((i : ℝ) * B ^ (8 * i ^ 2 + 3)) :=
      Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hinner p hp) (by positivity))
    refine hstep.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hbigsum_nn : 0 ≤ ∑ p ∈ Finset.range i, (100 * R ^ 2) * ∑ l ∈ Finset.range (i - p), Q l :=
    Finset.sum_nonneg (fun p _ =>
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun l _ => hQnn l)))
  have hquad : appCcGdiag (E := E) i *
        (∑ p ∈ Finset.range i, (100 * R ^ 2) * ∑ l ∈ Finset.range (i - p), Q l)
      ≤ B ^ i * ((i : ℝ) * (100 * R ^ 2 * ((i : ℝ) * B ^ (8 * i ^ 2 + 3)))) := by
    refine le_trans (mul_le_mul_of_nonneg_right hgdiag hbigsum_nn) ?_
    exact mul_le_mul_of_nonneg_left hbigsum (pow_nonneg hBnn _)
  have hRHS1 : B ^ i * ((i : ℝ) * (100 * R ^ 2 * ((i : ℝ) * B ^ (8 * i ^ 2 + 3))))
      ≤ 100 * (i : ℝ) ^ 2 * B ^ (8 * i ^ 2 + i + 5) := by
    have hcollect : B ^ i * ((i : ℝ) * (100 * R ^ 2 * ((i : ℝ) * B ^ (8 * i ^ 2 + 3))))
        = 100 * (i : ℝ) ^ 2 * R ^ 2 * (B ^ i * B ^ (8 * i ^ 2 + 3)) := by ring
    rw [hcollect, ← pow_add]
    have hexp : i + (8 * i ^ 2 + 3) = 8 * i ^ 2 + i + 3 := by ring
    rw [hexp]
    have h2 : 100 * (i : ℝ) ^ 2 * R ^ 2 * B ^ (8 * i ^ 2 + i + 3)
        ≤ 100 * (i : ℝ) ^ 2 * B ^ 2 * B ^ (8 * i ^ 2 + i + 3) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR2B2 (by positivity))
        (pow_nonneg hBnn _)
    refine h2.trans (le_of_eq ?_)
    have hexp2 : (8 * i ^ 2 + i + 5) = 2 + (8 * i ^ 2 + i + 3) := by ring
    rw [hexp2, pow_add]
    ring
  have hQi : Q i ≤ B ^ 11 + 100 * (i : ℝ) ^ 2 * B ^ (8 * i ^ 2 + i + 5) :=
    hrec.trans (add_le_add (le_refl _) (hquad.trans hRHS1))
  have hfinal : B ^ 11 + 100 * (i : ℝ) ^ 2 * B ^ (8 * i ^ 2 + i + 5)
      ≤ B ^ (8 * (i + 1) ^ 2 + 3) := by
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hz : 100 * ((0 : ℕ) : ℝ) ^ 2 * B ^ (8 * 0 ^ 2 + 0 + 5) = 0 := by norm_num
      rw [hz, add_zero]
      exact le_of_eq (by rw [show 8 * (0 + 1) ^ 2 + 3 = 11 from by norm_num])
    · have hsq1 : 1 ≤ i ^ 2 := Nat.one_le_pow 2 i hipos
      have hB11 : B ^ 11 ≤ B ^ (8 * i ^ 2 + i + 5) := pow_le_pow_right₀ hB1 (by omega)
      have hi1 : (1 : ℝ) ≤ (i : ℝ) ^ 2 := by
        have hii : (1 : ℝ) ≤ (i : ℝ) := by
          have : (1 : ℕ) ≤ i := hipos
          exact_mod_cast this
        nlinarith [hii]
      have h101 : 101 * (i : ℝ) ^ 2 ≤ B ^ (15 * i + 6) := by
        have hsqfour : (i : ℝ) ^ 2 ≤ (4 : ℝ) ^ i := by
          have hn : i ^ 2 ≤ 4 ^ i := nat_sq_le_four_pow i
          calc (i : ℝ) ^ 2 = ((i ^ 2 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((4 ^ i : ℕ) : ℝ) := by exact_mod_cast hn
            _ = (4 : ℝ) ^ i := by push_cast; ring
        have h1 : 101 * (i : ℝ) ^ 2 ≤ 101 * (4 : ℝ) ^ i :=
          mul_le_mul_of_nonneg_left hsqfour (by norm_num)
        have h2 : (101 : ℝ) * (4 : ℝ) ^ i ≤ (4 : ℝ) ^ (i + 4) := by
          rw [pow_add]
          have h256 : (101 : ℝ) ≤ (4 : ℝ) ^ 4 := by norm_num
          calc (101 : ℝ) * (4 : ℝ) ^ i ≤ (4 : ℝ) ^ 4 * (4 : ℝ) ^ i :=
                mul_le_mul_of_nonneg_right h256 (by positivity)
            _ = (4 : ℝ) ^ i * (4 : ℝ) ^ 4 := by ring
        have h3 : (4 : ℝ) ^ (i + 4) ≤ B ^ (i + 4) := pow_le_pow_left₀ (by norm_num) hB4 (i + 4)
        have h4 : B ^ (i + 4) ≤ B ^ (15 * i + 6) := pow_le_pow_right₀ hB1 (by omega)
        linarith [h1, h2, h3, h4]
      calc B ^ 11 + 100 * (i : ℝ) ^ 2 * B ^ (8 * i ^ 2 + i + 5)
          ≤ B ^ (8 * i ^ 2 + i + 5) + 100 * (i : ℝ) ^ 2 * B ^ (8 * i ^ 2 + i + 5) :=
            add_le_add hB11 (le_refl _)
        _ = (1 + 100 * (i : ℝ) ^ 2) * B ^ (8 * i ^ 2 + i + 5) := by ring
        _ ≤ (101 * (i : ℝ) ^ 2) * B ^ (8 * i ^ 2 + i + 5) := by
            refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hBnn _)
            nlinarith [hi1]
        _ ≤ B ^ (15 * i + 6) * B ^ (8 * i ^ 2 + i + 5) :=
            mul_le_mul_of_nonneg_right h101 (pow_nonneg hBnn _)
        _ = B ^ (15 * i + 6 + (8 * i ^ 2 + i + 5)) := by rw [← pow_add]
        _ = B ^ (8 * (i + 1) ^ 2 + 3) := by congr 1; ring
  have hgoal : Q i ≤ B ^ (8 * (i + 1) ^ 2 + 3) := hQi.trans hfinal
  have hcjb : connDiffJetBound (E := E) R δ i = B ^ (8 * (i + 1) ^ 2 + 3) := by
    simp only [connDiffJetBound, hBdef]
  rw [hcjb]
  exact hgoal

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
theorem rfns_iteratedCovGrad_connDiffSection_riccati_recursion_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2) :
    ∀ i : ℕ, i ≤ a → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
        inverseEndoBase (E := E) R δ ^ 11
        + appCcGdiag (E := E) i *
            ∑ p ∈ Finset.range i, (100 * R ^ 2) *
              ∑ l ∈ Finset.range (i - p),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) g₁ g₀)).toSection x) :=
  sorry

set_option linter.unusedSectionVars false in
theorem rfns_iteratedCovGrad_connDiffSection_riccati_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    {R : ℝ} (hR : 0 ≤ R) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTjet : ∀ j : ℕ, j ≤ a + 1 → ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) y
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection y) ≤ R ^ 2) :
    ∀ i : ℕ, i ≤ a → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
        connDiffJetBound (E := E) R δ i := by
  have hrec := rfns_iteratedCovGrad_connDiffSection_riccati_recursion_le (I := I) (M := M)
    g₀ g₁ a T htie hR hδ0 hδ1 hδ hTjet
  intro i
  induction i using Nat.strong_induction_on with
  | _ i hstrong =>
    intro hi_le x
    exact riccati_closure (E := E) R δ hR hδ0 hδ1 i
      (fun k => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 1 2 k (connDiffSection (I := I) g₁ g₀)).toSection x))
      (fun k => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + k) x _)
      (fun l hl => hstrong l hl (by omega) x)
      (hrec i hi_le x)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
