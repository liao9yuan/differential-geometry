import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseEndoCovariantJetTower

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

noncomputable def connDiffJetBound (R δ : ℝ) (i : ℕ) : ℝ :=
  inverseEndoBase (E := E) R δ ^ (8 * (i + 1) ^ 2 + 3)

set_option linter.unusedSectionVars false in
lemma connDiffJetBound_nonneg (R δ : ℝ) (hR : 0 ≤ R) (hδ1 : δ < 1) (i : ℕ) :
    0 ≤ connDiffJetBound (E := E) R δ i :=
  pow_nonneg (inverseEndoBase_nonneg R δ hR hδ1) _

private lemma succ_le_two_pow (j : ℕ) : j + 1 ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ k ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    calc k + 1 + 1 ≤ 2 ^ (k + 1) + 1 := by omega
      _ ≤ 2 ^ (k + 1) + 2 ^ (k + 1) := by omega
      _ = 2 ^ (k + 1 + 1) := by rw [pow_succ]; ring

private lemma sq_succ_le_four_pow (j : ℕ) : (j + 1) ^ 2 ≤ 4 ^ (j + 1) := by
  have hself := succ_le_two_pow j
  calc (j + 1) ^ 2 ≤ (2 ^ (j + 1)) ^ 2 := Nat.pow_le_pow_left hself 2
    _ = 2 ^ ((j + 1) * 2) := by rw [← pow_mul]
    _ = 2 ^ (2 * (j + 1)) := by rw [Nat.mul_comm]
    _ = (2 ^ 2) ^ (j + 1) := by rw [pow_mul]
    _ = 4 ^ (j + 1) := by norm_num

private lemma sq_split_le (i j : ℕ) (hij : i ≤ j) :
    (i + 1) ^ 2 + (j - i + 1) ^ 2 ≤ (j + 1) ^ 2 + 1 := by
  obtain ⟨d, hd⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  subst hd
  simp only [Nat.add_sub_cancel_left]
  nlinarith [Nat.zero_le (i * d)]

set_option linter.unusedSectionVars false in
private lemma connDiff_grid_le_jetBound (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (j : ℕ) :
    appCcGdiag (E := E) j *
        (∑ i ∈ Finset.range (j + 1), raisedKoszulJetBound (E := E) R δ i *
          ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l)
      ≤ connDiffJetBound (E := E) R δ j := by
  unfold connDiffJetBound
  set B0 := inverseEndoBase (E := E) R δ with hB0def
  have hB0_4 : (4 : ℝ) ≤ B0 := four_le_inverseEndoBase R δ hR hδ0 hδ1
  have hB1 : (1 : ℝ) ≤ B0 := le_trans (by norm_num) hB0_4
  have hB0nn : (0 : ℝ) ≤ B0 := le_trans (by norm_num) hB0_4
  have hf0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hfin2 : 2 * ((Module.finrank ℝ E : ℝ) + 1) ≤ B0 :=
    finrankFactor_le_inverseEndoBase R δ hR hδ0 hδ1
  have hfr : (Module.finrank ℝ E : ℝ) ≤ B0 := by linarith
  have hQle : ∀ i, raisedKoszulJetBound (E := E) R δ i ≤ B0 ^ (i + 3) * B0 ^ (2 * (i + 1) ^ 2) := by
    intro i
    unfold raisedKoszulJetBound raisedKoszulComponentBound
    rw [show raisedKoszulJetBase (E := E) R δ = inverseEndoBase (E := E) R δ from rfl, ← hB0def]
    apply mul_le_mul_of_nonneg_right
    · rw [show 3 + i = i + 3 from by omega]
      exact pow_le_pow_left₀ hf0 hfr (i + 3)
    · exact pow_nonneg hB0nn _
  have hEle : ∀ l, inverseEndoJetBound (E := E) R δ l ≤ B0 ^ (l + 3) * B0 ^ (2 * (l + 1) ^ 2) := by
    intro l
    unfold inverseEndoJetBound
    rw [← hB0def]
    apply mul_le_mul_of_nonneg_right
    · rw [show 3 + l = l + 3 from by omega]
      exact pow_le_pow_left₀ hf0 hfr (l + 3)
    · exact pow_nonneg hB0nn _
  have hinner : ∀ i, i ≤ j →
      ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l
        ≤ ((j : ℝ) + 1) * B0 ^ ((j - i + 3) + 2 * (j - i + 1) ^ 2) := by
    intro i hij
    have hterm : ∀ l ∈ Finset.range (j + 1 - i),
        inverseEndoJetBound (E := E) R δ l ≤ B0 ^ ((j - i + 3) + 2 * (j - i + 1) ^ 2) := by
      intro l hl
      have hlmi : l ≤ j - i := by simp only [Finset.mem_range] at hl; omega
      have hsq : (l + 1) ^ 2 ≤ (j - i + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      calc inverseEndoJetBound (E := E) R δ l
          ≤ B0 ^ (l + 3) * B0 ^ (2 * (l + 1) ^ 2) := hEle l
        _ = B0 ^ ((l + 3) + 2 * (l + 1) ^ 2) := by rw [← pow_add]
        _ ≤ B0 ^ ((j - i + 3) + 2 * (j - i + 1) ^ 2) := by
            apply pow_le_pow_right₀ hB1; omega
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    rw [Finset.card_range, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hB0nn _)
    have hcard : (j + 1 - i : ℕ) ≤ j + 1 := by omega
    calc ((j + 1 - i : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = (j : ℝ) + 1 := by push_cast; ring
  have hcell : ∀ i ∈ Finset.range (j + 1),
      raisedKoszulJetBound (E := E) R δ i *
          ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l
        ≤ ((j : ℝ) + 1) * B0 ^ (2 * (j + 1) ^ 2 + (j + 8)) := by
    intro i hi
    have hij : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    have hQi := hQle i
    have hinn := hinner i hij
    have hinn_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l :=
      Finset.sum_nonneg (fun l _ => inverseEndoJetBound_nonneg R δ hR hδ1 l)
    have hb_nn : (0 : ℝ) ≤ B0 ^ (i + 3) * B0 ^ (2 * (i + 1) ^ 2) :=
      mul_nonneg (pow_nonneg hB0nn _) (pow_nonneg hB0nn _)
    calc raisedKoszulJetBound (E := E) R δ i *
            ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l
        ≤ (B0 ^ (i + 3) * B0 ^ (2 * (i + 1) ^ 2)) *
            (((j : ℝ) + 1) * B0 ^ ((j - i + 3) + 2 * (j - i + 1) ^ 2)) :=
          mul_le_mul hQi hinn hinn_nn hb_nn
      _ = ((j : ℝ) + 1) *
            (B0 ^ (i + 3) * B0 ^ (2 * (i + 1) ^ 2) *
              B0 ^ ((j - i + 3) + 2 * (j - i + 1) ^ 2)) := by ring
      _ = ((j : ℝ) + 1) *
            B0 ^ ((i + 3) + 2 * (i + 1) ^ 2 + ((j - i + 3) + 2 * (j - i + 1) ^ 2)) := by
          rw [← pow_add, ← pow_add]
      _ ≤ ((j : ℝ) + 1) * B0 ^ (2 * (j + 1) ^ 2 + (j + 8)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply pow_le_pow_right₀ hB1
          have hsq := sq_split_le i j hij
          set A := (i + 1) ^ 2 with hA
          set Bb := (j - i + 1) ^ 2 with hBb
          set C := (j + 1) ^ 2 with hC
          omega
  have hsum : ∑ i ∈ Finset.range (j + 1),
        raisedKoszulJetBound (E := E) R δ i *
          ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l
      ≤ ((j : ℝ) + 1) ^ 2 * B0 ^ (2 * (j + 1) ^ 2 + (j + 8)) := by
    refine le_trans (Finset.sum_le_sum hcell) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (j + 1),
      raisedKoszulJetBound (E := E) R δ i *
        ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l := by
    apply Finset.sum_nonneg; intro i _
    exact mul_nonneg (raisedKoszulJetBound_nonneg R δ hR hδ1 i)
      (Finset.sum_nonneg (fun l _ => inverseEndoJetBound_nonneg R δ hR hδ1 l))
  have hgrid_le : appCcGdiag (E := E) j ≤ B0 ^ j := by
    rw [appCcGdiag]
    exact pow_le_pow_left₀ (by positivity) hfin2 j
  have hsqfold : ((j : ℝ) + 1) ^ 2 ≤ B0 ^ (j + 1) := by
    have hnat : (j + 1) ^ 2 ≤ 4 ^ (j + 1) := sq_succ_le_four_pow j
    have hcast : ((j : ℝ) + 1) ^ 2 ≤ (4 : ℝ) ^ (j + 1) := by exact_mod_cast hnat
    exact le_trans hcast (pow_le_pow_left₀ (by norm_num) hB0_4 (j + 1))
  calc appCcGdiag (E := E) j *
          (∑ i ∈ Finset.range (j + 1), raisedKoszulJetBound (E := E) R δ i *
            ∑ l ∈ Finset.range (j + 1 - i), inverseEndoJetBound (E := E) R δ l)
      ≤ B0 ^ j * (((j : ℝ) + 1) ^ 2 * B0 ^ (2 * (j + 1) ^ 2 + (j + 8))) :=
        mul_le_mul hgrid_le hsum hsum_nn (pow_nonneg hB0nn _)
    _ ≤ B0 ^ j * (B0 ^ (j + 1) * B0 ^ (2 * (j + 1) ^ 2 + (j + 8))) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB0nn _)
        exact mul_le_mul_of_nonneg_right hsqfold (pow_nonneg hB0nn _)
    _ = B0 ^ (j + ((j + 1) + (2 * (j + 1) ^ 2 + (j + 8)))) := by rw [← pow_add, ← pow_add]
    _ ≤ B0 ^ (8 * (j + 1) ^ 2 + 3) := by
        apply pow_le_pow_right₀ hB1
        have h1 : j + ((j + 1) + (2 * (j + 1) ^ 2 + (j + 8))) = 2 * (j + 1) ^ 2 + (3 * j + 9) := by
          ring
        have h2 : 8 * (j + 1) ^ 2 + 3 = 2 * (j + 1) ^ 2 + (6 * (j + 1) ^ 2 + 3) := by ring
        rw [h1, h2]
        have h3 : 3 * j + 6 ≤ 6 * (j + 1) ^ 2 := by nlinarith [Nat.zero_le j]
        linarith [h3]

set_option linter.unusedSectionVars false in
theorem rfns_iteratedCovGrad_connDiffSection_allOrders_le
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
  intro i hi x
  have hKos := rfns_iteratedCovGrad_raisedKoszul_le (I := I) g₀ g₁ a T htie hR hδ0 hδ1 hδ hTjet
  have hSharp := rfns_iteratedCovGrad_sharpFlatEndoCc_uniform_le (I := I) g₀ g₁ a T htie hR hδ0 hδ1
    hδ hTjet
  refine le_trans (rfns_iteratedCovGrad_connDiffSection_le (I := I) (M := M) g₀ g₁ i x
    (raisedKoszulJetBound (E := E) R δ) (inverseEndoJetBound (E := E) R δ)
    (fun i' hi' => hKos i' (le_trans hi' hi) x)
    (fun l hl => hSharp l (by omega) x)
    (fun l => inverseEndoJetBound_nonneg R δ hR hδ1 l)) ?_
  exact connDiff_grid_le_jetBound (E := E) R δ hR hδ0 hδ1 i

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
