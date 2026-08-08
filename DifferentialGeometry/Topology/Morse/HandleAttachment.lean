import DifferentialGeometry.Topology.Morse.CellAttachment
import DifferentialGeometry.Topology.Morse.ModifiedFunction

namespace DifferentialGeometry.Topology.Morse.CellAttachment

open scoped BigOperators

noncomputable section

def modelModifiedDip {n k : ℕ} (hk : k ≤ n) (ε δ : ℝ) (y : MorseModel n) : ℝ :=
  modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖

theorem modelModifiedDip_nonneg {n k : ℕ} (hk : k ≤ n) (ε δ : ℝ) (hε : 0 ≤ ε)
    (y : MorseModel n) : 0 ≤ modelModifiedDip hk ε δ y := by
  dsimp [modelModifiedDip]
  exact mul_nonneg (modMu_nonneg (ε := ε) (t := ‖negPart hk y‖ ^ 2) hε)
    (modGamma_nonneg δ ‖posPart hk y‖)

theorem modifiedNormalForm_eq_sub_dip {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y = morseNormalForm hk c y - modelModifiedDip hk ε δ y := by
  simp [modifiedNormalForm, modelModifiedDip]

theorem modifiedNormalForm_sublevel_iff {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y ≤ c - ε ↔
      ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
  rw [modifiedNormalForm_eq_sub_dip]
  rw [morseNormalForm_split]
  dsimp [modelModifiedDip]
  constructor <;> intro h <;> nlinarith

theorem modelModifiedDip_sublevel_denom_pos {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) {y : MorseModel n} (hy : modifiedNormalForm hk c ε δ y ≤ c - ε) :
    0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
  have hle : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
    (modifiedNormalForm_sublevel_iff hk c ε δ y).1 hy
  by_contra hnot
  have hden : ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε ≤ 0 := le_of_not_gt hnot
  have hpos0 : ‖posPart hk y‖ ^ 2 = 0 := by nlinarith
  have hb0 : posPart hk y = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hpos0)
  have hDnonneg : 0 ≤ modelModifiedDip hk ε δ y := modelModifiedDip_nonneg hk ε δ (le_of_lt hε) y
  have hmu : modMu ε (‖negPart hk y‖ ^ 2) = 3 / 2 * ε := by
    exact modMu_const hε (by nlinarith [hden, hDnonneg])
  have hs : ‖posPart hk y‖ ≤ δ / 2 := by
    rw [hb0]
    exact by
      have hz : (‖(0 : EuclideanSpace ℝ (Fin (n - k)))‖) = 0 := by simp
      rw [hz]
      exact le_of_lt (half_pos hδ)
  have hga : modGamma δ ‖posPart hk y‖ = 1 := modGamma_one hδ hs
  have hden' : ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε =
      ‖negPart hk y‖ ^ 2 + ε := by
    dsimp [modelModifiedDip]
    rw [hmu, hga]
    ring
  nlinarith [hden, hden', sq_nonneg ‖negPart hk y‖]

noncomputable def modelModifiedStretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
      (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε))) • posPart hk y)

theorem modelModifiedStretchMap_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    negPart hk (modelModifiedStretchMap hk ε r δ y) = negPart hk y := by
  dsimp [modelModifiedStretchMap]
  rw [negPart_recombine]

theorem modelModifiedStretchMap_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (y : MorseModel n) :
    posPart hk (modelModifiedStretchMap hk ε r δ y) =
      (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε))) • posPart hk y := by
  dsimp [modelModifiedStretchMap]
  rw [posPart_recombine]

theorem modelModifiedStretchMap_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (y : MorseModel n)
    (hy : modifiedNormalForm hk c ε δ y ≤ c - ε) :
    ‖posPart hk (modelModifiedStretchMap hk ε r δ y)‖ ^ 2 =
      ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2) /
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) := by
  rw [modelModifiedStretchMap_posPart]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt]
  · field_simp
  · have hpos := modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hy
    have hnum : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      nlinarith [sq_nonneg ‖negPart hk y‖, sq_nonneg r]
    exact div_nonneg hnum (le_of_lt hpos)

theorem modelModifiedStretchMap_mem_upper {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ)
    {y : MorseModel n} (hy : modifiedNormalForm hk c ε δ y ≤ c - ε) :
    morseNormalForm hk c (modelModifiedStretchMap hk ε r δ y) ≤ c + r ^ 2 / 2 := by
  have hsq := modelModifiedStretchMap_posPart_norm_sq hk c ε r δ hε hδ y hy
  rw [morseNormalForm_split]
  rw [modelModifiedStretchMap_negPart]
  have hle : ‖posPart hk (modelModifiedStretchMap hk ε r δ y)‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hd : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
      modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hy
    have hnonneg : 0 ≤ ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      nlinarith [sq_nonneg ‖negPart hk y‖, sq_nonneg r]
    have hle' : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
      (modifiedNormalForm_sublevel_iff hk c ε δ y).1 hy
    rw [hsq]
    have hmul : ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2) ≤
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) *
          (‖negPart hk y‖ ^ 2 + r ^ 2) := by
      exact mul_le_mul_of_nonneg_right hle' hnonneg
    rw [div_le_iff₀ hd]
    nlinarith [hmul]
  nlinarith [hle]

theorem modelModifiedStretchMap_boundary {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) {y : MorseModel n}
    (hy : modifiedNormalForm hk c ε δ y = c - ε) :
    morseNormalForm hk c (modelModifiedStretchMap hk ε r δ y) = c + r ^ 2 / 2 := by
  have hmem : modifiedNormalForm hk c ε δ y ≤ c - ε := le_of_eq hy
  have hsq := modelModifiedStretchMap_posPart_norm_sq hk c ε r δ hε hδ y hmem
  rw [morseNormalForm_split]
  rw [modelModifiedStretchMap_negPart]
  have hle' : ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
    have hiff := modifiedNormalForm_sublevel_iff hk c ε δ y
    have hge : ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε ≤
        ‖posPart hk y‖ ^ 2 := by
      rw [modifiedNormalForm_eq_sub_dip, morseNormalForm_split] at hy
      dsimp [modelModifiedDip] at hy ⊢
      nlinarith
    exact le_antisymm (hiff.1 (le_of_eq hy)) hge
  have hd : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
    modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hmem
  have hnorm : ‖posPart hk (modelModifiedStretchMap hk ε r δ y)‖ ^ 2 =
      ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    rw [hsq, hle']
    field_simp [ne_of_gt hd]
  rw [hnorm]
  ring

theorem modelModifiedStretchMap_strict {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : 0 < r ^ 2) {y : MorseModel n}
    (hy : modifiedNormalForm hk c ε δ y < c - ε) :
    morseNormalForm hk c (modelModifiedStretchMap hk ε r δ y) < c + r ^ 2 / 2 := by
  have hmem : modifiedNormalForm hk c ε δ y ≤ c - ε := le_of_lt hy
  have hsq := modelModifiedStretchMap_posPart_norm_sq hk c ε r δ hε hδ y hmem
  rw [morseNormalForm_split]
  rw [modelModifiedStretchMap_negPart]
  have hle' : ‖posPart hk y‖ ^ 2 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
    rw [modifiedNormalForm_eq_sub_dip, morseNormalForm_split] at hy
    dsimp [modelModifiedDip] at hy ⊢
    nlinarith
  have hd : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
    modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hmem
  have hnorm : ‖posPart hk (modelModifiedStretchMap hk ε r δ y)‖ ^ 2 <
      ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    rw [hsq]
    have hpos : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by nlinarith [sq_nonneg ‖negPart hk y‖, hr]
    have hmul : ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2) <
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) *
          (‖negPart hk y‖ ^ 2 + r ^ 2) := by
      exact mul_lt_mul_of_pos_right hle' hpos
    rw [div_lt_iff₀ hd]
    nlinarith [hmul]
  nlinarith [hnorm]

end

end DifferentialGeometry.Topology.Morse.CellAttachment
