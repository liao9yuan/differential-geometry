import DifferentialGeometry.Topology.Morse.CellAttachment
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace DifferentialGeometry.Topology.Morse.CellAttachment

open Filter Set
open scoped Topology BigOperators

noncomputable section

def modMu (ε : ℝ) : ℝ → ℝ := fun t => (3 / 2 * ε) * (1 - Real.smoothTransition ((t - 2 * ε) / (2 * ε)))

def modGamma (δ : ℝ) : ℝ → ℝ := fun s => 1 - Real.smoothTransition ((2 * s - δ) / δ)

theorem modMu_const {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 2 * ε) : modMu ε t = 3 / 2 * ε := by
  dsimp [modMu]
  have h : (t - 2 * ε) / (2 * ε) ≤ 0 := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * ε)]
    nlinarith
  rw [Real.smoothTransition.zero_of_nonpos h]
  ring

theorem modMu_zero {ε t : ℝ} (hε : 0 < ε) (ht : 4 * ε ≤ t) : modMu ε t = 0 := by
  dsimp [modMu]
  have h : 1 ≤ (t - 2 * ε) / (2 * ε) := by
    rw [one_le_div (by positivity : 0 < 2 * ε)]
    nlinarith
  rw [Real.smoothTransition.one_of_one_le h]
  ring

theorem modMu_nonneg {ε t : ℝ} (hε : 0 ≤ ε) : 0 ≤ modMu ε t := by
  dsimp [modMu]
  have h1 : 0 ≤ Real.smoothTransition ((t - 2 * ε) / (2 * ε)) := Real.smoothTransition.nonneg _
  have h2 : Real.smoothTransition ((t - 2 * ε) / (2 * ε)) ≤ 1 := Real.smoothTransition.le_one _
  nlinarith

theorem modMu_antitone {ε : ℝ} (hε : 0 ≤ ε) : AntitoneOn (modMu ε) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  dsimp [modMu]
  have hmono : (fun t : ℝ => Real.smoothTransition ((t - 2 * ε) / (2 * ε))) a ≤
      (fun t : ℝ => Real.smoothTransition ((t - 2 * ε) / (2 * ε))) b := by
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε))
  have hmono' : 1 - Real.smoothTransition ((b - 2 * ε) / (2 * ε)) ≤
      1 - Real.smoothTransition ((a - 2 * ε) / (2 * ε)) := by linarith
  exact mul_le_mul_of_nonneg_left hmono' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) hε)

theorem modGamma_one {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ δ / 2) : modGamma δ s = 1 := by
  dsimp [modGamma]
  have h : (2 * s - δ) / δ ≤ 0 := by
    rw [div_le_iff₀ hδ]
    nlinarith
  rw [Real.smoothTransition.zero_of_nonpos h]
  norm_num

theorem modGamma_zero {δ s : ℝ} (hδ : 0 < δ) (hs : 3 * δ / 2 ≤ s) : modGamma δ s = 0 := by
  dsimp [modGamma]
  have h : 1 ≤ (2 * s - δ) / δ := by
    rw [one_le_div hδ]
    nlinarith
  rw [Real.smoothTransition.one_of_one_le h]
  norm_num

theorem modGamma_nonneg (δ s : ℝ) : 0 ≤ modGamma δ s := by
  dsimp [modGamma]
  have h1 : 0 ≤ Real.smoothTransition ((2 * s - δ) / δ) := Real.smoothTransition.nonneg _
  have h2 : Real.smoothTransition ((2 * s - δ) / δ) ≤ 1 := Real.smoothTransition.le_one _
  nlinarith

theorem modGamma_le_one (δ s : ℝ) : modGamma δ s ≤ 1 := by
  dsimp [modGamma]
  have h1 : 0 ≤ Real.smoothTransition ((2 * s - δ) / δ) := Real.smoothTransition.nonneg _
  nlinarith

theorem modGamma_antitone {δ : ℝ} (hδ : 0 ≤ δ) : AntitoneOn (modGamma δ) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  dsimp [modGamma]
  have hmono : (fun s : ℝ => Real.smoothTransition ((2 * s - δ) / δ)) a ≤
      (fun s : ℝ => Real.smoothTransition ((2 * s - δ) / δ)) b := by
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hδ)
  have hmono' : 1 - Real.smoothTransition ((2 * b - δ) / δ) ≤
      1 - Real.smoothTransition ((2 * a - δ) / δ) := by linarith
  exact hmono'

def modifiedNormalForm {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) : ℝ :=
  morseNormalForm hk c y - modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ (‖posPart hk y‖)

theorem modifiedNormalForm_le_f {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (hε : 0 < ε)
    (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y ≤ morseNormalForm hk c y := by
  dsimp [modifiedNormalForm]
  have h1 : 0 ≤ modMu ε (‖negPart hk y‖ ^ 2) :=
    modMu_nonneg (ε := ε) (t := ‖negPart hk y‖ ^ 2) (le_of_lt hε)
  have h2 : 0 ≤ modGamma δ ‖posPart hk y‖ := modGamma_nonneg δ _
  have h3 : 0 ≤ modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ := mul_nonneg h1 h2
  linarith

theorem modifiedNormalForm_sublevel_upper {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδε : 9 * δ ^ 2 < 4 * ε) :
    {y : MorseModel n | modifiedNormalForm hk c ε δ y ≤ c + ε} =
      {y : MorseModel n | morseNormalForm hk c y ≤ c + ε} := by
  ext y
  constructor
  · intro hy
    by_contra hnot
    have hf : c + ε < morseNormalForm hk c y := lt_of_not_ge hnot
    have hcorr0 : modMu ε (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖ = 0 := by
      by_cases hs : 3 * δ / 2 ≤ ‖posPart hk y‖
      · have hγ : modGamma δ ‖posPart hk y‖ = 0 := modGamma_zero hδ hs
        simp [hγ]
      · have hs' : ‖posPart hk y‖ < 3 * δ / 2 := lt_of_not_ge hs
        have hsq : ‖posPart hk y‖ ^ 2 < ε := by
          have hs'' : ‖posPart hk y‖ ^ 2 < (3 * δ / 2) ^ 2 := by
            apply sq_lt_sq.mpr
            rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : 0 ≤ 3 * δ / 2)]
            exact hs'
          nlinarith [hs'', hδε]
        have hwell : morseNormalForm hk c y < c + ε := by
          have hsplit := morseNormalForm_split hk c y
          rw [hsplit]
          nlinarith [hsq, sq_nonneg ‖negPart hk y‖]
        exact False.elim (not_lt_of_ge hf.le hwell)
    have hg : modifiedNormalForm hk c ε δ y = morseNormalForm hk c y := by
      dsimp [modifiedNormalForm]
      simp [hcorr0]
    exact (not_lt_of_ge hy) (hg ▸ hf)
  · intro hy
    exact le_trans (modifiedNormalForm_le_f hk c ε δ hε y) hy

theorem modifiedNormalForm_cell_mem_lower {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (x : ClosedCell k) :
    modifiedNormalForm hk c ε δ (cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))) ≤
      c - ε := by
  let y : MorseModel n := cellMap hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))
  have hpos : posPart hk y = 0 := by
    ext j
    dsimp [y, posPart]
    exact cellMap_posIdx hk (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k)) j
  have ht : ‖negPart hk y‖ ^ 2 ≤ 2 * ε := by
    have hle : ‖negPart hk y‖ ≤ Real.sqrt (2 * ε) := by
      have hne : negPart hk y = (Real.sqrt (2 * ε)) • (x : EuclideanSpace ℝ (Fin k)) := by
        ext i
        dsimp [y, negPart]
        rw [cellMap_negIdx]
      rw [hne]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_right (Real.sqrt_nonneg _) x.2
    have hsq' : ‖negPart hk y‖ ^ 2 ≤ (Real.sqrt (2 * ε)) ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
        exact hle)
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)] at hsq'
    exact hsq'
  have hμ : modMu ε (‖negPart hk y‖ ^ 2) = 3 / 2 * ε := modMu_const hε ht
  have hγ : modGamma δ ‖posPart hk y‖ = 1 := by
    have hs : ‖posPart hk y‖ ≤ δ / 2 := by
      rw [hpos]
      simp only [norm_zero]
      exact le_of_lt (half_pos hδ)
    exact modGamma_one hδ hs
  have hf : morseNormalForm hk c y ≤ c := by
    dsimp [y]
    rw [morseNormalForm_cellMap hk c (Real.sqrt (2 * ε)) (x : EuclideanSpace ℝ (Fin k))]
    have hsq : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * ε)]
    rw [hsq]
    have hnorm : 0 ≤ ‖(x : EuclideanSpace ℝ (Fin k))‖ ^ 2 := sq_nonneg _
    nlinarith
  dsimp [modifiedNormalForm]
  rw [hμ, hγ]
  nlinarith [hε]

end

end DifferentialGeometry.Topology.Morse.CellAttachment
