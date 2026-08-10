import DifferentialGeometry.Topology.Morse.CellAttachment
import DifferentialGeometry.Topology.Morse.LevelSet
import DifferentialGeometry.Topology.Morse.ModifiedFunction
import Mathlib.Topology.Order.IntermediateValue

namespace DifferentialGeometry.Topology.Morse.CellAttachment

open Set
open Filter

open scoped BigOperators Topology ContDiff

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


def modGammaSqrt (δ : ℝ) (u : ℝ) : ℝ := modGamma δ (Real.sqrt u)

theorem modGammaSqrt_antitone {δ : ℝ} (hδ : 0 ≤ δ) : AntitoneOn (modGammaSqrt δ) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  dsimp [modGammaSqrt]
  exact modGamma_antitone hδ (Real.sqrt_nonneg a) (Real.sqrt_nonneg b) (Real.sqrt_monotone hab)

def modelModifiedFiberDip (ε δ s u : ℝ) : ℝ := modMu ε s * modGammaSqrt δ u

theorem modelModifiedFiberDip_nonneg {ε δ s u : ℝ} (hε : 0 ≤ ε) :
    0 ≤ modelModifiedFiberDip ε δ s u := by
  dsimp [modelModifiedFiberDip]
  exact mul_nonneg (modMu_nonneg hε) (modGamma_nonneg δ (Real.sqrt u))

theorem modelModifiedFiberDip_antitone {ε δ s : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) :
    AntitoneOn (modelModifiedFiberDip ε δ s) (Ici (0 : ℝ)) := by
  intro u hu v hv huv
  dsimp [modelModifiedFiberDip]
  exact mul_le_mul_of_nonneg_left (modGammaSqrt_antitone hδ hu hv huv) (modMu_nonneg hε)

theorem modelModifiedFiberDip_le {ε δ s u : ℝ} (hε : 0 ≤ ε) :
    modelModifiedFiberDip ε δ s u ≤ 3 / 2 * ε := by
  dsimp [modelModifiedFiberDip]
  have h1 : modMu ε s * modGammaSqrt δ u ≤ modMu ε s * 1 := by
    exact mul_le_mul_of_nonneg_left (modGamma_le_one δ (Real.sqrt u)) (modMu_nonneg hε)
  have h2 : modMu ε s ≤ 3 / 2 * ε := modMu_le (ε := ε) (t := s) hε
  nlinarith [h1, h2]

theorem modMu_denom_lower {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) : 0 ≤ s + 2 * modMu ε s - 2 * ε := by
  by_cases hs2 : s ≤ 2 * ε
  · have hmu : modMu ε s = 3 / 2 * ε := modMu_const hε hs2
    rw [hmu]
    nlinarith [hs]
  · have hmu : 0 ≤ modMu ε s := modMu_nonneg (le_of_lt hε)
    nlinarith [hs, hmu]

theorem modelModifiedFiberDip_zero {ε δ s : ℝ} (hδ : 0 < δ) :
    modelModifiedFiberDip ε δ s 0 = modMu ε s := by
  dsimp [modelModifiedFiberDip, modGammaSqrt]
  have hz : Real.sqrt (0 : ℝ) = 0 := by simp
  rw [hz]
  have hg : modGamma δ 0 = 1 := modGamma_one hδ (by positivity)
  rw [hg]
  ring

theorem modelModifiedFiberRoot_exists (ε δ r s w2 : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    ∃ u : ℝ, 0 ≤ u ∧
      u * (s + r ^ 2) = w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) := by
  let F : ℝ → ℝ := fun u => u * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε)
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [hs, hr2]
  have hF0 : F 0 ≤ 0 := by
    dsimp [F]
    rw [modelModifiedFiberDip_zero hδ]
    have hden : 0 ≤ s + 2 * modMu ε s - 2 * ε := modMu_denom_lower hε hs
    nlinarith [hw, hden]
  have hq : 0 ≤ w2 * (s + ε) / (s + r ^ 2) := by
    have hsε : 0 ≤ s + ε := by nlinarith [hs, hε]
    exact div_nonneg (mul_nonneg hw hsε) (le_of_lt hsr)
  obtain ⟨M, hM⟩ := exists_gt (w2 * (s + ε) / (s + r ^ 2))
  let U : ℝ := M + 1
  have hFUp : 0 < F U := by
    dsimp [F, U]
    have hbd : s + 2 * modelModifiedFiberDip ε δ s U - 2 * ε ≤ s + ε := by
      have hDle : modelModifiedFiberDip ε δ s U ≤ 3 / 2 * ε := modelModifiedFiberDip_le (le_of_lt hε)
      nlinarith
    have hstep : w2 * (s + ε) < M * (s + r ^ 2) := (div_lt_iff₀ hsr).mp hM
    have h1 : (M + 1) * (s + r ^ 2) - w2 * (s + ε) > 0 := by nlinarith [hstep, hsr]
    nlinarith [hbd, h1]
  have hcont : ContinuousOn F (Icc 0 U) := by
    have hcd : Continuous (fun u : ℝ => modelModifiedFiberDip ε δ s u) := by
      dsimp [modelModifiedFiberDip, modGammaSqrt]
      have hc1 : Continuous (fun u : ℝ => modMu ε s) := continuous_const
      have hc2 : Continuous (fun u : ℝ => modGamma δ (Real.sqrt u)) :=
        (contDiff_modGamma (δ := δ)).continuous.comp Real.continuous_sqrt
      exact hc1.mul hc2
    dsimp [F]
    fun_prop
  have himg : (0 : ℝ) ∈ F '' Icc 0 U := by
    have hUpos : 0 < U := by
      dsimp [U]
      have hMpos : 0 < M := lt_of_le_of_lt hq hM
      linarith
    exact intermediate_value_Icc (le_of_lt hUpos) hcont ⟨hF0, le_of_lt hFUp⟩
  rcases himg with ⟨u, hu, hFu⟩
  refine ⟨u, hu.1, ?_⟩
  dsimp [F] at hFu
  linarith

theorem modelModifiedFiberRoot_unique (ε δ r s w2 : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu' : u * (s + r ^ 2) = w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε))
    (hv' : v * (s + r ^ 2) = w2 * (s + 2 * modelModifiedFiberDip ε δ s v - 2 * ε)) :
    u = v := by
  by_contra huv
  have hlt := lt_or_gt_of_ne huv
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [hs, hr2]
  rcases hlt with hlt | hgt
  · have hmono : u * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) <
      v * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s v - 2 * ε) := by
      have hD : modelModifiedFiberDip ε δ s v ≤ modelModifiedFiberDip ε δ s u :=
        modelModifiedFiberDip_antitone (le_of_lt hε) (le_of_lt hδ) hu hv (le_of_lt hlt)
      have hd : 0 < (v - u) * (s + r ^ 2) := mul_pos (sub_pos.mpr hlt) hsr
      nlinarith
    have heq : u * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) =
        v * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s v - 2 * ε) := by
      rw [hu', hv']
      ring
    exact (not_lt_of_ge (le_of_eq heq.symm)) hmono
  · have hmono : v * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s v - 2 * ε) <
      u * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) := by
      have hD : modelModifiedFiberDip ε δ s u ≤ modelModifiedFiberDip ε δ s v :=
        modelModifiedFiberDip_antitone (le_of_lt hε) (le_of_lt hδ) hv hu (le_of_lt hgt)
      have hd : 0 < (u - v) * (s + r ^ 2) := mul_pos (sub_pos.mpr hgt) hsr
      nlinarith
    have heq : v * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s v - 2 * ε) =
        u * (s + r ^ 2) - w2 * (s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) := by
      rw [hv', hu']
      ring
    exact (not_lt_of_ge (le_of_eq heq.symm)) hmono

noncomputable def modelModifiedFiberRoot (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    (s w2 : ℝ) : ℝ :=
  if hs₀ : 0 ≤ s then
    if hw₀ : 0 ≤ w2 then
      Classical.choose (modelModifiedFiberRoot_exists ε δ r s w2 hε hδ hr hs₀ hw₀)
    else 0
  else 0

theorem modelModifiedFiberRoot_nonneg {ε δ r s w2 : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    0 ≤ modelModifiedFiberRoot ε δ r hε hδ hr s w2 := by
  rw [modelModifiedFiberRoot, dif_pos hs, dif_pos hw]
  exact (Classical.choose_spec (modelModifiedFiberRoot_exists ε δ r s w2 hε hδ hr hs hw)).1

theorem modelModifiedFiberRoot_eq {ε δ r s w2 : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) =
      w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε) := by
  rw [modelModifiedFiberRoot, dif_pos hs, dif_pos hw]
  exact (Classical.choose_spec (modelModifiedFiberRoot_exists ε δ r s w2 hε hδ hr hs hw)).2



noncomputable def modelModifiedUnstretchFactor (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (s w2 : ℝ) : ℝ :=
  Real.sqrt ((s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2)
      - 2 * ε) / (s + r ^ 2))

noncomputable def modelModifiedUnstretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) (y : MorseModel n) : MorseModel n :=
  recombine hk (negPart hk y)
    ((modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) • posPart hk y)

theorem modelModifiedUnstretchMap_negPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) (y : MorseModel n) :
    negPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) = negPart hk y := by
  dsimp [modelModifiedUnstretchMap]
  rw [negPart_recombine]

theorem modelModifiedUnstretchMap_posPart {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) (y : MorseModel n) :
    posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) =
      (modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) • posPart hk y := by
  dsimp [modelModifiedUnstretchMap]
  rw [posPart_recombine]

theorem modelModifiedDip_eq_fiber {n k : ℕ} (hk : k ≤ n) (ε δ : ℝ) (y : MorseModel n) :
    modelModifiedDip hk ε δ y = modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) := by
  dsimp [modelModifiedDip, modelModifiedFiberDip, modGammaSqrt]
  congr 1
  rw [Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg (norm_nonneg _)]


theorem modifiedSublevel_norm_sq_le {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (hε : 0 ≤ ε) {z : MorseModel n} (hz : modifiedNormalForm hk c ε δ z ≤ c - ε) :
    morseNorm n z ^ 2 ≤ 2 * ‖negPart hk z‖ ^ 2 + ε := by
  have hpos : ‖posPart hk z‖ ^ 2 ≤ ‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε :=
    (modifiedNormalForm_sublevel_iff hk c ε δ z).1 hz
  have hdip : modelModifiedDip hk ε δ z ≤ 3 / 2 * ε := by
    rw [modelModifiedDip_eq_fiber]
    exact modelModifiedFiberDip_le hε
  have hnorm : morseNorm n z ^ 2 = ‖negPart hk z‖ ^ 2 + ‖posPart hk z‖ ^ 2 := by
    calc
      morseNorm n z ^ 2 = morseNorm n (recombine hk (negPart hk z) (posPart hk z)) ^ 2 := by
        rw [recombine_decompose hk z]
      _ = ‖negPart hk z‖ ^ 2 + ‖posPart hk z‖ ^ 2 :=
        morseNorm_recombine_sq hk (negPart hk z) (posPart hk z)
  nlinarith [hpos, hdip, hnorm]


theorem modelModifiedFiberDenom_root_nonneg {ε δ r s w2 : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    0 ≤ s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2)
      - 2 * ε := by
  by_cases hu : modelModifiedFiberRoot ε δ r hε hδ hr s w2 = 0
  · rw [hu]
    have hg0 : modGammaSqrt δ 0 = 1 := by
      dsimp [modGammaSqrt]
      have hz : Real.sqrt (0 : ℝ) = 0 := by simp
      rw [hz]
      exact modGamma_one hδ (le_of_lt (half_pos hδ))
    have hmu : 0 ≤ modMu ε s := modMu_nonneg (le_of_lt hε)
    have hga : 0 ≤ modGammaSqrt δ 0 := modGamma_nonneg δ (Real.sqrt 0)
    have hd : 0 ≤ s + 2 * modMu ε s - 2 * ε := modMu_denom_lower hε hs
    dsimp [modelModifiedFiberDip]
    rw [hg0]
    nlinarith [hmu, hd]
  · have hpos : 0 < modelModifiedFiberRoot ε δ r hε hδ hr s w2 :=
      lt_of_le_of_ne (modelModifiedFiberRoot_nonneg (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw) (Ne.symm hu)
    have hroot' := modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw
    have hsr : 0 < s + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [hs, hr2]
    have hmul : 0 ≤ modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) :=
      mul_nonneg (le_of_lt hpos) (le_of_lt hsr)
    have hrew : modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) =
        w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2)
          - 2 * ε) := by
      simpa [modelModifiedFiberDip] using hroot'
    nlinarith [hmul, hrew, hw]

theorem modelModifiedUnstretchMap_posPart_norm_sq {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) (y : MorseModel n) :
    ‖posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)‖ ^ 2 =
      ‖posPart hk y‖ ^ 2 *
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
          (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε) /
        (‖negPart hk y‖ ^ 2 + r ^ 2) := by
  dsimp [modelModifiedUnstretchMap, modelModifiedUnstretchFactor]
  rw [posPart_recombine]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow]
  rw [Real.sq_sqrt]
  · field_simp
  · have hsr : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [sq_nonneg ‖negPart hk y‖, hr2]
    have hden : 0 ≤ ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
        (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε :=
      modelModifiedFiberDenom_root_nonneg hε hδ hr (sq_nonneg ‖negPart hk y‖)
        (sq_nonneg ‖posPart hk y‖)
    exact div_nonneg hden (le_of_lt hsr)

theorem modelModifiedUnstretchMap_mem_modified {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    {y : MorseModel n} (hy : morseNormalForm hk c y ≤ c + r ^ 2 / 2) :
    modifiedNormalForm hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) ≤ c - ε := by
  set s : ℝ := ‖negPart hk y‖ ^ 2 with hs_def
  set w2 : ℝ := ‖posPart hk y‖ ^ 2 with hw2_def
  set u : ℝ := modelModifiedFiberRoot ε δ r hε hδ hr s w2 with hu_def
  set D : ℝ := s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε with hD_def
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    rw [hs_def]
    nlinarith [hr2]
  have hroot' : u * (s + r ^ 2) = w2 * D := by
    rw [hu_def, hD_def]
    simpa using (modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2)
      hε hδ hr (by rw [hs_def]; exact sq_nonneg _) (by rw [hw2_def]; exact sq_nonneg _))
  have hw2le : w2 ≤ s + r ^ 2 := by
    rw [hs_def, hw2_def]
    rw [morseNormalForm_split] at hy
    nlinarith
  have hD0 : 0 ≤ D := by
    rw [hD_def]
    simpa using (modelModifiedFiberDenom_root_nonneg hε hδ hr (by rw [hs_def]; exact sq_nonneg _)
      (by rw [hw2_def]; exact sq_nonneg _))
  have huleD : u ≤ D := by
    have hmul : u * (s + r ^ 2) ≤ D * (s + r ^ 2) := by
      rw [hroot']
      calc
        w2 * D ≤ (s + r ^ 2) * D := mul_le_mul_of_nonneg_right hw2le hD0
        _ = D * (s + r ^ 2) := by ring
    exact (mul_le_mul_iff_of_pos_right hsr).mp hmul
  have hsq' : ‖posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)‖ ^ 2 = u := by
    rw [modelModifiedUnstretchMap_posPart_norm_sq]
    have hdiv : w2 * D / (s + r ^ 2) = u := by
      rw [← hroot']
      field_simp [ne_of_gt hsr]
    simpa [hs_def, hw2_def, hD_def, hu_def] using hdiv
  exact (modifiedNormalForm_sublevel_iff hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)).2 (by
    rw [modelModifiedDip_eq_fiber]
    rw [modelModifiedUnstretchMap_negPart]
    rw [hsq']
    rw [← hs_def]
    exact huleD)



theorem modifiedNormalForm_eq_iff {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y = c - ε ↔
      ‖posPart hk y‖ ^ 2 = ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
  rw [modifiedNormalForm_eq_sub_dip]
  rw [morseNormalForm_split]
  dsimp [modelModifiedDip]
  constructor <;> intro h <;> nlinarith

theorem modifiedNormalForm_lt_iff {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ) (y : MorseModel n) :
    modifiedNormalForm hk c ε δ y < c - ε ↔
      ‖posPart hk y‖ ^ 2 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε := by
  rw [modifiedNormalForm_eq_sub_dip]
  rw [morseNormalForm_split]
  dsimp [modelModifiedDip]
  constructor <;> intro h <;> nlinarith

theorem modelModifiedFiberDenom_root_pos {ε δ r s w2 : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    0 < s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2)
      - 2 * ε := by
  have hroot_nonneg := modelModifiedFiberRoot_nonneg (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw
  by_cases hu : modelModifiedFiberRoot ε δ r hε hδ hr s w2 = 0
  · rw [hu]
    have hg0 : modGammaSqrt δ 0 = 1 := by
      dsimp [modGammaSqrt]
      have hz : Real.sqrt (0 : ℝ) = 0 := by simp
      rw [hz]
      exact modGamma_one hδ (le_of_lt (half_pos hδ))
    have hmain : 0 < s + 2 * modMu ε s - 2 * ε := by
      by_cases hs2 : s ≤ 2 * ε
      · have hmu : modMu ε s = 3 / 2 * ε := modMu_const hε hs2
        rw [hmu]
        nlinarith [hs]
      · have hgt : 2 * ε < s := lt_of_not_ge hs2
        have hmu : 0 ≤ modMu ε s := modMu_nonneg (le_of_lt hε)
        nlinarith [hmu]
    dsimp [modelModifiedFiberDip]
    rw [hg0]
    nlinarith [hmain]
  · have hpos : 0 < modelModifiedFiberRoot ε δ r hε hδ hr s w2 :=
      lt_of_le_of_ne hroot_nonneg (Ne.symm hu)
    have hroot' := modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw
    have hsr : 0 < s + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [hs, hr2]
    have hden_nonneg : 0 ≤ s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε :=
      modelModifiedFiberDenom_root_nonneg hε hδ hr hs hw
    have hw2pos : 0 < w2 := by
      by_contra hw0
      have hw2le : w2 ≤ 0 := le_of_not_gt hw0
      have hz : w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε) = 0 := by
        have hmul : w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε) ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg hw2le hden_nonneg
        have hge : 0 ≤ w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε) := by
          exact mul_nonneg hw hden_nonneg
        exact le_antisymm hmul hge
      have hz' : modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) = 0 := by
        rw [hroot']
        exact hz
      have hz'' : modelModifiedFiberRoot ε δ r hε hδ hr s w2 = 0 := by
        exact (mul_eq_zero.mp hz').resolve_right (ne_of_gt hsr)
      exact hu hz''
    have hden : 0 < s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε := by
      have heq : modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) =
          w2 * (s + 2 * modelModifiedFiberDip ε δ s (modelModifiedFiberRoot ε δ r hε hδ hr s w2) - 2 * ε) := hroot'
      have hmul : 0 < modelModifiedFiberRoot ε δ r hε hδ hr s w2 * (s + r ^ 2) :=
        mul_pos hpos hsr
      rw [heq] at hmul
      exact (pos_of_mul_pos_right hmul (le_of_lt hw2pos))
    exact hden

theorem modelModifiedUnstretchMap_boundary {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    {y : MorseModel n} (hy : morseNormalForm hk c y = c + r ^ 2 / 2) :
    modifiedNormalForm hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) = c - ε := by
  set s : ℝ := ‖negPart hk y‖ ^ 2 with hs_def
  set w2 : ℝ := ‖posPart hk y‖ ^ 2 with hw2_def
  set u : ℝ := modelModifiedFiberRoot ε δ r hε hδ hr s w2 with hu_def
  set D : ℝ := s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε with hD_def
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    rw [hs_def]
    nlinarith [hr2]
  have hroot' : u * (s + r ^ 2) = w2 * D := by
    rw [hu_def, hD_def]
    simpa using (modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2)
      hε hδ hr (by rw [hs_def]; exact sq_nonneg _) (by rw [hw2_def]; exact sq_nonneg _))
  have hw2eq : w2 = s + r ^ 2 := by
    rw [hs_def, hw2_def]
    rw [morseNormalForm_split] at hy
    nlinarith
  have hEqD : u = D := by
    have hmul : u * (s + r ^ 2) = D * (s + r ^ 2) := by
      rw [hroot', hw2eq]
      ring
    exact (mul_right_cancel₀ (ne_of_gt hsr)) hmul
  have hsq' : ‖posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)‖ ^ 2 = u := by
    rw [modelModifiedUnstretchMap_posPart_norm_sq]
    have hdiv : w2 * D / (s + r ^ 2) = u := by
      rw [← hroot']
      field_simp [ne_of_gt hsr]
    simpa [hs_def, hw2_def, hD_def, hu_def] using hdiv
  exact (modifiedNormalForm_eq_iff hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)).2 (by
    rw [modelModifiedDip_eq_fiber]
    rw [modelModifiedUnstretchMap_negPart]
    rw [hsq']
    rw [← hs_def]
    exact hEqD)

theorem modelModifiedUnstretchMap_strict {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    {y : MorseModel n} (hy : morseNormalForm hk c y < c + r ^ 2 / 2) :
    modifiedNormalForm hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) < c - ε := by
  set s : ℝ := ‖negPart hk y‖ ^ 2 with hs_def
  set w2 : ℝ := ‖posPart hk y‖ ^ 2 with hw2_def
  set u : ℝ := modelModifiedFiberRoot ε δ r hε hδ hr s w2 with hu_def
  set D : ℝ := s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε with hD_def
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    rw [hs_def]
    nlinarith [hr2]
  have hroot' : u * (s + r ^ 2) = w2 * D := by
    rw [hu_def, hD_def]
    simpa using (modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2)
      hε hδ hr (by rw [hs_def]; exact sq_nonneg _) (by rw [hw2_def]; exact sq_nonneg _))
  have hw2lt : w2 < s + r ^ 2 := by
    rw [hs_def, hw2_def]
    rw [morseNormalForm_split] at hy
    nlinarith
  have hDpos : 0 < D := by
    rw [hD_def]
    simpa using (modelModifiedFiberDenom_root_pos hε hδ hr (by rw [hs_def]; exact sq_nonneg _)
      (by rw [hw2_def]; exact sq_nonneg _))
  have hltD : u < D := by
    have hmul : u * (s + r ^ 2) < D * (s + r ^ 2) := by
      rw [hroot']
      calc
        w2 * D < (s + r ^ 2) * D := mul_lt_mul_of_pos_right hw2lt hDpos
        _ = D * (s + r ^ 2) := by ring
    exact (mul_lt_mul_iff_of_pos_right hsr).mp hmul
  have hsq' : ‖posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)‖ ^ 2 = u := by
    rw [modelModifiedUnstretchMap_posPart_norm_sq]
    have hdiv : w2 * D / (s + r ^ 2) = u := by
      rw [← hroot']
      field_simp [ne_of_gt hsr]
    simpa [hs_def, hw2_def, hD_def, hu_def] using hdiv
  exact (modifiedNormalForm_lt_iff hk c ε δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y)).2 (by
    rw [modelModifiedDip_eq_fiber]
    rw [modelModifiedUnstretchMap_negPart]
    rw [hsq']
    rw [← hs_def]
    exact hltD)




theorem sqrt_div_mul_sqrt_rev {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a / b) * Real.sqrt (b / a) = 1 := by
  have h1 : 0 ≤ a / b := div_nonneg (le_of_lt ha) (le_of_lt hb)
  rw [← Real.sqrt_mul h1]
  have hprod : (a / b) * (b / a) = 1 := by field_simp [ne_of_gt ha, ne_of_gt hb]
  rw [hprod, Real.sqrt_one]

theorem modelModifiedUnstretchFactor_of_root {ε δ r s w2 u : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0)
    (hroot : modelModifiedFiberRoot ε δ r hε hδ hr s w2 = u) :
    modelModifiedUnstretchFactor ε δ r hε hδ hr s w2 =
      Real.sqrt ((s + 2 * modelModifiedFiberDip ε δ s u - 2 * ε) / (s + r ^ 2)) := by
  dsimp [modelModifiedUnstretchFactor]
  rw [hroot]

theorem modelModifiedUnstretchMap_stretchMap {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    {y : MorseModel n} (hy : modifiedNormalForm hk c ε δ y ≤ c - ε) :
    modelModifiedUnstretchMap hk ε r δ hε hδ hr (modelModifiedStretchMap hk ε r δ y) = y := by
  let z : MorseModel n := modelModifiedStretchMap hk ε r δ y
  have hzneg : negPart hk z = negPart hk y := modelModifiedStretchMap_negPart hk ε r δ y
  have hd : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε :=
    modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hy
  have hsr : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [hr2, sq_nonneg ‖negPart hk y‖]
  have hdeq : ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε =
      ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)
        - 2 * ε := by
    rw [modelModifiedDip_eq_fiber]
  have hroot : modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2)
      (‖posPart hk z‖ ^ 2) = ‖posPart hk y‖ ^ 2 := by
    have hsqz := modelModifiedStretchMap_posPart_norm_sq hk c ε r δ hε hδ y hy
    have hrootEq2 : ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2) =
        ‖posPart hk z‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
          (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε) := by
      calc
        ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2)
            = (‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + r ^ 2) /
                (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε)) *
                (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) := by
              field_simp [ne_of_gt hd]
        _ = ‖posPart hk z‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) := by
              rw [hsqz]
        _ = ‖posPart hk z‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
              (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε) := by
              rw [hdeq]
    exact modelModifiedFiberRoot_unique ε δ r (‖negPart hk y‖ ^ 2) (‖posPart hk z‖ ^ 2)
      hε hδ hr (sq_nonneg _) (sq_nonneg _)
      (modelModifiedFiberRoot_nonneg (ε := ε) (δ := δ) (r := r) (s := ‖negPart hk y‖ ^ 2)
        (w2 := ‖posPart hk z‖ ^ 2) hε hδ hr (sq_nonneg _) (sq_nonneg _))
      (sq_nonneg _)
      (modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := ‖negPart hk y‖ ^ 2)
        (w2 := ‖posPart hk z‖ ^ 2) hε hδ hr (sq_nonneg _) (sq_nonneg _))
      hrootEq2
  calc
    modelModifiedUnstretchMap hk ε r δ hε hδ hr z
        = recombine hk (negPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr z))
            (posPart hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr z)) :=
      (recombine_decompose hk (modelModifiedUnstretchMap hk ε r δ hε hδ hr z)).symm
    _ = recombine hk (negPart hk y) (posPart hk y) := by
      congr 1
      · rw [modelModifiedUnstretchMap_negPart, hzneg]
      · rw [modelModifiedUnstretchMap_posPart]
        rw [hzneg]
        have hfactor : modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk y‖ ^ 2)
            (‖posPart hk z‖ ^ 2) =
            Real.sqrt ((‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
              (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε) / (‖negPart hk y‖ ^ 2 + r ^ 2)) := by
          exact modelModifiedUnstretchFactor_of_root hε hδ hr hroot
        rw [hfactor]
        rw [modelModifiedStretchMap_posPart]
        rw [hdeq]
        rw [smul_smul]
        have hDpos' : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
            (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε := by
          simpa [hdeq] using hd
        have hscalar : Real.sqrt ((‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
              (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
            Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / (‖negPart hk y‖ ^ 2 + 2 *
              modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε)) = 1 :=
          sqrt_div_mul_sqrt_rev hDpos' hsr
        calc
          (Real.sqrt ((‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
                (‖posPart hk y‖ ^ 2) - 2 * ε) / (‖negPart hk y‖ ^ 2 + r ^ 2)) *
            Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / (‖negPart hk y‖ ^ 2 + 2 *
                modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) - 2 * ε))) •
              posPart hk y
              = (1 : ℝ) • posPart hk y := congrArg (fun t : ℝ => t • posPart hk y) hscalar
          _ = posPart hk y := by simp
    _ = y := recombine_decompose hk y


theorem modelModifiedStretchMap_unstretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    (y : MorseModel n) :
    modelModifiedStretchMap hk ε r δ (modelModifiedUnstretchMap hk ε r δ hε hδ hr y) = y := by
  let z : MorseModel n := modelModifiedUnstretchMap hk ε r δ hε hδ hr y
  have hzneg : negPart hk z = negPart hk y := modelModifiedUnstretchMap_negPart hk ε r δ hε hδ hr y
  have hsr : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [hr2, sq_nonneg ‖negPart hk y‖]
  have hroot' : modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) * (‖negPart hk y‖ ^ 2 + r ^ 2) =
      ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
        (‖negPart hk y‖ ^ 2)
        (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε) :=
    modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := ‖negPart hk y‖ ^ 2)
      (w2 := ‖posPart hk y‖ ^ 2) hε hδ hr (sq_nonneg ‖negPart hk y‖)
      (sq_nonneg ‖posPart hk y‖)
  have hDpos : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
      (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε :=
    modelModifiedFiberDenom_root_pos hε hδ hr (sq_nonneg ‖negPart hk y‖)
      (sq_nonneg ‖posPart hk y‖)
  have hsqz : ‖posPart hk z‖ ^ 2 =
      modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) := by
    dsimp [z]
    rw [modelModifiedUnstretchMap_posPart_norm_sq]
    have hdiv : ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
          (‖negPart hk y‖ ^ 2)
          (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε) /
          (‖negPart hk y‖ ^ 2 + r ^ 2) =
        modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) := by
      rw [← hroot']
      field_simp [ne_of_gt hsr]
    exact hdiv
  have hDpos : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
      (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε :=
    modelModifiedFiberDenom_root_pos hε hδ hr (sq_nonneg ‖negPart hk y‖)
      (sq_nonneg ‖posPart hk y‖)
  have hsqz : ‖posPart hk z‖ ^ 2 =
      modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) := by
    dsimp [z]
    rw [modelModifiedUnstretchMap_posPart_norm_sq]
    have hdiv : ‖posPart hk y‖ ^ 2 * (‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ
          (‖negPart hk y‖ ^ 2)
          (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε) /
          (‖negPart hk y‖ ^ 2 + r ^ 2) =
        modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2) := by
      rw [← hroot']
      field_simp [ne_of_gt hsr]
    exact hdiv
  calc
    modelModifiedStretchMap hk ε r δ z
        = recombine hk (negPart hk (modelModifiedStretchMap hk ε r δ z))
            (posPart hk (modelModifiedStretchMap hk ε r δ z)) :=
      (recombine_decompose hk (modelModifiedStretchMap hk ε r δ z)).symm
    _ = recombine hk (negPart hk y) (posPart hk y) := by
      congr 1
      · rw [modelModifiedStretchMap_negPart, hzneg]
      · rw [modelModifiedStretchMap_posPart]
        rw [modelModifiedUnstretchMap_posPart]
        rw [hzneg]
        rw [modelModifiedDip_eq_fiber]
        rw [hzneg]
        rw [hsqz]
        rw [smul_smul]
        dsimp [modelModifiedUnstretchFactor]
        set D : ℝ := ‖negPart hk y‖ ^ 2 + 2 * modelModifiedFiberDip ε δ (‖negPart hk y‖ ^ 2)
            (modelModifiedFiberRoot ε δ r hε hδ hr (‖negPart hk y‖ ^ 2) (‖posPart hk y‖ ^ 2)) - 2 * ε with hD_def
        have hDpos' : 0 < D := by
          rw [hD_def]
          exact hDpos
        have hscalar2 : Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / D) *
            Real.sqrt (D / (‖negPart hk y‖ ^ 2 + r ^ 2)) = 1 :=
          sqrt_div_mul_sqrt_rev hsr hDpos'
        calc
          (Real.sqrt ((‖negPart hk y‖ ^ 2 + r ^ 2) / D) *
            Real.sqrt (D / (‖negPart hk y‖ ^ 2 + r ^ 2))) • posPart hk y
              = (1 : ℝ) • posPart hk y := congrArg (fun t : ℝ => t • posPart hk y) hscalar2
          _ = posPart hk y := by simp
    _ = y := recombine_decompose hk y





theorem recombine_contDiff_generic {n k : ℕ} (hk : k ≤ n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2) := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i.val < k
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2 i) = fun p => p.1 ⟨i.val, hi⟩ := by
      funext p
      dsimp [recombine]
      rw [dif_pos hi]
    rw [hcomp]
    fun_prop
  · have hcomp : (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2 i) = fun p => p.2 ⟨i.val - k, by
          have hkle : k ≤ i.val := le_of_not_gt hi
          have hi' : i.val < n := i.isLt
          omega⟩ := by
      funext p
      dsimp [recombine]
      rw [dif_neg hi]
    rw [hcomp]
    fun_prop

theorem contDiffAt_modelModifiedStretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (hδ : 0 < δ) (hr : r ≠ 0)
    {y : MorseModel n} (hy : 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) :
    ContDiffAt ℝ (⊤ : ℕ∞) (modelModifiedStretchMap hk ε r δ) y := by
  change ContDiffAt ℝ (⊤ : ℕ∞)
    (fun z : MorseModel n => recombine hk (negPart hk z)
      ((Real.sqrt ((‖negPart hk z‖ ^ 2 + r ^ 2) /
        (‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε))) • posPart hk z)) y
  have hnum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => ‖negPart hk z‖ ^ 2 + r ^ 2) y := by
    have hns : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) :=
      ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
    exact (hns.contDiffAt.add (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _ : MorseModel n => r ^ 2) y))
  have hdipG : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => modelModifiedDip hk ε δ z) := by
    have hmu : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : MorseModel n => modMu ε (‖negPart hk z‖ ^ 2)) := by
      have hns : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) :=
        ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
      simpa [Function.comp_def] using (ContDiff.comp (contDiff_modMu (ε := ε)) hns)
    have hga : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => modGamma δ ‖posPart hk z‖) :=
      contDiff_modGamma_norm hk δ hδ
    simpa [modelModifiedDip] using hmu.mul hga
  have hden : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => ‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε) y := by
    have hns : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) :=
      ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
    have hdenG : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : MorseModel n => ‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε) := by
      exact (hns.add ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => (2 : ℝ))).mul hdipG)).sub
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => 2 * ε))
    exact hdenG.contDiffAt
  have hden0 : (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) ≠ 0 := ne_of_gt hy
  have hratio : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => (‖negPart hk z‖ ^ 2 + r ^ 2) /
        (‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε)) y :=
    ContDiffAt.div hnum hden hden0
  have hratio0 : 0 < (‖negPart hk y‖ ^ 2 + r ^ 2) /
      (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε) := by
    have hnum0 : 0 < ‖negPart hk y‖ ^ 2 + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [sq_nonneg ‖negPart hk y‖, hr2]
    exact div_pos hnum0 hy
  have hsqrtAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt t)
      ((‖negPart hk y‖ ^ 2 + r ^ 2) /
        (‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε)) :=
    (Real.deriv_sqrt_aux (ne_of_gt hratio0)).2 (⊤ : ℕ∞)
  have hfactor : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => Real.sqrt ((‖negPart hk z‖ ^ 2 + r ^ 2) /
        (‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε))) y :=
    ContDiffAt.comp y hsqrtAt hratio
  have hneg : ContDiffAt ℝ (⊤ : ℕ∞) (negPart hk) y :=
    (negPartCLM hk).contDiff.contDiffAt
  have hpos : ContDiffAt ℝ (⊤ : ℕ∞) (posPart hk) y :=
    (posPartCLM hk).contDiff.contDiffAt
  have hsmul : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => (Real.sqrt ((‖negPart hk z‖ ^ 2 + r ^ 2) /
        (‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε))) • posPart hk z) y :=
    ContDiffAt.smul hfactor hpos
  have hrec : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2) := recombine_contDiff_generic hk
  have hpair2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => (negPart hk z, (Real.sqrt ((‖negPart hk z‖ ^ 2 + r ^ 2) /
        (‖negPart hk z‖ ^ 2 + 2 * modelModifiedDip hk ε δ z - 2 * ε))) • posPart hk z)) y :=
    hneg.prodMk hsmul
  exact ContDiffAt.comp y (ContDiff.contDiffAt hrec) hpair2

theorem contDiffOn_modelModifiedStretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ) (hδ : 0 < δ) (hr : r ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (modelModifiedStretchMap hk ε r δ)
      {y : MorseModel n | 0 < ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε} := by
  intro y hy
  exact (contDiffAt_modelModifiedStretchMap hk ε r δ hδ hr hy).contDiffWithinAt



theorem contMDiff_modelModifiedStretchMap_sublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
      sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
        (contDiff_modifiedNormalForm hk c ε δ hδ)
        (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
          ⟨le_of_eq hy.symm, by linarith⟩))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
        (contDiff_morseNormalForm hk c)
        (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hchart₁ : ∀ y : SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε),
      hcs₁.chartAt y =
        (if h : modifiedNormalForm hk c ε δ y.1 = c - ε then
          sublevelBoundaryChart (modifiedNormalForm hk c ε δ) (c - ε) y h
            (contDiff_modifiedNormalForm hk c ε δ hδ)
            (modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
              ⟨le_of_eq h.symm, by linarith⟩)
        else sublevelInteriorChart (modifiedNormalForm hk c ε δ) (c - ε) y
          (lt_of_le_of_ne (show modifiedNormalForm hk c ε δ y.1 ≤ c - ε from y.2) h)
          (contDiff_modifiedNormalForm hk c ε δ hδ)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₂.chartAt y =
        (if h : morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (contDiff_morseNormalForm hk c)
            (fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (contDiff_morseNormalForm hk c)) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε) =>
        (⟨modelModifiedStretchMap hk ε r δ y.1,
          modelModifiedStretchMap_mem_upper hk c ε r δ hε hδ y.2⟩ :
          SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2))) := by
  let denomFun : MorseModel (m + 1) → ℝ :=
    fun y => ‖negPart hk y‖ ^ 2 + 2 * modelModifiedDip hk ε δ y - 2 * ε
  let U : Set (MorseModel (m + 1)) := {y | 0 < denomFun y}
  have hUopen : IsOpen U := by
    have hden : ContDiff ℝ (⊤ : ℕ∞) denomFun := by
      have hns : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => ‖negPart hk y‖ ^ 2) :=
        ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
      have hdipG : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => modelModifiedDip hk ε δ y) := by
        have hmu : ContDiff ℝ (⊤ : ℕ∞)
            (fun y : MorseModel (m + 1) => modMu ε (‖negPart hk y‖ ^ 2)) := by
          have hns' : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => ‖negPart hk y‖ ^ 2) :=
            ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
          simpa [Function.comp_def] using (ContDiff.comp (contDiff_modMu (ε := ε)) hns')
        have hga : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => modGamma δ ‖posPart hk y‖) :=
          contDiff_modGamma_norm hk δ hδ
        simpa [modelModifiedDip] using hmu.mul hga
      exact (hns.add ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel (m + 1) => (2 : ℝ))).mul hdipG)).sub
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel (m + 1) => 2 * ε))
    change IsOpen {y : MorseModel (m + 1) | 0 < denomFun y}
    exact isOpen_lt continuous_const hden.continuous
  have hUsub : ∀ y : MorseModel (m + 1), modifiedNormalForm hk c ε δ y ≤ c - ε → y ∈ U := by
    intro y hy
    dsimp [U]
    exact modelModifiedDip_sublevel_denom_pos hk c ε δ hε hδ hy
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (modelModifiedStretchMap hk ε r δ) U := by
    exact contDiffOn_modelModifiedStretchMap hk ε r δ hδ hr
  exact contMDiff_sublevelMap_on (m := m) (modifiedNormalForm hk c ε δ) (morseNormalForm hk c)
    (c - ε) (c + r ^ 2 / 2)
    (contDiff_modifiedNormalForm hk c ε δ hδ) (contDiff_morseNormalForm hk c)
    (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
      ⟨le_of_eq hy.symm, by linarith⟩)
    (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
    (modelModifiedStretchMap hk ε r δ) U hUopen hUsub hΦ
    (fun y hy => modelModifiedStretchMap_mem_upper hk c ε r δ hε hδ hy)
    (fun y hy => modelModifiedStretchMap_boundary hk c ε r δ hε hδ hy)
    (fun y hy => modelModifiedStretchMap_strict hk c ε r δ hε hδ (sq_pos_of_ne_zero hr) hy)
    (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)



theorem contDiff_modGammaSqrt {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ (⊤ : ℕ∞) (modGammaSqrt δ) := by
  let s : Set ℝ := {u | u < δ ^ 2 / 4}
  let t : Set ℝ := {u | 0 < u}
  have hconstOn : ContDiffOn ℝ (⊤ : ℕ∞) (modGammaSqrt δ) s := by
    rintro u hu
    have hconst : (fun z : ℝ => modGammaSqrt δ z) =ᶠ[nhds u] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_lt continuous_id (continuous_const : Continuous fun _ : ℝ => δ ^ 2 / 4) |>.mem_nhds hu] with z hz
      dsimp [modGammaSqrt]
      have hz' : Real.sqrt z ≤ δ / 2 := by
        have hsq : (Real.sqrt z) ^ 2 ≤ (δ / 2) ^ 2 := by
          have hz2 : z ≤ δ ^ 2 / 4 := le_of_lt hz
          by_cases hz3 : 0 ≤ z
          · rw [Real.sq_sqrt hz3]
            nlinarith
          · have hsqrt0 : Real.sqrt z = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hz3)
            rw [hsqrt0]
            simpa using (sq_nonneg (δ / 2))
        have hnn : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z
        exact le_of_sq_le_sq hsq (le_of_lt (half_pos hδ))
      exact modGamma_one hδ hz'
    exact (ContDiffAt.contDiffWithinAt (n := (⊤ : ℕ∞)) (x := u)
      (contDiffAt_const.congr_of_eventuallyEq hconst))
  have hsmOn : ContDiffOn ℝ (⊤ : ℕ∞) (modGammaSqrt δ) t := by
    rintro u hu
    have hsq : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.sqrt x) u :=
      (Real.deriv_sqrt_aux (ne_of_gt hu)).2 (⊤ : ℕ∞)
    have hgamma : ContDiffAt ℝ (⊤ : ℕ∞) (modGamma δ) (Real.sqrt u) :=
      (contDiff_modGamma (δ := δ)).contDiffAt
    exact (ContDiffAt.comp u hgamma hsq).contDiffWithinAt
  have hs : IsOpen s := isOpen_lt continuous_id (continuous_const : Continuous fun _ : ℝ => δ ^ 2 / 4)
  have ht : IsOpen t := isOpen_lt (continuous_const : Continuous fun _ : ℝ => (0 : ℝ)) continuous_id
  have hcov : s ∪ t = Set.univ := by
    ext x
    constructor <;> intro hx
    · trivial
    · by_cases hx' : 0 < x
      · exact Or.inr hx'
      · have hle : x ≤ 0 := le_of_not_gt hx'
        have hmain : x < δ ^ 2 / 4 := by
          have hδ2 : 0 < δ ^ 2 / 4 := div_pos (sq_pos_of_pos hδ) (by norm_num)
          linarith
        exact Or.inl hmain
  exact contDiff_of_contDiffOn_union_of_isOpen hconstOn hsmOn hcov hs ht

theorem contDiff_modelModifiedFiberDip {ε δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelModifiedFiberDip ε δ p.1 p.2) := by
  have hmu : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modMu ε p.1) :=
    (contDiff_modMu (ε := ε)).comp contDiff_fst
  have hga : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modGammaSqrt δ p.2) :=
    (contDiff_modGammaSqrt hδ).comp contDiff_snd
  simpa [modelModifiedFiberDip, Function.comp_def] using hmu.mul hga

noncomputable def modelModifiedFiberEquation (ε δ r : ℝ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  p.2 * (p.1.1 + r ^ 2) - p.1.2 * (p.1.1 + 2 * modelModifiedFiberDip ε δ p.1.1 p.2 - 2 * ε)

theorem contDiff_modelModifiedFiberEquation (ε δ r : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (modelModifiedFiberEquation ε δ r) := by
  have hdip : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × ℝ => modelModifiedFiberDip ε δ p.1.1 p.2) := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => modelModifiedFiberDip ε δ p.1 p.2) :=
      contDiff_modelModifiedFiberDip hδ
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.2)) := by
      fun_prop
    simpa [Function.comp_def] using hd.comp hmap
  have hterm1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × ℝ => p.2 * (p.1.1 + r ^ 2)) := by
    fun_prop
  have hterm2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ) × ℝ => p.1.2 * (p.1.1 + 2 * modelModifiedFiberDip ε δ p.1.1 p.2 - 2 * ε)) := by
    have hinner : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (ℝ × ℝ) × ℝ => p.1.1 + 2 * modelModifiedFiberDip ε δ p.1.1 p.2 - 2 * ε) := by
      fun_prop
    have hproj : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ) × ℝ => p.1.2) := by
      fun_prop
    exact hproj.mul hinner
  simpa [modelModifiedFiberEquation] using hterm1.sub hterm2

theorem differentiableAt_modelModifiedFiberDip_fiber {ε δ : ℝ} (hδ : 0 < δ) (s u : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => modelModifiedFiberDip ε δ s t) u := by
  have hga : DifferentiableAt ℝ (modGammaSqrt δ) u :=
    ((contDiff_modGammaSqrt hδ).differentiable (by norm_num)).differentiableAt
  have hmuC : DifferentiableAt ℝ (fun t : ℝ => modMu ε s) u := by fun_prop
  have hmul := hmuC.mul hga
  dsimp [modelModifiedFiberDip]
  exact hmul

theorem deriv_modelModifiedFiberEquation_fiber {ε δ : ℝ} (hδ : 0 < δ) (s u : ℝ) :
    deriv (fun t : ℝ => modelModifiedFiberDip ε δ s t) u =
      modMu ε s * deriv (modGammaSqrt δ) u := by
  have hga : DifferentiableAt ℝ (modGammaSqrt δ) u :=
    ((contDiff_modGammaSqrt hδ).differentiable (by norm_num)).differentiableAt
  dsimp [modelModifiedFiberDip]
  exact deriv_const_mul (modMu ε s) hga

theorem deriv_modelModifiedFiberEquation {ε δ r : ℝ} (hδ : 0 < δ) (s w2 u : ℝ) :
    deriv (fun t : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), t)) u =
      (s + r ^ 2) - 2 * w2 * modMu ε s * deriv (modGammaSqrt δ) u := by
  have hdipDeriv : deriv (fun t : ℝ => modelModifiedFiberDip ε δ s t) u =
      modMu ε s * deriv (modGammaSqrt δ) u := deriv_modelModifiedFiberEquation_fiber hδ s u
  have hDipDiff : DifferentiableAt ℝ (fun t : ℝ => modelModifiedFiberDip ε δ s t) u :=
    differentiableAt_modelModifiedFiberDip_fiber hδ s u
  have hF1 : deriv (fun t : ℝ => t * (s + r ^ 2)) u = s + r ^ 2 := by
    have hc : DifferentiableAt ℝ (fun t : ℝ => t) u := by fun_prop
    rw [deriv_mul_const hc]
    simp
  have htwo : deriv (fun t : ℝ => 2 * modelModifiedFiberDip ε δ s t) u =
      2 * (modMu ε s * deriv (modGammaSqrt δ) u) := by
    rw [deriv_const_mul (2 : ℝ) hDipDiff]
    rw [hdipDeriv]
  have hinner : deriv (fun t : ℝ => s + 2 * modelModifiedFiberDip ε δ s t - 2 * ε) u =
      2 * (modMu ε s * deriv (modGammaSqrt δ) u) := by
    have h2 : deriv (fun t : ℝ => s + 2 * modelModifiedFiberDip ε δ s t) u =
        2 * (modMu ε s * deriv (modGammaSqrt δ) u) := by
      rw [deriv_const_add]
      rw [htwo]
    rw [deriv_sub_const]
    exact h2
  have hF2 : deriv (fun t : ℝ => w2 * (s + 2 * modelModifiedFiberDip ε δ s t - 2 * ε)) u =
      w2 * (2 * (modMu ε s * deriv (modGammaSqrt δ) u)) := by
    have hinnerDiff : DifferentiableAt ℝ (fun t : ℝ =>
        s + 2 * modelModifiedFiberDip ε δ s t - 2 * ε) u := by
      fun_prop
    rw [deriv_const_mul w2 hinnerDiff]
    rw [hinner]
  have hF : deriv (fun t : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), t)) u =
      deriv (fun t : ℝ => t * (s + r ^ 2)) u -
        deriv (fun t : ℝ => w2 * (s + 2 * modelModifiedFiberDip ε δ s t - 2 * ε)) u := by
    have h1 : DifferentiableAt ℝ (fun t : ℝ => t * (s + r ^ 2)) u := by fun_prop
    have h2 : DifferentiableAt ℝ (fun t : ℝ =>
        w2 * (s + 2 * modelModifiedFiberDip ε δ s t - 2 * ε)) u := by
      fun_prop
    dsimp [modelModifiedFiberEquation]
    exact deriv_sub h1 h2
  rw [hF, hF1, hF2]
  ring

theorem modGammaSqrt_antitone_global {δ : ℝ} (hδ : 0 < δ) : Antitone (modGammaSqrt δ) := by
  intro a b hab
  dsimp [modGammaSqrt]
  exact modGamma_antitone_global hδ (Real.sqrt_monotone hab)

theorem deriv_modGammaSqrt_nonpos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    deriv (modGammaSqrt δ) u ≤ 0 :=
  Antitone.deriv_nonpos (modGammaSqrt_antitone_global hδ)

theorem fderiv_modelModifiedFiberEquation_inr (ε δ r : ℝ) (hδ : 0 < δ) (s w2 u : ℝ) :
    fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u) (((0, 0), 1) : (ℝ × ℝ) × ℝ) =
      (s + r ^ 2) - 2 * w2 * modMu ε s * deriv (modGammaSqrt δ) u := by
  have hdiff : DifferentiableAt ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u) :=
    (contDiff_modelModifiedFiberEquation ε δ r hδ).differentiable (by norm_num) ((s, w2), u)
  have hFder : HasFDerivAt (modelModifiedFiberEquation ε δ r)
      (fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u)) ((s, w2), u) :=
    hdiff.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => ((s, w2), t)) (((0, 0), 1) : (ℝ × ℝ) × ℝ) u := by
    have h1 : HasDerivAt (fun t : ℝ => t • (((0, 0), 1) : (ℝ × ℝ) × ℝ))
        (((0, 0), 1) : (ℝ × ℝ) × ℝ) u := by
      simpa using (hasDerivAt_id u).smul_const (((0, 0), 1) : (ℝ × ℝ) × ℝ)
    have h2 : HasDerivAt (fun t : ℝ => ((s, w2), 0) + t • (((0, 0), 1) : (ℝ × ℝ) × ℝ))
        (((0, 0), 1) : (ℝ × ℝ) × ℝ) u :=
      HasDerivAt.const_add (c := ((s, w2), 0)) h1
    simpa using h2
  have hcomp' : HasDerivAt (fun t : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), t))
      (fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u) (((0, 0), 1) : (ℝ × ℝ) × ℝ)) u :=
    HasFDerivAt.comp_hasDerivAt_of_eq (hl := hFder) (hf := hline) (hy := rfl)
  have hd1 : deriv (fun τ : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), τ)) u =
      fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u) (((0, 0), 1) : (ℝ × ℝ) × ℝ) := by
    simpa using hcomp'.deriv
  calc
    fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u) (((0, 0), 1) : (ℝ × ℝ) × ℝ)
        = deriv (fun τ : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), τ)) u := hd1.symm
    _ = (s + r ^ 2) - 2 * w2 * modMu ε s * deriv (modGammaSqrt δ) u :=
          deriv_modelModifiedFiberEquation hδ s w2 u

theorem modelModifiedFiberEquation_fiber_deriv_pos (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (s w2 u : ℝ) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    0 < deriv (fun t : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), t)) u := by
  rw [deriv_modelModifiedFiberEquation hδ]
  have hga : deriv (modGammaSqrt δ) u ≤ 0 := deriv_modGammaSqrt_nonpos hδ u
  have hmu : 0 ≤ modMu ε s := modMu_nonneg (le_of_lt hε)
  have hterm : 2 * w2 * modMu ε s * deriv (modGammaSqrt δ) u ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg (by positivity) hw) hmu) hga
  have hsr : 0 < s + r ^ 2 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    nlinarith [hs, hr2]
  nlinarith

theorem modelModifiedFiberEquation_strictMono (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) (s w2 : ℝ) (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    StrictMono (fun u : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), u)) :=
  strictMono_of_deriv_pos (fun u =>
    modelModifiedFiberEquation_fiber_deriv_pos ε δ r hε hδ hr s w2 u hs hw)

theorem modelModifiedFiberRoot_eq_of_modelModifiedFiberEquation {ε δ r : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hr : r ≠ 0) (s w2 u : ℝ) (hs : 0 ≤ s) (hw : 0 ≤ w2)
    (hu : modelModifiedFiberEquation ε δ r ((s, w2), u) = 0) :
    u = modelModifiedFiberRoot ε δ r hε hδ hr s w2 := by
  have hroot' : modelModifiedFiberEquation ε δ r
      ((s, w2), modelModifiedFiberRoot ε δ r hε hδ hr s w2) = 0 := by
    dsimp [modelModifiedFiberEquation]
    rw [modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw]
    ring
  exact (modelModifiedFiberEquation_strictMono ε δ r hε hδ hr s w2 hs hw).injective
    (by rw [hu, hroot'])

theorem contDiffWithinAt_modelModifiedFiberRoot (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) {s w2 : ℝ} (hs : 0 ≤ s) (hw : 0 ≤ w2) :
    ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} (s, w2) := by
  let Q : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}
  let u₀ : ℝ := modelModifiedFiberRoot ε δ r hε hδ hr s w2
  have hFdiff : ContDiffAt ℝ (⊤ : ℕ∞) (modelModifiedFiberEquation ε δ r) ((s, w2), u₀) :=
    (contDiff_modelModifiedFiberEquation ε δ r hδ).contDiffAt
  have hroot : modelModifiedFiberEquation ε δ r ((s, w2), u₀) = 0 := by
    dsimp [u₀, modelModifiedFiberEquation]
    rw [modelModifiedFiberRoot_eq (ε := ε) (δ := δ) (r := r) (s := s) (w2 := w2) hε hδ hr hs hw]
    ring
  have hpos : 0 < fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u₀)
      (((0, 0), 1) : (ℝ × ℝ) × ℝ) := by
    rw [fderiv_modelModifiedFiberEquation_inr ε δ r hδ s w2 u₀]
    have hd : 0 < deriv (fun t : ℝ => modelModifiedFiberEquation ε δ r ((s, w2), t)) u₀ :=
      modelModifiedFiberEquation_fiber_deriv_pos ε δ r hε hδ hr s w2 u₀ hs hw
    rw [deriv_modelModifiedFiberEquation hδ s w2 u₀] at hd
    exact hd
  have hinv : (fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u₀) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    let c : ℝ := fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u₀)
      (((0, 0), 1) : (ℝ × ℝ) × ℝ)
    have hc : c ≠ 0 := ne_of_gt hpos
    let e : ℝ ≃L[ℝ] ℝ :=
      { toFun := fun y => c * y
        invFun := fun y => c⁻¹ * y
        left_inv := fun y => by field_simp [hc]
        right_inv := fun y => by field_simp [hc]
        map_add' := by intro x y; ring
        map_smul' := by
          intro a y
          simp only [smul_eq_mul, RingHom.id_apply]
          ring }
    refine ⟨e, ?_⟩
    apply ContinuousLinearMap.ext
    intro y
    change c * y = (fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u₀) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) y
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply]
    have harg : ((0, y) : (ℝ × ℝ) × ℝ) = y • (((0, 0), 1) : (ℝ × ℝ) × ℝ) := by
      rw [Prod.smul_mk]
      rw [Prod.smul_mk]
      congr 1
      · rw [smul_eq_mul]
        rw [mul_zero]
        rfl
      · rw [smul_eq_mul]
        rw [mul_one]
    have hlin : (fderiv ℝ (modelModifiedFiberEquation ε δ r) ((s, w2), u₀))
        (y • (((0, 0), 1) : (ℝ × ℝ) × ℝ)) = y * c := by
      rw [map_smul]
      simp only [smul_eq_mul, c]
    rw [harg, hlin]
    rw [mul_comm]
  let ψ : (ℝ × ℝ) → ℝ :=
    hFdiff.implicitFunction (n := (⊤ : ℕ∞)) (by norm_num) hinv
  have hψdiff : ContDiffAt ℝ (⊤ : ℕ∞) ψ (s, w2) := by
    simpa [ψ] using hFdiff.contDiffAt_implicitFunction (n := (⊤ : ℕ∞)) (by norm_num) hinv
  have hψeq : ψ (s, w2) = u₀ := by
    simpa [ψ] using (hFdiff.implicitFunction_apply_self (n := (⊤ : ℕ∞)) (by norm_num) hinv)
  have heq : ∀ᶠ p in nhdsWithin (s, w2) Q,
      modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2 = ψ p := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hFdiff.eventually_apply_implicitFunction (n := (⊤ : ℕ∞)) (by norm_num) hinv]
      with p hp
    intro hpq
    have hp' : modelModifiedFiberEquation ε δ r (p, ψ p) = 0 := by
      simpa [hroot] using hp
    exact (modelModifiedFiberRoot_eq_of_modelModifiedFiberEquation hε hδ hr p.1 p.2 (ψ p)
      hpq.1 hpq.2 hp').symm
  exact hψdiff.contDiffWithinAt.congr_of_eventuallyEq heq (by
    rw [hψeq])

theorem contDiffOn_modelModifiedFiberRoot (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
  intro p hp
  exact contDiffWithinAt_modelModifiedFiberRoot ε δ r hε hδ hr hp.1 hp.2

theorem contDiffOn_modelModifiedUnstretchFactor (ε δ r : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hr : r ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => modelModifiedUnstretchFactor ε δ r hε hδ hr p.1 p.2)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
  intro p hp
  let Q : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun q : ℝ × ℝ => Real.sqrt
      ((q.1 + 2 * modelModifiedFiberDip ε δ q.1
          (modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2) - 2 * ε) / (q.1 + r ^ 2))) Q p
  have hrootW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2) Q p :=
    contDiffWithinAt_modelModifiedFiberRoot ε δ r hε hδ hr hp.1 hp.2
  have hfstW : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.1) Q p :=
    (contDiff_fst : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.1)).contDiffAt.contDiffWithinAt
  have hpairW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => (q.1, modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2)) Q p :=
    hfstW.prodMk hrootW
  have hdipC : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => modelModifiedFiberDip ε δ q.1
        (modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2)) Q p := by
    have hdipW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
        (fun z : ℝ × ℝ => modelModifiedFiberDip ε δ z.1 z.2) Set.univ
        (p.1, modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2) :=
      (contDiff_modelModifiedFiberDip hδ).contDiffAt.contDiffWithinAt
    exact ContDiffWithinAt.comp p hdipW hpairW (by intro q hq; trivial)
  have hnumW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => q.1 + 2 * modelModifiedFiberDip ε δ q.1
        (modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2) - 2 * ε) Q p := by
    have hc2 : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => (2 : ℝ)) Q p :=
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => (2 : ℝ))).contDiffAt.contDiffWithinAt
    have hcε : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => 2 * ε) Q p :=
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => 2 * ε)).contDiffAt.contDiffWithinAt
    exact (hfstW.add (hc2.mul hdipC)).sub hcε
  have hdenW : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => q.1 + r ^ 2) Q p := by
    have hc : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => r ^ 2) Q p :=
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ => r ^ 2)).contDiffAt.contDiffWithinAt
    exact hfstW.add hc
  have hden0 : p.1 + r ^ 2 ≠ 0 := by
    have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
    have hpos : 0 < p.1 + r ^ 2 := by nlinarith [hp.1, hr2]
    exact ne_of_gt hpos
  have hratioW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => (q.1 + 2 * modelModifiedFiberDip ε δ q.1
        (modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2) - 2 * ε) / (q.1 + r ^ 2)) Q p :=
    ContDiffWithinAt.div hnumW hdenW hden0
  have hratio0 : 0 < (p.1 + 2 * modelModifiedFiberDip ε δ p.1
      (modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2) - 2 * ε) / (p.1 + r ^ 2) := by
    have hnum0 : 0 < p.1 + 2 * modelModifiedFiberDip ε δ p.1
        (modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2) - 2 * ε :=
      modelModifiedFiberDenom_root_pos hε hδ hr hp.1 hp.2
    have hdenpos : 0 < p.1 + r ^ 2 := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
      nlinarith [hp.1, hr2]
    exact div_pos hnum0 hdenpos
  have hsqrtAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt t)
      ((p.1 + 2 * modelModifiedFiberDip ε δ p.1
        (modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2) - 2 * ε) / (p.1 + r ^ 2)) :=
    (Real.deriv_sqrt_aux (ne_of_gt hratio0)).2 (⊤ : ℕ∞)
  have hfactorW : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => Real.sqrt ((q.1 + 2 * modelModifiedFiberDip ε δ q.1
        (modelModifiedFiberRoot ε δ r hε hδ hr q.1 q.2) - 2 * ε) / (q.1 + r ^ 2))) Q p := by
    have hsqrtW : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt t) Set.univ
        ((p.1 + 2 * modelModifiedFiberDip ε δ p.1
          (modelModifiedFiberRoot ε δ r hε hδ hr p.1 p.2) - 2 * ε) / (p.1 + r ^ 2)) :=
      hsqrtAt.contDiffWithinAt
    exact ContDiffWithinAt.comp p hsqrtW hratioW (by intro q hq; trivial)
  exact hfactorW

theorem contDiffAt_modelModifiedUnstretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) (y : MorseModel n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (modelModifiedUnstretchMap hk ε r δ hε hδ hr) y := by
  let Q : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}
  change ContDiffAt ℝ (⊤ : ℕ∞)
    (fun z : MorseModel n => recombine hk (negPart hk z)
      ((modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk z‖ ^ 2) (‖posPart hk z‖ ^ 2)) •
        posPart hk z)) y
  have hns : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖negPart hk z‖ ^ 2) :=
    ContDiff.norm_sq ℝ (negPartCLM hk).contDiff
  have hps : ContDiff ℝ (⊤ : ℕ∞) (fun z : MorseModel n => ‖posPart hk z‖ ^ 2) :=
    ContDiff.norm_sq ℝ (posPartCLM hk).contDiff
  have hfacOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => modelModifiedUnstretchFactor ε δ r hε hδ hr
        (‖negPart hk z‖ ^ 2) (‖posPart hk z‖ ^ 2)) Set.univ := by
    refine ContDiffOn.comp
      (g := fun p : ℝ × ℝ => modelModifiedUnstretchFactor ε δ r hε hδ hr p.1 p.2)
      (f := fun z : MorseModel n => (‖negPart hk z‖ ^ 2, ‖posPart hk z‖ ^ 2))
      (s := Set.univ) (t := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) ?hg ?hf ?st
    · exact contDiffOn_modelModifiedUnstretchFactor ε δ r hε hδ hr
    · exact (hns.prodMk hps).contDiffOn
    · intro z hz
      exact ⟨sq_nonneg _, sq_nonneg _⟩
  have hfacAt : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => modelModifiedUnstretchFactor ε δ r hε hδ hr
        (‖negPart hk z‖ ^ 2) (‖posPart hk z‖ ^ 2)) y :=
    contDiffWithinAt_univ.mp (hfacOn y trivial)
  have hneg : ContDiffAt ℝ (⊤ : ℕ∞) (negPart hk) y :=
    (negPartCLM hk).contDiff.contDiffAt
  have hpos : ContDiffAt ℝ (⊤ : ℕ∞) (posPart hk) y :=
    (posPartCLM hk).contDiff.contDiffAt
  have hsmul : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n =>
        (modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk z‖ ^ 2) (‖posPart hk z‖ ^ 2)) •
          posPart hk z) y :=
    ContDiffAt.smul hfacAt hpos
  have hrec : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin (n - k)) =>
        recombine hk p.1 p.2) := recombine_contDiff_generic hk
  have hpair2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : MorseModel n => (negPart hk z,
        (modelModifiedUnstretchFactor ε δ r hε hδ hr (‖negPart hk z‖ ^ 2) (‖posPart hk z‖ ^ 2)) •
          posPart hk z)) y :=
    hneg.prodMk hsmul
  exact ContDiffAt.comp y (ContDiff.contDiffAt hrec) hpair2

theorem contDiffOn_modelModifiedUnstretchMap {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (modelModifiedUnstretchMap hk ε r δ hε hδ hr) Set.univ := by
  intro y hy
  exact (contDiffAt_modelModifiedUnstretchMap hk ε r δ hε hδ hr y).contDiffWithinAt

theorem contMDiff_modelModifiedUnstretchMap_sublevel {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
        (contDiff_morseNormalForm hk c)
        (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
      sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
        (contDiff_modifiedNormalForm hk c ε δ hδ)
        (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
          ⟨le_of_eq hy.symm, by linarith⟩))
    (hchart₁ : ∀ y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₁.chartAt y =
        (if h : morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (contDiff_morseNormalForm hk c)
            (fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (contDiff_morseNormalForm hk c)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε),
      hcs₂.chartAt y =
        (if h : modifiedNormalForm hk c ε δ y.1 = c - ε then
          sublevelBoundaryChart (modifiedNormalForm hk c ε δ) (c - ε) y h
            (contDiff_modifiedNormalForm hk c ε δ hδ)
            (modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
              ⟨le_of_eq h.symm, by linarith⟩)
        else sublevelInteriorChart (modifiedNormalForm hk c ε δ) (c - ε) y
          (lt_of_le_of_ne (show modifiedNormalForm hk c ε δ y.1 ≤ c - ε from y.2) h)
          (contDiff_modifiedNormalForm hk c ε δ hδ)) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2) =>
        (⟨modelModifiedUnstretchMap hk ε r δ hε hδ hr y.1,
          modelModifiedUnstretchMap_mem_modified hk c ε r δ hε hδ hr y.2⟩ :
          SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε))) := by
  exact contMDiff_sublevelMap_on (m := m) (morseNormalForm hk c) (modifiedNormalForm hk c ε δ)
    (c + r ^ 2 / 2) (c - ε)
    (contDiff_morseNormalForm hk c) (contDiff_modifiedNormalForm hk c ε δ hδ)
    (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
    (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
      ⟨le_of_eq hy.symm, by linarith⟩)
    (modelModifiedUnstretchMap hk ε r δ hε hδ hr) Set.univ isOpen_univ (by intro y hy; trivial)
    (contDiffOn_modelModifiedUnstretchMap hk ε r δ hε hδ hr)
    (fun y hy => modelModifiedUnstretchMap_mem_modified hk c ε r δ hε hδ hr hy)
    (fun y hy => modelModifiedUnstretchMap_boundary hk c ε r δ hε hδ hr hy)
    (fun y hy => modelModifiedUnstretchMap_strict hk c ε r δ hε hδ hr hy)
    (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

noncomputable def modelModifiedSublevelDiffeomorph {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hr : r ≠ 0)
    (hcs₁ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
      sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
        (contDiff_modifiedNormalForm hk c ε δ hδ)
        (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
          ⟨le_of_eq hy.symm, by linarith⟩))
    (hcs₂ : ChartedSpace (MorseHalfSpace m)
        (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
      sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
        (contDiff_morseNormalForm hk c)
        (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy))
    (hchart₁ : ∀ y : SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε),
      hcs₁.chartAt y =
        (if h : modifiedNormalForm hk c ε δ y.1 = c - ε then
          sublevelBoundaryChart (modifiedNormalForm hk c ε δ) (c - ε) y h
            (contDiff_modifiedNormalForm hk c ε δ hδ)
            (modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
              ⟨le_of_eq h.symm, by linarith⟩)
        else sublevelInteriorChart (modifiedNormalForm hk c ε δ) (c - ε) y
          (lt_of_le_of_ne (show modifiedNormalForm hk c ε δ y.1 ≤ c - ε from y.2) h)
          (contDiff_modifiedNormalForm hk c ε δ hδ)) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2),
      hcs₂.chartAt y =
        (if h : morseNormalForm hk c y.1 = c + r ^ 2 / 2 then
          sublevelBoundaryChart (morseNormalForm hk c) (c + r ^ 2 / 2) y h
            (contDiff_morseNormalForm hk c)
            (fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y.1 h)
        else sublevelInteriorChart (morseNormalForm hk c) (c + r ^ 2 / 2) y
          (lt_of_le_of_ne (show morseNormalForm hk c y.1 ≤ c + r ^ 2 / 2 from y.2) h)
          (contDiff_morseNormalForm hk c)) := by
      intro y
      rfl) :
    @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) _ hcs₁
      (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) _ hcs₂
      (⊤ : ℕ∞) where
  toEquiv :=
    { toFun := fun y => (⟨modelModifiedStretchMap hk ε r δ y.1,
        modelModifiedStretchMap_mem_upper hk c ε r δ hε hδ y.2⟩ :
        SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2))
      invFun := fun y => (⟨modelModifiedUnstretchMap hk ε r δ hε hδ hr y.1,
        modelModifiedUnstretchMap_mem_modified hk c ε r δ hε hδ hr y.2⟩ :
        SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε))
      left_inv := by
        intro y
        apply Subtype.ext
        exact modelModifiedUnstretchMap_stretchMap hk c ε r δ hε hδ hr y.2
      right_inv := by
        intro y
        apply Subtype.ext
        exact modelModifiedStretchMap_unstretchMap hk ε r δ hε hδ hr y.1 }
  contMDiff_toFun := by
    simpa using (contMDiff_modelModifiedStretchMap_sublevel (hk := hk) (c := c) (ε := ε) (r := r)
      (δ := δ) (hε := hε) (hδ := hδ) (hr := hr) (hcs₁ := hcs₁) (hcs₂ := hcs₂)
      (hchart₁ := hchart₁) (hchart₂ := hchart₂))
  contMDiff_invFun := by
    simpa using (contMDiff_modelModifiedUnstretchMap_sublevel (hk := hk) (c := c) (ε := ε) (r := r)
      (δ := δ) (hε := hε) (hδ := hδ) (hr := hr) (hcs₁ := hcs₂) (hcs₂ := hcs₁)
      (hchart₁ := hchart₂) (hchart₂ := hchart₁))

noncomputable def modelAttachedRegionEquivModified {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    {y : MorseModel (m + 1) // y ∈ modelAttachedRegion hk ε r δ} ≃ₜ
      {y : MorseModel (m + 1) // modifiedNormalForm hk c ε δ y ≤ c - ε} := by
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
    sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
      (contDiff_modifiedNormalForm hk c ε δ hδ)
      (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
        ⟨le_of_eq hy.symm, by linarith⟩)
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
    sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
      (contDiff_morseNormalForm hk c)
      (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
  exact (modelAttachedRegionEquivUpper hk c ε r δ hδ hδr hr).trans
    (modelModifiedSublevelDiffeomorph hk c ε r δ hε hδ hr).toHomeomorph.symm

noncomputable def modelSharpUnionEquivModifiedHomeo {m k : ℕ} (hk : k ≤ m + 1) (c ε r δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδr : δ < r ^ 2) (hr : r ≠ 0) :
    {y : MorseModel (m + 1) // y ∈ (sublevel (morseNormalForm hk c) (c - ε) : Set (MorseModel (m + 1))) ∪
      modelHandle hk ε r} ≃ₜ
      {y : MorseModel (m + 1) // modifiedNormalForm hk c ε δ y ≤ c - ε} := by
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (modifiedNormalForm hk c ε δ) (c - ε)) :=
    sublevelChartedSpace (m := m) (modifiedNormalForm hk c ε δ) (c - ε)
      (contDiff_modifiedNormalForm hk c ε δ hδ)
      (fun y hy => modifiedNormalForm_no_critical_point_in_strip hk c ε δ hε hδ
        ⟨le_of_eq hy.symm, by linarith⟩)
  letI : ChartedSpace (MorseHalfSpace m)
      (SublevelSpace (morseNormalForm hk c) (c + r ^ 2 / 2)) :=
    sublevelChartedSpace (m := m) (morseNormalForm hk c) (c + r ^ 2 / 2)
      (contDiff_morseNormalForm hk c)
      (fun y hy => fderiv_morseNormalForm_ne_zero hk c (r ^ 2 / 2) (by positivity) y hy)
  exact (modelSharpUnionToUpperHomeo hk c ε r δ hδ hδr).trans
    (modelModifiedSublevelDiffeomorph hk c ε r δ hε hδ hr).toHomeomorph.symm

noncomputable def modelRoundedFunction {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (y : MorseModel n) : ℝ :=
  modelAttachedFunction hk c ε r δ y +
    (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) *
      Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))

theorem modelRoundedFunction_eq_attached_of_norm_le {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n} (hy : morseNorm n y ≤ R₀) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y = modelAttachedFunction hk c ε r δ y := by
  dsimp [modelRoundedFunction]
  have harg : (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) ≤ 0 := by
    have hsq : morseNorm n y ^ 2 ≤ R₀ ^ 2 := by
      have hnon : 0 ≤ morseNorm n y := by
        dsimp [morseNorm]
        exact norm_nonneg _
      exact sq_le_sq' (by nlinarith [hnon, hR0]) hy
    have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith [hR0, hR]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0, abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsq) (le_of_lt hden)
  rw [Real.smoothTransition.zero_of_nonpos harg]
  ring

theorem modelRoundedFunction_eq_morse_add_eps_of_norm_ge {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n}
    (hy : R₁ ≤ morseNorm n y) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y = morseNormalForm hk c y + ε := by
  dsimp [modelRoundedFunction]
  have harg : 1 ≤ (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2) := by
    have hsq : R₁ ^ 2 ≤ morseNorm n y ^ 2 := by
      have hnon : 0 ≤ morseNorm n y := by
        dsimp [morseNorm]
        exact norm_nonneg _
      exact sq_le_sq' (by nlinarith [hR0, hR]) hy
    have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith [hR0, hR]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0, abs_of_nonneg h0]
          exact hR)
      nlinarith
    exact (one_le_div hden).mpr (by nlinarith [hsq])
  rw [Real.smoothTransition.one_of_one_le harg]
  ring

theorem contDiff_modelRoundedFunction {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (modelRoundedFunction hk c ε r δ R₀ R₁) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
    modelAttachedFunction hk c ε r δ y +
      (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) *
        Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)))
  have hnormSq : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNorm n y ^ 2) := by
    dsimp [morseNorm]
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
        (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))) := by
      simpa using ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff)
    exact hlin.norm_sq ℝ
  have harg : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      (morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2)) := by
    exact ((hnormSq.sub (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : MorseModel n => R₀ ^ 2))).div_const (R₁ ^ 2 - R₀ ^ 2))
  have htrans : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n =>
      Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp harg
  have hF₁ : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => modelAttachedFunction hk c ε r δ y) :=
    contDiff_modelAttachedFunction hk c ε r δ
  have hF₂ : ContDiff ℝ (⊤ : ℕ∞) (fun y : MorseModel n => morseNormalForm hk c y + ε) :=
    (contDiff_morseNormalForm hk c).add contDiff_const
  exact (hF₁.add ((hF₂.sub hF₁).mul htrans))

theorem modelRoundedFunction_eq_morse_add_eps_of_negPart_large {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hδ : 0 < δ) {y : MorseModel n}
    (hy : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y = morseNormalForm hk c y + ε := by
  dsimp [modelRoundedFunction]
  have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
    smoothCap_upper hδ hy
  have hf : modelAttachedFunction hk c ε r δ y = morseNormalForm hk c y + ε := by
    dsimp [modelAttachedFunction]
    rw [morseNormalForm_split]
    rw [hcap]
    ring
  rw [hf]
  ring

theorem modelLowerSublevel_norm_sq_lt_of_negPart_lt {n k : ℕ} (hk : k ≤ n) (c ε r δ : ℝ)
    {y : MorseModel n} (hy : morseNormalForm hk c y ≤ c - ε)
    (hneg : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ) :
    morseNorm n y ^ 2 < 2 * (r ^ 2 + 2 * ε + δ) - 2 * ε := by
  have hpos : ‖posPart hk y‖ ^ 2 ≤ ‖negPart hk y‖ ^ 2 - 2 * ε := by
    rw [morseNormalForm_split] at hy
    nlinarith
  have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
    calc
      morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
        rw [recombine_decompose hk y]
      _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
        morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
  nlinarith [hneg, hpos, hnorm]

theorem modelAttached_norm_sq_lt_of_negPart_lt {n k : ℕ} (hk : k ≤ n) (ε r δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) {y : MorseModel n}
    (hy : y ∈ modelAttachedRegion hk ε r δ)
    (hneg : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ) :
    morseNorm n y ^ 2 < 2 * (r ^ 2 + 2 * ε + δ) := by
  have hpos : ‖posPart hk y‖ ^ 2 ≤ max (r ^ 2) (‖negPart hk y‖ ^ 2) := by
    dsimp [modelAttachedRegion] at hy
    exact le_trans hy (smoothCap_le_max (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2) hε hδ)
  have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
    calc
      morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
        rw [recombine_decompose hk y]
      _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
        morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
  have hle : ‖negPart hk y‖ ^ 2 + max (r ^ 2) (‖negPart hk y‖ ^ 2) < 2 * (r ^ 2 + 2 * ε + δ) := by
    by_cases hle' : ‖negPart hk y‖ ^ 2 ≤ r ^ 2
    · have hmax : max (r ^ 2) (‖negPart hk y‖ ^ 2) = r ^ 2 := max_eq_left hle'
      nlinarith [hneg, hle', hmax]
    · have hgt : r ^ 2 < ‖negPart hk y‖ ^ 2 := lt_of_not_ge hle'
      have hmax : max (r ^ 2) (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 := max_eq_right (le_of_lt hgt)
      nlinarith [hneg, hgt, hmax]
  nlinarith [hpos, hnorm, hle]

theorem smoothCap_le_max_sub {ε r δ t : ℝ} :
    smoothCap ε r δ t ≤ max (r ^ 2) (t - 2 * ε) := by
  dsimp [smoothCap]
  let σ : ℝ := Real.smoothTransition ((t - (r ^ 2 + 2 * ε - δ)) / (2 * δ))
  have hσ : 0 ≤ σ := by dsimp [σ]; exact Real.smoothTransition.nonneg _
  have hσ₁ : σ ≤ 1 := by dsimp [σ]; exact Real.smoothTransition.le_one _
  by_cases hle : t - 2 * ε - r ^ 2 ≤ 0
  · have hmain : r ^ 2 + (t - 2 * ε - r ^ 2) * σ ≤ r ^ 2 := by nlinarith [hσ, hle]
    have hmax : r ^ 2 ≤ max (r ^ 2) (t - 2 * ε) := le_max_left _ _
    nlinarith
  · have hpos : 0 < t - 2 * ε - r ^ 2 := lt_of_not_ge hle
    have hmain : r ^ 2 + (t - 2 * ε - r ^ 2) * σ ≤ t - 2 * ε := by nlinarith [hσ₁, hpos]
    have hmax : t - 2 * ε ≤ max (r ^ 2) (t - 2 * ε) := le_max_right _ _
    nlinarith

theorem modelRoundedFunction_gt_c_of_norm_gt_negPart_lt {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hy₀ : R₀ < morseNorm n y)
    (hneg : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ) :
    c < modelRoundedFunction hk c ε r δ R₀ R₁ y := by
  by_cases hy₁ : R₁ ≤ morseNorm n y
  · rw [modelRoundedFunction_eq_morse_add_eps_of_norm_ge hk c ε r δ R₀ R₁ hR hR0 hy₁]
    rw [morseNormalForm_split]
    have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
      calc
        morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
          rw [recombine_decompose hk y]
        _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
          morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
    have hsq : R₁ ^ 2 ≤ morseNorm n y ^ 2 := by
      exact sq_le_sq' (by nlinarith [hR0, hR]) hy₁
    have hbig' : r ^ 2 + 2 * ε + δ < R₁ ^ 2 := by
      have h01 : R₀ ^ 2 < R₁ ^ 2 := by
        have h0 : 0 ≤ R₁ := by nlinarith [hR0, hR]
        exact sq_lt_sq.mpr (by
          rw [abs_of_nonneg hR0, abs_of_nonneg h0]
          exact hR)
      have hb' : 2 * (r ^ 2 + 2 * ε + δ) < R₁ ^ 2 := by nlinarith [hbig, h01]
      nlinarith
    have hb : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk y‖ ^ 2 := by
      nlinarith [hnorm, hsq, hbig', hneg]
    nlinarith
  · have hy₁' : morseNorm n y < R₁ := lt_of_not_ge hy₁
    let σ : ℝ := Real.smoothTransition ((morseNorm n y ^ 2 - R₀ ^ 2) / (R₁ ^ 2 - R₀ ^ 2))
    have hσ : 0 ≤ σ := by dsimp [σ]; exact Real.smoothTransition.nonneg _
    have hσ₁ : σ ≤ 1 := by dsimp [σ]; exact Real.smoothTransition.le_one _
    have hpos : R₀ ^ 2 < morseNorm n y ^ 2 := by
      exact sq_lt_sq' (by nlinarith [hR0, norm_nonneg (morseNorm n y)]) hy₀
    have hpos2 : ‖posPart hk y‖ ^ 2 > max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) := by
      have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
        calc
          morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
            rw [recombine_decompose hk y]
          _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
            morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
      have hb : ‖negPart hk y‖ ^ 2 + max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) < R₀ ^ 2 := by
        have h1 : max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) ≤ r ^ 2 + 2 * ε + δ := by
          exact max_le (by nlinarith) (by nlinarith [hneg])
        nlinarith [hbig, h1, hneg]
      nlinarith [hnorm, hpos, hb]
    have hF₁ : c < modelAttachedFunction hk c ε r δ y := by
      dsimp [modelAttachedFunction]
      have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) ≤ max (r ^ 2) (‖negPart hk y‖ ^ 2 - 2 * ε) :=
        smoothCap_le_max_sub (ε := ε) (r := r) (δ := δ) (t := ‖negPart hk y‖ ^ 2)
      nlinarith [hpos2, hcap]
    have hF₂ : c < morseNormalForm hk c y + ε := by
      rw [morseNormalForm_split]
      have hnorm : morseNorm n y ^ 2 = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 := by
        calc
          morseNorm n y ^ 2 = morseNorm n (recombine hk (negPart hk y) (posPart hk y)) ^ 2 := by
            rw [recombine_decompose hk y]
          _ = ‖negPart hk y‖ ^ 2 + ‖posPart hk y‖ ^ 2 :=
            morseNorm_recombine_sq hk (negPart hk y) (posPart hk y)
      have hb : ‖negPart hk y‖ ^ 2 - 2 * ε < ‖posPart hk y‖ ^ 2 := by nlinarith [hpos2, hnorm]
      nlinarith
    dsimp [modelRoundedFunction]
    have hmain : c < modelAttachedFunction hk c ε r δ y +
        (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) * σ := by
      have hσlt : σ < 1 := by
        dsimp [σ]
        exact Real.smoothTransition.lt_one_of_lt_one (by
          have hsq : morseNorm n y ^ 2 < R₁ ^ 2 := by
            exact sq_lt_sq' (by nlinarith [hR0, hR]) hy₁'
          have hden : 0 < R₁ ^ 2 - R₀ ^ 2 := by nlinarith [hR, hR0]
          exact (div_lt_one hden).mpr (by nlinarith [hsq]))
      have hpos1 : 0 < modelAttachedFunction hk c ε r δ y - c := by linarith [hF₁]
      have hpos2 : 0 < morseNormalForm hk c y + ε - c := by linarith [hF₂]
      have hmain' : 0 < (1 - σ) * (modelAttachedFunction hk c ε r δ y - c) +
          σ * (morseNormalForm hk c y + ε - c) := by
        have h₁ : 0 < (1 - σ) * (modelAttachedFunction hk c ε r δ y - c) :=
          mul_pos (by linarith [hσlt]) hpos1
        have h₂ : 0 ≤ σ * (morseNormalForm hk c y + ε - c) :=
          mul_nonneg hσ (le_of_lt hpos2)
        nlinarith
      have hrew : modelAttachedFunction hk c ε r δ y +
          (morseNormalForm hk c y + ε - modelAttachedFunction hk c ε r δ y) * σ - c =
          (1 - σ) * (modelAttachedFunction hk c ε r δ y - c) +
            σ * (morseNormalForm hk c y + ε - c) := by
        ring
      rw [← hrew] at hmain'
      linarith
    exact hmain

theorem modelRoundedFunction_le_c_iff_of_norm_gt {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) {y : MorseModel n}
    (hy₀ : R₀ < morseNorm n y) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y ≤ c ↔ morseNormalForm hk c y ≤ c - ε := by
  constructor
  · intro hy
    by_cases hy₁ : R₁ ≤ morseNorm n y
    · rw [modelRoundedFunction_eq_morse_add_eps_of_norm_ge hk c ε r δ R₀ R₁ hR hR0 hy₁] at hy
      nlinarith
    · have hy₁' : morseNorm n y < R₁ := lt_of_not_ge hy₁
      have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
        by_contra hnot
        have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
        have hgt : c < modelRoundedFunction hk c ε r δ R₀ R₁ y :=
          modelRoundedFunction_gt_c_of_norm_gt_negPart_lt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig hy₀ hlt
        exact (not_lt_of_ge hy) hgt
      rw [modelRoundedFunction_eq_morse_add_eps_of_negPart_large hk c ε r δ R₀ R₁ hδ hnegl] at hy
      nlinarith
  · intro hy
    by_cases hy₁ : R₁ ≤ morseNorm n y
    · rw [modelRoundedFunction_eq_morse_add_eps_of_norm_ge hk c ε r δ R₀ R₁ hR hR0 hy₁]
      nlinarith
    · have hy₁' : morseNorm n y < R₁ := lt_of_not_ge hy₁
      have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
        by_contra hnot
        have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
        have hnormle : morseNorm n y ^ 2 < R₀ ^ 2 := by
          have h1 := modelLowerSublevel_norm_sq_lt_of_negPart_lt hk c ε r δ hy hlt
          have h2 : 2 * (r ^ 2 + 2 * ε + δ) - 2 * ε < R₀ ^ 2 := by nlinarith [hbig]
          nlinarith [h1, h2]
        have hle : morseNorm n y ≤ R₀ := by
          have habs := sq_lt_sq.mp hnormle
          have hnon : 0 ≤ morseNorm n y := by
            dsimp [morseNorm]
            exact norm_nonneg _
          have h1 : |morseNorm n y| = morseNorm n y := abs_of_nonneg hnon
          have h2 : |R₀| = R₀ := abs_of_nonneg hR0
          rw [h1, h2] at habs
          exact le_of_lt habs
        exact (not_lt_of_ge hle) hy₀
      rw [modelRoundedFunction_eq_morse_add_eps_of_negPart_large hk c ε r δ R₀ R₁ hδ hnegl]
      nlinarith

theorem modelRoundedFunction_le_c_iff_of_norm_le {n k : ℕ} (hk : k ≤ n) (c ε r δ R₀ R₁ : ℝ)
    (hR : R₀ < R₁) (hR0 : 0 ≤ R₀) {y : MorseModel n} (hy : morseNorm n y ≤ R₀) :
    modelRoundedFunction hk c ε r δ R₀ R₁ y ≤ c ↔ y ∈ modelAttachedRegion hk ε r δ := by
  rw [modelRoundedFunction_eq_attached_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hy]
  exact (modelAttachedRegion_iff_sublevel hk c ε r δ y).symm

theorem modelRoundedFunction_sublevel_eq_attached_union_lower {n k : ℕ} (hk : k ≤ n)
    (c ε r δ R₀ R₁ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hR : R₀ < R₁) (hR0 : 0 ≤ R₀)
    (hbig : 2 * (r ^ 2 + 2 * ε + δ) ≤ R₀ ^ 2) :
    {y : MorseModel n | modelRoundedFunction hk c ε r δ R₀ R₁ y ≤ c} =
      (modelAttachedRegion hk ε r δ : Set (MorseModel n)) ∪
        {y : MorseModel n | r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 ∧
          morseNormalForm hk c y ≤ c - ε} := by
  ext y
  constructor
  · intro hy
    by_cases hnorm : morseNorm n y ≤ R₀
    · left
      exact (modelRoundedFunction_le_c_iff_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hnorm).mp hy
    · have hnorm' : R₀ < morseNorm n y := lt_of_not_ge hnorm
      have hlow : morseNormalForm hk c y ≤ c - ε :=
        (modelRoundedFunction_le_c_iff_of_norm_gt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig hnorm').mp hy
      have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
        by_contra hnot
        have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
        have hnormle : morseNorm n y ^ 2 < R₀ ^ 2 := by
          have h1 := modelLowerSublevel_norm_sq_lt_of_negPart_lt hk c ε r δ hlow hlt
          have h2 : 2 * (r ^ 2 + 2 * ε + δ) - 2 * ε < R₀ ^ 2 := by nlinarith [hbig]
          nlinarith [h1, h2]
        have hle : morseNorm n y ≤ R₀ := by
          have habs := sq_lt_sq.mp hnormle
          have hnon : 0 ≤ morseNorm n y := by
            dsimp [morseNorm]
            exact norm_nonneg _
          have h1 : |morseNorm n y| = morseNorm n y := abs_of_nonneg hnon
          have h2 : |R₀| = R₀ := abs_of_nonneg hR0
          rw [h1, h2] at habs
          exact le_of_lt habs
        exact (not_lt_of_ge hle) hnorm'
      exact Or.inr ⟨hnegl, hlow⟩
  · intro hy
    rcases hy with hatt | hlow
    · by_cases hnorm : morseNorm n y ≤ R₀
      · exact (modelRoundedFunction_le_c_iff_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hnorm).mpr hatt
      · have hnorm' : R₀ < morseNorm n y := lt_of_not_ge hnorm
        have hnegl : r ^ 2 + 2 * ε + δ ≤ ‖negPart hk y‖ ^ 2 := by
          by_contra hnot
          have hlt : ‖negPart hk y‖ ^ 2 < r ^ 2 + 2 * ε + δ := lt_of_not_ge hnot
          have hnormle : morseNorm n y ^ 2 < R₀ ^ 2 := by
            have h1 := modelAttached_norm_sq_lt_of_negPart_lt hk ε r δ (le_of_lt hε) hδ hatt hlt
            nlinarith [hbig, h1]
          have hle : morseNorm n y ≤ R₀ := by
            have habs := sq_lt_sq.mp hnormle
            have hnon : 0 ≤ morseNorm n y := by
              dsimp [morseNorm]
              exact norm_nonneg _
            have h1 : |morseNorm n y| = morseNorm n y := abs_of_nonneg hnon
            have h2 : |R₀| = R₀ := abs_of_nonneg hR0
            rw [h1, h2] at habs
            exact le_of_lt habs
          exact (not_lt_of_ge hle) hnorm'
        have hlow : morseNormalForm hk c y ≤ c - ε := by
          dsimp [modelAttachedRegion] at hatt
          have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
            smoothCap_upper hδ hnegl
          rw [morseNormalForm_split]
          nlinarith [hatt, hcap]
        exact (modelRoundedFunction_le_c_iff_of_norm_gt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig hnorm').mpr hlow
    · rcases hlow with ⟨hnegl, hlow⟩
      by_cases hnorm : morseNorm n y ≤ R₀
      · have hatt : y ∈ modelAttachedRegion hk ε r δ := by
          dsimp [modelAttachedRegion]
          rw [morseNormalForm_split] at hlow
          have hcap : smoothCap ε r δ (‖negPart hk y‖ ^ 2) = ‖negPart hk y‖ ^ 2 - 2 * ε :=
            smoothCap_upper hδ hnegl
          nlinarith [hlow, hcap]
        exact (modelRoundedFunction_le_c_iff_of_norm_le hk c ε r δ R₀ R₁ hR hR0 hnorm).mpr hatt
      · have hnorm' : R₀ < morseNorm n y := lt_of_not_ge hnorm
        exact (modelRoundedFunction_le_c_iff_of_norm_gt hk c ε r δ R₀ R₁ hε hδ hR hR0 hbig hnorm').mpr hlow


end

end DifferentialGeometry.Topology.Morse.CellAttachment
