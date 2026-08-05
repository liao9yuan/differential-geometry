import DifferentialGeometry.Topology.Morse.CellAttachment
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace DifferentialGeometry.Topology.Morse.CellAttachment

open Filter Set
open scoped Topology BigOperators ContDiff

noncomputable section

def modMu (ε : ℝ) : ℝ → ℝ := fun t => (3 / 2 * ε) * (1 - Real.smoothTransition ((t - 2 * ε) / (2 * ε)))

def modGamma (δ : ℝ) : ℝ → ℝ := fun s => 1 - Real.smoothTransition ((2 * s - δ) / δ)

def negPartCLM {n k : ℕ} (hk : k ≤ n) : MorseModel n →L[ℝ] EuclideanSpace ℝ (Fin k) where
  toFun := fun y => negPart hk y
  map_add' := by
    intro x y
    ext i
    simp [negPart]
  map_smul' := by
    intro a x
    ext i
    simp [negPart]
  cont := by
    have h : Continuous (fun y : MorseModel n => (fun i : Fin k => y (negIdx hk i))) :=
      continuous_pi (fun i => continuous_apply (negIdx hk i))
    exact (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin k => ℝ)).comp h

def negBasis {n k : ℕ} (hk : k ≤ n) (i : Fin k) : MorseModel n :=
  fun r => if r = negIdx hk i then (1 : ℝ) else 0

def negUnit {k : ℕ} (i : Fin k) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp (p := 2) (fun j : Fin k => if j = i then (1 : ℝ) else 0)

theorem negPart_negBasis {n k : ℕ} (hk : k ≤ n) (i : Fin k) :
    negPart hk (negBasis hk i) = negUnit i := by
  ext j
  change (if negIdx hk j = negIdx hk i then (1 : ℝ) else 0) =
      (if j = i then (1 : ℝ) else 0)
  by_cases h : i = j
  · have hz : negIdx hk j = negIdx hk i := by rw [h]
    simp [h, hz]
  · have h' : negIdx hk j ≠ negIdx hk i := by
      intro hz
      exact h (Fin.castLE_injective hk hz).symm
    have hc2 : ¬(j = i) := fun hj => h hj.symm
    rw [if_neg h', if_neg hc2]

theorem posPart_negBasis {n k : ℕ} (hk : k ≤ n) (i : Fin k) :
    posPart hk (negBasis hk i) = 0 := by
  ext j
  simp only [negBasis, posPart]
  have h : posIdx hk j ≠ negIdx hk i := by
    intro hz
    have hval : (posIdx hk j).val = (negIdx hk i).val := congrArg Fin.val hz
    dsimp [posIdx, negIdx] at hval
    omega
  simp [h]

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

theorem differentiableAt_modMu {ε : ℝ} (x : ℝ) : DifferentiableAt ℝ (modMu ε) x := by
  have hst : DifferentiableAt ℝ Real.smoothTransition ((x - 2 * ε) / (2 * ε)) :=
    by
      have hc : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
        Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
      exact (hc.contDiffAt (x := (x - 2 * ε) / (2 * ε))).differentiableAt (by norm_num)
  have hinner : DifferentiableAt ℝ (fun t : ℝ => (t - 2 * ε) / (2 * ε)) x := by
    fun_prop
  have hcomp : DifferentiableAt ℝ (fun t : ℝ => Real.smoothTransition ((t - 2 * ε) / (2 * ε))) x :=
    DifferentiableAt.comp (x := x) (g := Real.smoothTransition)
      (f := fun t : ℝ => (t - 2 * ε) / (2 * ε)) hst hinner
  have hone : DifferentiableAt ℝ (fun t : ℝ => 1 - Real.smoothTransition ((t - 2 * ε) / (2 * ε))) x :=
    DifferentiableAt.sub (differentiableAt_const (1 : ℝ)) hcomp
  have hres : DifferentiableAt ℝ (fun t : ℝ =>
      (3 / 2 * ε) * (1 - Real.smoothTransition ((t - 2 * ε) / (2 * ε)))) x :=
    hone.const_mul (3 / 2 * ε)
  simpa [modMu] using hres

theorem differentiableAt_modGamma {δ : ℝ} (x : ℝ) : DifferentiableAt ℝ (modGamma δ) x := by
  change DifferentiableAt ℝ (fun s : ℝ => 1 - Real.smoothTransition ((2 * s - δ) / δ)) x
  have hst : DifferentiableAt ℝ Real.smoothTransition ((2 * x - δ) / δ) := by
    have hc : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
      Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
    exact (hc.contDiffAt (x := (2 * x - δ) / δ)).differentiableAt (by norm_num)
  have hinner : DifferentiableAt ℝ (fun s : ℝ => (2 * s - δ) / δ) x := by
    fun_prop
  have hcomp : DifferentiableAt ℝ (fun s : ℝ => Real.smoothTransition ((2 * s - δ) / δ)) x :=
    DifferentiableAt.comp (x := x) (g := Real.smoothTransition)
      (f := fun s : ℝ => (2 * s - δ) / δ) hst hinner
  have hc1 : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) x := differentiableAt_const (1 : ℝ)
  exact hc1.sub hcomp

lemma fderiv_apply_eq_deriv_line {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : MorseModel n → F} {y e : MorseModel n}
    (hgdiff : DifferentiableAt ℝ g y) {D : F}
    (hline : HasDerivAt (fun h : ℝ => g (y + h • e)) D 0) :
    fderiv ℝ g y e = D := by
  have hTdiff : DifferentiableAt ℝ (fun h : ℝ => y + h • e) 0 := by
    fun_prop
  have hcomp := fderiv_comp' (g := g) (f := fun h : ℝ => y + h • e) (x := 0)
    (by simpa using hgdiff) hTdiff
  have hT : fderiv ℝ (fun h : ℝ => y + h • e) 0 = (1 : ℝ →L[ℝ] ℝ).smulRight e := by
    apply ContinuousLinearMap.ext
    intro v
    have hlin : HasFDerivAt (fun h : ℝ => h • e) ((1 : ℝ →L[ℝ] ℝ).smulRight e) 0 := by
      exact (ContinuousLinearMap.hasFDerivAt (f := (1 : ℝ →L[ℝ] ℝ).smulRight e) (x := 0))
    have hconst : HasFDerivAt (fun h : ℝ => y) (0 : ℝ →L[ℝ] MorseModel n) 0 :=
      hasFDerivAt_const _ _
    have hsum := hlin.add hconst
    have hfd := hsum.fderiv
    have hgoal : fderiv ℝ (fun h : ℝ => y + h • e) 0 = (1 : ℝ →L[ℝ] ℝ).smulRight e := by
      have hfuneq : (fun h : ℝ => y + h • e) = (fun h : ℝ => h • e) + (fun h : ℝ => y) := by
        funext h
        simp only [Pi.add_apply]
        ring_nf
      exact ((congrArg (fun f : ℝ → MorseModel n => fderiv ℝ f 0) hfuneq).trans hfd).trans
        (add_zero _)
    have hh := congrArg (fun L : ℝ →L[ℝ] MorseModel n => L v) hgoal
    simpa using hh
  have hline' : fderiv ℝ (fun h : ℝ => g (y + h • e)) 0 (1 : ℝ) = D := by
    have hf := hline.hasFDerivAt
    have hfd : fderiv ℝ (fun h : ℝ => g (y + h • e)) 0 =
        (ContinuousLinearMap.toSpanSingleton ℝ D : ℝ →L[ℝ] F) := hf.fderiv
    have hh := congrArg (fun L : ℝ →L[ℝ] F => L (1 : ℝ)) hfd
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using hh
  have hh := congrArg (fun L : ℝ →L[ℝ] F => L (1 : ℝ)) hcomp
  have hfuneq2 : (fun y_1 : ℝ => g ((fun h : ℝ => y + h • e) y_1)) =
      (fun h : ℝ => g (y + h • e)) := by
    rfl
  rw [hfuneq2] at hh
  rw [hT] at hh
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul] at hh
  rw [← hline']
  simpa using hh.symm

lemma hasDerivAt_smul_const {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (w : F) :
    HasDerivAt (fun h : ℝ => h • w) w 0 := by
  rw [hasDerivAt_iff_hasFDerivAt]
  have hL : HasFDerivAt (fun h : ℝ => h • w) ((1 : ℝ →L[ℝ] ℝ).smulRight w) 0 := by
    exact ContinuousLinearMap.hasFDerivAt (f := (1 : ℝ →L[ℝ] ℝ).smulRight w) (x := 0)
  have hEq : ContinuousLinearMap.toSpanSingleton ℝ w = (1 : ℝ →L[ℝ] ℝ).smulRight w := by
    ext
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  rwa [hEq]

lemma hasDerivAt_const_add_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (x w : F) :
    HasDerivAt (fun h : ℝ => x + h • w) w 0 := by
  rw [hasDerivAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun h : ℝ => h • w) ((1 : ℝ →L[ℝ] ℝ).smulRight w) 0 := by
    exact ContinuousLinearMap.hasFDerivAt (f := (1 : ℝ →L[ℝ] ℝ).smulRight w) (x := 0)
  have h2 : HasFDerivAt (fun h : ℝ => x) (0 : ℝ →L[ℝ] F) 0 := hasFDerivAt_const x 0
  have h3 := h1.add h2
  have hEq' : ContinuousLinearMap.toSpanSingleton ℝ w = (1 : ℝ →L[ℝ] ℝ).smulRight w := by
    ext
    simp [ContinuousLinearMap.toSpanSingleton_apply]
  convert h3 using 1
  · funext h
    simp only [Pi.add_apply]
    rw [add_comm]
  · simp [hEq']

lemma hasDerivAt_norm_add_smul {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x w : F} (hx : x ≠ 0) :
    HasDerivAt (fun h : ℝ => ‖x + h • w‖) (inner ℝ x w / ‖x‖) 0 := by
  have hsmulw : HasDerivAt (fun h : ℝ => h • w) w 0 := hasDerivAt_smul_const w
  have hlin : HasDerivAt (fun h : ℝ => x + h • w) w 0 := by
    rw [hasDerivAt_iff_hasFDerivAt]
    have h1 : HasFDerivAt (fun h : ℝ => h • w) ((1 : ℝ →L[ℝ] ℝ).smulRight w) 0 := by
      exact ContinuousLinearMap.hasFDerivAt (f := (1 : ℝ →L[ℝ] ℝ).smulRight w) (x := 0)
    have h2 : HasFDerivAt (fun h : ℝ => x) (0 : ℝ →L[ℝ] F) 0 := hasFDerivAt_const x 0
    have h3 := h1.add h2
    have hEq' : ContinuousLinearMap.toSpanSingleton ℝ w = (1 : ℝ →L[ℝ] ℝ).smulRight w := by
      ext
      simp [ContinuousLinearMap.toSpanSingleton_apply]
    convert h3 using 1
    · funext h
      simp only [Pi.add_apply]
      rw [add_comm]
    · simp [hEq']
  have hsq : HasDerivAt (fun h : ℝ => ‖x + h • w‖ ^ 2) (2 * inner ℝ x w) 0 := by
    simpa using (HasDerivAt.norm_sq hlin)
  have hne : ‖x + (0 : ℝ) • w‖ ^ 2 ≠ 0 := by
    simpa only [zero_smul, add_zero] using (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have hsqrt := hsq.sqrt hne
  have hfun : (fun h : ℝ => ‖x + h • w‖) = (fun h : ℝ => Real.sqrt (‖x + h • w‖ ^ 2)) := by
    funext h
    rw [Real.sqrt_sq (norm_nonneg _)]
  have hval : (2 * inner ℝ x w) / (2 * ‖x‖) = inner ℝ x w / ‖x‖ := by
    field_simp [norm_pos_iff.mpr hx]
  convert hsqrt using 1
  · simp [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg _), hval]

lemma negPart_add_smul {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) (h : ℝ)
    (i : Fin k) :
    negPart hk (y + h • negBasis hk i) =
      negPart hk y + h • negUnit i := by
  change negPartCLM hk (y + h • negBasis hk i) =
      negPartCLM hk y + h • negUnit i
  rw [map_add, map_smul]
  have hneg : negPartCLM hk (negBasis hk i) = negUnit i := by
    simpa using (negPart_negBasis hk i)
  rw [hneg]

lemma posPart_add_smul {n k : ℕ} (hk : k ≤ n) (y : MorseModel n) (h : ℝ)
    (i : Fin k) :
    posPart hk (y + h • negBasis hk i) = posPart hk y := by
  ext j
  simp only [posPart, Pi.add_apply, Pi.smul_apply, negBasis]
  have h : posIdx hk j ≠ negIdx hk i := by
    intro hz
    have hval : (posIdx hk j).val = (negIdx hk i).val := congrArg Fin.val hz
    dsimp [posIdx, negIdx] at hval
    omega
  simp [h]

lemma hasDerivAt_modifiedNormalForm_negCoord {n k : ℕ} (hk : k ≤ n) (c ε δ : ℝ)
    (y : MorseModel n) (i : Fin k) :
    HasDerivAt (fun h : ℝ => modifiedNormalForm hk c ε δ
      (y + h • negBasis hk i))
      (-(negPart hk y i) * (1 + 2 * deriv (modMu ε) (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖)) 0 := by
  let e : MorseModel n := negBasis hk i
  have hu : ∀ h : ℝ, negPart hk (y + h • e) =
      negPart hk y + h • negUnit i :=
    fun h => by simpa [e] using (negPart_add_smul hk y h i)
  have hp : ∀ h : ℝ, posPart hk (y + h • e) = posPart hk y :=
    fun h => by simpa [e] using (posPart_add_smul hk y h i)
  have hlin : HasDerivAt (fun h : ℝ => negPart hk y + h • negUnit i)
      (negUnit i : EuclideanSpace ℝ (Fin k)) 0 := by
    exact hasDerivAt_const_add_smul (negPart hk y) (negUnit i)
  have ht : HasDerivAt (fun h : ℝ => ‖negPart hk (y + h • e)‖ ^ 2) (2 * negPart hk y i) 0 := by
    have h' := hlin.norm_sq
    have hfun : (fun h : ℝ => ‖negPart hk (y + h • e)‖ ^ 2) =
        (fun h : ℝ => ‖negPart hk y + h • negUnit i‖ ^ 2) := by
      funext h
      rw [hu h]
    have hval : 2 * inner ℝ (negPart hk y) (negUnit i) = 2 * negPart hk y i := by
      have hin : inner ℝ (negPart hk y) (negUnit i) = negPart hk y i := by
        rw [PiLp.inner_apply]
        rw [Finset.sum_eq_single i]
        · have hfiber : inner ℝ (negPart hk y i) (1 : ℝ) = negPart hk y i := by
            rw [real_inner_eq_re_inner]
            rw [RCLike.inner_apply']
            simp
          simpa [negUnit, negPart] using hfiber
        · intro j hj hji
          have hzero : inner ℝ (negPart hk y j) (0 : ℝ) = 0 := by
            rw [real_inner_eq_re_inner, RCLike.inner_apply']
            simp
          simpa only [hji, negUnit, negPart] using hzero
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      rw [hin]
    rw [hfun]
    simpa [hval] using h'
  have hf : HasDerivAt (fun h : ℝ => morseNormalForm hk c (y + h • e)) (-(negPart hk y i)) 0 := by
    have hsplit : (fun h : ℝ => morseNormalForm hk c (y + h • e)) =
        (fun h : ℝ => c + (1 / 2) * (‖posPart hk (y + h • e)‖ ^ 2 - ‖negPart hk (y + h • e)‖ ^ 2)) := by
      funext h
      rw [morseNormalForm_split hk c (y + h • e)]
    rw [hsplit]
    have hpos' : HasDerivAt (fun h : ℝ => ‖posPart hk (y + h • e)‖ ^ 2) 0 0 := by
      have hfun : (fun h : ℝ => ‖posPart hk (y + h • e)‖ ^ 2) = fun _ : ℝ => ‖posPart hk y‖ ^ 2 := by
        funext h
        rw [hp h]
      rw [hfun]
      exact hasDerivAt_const (c := ‖posPart hk y‖ ^ 2) (x := (0 : ℝ))
    have hsub := hpos'.sub ht
    have hmul : HasDerivAt (fun h : ℝ => (1 / 2) * (‖posPart hk (y + h • e)‖ ^ 2 - ‖negPart hk (y + h • e)‖ ^ 2))
        ((1 / 2) * (0 - 2 * negPart hk y i)) 0 :=
      hsub.const_mul (1 / 2)
    have hconst : HasDerivAt (fun _ : ℝ => c) 0 (0 : ℝ) :=
      hasDerivAt_const (x := (0 : ℝ)) (c := c)
    have hadd := HasDerivAt.add hconst hmul
    have hval : (1 / 2) * (0 - 2 * negPart hk y i) = -(negPart hk y i) := by ring
    convert hadd using 1
    · rw [hval]
      simp
  have hmu : HasDerivAt (fun h : ℝ => modMu ε (‖negPart hk (y + h • e)‖ ^ 2))
      (deriv (modMu ε) (‖negPart hk y‖ ^ 2) * (2 * negPart hk y i)) 0 := by
    have hcv : HasDerivAt (modMu ε) (deriv (modMu ε) (‖negPart hk y‖ ^ 2)) (‖negPart hk y‖ ^ 2) :=
      (differentiableAt_modMu (ε := ε) (‖negPart hk y‖ ^ 2)).hasDerivAt
    have hcv0 : HasDerivAt (modMu ε) (deriv (modMu ε) (‖negPart hk y‖ ^ 2))
        (‖negPart hk (y + (0 : ℝ) • e)‖ ^ 2) := by
      simpa using hcv
    simpa [Function.comp_def] using (hcv0.comp (x := 0) ht)
  have hga : HasDerivAt (fun h : ℝ => modGamma δ ‖posPart hk (y + h • e)‖) 0 0 := by
    have hfun : (fun h : ℝ => modGamma δ ‖posPart hk (y + h • e)‖) = fun _ : ℝ => modGamma δ ‖posPart hk y‖ := by
      funext h
      rw [hp h]
    rw [hfun]
    exact hasDerivAt_const (c := modGamma δ ‖posPart hk y‖) (x := (0 : ℝ))
  have hprod : HasDerivAt (fun h : ℝ => modMu ε (‖negPart hk (y + h • e)‖ ^ 2) * modGamma δ ‖posPart hk (y + h • e)‖)
      (deriv (modMu ε) (‖negPart hk y‖ ^ 2) * (2 * negPart hk y i) * modGamma δ ‖posPart hk y‖) 0 := by
    have hmul := hmu.mul hga
    have hval : (deriv (modMu ε) (‖negPart hk y‖ ^ 2) * (2 * negPart hk y i)) * modGamma δ ‖posPart hk y‖ +
        modMu ε (‖negPart hk y‖ ^ 2) * 0 =
        deriv (modMu ε) (‖negPart hk y‖ ^ 2) * (2 * negPart hk y i) * modGamma δ ‖posPart hk y‖ := by
      ring
    simpa [Pi.mul_apply, hval] using hmul
  have hsub := hf.sub hprod
  have hval : -(negPart hk y i) - deriv (modMu ε) (‖negPart hk y‖ ^ 2) * (2 * negPart hk y i) *
      modGamma δ ‖posPart hk y‖ =
      -(negPart hk y i) * (1 + 2 * deriv (modMu ε) (‖negPart hk y‖ ^ 2) * modGamma δ ‖posPart hk y‖) := by
    ring
  simpa [modifiedNormalForm, hval] using hsub

end

end DifferentialGeometry.Topology.Morse.CellAttachment
