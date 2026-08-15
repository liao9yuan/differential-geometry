import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem second_deriv_nonneg {L : ℝ → ℝ} {x c : ℝ}
    (hmin : IsLocalMin L x) (hL' : HasDerivAt L 0 x)
    (hL'' : HasDerivAt (deriv L) c x) : 0 ≤ c := by
  by_contra hc
  push Not at hc
  have hderiv0 : deriv L x = 0 := hL'.deriv
  have hsecond : deriv (deriv L) x = c := hL''.deriv
  have hmax : IsLocalMax L x :=
    isLocalMax_of_deriv_deriv_neg (by rw [hsecond]; exact hc)
      hderiv0 hL'.continuousAt
  have hconst : L =ᶠ[𝓝 x] (fun _ => L x) :=
    eventuallyEq_of_isMinFilter_of_isMaxFilter hmin hmax
  have hderiv_const : deriv L =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    have h := hconst.deriv
    refine h.trans ?_
    filter_upwards with y using deriv_const y (L x)
  have hL''0 : HasDerivAt (deriv L) c x := hL''
  rw [hderiv_const.hasDerivAt_iff] at hL''0
  have hzero : c = 0 := hL''0.unique (hasDerivAt_const x (0 : ℝ))
  exact absurd hzero (ne_of_lt hc)

theorem concaveOn_of_upper
    {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D)
    (hsupport : ∀ x ∈ interior D,
      ∃ φ : ℝ → ℝ,
        ContDiffAt ℝ 2 φ x ∧
        φ x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ φ y) ∧
        deriv (deriv φ) x ≤ 0) :
    ConcaveOn ℝ D f := by
  refine concaveOn_of_slope_anti_adjacent hD ?_
  intro a b c ha hc hab hbc
  by_contra hslope_le
  have hslope :
      (f b - f a) / (b - a) < (f c - f b) / (c - b) :=
    lt_of_not_ge hslope_le
  have hba : 0 < b - a := sub_pos.mpr hab
  have hcb : 0 < c - b := sub_pos.mpr hbc
  have hca : 0 < c - a := sub_pos.mpr (hab.trans hbc)
  have hcross :
      (f b - f a) * (c - b) < (f c - f b) * (b - a) :=
    (div_lt_div_iff₀ hba hcb).mp hslope
  have hscaled :
      (f b - f a) * (c - a) < (f c - f a) * (b - a) := by
    nlinarith
  let m : ℝ := (f c - f a) / (c - a)
  let line : ℝ → ℝ := fun y => f a + m * (y - a)
  have hline_a : line a = f a := by
    simp [line]
  have hline_c : line c = f c := by
    dsimp only [line, m]
    field_simp [hca.ne']
    ring
  have hfb : f b < line b := by
    have hdiff :
        f b - f a < (f c - f a) / (c - a) * (b - a) := by
      rw [div_mul_eq_mul_div]
      exact (lt_div_iff₀ hca).2 hscaled
    dsimp only [line, m]
    linarith
  let gap : ℝ := line b - f b
  let P : ℝ := (b - a) * (c - b)
  have hgap : 0 < gap := by
    dsimp only [gap]
    linarith
  have hP : 0 < P := by
    exact mul_pos hba hcb
  let κ : ℝ := gap / (2 * P)
  have hκ : 0 < κ := by
    exact div_pos hgap (mul_pos (by norm_num) hP)
  have hκP : κ * P = gap / 2 := by
    dsimp only [κ]
    field_simp [hP.ne']
  let q : ℝ → ℝ := fun y =>
    -line y + κ * ((y - a) * (c - y))
  let w : ℝ → ℝ := fun y => f y + q y
  have hwa : w a = 0 := by
    simp [w, q, hline_a]
  have hwc : w c = 0 := by
    simp [w, q, hline_c]
  have hwb : w b < 0 := by
    change f b + (-line b + κ * P) < 0
    rw [hκP]
    dsimp only [gap]
    linarith
  have hac : a < c := hab.trans hbc
  have hacD : Icc a c ⊆ D := hD.ordConnected.out ha hc
  have hline_cont : Continuous line := by
    dsimp only [line]
    fun_prop
  have hq_cont : Continuous q := by
    dsimp only [q]
    fun_prop
  have hw_cont : ContinuousOn w (Icc a c) := by
    exact (hf.mono hacD).add hq_cont.continuousOn
  obtain ⟨p, hpIcc, hpmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hac.le) hw_cont
  have hbIcc : b ∈ Icc a c := ⟨hab.le, hbc.le⟩
  have hpneg : w p < 0 := (hpmin hbIcc).trans_lt hwb
  have hap_ne : a ≠ p := by
    intro hap
    rw [← hap, hwa] at hpneg
    exact (lt_irrefl 0) hpneg
  have hpc_ne : p ≠ c := by
    intro hpc
    rw [hpc, hwc] at hpneg
    exact (lt_irrefl 0) hpneg
  have hap : a < p := lt_of_le_of_ne hpIcc.1 hap_ne
  have hpc : p < c := lt_of_le_of_ne hpIcc.2 hpc_ne
  have hIooD : Ioo a c ⊆ interior D :=
    subset_sUnion_of_mem
      ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hacD⟩
  obtain ⟨φ, hφ, hφp, hupper, hφ2⟩ :=
    hsupport p (hIooD ⟨hap, hpc⟩)
  let ψ : ℝ → ℝ := fun y => φ y + q y
  have hlocal : IsLocalMin ψ p := by
    filter_upwards [hupper, isOpen_Ioo.mem_nhds ⟨hap, hpc⟩] with y hy hyIoo
    calc
      ψ p = w p := by
        dsimp only [ψ, w]
        rw [hφp]
      _ ≤ w y := hpmin (Ioo_subset_Icc_self hyIoo)
      _ ≤ ψ y := by
        dsimp only [w, ψ]
        linarith
  let q' : ℝ → ℝ := fun y =>
    -m + κ * ((c - y) - (y - a))
  have hline' (y : ℝ) : HasDerivAt line m y := by
    dsimp only [line]
    convert (hasDerivAt_const y (f a)).add
      (((hasDerivAt_id y).sub_const a).const_mul m) using 1
    all_goals ring
  have hq' (y : ℝ) : HasDerivAt q (q' y) y := by
    have hya : HasDerivAt (fun z : ℝ => z - a) 1 y :=
      (hasDerivAt_id y).sub_const a
    have hcy : HasDerivAt (fun z : ℝ => c - z) (-1) y :=
      by simpa only [Pi.sub_apply, id_eq, zero_sub] using
        (hasDerivAt_const y c).sub (hasDerivAt_id y)
    dsimp only [q, q']
    convert (hline' y).neg.add ((hya.mul hcy).const_mul κ) using 1
    all_goals ring
  have hq'' (y : ℝ) : HasDerivAt q' (-2 * κ) y := by
    have hcy : HasDerivAt (fun z : ℝ => c - z) (-1) y :=
      by simpa only [Pi.sub_apply, id_eq, zero_sub] using
        (hasDerivAt_const y c).sub (hasDerivAt_id y)
    have hya : HasDerivAt (fun z : ℝ => z - a) 1 y :=
      (hasDerivAt_id y).sub_const a
    dsimp only [q']
    convert (hasDerivAt_const y (-m)).add
      ((hcy.sub hya).const_mul κ) using 1
    all_goals ring
  have hφdiff : ∀ᶠ y in 𝓝 p, DifferentiableAt ℝ φ y := by
    filter_upwards [hφ.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hderiv :
      deriv ψ =ᶠ[𝓝 p] fun y => deriv φ y + q' y := by
    filter_upwards [hφdiff] with y hy
    dsimp only [ψ]
    simpa only [Pi.add_apply, (hq' y).deriv] using
      deriv_add hy (hq' y).differentiableAt
  have hφderiv : DifferentiableAt ℝ (deriv φ) p := by
    have hd : ContDiffAt ℝ 1 (deriv φ) p :=
      hφ.derivWithin (m := 1) (by norm_num)
    exact hd.differentiableAt (by norm_num)
  have hψdiff : DifferentiableAt ℝ ψ p := by
    exact (hφ.differentiableAt (by norm_num)).add (hq' p).differentiableAt
  have hψ' : HasDerivAt ψ 0 p := by
    simpa only [hlocal.deriv_eq_zero] using hψdiff.hasDerivAt
  have hψ'' :
      HasDerivAt (deriv ψ) (deriv (deriv φ) p - 2 * κ) p := by
    rw [hderiv.hasDerivAt_iff]
    convert hφderiv.hasDerivAt.add (hq'' p) using 1
    all_goals ring
  have hnonneg := second_deriv_nonneg hlocal hψ' hψ''
  linarith

theorem concaveOn_sub_sq
    {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} {C : ℝ}
    (hf : ContinuousOn f D)
    (hsupport : ∀ x ∈ interior D,
      ∃ φ : ℝ → ℝ,
        ContDiffAt ℝ 2 φ x ∧
        φ x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ φ y) ∧
        deriv (deriv φ) x ≤ C) :
    ConcaveOn ℝ D (fun x => f x - C / 2 * x ^ 2) := by
  let q : ℝ → ℝ := fun x => (-(C / 2)) * (x * x)
  have hq_cont : Continuous q := by
    dsimp only [q]
    fun_prop
  have hconc : ConcaveOn ℝ D (fun x => f x + q x) := by
    apply concaveOn_of_upper (f := fun x => f x + q x) hD
      (hf.add hq_cont.continuousOn)
    intro x hx
    obtain ⟨φ, hφ, hφx, hupper, hφ2⟩ := hsupport x hx
    let ψ : ℝ → ℝ := fun y => φ y + q y
    let q' : ℝ → ℝ := fun y => -C * y
    have hq' (y : ℝ) : HasDerivAt q (q' y) y := by
      dsimp only [q, q']
      convert ((hasDerivAt_id y).mul (hasDerivAt_id y)).const_mul (-(C / 2)) using 1
      all_goals simp only [id_eq]
      all_goals ring
    have hq'' (y : ℝ) : HasDerivAt q' (-C) y := by
      dsimp only [q']
      simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul (-C)
    have hq_cd : ContDiffAt ℝ 2 q x := by
      dsimp only [q]
      fun_prop
    refine ⟨ψ, ContDiffAt.add hφ hq_cd, ?_, ?_, ?_⟩
    · dsimp only [ψ]
      rw [hφx]
    · filter_upwards [hupper] with y hy
      dsimp only [ψ]
      linarith
    · have hφdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ y := by
        filter_upwards [hφ.eventually (by norm_num)] with y hy
        exact hy.differentiableAt (by norm_num)
      have hderiv :
          deriv ψ =ᶠ[𝓝 x] fun y => deriv φ y + q' y := by
        filter_upwards [hφdiff] with y hy
        dsimp only [ψ]
        simpa only [Pi.add_apply, (hq' y).deriv] using
          deriv_add hy (hq' y).differentiableAt
      have hφderiv : DifferentiableAt ℝ (deriv φ) x := by
        have hd : ContDiffAt ℝ 1 (deriv φ) x :=
          hφ.derivWithin (m := 1) (by norm_num)
        exact hd.differentiableAt (by norm_num)
      calc
        deriv (deriv ψ) x =
            deriv (fun y => deriv φ y + q' y) x := hderiv.deriv_eq
        _ = deriv (deriv φ) x + (-C) := by
          simpa only [Pi.add_apply, (hq'' x).deriv] using
            deriv_add hφderiv (hq'' x).differentiableAt
        _ ≤ 0 := by linarith
  have heq : (fun x => f x + q x) =
      (fun x => f x - C / 2 * x ^ 2) := by
    funext x
    dsimp only [q]
    ring
  rw [← heq]
  exact hconc

theorem concaveOn_tendsto
    {D : Set ℝ} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, ConcaveOn ℝ D (f n))
    (hlim : ∀ x ∈ D, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ConcaveOn ℝ D g := by
  refine ⟨(hf 0).1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a • x + b • y ∈ D := (hf 0).1 hx hy ha hb hab
  apply tendsto_le_of_eventuallyLE
    (((hlim x hx).const_mul a).add ((hlim y hy).const_mul b))
    (hlim (a • x + b • y) hz)
  filter_upwards with n
  exact (hf n).2 hx hy ha hb hab

end DifferentialGeometry.Analysis
