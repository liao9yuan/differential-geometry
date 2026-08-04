import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.Energy

theorem weight_mul_sub_eq_intervalIntegral
    {weight dweight energy denergy : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hdenergy : ContinuousOn denergy (Icc a b))
    (henergy : ∀ t ∈ Icc a b, HasDerivAt energy (denergy t) t) :
    weight b * energy b - weight a * energy a =
      ∫ t in a..b, dweight t * energy t + weight t * denergy t := by
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have henergy_cont : ContinuousOn energy (Icc a b) :=
    fun t ht => (henergy t ht).continuousAt.continuousWithinAt
  have hintegrand : ContinuousOn
      (fun t => dweight t * energy t + weight t * denergy t) (Icc a b) :=
    (hdweight.mul henergy_cont).add (hweight_cont.mul hdenergy)
  have hintegrand_int : IntervalIntegrable
      (fun t => dweight t * energy t + weight t * denergy t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hintegrand
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t => weight t * energy t)
    (f' := fun t => dweight t * energy t + weight t * denergy t)
    hab (hweight_cont.mul henergy_cont)
    (fun t ht => (hweight t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).mul
      (henergy t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)) hintegrand_int

theorem weight_mul_energy_inequality
    {weight dweight energy denergy dissipation source : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hdenergy : ContinuousOn denergy (Icc a b))
    (henergyDeriv : ∀ t ∈ Icc a b, HasDerivAt energy (denergy t) t)
    (hdissipation : ContinuousOn dissipation (Icc a b))
    (hsource : ContinuousOn source (Icc a b))
    (henergy : ∀ t ∈ Icc a b,
      dweight t * energy t + weight t * denergy t + dissipation t ≤ source t) :
    weight b * energy b - weight a * energy a +
        ∫ t in a..b, dissipation t ≤ ∫ t in a..b, source t := by
  have hidentity := weight_mul_sub_eq_intervalIntegral
    hab hdweight hweight hdenergy henergyDeriv
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have henergy_cont : ContinuousOn energy (Icc a b) :=
    fun t ht => (henergyDeriv t ht).continuousAt.continuousWithinAt
  have hderivative : ContinuousOn
      (fun t => dweight t * energy t + weight t * denergy t) (Icc a b) :=
    (hdweight.mul henergy_cont).add (hweight_cont.mul hdenergy)
  have hleft_int : IntervalIntegrable
      (fun t => dweight t * energy t + weight t * denergy t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hderivative
  have hdiss_int : IntervalIntegrable dissipation volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hdissipation
  have hsource_int : IntervalIntegrable source volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hsource
  have hmono :
      (∫ t in a..b,
        (dweight t * energy t + weight t * denergy t) + dissipation t) ≤
          ∫ t in a..b, source t :=
    intervalIntegral.integral_mono_on hab (hleft_int.add hdiss_int) hsource_int henergy
  rw [intervalIntegral.integral_add hleft_int hdiss_int, ← hidentity] at hmono
  exact hmono

theorem intervalIntegral_le_const_mul_sup_rpow
    {lhs mass energy : ℝ → ℝ} {C S theta a b : ℝ}
    (hab : a ≤ b)
    (hlhs : ContinuousOn lhs (Icc a b))
    (henergy : ContinuousOn energy (Icc a b))
    (hC : 0 ≤ C) (htheta : 0 ≤ theta)
    (hmass_nonneg : ∀ t ∈ Icc a b, 0 ≤ mass t)
    (hmass_le : ∀ t ∈ Icc a b, mass t ≤ S)
    (henergy_nonneg : ∀ t ∈ Icc a b, 0 ≤ energy t)
    (hpoint : ∀ t ∈ Icc a b,
      lhs t ≤ C * mass t ^ theta * energy t) :
    ∫ t in a..b, lhs t ≤
      C * S ^ theta * ∫ t in a..b, energy t := by
  have hlhs_int : IntervalIntegrable lhs volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hlhs
  have hright_cont : ContinuousOn
      (fun t => (C * S ^ theta) * energy t) (Icc a b) :=
    continuousOn_const.mul henergy
  have hright_int : IntervalIntegrable
      (fun t => (C * S ^ theta) * energy t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hright_cont
  have hmono : ∀ t ∈ Icc a b,
      lhs t ≤ (C * S ^ theta) * energy t := by
    intro t ht
    refine (hpoint t ht).trans ?_
    have hrpow : mass t ^ theta ≤ S ^ theta :=
      Real.rpow_le_rpow (hmass_nonneg t ht) (hmass_le t ht) htheta
    calc
      C * mass t ^ theta * energy t ≤
          C * S ^ theta * energy t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpow hC) (henergy_nonneg t ht)
      _ = (C * S ^ theta) * energy t := rfl
  have hint := intervalIntegral.integral_mono_on hab hlhs_int hright_int hmono
  simpa only [intervalIntegral.integral_const_mul] using hint

theorem inner_mass_and_dissipation_le
    {weight mass dissipation source : ℝ → ℝ}
    {a t₀ t₁ A : ℝ}
    (hat₀ : a ≤ t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hweight : ContinuousOn weight (Icc a t₁))
    (hdissipation : ContinuousOn dissipation (Icc a t₁))
    (hweight_nonneg : ∀ t ∈ Icc a t₁, 0 ≤ weight t)
    (hdissipation_nonneg : ∀ t ∈ Icc a t₁, 0 ≤ dissipation t)
    (hweight_a : weight a = 0)
    (hweight_inner : ∀ t ∈ Icc t₀ t₁, weight t = 1)
    (hmass_nonneg : ∀ t ∈ Icc t₀ t₁, 0 ≤ mass t)
    (hsource_le : ∀ t ∈ Icc t₀ t₁, ∫ s in a..t, source s ≤ A)
    (hweighted : ∀ t ∈ Icc t₀ t₁,
      weight t * mass t - weight a * mass a +
          ∫ s in a..t, weight s * dissipation s ≤
        ∫ s in a..t, source s) :
    (∀ t ∈ Icc t₀ t₁, mass t ≤ A) ∧
      (∫ t in t₀..t₁, dissipation t) ≤ A := by
  have hat₁ : a ≤ t₁ := hat₀.trans ht₀t₁
  have hweighted_cont : ContinuousOn
      (fun t => weight t * dissipation t) (Icc a t₁) :=
    hweight.mul hdissipation
  have hmass_le : ∀ t ∈ Icc t₀ t₁, mass t ≤ A := by
    intro t ht
    have hat : a ≤ t := hat₀.trans ht.1
    have hinterval_nonneg : 0 ≤ ∫ s in a..t, weight s * dissipation s :=
      intervalIntegral.integral_nonneg hat (fun s hs =>
        mul_nonneg
          (hweight_nonneg s ⟨hs.1, hs.2.trans ht.2⟩)
          (hdissipation_nonneg s ⟨hs.1, hs.2.trans ht.2⟩))
    have h := (hweighted t ht).trans (hsource_le t ht)
    rw [hweight_inner t ht, hweight_a] at h
    simpa only [one_mul, zero_mul, zero_add] using h.trans' (by linarith)
  refine ⟨hmass_le, ?_⟩
  have hleft_cont : ContinuousOn
      (fun t => weight t * dissipation t) (Icc a t₀) :=
    hweighted_cont.mono (fun t ht => ⟨ht.1, ht.2.trans ht₀t₁⟩)
  have hinner_cont : ContinuousOn
      (fun t => weight t * dissipation t) (Icc t₀ t₁) :=
    hweighted_cont.mono (fun t ht => ⟨hat₀.trans ht.1, ht.2⟩)
  have hleft_int : IntervalIntegrable
      (fun t => weight t * dissipation t) volume a t₀ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hat₀] using hleft_cont
  have hinner_int : IntervalIntegrable
      (fun t => weight t * dissipation t) volume t₀ t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le ht₀t₁] using hinner_cont
  have hleft_nonneg : 0 ≤ ∫ t in a..t₀, weight t * dissipation t :=
    intervalIntegral.integral_nonneg hat₀ (fun t ht =>
      mul_nonneg
        (hweight_nonneg t ⟨ht.1, ht.2.trans ht₀t₁⟩)
        (hdissipation_nonneg t ⟨ht.1, ht.2.trans ht₀t₁⟩))
  have hinner_eq :
      (∫ t in t₀..t₁, weight t * dissipation t) =
        ∫ t in t₀..t₁, dissipation t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change weight t * dissipation t = dissipation t
    rw [hweight_inner t (by simpa [uIcc_of_le ht₀t₁] using ht), one_mul]
  have htotal := (hweighted t₁ ⟨ht₀t₁, le_rfl⟩).trans
    (hsource_le t₁ ⟨ht₀t₁, le_rfl⟩)
  rw [hweight_inner t₁ ⟨ht₀t₁, le_rfl⟩, hweight_a] at htotal
  simp only [one_mul, zero_mul, sub_zero] at htotal
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft_int hinner_int,
    hinner_eq] at htotal
  linarith [hmass_nonneg t₁ ⟨ht₀t₁, le_rfl⟩]

theorem norm_sq_sub_eq_intervalIntegral_inner_deriv
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {u du : ℝ → X} {a b : ℝ}
    (hab : a ≤ b)
    (hdu : ContinuousOn du (Icc a b))
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (du t) t) :
    ‖u b‖ ^ 2 - ‖u a‖ ^ 2 =
      ∫ t in a..b, 2 * inner ℝ (u t) (du t) := by
  have hu_cont : ContinuousOn u (Icc a b) :=
    fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hintegrand : ContinuousOn (fun t => 2 * inner ℝ (u t) (du t)) (Icc a b) :=
    continuousOn_const.mul (hu_cont.inner hdu)
  have hintegrand_int : IntervalIntegrable (fun t => 2 * inner ℝ (u t) (du t))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hintegrand
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t => ‖u t‖ ^ 2) (f' := fun t => 2 * inner ℝ (u t) (du t)) hab
    (hu_cont.norm.pow 2)
    (fun t ht => (hu t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).norm_sq) hintegrand_int

theorem weight_mul_norm_sq_sub_eq_intervalIntegral
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {weight dweight : ℝ → ℝ} {u du : ℝ → X} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hdu : ContinuousOn du (Icc a b))
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (du t) t) :
    weight b * ‖u b‖ ^ 2 - weight a * ‖u a‖ ^ 2 =
      ∫ t in a..b,
        dweight t * ‖u t‖ ^ 2 + weight t * (2 * inner ℝ (u t) (du t)) := by
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hu_cont : ContinuousOn u (Icc a b) :=
    fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hintegrand : ContinuousOn
      (fun t => dweight t * ‖u t‖ ^ 2 + weight t * (2 * inner ℝ (u t) (du t)))
      (Icc a b) :=
    (hdweight.mul (hu_cont.norm.pow 2)).add
      (hweight_cont.mul (continuousOn_const.mul (hu_cont.inner hdu)))
  have hintegrand_int : IntervalIntegrable
      (fun t => dweight t * ‖u t‖ ^ 2 + weight t * (2 * inner ℝ (u t) (du t)))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hintegrand
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t => weight t * ‖u t‖ ^ 2)
    (f' := fun t => dweight t * ‖u t‖ ^ 2 + weight t * (2 * inner ℝ (u t) (du t)))
    hab _ _ hintegrand_int
  · exact hweight_cont.mul (hu_cont.norm.pow 2)
  · intro t ht
    exact (hweight t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).mul
      ((hu t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).norm_sq)

theorem weight_mul_norm_sq_energy_inequality
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {weight dweight : ℝ → ℝ} {u du : ℝ → X}
    {dissipation source : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hdu : ContinuousOn du (Icc a b))
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (du t) t)
    (hdissipation : ContinuousOn dissipation (Icc a b))
    (hsource : ContinuousOn source (Icc a b))
    (henergy : ∀ t ∈ Icc a b,
      dweight t * ‖u t‖ ^ 2 + weight t * (2 * inner ℝ (u t) (du t)) +
        dissipation t ≤ source t) :
    weight b * ‖u b‖ ^ 2 - weight a * ‖u a‖ ^ 2 +
        ∫ t in a..b, dissipation t ≤ ∫ t in a..b, source t := by
  have hidentity := weight_mul_norm_sq_sub_eq_intervalIntegral
    hab hdweight hweight hdu hu
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hu_cont : ContinuousOn u (Icc a b) :=
    fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hderivative : ContinuousOn
      (fun t => dweight t * ‖u t‖ ^ 2 + weight t * (2 * inner ℝ (u t) (du t)))
      (Icc a b) :=
    (hdweight.mul (hu_cont.norm.pow 2)).add
      (hweight_cont.mul (continuousOn_const.mul (hu_cont.inner hdu)))
  have hleft_int : IntervalIntegrable
      (fun t => dweight t * ‖u t‖ ^ 2 + weight t * (2 * inner ℝ (u t) (du t)))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hderivative
  have hdiss_int : IntervalIntegrable dissipation volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hdissipation
  have hsource_int : IntervalIntegrable source volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hsource
  have hmono : (∫ t in a..b,
      (dweight t * ‖u t‖ ^ 2 + weight t * (2 * inner ℝ (u t) (du t))) +
        dissipation t) ≤ ∫ t in a..b, source t :=
    intervalIntegral.integral_mono_on hab (hleft_int.add hdiss_int) hsource_int henergy
  rw [intervalIntegral.integral_add hleft_int hdiss_int, ← hidentity] at hmono
  exact hmono

end DifferentialGeometry.Analysis.Parabolic.Energy

end
