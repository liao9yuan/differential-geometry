import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.Energy

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
