import DifferentialGeometry.Analysis.Calculus.RatioMonotonicity
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Hyperbolic radial comparison model

This file defines the nonpositive-curvature radial model used by the
Bishop--Gromov route.  The parameter `q >= 0` is the square root of the
absolute curvature scale, so the warping function is `sinh (q r) / q`, with
its continuous `q = 0` specialization `r`.
-/

noncomputable section

open Set

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

/-- Hyperbolic radial warping function, including the Euclidean `q = 0`
case. -/
def hypSn (q r : ℝ) : ℝ :=
  if q = 0 then r else Real.sinh (q * r) / q

/-- Radial derivative of `hypSn`. -/
def hypSnDeriv (q r : ℝ) : ℝ :=
  if q = 0 then 1 else Real.cosh (q * r)

/-- The hyperbolic warping function has the expected radial derivative. -/
theorem hasDerivAt_hypSn (q r : ℝ) :
    HasDerivAt (hypSn q) (hypSnDeriv q r) r := by
  by_cases hq : q = 0
  · subst q
    have hfun : hypSn 0 = fun x : ℝ => x := by
      funext x
      simp [hypSn]
    rw [hfun]
    simp only [hypSnDeriv]
    exact hasDerivAt_id r
  · have h := ((hasDerivAt_id r).const_mul q).sinh.div_const q
    have hfun : hypSn q = fun x : ℝ => Real.sinh (q * x) / q := by
      funext x
      simp [hypSn, hq]
    rw [hfun]
    simpa [hypSnDeriv, hq] using h

/-- The radial derivative of the hyperbolic warping function satisfies the
model Jacobi equation. -/
theorem hasDerivAt_hypSnD (q r : ℝ) :
    HasDerivAt (hypSnDeriv q) (q ^ 2 * hypSn q r) r := by
  by_cases hq : q = 0
  · subst q
    have hfun : hypSnDeriv 0 = fun _ : ℝ => 1 := by
      funext x
      simp [hypSnDeriv]
    rw [hfun]
    simpa [hypSn] using
      (hasDerivAt_const (x := r) (c := (1 : ℝ)))
  · have h := ((hasDerivAt_id r).const_mul q).cosh
    have hfun : hypSnDeriv q = fun x : ℝ => Real.cosh (q * x) := by
      funext x
      simp [hypSnDeriv, hq]
    have hderiv : Real.sinh (q * r) * q = q ^ 2 * hypSn q r := by
      rw [hypSn, if_neg hq]
      field_simp
    have hderiv' : Real.sinh (q * id r) * (q * 1) = q ^ 2 * hypSn q r := by
      simpa only [id_eq, mul_one] using hderiv
    rw [hfun]
    simpa only [id_eq, mul_one] using h.congr_deriv hderiv'

/-- Conserved energy identity for the hyperbolic warping function. -/
theorem hypSn_energy (q r : ℝ) :
    hypSnDeriv q r ^ 2 - q ^ 2 * hypSn q r ^ 2 = 1 := by
  by_cases hq : q = 0
  · subst q
    simp [hypSnDeriv, hypSn]
  · rw [hypSnDeriv, if_neg hq, hypSn, if_neg hq]
    calc
      Real.cosh (q * r) ^ 2 - q ^ 2 * (Real.sinh (q * r) / q) ^ 2 =
          Real.cosh (q * r) ^ 2 - Real.sinh (q * r) ^ 2 := by
        field_simp
      _ = 1 := Real.cosh_sq_sub_sinh_sq (q * r)

/-- The hyperbolic radial warping function is continuous in the radius. -/
theorem hypSn_continuous (q : ℝ) : Continuous (hypSn q) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_hypSn q r).continuousAt

/-- `hypSn q r` is positive at positive radius when `q` is nonnegative. -/
theorem hypSn_pos {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) :
    0 < hypSn q r := by
  by_cases hq0 : q = 0
  · simpa [hypSn, hq0] using hr
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    rw [hypSn, if_neg hq0]
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hqpos hr)) hqpos

/-- Hyperbolic radial area density in transverse dimension `d`. -/
def hypDensity (q : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  hypSn q r ^ d

/-- Radial derivative of the hyperbolic area density. -/
def hypDensityDeriv (q : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  (d : ℝ) * hypSn q r ^ (d - 1) * hypSnDeriv q r

/-- The hyperbolic area density has the power-rule derivative. -/
theorem hasDerivAt_hypDen (q : ℝ) (d : ℕ) (r : ℝ) :
    HasDerivAt (hypDensity q d) (hypDensityDeriv q d r) r := by
  simpa [hypDensity, hypDensityDeriv] using (hasDerivAt_hypSn q r).pow d

/-- The hyperbolic radial area density is continuous in the radius. -/
theorem hypDen_continuous (q : ℝ) (d : ℕ) : Continuous (hypDensity q d) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_hypDen q d r).continuousAt

/-- Logarithmic radial derivative of the hyperbolic area density. -/
def hypMeanCurv (q : ℝ) (d : ℕ) (r : ℝ) : ℝ :=
  (d : ℝ) * hypSnDeriv q r / hypSn q r

/-- The hyperbolic model mean curvature satisfies its scalar Riccati equation. -/
theorem hasDerivAt_hypMean
    {q r : ℝ} {d : ℕ} (hq : 0 ≤ q) (hr : 0 < r) (hd : 0 < d) :
    HasDerivAt (hypMeanCurv q d)
      ((d : ℝ) * q ^ 2 - hypMeanCurv q d r ^ 2 / (d : ℝ)) r := by
  have hsn : hypSn q r ≠ 0 := ne_of_gt (hypSn_pos hq hr)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have h := ((hasDerivAt_hypSnD q r).const_mul (d : ℝ)).fun_div
    (hasDerivAt_hypSn q r) hsn
  refine h.congr_deriv ?_
  simp only [hypMeanCurv]
  field_simp

/-- The model density derivative is its mean curvature times the density. -/
theorem hypDenDeriv_eq_mean
    {q r : ℝ} {d : ℕ} (hq : 0 ≤ q) (hr : 0 < r) :
    hypDensityDeriv q d r = hypMeanCurv q d r * hypDensity q d r := by
  have hsn : hypSn q r ≠ 0 := ne_of_gt (hypSn_pos hq hr)
  cases d with
  | zero => simp [hypDensityDeriv, hypMeanCurv, hypDensity]
  | succ d =>
      simp only [hypDensityDeriv, hypMeanCurv, hypDensity, Nat.cast_succ,
        Nat.succ_sub_one, pow_succ]
      field_simp

/-- The hyperbolic area density is positive at positive radius. -/
theorem hypDensity_pos {q r : ℝ} {d : ℕ} (hq : 0 ≤ q) (hr : 0 < r) :
    0 < hypDensity q d r := by
  exact pow_pos (hypSn_pos hq hr) d

/-- A radial density satisfying the Bishop cross-derivative inequality has
antitone ratio to the hyperbolic model density. -/
theorem hypRatio_anti
    {j j' : ℝ → ℝ} {q a b : ℝ} {d : ℕ}
    (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hj : ∀ r ∈ Ioo a b, HasDerivAt j (j' r) r)
    (hcross : ∀ r ∈ Ioo a b,
      j' r * hypDensity q d r ≤ j r * hypDensityDeriv q d r) :
    AntitoneOn (fun r => j r / hypDensity q d r) (Ioo a b) := by
  refine ratio_anti_of_cross hj
    (fun r _hr => hasDerivAt_hypDen q d r) ?_ hcross
  intro r hr
  exact hypDensity_pos hq (lt_of_le_of_lt ha hr.1)

/-- The Bishop cross-derivative inequality implies monotonicity of the
cumulative radial volume ratio. -/
theorem hypVolumeRatio_anti
    {j j' : ℝ → ℝ} {q b : ℝ} {d : ℕ}
    (hq : 0 ≤ q)
    (hjcont : Continuous j)
    (hj : ∀ r ∈ Ioo (0 : ℝ) b, HasDerivAt j (j' r) r)
    (hcross : ∀ r ∈ Ioo (0 : ℝ) b,
      j' r * hypDensity q d r ≤ j r * hypDensityDeriv q d r) :
    AntitoneOn
      (fun r => (∫ x in 0..r, j x) / ∫ x in 0..r, hypDensity q d x)
      (Ioo (0 : ℝ) b) := by
  refine integralRatio_anti hjcont (hypDen_continuous q d) ?_ ?_
  · intro r hr
    exact hypDensity_pos hq hr.1
  · exact hypRatio_anti hq le_rfl hj hcross

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
