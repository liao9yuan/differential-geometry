import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammSpaces
import DifferentialGeometry.Analysis.Parabolic.Euclidean.RoughCarleson

/-!
# The early divergence arm in the Koch--Lamm source space

This file identifies the local `R^{-n/2} L²` arm of `KLSource1` with the
gradient-Carleson class consumed by the global early first-derivative heat
potential.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The inverse local Koch--Lamm `L²` scale is `R^(n/2)`. -/
theorem klL2Scale_inv {R : ℝ} (hR : 0 < R) :
    (klL2Scale (V := V) R)⁻¹ =
      ENNReal.ofReal (Real.rpow R (klDim V / 2)) := by
  unfold klL2Scale klL2ScaleR
  have hpow : 0 < Real.rpow R (-klDim V / 2) :=
    Real.rpow_pos_of_pos hR _
  rw [← ENNReal.ofReal_inv_of_pos hpow]
  congr 1
  rw [show -klDim V / 2 = -(klDim V / 2) by ring]
  have hneg := Real.rpow_neg hR.le (klDim V / 2)
  calc
    (Real.rpow R (-(klDim V / 2)))⁻¹ =
        ((Real.rpow R (klDim V / 2))⁻¹)⁻¹ :=
      congrArg (fun z : ℝ => z⁻¹) hneg
    _ = Real.rpow R (klDim V / 2) := inv_inv _

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Squaring the inverse local `L²` scale gives the spatial volume power. -/
theorem klL2_inv_sq {R : ℝ} (hR : 0 < R) :
    ((klL2Scale (V := V) R)⁻¹) ^ 2 =
      ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
  rw [klL2Scale_inv (V := V) hR]
  have hpow : ENNReal.ofReal
      ((Real.rpow R (klDim V / 2)) ^ 2) =
      (ENNReal.ofReal (Real.rpow R (klDim V / 2))) ^ 2 :=
    ENNReal.ofReal_pow (Real.rpow_nonneg hR.le _) 2
  have hreal : (Real.rpow R (klDim V / 2)) ^ 2 =
      R ^ Module.finrank ℝ V := by
    calc
      (Real.rpow R (klDim V / 2)) ^ 2 =
          Real.rpow R (klDim V / 2 * 2) :=
        (Real.rpow_mul_natCast hR.le (klDim V / 2) 2).symm
      _ = Real.rpow R (Module.finrank ℝ V) := by
        congr 1
        simp [klDim]
      _ = R ^ Module.finrank ℝ V := Real.rpow_natCast _ _
  rw [← hpow, hreal]

omit [Nontrivial V] [NormedSpace ℝ F] in
/-- The rough gradient mass is the square of the local `eLpNorm 2`. -/
theorem gradMass_eq_l2sq (f : ℝ × V → F) (x : V) (R : ℝ) :
    gradMass f x R =
      (eLpNorm f 2
        ((klVolume : Measure (ℝ × V)).restrict (klCyl x R))) ^ 2 := by
  let μ : Measure (ℝ × V) :=
    (klVolume : Measure (ℝ × V)).restrict (klCyl x R)
  have hl2 := eLpNorm_nnreal_pow_eq_lintegral
    (μ := μ) (f := f) (p := (2 : ℝ≥0)) (by norm_num)
  change (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μ) = _
  calc
    (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μ) =
        ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂μ := by
      apply lintegral_congr
      intro z
      rw [ENNReal.rpow_two, ← ofReal_norm_eq_enorm,
        ← ENNReal.ofReal_pow (norm_nonneg _) 2]
    _ = eLpNorm f 2 μ ^ (2 : ℝ) := hl2.symm
    _ = eLpNorm f 2 μ ^ 2 := ENNReal.rpow_two _

omit [Nontrivial V] [NormedSpace ℝ F] in
/-- The local `L²` arm of a Koch--Lamm divergence source is exactly the
gradient-Carleson estimate needed by the early first-derivative potential. -/
theorem kl1_to_gradCarl {T : ℝ} {A₂ Aₚ : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource1 T A₂ Aₚ f) :
    GradCarl T ((A₂ : ℝ≥0∞) ^ 2) f := by
  refine ⟨?_, ?_⟩
  · simpa [klVolume, stVolume] using h.ae
  · intro x R hR hRT
    have hb := h.local_l2 x R hR hRT
    have hs0 : klL2Scale (V := V) R ≠ 0 := by
      exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hR (-klDim V / 2))).ne'
    have hsT : klL2Scale (V := V) R ≠ ∞ := ENNReal.ofReal_ne_top
    have hi := (ENNReal.mul_le_iff_le_inv hs0 hsT).mp hb
    have hi2 :
        (eLpNorm f 2
          ((klVolume : Measure (ℝ × V)).restrict (klCyl x R))) ^ 2 ≤
        ((klL2Scale (V := V) R)⁻¹ * (A₂ : ℝ≥0∞)) ^ 2 := by
      gcongr
    rw [gradMass_eq_l2sq (V := V) f x R]
    calc
      (eLpNorm f 2
          ((klVolume : Measure (ℝ × V)).restrict (klCyl x R))) ^ 2 ≤
          ((klL2Scale (V := V) R)⁻¹ * (A₂ : ℝ≥0∞)) ^ 2 := hi2
      _ = (A₂ : ℝ≥0∞) ^ 2 *
          ENNReal.ofReal (R ^ Module.finrank ℝ V) := by
        rw [mul_pow, klL2_inv_sq (V := V) hR]
        ac_rfl

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
