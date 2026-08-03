import DifferentialGeometry.Analysis.Schauder.Localization
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section

open scoped NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {X A B C : Type*} [MetricSpace X]
  [NormedAddCommGroup A] [NormedSpace Real A]
  [NormedAddCommGroup B] [NormedSpace Real B]
  [NormedAddCommGroup C] [NormedSpace Real C]

theorem holderWith_bilinear_of_norm_le
    {alpha Kf Kg Mf Mg : NNReal}
    (L : A →L[Real] B →L[Real] C)
    (hL : ∀ a b, ‖L a b‖ ≤ ‖a‖ * ‖b‖)
    {f : X → A} {g : X → B}
    (hf : HolderWith Kf alpha f) (hg : HolderWith Kg alpha g)
    (hfnorm : ∀ x, ‖f x‖ ≤ Mf) (hgnorm : ∀ x, ‖g x‖ ≤ Mg) :
    HolderWith (Mf * Kg + Mg * Kf) alpha (fun x ↦ L (f x) (g x)) := by
  intro x y
  rw [edist_dist, edist_dist]
  have hfirst :
      ‖L (f x) (g x - g y)‖ ≤
        (Mf : Real) * ((Kg : Real) * dist x y ^ (alpha : Real)) := by
    calc
      ‖L (f x) (g x - g y)‖ ≤
          ‖f x‖ * ‖g x - g y‖ := hL _ _
      _ ≤ (Mf : Real) *
          ((Kg : Real) * dist x y ^ (alpha : Real)) := by
        gcongr
        · exact hfnorm x
        · simpa only [dist_eq_norm] using hg.dist_le x y
      _ = (Mf : Real) *
          ((Kg : Real) * dist x y ^ (alpha : Real)) := by ring
  have hsecond :
      ‖L (f x - f y) (g y)‖ ≤
        ((Kf : Real) * dist x y ^ (alpha : Real)) * (Mg : Real) := by
    calc
      ‖L (f x - f y) (g y)‖ ≤
          ‖f x - f y‖ * ‖g y‖ := hL _ _
      _ ≤ ((Kf : Real) * dist x y ^ (alpha : Real)) *
          (Mg : Real) := by
        gcongr
        · simpa only [dist_eq_norm] using hf.dist_le x y
        · exact hgnorm y
      _ = ((Kf : Real) * dist x y ^ (alpha : Real)) * (Mg : Real) := by ring
  have hreal : dist (L (f x) (g x)) (L (f y) (g y)) ≤
      ((Mf * Kg + Mg * Kf : NNReal) : Real) *
        dist x y ^ (alpha : Real) := by
    rw [dist_eq_norm]
    calc
      ‖L (f x) (g x) - L (f y) (g y)‖ =
          ‖L (f x) (g x - g y) + L (f x - f y) (g y)‖ := by
        congr 1
        simp only [map_sub, ContinuousLinearMap.sub_apply]
        abel
      _ ≤ ‖L (f x) (g x - g y)‖ +
          ‖L (f x - f y) (g y)‖ := norm_add_le _ _
      _ ≤ (Mf : Real) * ((Kg : Real) * dist x y ^ (alpha : Real)) +
          ((Kf : Real) * dist x y ^ (alpha : Real)) * (Mg : Real) :=
        add_le_add hfirst hsecond
      _ = ((Mf * Kg + Mg * Kf : NNReal) : Real) *
          dist x y ^ (alpha : Real) := by
        push_cast
        ring
  calc
    ENNReal.ofReal (dist (L (f x) (g x)) (L (f y) (g y))) ≤
        ENNReal.ofReal (((Mf * Kg + Mg * Kf : NNReal) : Real) *
          dist x y ^ (alpha : Real)) := ENNReal.ofReal_le_ofReal hreal
    _ = ((Mf * Kg + Mg * Kf : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul (by positivity :
        (0 : Real) ≤ ((Mf * Kg + Mg * Kf : NNReal) : Real))]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = ((Mf * Kg + Mg * Kf : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]

theorem holderWith_bilinear_of_opNorm_le_one
    {alpha Kf Kg Mf Mg : NNReal}
    (L : A →L[Real] B →L[Real] C) (hL : ‖L‖ ≤ 1)
    {f : X → A} {g : X → B}
    (hf : HolderWith Kf alpha f) (hg : HolderWith Kg alpha g)
    (hfnorm : ∀ x, ‖f x‖ ≤ Mf) (hgnorm : ∀ x, ‖g x‖ ≤ Mg) :
    HolderWith (Mf * Kg + Mg * Kf) alpha (fun x ↦ L (f x) (g x)) := by
  apply holderWith_bilinear_of_norm_le L
  · intro a b
    have hLa : ‖L‖ * ‖a‖ ≤ ‖a‖ := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hL (norm_nonneg a)
    exact (L.le_opNorm₂ a b).trans
      (mul_le_mul_of_nonneg_right hLa (norm_nonneg b))
  · exact hf
  · exact hg
  · exact hfnorm
  · exact hgnorm

end DifferentialGeometry.Analysis.Schauder

end
