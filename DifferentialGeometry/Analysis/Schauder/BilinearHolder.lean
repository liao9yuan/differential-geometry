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

theorem holderWith_bilinear_of_restrict_of_support
    {s : Set X} {alpha Kf Kg Mf Mg : NNReal}
    (L : A →L[Real] B →L[Real] C)
    (hL : ∀ a b, ‖L a b‖ ≤ ‖a‖ * ‖b‖)
    {f : X → A} {g : X → B}
    (hf : HolderWith Kf alpha (s.restrict f))
    (hg : HolderWith Kg alpha g)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf)
    (hgnorm : ∀ x, ‖g x‖ ≤ Mg)
    (hgsupport : ∀ x, x ∉ s → g x = 0) :
    HolderWith (Mf * Kg + Mg * Kf) alpha (fun x ↦ L (f x) (g x)) := by
  have hlocal : HolderWith (Mf * Kg + Mg * Kf) alpha
      (s.restrict fun x ↦ L (f x) (g x)) := by
    have hgrestrict : HolderWith Kg alpha (s.restrict g) :=
      (hg.holderOnWith s).holderWith
    exact holderWith_bilinear_of_norm_le L hL hf hgrestrict
      (fun x ↦ hfnorm x x.2) (fun x ↦ hgnorm x)
  intro x y
  rw [edist_dist, edist_dist]
  have hreal : dist (L (f x) (g x)) (L (f y) (g y)) ≤
      ((Mf * Kg + Mg * Kf : NNReal) : Real) *
        dist x y ^ (alpha : Real) := by
    by_cases hx : x ∈ s
    · by_cases hy : y ∈ s
      · simpa only [Set.restrict_apply, Subtype.dist_eq] using
          hlocal.dist_le (⟨x, hx⟩ : s) (⟨y, hy⟩ : s)
      · rw [hgsupport y hy, map_zero, dist_zero_right]
        calc
          ‖L (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖ := hL _ _
          _ ≤ (Mf : Real) * ((Kg : Real) *
                dist x y ^ (alpha : Real)) := by
            gcongr
            · exact hfnorm x hx
            · simpa only [dist_eq_norm, hgsupport y hy, sub_zero] using
                hg.dist_le x y
          _ ≤ ((Mf * Kg + Mg * Kf : NNReal) : Real) *
                dist x y ^ (alpha : Real) := by
            push_cast
            have hpow : 0 ≤ dist x y ^ (alpha : Real) :=
              Real.rpow_nonneg (dist_nonneg) _
            calc
              (Mf : Real) * ((Kg : Real) * dist x y ^ (alpha : Real)) =
                  ((Mf : Real) * Kg) * dist x y ^ (alpha : Real) := by ring
              _ ≤ ((Mf : Real) * Kg + (Mg : Real) * Kf) *
                    dist x y ^ (alpha : Real) :=
                mul_le_mul_of_nonneg_right
                  (le_add_of_nonneg_right
                    (mul_nonneg Mg.coe_nonneg Kf.coe_nonneg)) hpow
    · by_cases hy : y ∈ s
      · rw [hgsupport x hx, map_zero, dist_zero_left]
        calc
          ‖L (f y) (g y)‖ ≤ ‖f y‖ * ‖g y‖ := hL _ _
          _ ≤ (Mf : Real) * ((Kg : Real) *
                dist x y ^ (alpha : Real)) := by
            gcongr
            · exact hfnorm y hy
            · have hgyx := hg.dist_le y x
              simpa only [dist_eq_norm, hgsupport x hx, sub_zero, dist_comm] using hgyx
          _ ≤ ((Mf * Kg + Mg * Kf : NNReal) : Real) *
                dist x y ^ (alpha : Real) := by
            push_cast
            have hpow : 0 ≤ dist x y ^ (alpha : Real) :=
              Real.rpow_nonneg (dist_nonneg) _
            calc
              (Mf : Real) * ((Kg : Real) * dist x y ^ (alpha : Real)) =
                  ((Mf : Real) * Kg) * dist x y ^ (alpha : Real) := by ring
              _ ≤ ((Mf : Real) * Kg + (Mg : Real) * Kf) *
                    dist x y ^ (alpha : Real) :=
                mul_le_mul_of_nonneg_right
                  (le_add_of_nonneg_right
                    (mul_nonneg Mg.coe_nonneg Kf.coe_nonneg)) hpow
      · rw [hgsupport x hx, hgsupport y hy]
        simp only [map_zero, dist_self]
        positivity
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

theorem holderWith_smul_of_restrict_of_support
    {s : Set X} {alpha Kf Kg Mf Mg : NNReal}
    {f : X → Real} {g : X → C}
    (hf : HolderWith Kf alpha (s.restrict f))
    (hg : HolderWith Kg alpha g)
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ Mf)
    (hgnorm : ∀ x, ‖g x‖ ≤ Mg)
    (hgsupport : ∀ x, x ∉ s → g x = 0) :
    HolderWith (Mf * Kg + Mg * Kf) alpha (f • g) := by
  have h := holderWith_bilinear_of_restrict_of_support
    (ContinuousLinearMap.lsmul Real Real : Real →L[Real] C →L[Real] C)
    (fun c v ↦ by rw [ContinuousLinearMap.lsmul_apply, norm_smul,
      Real.norm_eq_abs]) hf hg hfnorm hgnorm hgsupport
  simpa only [Pi.smul_apply, ContinuousLinearMap.lsmul_apply] using h

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
