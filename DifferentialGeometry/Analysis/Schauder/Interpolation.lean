import DifferentialGeometry.Analysis.Schauder.Holder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

open Set
open scoped BoundedContinuousFunction NNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem norm_first_order_taylor_remainder_le_on
    {f : E → F} {C alpha : NNReal} {s : Set E}
    (hs : Convex Real s) (hf : ∀ z ∈ s, DifferentiableAt Real f z)
    (hDf : HolderOnWith C alpha (fderiv Real f) s)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - fderiv Real f x (y - x)‖ ≤
      C * ‖y - x‖ ^ (1 + (alpha : Real)) := by
  by_cases hxy : y = x
  · subst y
    simp only [sub_self, map_zero, norm_zero]
    positivity
  have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hbound : ∀ z ∈ segment Real x y,
      ‖fderiv Real f z - fderiv Real f x‖ ≤
        C * ‖y - x‖ ^ (alpha : Real) := by
    intro z hz
    have hz' : z ∈ s := hs.segment_subset hx hy hz
    have hdist : dist z x ≤ ‖y - x‖ := by
      simpa only [dist_eq_norm] using norm_sub_le_of_mem_segment hz
    simpa only [dist_eq_norm] using hDf.dist_le_of_le hz' hx hdist
  have hmean := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (s := segment Real x y) (x := x) (y := y) (f := f)
    (C := (C : Real) * ‖y - x‖ ^ (alpha : Real))
    (φ := fderiv Real f x) (fun z hz => hf z (hs.segment_subset hx hy hz)) hbound
    (left_mem_segment Real x y) (right_mem_segment Real x y)
  calc
    ‖f y - f x - fderiv Real f x (y - x)‖ ≤
        ((C : Real) * ‖y - x‖ ^ (alpha : Real)) * ‖y - x‖ := hmean
    _ = C * ‖y - x‖ ^ (1 + (alpha : Real)) := by
      rw [add_comm, Real.rpow_add hnorm, Real.rpow_one]
      ring

theorem norm_first_order_taylor_remainder_le
    {f : E → F} {C alpha : NNReal}
    (hf : Differentiable Real f)
    (hDf : HolderWith C alpha (fderiv Real f)) (x y : E) :
    ‖f y - f x - fderiv Real f x (y - x)‖ ≤
      C * ‖y - x‖ ^ (1 + (alpha : Real)) :=
  norm_first_order_taylor_remainder_le_on convex_univ
    (fun z _ => hf z) (hDf.holderOnWith univ) (mem_univ x) (mem_univ y)

theorem norm_fderiv_le_at_scale
    {f : E → F} {M C alpha : NNReal}
    (hf : Differentiable Real f)
    (hDf : HolderWith C alpha (fderiv Real f))
    (hfnorm : ∀ z, ‖f z‖ ≤ M) {epsilon : Real} (hepsilon : 0 < epsilon) (x : E) :
    ‖fderiv Real f x‖ ≤
      2 * M / epsilon + C * epsilon ^ (alpha : Real) := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm
  · positivity
  intro v hv
  let y := x + epsilon • v
  have hstep : y - x = epsilon • v := by simp [y]
  have hstepnorm : ‖y - x‖ = epsilon := by
    rw [hstep, norm_smul, Real.norm_of_nonneg hepsilon.le, hv, mul_one]
  have htaylor := norm_first_order_taylor_remainder_le hf hDf x y
  have hfunction : ‖f y - f x‖ ≤ 2 * M := by
    calc
      ‖f y - f x‖ ≤ ‖f y‖ + ‖f x‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hfnorm y) (hfnorm x)
      _ = 2 * M := by ring
  have hderivstep : ‖fderiv Real f x (y - x)‖ ≤
      2 * M + C * epsilon ^ (1 + (alpha : Real)) := by
    calc
      ‖fderiv Real f x (y - x)‖ ≤
          ‖f y - f x‖ + ‖(f y - f x) - fderiv Real f x (y - x)‖ :=
        norm_le_norm_add_norm_sub (f y - f x) (fderiv Real f x (y - x))
      _ ≤ 2 * M + C * ‖y - x‖ ^ (1 + (alpha : Real)) :=
        add_le_add hfunction htaylor
      _ = 2 * M + C * epsilon ^ (1 + (alpha : Real)) := by rw [hstepnorm]
  have hleft : ‖fderiv Real f x (y - x)‖ =
      epsilon * ‖fderiv Real f x v‖ := by
    rw [hstep, map_smul, norm_smul, Real.norm_of_nonneg hepsilon.le]
  have hright : epsilon * (2 * M / epsilon + C * epsilon ^ (alpha : Real)) =
      2 * M + C * epsilon ^ (1 + (alpha : Real)) := by
    rw [mul_add, mul_div_cancel₀ _ hepsilon.ne']
    congr 1
    calc
      epsilon * (C * epsilon ^ (alpha : Real)) =
          C * (epsilon ^ (1 : Real) * epsilon ^ (alpha : Real)) := by
        rw [Real.rpow_one]
        ring
      _ = C * epsilon ^ (1 + (alpha : Real)) := by
        rw [Real.rpow_add hepsilon]
  have hmul : epsilon * ‖fderiv Real f x v‖ ≤
      epsilon * (2 * M / epsilon + C * epsilon ^ (alpha : Real)) := by
    rw [hright]
    simpa only [hleft] using hderivstep
  exact le_of_mul_le_mul_left hmul hepsilon

theorem norm_iteratedFDeriv_succ_le_at_scale
    {f : E → F} {k : Nat} {M C alpha : NNReal}
    (hf : ContDiff Real (k + 1) f)
    (hjet : HolderWith C alpha (iteratedFDeriv Real (k + 1) f))
    (hfnorm : ∀ z, ‖iteratedFDeriv Real k f z‖ ≤ M)
    {epsilon : Real} (hepsilon : 0 < epsilon) (x : E) :
    ‖iteratedFDeriv Real (k + 1) f x‖ ≤
      2 * M / epsilon + C * epsilon ^ (alpha : Real) := by
  let curryEquiv :=
    continuousMultilinearCurryLeftEquiv Real (fun _ : Fin (k + 1) => E) F
  have hderivHolder : HolderWith C alpha
      (fderiv Real (iteratedFDeriv Real k f)) := by
    rw [fderiv_iteratedFDeriv]
    simpa only [curryEquiv, one_mul, NNReal.rpow_one, NNReal.coe_one] using
      (curryEquiv.lipschitz.holderWith.comp hjet)
  have hbound := norm_fderiv_le_at_scale
    (hf.differentiable_iteratedFDeriv (mod_cast Nat.lt_succ_self k))
    hderivHolder hfnorm hepsilon x
  rwa [norm_fderiv_iteratedFDeriv] at hbound

def hessianInterpolationFunctionConst (epsilon M : NNReal) : NNReal :=
  32 * M / epsilon ^ 2

def hessianInterpolationConst
    (epsilon alpha M K : NNReal) : NNReal :=
  hessianInterpolationFunctionConst epsilon M +
    2 * K * epsilon ^ (alpha : Real)

theorem norm_hessian_le_hessianInterpolationConst
    (u : BoundedContinuousFunction E F)
    (du : BoundedContinuousFunction E (E →L[Real] F))
    (d2u : BoundedContinuousFunction E (E →L[Real] E →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : E → F) (du x) x)
    (hdu : ∀ x, HasFDerivAt (du : E → E →L[Real] F) (d2u x) x)
    {epsilon alpha K : NNReal} (hepsilon : 0 < epsilon)
    (hd2uHolder : HolderWith K alpha
      (d2u : E → E →L[Real] E →L[Real] F)) :
    ‖d2u‖ ≤ hessianInterpolationConst epsilon alpha ‖u‖₊ K := by
  have huDifferentiable : Differentiable Real (u : E → F) :=
    fun x ↦ (hu x).differentiableAt
  have hduDifferentiable : Differentiable Real
      (du : E → E →L[Real] F) :=
    fun x ↦ (hdu x).differentiableAt
  have hfderivU : fderiv Real (u : E → F) =
      (du : E → E →L[Real] F) := by
    funext x
    exact (hu x).fderiv
  have hfderivDu : fderiv Real (du : E → E →L[Real] F) =
      (d2u : E → E →L[Real] E →L[Real] F) := by
    funext x
    exact (hdu x).fderiv
  have hduLipschitz : LipschitzWith ‖d2u‖₊
      (du : E → E →L[Real] F) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (f := (du : E → E →L[Real] F))
      (fun x ↦ (hdu x).differentiableAt)
    intro x
    rw [hfderivDu]
    exact_mod_cast d2u.norm_coe_le_norm x
  have hduHolderOne : HolderWith ‖d2u‖₊ 1
      (fderiv Real (u : E → F)) := by
    rw [hfderivU]
    exact hduLipschitz.holderWith
  let G : NNReal := 8 * ‖u‖₊ / epsilon + ‖d2u‖₊ * epsilon / 4
  have hduNorm : ∀ x, ‖du x‖ ≤ G := by
    intro x
    have hraw := norm_fderiv_le_at_scale (M := ‖u‖₊)
      huDifferentiable hduHolderOne
      (fun z ↦ by simpa using u.norm_coe_le_norm z)
      (show 0 < (epsilon : Real) / 4 by positivity) x
    rw [hfderivU] at hraw
    calc
      ‖du x‖ ≤ 2 * (‖u‖₊ : Real) / ((epsilon : Real) / 4) +
          (‖d2u‖₊ : Real) * ((epsilon : Real) / 4) ^ (1 : Real) := hraw
      _ = G := by
        simp only [G, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul,
          NNReal.coe_ofNat, Real.rpow_one]
        field_simp [ne_of_gt hepsilon]
        ring
  have hrawPoint : ∀ x, ‖d2u x‖ ≤
      2 * (G : Real) / epsilon + K * (epsilon : Real) ^ (alpha : Real) := by
    intro x
    have hraw := norm_fderiv_le_at_scale (M := G) hduDifferentiable
      (by rw [hfderivDu]; exact hd2uHolder) hduNorm
      (show 0 < (epsilon : Real) by exact_mod_cast hepsilon) x
    rwa [hfderivDu] at hraw
  have hrawNorm : ‖d2u‖ ≤
      2 * (G : Real) / epsilon + K * (epsilon : Real) ^ (alpha : Real) := by
    rw [BoundedContinuousFunction.norm_le]
    · exact hrawPoint
    · positivity
  have hrewrite :
      2 * (G : Real) / epsilon + K * (epsilon : Real) ^ (alpha : Real) =
        16 * (‖u‖₊ : Real) / (epsilon : Real) ^ 2 +
          ‖d2u‖ / 2 + K * (epsilon : Real) ^ (alpha : Real) := by
    simp only [G, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul,
      NNReal.coe_ofNat, coe_nnnorm]
    field_simp [ne_of_gt hepsilon]
    ring
  rw [hrewrite] at hrawNorm
  let A : Real := 16 * (‖u‖₊ : Real) / (epsilon : Real) ^ 2
  let B : Real := (K : Real) * (epsilon : Real) ^ (alpha : Real)
  have hrawNorm' : ‖d2u‖ ≤ A + ‖d2u‖ / 2 + B := by
    simpa only [A, B] using hrawNorm
  have habsorb : ‖d2u‖ ≤ 2 * (A + B) := by
    linarith
  have htarget : ‖d2u‖ ≤
      32 * (‖u‖₊ : Real) / (epsilon : Real) ^ 2 +
        2 * K * (epsilon : Real) ^ (alpha : Real) := by
    calc
      ‖d2u‖ ≤ 2 * (A + B) := habsorb
      _ = 32 * (‖u‖₊ : Real) / (epsilon : Real) ^ 2 +
          2 * K * (epsilon : Real) ^ (alpha : Real) := by
        simp only [A, B]
        ring
  simpa only [hessianInterpolationConst, hessianInterpolationFunctionConst,
    NNReal.coe_add, NNReal.coe_div,
    NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_rpow] using htarget

end DifferentialGeometry.Analysis.Schauder
