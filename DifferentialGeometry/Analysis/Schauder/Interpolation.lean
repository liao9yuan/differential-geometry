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

section Parabolic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]

theorem lipschitzOnWith_time_slice_of_parabolicC2HolderGaugeOn
    {J : Set Real} (hJ : Convex Real J)
    {alpha C : NNReal} {u : Real → V → F}
    (hu : IsParabolicC2On (parabolicCylinder J Set.univ) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) u ≤ C)
    (x : V) :
    LipschitzOnWith C (fun t ↦ u t x) J := by
  apply hJ.lipschitzOnWith_of_nnnorm_deriv_le
  · intro t ht
    exact hu.2 (parabolicPoint t x) ⟨ht, Set.mem_univ x⟩
  · intro t ht
    rw [← NNReal.coe_le_coe]
    have htime := parabolicTimeDerivative_norm_le hgauge
      (p := parabolicPoint t x) ⟨ht, Set.mem_univ x⟩
    simpa only [parabolicTimeDerivative, deriv, parabolicPoint_time,
      parabolicPoint_space, coe_nnnorm] using htime

theorem lipschitzOnWith_parabolicValue_of_parabolicC2HolderGaugeOn
    {J : Set Real} (hJ : Convex Real J)
    {alpha C : NNReal} {u : Real → V → F}
    (hu : IsParabolicC2On (parabolicCylinder J Set.univ) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) u ≤ C) :
    LipschitzOnWith (2 * C)
      (fun p : ParabolicPoint V ↦ u p.time p.space)
      (parabolicCylinder J Set.univ) := by
  have hspace : ∀ t ∈ J, LipschitzWith C (u t) := by
    intro t ht
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := Real)
    · intro x
      exact (hu.1 (parabolicPoint t x) ⟨ht, Set.mem_univ x⟩).differentiableAt
        (by norm_num)
    · intro x
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm]
      rw [← norm_iteratedFDeriv_one]
      exact parabolicSpatialJet_norm_le hgauge (by omega)
        (p := parabolicPoint t x) ⟨ht, Set.mem_univ x⟩
  have hnorm : ∀ p ∈ parabolicCylinder J (Set.univ : Set V),
      ‖u p.time p.space‖ ≤ C := by
    intro p hp
    have hzero := parabolicSpatialJet_norm_le hgauge
      (j := 0) (by omega) (p := p) hp
    simpa only [parabolicSpatialJet, norm_iteratedFDeriv_zero] using hzero
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  have htime :=
    (lipschitzOnWith_time_slice_of_parabolicC2HolderGaugeOn
      hJ hu hgauge p.space).dist_le_mul p.time hp.1 q.time hq.1
  have hspace' := (hspace q.time hq.1).dist_le_mul p.space q.space
  rw [dist_eq_norm, Real.dist_eq] at htime
  rw [dist_eq_norm, dist_eq_norm] at hspace'
  rw [dist_eq_norm]
  by_cases hpq : dist p q ≤ 1
  · have hroot : Real.sqrt |p.time - q.time| ≤ dist p q := by
      rw [Real.sqrt_eq_rpow, ← parabolicPoint_time_space p,
        ← parabolicPoint_time_space q, dist_parabolicPoint]
      exact le_max_left _ _
    have htimeDist : |p.time - q.time| ≤ dist p q := by
      have hsquare : Real.sqrt |p.time - q.time| ^ 2 = |p.time - q.time| :=
        Real.sq_sqrt (abs_nonneg _)
      have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (dist_nonneg)).mpr hroot
      calc
        |p.time - q.time| = Real.sqrt |p.time - q.time| ^ 2 := hsquare.symm
        _ ≤ dist p q ^ 2 := hsq
        _ ≤ dist p q := by nlinarith [(dist_nonneg : 0 ≤ dist p q)]
    have hspaceDist : dist p.space q.space ≤ dist p q := by
      rw [← parabolicPoint_time_space p, ← parabolicPoint_time_space q,
        dist_parabolicPoint]
      exact le_max_right _ _
    calc
      ‖u p.time p.space - u q.time q.space‖ ≤
          ‖u p.time p.space - u q.time p.space‖ +
            ‖u q.time p.space - u q.time q.space‖ := by
        rw [show u p.time p.space - u q.time q.space =
            (u p.time p.space - u q.time p.space) +
              (u q.time p.space - u q.time q.space) by abel]
        exact norm_add_le _ _
      _ ≤ C * |p.time - q.time| + C * dist p.space q.space :=
        add_le_add htime (by simpa only [dist_eq_norm] using hspace')
      _ ≤ (2 * C : NNReal) * dist p q := by
        calc
          (C : Real) * |p.time - q.time| +
              (C : Real) * dist p.space q.space ≤
            (C : Real) * dist p q + (C : Real) * dist p q := by
              gcongr
          _ = ((2 * C : NNReal) : Real) * dist p q := by
            push_cast
            ring
  · have hpq' : 1 ≤ dist p q := le_of_not_ge hpq
    calc
      ‖u p.time p.space - u q.time q.space‖ ≤
          ‖u p.time p.space‖ + ‖u q.time q.space‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hnorm p hp) (hnorm q hq)
      _ ≤ (2 * C : NNReal) * dist p q := by
        calc
          (C : Real) + C = ((2 * C : NNReal) : Real) := by
            push_cast
            ring
          _ ≤ ((2 * C : NNReal) : Real) * dist p q := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hpq'
              (by positivity : 0 ≤ ((2 * C : NNReal) : Real))

theorem parabolicValue_holderWith_restrict
    {J : Set Real} (hJ : Convex Real J)
    {alpha C : NNReal} (halpha : alpha ≤ 1)
    {u : Real → V → F}
    (hu : IsParabolicC2On (parabolicCylinder J Set.univ) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) u ≤ C) :
    HolderWith (2 * C) alpha
      ((parabolicCylinder J Set.univ).restrict
        (fun p : ParabolicPoint V ↦ u p.time p.space)) := by
  have hnorm : ∀ p : parabolicCylinder J (Set.univ : Set V),
      ‖u p.1.time p.1.space‖ ≤ C := by
    intro p
    have hzero := parabolicSpatialJet_norm_le hgauge
      (j := 0) (by omega) (p := p.1) p.2
    simpa only [parabolicSpatialJet, norm_iteratedFDeriv_zero] using hzero
  have hzero : HolderWith (2 * C) 0
      ((parabolicCylinder J Set.univ).restrict
        (fun p : ParabolicPoint V ↦ u p.time p.space)) :=
    holderWith_zero_of_norm_le hnorm
  have hlip :=
    (lipschitzOnWith_parabolicValue_of_parabolicC2HolderGaugeOn
      hJ hu hgauge).holderOnWith.holderWith
  simpa only [max_self] using hzero.of_le_of_le hlip
    (by positivity) halpha

theorem lipschitzWith_time_slice_of_parabolicC2HolderGauge
    {alpha C : NNReal} {u : Real → V → F}
    (hu : IsParabolicC2On Set.univ u)
    (hgauge : eParabolicC2HolderGaugeOn alpha Set.univ u ≤ C)
    (x : V) :
    LipschitzWith C (fun t ↦ u t x) := by
  have hQ : parabolicCylinder Set.univ (Set.univ : Set V) = Set.univ := by
    ext p
    simp only [parabolicCylinder, Set.mem_setOf_eq, Set.mem_univ, and_self]
  rw [← hQ] at hu hgauge
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_time_slice_of_parabolicC2HolderGaugeOn
    convex_univ hu hgauge x

theorem lipschitzWith_parabolicValue
    {alpha C : NNReal} {u : Real → V → F}
    (hu : IsParabolicC2On Set.univ u)
    (hgauge : eParabolicC2HolderGaugeOn alpha Set.univ u ≤ C) :
    LipschitzWith (2 * C) (fun p : ParabolicPoint V ↦ u p.time p.space) := by
  have hspace : ∀ t, LipschitzWith C (u t) := by
    intro t
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := Real)
    · intro x
      exact (hu.1 (parabolicPoint t x) (Set.mem_univ _)).differentiableAt
        (by norm_num)
    · intro x
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm]
      rw [← norm_iteratedFDeriv_one]
      exact parabolicSpatialJet_norm_le hgauge (by omega)
        (p := parabolicPoint t x) (Set.mem_univ _)
  have hnorm : ∀ p : ParabolicPoint V, ‖u p.time p.space‖ ≤ C := by
    intro p
    have hzero := parabolicSpatialJet_norm_le hgauge
      (j := 0) (by omega) (p := p) (Set.mem_univ _)
    simpa only [parabolicSpatialJet, norm_iteratedFDeriv_zero] using hzero
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have htime := (lipschitzWith_time_slice_of_parabolicC2HolderGauge
    hu hgauge p.space).dist_le_mul p.time q.time
  have hspace' := (hspace q.time).dist_le_mul p.space q.space
  rw [dist_eq_norm, Real.dist_eq] at htime
  rw [dist_eq_norm, dist_eq_norm] at hspace'
  rw [dist_eq_norm]
  by_cases hpq : dist p q ≤ 1
  · have hroot : Real.sqrt |p.time - q.time| ≤ dist p q := by
      rw [Real.sqrt_eq_rpow, ← parabolicPoint_time_space p,
        ← parabolicPoint_time_space q, dist_parabolicPoint]
      exact le_max_left _ _
    have htimeDist : |p.time - q.time| ≤ dist p q := by
      have hsquare : Real.sqrt |p.time - q.time| ^ 2 = |p.time - q.time| :=
        Real.sq_sqrt (abs_nonneg _)
      have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (dist_nonneg)).mpr hroot
      calc
        |p.time - q.time| = Real.sqrt |p.time - q.time| ^ 2 := hsquare.symm
        _ ≤ dist p q ^ 2 := hsq
        _ ≤ dist p q := by nlinarith [(dist_nonneg : 0 ≤ dist p q)]
    have hspaceDist : dist p.space q.space ≤ dist p q := by
      rw [← parabolicPoint_time_space p, ← parabolicPoint_time_space q,
        dist_parabolicPoint]
      exact le_max_right _ _
    calc
      ‖u p.time p.space - u q.time q.space‖ ≤
          ‖u p.time p.space - u q.time p.space‖ +
            ‖u q.time p.space - u q.time q.space‖ := by
        rw [show u p.time p.space - u q.time q.space =
            (u p.time p.space - u q.time p.space) +
              (u q.time p.space - u q.time q.space) by abel]
        exact norm_add_le _ _
      _ ≤ C * |p.time - q.time| + C * dist p.space q.space :=
        add_le_add htime (by simpa only [dist_eq_norm] using hspace')
      _ ≤ (2 * C : NNReal) * dist p q := by
        calc
          (C : Real) * |p.time - q.time| +
              (C : Real) * dist p.space q.space ≤
            (C : Real) * dist p q + (C : Real) * dist p q := by
              gcongr
          _ = ((2 * C : NNReal) : Real) * dist p q := by
            push_cast
            ring
  · have hpq' : 1 ≤ dist p q := le_of_not_ge hpq
    calc
      ‖u p.time p.space - u q.time q.space‖ ≤
          ‖u p.time p.space‖ + ‖u q.time q.space‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hnorm p) (hnorm q)
      _ ≤ (2 * C : NNReal) * dist p q := by
        calc
          (C : Real) + C = ((2 * C : NNReal) : Real) := by
            push_cast
            ring
          _ ≤ ((2 * C : NNReal) : Real) * dist p q := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hpq'
              (by positivity : 0 ≤ ((2 * C : NNReal) : Real))

theorem parabolicValue_holderWith
    {alpha C : NNReal} (halpha : alpha ≤ 1)
    {u : Real → V → F}
    (hu : IsParabolicC2On Set.univ u)
    (hgauge : eParabolicC2HolderGaugeOn alpha Set.univ u ≤ C) :
    HolderWith (2 * C) alpha
      (fun p : ParabolicPoint V ↦ u p.time p.space) := by
  have hnorm : ∀ p : ParabolicPoint V, ‖u p.time p.space‖ ≤ C := by
    intro p
    have hzero := parabolicSpatialJet_norm_le hgauge
      (j := 0) (by omega) (p := p) (Set.mem_univ _)
    simpa only [parabolicSpatialJet, norm_iteratedFDeriv_zero] using hzero
  have hzero : HolderWith (2 * C) 0
      (fun p : ParabolicPoint V ↦ u p.time p.space) :=
    holderWith_zero_of_norm_le hnorm
  simpa only [max_self] using hzero.of_le_of_le
    (lipschitzWith_parabolicValue hu hgauge).holderWith
    (by positivity) halpha

theorem norm_parabolicSpatialJet_one_time_sub_le_of_mem
    {J : Set Real} (hJ : Convex Real J)
    {alpha C : NNReal} {u : Real → V → F}
    (hu : IsParabolicC2On (parabolicCylinder J Set.univ) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) u ≤ C)
    (t : Real) (ht : t ∈ J) (s : Real) (hs : s ∈ J) (x : V) :
    ‖parabolicSpatialJet 1 u (parabolicPoint t x) -
        parabolicSpatialJet 1 u (parabolicPoint s x)‖ ≤
      4 * C * Real.sqrt |t - s| := by
  by_cases hts : t = s
  · subst s
    simp
  let f : V → F := fun y ↦ u t y - u s y
  have hut : ContDiff Real 2 (u t) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact hu.1 (parabolicPoint t y) ⟨ht, Set.mem_univ y⟩
  have hus : ContDiff Real 2 (u s) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact hu.1 (parabolicPoint s y) ⟨hs, Set.mem_univ y⟩
  have hf : ContDiff Real 2 f := hut.sub hus
  have hfdiff : Differentiable Real (fderiv Real f) := by
    exact (((contDiff_succ_iff_fderiv (n := 1)).mp hf).2.2).differentiable
      (by norm_num)
  have hsecond : ∀ y, ‖fderiv Real (fderiv Real f) y‖ ≤ 2 * C := by
    intro y
    rw [← hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv,
      LinearIsometryEquiv.norm_map]
    change ‖iteratedFDeriv Real 2 (u t - u s) y‖ ≤ (2 * C : NNReal)
    rw [iteratedFDeriv_sub_apply (x := y) hut.contDiffAt hus.contDiffAt]
    calc
      ‖iteratedFDeriv Real 2 (u t) y - iteratedFDeriv Real 2 (u s) y‖ ≤
          ‖iteratedFDeriv Real 2 (u t) y‖ +
            ‖iteratedFDeriv Real 2 (u s) y‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add
        (parabolicSpatialJet_norm_le hgauge (j := 2) (by omega)
          (p := parabolicPoint t y) ⟨ht, Set.mem_univ y⟩)
        (parabolicSpatialJet_norm_le hgauge (j := 2) (by omega)
          (p := parabolicPoint s y) ⟨hs, Set.mem_univ y⟩)
      _ = 2 * C := by ring
  have hholder : HolderWith (2 * C) 1 (fderiv Real f) := by
    apply LipschitzWith.holderWith
    apply lipschitzWith_of_nnnorm_fderiv_le hfdiff
    intro y
    rw [← NNReal.coe_le_coe]
    simpa only [coe_nnnorm] using hsecond y
  let delta : NNReal := Real.toNNReal |t - s|
  have hfnorm : ∀ y, ‖f y‖ ≤ C * delta := by
    intro y
    have htime :=
      (lipschitzOnWith_time_slice_of_parabolicC2HolderGaugeOn
        hJ hu hgauge y).dist_le_mul t ht s hs
    simpa only [f, dist_eq_norm, Real.dist_eq, delta, NNReal.coe_mul,
      Real.coe_toNNReal _ (abs_nonneg _)] using htime
  have hdelta : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr hts)
  have hsqrt : 0 < Real.sqrt |t - s| := Real.sqrt_pos.2 hdelta
  have hraw := norm_fderiv_le_at_scale
    (M := C * delta) (C := 2 * C) (alpha := 1)
    (hf.differentiable (by norm_num)) hholder hfnorm hsqrt x
  simp only [NNReal.coe_one, Real.rpow_one] at hraw
  have hrewrite :
      2 * ((C * delta : NNReal) : Real) / Real.sqrt |t - s| +
          ((2 * C : NNReal) : Real) * Real.sqrt |t - s| =
        ((4 * C : NNReal) : Real) * Real.sqrt |t - s| := by
    have hsqrtSq : Real.sqrt |t - s| ^ 2 = |t - s| :=
      Real.sq_sqrt (abs_nonneg _)
    have hdeltaCoe : (delta : Real) = Real.sqrt |t - s| ^ 2 := by
      simp only [delta, Real.coe_toNNReal _ (abs_nonneg _)]
      exact hsqrtSq.symm
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    rw [hdeltaCoe]
    field_simp [hsqrt.ne']
    ring_nf
  have hfderiv : fderiv Real f x =
      fderiv Real (u t) x - fderiv Real (u s) x := by
    change fderiv Real (u t - u s) x = _
    rw [fderiv_sub (hut.differentiable (by norm_num)).differentiableAt
      (hus.differentiable (by norm_num)).differentiableAt]
  have hjet : ‖parabolicSpatialJet 1 u (parabolicPoint t x) -
      parabolicSpatialJet 1 u (parabolicPoint s x)‖ =
      ‖fderiv Real (u t) x - fderiv Real (u s) x‖ := by
    let e := continuousMultilinearCurryFin1 Real V F
    have ht' : e (parabolicSpatialJet 1 u (parabolicPoint t x)) =
        fderiv Real (u t) x := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, e, continuousMultilinearCurryFin1_apply,
        iteratedFDeriv_one_apply, Fin.snoc_zero]
    have hs' : e (parabolicSpatialJet 1 u (parabolicPoint s x)) =
        fderiv Real (u s) x := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, e, continuousMultilinearCurryFin1_apply,
        iteratedFDeriv_one_apply, Fin.snoc_zero]
    rw [← LinearIsometryEquiv.norm_map e, map_sub, ht', hs']
  rw [hrewrite, hfderiv] at hraw
  rw [hjet]
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hraw

theorem norm_parabolicSpatialJet_one_time_sub_le
    {alpha C : NNReal} {u : Real → V → F}
    (hu : IsParabolicC2On Set.univ u)
    (hgauge : eParabolicC2HolderGaugeOn alpha Set.univ u ≤ C)
    (t s : Real) (x : V) :
    ‖parabolicSpatialJet 1 u (parabolicPoint t x) -
        parabolicSpatialJet 1 u (parabolicPoint s x)‖ ≤
      4 * C * Real.sqrt |t - s| := by
  by_cases hts : t = s
  · subst s
    simp
  let f : V → F := fun y ↦ u t y - u s y
  have hut : ContDiff Real 2 (u t) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact hu.1 (parabolicPoint t y) (Set.mem_univ _)
  have hus : ContDiff Real 2 (u s) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact hu.1 (parabolicPoint s y) (Set.mem_univ _)
  have hf : ContDiff Real 2 f := hut.sub hus
  have hfdiff : Differentiable Real (fderiv Real f) := by
    exact (((contDiff_succ_iff_fderiv (n := 1)).mp hf).2.2).differentiable
      (by norm_num)
  have hsecond : ∀ y, ‖fderiv Real (fderiv Real f) y‖ ≤ 2 * C := by
    intro y
    rw [← hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv,
      LinearIsometryEquiv.norm_map]
    change ‖iteratedFDeriv Real 2 (u t - u s) y‖ ≤ (2 * C : NNReal)
    rw [iteratedFDeriv_sub_apply (x := y) hut.contDiffAt hus.contDiffAt]
    calc
      ‖iteratedFDeriv Real 2 (u t) y - iteratedFDeriv Real 2 (u s) y‖ ≤
          ‖iteratedFDeriv Real 2 (u t) y‖ +
            ‖iteratedFDeriv Real 2 (u s) y‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add
        (parabolicSpatialJet_norm_le hgauge (j := 2) (by omega)
          (p := parabolicPoint t y) (Set.mem_univ _))
        (parabolicSpatialJet_norm_le hgauge (j := 2) (by omega)
          (p := parabolicPoint s y) (Set.mem_univ _))
      _ = 2 * C := by ring
  have hholder : HolderWith (2 * C) 1 (fderiv Real f) := by
    apply LipschitzWith.holderWith
    apply lipschitzWith_of_nnnorm_fderiv_le hfdiff
    intro y
    rw [← NNReal.coe_le_coe]
    simpa only [coe_nnnorm] using hsecond y
  let delta : NNReal := Real.toNNReal |t - s|
  have hfnorm : ∀ y, ‖f y‖ ≤ C * delta := by
    intro y
    have htime := (lipschitzWith_time_slice_of_parabolicC2HolderGauge
      hu hgauge y).dist_le_mul t s
    simpa only [f, dist_eq_norm, Real.dist_eq, delta, NNReal.coe_mul,
      Real.coe_toNNReal _ (abs_nonneg _)] using htime
  have hdelta : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr hts)
  have hsqrt : 0 < Real.sqrt |t - s| := Real.sqrt_pos.2 hdelta
  have hraw := norm_fderiv_le_at_scale
    (M := C * delta) (C := 2 * C) (alpha := 1)
    (hf.differentiable (by norm_num)) hholder hfnorm hsqrt x
  simp only [NNReal.coe_one, Real.rpow_one] at hraw
  have hrewrite :
      2 * ((C * delta : NNReal) : Real) / Real.sqrt |t - s| +
          ((2 * C : NNReal) : Real) * Real.sqrt |t - s| =
        ((4 * C : NNReal) : Real) * Real.sqrt |t - s| := by
    have hsqrtSq : Real.sqrt |t - s| ^ 2 = |t - s| :=
      Real.sq_sqrt (abs_nonneg _)
    have hdeltaCoe : (delta : Real) = Real.sqrt |t - s| ^ 2 := by
      simp only [delta, Real.coe_toNNReal _ (abs_nonneg _)]
      exact hsqrtSq.symm
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    rw [hdeltaCoe]
    field_simp [hsqrt.ne']
    ring_nf
  have hfderiv : fderiv Real f x =
      fderiv Real (u t) x - fderiv Real (u s) x := by
    change fderiv Real (u t - u s) x = _
    rw [fderiv_sub (hut.differentiable (by norm_num)).differentiableAt
      (hus.differentiable (by norm_num)).differentiableAt]
  have hjet : ‖parabolicSpatialJet 1 u (parabolicPoint t x) -
      parabolicSpatialJet 1 u (parabolicPoint s x)‖ =
      ‖fderiv Real (u t) x - fderiv Real (u s) x‖ := by
    let e := continuousMultilinearCurryFin1 Real V F
    have ht : e (parabolicSpatialJet 1 u (parabolicPoint t x)) =
        fderiv Real (u t) x := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, e, continuousMultilinearCurryFin1_apply,
        iteratedFDeriv_one_apply, Fin.snoc_zero]
    have hs : e (parabolicSpatialJet 1 u (parabolicPoint s x)) =
        fderiv Real (u s) x := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, e, continuousMultilinearCurryFin1_apply,
        iteratedFDeriv_one_apply, Fin.snoc_zero]
    rw [← LinearIsometryEquiv.norm_map e, map_sub, ht, hs]
  rw [hrewrite, hfderiv] at hraw
  rw [hjet]
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hraw

theorem lipschitzOnWith_parabolicSpatialJet_one_of_parabolicC2HolderGaugeOn
    {J : Set Real} (hJ : Convex Real J)
    {alpha C : NNReal} {u : Real → V → F}
    (hu : IsParabolicC2On (parabolicCylinder J Set.univ) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) u ≤ C) :
    LipschitzOnWith (5 * C) (parabolicSpatialJet 1 u)
      (parabolicCylinder J Set.univ) := by
  have hspace : ∀ t ∈ J, LipschitzWith C (fderiv Real (u t)) := by
    intro t ht
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := Real)
    · have hut : ContDiff Real 2 (u t) := by
        rw [contDiff_iff_contDiffAt]
        intro y
        exact hu.1 (parabolicPoint t y) ⟨ht, Set.mem_univ y⟩
      exact (((contDiff_succ_iff_fderiv (n := 1)).mp hut).2.2).differentiable
        (by norm_num)
    · intro y
      change ‖fderiv Real (fderiv Real (u t)) y‖ ≤ (C : Real)
      rw [← hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv,
        LinearIsometryEquiv.norm_map]
      have hbound := parabolicSpatialJet_norm_le hgauge
        (j := 2) (by omega) (p := parabolicPoint t y)
          ⟨ht, Set.mem_univ y⟩
      simpa only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, coe_nnnorm] using hbound
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  have htime := norm_parabolicSpatialJet_one_time_sub_le_of_mem
    hJ hu hgauge p.time hp.1 q.time hq.1 p.space
  have hspace' := (hspace q.time hq.1).dist_le_mul p.space q.space
  rw [dist_eq_norm, dist_eq_norm] at hspace'
  have hspaceJet :
      ‖parabolicSpatialJet 1 u (parabolicPoint q.time p.space) -
          parabolicSpatialJet 1 u (parabolicPoint q.time q.space)‖ =
        ‖fderiv Real (u q.time) p.space -
          fderiv Real (u q.time) q.space‖ := by
    let e := continuousMultilinearCurryFin1 Real V F
    have hp' : e (parabolicSpatialJet 1 u
        (parabolicPoint q.time p.space)) =
        fderiv Real (u q.time) p.space := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, e, continuousMultilinearCurryFin1_apply,
        iteratedFDeriv_one_apply, Fin.snoc_zero]
    have hq' : e (parabolicSpatialJet 1 u
        (parabolicPoint q.time q.space)) =
        fderiv Real (u q.time) q.space := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, e, continuousMultilinearCurryFin1_apply,
        iteratedFDeriv_one_apply, Fin.snoc_zero]
    rw [← LinearIsometryEquiv.norm_map e, map_sub, hp', hq']
  have hspaceTarget :
      ‖parabolicSpatialJet 1 u (parabolicPoint q.time p.space) -
          parabolicSpatialJet 1 u (parabolicPoint q.time q.space)‖ ≤
        C * dist p.space q.space := by
    rw [hspaceJet]
    simpa only [dist_eq_norm] using hspace'
  rw [parabolicPoint_time_space q] at hspaceTarget
  rw [dist_eq_norm]
  calc
    ‖parabolicSpatialJet 1 u p - parabolicSpatialJet 1 u q‖ ≤
        ‖parabolicSpatialJet 1 u p -
            parabolicSpatialJet 1 u (parabolicPoint q.time p.space)‖ +
          ‖parabolicSpatialJet 1 u (parabolicPoint q.time p.space) -
            parabolicSpatialJet 1 u q‖ := by
      rw [show parabolicSpatialJet 1 u p - parabolicSpatialJet 1 u q =
          (parabolicSpatialJet 1 u p -
            parabolicSpatialJet 1 u (parabolicPoint q.time p.space)) +
          (parabolicSpatialJet 1 u (parabolicPoint q.time p.space) -
            parabolicSpatialJet 1 u q) by abel]
      exact norm_add_le _ _
    _ ≤ 4 * C * Real.sqrt |p.time - q.time| +
          C * dist p.space q.space := add_le_add (by
            simpa only [parabolicPoint_time_space] using htime) hspaceTarget
    _ ≤ (5 * C : NNReal) * dist p q := by
      rw [← parabolicPoint_time_space p, ← parabolicPoint_time_space q,
        dist_parabolicPoint, Real.sqrt_eq_rpow]
      have htimeMax : |p.time - q.time| ^ (1 / 2 : Real) ≤
          max (|p.time - q.time| ^ (1 / 2 : Real))
            (dist p.space q.space) := le_max_left _ _
      have hspaceMax : dist p.space q.space ≤
          max (|p.time - q.time| ^ (1 / 2 : Real))
            (dist p.space q.space) := le_max_right _ _
      calc
        4 * (C : Real) * |p.time - q.time| ^ (1 / 2 : Real) +
            (C : Real) * dist p.space q.space ≤
          4 * (C : Real) *
              max (|p.time - q.time| ^ (1 / 2 : Real))
                (dist p.space q.space) +
            (C : Real) *
              max (|p.time - q.time| ^ (1 / 2 : Real))
                (dist p.space q.space) := by
          gcongr
        _ = ((5 * C : NNReal) : Real) *
              max (|p.time - q.time| ^ (1 / 2 : Real))
                (dist p.space q.space) := by
          push_cast
          ring

theorem parabolicSpatialJet_one_holderWith_restrict
    {J : Set Real} (hJ : Convex Real J)
    {alpha C : NNReal} (halpha : alpha ≤ 1)
    {u : Real → V → F}
    (hu : IsParabolicC2On (parabolicCylinder J Set.univ) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) u ≤ C) :
    HolderWith (5 * C) alpha
      ((parabolicCylinder J Set.univ).restrict
        (parabolicSpatialJet 1 u)) := by
  have hnorm : ∀ p : parabolicCylinder J (Set.univ : Set V),
      ‖parabolicSpatialJet 1 u p.1‖ ≤ C := by
    intro p
    exact parabolicSpatialJet_norm_le hgauge (by omega) p.2
  have hzero : HolderWith (2 * C) 0
      ((parabolicCylinder J Set.univ).restrict
        (parabolicSpatialJet 1 u)) :=
    holderWith_zero_of_norm_le hnorm
  have hlip :=
    (lipschitzOnWith_parabolicSpatialJet_one_of_parabolicC2HolderGaugeOn
      hJ hu hgauge).holderOnWith.holderWith
  have hconst : max (2 * C) (5 * C) = 5 * C := by
    apply max_eq_right
    gcongr
    norm_num
  simpa only [hconst] using hzero.of_le_of_le hlip
    (by positivity) halpha

theorem eParabolicC2HolderGaugeWithLowerJetsOn_cylinder_le
    {J : Set Real} (hJ : Convex Real J)
    {alpha C : NNReal} (halpha : alpha ≤ 1)
    {u : Real → V → F}
    (hu : IsParabolicC2On (parabolicCylinder J Set.univ) u)
    (hgauge : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder J Set.univ) u ≤ C) :
    eParabolicC2HolderGaugeWithLowerJetsOn alpha
        (parabolicCylinder J Set.univ) u ≤
      ((8 * C : NNReal) : ENNReal) := by
  calc
    eParabolicC2HolderGaugeWithLowerJetsOn alpha
        (parabolicCylinder J Set.univ) u ≤
      (C + 2 * C + 5 * C : NNReal) :=
        eParabolicC2HolderGaugeWithLowerJetsOn_le
          C (2 * C) (5 * C) hgauge
            (parabolicValue_holderWith_restrict hJ halpha hu hgauge)
            (parabolicSpatialJet_one_holderWith_restrict
              hJ halpha hu hgauge)
    _ = ((8 * C : NNReal) : ENNReal) := by
      push_cast
      ring

theorem lipschitzWith_parabolicSpatialJet_one
    {alpha C : NNReal} {u : Real → V → F}
    (hu : IsParabolicC2On Set.univ u)
    (hgauge : eParabolicC2HolderGaugeOn alpha Set.univ u ≤ C) :
    LipschitzWith (5 * C) (parabolicSpatialJet 1 u) := by
  have hspace : ∀ t, LipschitzWith C (fderiv Real (u t)) := by
    intro t
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := Real)
    · have hut : ContDiff Real 2 (u t) := by
        rw [contDiff_iff_contDiffAt]
        intro y
        exact hu.1 (parabolicPoint t y) (Set.mem_univ _)
      exact (((contDiff_succ_iff_fderiv (n := 1)).mp hut).2.2).differentiable
        (by norm_num)
    · intro y
      change ‖fderiv Real (fderiv Real (u t)) y‖ ≤ (C : Real)
      rw [← hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv,
        LinearIsometryEquiv.norm_map]
      have hbound := parabolicSpatialJet_norm_le hgauge
        (j := 2) (by omega) (p := parabolicPoint t y) (Set.mem_univ _)
      simpa only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, coe_nnnorm] using hbound
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have htime := norm_parabolicSpatialJet_one_time_sub_le hu hgauge
    p.time q.time p.space
  have hspace' := (hspace q.time).dist_le_mul p.space q.space
  rw [dist_eq_norm, dist_eq_norm] at hspace'
  have hspaceJet :
      ‖parabolicSpatialJet 1 u (parabolicPoint q.time p.space) -
          parabolicSpatialJet 1 u (parabolicPoint q.time q.space)‖ =
        ‖fderiv Real (u q.time) p.space -
          fderiv Real (u q.time) q.space‖ := by
    let e := continuousMultilinearCurryFin1 Real V F
    have hp : e (parabolicSpatialJet 1 u
        (parabolicPoint q.time p.space)) =
        fderiv Real (u q.time) p.space := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, e, continuousMultilinearCurryFin1_apply,
        iteratedFDeriv_one_apply, Fin.snoc_zero]
    have hq : e (parabolicSpatialJet 1 u
        (parabolicPoint q.time q.space)) =
        fderiv Real (u q.time) q.space := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, e, continuousMultilinearCurryFin1_apply,
        iteratedFDeriv_one_apply, Fin.snoc_zero]
    rw [← LinearIsometryEquiv.norm_map e, map_sub, hp, hq]
  have hspaceTarget :
      ‖parabolicSpatialJet 1 u (parabolicPoint q.time p.space) -
          parabolicSpatialJet 1 u (parabolicPoint q.time q.space)‖ ≤
        C * dist p.space q.space := by
    rw [hspaceJet]
    simpa only [dist_eq_norm] using hspace'
  rw [parabolicPoint_time_space q] at hspaceTarget
  rw [dist_eq_norm]
  calc
    ‖parabolicSpatialJet 1 u p - parabolicSpatialJet 1 u q‖ ≤
        ‖parabolicSpatialJet 1 u p -
            parabolicSpatialJet 1 u (parabolicPoint q.time p.space)‖ +
          ‖parabolicSpatialJet 1 u (parabolicPoint q.time p.space) -
            parabolicSpatialJet 1 u q‖ := by
      rw [show parabolicSpatialJet 1 u p - parabolicSpatialJet 1 u q =
          (parabolicSpatialJet 1 u p -
            parabolicSpatialJet 1 u (parabolicPoint q.time p.space)) +
          (parabolicSpatialJet 1 u (parabolicPoint q.time p.space) -
            parabolicSpatialJet 1 u q) by abel]
      exact norm_add_le _ _
    _ ≤ 4 * C * Real.sqrt |p.time - q.time| +
          C * dist p.space q.space := add_le_add (by
            simpa only [parabolicPoint_time_space] using htime) (by
            exact hspaceTarget)
    _ ≤ (5 * C : NNReal) * dist p q := by
      rw [← parabolicPoint_time_space p, ← parabolicPoint_time_space q,
        dist_parabolicPoint, Real.sqrt_eq_rpow]
      have htimeMax : |p.time - q.time| ^ (1 / 2 : Real) ≤
          max (|p.time - q.time| ^ (1 / 2 : Real))
            (dist p.space q.space) := le_max_left _ _
      have hspaceMax : dist p.space q.space ≤
          max (|p.time - q.time| ^ (1 / 2 : Real))
            (dist p.space q.space) := le_max_right _ _
      calc
        4 * (C : Real) * |p.time - q.time| ^ (1 / 2 : Real) +
            (C : Real) * dist p.space q.space ≤
          4 * (C : Real) *
              max (|p.time - q.time| ^ (1 / 2 : Real))
                (dist p.space q.space) +
            (C : Real) *
              max (|p.time - q.time| ^ (1 / 2 : Real))
                (dist p.space q.space) := by
          gcongr
        _ = ((5 * C : NNReal) : Real) *
              max (|p.time - q.time| ^ (1 / 2 : Real))
                (dist p.space q.space) := by
          push_cast
          ring

theorem parabolicSpatialJet_one_holderWith
    {alpha C : NNReal} (halpha : alpha ≤ 1)
    {u : Real → V → F}
    (hu : IsParabolicC2On Set.univ u)
    (hgauge : eParabolicC2HolderGaugeOn alpha Set.univ u ≤ C) :
    HolderWith (5 * C) alpha (parabolicSpatialJet 1 u) := by
  have hnorm : ∀ p, ‖parabolicSpatialJet 1 u p‖ ≤ C := by
    intro p
    exact parabolicSpatialJet_norm_le hgauge (by omega) (Set.mem_univ _)
  have hzero : HolderWith (2 * C) 0 (parabolicSpatialJet 1 u) :=
    holderWith_zero_of_norm_le hnorm
  have hlip := lipschitzWith_parabolicSpatialJet_one hu hgauge
  have hconst : max (2 * C) (5 * C) = 5 * C := by
    apply max_eq_right
    gcongr
    norm_num
  simpa only [hconst] using hzero.of_le_of_le hlip.holderWith
    (by positivity) halpha

theorem eParabolicC2HolderGaugeWithLowerJetsOn_univ_le
    {alpha C : NNReal} (halpha : alpha ≤ 1)
    {u : Real → V → F}
    (hu : IsParabolicC2On Set.univ u)
    (hgauge : eParabolicC2HolderGaugeOn alpha Set.univ u ≤ C) :
    eParabolicC2HolderGaugeWithLowerJetsOn alpha Set.univ u ≤
      ((8 * C : NNReal) : ENNReal) := by
  have hvalue : HolderWith (2 * C) alpha
      (Set.univ.restrict (fun p : ParabolicPoint V ↦ u p.time p.space)) :=
    (parabolicValue_holderWith halpha hu hgauge).holderOnWith Set.univ
      |>.holderWith
  have hgradient : HolderWith (5 * C) alpha
      (Set.univ.restrict (parabolicSpatialJet 1 u)) :=
    (parabolicSpatialJet_one_holderWith halpha hu hgauge).holderOnWith Set.univ
      |>.holderWith
  calc
    eParabolicC2HolderGaugeWithLowerJetsOn alpha Set.univ u ≤
        (C + 2 * C + 5 * C : NNReal) :=
      eParabolicC2HolderGaugeWithLowerJetsOn_le
        C (2 * C) (5 * C) hgauge hvalue hgradient
    _ = ((8 * C : NNReal) : ENNReal) := by
      push_cast
      ring

end Parabolic

end DifferentialGeometry.Analysis.Schauder
