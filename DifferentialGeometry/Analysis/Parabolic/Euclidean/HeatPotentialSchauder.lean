import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelSchauderHigher
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open MeasureTheory Real Set Filter
open scoped NNReal RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2_space_sub_eq_integral_heatD3 {t : Real} (ht : 0 < t)
    (h v w z : V) :
    heatD2 t v w (z - h) - heatD2 t v w z =
      ∫ s : Real in 0..1, -heatD3 t h v w (z + s • (-h)) := by
  let gamma : Real → V := fun s => z + s • (-h)
  have hgamma : ∀ s : Real, HasDerivAt gamma (-h) s := by
    intro s
    have hs : HasDerivAt (fun r : Real => r • (-h)) (-h) s := by
      simpa using (hasDerivAt_id s).smul_const (-h)
    simpa only [gamma] using hs.const_add z
  have hcomp : ∀ s : Real,
      HasDerivAt (fun r : Real => heatD2 t v w (gamma r))
        (-heatD3 t h v w (gamma s)) s := by
    intro s
    have h0 := (heatD2_hasFDeriv (t := t) ht v w (gamma s)).comp_hasDerivAt s (hgamma s)
    convert h0 using 1
    simp only [heatD3Map_apply]
    simp [heatD3, baseD3]
    ring
  have hderiv : IntervalIntegrable
      (fun s : Real => -heatD3 t h v w (gamma s)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold gamma heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hcomp s) hderiv
  have hgamma0 : gamma 0 = z := by simp [gamma]
  have hgamma1 : gamma 1 = z - h := by simp [gamma, sub_eq_add_neg]
  simpa only [hgamma1, hgamma0] using hftc.symm

section Convolution

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace Real F]

omit [Nontrivial V] in
theorem heatD2Conv_translate_kernel (t : Real) (h v w : V)
    (f : V → F) (x : V) :
    heatD2Conv t v w f (x - h) =
      ∫ z : V, heatD2 t v w (z - h) • f (x - z) := by
  let g : V → F := fun z => heatD2 t v w (z - h) • f (x - z)
  have htranslate := MeasureTheory.integral_add_right_eq_self
    (μ := volume) g h
  unfold heatD2Conv
  calc
    (∫ y : V, heatD2 t v w y • f (x - h - y)) =
        ∫ y : V, g (y + h) := by
      apply integral_congr_ae
      filter_upwards with y
      have hk : y + h - h = y := by abel
      have hfarg : x - h - y = x - (y + h) := by abel
      simp only [g, hk, hfarg]
    _ = ∫ z : V, g z := htranslate
    _ = ∫ z : V, heatD2 t v w (z - h) • f (x - z) := by rfl

variable [CompleteSpace F]

omit [CompleteSpace F] in
theorem heatD2Conv_space_sub_eq_integral_kernel_diff_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    heatD2Conv t v w f (x - h) - heatD2Conv t v w f x =
      ∫ z : V, (heatD2 t v w (z - h) - heatD2 t v w z) • f (x - z) := by
  have hzero := heatD2Conv_int_of_holder halpha0 halpha1 ht hf v w x
  have hone0 := heatD2Conv_int_of_holder halpha0 halpha1 ht hf v w (x - h)
  have hone : Integrable
      (fun z : V => heatD2 t v w (z - h) • f (x - z)) := by
    have htranslated := hone0.comp_add_right (-h)
    refine htranslated.congr (Filter.Eventually.of_forall fun z => ?_)
    have hk : z + -h = z - h := by abel
    have hfarg : x - h - (z - h) = x - z := by abel
    simp only [hk, hfarg]
  rw [heatD2Conv_translate_kernel]
  unfold heatD2Conv
  rw [← integral_sub hone hzero]
  apply integral_congr_ae
  filter_upwards with z
  rw [sub_smul]

omit [Nontrivial V] [CompleteSpace F] in
theorem integral_heatD3_path_eq_neg_heatD3Conv
    (t : Real) (h v w : V) (f : V → F) (x : V) (s : Real) :
    (∫ z : V, (-heatD3 t h v w (z + s • (-h))) • f (x - z)) =
      -heatD3Conv t h v w f (x - s • h) := by
  let g : V → F := fun z =>
    (-heatD3 t h v w (z + s • (-h))) • f (x - z)
  have htranslate := MeasureTheory.integral_add_right_eq_self
    (μ := volume) g (s • h)
  calc
    (∫ z : V, (-heatD3 t h v w (z + s • (-h))) • f (x - z)) =
        ∫ z : V, g z := by rfl
    _ = ∫ z : V, g (z + s • h) := htranslate.symm
    _ = ∫ z : V, -(heatD3 t h v w z • f (x - s • h - z)) := by
      apply integral_congr_ae
      filter_upwards with z
      have hk : z + s • h + s • (-h) = z := by
        rw [smul_neg]
        abel
      have hfarg : x - (z + s • h) = x - s • h - z := by abel
      simp only [g, hk, hfarg, neg_smul]
    _ = -heatD3Conv t h v w f (x - s • h) := by
      rw [integral_neg]
      rfl

omit [InnerProductSpace Real V] [FiniteDimensional Real V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedSpace Real F] [CompleteSpace F] in
private theorem holder_shift_bound_heatPotential {alpha K : NNReal}
    {f : V → F} (hf : HolderWith K alpha f) (x y : V) :
    ‖f (x - y) - f x‖ ≤ (K : Real) * ‖y‖ ^ (alpha : Real) := by
  have hxy : dist (x - y) x = ‖y‖ := by
    rw [dist_eq_norm]
    have : (x - y) - x = -y := by abel
    rw [this, norm_neg]
  have h := hf.dist_le (x - y) x
  rw [dist_eq_norm, hxy] at h
  exact h

omit [CompleteSpace F] in
private theorem heatD3_path_integrable_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    Integrable
      (fun z : Real × V ↦
        (-heatD3 t h v w (z.2 + z.1 • (-h))) • f (x - z.2))
      ((volume.restrict (Ioc 0 1)).prod volume) := by
  let μ : Measure Real := volume.restrict (Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • f (x - z.2)
  let A : Real := ‖h‖ * ‖v‖ * ‖w‖ * (K : Real)
  let B : Real → Real := fun s ↦
    ‖h‖ * ‖v‖ * ‖w‖ * ‖f (x - s • h)‖
  let C : Real → Real := fun s ↦
    A * (∫ y : V, heatD3Holder alpha t y) +
      B s * (∫ y : V, heatD3Maj t y)
  have hfcont : Continuous f := hf.continuous halpha0
  have hGmeas : AEStronglyMeasurable G (μ.prod (volume : Measure V)) := by
    apply Continuous.aestronglyMeasurable
    unfold G heatD3 baseD3 baseHeat baseHeatMass heatScale
    fun_prop
  have hslice_int : ∀ s : Real, Integrable (fun y : V ↦ G (s, y)) := by
    intro s
    have hs :=
      (heatD3Conv_int_of_holder halpha0 halpha1 ht hf h v w (x - s • h)).neg
        |>.comp_add_right (s • (-h))
    refine hs.congr (Eventually.of_forall fun y ↦ ?_)
    have hfarg : x - s • h - (y + s • (-h)) = x - y := by
      rw [smul_neg]
      abel
    simp only [G, hfarg, Pi.neg_apply, neg_smul]
  have hpoint : ∀ (s : Real) (y : V),
      ‖heatD3 t h v w y • f (x - s • h - y)‖ ≤
        A * heatD3Holder alpha t y + B s * heatD3Maj t y := by
    intro s y
    have hfvalue : ‖f (x - s • h - y)‖ ≤
        (K : Real) * ‖y‖ ^ (alpha : Real) + ‖f (x - s • h)‖ := by
      calc
        ‖f (x - s • h - y)‖ =
            ‖(f (x - s • h - y) - f (x - s • h)) +
              f (x - s • h)‖ := by rw [sub_add_cancel]
        _ ≤ ‖f (x - s • h - y) - f (x - s • h)‖ +
              ‖f (x - s • h)‖ := norm_add_le _ _
        _ ≤ (K : Real) * ‖y‖ ^ (alpha : Real) +
              ‖f (x - s • h)‖ := by
          gcongr
          exact holder_shift_bound_heatPotential hf (x - s • h) y
    rw [norm_smul]
    have hd3 := heatD3_bound ht h v w y
    have hd3holder := heatD3_holder_bound alpha ht h v w y
    calc
      ‖heatD3 t h v w y‖ * ‖f (x - s • h - y)‖ ≤
          ‖heatD3 t h v w y‖ *
            ((K : Real) * ‖y‖ ^ (alpha : Real) +
              ‖f (x - s • h)‖) := by
        gcongr
      _ = ((K : Real) *
            (‖heatD3 t h v w y‖ * ‖y‖ ^ (alpha : Real))) +
          ‖f (x - s • h)‖ * ‖heatD3 t h v w y‖ := by ring
      _ ≤ (K : Real) *
            (‖h‖ * ‖v‖ * ‖w‖ * heatD3Holder alpha t y) +
          ‖f (x - s • h)‖ *
            (‖h‖ * ‖v‖ * ‖w‖ * heatD3Maj t y) := by
        gcongr
      _ = A * heatD3Holder alpha t y + B s * heatD3Maj t y := by
        unfold A B
        ring
  have hslice_bound : ∀ s : Real,
      (∫ y : V, ‖G (s, y)‖) ≤ C s := by
    intro s
    let q : V → Real := fun y ↦
      ‖heatD3 t h v w y • f (x - s • h - y)‖
    have htranslate := MeasureTheory.integral_add_right_eq_self
      (μ := volume) q (s • (-h))
    have hleft_eq : (∫ y : V, ‖G (s, y)‖) = ∫ y : V, q y := by
      rw [← htranslate]
      apply integral_congr_ae
      filter_upwards with y
      have hfarg : x - s • h - (y + s • (-h)) = x - y := by
        rw [smul_neg]
        abel
      simp only [G, q, hfarg, norm_smul, Real.norm_eq_abs, abs_neg]
    have hmajor : Integrable (fun y : V ↦
        A * heatD3Holder alpha t y + B s * heatD3Maj t y) :=
      ((heatD3Holder_int (V := V) halpha1 ht).const_mul A).add
        ((heatD3Maj_int (V := V) ht).const_mul (B s))
    have hq : Integrable q := by
      have hs := heatD3Conv_int_of_holder halpha0 halpha1 ht hf h v w
        (x - s • h)
      exact hs.norm
    rw [hleft_eq]
    calc
      (∫ y : V, q y) ≤
          ∫ y : V, A * heatD3Holder alpha t y + B s * heatD3Maj t y := by
        exact integral_mono hq hmajor (fun y ↦ hpoint s y)
      _ = C s := by
        have hfirst := (heatD3Holder_int (V := V) halpha1 ht).const_mul A
        have hsecond := (heatD3Maj_int (V := V) ht).const_mul (B s)
        unfold C
        rw [integral_add hfirst hsecond,
          integral_const_mul, integral_const_mul]
  have hCcont : Continuous C := by
    have hcenter : Continuous (fun s : Real ↦ f (x - s • h)) := by
      exact hfcont.comp (by fun_prop)
    unfold C B A
    exact continuous_const.add
      ((continuous_const.mul hcenter.norm).mul continuous_const)
  have hCint : Integrable C μ := by
    have hi := hCcont.intervalIntegrable (μ := volume)
      (a := (0 : Real)) (b := 1)
    simpa only [μ, intervalIntegrable_iff,
      uIoc_of_le (by norm_num : (0 : Real) ≤ 1)] using hi
  have hCnonneg : ∀ s : Real, 0 ≤ C s := by
    intro s
    have hholder : 0 ≤ ∫ y : V, heatD3Holder alpha t y :=
      integral_nonneg (heatD3Holder_nonneg alpha ht)
    have hmaj : 0 ≤ ∫ y : V, heatD3Maj t y :=
      integral_nonneg (heatD3Maj_nonneg ht)
    unfold C A B
    exact add_nonneg
      (mul_nonneg (by positivity) hholder)
      (mul_nonneg (by positivity) hmaj)
  have houter : Integrable (fun s : Real ↦ ∫ y : V, ‖G (s, y)‖) μ := by
    refine hCint.mono hGmeas.norm.integral_prod_right' ?_
    filter_upwards with s
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun y ↦ norm_nonneg (G (s, y))),
      Real.norm_eq_abs, abs_of_nonneg (hCnonneg s)]
    exact hslice_bound s
  exact (integrable_prod_iff hGmeas).2
    ⟨Eventually.of_forall hslice_int, houter⟩

theorem heatD2Conv_space_sub_eq_integral_heatD3Conv_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    heatD2Conv t v w f (x - h) - heatD2Conv t v w f x =
      ∫ s : Real in 0..1, -heatD3Conv t h v w f (x - s • h) := by
  let μ : Measure Real := volume.restrict (Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • f (x - z.2)
  have hGint : Integrable G (μ.prod (volume : Measure V)) := by
    simpa only [G, μ] using
      heatD3_path_integrable_of_holder halpha0 halpha1 ht hf h v w x
  rw [heatD2Conv_space_sub_eq_integral_kernel_diff_of_holder
    halpha0 halpha1 ht hf]
  calc
    (∫ z : V, (heatD2 t v w (z - h) - heatD2 t v w z) • f (x - z)) =
        ∫ z : V, (∫ s : Real in 0..1,
          -heatD3 t h v w (z + s • (-h))) • f (x - z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [heatD2_space_sub_eq_integral_heatD3 ht]
    _ = ∫ z : V, ∫ s : Real in 0..1,
        (-heatD3 t h v w (z + s • (-h))) • f (x - z) := by
      apply integral_congr_ae
      filter_upwards with z
      exact (intervalIntegral.integral_smul_const
        (fun s : Real ↦ -heatD3 t h v w (z + s • (-h))) (f (x - z))).symm
    _ = ∫ z : V, (∫ s : Real, G (s, z) ∂μ) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [intervalIntegral.integral_of_le (by norm_num)]
    _ = ∫ s : Real, (∫ z : V, G (s, z)) ∂μ := by
      have huncurry : Integrable
          (Function.uncurry (fun s : Real ↦ fun z : V ↦ G (s, z)))
          (μ.prod (volume : Measure V)) := by
        simpa only [Function.uncurry_apply_pair] using hGint
      have hswap :
          (∫ s : Real, (∫ z : V, G (s, z)) ∂μ) =
            ∫ z : V, (∫ s : Real, G (s, z) ∂μ) :=
        integral_integral_swap huncurry
      exact hswap.symm
    _ = ∫ s : Real in 0..1, -heatD3Conv t h v w f (x - s • h) := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply integral_congr_ae
      filter_upwards with s
      simpa only [G] using integral_heatD3_path_eq_neg_heatD3Conv t h v w f x s

omit [CompleteSpace F] in
theorem heatD3Conv_path_intervalIntegrable_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    IntervalIntegrable
      (fun s : Real ↦ heatD3Conv t h v w f (x - s • h)) volume 0 1 := by
  let μ : Measure Real := volume.restrict (Ioc 0 1)
  let G : Real × V → F := fun z ↦
    (-heatD3 t h v w (z.2 + z.1 • (-h))) • f (x - z.2)
  have hGint : Integrable G (μ.prod (volume : Measure V)) := by
    simpa only [G, μ] using
      heatD3_path_integrable_of_holder halpha0 halpha1 ht hf h v w x
  have hneg : Integrable
      (fun s : Real ↦ -heatD3Conv t h v w f (x - s • h)) μ := by
    refine hGint.integral_prod_left.congr (Eventually.of_forall fun s ↦ ?_)
    simpa only [G] using integral_heatD3_path_eq_neg_heatD3Conv t h v w f x s
  have hconv : Integrable
      (fun s : Real ↦ heatD3Conv t h v w f (x - s • h)) μ := by
    refine hneg.neg.congr (Eventually.of_forall fun s ↦ ?_)
    simp
  simpa only [μ, intervalIntegrable_iff,
    uIoc_of_le (by norm_num : (0 : Real) ≤ 1)] using hconv

theorem heatD2Conv_space_sub_norm_le_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    ‖heatD2Conv t v w f (x - h) - heatD2Conv t v w f x‖ ≤
      ‖h‖ * ‖v‖ * ‖w‖ * (K : Real) * holderThirdHeatScale alpha t *
        heatC3Holder (V := V) alpha := by
  let M : Real :=
    ‖h‖ * ‖v‖ * ‖w‖ * (K : Real) * holderThirdHeatScale alpha t *
      heatC3Holder (V := V) alpha
  have hpath :=
    heatD3Conv_path_intervalIntegrable_of_holder halpha0 halpha1 ht hf h v w x
  have hconst : IntervalIntegrable (fun _ : Real ↦ M) volume 0 1 :=
    (continuous_const : Continuous (fun _ : Real ↦ M)).intervalIntegrable
      (μ := volume) 0 1
  rw [heatD2Conv_space_sub_eq_integral_heatD3Conv_of_holder
    halpha0 halpha1 ht hf]
  calc
    ‖∫ s : Real in 0..1, -heatD3Conv t h v w f (x - s • h)‖ ≤
        ∫ s : Real in 0..1, ‖-heatD3Conv t h v w f (x - s • h)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ _s : Real in 0..1, M := by
      refine intervalIntegral.integral_mono (by norm_num) hpath.neg.norm hconst ?_
      intro s
      dsimp only
      rw [norm_neg]
      simpa only [M] using
        heatD3Conv_norm_of_holder halpha0 halpha1 ht hf h v w (x - s • h)
    _ = M := by simp
    _ = ‖h‖ * ‖v‖ * ‖w‖ * (K : Real) * holderThirdHeatScale alpha t *
        heatC3Holder (V := V) alpha := by rfl

end Convolution

end DifferentialGeometry.Analysis.Parabolic.Euclidean
