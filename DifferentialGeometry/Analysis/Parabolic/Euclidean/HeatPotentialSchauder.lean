import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelSchauderTime
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

theorem heatD2Conv_space_sub_norm_le_recent_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) {f : V → F} (hf : HolderWith K alpha f)
    (h v w x : V) :
    ‖heatD2Conv t v w f (x - h) - heatD2Conv t v w f x‖ ≤
      2 * (‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha) := by
  calc
    ‖heatD2Conv t v w f (x - h) - heatD2Conv t v w f x‖ ≤
        ‖heatD2Conv t v w f (x - h)‖ +
          ‖heatD2Conv t v w f x‖ := norm_sub_le _ _
    _ ≤ (‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
          heatC2Holder (V := V) alpha) +
        (‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
          heatC2Holder (V := V) alpha) := by
      exact add_le_add
        (by
          rw [heatD2Conv_eq_cancel_of_holder halpha0 halpha1 ht hf]
          exact heatD2Cancel_norm_of_holder halpha1 ht hf v w (x - h))
        (by
          rw [heatD2Conv_eq_cancel_of_holder halpha0 halpha1 ht hf]
          exact heatD2Cancel_norm_of_holder halpha1 ht hf v w x)
    _ = 2 * (‖v‖ * ‖w‖ * (K : Real) * holderHeatScale alpha t *
        heatC2Holder (V := V) alpha) := by ring

omit [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private theorem holderHeatScale_intervalIntegrable {alpha : NNReal}
    (halpha0 : 0 < alpha) (a b : Real) :
    IntervalIntegrable (holderHeatScale alpha) volume a b := by
  unfold holderHeatScale
  apply intervalIntegral.intervalIntegrable_rpow'
  have ha : 0 < (alpha : Real) := by exact_mod_cast halpha0
  linarith

omit [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private theorem holderHeatScale_terminal_interval_int {alpha : NNReal}
    (halpha0 : 0 < alpha) {a b : Real} (hab : a < b) :
    ∫ s : Real in a..b, holderHeatScale alpha (b - s) =
      (2 / (alpha : Real)) * (b - a) ^ ((alpha : Real) / 2) := by
  rw [intervalIntegral.integral_comp_sub_left]
  have h := timeHolderHeatScale_int halpha0 (sub_pos.mpr hab)
  rw [intervalIntegral.integral_comp_sub_left] at h
  simpa only [sub_self, sub_zero] using h

omit [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private theorem holderHeatScale_add_le {alpha : NNReal}
    (halpha1 : alpha ≤ 1) {u d : Real} (hu : 0 < u) (hd : 0 ≤ d) :
    holderHeatScale alpha (u + d) ≤ holderHeatScale alpha u := by
  unfold holderHeatScale
  apply Real.rpow_le_rpow_of_nonpos hu (le_add_of_nonneg_right hd)
  have halpha_real : (alpha : Real) ≤ 1 := by exact_mod_cast halpha1
  linarith

omit [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F] in
private theorem holderThirdHeatScale_intervalIntegrable_of_pos
    {alpha : NNReal} {a b : Real} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (holderThirdHeatScale alpha) volume a b := by
  unfold holderThirdHeatScale
  apply ContinuousOn.intervalIntegrable
  intro y hy
  apply (Real.continuousAt_rpow_const y ((alpha : Real) / 2 - 3 / 2)
    (Or.inl ?_)).continuousWithinAt
  rw [uIcc_of_le hab] at hy
  exact (ha.trans_le hy.1).ne'

def d2DuhSpaceHolderConst (alpha : NNReal) (v w : V) (K : NNReal) : Real :=
  ‖v‖ * ‖w‖ * (K : Real) *
    ((4 / (alpha : Real)) * heatC2Holder (V := V) alpha +
      (2 / (1 - (alpha : Real))) * heatC3Holder (V := V) alpha)

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem d2DuhSpaceHolderConst_nonneg {alpha : NNReal} (halpha : alpha ≤ 1)
    (v w : V) (K : NNReal) :
    0 ≤ d2DuhSpaceHolderConst alpha v w K := by
  have halpha_real : (alpha : Real) ≤ 1 := by exact_mod_cast halpha
  unfold d2DuhSpaceHolderConst
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
    (add_nonneg
      (mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
        (heatC2Holder_nonneg (V := V) alpha))
      (mul_nonneg (div_nonneg (by norm_num) (sub_nonneg.mpr halpha_real))
        (heatC3Holder_nonneg (V := V) alpha)))

theorem heatD2Duh_space_sub_eq_integral {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t : Real} (ht : 0 < t) (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (h v w x : V)
    (hmeas0 : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (t - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (t - s) v w (f s) (x - h))
      (volume.restrict (uIoc (0 : Real) t))) :
    heatD2Duh t v w f (x - h) - heatD2Duh t v w f x =
      ∫ s : Real in 0..t,
        heatD2Conv (t - s) v w (f s) (x - h) -
          heatD2Conv (t - s) v w (f s) x := by
  have h0 := heatD2Duh_int_of_holder halpha0 halpha1 ht f hf v w x hmeas0
  have h1 :=
    heatD2Duh_int_of_holder halpha0 halpha1 ht f hf v w (x - h) hmeas1
  unfold heatD2Duh
  exact (intervalIntegral.integral_sub h1 h0).symm

theorem heatD2Duh_space_sub_norm_le_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {t : Real} (ht : 0 < t) (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (h v w x : V)
    (hmeas0 : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (t - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeas1 : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (t - s) v w (f s) (x - h))
      (volume.restrict (uIoc (0 : Real) t))) :
    ‖heatD2Duh t v w f (x - h) - heatD2Duh t v w f x‖ ≤
      d2DuhSpaceHolderConst alpha v w K * ‖h‖ ^ (alpha : Real) := by
  have halpha_le : alpha ≤ 1 := halpha1.le
  have h0 := heatD2Duh_int_of_holder halpha0 halpha_le ht f hf v w x hmeas0
  have h1 :=
    heatD2Duh_int_of_holder halpha0 halpha_le ht f hf v w (x - h) hmeas1
  let q : Real → F := fun s ↦
    heatD2Conv (t - s) v w (f s) (x - h) -
      heatD2Conv (t - s) v w (f s) x
  have hq : IntervalIntegrable q volume 0 t := h1.sub h0
  rw [heatD2Duh_space_sub_eq_integral halpha0 halpha_le ht f hf h v w x
    hmeas0 hmeas1]
  change ‖∫ s : Real in 0..t, q s‖ ≤ _
  by_cases hh0 : ‖h‖ = 0
  · have hh : h = 0 := norm_eq_zero.mp hh0
    subst h
    have halpha_ne : (alpha : Real) ≠ 0 := by exact_mod_cast halpha0.ne'
    have hpow0 : (0 : Real) ^ (alpha : Real) = 0 :=
      Real.zero_rpow halpha_ne
    simp [q, hpow0]
  have hr : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg h) (Ne.symm hh0)
  let A2 : Real := 2 * (‖v‖ * ‖w‖ * (K : Real) *
    heatC2Holder (V := V) alpha)
  let A3 : Real := ‖v‖ * ‖w‖ * (K : Real) *
    heatC3Holder (V := V) alpha
  have hA2 : 0 ≤ A2 := by
    unfold A2
    exact mul_nonneg (by norm_num) <|
      mul_nonneg
        (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
        (heatC2Holder_nonneg (V := V) alpha)
  have hA3 : 0 ≤ A3 := by
    unfold A3
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
      (heatC3Holder_nonneg (V := V) alpha)
  by_cases hsplit : ‖h‖ ^ 2 ≤ t
  · let c : Real := t - ‖h‖ ^ 2
    have hc0 : 0 ≤ c := sub_nonneg.mpr hsplit
    have hct : c ≤ t := sub_le_self t (sq_nonneg ‖h‖)
    have hqe : IntervalIntegrable q volume 0 c := by
      apply hq.mono_set
      rw [uIcc_of_le hc0, uIcc_of_le ht.le]
      exact Icc_subset_Icc le_rfl hct
    have hqr : IntervalIntegrable q volume c t := by
      apply hq.mono_set
      rw [uIcc_of_le hct, uIcc_of_le ht.le]
      exact Icc_subset_Icc hc0 le_rfl
    have hscale2 : IntervalIntegrable
        (fun s : Real ↦ holderHeatScale alpha (t - s)) volume c t := by
      have hs :=
        (holderHeatScale_intervalIntegrable halpha0 0 (‖h‖ ^ 2)).comp_sub_left t
      simpa only [c, sub_zero, sub_sub_cancel] using hs.symm
    have hscale3 : IntervalIntegrable
        (fun s : Real ↦ holderThirdHeatScale alpha (t - s)) volume 0 c := by
      have hs :=
        (holderThirdHeatScale_intervalIntegrable_of_pos
          (sq_pos_of_pos hr) hsplit).comp_sub_left t
      simpa only [c, sub_self, sub_sub_cancel] using hs.symm
    have hearly :
        ‖∫ s : Real in 0..c, q s‖ ≤
          ∫ s : Real in 0..c,
            (‖h‖ * A3) * holderThirdHeatScale alpha (t - s) := by
      calc
        ‖∫ s : Real in 0..c, q s‖ ≤
            ∫ s : Real in 0..c, ‖q s‖ :=
          intervalIntegral.norm_integral_le_integral_norm hc0
        _ ≤ ∫ s : Real in 0..c,
            (‖h‖ * A3) * holderThirdHeatScale alpha (t - s) := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo hc0 hqe.norm
            (hscale3.const_mul (‖h‖ * A3))
          intro s hs
          have hst : 0 < t - s := sub_pos.mpr (hs.2.trans_le hct)
          have hfs : HolderWith K alpha (f s) :=
            hf s ⟨hs.1.le, (hs.2.trans_le hct).le⟩
          change ‖heatD2Conv (t - s) v w (f s) (x - h) -
              heatD2Conv (t - s) v w (f s) x‖ ≤ _
          refine (heatD2Conv_space_sub_norm_le_of_holder
            halpha0 halpha_le hst hfs h v w x).trans_eq ?_
          unfold A3
          ring
    have hrecent :
        ‖∫ s : Real in c..t, q s‖ ≤
          ∫ s : Real in c..t, A2 * holderHeatScale alpha (t - s) := by
      calc
        ‖∫ s : Real in c..t, q s‖ ≤
            ∫ s : Real in c..t, ‖q s‖ :=
          intervalIntegral.norm_integral_le_integral_norm hct
        _ ≤ ∫ s : Real in c..t, A2 * holderHeatScale alpha (t - s) := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo hct hqr.norm
            (hscale2.const_mul A2)
          intro s hs
          have hst : 0 < t - s := sub_pos.mpr hs.2
          have hfs : HolderWith K alpha (f s) :=
            hf s ⟨hc0.trans_lt hs.1 |>.le, hs.2.le⟩
          change ‖heatD2Conv (t - s) v w (f s) (x - h) -
              heatD2Conv (t - s) v w (f s) x‖ ≤ _
          refine (heatD2Conv_space_sub_norm_le_recent_of_holder
            halpha0 halpha_le hst hfs h v w x).trans_eq ?_
          unfold A2
          ring
    have hearly_scale :
        (∫ s : Real in 0..c,
          (‖h‖ * A3) * holderThirdHeatScale alpha (t - s)) ≤
        A3 * ((2 / (1 - (alpha : Real))) * ‖h‖ ^ (alpha : Real)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left]
      simp only [c, sub_zero, sub_sub_cancel]
      have hm := mul_holderThirdHeatScale_integral_le halpha1 hr hsplit
      calc
        (‖h‖ * A3) *
            ∫ y : Real in ‖h‖ ^ 2..t, holderThirdHeatScale alpha y =
            A3 * (‖h‖ *
              ∫ y : Real in ‖h‖ ^ 2..t, holderThirdHeatScale alpha y) := by ring
        _ ≤ A3 * ((2 / (1 - (alpha : Real))) *
            ‖h‖ ^ (alpha : Real)) := mul_le_mul_of_nonneg_left hm hA3
    have hrecent_scale :
        (∫ s : Real in c..t, A2 * holderHeatScale alpha (t - s)) =
        A2 * ((2 / (alpha : Real)) * ‖h‖ ^ (alpha : Real)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left]
      simp only [c, sub_self, sub_sub_cancel]
      rw [holderHeatScale_integral_sq halpha0 hr.le]
    have hadd := intervalIntegral.integral_add_adjacent_intervals hqe hqr
    calc
      ‖∫ s : Real in 0..t, q s‖ =
          ‖(∫ s : Real in 0..c, q s) + ∫ s : Real in c..t, q s‖ := by
        rw [hadd]
      _ ≤ ‖∫ s : Real in 0..c, q s‖ +
          ‖∫ s : Real in c..t, q s‖ := norm_add_le _ _
      _ ≤ (∫ s : Real in 0..c,
            (‖h‖ * A3) * holderThirdHeatScale alpha (t - s)) +
          ∫ s : Real in c..t, A2 * holderHeatScale alpha (t - s) :=
        add_le_add hearly hrecent
      _ ≤ A3 * ((2 / (1 - (alpha : Real))) * ‖h‖ ^ (alpha : Real)) +
          A2 * ((2 / (alpha : Real)) * ‖h‖ ^ (alpha : Real)) := by
        rw [hrecent_scale]
        gcongr
      _ = d2DuhSpaceHolderConst alpha v w K * ‖h‖ ^ (alpha : Real) := by
        unfold A2 A3 d2DuhSpaceHolderConst
        ring
  · have htr : t ≤ ‖h‖ ^ 2 := le_of_lt (lt_of_not_ge hsplit)
    have hscale : IntervalIntegrable
        (fun s : Real ↦ holderHeatScale alpha (t - s)) volume 0 t :=
      holderHeatScale_intble halpha0 ht
    have hfull :
        ‖∫ s : Real in 0..t, q s‖ ≤
          ∫ s : Real in 0..t, A2 * holderHeatScale alpha (t - s) := by
      calc
        ‖∫ s : Real in 0..t, q s‖ ≤
            ∫ s : Real in 0..t, ‖q s‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht.le
        _ ≤ ∫ s : Real in 0..t, A2 * holderHeatScale alpha (t - s) := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo ht.le hq.norm
            (hscale.const_mul A2)
          intro s hs
          have hst : 0 < t - s := sub_pos.mpr hs.2
          have hfs : HolderWith K alpha (f s) := hf s ⟨hs.1.le, hs.2.le⟩
          change ‖heatD2Conv (t - s) v w (f s) (x - h) -
              heatD2Conv (t - s) v w (f s) x‖ ≤ _
          refine (heatD2Conv_space_sub_norm_le_recent_of_holder
            halpha0 halpha_le hst hfs h v w x).trans_eq ?_
          unfold A2
          ring
    have hpow : t ^ ((alpha : Real) / 2) ≤ ‖h‖ ^ (alpha : Real) := by
      have hmono := Real.rpow_le_rpow ht.le htr
        (by positivity : 0 ≤ (alpha : Real) / 2)
      calc
        t ^ ((alpha : Real) / 2) ≤ (‖h‖ ^ 2) ^ ((alpha : Real) / 2) := hmono
        _ = ‖h‖ ^ (alpha : Real) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul hr.le]
          congr 1
          ring
    calc
      ‖∫ s : Real in 0..t, q s‖ ≤
          ∫ s : Real in 0..t, A2 * holderHeatScale alpha (t - s) := hfull
      _ = A2 * ((2 / (alpha : Real)) * t ^ ((alpha : Real) / 2)) := by
        rw [intervalIntegral.integral_const_mul,
          timeHolderHeatScale_int halpha0 ht]
      _ ≤ A2 * ((2 / (alpha : Real)) * ‖h‖ ^ (alpha : Real)) := by
        gcongr
      _ ≤ d2DuhSpaceHolderConst alpha v w K * ‖h‖ ^ (alpha : Real) := by
        unfold A2 d2DuhSpaceHolderConst
        have hlate : 0 ≤ (2 / (1 - (alpha : Real))) *
            heatC3Holder (V := V) alpha := by
          exact mul_nonneg
            (div_nonneg (by norm_num)
              (sub_nonneg.mpr (by exact_mod_cast halpha1.le)))
            (heatC3Holder_nonneg (V := V) alpha)
        calc
          2 * (‖v‖ * ‖w‖ * (K : Real) * heatC2Holder alpha) *
              (2 / (alpha : Real) * ‖h‖ ^ (alpha : Real)) =
              (‖v‖ * ‖w‖ * (K : Real)) *
                ((4 / (alpha : Real)) * heatC2Holder alpha) *
                  ‖h‖ ^ (alpha : Real) := by ring
          _ ≤ (‖v‖ * ‖w‖ * (K : Real)) *
                ((4 / (alpha : Real)) * heatC2Holder alpha +
                  (2 / (1 - (alpha : Real))) * heatC3Holder alpha) *
                ‖h‖ ^ (alpha : Real) := by
            gcongr
            exact le_add_of_nonneg_right hlate

theorem heatD2Duh_norm_sub_le_of_holder {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    {t : Real} (ht : 0 < t) (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) t, HolderWith K alpha (f s))
    (v w x y : V)
    (hmeasx : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (t - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) t)))
    (hmeasy : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (t - s) v w (f s) y)
      (volume.restrict (uIoc (0 : Real) t))) :
    ‖heatD2Duh t v w f y - heatD2Duh t v w f x‖ ≤
      d2DuhSpaceHolderConst alpha v w K * ‖y - x‖ ^ (alpha : Real) := by
  have h := heatD2Duh_space_sub_norm_le_of_holder
    halpha0 halpha1 ht f hf (x - y) v w x hmeasx (by
      simpa only [sub_sub_cancel] using hmeasy)
  simpa only [sub_sub_cancel, norm_sub_rev] using h

theorem heatD2Conv_time_add_sub_eq_cancel_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t d : Real} (ht : 0 < t) (hd : 0 ≤ d)
    {f : V → F} (hf : HolderWith K alpha f) (v w x : V) :
    heatD2Conv (t + d) v w f x - heatD2Conv t v w f x =
      ∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) •
        (f (x - y) - f x) := by
  have htplus : 0 < t + d := ht.trans_le (le_add_of_nonneg_right hd)
  have hrawplus := heatD2Conv_int_of_holder halpha0 halpha1 htplus hf v w x
  have hrawnow := heatD2Conv_int_of_holder halpha0 halpha1 ht hf v w x
  have hker := (heatD2_int htplus v w).sub (heatD2_int ht v w)
  have hconst := hker.smul_const (f x)
  have hrawdiff := hrawplus.sub hrawnow
  have hcancel : Integrable (fun y : V ↦
      (heatD2 (t + d) v w y - heatD2 t v w y) •
        (f (x - y) - f x)) := by
    refine (hrawdiff.sub hconst).congr (Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.sub_apply, sub_smul, smul_sub]
  unfold heatD2Conv
  rw [← integral_sub hrawplus hrawnow]
  calc
    (∫ y : V, heatD2 (t + d) v w y • f (x - y) -
        heatD2 t v w y • f (x - y)) =
        ∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) •
          (f (x - y) - f x) +
            (heatD2 (t + d) v w y - heatD2 t v w y) • f x := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [sub_smul, smul_sub]
      module
    _ = (∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) •
          (f (x - y) - f x)) +
        ∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) • f x :=
      integral_add hcancel hconst
    _ = ∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) •
        (f (x - y) - f x) := by
      rw [integral_smul_const, integral_sub (heatD2_int htplus v w)
        (heatD2_int ht v w), integral_heatD2_zero htplus,
        integral_heatD2_zero ht, sub_zero, zero_smul, add_zero]

theorem heatD2Conv_time_add_sub_norm_le_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {t d : Real} (ht : 0 < t) (hd : 0 ≤ d)
    {f : V → F} (hf : HolderWith K alpha f) (v w x : V) :
    ‖heatD2Conv (t + d) v w f x - heatD2Conv t v w f x‖ ≤
      d * ‖v‖ * ‖w‖ * (K : Real) * holderSecondTimeHeatScale alpha t *
        heatC2DtHolder (V := V) alpha := by
  rw [heatD2Conv_time_add_sub_eq_cancel_of_holder
    halpha0 halpha1 ht hd hf]
  have hmajor :=
    (heatD2_time_add_diff_holder_int halpha1 ht hd v w).const_mul (K : Real)
  calc
    ‖∫ y : V, (heatD2 (t + d) v w y - heatD2 t v w y) •
        (f (x - y) - f x)‖ ≤
      ∫ y : V, (K : Real) *
        (‖heatD2 (t + d) v w y - heatD2 t v w y‖ *
          ‖y‖ ^ (alpha : Real)) := by
      apply norm_integral_le_of_norm_le hmajor
      filter_upwards with y
      rw [norm_smul, Real.norm_eq_abs]
      have hshift := holder_shift_bound_heatPotential hf x y
      rw [← Real.norm_eq_abs]
      calc
        ‖heatD2 (t + d) v w y - heatD2 t v w y‖ *
            ‖f (x - y) - f x‖ ≤
          ‖heatD2 (t + d) v w y - heatD2 t v w y‖ *
            ((K : Real) * ‖y‖ ^ (alpha : Real)) := by gcongr
        _ = (K : Real) *
            (‖heatD2 (t + d) v w y - heatD2 t v w y‖ *
              ‖y‖ ^ (alpha : Real)) := by ring
    _ ≤ (K : Real) *
        (d * ‖v‖ * ‖w‖ * holderSecondTimeHeatScale alpha t *
          heatC2DtHolder (V := V) alpha) := by
      rw [integral_const_mul]
      gcongr
      exact heatD2_time_add_diff_holder halpha1 ht hd v w
    _ = d * ‖v‖ * ‖w‖ * (K : Real) * holderSecondTimeHeatScale alpha t *
        heatC2DtHolder (V := V) alpha := by ring

def d2DuhTimeHolderConst (alpha : NNReal) (v w : V) (K : NNReal) : Real :=
  ‖v‖ * ‖w‖ * (K : Real) *
    ((6 / (alpha : Real)) * heatC2Holder (V := V) alpha +
      (2 / (2 - (alpha : Real))) * heatC2DtHolder (V := V) alpha)

omit [Nontrivial V] [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F] in
theorem d2DuhTimeHolderConst_nonneg {alpha : NNReal} (halpha : alpha ≤ 1)
    (v w : V) (K : NNReal) :
    0 ≤ d2DuhTimeHolderConst alpha v w K := by
  have halpha_real : (alpha : Real) ≤ 1 := by exact_mod_cast halpha
  have hfirst : 0 ≤ (6 / (alpha : Real)) * heatC2Holder (V := V) alpha :=
    mul_nonneg (div_nonneg (by norm_num) alpha.coe_nonneg)
      (heatC2Holder_nonneg (V := V) alpha)
  have hsecond : 0 ≤ (2 / (2 - (alpha : Real))) *
      heatC2DtHolder (V := V) alpha :=
    mul_nonneg (div_nonneg (by norm_num) (by linarith))
      (heatC2DtHolder_nonneg (V := V) alpha)
  unfold d2DuhTimeHolderConst
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
    (add_nonneg hfirst hsecond)

theorem heatD2Duh_time_add_sub_eq {alpha K : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (htau : 0 < tau) (hd : 0 ≤ d)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hmeasplus : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (tau + d - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) (tau + d))))
    (hmeasnow : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (tau - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) tau))) :
    heatD2Duh (tau + d) v w f x - heatD2Duh tau v w f x =
      (∫ s : Real in 0..tau,
        heatD2Conv ((tau - s) + d) v w (f s) x -
          heatD2Conv (tau - s) v w (f s) x) +
      ∫ s : Real in tau..tau + d,
        heatD2Conv (tau + d - s) v w (f s) x := by
  have htplus : 0 < tau + d := htau.trans_le (le_add_of_nonneg_right hd)
  have hplus := heatD2Duh_int_of_holder halpha0 halpha1 htplus f hf v w x hmeasplus
  have hfnow : ∀ s ∈ Icc (0 : Real) tau, HolderWith K alpha (f s) := by
    intro s hs
    exact hf s ⟨hs.1, hs.2.trans (le_add_of_nonneg_right hd)⟩
  have hnow := heatD2Duh_int_of_holder halpha0 halpha1 htau f hfnow v w x hmeasnow
  have hplusOld : IntervalIntegrable
      (fun s : Real ↦ heatD2Conv (tau + d - s) v w (f s) x)
      volume 0 tau := by
    apply hplus.mono_set
    rw [uIcc_of_le htau.le, uIcc_of_le htplus.le]
    exact Icc_subset_Icc le_rfl (le_add_of_nonneg_right hd)
  have hplusNew : IntervalIntegrable
      (fun s : Real ↦ heatD2Conv (tau + d - s) v w (f s) x)
      volume tau (tau + d) := by
    apply hplus.mono_set
    rw [uIcc_of_le (le_add_of_nonneg_right hd), uIcc_of_le htplus.le]
    exact Icc_subset_Icc htau.le le_rfl
  have hadd := intervalIntegral.integral_add_adjacent_intervals hplusOld hplusNew
  have holdsub := intervalIntegral.integral_sub hplusOld hnow
  unfold heatD2Duh
  calc
    (∫ s : Real in 0..tau + d, heatD2Conv (tau + d - s) v w (f s) x) -
        ∫ s : Real in 0..tau, heatD2Conv (tau - s) v w (f s) x =
      ((∫ s : Real in 0..tau, heatD2Conv (tau + d - s) v w (f s) x) +
        ∫ s : Real in tau..tau + d,
          heatD2Conv (tau + d - s) v w (f s) x) -
        ∫ s : Real in 0..tau, heatD2Conv (tau - s) v w (f s) x := by
      rw [hadd]
    _ = (∫ s : Real in 0..tau,
        heatD2Conv (tau + d - s) v w (f s) x -
          heatD2Conv (tau - s) v w (f s) x) +
        ∫ s : Real in tau..tau + d,
          heatD2Conv (tau + d - s) v w (f s) x := by
      rw [holdsub]
      abel
    _ = (∫ s : Real in 0..tau,
        heatD2Conv ((tau - s) + d) v w (f s) x -
          heatD2Conv (tau - s) v w (f s) x) +
        ∫ s : Real in tau..tau + d,
          heatD2Conv (tau + d - s) v w (f s) x := by
      congr 2
      funext s
      congr 3
      ring

private theorem heatD2Duh_time_add_sub_norm_le_large
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (htau : 0 < tau) (htd : tau ≤ d)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hmeasplus : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (tau + d - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) (tau + d))))
    (hmeasnow : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (tau - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) tau))) :
    ‖heatD2Duh (tau + d) v w f x - heatD2Duh tau v w f x‖ ≤
      d2DuhTimeHolderConst alpha v w K * d ^ ((alpha : Real) / 2) := by
  have hd : 0 < d := htau.trans_le htd
  have htplus : 0 < tau + d := htau.trans (lt_add_of_pos_right tau hd)
  have hfnow : ∀ s ∈ Icc (0 : Real) tau, HolderWith K alpha (f s) := by
    intro s hs
    exact hf s ⟨hs.1, hs.2.trans (le_add_of_nonneg_right hd.le)⟩
  have hplus := heatD2Duh_norm_of_holder
    halpha0 halpha1 htplus f hf v w x hmeasplus
  have hnow := heatD2Duh_norm_of_holder
    halpha0 halpha1 htau f hfnow v w x hmeasnow
  let p : Real := (alpha : Real) / 2
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hp1 : p ≤ 1 := by
    have halpha_real : (alpha : Real) ≤ 1 := by exact_mod_cast halpha1
    dsimp [p]
    linarith
  have htauPow : tau ^ p ≤ d ^ p :=
    Real.rpow_le_rpow htau.le htd hp0
  have htplusPow : (tau + d) ^ p ≤ 2 * d ^ p := by
    calc
      (tau + d) ^ p ≤ (2 * d) ^ p := by
        apply Real.rpow_le_rpow htplus.le
        · linarith
        · exact hp0
      _ = 2 ^ p * d ^ p := Real.mul_rpow (by norm_num) hd.le
      _ ≤ 2 * d ^ p := by
        gcongr
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) hp1
  have hduh : 0 ≤ d2DuhHolderConst alpha v w K := by
    unfold d2DuhHolderConst
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
      (heatC2Holder_nonneg (V := V) alpha)
  calc
    ‖heatD2Duh (tau + d) v w f x - heatD2Duh tau v w f x‖ ≤
        ‖heatD2Duh (tau + d) v w f x‖ + ‖heatD2Duh tau v w f x‖ :=
      norm_sub_le _ _
    _ ≤ d2DuhHolderConst alpha v w K *
          ((2 / (alpha : Real)) * (tau + d) ^ p) +
        d2DuhHolderConst alpha v w K *
          ((2 / (alpha : Real)) * tau ^ p) := add_le_add hplus hnow
    _ ≤ d2DuhHolderConst alpha v w K *
          ((2 / (alpha : Real)) * (2 * d ^ p)) +
        d2DuhHolderConst alpha v w K *
          ((2 / (alpha : Real)) * d ^ p) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htplusPow (by positivity)) hduh)
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htauPow (by positivity)) hduh)
    _ ≤ d2DuhTimeHolderConst alpha v w K * d ^ p := by
      unfold d2DuhHolderConst d2DuhTimeHolderConst
      have hlate : 0 ≤ (2 / (2 - (alpha : Real))) *
          heatC2DtHolder (V := V) alpha := by
        have halpha_real : (alpha : Real) ≤ 1 := by exact_mod_cast halpha1
        exact mul_nonneg (div_nonneg (by norm_num) (by linarith))
          (heatC2DtHolder_nonneg (V := V) alpha)
      have hbase : 0 ≤ ‖v‖ * ‖w‖ * (K : Real) := by positivity
      have hpow : 0 ≤ d ^ p := Real.rpow_nonneg hd.le p
      calc
        (‖v‖ * ‖w‖ * (K : Real) * heatC2Holder alpha) *
              (2 / (alpha : Real) * (2 * d ^ p)) +
            (‖v‖ * ‖w‖ * (K : Real) * heatC2Holder alpha) *
              (2 / (alpha : Real) * d ^ p) =
            (‖v‖ * ‖w‖ * (K : Real)) *
              ((6 / (alpha : Real)) * heatC2Holder alpha) * d ^ p := by ring
        _ ≤ (‖v‖ * ‖w‖ * (K : Real)) *
              ((6 / (alpha : Real)) * heatC2Holder alpha +
                (2 / (2 - (alpha : Real))) * heatC2DtHolder alpha) *
              d ^ p := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hlate) hbase) hpow

private theorem heatD2Duh_time_add_new_norm_le
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (htau : 0 ≤ tau) (hd : 0 < d) (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hnew : IntervalIntegrable
      (fun s : Real ↦ heatD2Conv (tau + d - s) v w (f s) x)
      volume tau (tau + d)) :
    ‖∫ s : Real in tau..tau + d,
        heatD2Conv (tau + d - s) v w (f s) x‖ ≤
      d2DuhHolderConst alpha v w K *
        ((2 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) := by
  have hscale : IntervalIntegrable
      (fun s : Real ↦ holderHeatScale alpha (tau + d - s))
      volume tau (tau + d) := by
    have hs :=
      (holderHeatScale_intervalIntegrable halpha0 0 d).comp_sub_left (tau + d)
    simpa only [sub_zero, add_sub_cancel_right] using hs.symm
  calc
    ‖∫ s : Real in tau..tau + d,
        heatD2Conv (tau + d - s) v w (f s) x‖ ≤
      ∫ s : Real in tau..tau + d,
        ‖heatD2Conv (tau + d - s) v w (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm
        (le_add_of_nonneg_right hd.le)
    _ ≤ ∫ s : Real in tau..tau + d,
        d2DuhHolderConst alpha v w K *
          holderHeatScale alpha (tau + d - s) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo
        (le_add_of_nonneg_right hd.le) hnew.norm
        (hscale.const_mul (d2DuhHolderConst alpha v w K))
      intro s hs
      have htime : 0 < tau + d - s := sub_pos.mpr hs.2
      rw [heatD2Conv_eq_cancel_of_holder halpha0 halpha1 htime
        (hf s ⟨htau.trans hs.1.le, hs.2.le⟩) v w x]
      refine (heatD2Cancel_norm_of_holder halpha1 htime
        (hf s ⟨htau.trans hs.1.le, hs.2.le⟩) v w x).trans_eq ?_
      unfold d2DuhHolderConst
      ring
    _ = d2DuhHolderConst alpha v w K *
        ((2 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) := by
      rw [intervalIntegral.integral_const_mul,
        holderHeatScale_terminal_interval_int halpha0
          (lt_add_of_pos_right tau hd), add_sub_cancel_left]

private theorem heatD2Duh_time_add_late_norm_le
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (hd : 0 < d) (hdt : d < tau)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hq : IntervalIntegrable
      (fun s : Real ↦ heatD2Conv ((tau - s) + d) v w (f s) x -
        heatD2Conv (tau - s) v w (f s) x)
      volume 0 (tau - d)) :
    ‖∫ s : Real in 0..tau - d,
        heatD2Conv ((tau - s) + d) v w (f s) x -
          heatD2Conv (tau - s) v w (f s) x‖ ≤
      (‖v‖ * ‖w‖ * (K : Real) * heatC2DtHolder (V := V) alpha) *
        ((2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2)) := by
  let B : Real := ‖v‖ * ‖w‖ * (K : Real) * heatC2DtHolder (V := V) alpha
  have hB : 0 ≤ B := by
    unfold B
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
      (heatC2DtHolder_nonneg (V := V) alpha)
  have hscale0 := holderSecondTimeHeatScale_intervalIntegrable
    (alpha := alpha) hd hdt.le
  have hscale : IntervalIntegrable
      (fun s : Real ↦ holderSecondTimeHeatScale alpha (tau - s))
      volume 0 (tau - d) := by
    have hs := hscale0.comp_sub_left tau
    simpa only [sub_self] using hs.symm
  have halpha2 : alpha < 2 := halpha1.trans_lt (by norm_num)
  calc
    ‖∫ s : Real in 0..tau - d,
        heatD2Conv ((tau - s) + d) v w (f s) x -
          heatD2Conv (tau - s) v w (f s) x‖ ≤
      ∫ s : Real in 0..tau - d,
        ‖heatD2Conv ((tau - s) + d) v w (f s) x -
          heatD2Conv (tau - s) v w (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (sub_nonneg.mpr hdt.le)
    _ ≤ ∫ s : Real in 0..tau - d,
        (d * B) * holderSecondTimeHeatScale alpha (tau - s) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo
        (sub_nonneg.mpr hdt.le) hq.norm (hscale.const_mul (d * B))
      intro s hs
      have htime : 0 < tau - s := by linarith [hs.2]
      have hfs : HolderWith K alpha (f s) :=
        hf s ⟨hs.1.le, by linarith [hs.2]⟩
      refine (heatD2Conv_time_add_sub_norm_le_of_holder
        halpha0 halpha1 htime hd.le hfs v w x).trans_eq ?_
      unfold B
      ring_nf
    _ = B * (d *
        ∫ u : Real in d..tau, holderSecondTimeHeatScale alpha u) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left]
      simp only [sub_sub_cancel]
      ring_nf
    _ ≤ B * ((2 / (2 - (alpha : Real))) *
        d ^ ((alpha : Real) / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_holderSecondTimeHeatScale_integral_le halpha2 hd hdt.le) hB
    _ = (‖v‖ * ‖w‖ * (K : Real) * heatC2DtHolder alpha) *
        ((2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2)) := by
      rfl

private theorem heatD2Duh_time_add_near_norm_le
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (hd : 0 < d) (hdt : d < tau)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hq : IntervalIntegrable
      (fun s : Real ↦ heatD2Conv ((tau - s) + d) v w (f s) x -
        heatD2Conv (tau - s) v w (f s) x)
      volume (tau - d) tau) :
    ‖∫ s : Real in tau - d..tau,
        heatD2Conv ((tau - s) + d) v w (f s) x -
          heatD2Conv (tau - s) v w (f s) x‖ ≤
      d2DuhHolderConst alpha v w K *
        ((4 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) := by
  have hscale : IntervalIntegrable
      (fun s : Real ↦ holderHeatScale alpha (tau - s))
      volume (tau - d) tau := by
    have hs :=
      (holderHeatScale_intervalIntegrable halpha0 0 d).comp_sub_left tau
    simpa only [sub_zero] using hs.symm
  have hC : 0 ≤ d2DuhHolderConst alpha v w K := by
    unfold d2DuhHolderConst
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w)) K.coe_nonneg)
      (heatC2Holder_nonneg (V := V) alpha)
  calc
    ‖∫ s : Real in tau - d..tau,
        heatD2Conv ((tau - s) + d) v w (f s) x -
          heatD2Conv (tau - s) v w (f s) x‖ ≤
      ∫ s : Real in tau - d..tau,
        ‖heatD2Conv ((tau - s) + d) v w (f s) x -
          heatD2Conv (tau - s) v w (f s) x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (sub_le_self tau hd.le)
    _ ≤ ∫ s : Real in tau - d..tau,
        (2 * d2DuhHolderConst alpha v w K) *
          holderHeatScale alpha (tau - s) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo
        (sub_le_self tau hd.le) hq.norm
        (hscale.const_mul (2 * d2DuhHolderConst alpha v w K))
      intro s hs
      have htime : 0 < tau - s := sub_pos.mpr hs.2
      have htimeplus : 0 < (tau - s) + d :=
        htime.trans_le (le_add_of_nonneg_right hd.le)
      have hfs : HolderWith K alpha (f s) :=
        hf s ⟨by linarith [hs.1, hdt], by linarith [hs.2]⟩
      have hplus : ‖heatD2Conv ((tau - s) + d) v w (f s) x‖ ≤
          d2DuhHolderConst alpha v w K *
            holderHeatScale alpha ((tau - s) + d) := by
        rw [heatD2Conv_eq_cancel_of_holder
          halpha0 halpha1 htimeplus hfs v w x]
        refine (heatD2Cancel_norm_of_holder halpha1 htimeplus hfs v w x).trans_eq ?_
        unfold d2DuhHolderConst
        ring
      have hnow : ‖heatD2Conv (tau - s) v w (f s) x‖ ≤
          d2DuhHolderConst alpha v w K * holderHeatScale alpha (tau - s) := by
        rw [heatD2Conv_eq_cancel_of_holder halpha0 halpha1 htime hfs v w x]
        refine (heatD2Cancel_norm_of_holder halpha1 htime hfs v w x).trans_eq ?_
        unfold d2DuhHolderConst
        ring
      have hscaleAdd := holderHeatScale_add_le halpha1 htime hd.le
      calc
        ‖heatD2Conv ((tau - s) + d) v w (f s) x -
            heatD2Conv (tau - s) v w (f s) x‖ ≤
          ‖heatD2Conv ((tau - s) + d) v w (f s) x‖ +
            ‖heatD2Conv (tau - s) v w (f s) x‖ := norm_sub_le _ _
        _ ≤ d2DuhHolderConst alpha v w K *
              holderHeatScale alpha ((tau - s) + d) +
            d2DuhHolderConst alpha v w K *
              holderHeatScale alpha (tau - s) := add_le_add hplus hnow
        _ ≤ d2DuhHolderConst alpha v w K * holderHeatScale alpha (tau - s) +
            d2DuhHolderConst alpha v w K * holderHeatScale alpha (tau - s) := by
          gcongr
        _ = (2 * d2DuhHolderConst alpha v w K) *
            holderHeatScale alpha (tau - s) := by ring
    _ = d2DuhHolderConst alpha v w K *
        ((4 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) := by
      rw [intervalIntegral.integral_const_mul,
        holderHeatScale_terminal_interval_int halpha0 (sub_lt_self tau hd),
        sub_sub_cancel]
      ring

private theorem heatD2Duh_time_add_sub_norm_le_small
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (htau : 0 < tau) (hd : 0 < d) (hdt : d < tau)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hmeasplus : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (tau + d - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) (tau + d))))
    (hmeasnow : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (tau - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) tau))) :
    ‖heatD2Duh (tau + d) v w f x - heatD2Duh tau v w f x‖ ≤
      d2DuhTimeHolderConst alpha v w K * d ^ ((alpha : Real) / 2) := by
  have htplus : 0 < tau + d := htau.trans (lt_add_of_pos_right tau hd)
  have hplus := heatD2Duh_int_of_holder
    halpha0 halpha1 htplus f hf v w x hmeasplus
  have hfnow : ∀ s ∈ Icc (0 : Real) tau, HolderWith K alpha (f s) := by
    intro s hs
    exact hf s ⟨hs.1, hs.2.trans (le_add_of_nonneg_right hd.le)⟩
  have hnow := heatD2Duh_int_of_holder
    halpha0 halpha1 htau f hfnow v w x hmeasnow
  have hplusOld : IntervalIntegrable
      (fun s : Real ↦ heatD2Conv (tau + d - s) v w (f s) x)
      volume 0 tau := by
    apply hplus.mono_set
    rw [uIcc_of_le htau.le, uIcc_of_le htplus.le]
    exact Icc_subset_Icc le_rfl (le_add_of_nonneg_right hd.le)
  have hnew : IntervalIntegrable
      (fun s : Real ↦ heatD2Conv (tau + d - s) v w (f s) x)
      volume tau (tau + d) := by
    apply hplus.mono_set
    rw [uIcc_of_le (le_add_of_nonneg_right hd.le), uIcc_of_le htplus.le]
    exact Icc_subset_Icc htau.le le_rfl
  have hq : IntervalIntegrable
      (fun s : Real ↦ heatD2Conv ((tau - s) + d) v w (f s) x -
        heatD2Conv (tau - s) v w (f s) x)
      volume 0 tau := by
    have hraw := hplusOld.sub hnow
    refine hraw.congr ?_
    intro s _
    ring_nf
  have hlate : IntervalIntegrable
      (fun s : Real ↦ heatD2Conv ((tau - s) + d) v w (f s) x -
        heatD2Conv (tau - s) v w (f s) x)
      volume 0 (tau - d) := by
    apply hq.mono_set
    rw [uIcc_of_le (sub_nonneg.mpr hdt.le), uIcc_of_le htau.le]
    exact Icc_subset_Icc le_rfl (sub_le_self tau hd.le)
  have hnear : IntervalIntegrable
      (fun s : Real ↦ heatD2Conv ((tau - s) + d) v w (f s) x -
        heatD2Conv (tau - s) v w (f s) x)
      volume (tau - d) tau := by
    apply hq.mono_set
    rw [uIcc_of_le (sub_le_self tau hd.le), uIcc_of_le htau.le]
    exact Icc_subset_Icc (sub_nonneg.mpr hdt.le) le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hlate hnear
  have hlateBound := heatD2Duh_time_add_late_norm_le
    halpha0 halpha1 hd hdt f hf v w x hlate
  have hnearBound := heatD2Duh_time_add_near_norm_le
    halpha0 halpha1 hd hdt f hf v w x hnear
  have hnewBound := heatD2Duh_time_add_new_norm_le
    halpha0 halpha1 htau.le hd f hf v w x hnew
  rw [heatD2Duh_time_add_sub_eq halpha0 halpha1 htau hd.le
    f hf v w x hmeasplus hmeasnow, ← hsplit]
  calc
    ‖((∫ s : Real in 0..tau - d,
          heatD2Conv (tau - s + d) v w (f s) x -
            heatD2Conv (tau - s) v w (f s) x) +
        ∫ s : Real in tau - d..tau,
          heatD2Conv (tau - s + d) v w (f s) x -
            heatD2Conv (tau - s) v w (f s) x) +
      ∫ s : Real in tau..tau + d,
        heatD2Conv (tau + d - s) v w (f s) x‖ ≤
      ‖∫ s : Real in 0..tau - d,
          heatD2Conv (tau - s + d) v w (f s) x -
            heatD2Conv (tau - s) v w (f s) x‖ +
        ‖∫ s : Real in tau - d..tau,
          heatD2Conv (tau - s + d) v w (f s) x -
            heatD2Conv (tau - s) v w (f s) x‖ +
        ‖∫ s : Real in tau..tau + d,
          heatD2Conv (tau + d - s) v w (f s) x‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖v‖ * ‖w‖ * (K : Real) * heatC2DtHolder alpha) *
          ((2 / (2 - (alpha : Real))) * d ^ ((alpha : Real) / 2)) +
        d2DuhHolderConst alpha v w K *
          ((4 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) +
        d2DuhHolderConst alpha v w K *
          ((2 / (alpha : Real)) * d ^ ((alpha : Real) / 2)) :=
      add_le_add (add_le_add hlateBound hnearBound) hnewBound
    _ = d2DuhTimeHolderConst alpha v w K * d ^ ((alpha : Real) / 2) := by
      unfold d2DuhHolderConst d2DuhTimeHolderConst
      ring

theorem heatD2Duh_time_add_sub_norm_le_of_holder
    {alpha K : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    {tau d : Real} (htau : 0 < tau) (hd : 0 ≤ d)
    (f : Real → V → F)
    (hf : ∀ s ∈ Icc (0 : Real) (tau + d), HolderWith K alpha (f s))
    (v w x : V)
    (hmeasplus : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (tau + d - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) (tau + d))))
    (hmeasnow : AEStronglyMeasurable
      (fun s : Real ↦ heatD2Conv (tau - s) v w (f s) x)
      (volume.restrict (uIoc (0 : Real) tau))) :
    ‖heatD2Duh (tau + d) v w f x - heatD2Duh tau v w f x‖ ≤
      d2DuhTimeHolderConst alpha v w K * d ^ ((alpha : Real) / 2) := by
  by_cases hd0 : d = 0
  · subst d
    simp only [add_zero, sub_self, norm_zero]
    rw [Real.zero_rpow]
    · simp
    · positivity
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  by_cases htd : tau ≤ d
  · exact heatD2Duh_time_add_sub_norm_le_large
      halpha0 halpha1 htau htd f hf v w x hmeasplus hmeasnow
  · exact heatD2Duh_time_add_sub_norm_le_small
      halpha0 halpha1 htau hdpos (lt_of_not_ge htd)
      f hf v w x hmeasplus hmeasnow

end Convolution

end DifferentialGeometry.Analysis.Parabolic.Euclidean
