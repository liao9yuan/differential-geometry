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

end Convolution

end DifferentialGeometry.Analysis.Parabolic.Euclidean
