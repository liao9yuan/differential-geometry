import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Operator
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.InteriorAllscaleTimeContinuity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Time regularity of the scalar per-mode Duhamel convolution

The per-mode convolution `perModeConv lam f t = ∫₀ᵗ e^{−lam(t−s)} f(s) ds` is the scalar
variation-of-constants solution of the ODE `φ' + lam·φ = f`, `φ(0) = 0`.  This file develops its
**one-real-variable time regularity** on the closed slab `Icc 0 T` (one-sided at the endpoints),
the ODE-iteration content the per-mode Duhamel time-tower consumes:

* `perModeConv_contDiffOn_succ_of_contDiffOn` / `perModeConv_contDiffOn_infty` — the **ODE
  bootstrap**: a globally-continuous forcing that is `C^n` (resp. `C^∞`) on `Icc 0 T` produces a
  per-mode convolution that is `C^(n+1)` (resp. `C^∞`) on `Icc 0 T`.  The one-order gain is the
  ODE `φ' = f − lam·φ`.
* `iteratedDerivWithin_perModeConv` — the **closed-form within-`Icc` iterated derivative** (the ODE
  iteration): `∂ₜʲ (perModeConv lam f) = Σ_{l<j} (−lam)^{j−1−l} ∂ₜˡ f + (−lam)ʲ perModeConv lam f`.
* `duhamel_coeff_integral_eq_perModeConv` — the **carrier ↔ convolution bridge**: the indefinite
  integral of the per-mode derivative coordinate of an `L²` forcing equals, pointwise on `Icc 0 T`,
  the per-mode convolution of any globally-continuous representative of the forcing's coordinate.
-/

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

section Scalar

/-- **ODE bootstrap (`ℕ` version).**  A globally-continuous forcing that is `C^n` on `Icc 0 T`
produces a per-mode convolution that is `C^(n+1)` on `Icc 0 T`. -/
theorem perModeConv_contDiffOn_nat_succ_of_contDiffOn (lam : ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hfn : ContDiffOn ℝ (n : ℕ) f (Set.Icc (0 : ℝ) T)) :
    ContDiffOn ℝ ((n + 1 : ℕ) : ℕ) (perModeConv lam f) (Set.Icc (0 : ℝ) T) := by
  have hderivOn : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (perModeConv lam f) (f t - lam * perModeConv lam f t)
        (Set.Icc (0 : ℝ) T) t := fun t _ => perModeConv_hasDerivWithinAt lam hf T t
  induction n with
  | zero =>
    rw [show (((0 + 1 : ℕ) : ℕ) : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
    refine ⟨fun t ht => (hderivOn t ht).differentiableWithinAt, by simp, ?_⟩
    refine ContDiffOn.congr ?_ (fun t ht =>
      (hderivOn t ht).derivWithin ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht))
    exact contDiffOn_zero.mpr (continuous_perModeConv_deriv lam hf).continuousOn
  | succ k ih =>
    simp only [Nat.cast_add, Nat.cast_one] at *
    rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
    refine ⟨fun t ht => (hderivOn t ht).differentiableWithinAt, by simp, ?_⟩
    refine ContDiffOn.congr ?_ (fun t ht =>
      (hderivOn t ht).derivWithin ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht))
    have hpmc : ContDiffOn ℝ ((k : ℕ) + 1) (perModeConv lam f) (Set.Icc (0 : ℝ) T) := ih hfn.of_succ
    exact hfn.sub (hpmc.const_smul lam |>.congr (fun t _ => by simp [smul_eq_mul]))

/-- **ODE bootstrap (`ℕ∞` version)**, the form the per-mode time tower consumes. -/
theorem perModeConv_contDiffOn_succ_of_contDiffOn (lam : ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    {T : ℝ} (hT : 0 < T) {n : ℕ} (hfn : ContDiffOn ℝ (n : ℕ∞) f (Set.Icc (0 : ℝ) T)) :
    ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞) (perModeConv lam f) (Set.Icc (0 : ℝ) T) := by
  have h := perModeConv_contDiffOn_nat_succ_of_contDiffOn lam hf hT (n := n) (by exact_mod_cast hfn)
  exact_mod_cast h

/-- A globally-continuous `C^∞`-on-`Icc` forcing produces a `C^∞`-on-`Icc` per-mode convolution. -/
theorem perModeConv_contDiffOn_infty (lam : ℝ) {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ} (hT : 0 < T)
    (hfsmooth : ContDiffOn ℝ (∞ : WithTop ℕ∞) f (Set.Icc (0 : ℝ) T)) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞) (perModeConv lam f) (Set.Icc (0 : ℝ) T) := by
  rw [contDiffOn_infty]
  intro n
  have h := perModeConv_contDiffOn_nat_succ_of_contDiffOn lam hf hT (n := n)
    (contDiffOn_infty.mp hfsmooth n)
  exact h.of_le (by exact_mod_cast Nat.le_succ n)

/-- The within-`Icc` derivative of a per-mode convolution of a globally-continuous forcing is the
ODE right-hand side, as an `EqOn` identity. -/
theorem derivWithin_perModeConv_eqOn (lam : ℝ) {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ} (hT : 0 < T) :
    Set.EqOn (derivWithin (perModeConv lam f) (Set.Icc (0 : ℝ) T))
      (fun t => f t - lam * perModeConv lam f t) (Set.Icc (0 : ℝ) T) := fun t ht =>
  (perModeConv_hasDerivWithinAt lam hf T t).derivWithin ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)

/-- A pointwise `L¹`-type bound on the per-mode convolution of a continuous forcing: for
`0 ≤ lam` and `t ∈ [0,T]`, `|perModeConv lam f t| ≤ ∫₀ᵗ |f s| ds` (the heat kernel is `≤ 1`). -/
theorem abs_perModeConv_le_integral_abs (lam : ℝ) (hlam : 0 ≤ lam) {f : ℝ → ℝ} (hf : Continuous f)
    {t : ℝ} (ht0 : 0 ≤ t) :
    |perModeConv lam f t| ≤ ∫ s in (0 : ℝ)..t, |f s| := by
  have hker : Continuous (fun s => Real.exp (-(lam * (t - s))) * f s) := by fun_prop
  rw [perModeConv, ← Real.norm_eq_abs]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm ht0) ?_
  refine intervalIntegral.integral_mono_on ht0 (hker.norm.intervalIntegrable 0 t)
    (hf.abs.intervalIntegrable 0 t) (fun s hs => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hk : |Real.exp (-(lam * (t - s)))| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [hs.1, hs.2])
  nlinarith [abs_nonneg (f s), hk]

/-- **The closed-form within-`Icc` iterated derivative of a per-mode convolution** (the ODE
iteration): `∂ₜʲ (perModeConv lam f) = Σ_{l<j} (−lam)^{j−1−l} ∂ₜˡ f + (−lam)ʲ perModeConv lam f`. -/
theorem iteratedDerivWithin_perModeConv (lam : ℝ) {f : ℝ → ℝ} (hf : Continuous f) {T : ℝ}
    (hT : 0 < T) (hfsmooth : ContDiffOn ℝ (∞ : WithTop ℕ∞) f (Set.Icc (0 : ℝ) T)) (j : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    iteratedDerivWithin j (perModeConv lam f) (Set.Icc (0 : ℝ) T) t
      = (∑ l ∈ Finset.range j, (-lam) ^ (j - 1 - l) * iteratedDerivWithin l f (Set.Icc (0 : ℝ) T) t)
        + (-lam) ^ j * perModeConv lam f t := by
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hpmc_smooth : ContDiffOn ℝ (∞ : WithTop ℕ∞) (perModeConv lam f) (Set.Icc (0 : ℝ) T) :=
    perModeConv_contDiffOn_infty lam hf hT hfsmooth
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDerivWithin_succ']
    have hcongr : Set.EqOn
        (iteratedDerivWithin j (derivWithin (perModeConv lam f) (Set.Icc (0 : ℝ) T))
          (Set.Icc (0 : ℝ) T))
        (iteratedDerivWithin j (fun s => f s - lam * perModeConv lam f s) (Set.Icc (0 : ℝ) T))
        (Set.Icc (0 : ℝ) T) :=
      iteratedDerivWithin_congr (derivWithin_perModeConv_eqOn lam hf hT)
    rw [hcongr ht]
    have hsub : iteratedDerivWithin j (fun s => f s - lam * perModeConv lam f s)
          (Set.Icc (0 : ℝ) T) t
        = iteratedDerivWithin j f (Set.Icc (0 : ℝ) T) t
          - lam * iteratedDerivWithin j (perModeConv lam f) (Set.Icc (0 : ℝ) T) t := by
      have hfj : ContDiffWithinAt ℝ j f (Set.Icc (0 : ℝ) T) t := (contDiffOn_infty.mp hfsmooth j t ht)
      have hpj : ContDiffWithinAt ℝ j (perModeConv lam f) (Set.Icc (0 : ℝ) T) t :=
        (contDiffOn_infty.mp hpmc_smooth j t ht)
      have hlam_pmc : ContDiffWithinAt ℝ j (fun s => lam * perModeConv lam f s)
          (Set.Icc (0 : ℝ) T) t := hpj.const_smul lam |>.congr_of_eventuallyEq
        (by filter_upwards with s using by simp [smul_eq_mul]) (by simp [smul_eq_mul])
      have hrw : (fun s => f s - lam * perModeConv lam f s)
          = (fun s => f s) - (fun s => lam * perModeConv lam f s) := by funext s; rfl
      rw [hrw, iteratedDerivWithin_sub ht huniq hfj hlam_pmc]
      congr 1
      have hcs := iteratedDerivWithin_fun_const_smul (𝕜 := ℝ) (R := ℝ) (n := j)
        (f := perModeConv lam f) (s := Set.Icc (0 : ℝ) T) (x := t) ht huniq lam hpj
      simpa only [smul_eq_mul] using hcs
    rw [hsub, ih]
    set F : ℕ → ℝ := fun l => iteratedDerivWithin l f (Set.Icc (0 : ℝ) T) t with hF
    set P : ℝ := perModeConv lam f t with hP
    rw [show (∑ l ∈ Finset.range (j + 1), (-lam) ^ (j + 1 - 1 - l) * F l)
        = F j + ∑ l ∈ Finset.range j, (-lam) ^ (j - l) * F l by
      rw [Finset.sum_range_succ, add_comm]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]]
    rw [mul_add, Finset.mul_sum]
    have hshift : ∀ l ∈ Finset.range j,
        lam * ((-lam) ^ (j - 1 - l) * F l) = -((-lam) ^ (j - l) * F l) := by
      intro l hl
      have hlj : l < j := Finset.mem_range.mp hl
      have hpow : (-lam) ^ (j - l) = (-lam) ^ (j - 1 - l) * (-lam) := by
        rw [← pow_succ]; congr 1; omega
      rw [hpow]; ring
    rw [Finset.sum_congr rfl hshift, Finset.sum_neg_distrib]
    have hpowj : (-lam) ^ (j + 1) = lam * ((-lam) ^ j) * (-1) := by rw [pow_succ]; ring
    rw [hpowj]; ring

end Scalar

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

/-- FTC for a per-mode convolution of a globally-continuous forcing: the convolution is the
indefinite integral from `0` of the ODE right-hand side. -/
theorem perModeConv_eq_integral_deriv_continuous (lam : ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    (t : ℝ) :
    perModeConv lam f t = ∫ s in (0 : ℝ)..t, (f s - lam * perModeConv lam f s) := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (perModeConv lam f) (f s - lam * perModeConv lam f s) s :=
    fun s _ => perModeConv_hasDerivAt lam hf s
  have hint : IntervalIntegrable (fun s => f s - lam * perModeConv lam f s) volume 0 t :=
    (continuous_perModeConv_deriv lam hf).intervalIntegrable 0 t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, perModeConv_zero_left, sub_zero]

set_option linter.unusedSectionVars false in
/-- **The carrier-coordinate ↔ per-mode-convolution bridge.**  The indefinite integral of the
per-mode derivative coordinate of an `L²` forcing equals, pointwise on `Icc 0 T`, the per-mode
convolution of any globally-continuous representative `G` of the forcing's `i`-th coordinate. -/
theorem duhamel_coeff_integral_eq_perModeConv
    {g : SmoothRiemannianMetric I M} {a : ℝ} {Te : ℝ} (hTe : 0 ≤ Te)
    (gforce : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) Te)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2)
    {T : ℝ} (hTTe : T ≤ Te)
    {G : ℝ → ℝ} (hG : Continuous G)
    (hagree : (fun t => timeModeCoeff (I := I) (M := M) gforce i t)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] G)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0:ℝ)..t, (derivModeCoeff (I := I) (M := M) (a := a) hTe gforce i) τ)
      = perModeConv (TensorEigenIdx.lambda (I := I) (M := M) i) G t := by
  set lam := TensorEigenIdx.lambda (I := I) (M := M) i with hlam
  have hderiv_ae : (fun τ => (derivModeCoeff (I := I) (M := M) (a := a) hTe gforce i) τ)
      =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
      (fun τ => G τ - lam * perModeConv lam G τ) := by
    have h1 : (fun τ => (derivModeCoeff (I := I) (M := M) (a := a) hTe gforce i) τ)
        =ᵐ[volume.restrict (Set.Icc (0 : ℝ) Te)]
        (fun τ => timeModeCoeff (I := I) (M := M) gforce i τ
          - lam * perModeConv lam (fun s => timeModeCoeff (I := I) (M := M) gforce i s) τ) := by
      rw [derivModeCoeff]
      exact perModeConvDerivL2_coeFn lam (tensor_lambda_nonneg (I := I) (M := M) i) hTe _
    have h1' := ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl hTTe) h1
    filter_upwards [h1', hagree,
      (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall
        (fun τ (hτ : τ ∈ Set.Icc (0:ℝ) T) => hτ))] with τ hτ1 hτ2 hτmem
    rw [hτ1, hτ2]
    congr 2
    exact perModeConv_timeL2_congr lam hagree hτmem
  have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)
  have hint_congr : (∫ τ in (0:ℝ)..t, (derivModeCoeff (I := I) (M := M) (a := a) hTe gforce i) τ)
      = ∫ τ in (0:ℝ)..t, (G τ - lam * perModeConv lam G τ) := by
    refine intervalIntegral.integral_congr_ae ?_
    have hae := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hderiv_ae
    rw [ae_restrict_iff' measurableSet_uIoc] at hae
    filter_upwards [hae] with τ hτ using hτ
  rw [hint_congr, ← perModeConv_eq_integral_deriv_continuous lam hG t]

end Bridge

end DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
