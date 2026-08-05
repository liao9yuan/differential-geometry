import DifferentialGeometry.Analysis.Calculus.CutoffProfile
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.PreH1
import DifferentialGeometry.Analysis.Parabolic.Energy.TimeCutoff
import DifferentialGeometry.Geometry.Metric.MetricBounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.CutoffProfile
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem

def moserCutoffLevel (k : ℕ) : ℝ :=
  1 - (2 : ℝ)⁻¹ ^ k

def moserCutoffWidth (k : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ (k + 1)

theorem moserCutoffWidth_pos (k : ℕ) :
    0 < moserCutoffWidth k := by
  exact pow_pos (by norm_num) _

theorem moserCutoffLevel_lt_one (k : ℕ) :
    moserCutoffLevel k < 1 := by
  rw [moserCutoffLevel]
  exact sub_lt_self 1 (pow_pos (by norm_num) k)

theorem moserCutoffLevel_succ_sub (k : ℕ) :
    moserCutoffLevel (k + 1) - moserCutoffLevel k = moserCutoffWidth k := by
  simp only [moserCutoffLevel, moserCutoffWidth, pow_succ]
  ring

theorem moserCutoffWidth_succ_inv_sq (k : ℕ) :
    (moserCutoffWidth (k + 1) ^ 2)⁻¹ = (16 : ℝ) * 4 ^ k := by
  simp only [moserCutoffWidth, pow_succ, inv_pow]
  ring_nf
  norm_num [pow_mul]
  rw [pow_two, ← mul_pow]
  norm_num

theorem moserCutoffLevel_strictMono : StrictMono moserCutoffLevel := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [← sub_pos, moserCutoffLevel_succ_sub]
  exact moserCutoffWidth_pos k

def moserTimeLevel (a τ : ℝ) (k : ℕ) : ℝ :=
  τ - (τ - a) * (2 : ℝ)⁻¹ ^ k

def moserTimeWidth (a τ : ℝ) (k : ℕ) : ℝ :=
  (τ - a) * (2 : ℝ)⁻¹ ^ (k + 1)

def moserUpperTimeLevel (τ b : ℝ) (k : ℕ) : ℝ :=
  τ + (b - τ) * (2 : ℝ)⁻¹ ^ k

def moserUpperTimeWidth (τ b : ℝ) (k : ℕ) : ℝ :=
  (b - τ) * (2 : ℝ)⁻¹ ^ (k + 1)

@[simp]
theorem moserTimeLevel_zero (a τ : ℝ) :
    moserTimeLevel a τ 0 = a := by
  simp [moserTimeLevel]

theorem moserTimeLevel_succ_sub (a τ : ℝ) (k : ℕ) :
    moserTimeLevel a τ (k + 1) - moserTimeLevel a τ k =
      moserTimeWidth a τ k := by
  simp only [moserTimeLevel, moserTimeWidth, pow_succ]
  ring

theorem moserTimeWidth_pos {a τ : ℝ} (haτ : a < τ) (k : ℕ) :
    0 < moserTimeWidth a τ k := by
  exact mul_pos (sub_pos.mpr haτ) (pow_pos (by norm_num) _)

theorem moserTimeWidth_inv (a τ : ℝ) (k : ℕ) :
    (moserTimeWidth a τ k)⁻¹ = (2 : ℝ) ^ (k + 1) / (τ - a) := by
  simp only [moserTimeWidth, mul_inv_rev, ← inv_pow, inv_inv, div_eq_mul_inv]

@[simp]
theorem moserUpperTimeLevel_zero (τ b : ℝ) :
    moserUpperTimeLevel τ b 0 = b := by
  simp [moserUpperTimeLevel]

theorem moserUpperTimeLevel_sub_succ (τ b : ℝ) (k : ℕ) :
    moserUpperTimeLevel τ b k - moserUpperTimeLevel τ b (k + 1) =
      moserUpperTimeWidth τ b k := by
  simp only [moserUpperTimeLevel, moserUpperTimeWidth, pow_succ]
  ring

theorem moserUpperTimeWidth_pos {τ b : ℝ} (hτb : τ < b) (k : ℕ) :
    0 < moserUpperTimeWidth τ b k := by
  exact mul_pos (sub_pos.mpr hτb) (pow_pos (by norm_num) _)

theorem moserUpperTimeWidth_inv (τ b : ℝ) (k : ℕ) :
    (moserUpperTimeWidth τ b k)⁻¹ = (2 : ℝ) ^ (k + 1) / (b - τ) := by
  simp only [moserUpperTimeWidth, mul_inv_rev, ← inv_pow, inv_inv, div_eq_mul_inv]

theorem moserUpperTimeLevel_succ_lt {τ b : ℝ} (hτb : τ < b) (k : ℕ) :
    moserUpperTimeLevel τ b (k + 1) < moserUpperTimeLevel τ b k := by
  rw [← sub_pos, moserUpperTimeLevel_sub_succ]
  exact moserUpperTimeWidth_pos hτb k

theorem moserUpperTimeLevel_strictAnti {τ b : ℝ} (hτb : τ < b) :
    StrictAnti (moserUpperTimeLevel τ b) := by
  exact strictAnti_nat_of_succ_lt (moserUpperTimeLevel_succ_lt hτb)

theorem moserUpperTimeLevel_le {τ b : ℝ} (hτb : τ < b) (k : ℕ) :
    moserUpperTimeLevel τ b k ≤ b := by
  calc
    moserUpperTimeLevel τ b k ≤ moserUpperTimeLevel τ b 0 :=
      (moserUpperTimeLevel_strictAnti hτb).antitone (Nat.zero_le k)
    _ = b := moserUpperTimeLevel_zero τ b

theorem moserUpperTimeLevel_lt {τ b : ℝ} (hτb : τ < b) (k : ℕ) :
    τ < moserUpperTimeLevel τ b k := by
  rw [moserUpperTimeLevel]
  exact lt_add_of_pos_right τ (mul_pos (sub_pos.mpr hτb) (pow_pos (by norm_num) _))

theorem moserTimeLevel_lt_succ {a τ : ℝ} (haτ : a < τ) (k : ℕ) :
    moserTimeLevel a τ k < moserTimeLevel a τ (k + 1) := by
  rw [← sub_pos, moserTimeLevel_succ_sub]
  exact moserTimeWidth_pos haτ k

theorem moserTimeLevel_strictMono {a τ : ℝ} (haτ : a < τ) :
    StrictMono (moserTimeLevel a τ) := by
  exact strictMono_nat_of_lt_succ (moserTimeLevel_lt_succ haτ)

theorem moserTimeLevel_le {a τ : ℝ} (haτ : a < τ) (k : ℕ) :
    a ≤ moserTimeLevel a τ k := by
  calc
    a = moserTimeLevel a τ 0 := (moserTimeLevel_zero a τ).symm
    _ ≤ moserTimeLevel a τ k :=
      (moserTimeLevel_strictMono haτ).monotone (Nat.zero_le k)

theorem moserTimeLevel_lt {a τ : ℝ} (haτ : a < τ) (k : ℕ) :
    moserTimeLevel a τ k < τ := by
  rw [moserTimeLevel]
  exact sub_lt_self τ (mul_pos (sub_pos.mpr haτ) (pow_pos (by norm_num) _))

theorem timeCutoffDeriv_moserTimeLevel_le
    {a τ : ℝ} (haτ : a < τ) (k : ℕ) (t : ℝ) :
    DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv
        (moserTimeLevel a τ k) (moserTimeLevel a τ (k + 1)) t ≤
      DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant /
        moserTimeWidth a τ k := by
  have h := DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv_le
    (moserTimeLevel_lt_succ haτ k) t
  rwa [moserTimeLevel_succ_sub] at h

theorem timeCutoffDeriv_moserTimeLevel_le_mul_pow
    {a τ : ℝ} (haτ : a < τ) (k : ℕ) (t : ℝ) :
    DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv
        (moserTimeLevel a τ k) (moserTimeLevel a τ (k + 1)) t ≤
      (2 * DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant /
          (τ - a)) * 2 ^ k := by
  calc
    _ ≤ DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant /
        moserTimeWidth a τ k := timeCutoffDeriv_moserTimeLevel_le haτ k t
    _ = DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant *
        ((2 : ℝ) ^ (k + 1) / (τ - a)) := by
      rw [div_eq_mul_inv, moserTimeWidth_inv]
    _ = (2 * DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant /
          (τ - a)) * 2 ^ k := by
      rw [pow_succ]
      ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def spatialMoserCutoffArgument
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g) (k : ℕ) (x : M) : ℝ :=
  1 + (moserCutoffLevel (k + 1) - rho.toFun x) / moserCutoffWidth k

def spatialMoserCutoff
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g) (k : ℕ) : SmoothScalar g where
  toFun := fun x => CutoffProfile.value (spatialMoserCutoffArgument rho k x)
  smooth := by
    apply CutoffProfile.contDiff.contMDiff.comp
    exact contMDiff_const.add
      ((contMDiff_const.sub rho.smooth).div_const (moserCutoffWidth k))

omit [Module.Finite ℝ E] in
@[simp]
theorem spatialMoserCutoff_toFun
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g) (k : ℕ) (x : M) :
    (spatialMoserCutoff rho k).toFun x =
      CutoffProfile.value (spatialMoserCutoffArgument rho k x) := rfl

omit [Module.Finite ℝ E] in
theorem spatialMoserCutoff_mem_Icc
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g) (k : ℕ) (x : M) :
    (spatialMoserCutoff rho k).toFun x ∈ Icc (0 : ℝ) 1 :=
  CutoffProfile.mem_Icc _

omit [Module.Finite ℝ E] in
theorem spatialMoserCutoff_eq_one_of_level_le
    {g : SmoothRiemannianMetric I M} {rho : SmoothScalar g} {k : ℕ} {x : M}
    (hx : moserCutoffLevel (k + 1) ≤ rho.toFun x) :
    (spatialMoserCutoff rho k).toFun x = 1 := by
  apply CutoffProfile.one_of_le_one
  rw [spatialMoserCutoffArgument]
  have hwidth := moserCutoffWidth_pos k
  have hquotient :
      (moserCutoffLevel (k + 1) - rho.toFun x) / moserCutoffWidth k ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hwidth.le
  linarith

omit [Module.Finite ℝ E] in
theorem spatialMoserCutoff_eq_zero_of_le_level
    {g : SmoothRiemannianMetric I M} {rho : SmoothScalar g} {k : ℕ} {x : M}
    (hx : rho.toFun x ≤ moserCutoffLevel k) :
    (spatialMoserCutoff rho k).toFun x = 0 := by
  apply CutoffProfile.zero_of_two_le
  rw [spatialMoserCutoffArgument]
  have hwidth := moserCutoffWidth_pos k
  rw [show (2 : ℝ) = 1 + 1 by norm_num, add_le_add_iff_left,
    le_div_iff₀ hwidth]
  rw [← moserCutoffLevel_succ_sub k]
  linarith

omit [Module.Finite ℝ E] in
theorem spatialMoserCutoff_succ_sq_le
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g) (k : ℕ) (x : M) :
    (spatialMoserCutoff rho (k + 1)).toFun x ^ 2 ≤
      (spatialMoserCutoff rho k).toFun x ^ 2 := by
  by_cases hx : rho.toFun x ≤ moserCutoffLevel (k + 1)
  · rw [spatialMoserCutoff_eq_zero_of_le_level hx]
    simpa using sq_nonneg ((spatialMoserCutoff rho k).toFun x)
  · have hone : (spatialMoserCutoff rho k).toFun x = 1 :=
      spatialMoserCutoff_eq_one_of_level_le (le_of_not_ge hx)
    rw [hone, one_pow]
    have hmem := spatialMoserCutoff_mem_Icc rho (k + 1) x
    simpa using (sq_le_sq₀ hmem.1 (by norm_num : (0 : ℝ) ≤ 1)).2 hmem.2

omit [Module.Finite ℝ E] in
theorem spatialMoserCutoff_add_two_sq_le_rpow
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g) (k : ℕ) (x : M)
    (p : ℝ) :
    (spatialMoserCutoff rho (k + 2)).toFun x ^ 2 ≤
      (spatialMoserCutoff rho (k + 1)).toFun x ^ p := by
  by_cases hx : rho.toFun x ≤ moserCutoffLevel (k + 2)
  · rw [spatialMoserCutoff_eq_zero_of_le_level hx]
    norm_num
    exact Real.rpow_nonneg (spatialMoserCutoff_mem_Icc rho (k + 1) x).1 p
  · have hone : (spatialMoserCutoff rho (k + 1)).toFun x = 1 := by
      apply spatialMoserCutoff_eq_one_of_level_le
      simpa only [Nat.add_assoc] using le_of_not_ge hx
    rw [hone, Real.one_rpow]
    have hmem := spatialMoserCutoff_mem_Icc rho (k + 2) x
    simpa using (sq_le_sq₀ hmem.1 (by norm_num : (0 : ℝ) ≤ 1)).2 hmem.2

theorem gradientFun_spatialMoserCutoff
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (rho : SmoothScalar g) (k : ℕ) (x : M) :
    gradientFun (I := I) g (spatialMoserCutoff rho k).toFun x =
      (deriv CutoffProfile.value (spatialMoserCutoffArgument rho k x) *
          (-1 / moserCutoffWidth k)) •
        gradientFun (I := I) g rho.toFun x := by
  let affine : ℝ → ℝ := fun s =>
    1 + (moserCutoffLevel (k + 1) - s) / moserCutoffWidth k
  let profile : ℝ → ℝ := fun s => CutoffProfile.value (affine s)
  have haffine : HasDerivAt affine (-1 / moserCutoffWidth k) (rho.toFun x) := by
    have h := (hasDerivAt_const (rho.toFun x) (1 : ℝ)).add
      (((hasDerivAt_const (rho.toFun x) (moserCutoffLevel (k + 1))).sub
        (hasDerivAt_id (rho.toFun x))).div_const (moserCutoffWidth k))
    simpa only [affine, zero_sub, zero_add] using h
  have hvalue : HasDerivAt CutoffProfile.value
      (deriv CutoffProfile.value (affine (rho.toFun x)))
      (affine (rho.toFun x)) :=
    (CutoffProfile.contDiff.differentiable (by simp) _).hasDerivAt
  have hprofile : HasDerivAt profile
      (deriv CutoffProfile.value (affine (rho.toFun x)) *
        (-1 / moserCutoffWidth k)) (rho.toFun x) := by
    simpa only [profile] using hvalue.comp (rho.toFun x) haffine
  have hgradient := gradientFun_comp (I := I) g hprofile.differentiableAt
    (rho.smooth.mdifferentiable (by simp) x)
  simpa only [profile, affine, spatialMoserCutoff_toFun,
    spatialMoserCutoffArgument, hprofile.deriv] using hgradient

theorem spatialMoserCutoff_succ_gradient_le
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (rho : SmoothScalar g)
    {B : ℝ} (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (k : ℕ) (x : M) :
    g.inner x
        (gradFun (I := I) g (spatialMoserCutoff rho (k + 1)).toFun x)
        (gradFun (I := I) g (spatialMoserCutoff rho (k + 1)).toFun x) ≤
      (CutoffProfile.derivBound ^ 2 * B / moserCutoffWidth (k + 1) ^ 2) *
        (spatialMoserCutoff rho k).toFun x ^ 2 := by
  let argument := spatialMoserCutoffArgument rho (k + 1) x
  let coefficient := deriv CutoffProfile.value argument *
    (-1 / moserCutoffWidth (k + 1))
  have hgradient :
      gradFun (I := I) g (spatialMoserCutoff rho (k + 1)).toFun x =
        coefficient • gradFun (I := I) g rho.toFun x := by
    exact gradientFun_spatialMoserCutoff (I := I) g rho (k + 1) x
  by_cases hx : rho.toFun x ≤ moserCutoffLevel (k + 1)
  · have hargument : 2 ≤ argument := by
      dsimp only [argument, spatialMoserCutoffArgument]
      have hwidth := moserCutoffWidth_pos (k + 1)
      rw [show (2 : ℝ) = 1 + 1 by norm_num, add_le_add_iff_left,
        le_div_iff₀ hwidth]
      rw [← moserCutoffLevel_succ_sub (k + 1)]
      linarith
    have hderiv : deriv CutoffProfile.value argument = 0 :=
      CutoffProfile.deriv_zero_of_ge hargument
    rw [hgradient]
    simp only [coefficient, hderiv, zero_mul, zero_smul, map_zero]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (sq_nonneg _) hB)
        (sq_nonneg (moserCutoffWidth (k + 1))))
      (sq_nonneg _)
  · have hone : (spatialMoserCutoff rho k).toFun x = 1 :=
      spatialMoserCutoff_eq_one_of_level_le (le_of_not_ge hx)
    have hwidth : 0 < moserCutoffWidth (k + 1) := moserCutoffWidth_pos _
    have hinner_nonneg : 0 ≤
        g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) :=
      metric_inner_self_nonneg (I := I) (M := M) g x _
    have hderiv_sq : deriv CutoffProfile.value argument ^ 2 ≤
        CutoffProfile.derivBound ^ 2 := by
      calc
        deriv CutoffProfile.value argument ^ 2 =
            |deriv CutoffProfile.value argument| ^ 2 :=
          (sq_abs _).symm
        _ ≤ CutoffProfile.derivBound ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) CutoffProfile.derivBound_nonneg).2
            (CutoffProfile.abs_deriv_le_derivBound argument)
    rw [hgradient, metric_inner_smul_self, hone, one_pow, mul_one]
    have hcoefficient : coefficient ^ 2 ≤
        CutoffProfile.derivBound ^ 2 / moserCutoffWidth (k + 1) ^ 2 := by
      dsimp only [coefficient]
      rw [mul_pow, div_pow]
      norm_num
      exact div_le_div_of_nonneg_right hderiv_sq (sq_nonneg _)
    calc
      coefficient ^ 2 *
          g.inner x
            (gradFun (I := I) g rho.toFun x)
            (gradFun (I := I) g rho.toFun x) ≤
          (CutoffProfile.derivBound ^ 2 /
            moserCutoffWidth (k + 1) ^ 2) * B :=
        mul_le_mul hcoefficient (hrho x) hinner_nonneg
          (div_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = CutoffProfile.derivBound ^ 2 * B /
          moserCutoffWidth (k + 1) ^ 2 := by
        ring

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [SigmaCompactSpace M] in
theorem exists_spatialMoserCutoff_gradient_bound
    (g : SmoothRiemannianMetric I M) (rho : SmoothScalar g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (k : ℕ) (x : M),
      g.inner x
          (gradFun (I := I) g (spatialMoserCutoff rho (k + 1)).toFun x)
          (gradFun (I := I) g (spatialMoserCutoff rho (k + 1)).toFun x) ≤
        K * 4 ^ k *
          (spatialMoserCutoff rho k).toFun x ^ 2 := by
  have hcontinuous : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I) g rho.toFun x)
        (gradFun (I := I) g rho.toFun x)) := by
    simpa only [grad_g_apply] using rho.continuous_inner_grad rho
  obtain ⟨B, hB⟩ := (isCompact_range hcontinuous).bddAbove
  let B₀ := max B 0
  let K := 16 * CutoffProfile.derivBound ^ 2 * B₀
  have hB₀ : 0 ≤ B₀ := le_max_right _ _
  have hK : 0 ≤ K := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg CutoffProfile.derivBound)) hB₀
  refine ⟨K, hK, ?_⟩
  intro k x
  have hgradient := spatialMoserCutoff_succ_gradient_le (I := I) g rho hB₀
    (fun y => (hB (mem_range_self y)).trans (le_max_left _ _)) k x
  calc
    _ ≤ (CutoffProfile.derivBound ^ 2 * B₀ /
          moserCutoffWidth (k + 1) ^ 2) *
        (spatialMoserCutoff rho k).toFun x ^ 2 := hgradient
    _ = K * 4 ^ k * (spatialMoserCutoff rho k).toFun x ^ 2 := by
      rw [div_eq_mul_inv, moserCutoffWidth_succ_inv_sq]
      dsimp only [K]
      ring

def spatialMoserCutoffGradientConstant
    (g : SmoothRiemannianMetric I M) (rho : SmoothScalar g) : ℝ :=
  Classical.choose (exists_spatialMoserCutoff_gradient_bound (I := I) g rho)

omit [SigmaCompactSpace M] in
theorem spatialMoserCutoffGradientConstant_nonneg
    (g : SmoothRiemannianMetric I M) (rho : SmoothScalar g) :
    0 ≤ spatialMoserCutoffGradientConstant (I := I) g rho :=
  (Classical.choose_spec
    (exists_spatialMoserCutoff_gradient_bound (I := I) g rho)).1

omit [SigmaCompactSpace M] in
theorem spatialMoserCutoff_gradient_le
    (g : SmoothRiemannianMetric I M) (rho : SmoothScalar g)
    (k : ℕ) (x : M) :
    g.inner x
        (gradFun (I := I) g (spatialMoserCutoff rho (k + 1)).toFun x)
        (gradFun (I := I) g (spatialMoserCutoff rho (k + 1)).toFun x) ≤
      spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ k *
        (spatialMoserCutoff rho k).toFun x ^ 2 :=
  (Classical.choose_spec
    (exists_spatialMoserCutoff_gradient_bound (I := I) g rho)).2 k x

end DifferentialGeometry.Analysis.Parabolic.Moser

end
