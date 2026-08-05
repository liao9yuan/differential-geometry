import DifferentialGeometry.Analysis.Parabolic.Moser.Cutoff

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian

def bombieriGiustiInvScale (k : ℕ) : ℝ :=
  1 / (k + 1 : ℝ)

@[simp]
theorem bombieriGiustiInvScale_zero :
    bombieriGiustiInvScale 0 = 1 := by
  norm_num [bombieriGiustiInvScale]

theorem bombieriGiustiInvScale_pos (k : ℕ) :
    0 < bombieriGiustiInvScale k := by
  exact div_pos one_pos (by positivity)

theorem bombieriGiustiInvScale_le_one (k : ℕ) :
    bombieriGiustiInvScale k ≤ 1 := by
  unfold bombieriGiustiInvScale
  apply (div_le_one (by positivity)).2
  norm_num

theorem bombieriGiustiInvScale_succ_lt (k : ℕ) :
    bombieriGiustiInvScale (k + 1) < bombieriGiustiInvScale k := by
  unfold bombieriGiustiInvScale
  apply one_div_lt_one_div_of_lt
  · positivity
  · norm_num

theorem bombieriGiustiInvScale_strictAnti :
    StrictAnti bombieriGiustiInvScale := by
  exact strictAnti_nat_of_succ_lt bombieriGiustiInvScale_succ_lt

def bombieriGiustiDescendingLevel (lower upper : ℝ) (k : ℕ) : ℝ :=
  lower + (upper - lower) * bombieriGiustiInvScale k

def bombieriGiustiIncreasingLevel (lower upper : ℝ) (k : ℕ) : ℝ :=
  upper - (upper - lower) * bombieriGiustiInvScale k

@[simp]
theorem bombieriGiustiDescendingLevel_zero (lower upper : ℝ) :
    bombieriGiustiDescendingLevel lower upper 0 = upper := by
  simp [bombieriGiustiDescendingLevel]

@[simp]
theorem bombieriGiustiIncreasingLevel_zero (lower upper : ℝ) :
    bombieriGiustiIncreasingLevel lower upper 0 = lower := by
  simp [bombieriGiustiIncreasingLevel]

theorem bombieriGiustiDescendingLevel_strictAnti
    {lower upper : ℝ} (hlowerUpper : lower < upper) :
    StrictAnti (bombieriGiustiDescendingLevel lower upper) := by
  apply strictAnti_nat_of_succ_lt
  intro k
  unfold bombieriGiustiDescendingLevel
  simpa only [add_comm] using add_lt_add_left
    (mul_lt_mul_of_pos_left (bombieriGiustiInvScale_succ_lt k)
      (sub_pos.mpr hlowerUpper)) lower

theorem bombieriGiustiIncreasingLevel_strictMono
    {lower upper : ℝ} (hlowerUpper : lower < upper) :
    StrictMono (bombieriGiustiIncreasingLevel lower upper) := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold bombieriGiustiIncreasingLevel
  exact sub_lt_sub_left
    (mul_lt_mul_of_pos_left (bombieriGiustiInvScale_succ_lt k)
      (sub_pos.mpr hlowerUpper)) upper

theorem bombieriGiustiDescendingLevel_gt
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    lower < bombieriGiustiDescendingLevel lower upper k := by
  unfold bombieriGiustiDescendingLevel
  exact lt_add_of_pos_right lower
    (mul_pos (sub_pos.mpr hlowerUpper) (bombieriGiustiInvScale_pos k))

theorem bombieriGiustiDescendingLevel_le
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    bombieriGiustiDescendingLevel lower upper k ≤ upper := by
  have hmul := mul_le_mul_of_nonneg_left (bombieriGiustiInvScale_le_one k)
    (sub_pos.mpr hlowerUpper).le
  unfold bombieriGiustiDescendingLevel
  linarith

theorem bombieriGiustiIncreasingLevel_ge
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    lower ≤ bombieriGiustiIncreasingLevel lower upper k := by
  have hmul := mul_le_mul_of_nonneg_left (bombieriGiustiInvScale_le_one k)
    (sub_pos.mpr hlowerUpper).le
  unfold bombieriGiustiIncreasingLevel
  linarith

theorem bombieriGiustiIncreasingLevel_lt
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    bombieriGiustiIncreasingLevel lower upper k < upper := by
  unfold bombieriGiustiIncreasingLevel
  exact sub_lt_self upper
    (mul_pos (sub_pos.mpr hlowerUpper) (bombieriGiustiInvScale_pos k))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def bombieriGiustiSpatialCutoff
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (lower upper : ℝ) (k : ℕ) : SmoothScalar g :=
  spatialCutoffBetween rho
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))
    (bombieriGiustiDescendingLevel lower upper (2 * k))

omit [Module.Finite ℝ E] in
theorem bombieriGiustiSpatialCutoff_mono
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) (x : M) :
    (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
      (bombieriGiustiSpatialCutoff rho lower upper (k + 1)).toFun x ^ 2 := by
  let level := bombieriGiustiDescendingLevel lower upper
  have hlevel : StrictAnti level :=
    bombieriGiustiDescendingLevel_strictAnti hlowerUpper
  apply spatialCutoffBetween_sq_le_of_nested_levels rho
  · exact hlevel (by omega)
  · exact (hlevel (by omega)).le
  · exact hlevel (by omega)

omit [Module.Finite ℝ E] in
theorem bombieriGiustiSpatialCutoff_le_outer
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {outerLower outerUpper lower upper : ℝ}
    (houter : outerLower < outerUpper) (houterLower : outerUpper ≤ lower)
    (hlowerUpper : lower < upper) (k : ℕ) (x : M) :
    (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
      (spatialCutoffBetween rho outerLower outerUpper).toFun x ^ 2 := by
  apply spatialCutoffBetween_sq_le_of_nested_levels rho houter
  · exact houterLower.trans
      (bombieriGiustiDescendingLevel_gt hlowerUpper (2 * k + 1)).le
  · exact (bombieriGiustiDescendingLevel_strictAnti hlowerUpper (by omega))

omit [Module.Finite ℝ E] in
theorem bombieriGiustiSpatialCutoff_le_forward_inner
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k m : ℕ) (x : M) :
    (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
      (spatialCutoffBetween rho
        (moserCutoffLevelBetween
          (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
          (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) (2 * m))
        (moserCutoffLevelBetween
          (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
          (bombieriGiustiDescendingLevel lower upper (2 * k + 1))
          (2 * m + 1))).toFun x ^ 2 := by
  let level := bombieriGiustiDescendingLevel lower upper
  have hlevel : StrictAnti level :=
    bombieriGiustiDescendingLevel_strictAnti hlowerUpper
  have hlocal : level (2 * k + 2) < level (2 * k + 1) := hlevel (by omega)
  apply spatialCutoffBetween_sq_le_of_nested_levels rho
  · exact moserCutoffLevelBetween_strictMono hlocal (by omega)
  · exact (moserCutoffLevelBetween_lt hlocal (2 * m + 1)).le
  · exact hlevel (by omega)

omit [Module.Finite ℝ E] in
theorem forward_initial_spatialCutoffBetween_le_bombieriGiustiSpatialCutoff_succ
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) (x : M) :
    (spatialCutoffBetween rho
      (moserCutoffLevelBetween
        (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
        (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) 0)
      (moserCutoffLevelBetween
        (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
        (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) 1)).toFun x ^ 2 ≤
      (bombieriGiustiSpatialCutoff rho lower upper (k + 1)).toFun x ^ 2 := by
  let level := bombieriGiustiDescendingLevel lower upper
  have hlevel : StrictAnti level :=
    bombieriGiustiDescendingLevel_strictAnti hlowerUpper
  have hlocal : level (2 * k + 2) < level (2 * k + 1) := hlevel (by omega)
  apply spatialCutoffBetween_sq_le_of_nested_levels rho
  · exact hlevel (by omega)
  · simpa only [moserCutoffLevelBetween_zero] using le_rfl
  · exact moserCutoffLevelBetween_strictMono hlocal (by norm_num)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
