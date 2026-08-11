import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifLow1PathPair
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private lemma two_mul_le_eps {eta x y : ℝ} (heta : 0 < eta) :
    2 * x * y ≤ eta * x ^ 2 + eta⁻¹ * y ^ 2 := by
  have hinv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
  have hs := mul_nonneg hinv (sq_nonneg (eta * x - y))
  have hexpand :
      eta⁻¹ * (eta * x - y) ^ 2 =
        eta * x ^ 2 - 2 * x * y + eta⁻¹ * y ^ 2 := by
    field_simp [ne_of_gt heta]
    ring
  rw [hexpand] at hs
  linarith

theorem carrier_pair_abs_of_h2
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2)
    {eta C D R : ℝ}
    (heta : 0 < eta) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R)
    (hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) +
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖)) :
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        ((eta / 2)⁻¹ * (D ^ 2 + (D + C) ^ 2)) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
        2 * C * R ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let e : ℝ := eta / 2
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let L2T : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let LY : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 Y
  have hx : 0 ≤ x := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hxR : x ≤ R := by simpa only [x] using hT2
  have hx1 : x ≤ 1 := hxR.trans hR1
  have hxy : x ≤ y := by
    let S3 := ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T
    have hinc := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num) S3
    have heq :
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ 3 by norm_num) S3 =
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
      ext i
      simp only [S3, tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
    simpa only [x, y, S3, heq] using hinc
  have hinterp : y ^ 2 ≤ x * z := by
    exact prodOfParam hx hz (fun t ht => by
      simpa only [x, y, z] using
        specInterp3 (I := I) (M := M) g 2 T ht)
  have hL2T : ‖L2T‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 L2T‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hLY : ‖LY‖ =
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 1 Y
    change ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) Y‖ =
      ‖SmoothCcTensor.toL2 LY‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [norm_ccHs_eq_smoothHs] using heven.symm
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        ‖L2T‖ * ‖LY‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L2T LY]
    exact abs_real_inner_le_norm L2T LY
  have hY' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * x + (D + C) * x * y + C * x * y ^ 2 := by
    simpa only [x, y] using hY.trans_eq (by ring)
  have hfirst : 2 * z * (D * x) ≤
      e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
    have hsq := pow_le_pow_left₀ hx hxy 2
    have hprod : (D * x) ^ 2 ≤ D ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hsq)
      nlinarith
    calc
      2 * z * (D * x) ≤ e * z ^ 2 + e⁻¹ * (D * x) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr he.le))
  have hsecond : 2 * z * ((D + C) * x * y) ≤
      e * z ^ 2 + e⁻¹ * (D + C) ^ 2 * y ^ 2 := by
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hcore : ((D + C) * x * y) ^ 2 ≤
        (D + C) ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg
        (mul_nonneg (sq_nonneg (D + C)) (sq_nonneg y))
        (sub_nonneg.mpr hx2)
      nlinarith
    calc
      2 * z * ((D + C) * x * y) ≤
          e * z ^ 2 + e⁻¹ * ((D + C) * x * y) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * (D + C) ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hcore (inv_nonneg.mpr he.le))
  have hthird : 2 * z * (C * x * y ^ 2) ≤
      2 * C * R ^ 2 * z ^ 2 := by
    have hxy2 : x * y ^ 2 ≤ R ^ 2 * z := by
      calc
        x * y ^ 2 ≤ x * (x * z) :=
          mul_le_mul_of_nonneg_left hinterp hx
        _ ≤ R ^ 2 * z := by
          have hx2 : x ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hx hxR 2
          nlinarith
    nlinarith [mul_nonneg hC hz, mul_nonneg hR hR]
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤ _
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        2 * (z * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖) := by
      rw [← hL2T, ← hLY]
      exact mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ ≤ 2 * z * (D * x + (D + C) * x * y + C * x * y ^ 2) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hY' (mul_nonneg (by norm_num) hz)
    _ = 2 * z * (D * x) + 2 * z * ((D + C) * x * y) +
          2 * z * (C * x * y ^ 2) := by ring
    _ ≤ (e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2) +
          (e * z ^ 2 + e⁻¹ * (D + C) ^ 2 * y ^ 2) +
          2 * C * R ^ 2 * z ^ 2 := by
      exact add_le_add (add_le_add hfirst hsecond) hthird
    _ = eta * z ^ 2 +
          (eta / 2)⁻¹ * (D ^ 2 + (D + C) ^ 2) * y ^ 2 +
          2 * C * R ^ 2 * z ^ 2 := by
      dsimp only [e]
      ring

theorem carrier_pair_abs_of_affine_h2
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2)
    {eta C D R : ℝ}
    (heta : 0 < eta) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R)
    (hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) +
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖)) :
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        ((eta / 2)⁻¹ * (D ^ 2 + 2 * (D ^ 2 + C ^ 2))) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
        2 * C * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let e : ℝ := eta / 2
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let L2T : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let LY : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 Y
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hxR : x ≤ R := by simpa only [x] using hT2
  have hx1 : x ≤ 1 := hxR.trans hR1
  have hxy : x ≤ y := by
    let S3 := ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T
    have hinc := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num) S3
    have heq :
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ 3 by norm_num) S3 =
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
      ext i
      simp only [S3, tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
    simpa only [x, y, S3, heq] using hinc
  have hinterp : y ^ 2 ≤ x * z := by
    exact prodOfParam hx hz (fun t ht => by
      simpa only [x, y, z] using
        specInterp3 (I := I) (M := M) g 2 T ht)
  have hL2T : ‖L2T‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 L2T‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hLY : ‖LY‖ =
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 1 Y
    change ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) Y‖ =
      ‖SmoothCcTensor.toL2 LY‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [norm_ccHs_eq_smoothHs] using heven.symm
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        ‖L2T‖ * ‖LY‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L2T LY]
    exact abs_real_inner_le_norm L2T LY
  have hY' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * x + (D * x + C) * y + C * y ^ 2 := by
    simpa only [x, y] using hY.trans_eq (by ring)
  have hfirst : 2 * z * (D * x) ≤
      e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
    have hsq := pow_le_pow_left₀ hx hxy 2
    have hprod : (D * x) ^ 2 ≤ D ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hsq)
      nlinarith
    calc
      2 * z * (D * x) ≤ e * z ^ 2 + e⁻¹ * (D * x) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr he.le))
  have hsecond : 2 * z * ((D * x + C) * y) ≤
      e * z ^ 2 + e⁻¹ * (2 * (D ^ 2 + C ^ 2)) * y ^ 2 := by
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hcoef : (D * x + C) ^ 2 ≤ 2 * (D ^ 2 + C ^ 2) := by
      nlinarith [sq_nonneg (D * x - C),
        mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hx2)]
    have hcore : ((D * x + C) * y) ^ 2 ≤
        2 * (D ^ 2 + C ^ 2) * y ^ 2 := by
      calc
        ((D * x + C) * y) ^ 2 = (D * x + C) ^ 2 * y ^ 2 := by ring
        _ ≤ 2 * (D ^ 2 + C ^ 2) * y ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg y)
    calc
      2 * z * ((D * x + C) * y) ≤
          e * z ^ 2 + e⁻¹ * ((D * x + C) * y) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * (2 * (D ^ 2 + C ^ 2)) * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hcore (inv_nonneg.mpr he.le))
  have hthird : 2 * z * (C * y ^ 2) ≤
      2 * C * R * z ^ 2 := by
    have hy2 : y ^ 2 ≤ R * z := hinterp.trans (by
      exact mul_le_mul_of_nonneg_right hxR hz)
    nlinarith [mul_nonneg hC hz, mul_nonneg hR hz]
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤ _
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        2 * (z * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖) := by
      rw [← hL2T, ← hLY]
      exact mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ ≤ 2 * z * (D * x + (D * x + C) * y + C * y ^ 2) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hY' (mul_nonneg (by norm_num) hz)
    _ = 2 * z * (D * x) + 2 * z * ((D * x + C) * y) +
          2 * z * (C * y ^ 2) := by ring
    _ ≤ (e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2) +
          (e * z ^ 2 + e⁻¹ * (2 * (D ^ 2 + C ^ 2)) * y ^ 2) +
          2 * C * R * z ^ 2 := by
      exact add_le_add (add_le_add hfirst hsecond) hthird
    _ = eta * z ^ 2 +
          (eta / 2)⁻¹ * (D ^ 2 + 2 * (D ^ 2 + C ^ 2)) * y ^ 2 +
          2 * C * R * z ^ 2 := by
      dsimp only [e]
      ring

theorem carrier_pair_abs_of_linear_quadratic_h2
    (g : SmoothRiemannianMetric I M)
    (T Y : SmoothCcTensor g 0 2)
    {eta C D E R : ℝ}
    (heta : 0 < eta) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R)
    (hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ *
            (1 + ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) +
          E * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ +
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2) :
    2 * |tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmooth (I := I) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T)).toFun
        (oneMinusConnLapSmooth (I := I) g 0 2 Y).toFun| ≤
      eta * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
        ((eta / 3)⁻¹ * (2 * D ^ 2 + E ^ 2)) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 +
        2 * C * R *
          ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 := by
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  let e : ℝ := eta / 3
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let L2T : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let LY : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 Y
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hz : 0 ≤ z := norm_nonneg _
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hxR : x ≤ R := by simpa only [x] using hT2
  have hx1 : x ≤ 1 := hxR.trans hR1
  have hxy : x ≤ y := by
    let S3 := ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T
    have hinc := tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num) S3
    have heq :
        tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ 3 by norm_num) S3 =
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
      ext i
      simp only [S3, tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]
    simpa only [x, y, S3, heq] using hinc
  have hinterp : y ^ 2 ≤ x * z := by
    exact prodOfParam hx hz (fun t ht => by
      simpa only [x, y, z] using
        specInterp3 (I := I) (M := M) g 2 T ht)
  have hL2T : ‖L2T‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 L2T‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hLY : ‖LY‖ =
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 1 Y
    change ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) Y‖ =
      ‖SmoothCcTensor.toL2 LY‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [norm_ccHs_eq_smoothHs] using heven.symm
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        ‖L2T‖ * ‖LY‖ := by
    rw [← SmoothCcTensor.inner_def (I := I) (M := M) L2T LY]
    exact abs_real_inner_le_norm L2T LY
  have hY' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        D * x + D * x * y + E * y + C * y ^ 2 := by
    simpa only [x, y] using hY.trans_eq (by ring)
  have hfirst : 2 * z * (D * x) ≤
      e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
    have hsq := pow_le_pow_left₀ hx hxy 2
    have hprod : (D * x) ^ 2 ≤ D ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hsq)
      nlinarith
    calc
      2 * z * (D * x) ≤ e * z ^ 2 + e⁻¹ * (D * x) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr he.le))
  have hsecond : 2 * z * (D * x * y) ≤
      e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hprod : (D * x * y) ^ 2 ≤ D ^ 2 * y ^ 2 := by
      have hfac := mul_nonneg (mul_nonneg (sq_nonneg D) (sq_nonneg y))
        (sub_nonneg.mpr hx2)
      nlinarith
    calc
      2 * z * (D * x * y) ≤ e * z ^ 2 + e⁻¹ * (D * x * y) ^ 2 :=
        two_mul_le_eps he
      _ ≤ e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2 := by
        simpa only [mul_assoc] using add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr he.le))
  have hthird : 2 * z * (E * y) ≤
      e * z ^ 2 + e⁻¹ * E ^ 2 * y ^ 2 := by
    simpa only [mul_pow, mul_assoc] using
      two_mul_le_eps (x := z) (y := E * y) he
  have hfourth : 2 * z * (C * y ^ 2) ≤
      2 * C * R * z ^ 2 := by
    have hy2 : y ^ 2 ≤ R * z := hinterp.trans
      (mul_le_mul_of_nonneg_right hxR hz)
    nlinarith [mul_nonneg hC hz, mul_nonneg hR hz]
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤ _
  calc
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 L2T.toFun LY.toFun| ≤
        2 * (z * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖) := by
      rw [← hL2T, ← hLY]
      exact mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ ≤ 2 * z * (D * x + D * x * y + E * y + C * y ^ 2) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hY' (mul_nonneg (by norm_num) hz)
    _ = 2 * z * (D * x) + 2 * z * (D * x * y) +
          2 * z * (E * y) + 2 * z * (C * y ^ 2) := by ring
    _ ≤ (e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2) +
          (e * z ^ 2 + e⁻¹ * D ^ 2 * y ^ 2) +
          (e * z ^ 2 + e⁻¹ * E ^ 2 * y ^ 2) +
          2 * C * R * z ^ 2 := by
      exact add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
    _ = eta * z ^ 2 + (eta / 3)⁻¹ * (2 * D ^ 2 + E ^ 2) * y ^ 2 +
          2 * C * R * z ^ 2 := by
      dsimp only [e]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
