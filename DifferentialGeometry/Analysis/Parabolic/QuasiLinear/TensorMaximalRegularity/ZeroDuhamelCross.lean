import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzExistence

/-!
# Zero-initial Duhamel fields at the intermediate scale

This file packages the zero-initial maximal-regularity Duhamel solution as a
cross-scale field.  Its produced intermediate representative is measurable,
linear in the forcing almost everywhere, and uniformly bounded in time by the
forcing norm.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a T : ℝ}

/-- The zero-initial Duhamel solution as a cross-scale field. -/
def zeroDuhamelCross (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    CrossScaleField (I := I) (M := M) g r s a T :=
  maxRegRecentredCrossScaleField (I := I) (M := M)
    (h_compact := h_compact) hT hT1 0 f

/-- The produced intermediate representative has zero initial value. -/
theorem zeroRepr_zero (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (zeroDuhamelCross (I := I) (M := M) hT hT1 h_compact f).repr 0 =
      (0 : tensorHs (I := I) (M := M) g r s (a + 1)) := by
  simpa only [zeroDuhamelCross] using
    recentred_repr_zero (I := I) (M := M)
      (h_compact := h_compact) hT hT1
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) f

/-- The intermediate representative agrees almost everywhere with the
zero-initial `H^(a+1)` Duhamel companion field. -/
theorem zeroRepr_ae (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (fun t => (zeroDuhamelCross (I := I) (M := M)
        hT hT1 h_compact f).repr t) =ᵐ[timeMeasure T]
      fun t => maxRegDuhamelSolFieldHa1 (I := I) (M := M)
        a hT hT1 0 f t := by
  simpa only [zeroDuhamelCross, map_zero, sub_zero] using
    recentred_repr_eq_field_sub (I := I) (M := M)
      (h_compact := h_compact) hT hT1
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) f

/-- The produced representative is strongly measurable for the restricted
time measure. -/
theorem zeroRepr_meas (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    AEStronglyMeasurable
      (fun t => (zeroDuhamelCross (I := I) (M := M)
        hT hT1 h_compact f).repr t)
      (timeMeasure T) := by
  exact (Lp.aestronglyMeasurable
    (maxRegDuhamelSolFieldHa1 (I := I) (M := M)
      a hT hT1 (0 : tensorHs (I := I) (M := M) g r s (a + 2)) f)).congr
        (zeroRepr_ae (I := I) (M := M) hT hT1 h_compact f).symm

private theorem homMode_zero (hT : 0 < T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i = 0 := by
  have hsq := norm_homModeCoeff_sq_le (I := I) (M := M)
    (a := a) (T := T) hT.le
    (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i
  rw [tensorHs.zero_coeff] at hsq
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg
    (homModeCoeff (I := I) (M := M) (a := a) (T := T)
      (0 : tensorHs (I := I) (M := M) g r s (a + 2)) i)]

private theorem homField_zero (hT : 0 < T)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s)) :
    maxRegHomogeneousSolFieldHa1 (I := I) (M := M) a T
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) = 0 := by
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M)
    (a := a) (T := T) hT.le, homMode_zero (I := I) (M := M) hT i]
  simp only [timeModeCoeff, map_zero]

private theorem duhField_sub (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 0 f -
        maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 0 f' =
      maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 0 (f - f') := by
  rw [maxRegDuhamelSolFieldHa1_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1]
  rw [maxRegDuhamelSolFieldHa1,
    homField_zero (I := I) (M := M) (a := a) hT h_compact, zero_add]

/-- The zero-initial intermediate representative commutes almost everywhere
with subtraction of forcing terms. -/
theorem zeroRepr_sub_ae (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f f' : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    (fun t =>
      (zeroDuhamelCross (I := I) (M := M) hT hT1 h_compact f).repr t -
        (zeroDuhamelCross (I := I) (M := M) hT hT1 h_compact f').repr t)
      =ᵐ[timeMeasure T]
    fun t =>
      (zeroDuhamelCross (I := I) (M := M)
        hT hT1 h_compact (f - f')).repr t := by
  have hf := zeroRepr_ae (I := I) (M := M) hT hT1 h_compact f
  have hf' := zeroRepr_ae (I := I) (M := M) hT hT1 h_compact f'
  have hd := zeroRepr_ae (I := I) (M := M) hT hT1 h_compact (f - f')
  have hsub := Lp.coeFn_sub
    (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 0 f)
    (maxRegDuhamelSolFieldHa1 (I := I) (M := M) a hT hT1 0 f')
  rw [duhField_sub (I := I) (M := M)
    (h_compact := h_compact) (a := a) hT hT1 f f'] at hsub
  filter_upwards [hf, hf', hd, hsub] with t hft hf't hdt hst
  rw [hft, hf't, hdt]
  exact hst.symm

/-- Uniform-in-time control of the zero-initial intermediate representative.
The constant remains bounded as the horizon tends to zero. -/
theorem zeroRepr_norm_le (hT : 0 < T) (hT1 : T ≤ 1)
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖(zeroDuhamelCross (I := I) (M := M)
        hT hT1 h_compact f).repr t‖ ≤
      2 * Real.sqrt (1 + T) * ‖f‖ := by
  set u := zeroDuhamelCross (I := I) (M := M)
    hT hT1 h_compact f with hu
  have hsq := u.repr_sq_le_norms hT ht
  have hzero : u.repr 0 =
      (0 : tensorHs (I := I) (M := M) g r s (a + 1)) := by
    simpa only [hu] using
      zeroRepr_zero (I := I) (M := M) hT hT1 h_compact f
  rw [hzero, norm_zero, zero_pow (by norm_num), zero_add] at hsq
  have hhi : ‖u.hiL2‖ ≤ (1 + T) * ‖f‖ := by
    simpa only [hu, zeroDuhamelCross, norm_zero, mul_zero, zero_add] using
      recentredHi_norm_le (I := I) (M := M)
        (h_compact := h_compact) hT hT1
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) f
  have hderiv : ‖u.lo.deriv‖ ≤ 2 * ‖f‖ := by
    simpa only [hu, zeroDuhamelCross, recentredCarrier,
      TimeSobolev.timeH1.deriv_mk, norm_zero, mul_zero, zero_add] using
      recentredCarrier_deriv_norm_le (I := I) (M := M)
        (h_compact := h_compact) hT hT1
        (0 : tensorHs (I := I) (M := M) g r s (a + 2)) f
  have hmul :
      ‖u.hiL2‖ * ‖u.lo.deriv‖ ≤
        ((1 + T) * ‖f‖) * (2 * ‖f‖) :=
    mul_le_mul hhi hderiv (norm_nonneg _) (by positivity)
  have hsq' :
      ‖u.repr t‖ ^ 2 ≤ 4 * (1 + T) * ‖f‖ ^ 2 := by
    nlinarith [hsq, hmul]
  have hbase : 0 ≤ 1 + T := by linarith
  have hrhs : 0 ≤ 2 * Real.sqrt (1 + T) * ‖f‖ := by positivity
  refine (sq_le_sq₀ (norm_nonneg _) hrhs).1 ?_
  calc
    ‖u.repr t‖ ^ 2 ≤ 4 * (1 + T) * ‖f‖ ^ 2 := hsq'
    _ = (2 * Real.sqrt (1 + T) * ‖f‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hbase]
      ring

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
