import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.TimeL2EigenProjection
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.SolutionSpace

/-!
# The spectral truncation commutes with the Duhamel family

The Galerkin projector `spatialEigenProj g σ N` keeps the eigenmodes below the
cut `eigenIdxFinset g N` and kills the rest; `timeL2EigenProj g σ T N` is its
pointwise action on `L²([0,T]; Hˢ)`.  The maximal-regularity machinery acts
*diagonally* on the same eigenbasis: `homModeCoeff` multiplies the `i`-th
coordinate by `e^{-λᵢ t}` and `solModeCoeff` convolves it against the same
kernel, both as a function of the mode `i` alone.  Two mode-diagonal operations
commute, so the solve of a truncated forcing is the truncation of the solve.

This is the commutation the projected (Galerkin) energy argument needs: the
projected trajectory is `V_N`-valued, so pairing it against the truncated
forcing is legitimate.

## Main results

* `spatialProj_idem` — the truncation is idempotent.
* `timeProj_modeCoeff` — the eigen-coordinates of a truncated time-`L²` field:
  kept below the cut, zero above it.
* `proj_solModeCoeff`, `proj_derivModeCoeff`, `proj_homModeCoeff` — the same
  for the three per-mode Duhamel coordinates.
* `proj_solField_comm`, `proj_derivField_comm`, `proj_homField_comm` — the
  truncation commutes with the maximal-regularity solution field, with its
  time-derivative field, and with the homogeneous-flow field.
* `proj_duhamel_comm`, `projDuhamel_zero` — the truncation commutes with the
  affine Duhamel field `maxRegDuhamelSolField` (general initial datum, and the
  zero-datum form used by the forcing fixed point).
* `proj_maxRegOp_deriv` — the map-level statement: the solution operator's
  time derivative commutes with the truncation (its trace is `0` either way).
* `projSol_mode_zero`, `projSol_fixed` — the projected solve is `V_N`-valued.

The mode-diagonality template is the one already used for the spectral
symmetrizer in `ShortTime/LowRegSymmPreserve.lean`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

variable (g : SmoothRiemannianMetric I M)

/-! ## The truncation in eigen-coordinates -/

open scoped Classical in
/-- The eigen-coordinates of a spectrally truncated tensor: the modes below the
cut survive unchanged, the modes above it are zero. -/
theorem spatialProj_coeff (σ : ℝ) (N : ℕ)
    (W : tensorHs (I := I) (M := M) g 0 2 σ)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    (spatialEigenProj (I := I) (M := M) g σ N W).coeff i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then W.coeff i else 0 := by
  rw [spatialEigenProj_apply, finiteEigenComboHs_coeff]

open scoped Classical in
/-- **The spectral truncation is idempotent**: keeping the modes below the cut
twice keeps them once.  This is what identifies a forcing produced by the
truncated nonlinearity as a fixed vector of the truncation. -/
theorem spatialProj_idem (σ : ℝ) (N : ℕ)
    (W : tensorHs (I := I) (M := M) g 0 2 σ) :
    spatialEigenProj (I := I) (M := M) g σ N
        (spatialEigenProj (I := I) (M := M) g σ N W) =
      spatialEigenProj (I := I) (M := M) g σ N W := by
  classical
  refine tensorHs.ext (funext fun i => ?_)
  simp only [spatialProj_coeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N <;> simp [hi]

/-- The spectral truncation is a `1`-Lipschitz map of `Hˢ`. -/
theorem spatialProj_lip (σ : ℝ) (N : ℕ) :
    LipschitzWith 1 (spatialEigenProj (I := I) (M := M) g σ N) := by
  refine LipschitzWith.of_dist_le_mul (fun W W' => ?_)
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact norm_spatialEigenProj_apply_le (I := I) (M := M) g σ N (W - W')

open scoped Classical in
/-- The eigen-coordinates of a truncated time-`L²` field. -/
theorem timeProj_modeCoeff (σ T : ℝ) (N : ℕ)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 σ) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    timeModeCoeff (I := I) (M := M)
        (timeL2EigenProj (I := I) (M := M) g σ T N f) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        timeModeCoeff (I := I) (M := M) f i else 0 := by
  classical
  have hL := timeModeCoeff_coeFn (I := I) (M := M)
    (timeL2EigenProj (I := I) (M := M) g σ T N f) i
  have hP : ⇑(timeL2EigenProj (I := I) (M := M) g σ T N f) =ᵐ[timeMeasure T]
      fun t => spatialEigenProj (I := I) (M := M) g σ N (f t) :=
    ContinuousLinearMap.coeFn_compLpL _ f
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, hP, timeModeCoeff_coeFn (I := I) (M := M) f i]
      with t h1 h2 h3
    rw [h1, h2, spatialProj_coeff, if_pos hi, h3]
  · rw [if_neg hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, hP, MeasureTheory.Lp.coeFn_zero ℝ 2 (timeMeasure T)]
      with t h1 h2 h3
    rw [h1, h2, spatialProj_coeff, if_neg hi, h3, Pi.zero_apply]

/-! ## Commutation with the per-mode Duhamel coordinates -/

open scoped Classical in
/-- The per-mode Duhamel coordinate of a truncated forcing. -/
theorem proj_solModeCoeff {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    solModeCoeff (I := I) (M := M) (a := a) hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        solModeCoeff (I := I) (M := M) (a := a) hT f i else 0 := by
  classical
  rw [solModeCoeff, timeProj_modeCoeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi, if_pos hi, solModeCoeff]
  · rw [if_neg hi, if_neg hi, map_zero]

open scoped Classical in
/-- The per-mode time-derivative coordinate of a truncated forcing. -/
theorem proj_derivModeCoeff {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    derivModeCoeff (I := I) (M := M) (a := a) hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        derivModeCoeff (I := I) (M := M) (a := a) hT f i else 0 := by
  classical
  rw [derivModeCoeff, timeProj_modeCoeff]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi, if_pos hi, derivModeCoeff]
  · rw [if_neg hi, if_neg hi, map_zero]

omit [BoundarylessManifold I M] in
private lemma homModeCoeFn {a T : ℝ}
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ⇑(homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i) =ᵐ[timeMeasure T]
      fun t => Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        u₀.coeff i :=
  coeFn_ofContinuousOn _

open scoped Classical in
/-- The homogeneous-flow coordinate of a truncated initial datum. -/
theorem proj_homModeCoeff {a T : ℝ} (N : ℕ)
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    homModeCoeff (I := I) (M := M) (a := a) (T := T)
        (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) i =
      if i ∈ eigenIdxFinset (I := I) (M := M) g N then
        homModeCoeff (I := I) (M := M) (a := a) (T := T) u₀ i else 0 := by
  classical
  have hL := homModeCoeFn (I := I) (M := M) (a := a) (T := T) g
    (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) i
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, homModeCoeFn (I := I) (M := M) (a := a) (T := T) g u₀ i]
      with t h1 h2
    rw [h1, h2, spatialProj_coeff, if_pos hi]
  · rw [if_neg hi]
    refine MeasureTheory.Lp.ext ?_
    filter_upwards [hL, MeasureTheory.Lp.coeFn_zero ℝ 2 (timeMeasure T)]
      with t h1 h2
    rw [h1, h2, spatialProj_coeff, if_neg hi, mul_zero, Pi.zero_apply]

/-! ## Commutation with the Duhamel fields -/

/-- **The truncation commutes with the maximal-regularity solution field.**
Solving the truncated forcing and truncating the solution agree; in particular
the projected solve gains the same two Sobolev derivatives. -/
theorem proj_solField_comm {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    maximalRegularitySolField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularitySolField (I := I) (M := M) a hT f) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maximalRegularitySolField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact (timeL2EigenProj (I := I) (M := M) g a T N f) i,
    proj_solModeCoeff (I := I) (M := M) g hT N f i,
    timeProj_modeCoeff (I := I) (M := M) g (a + 2) T N
      (maximalRegularitySolField (I := I) (M := M) a hT f) i,
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact f i]

/-- **The truncation commutes with the maximal-regularity derivative field.** -/
theorem proj_derivField_comm {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    maximalRegularityDerivField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g a T N
        (maximalRegularityDerivField (I := I) (M := M) a hT f) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maximalRegularityDerivField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact (timeL2EigenProj (I := I) (M := M) g a T N f) i,
    proj_derivModeCoeff (I := I) (M := M) g hT N f i,
    timeProj_modeCoeff (I := I) (M := M) g a T N
      (maximalRegularityDerivField (I := I) (M := M) a hT f) i,
    maximalRegularityDerivField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact f i]

/-- **The truncation commutes with the homogeneous heat-flow field.** -/
theorem proj_homField_comm {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2)) :
    maxRegHomogeneousSolField (I := I) (M := M) a T
        (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M) (a := a) (T := T)
      hT (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀) i,
    proj_homModeCoeff (I := I) (M := M) g N u₀ i,
    timeProj_modeCoeff (I := I) (M := M) g (a + 2) T N
      (maxRegHomogeneousSolField (I := I) (M := M) a T u₀) i,
    maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M) (a := a) (T := T)
      hT u₀ i]

/-- **The truncation commutes with the affine Duhamel field.**  The Duhamel
field of truncated data is the truncation of the Duhamel field. -/
theorem proj_duhamel_comm {a T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (u₀ : tensorHs (I := I) (M := M) g 0 2 (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    maxRegDuhamelSolField (I := I) (M := M) a hT hT1
        (spatialEigenProj (I := I) (M := M) g (a + 2) N u₀)
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1 u₀ f) := by
  rw [maxRegDuhamelSolField, maxRegDuhamelSolField, map_add,
    proj_homField_comm (I := I) (M := M) g hT.le N h_compact u₀,
    proj_solField_comm (I := I) (M := M) g hT.le N h_compact f]

/-- **The zero-datum Duhamel field of a truncated forcing is truncated.**  This
is the form consumed by the forcing fixed point, whose seed is `0`. -/
theorem projDuhamel_zero {a T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    maxRegDuhamelSolField (I := I) (M := M) a hT hT1
        (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2))
        (timeL2EigenProj (I := I) (M := M) g a T N f) =
      timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maxRegDuhamelSolField (I := I) (M := M) a hT hT1
          (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2)) f) := by
  have h := proj_duhamel_comm (I := I) (M := M) g hT hT1 N h_compact
    (0 : tensorHs (I := I) (M := M) g 0 2 (a + 2)) f
  rwa [map_zero] at h

/-- **The map-level commutation.**  The `L²` time derivative of the solution
operator commutes with the truncation; its initial trace is `0` for either
forcing, so this is the whole content at the level of `maximalRegularityOp`. -/
theorem proj_maxRegOp_deriv {a T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    timeH1.timeDeriv _ T
        (maximalRegularityOp (I := I) (M := M) a hT hT1
          (timeL2EigenProj (I := I) (M := M) g a T N f)) =
      timeL2EigenProj (I := I) (M := M) g a T N
        (timeH1.timeDeriv _ T
          (maximalRegularityOp (I := I) (M := M) a hT hT1 f)) := by
  rw [maximalRegularityOp_timeDeriv, maximalRegularityOp_timeDeriv,
    proj_derivField_comm (I := I) (M := M) g hT.le N h_compact f]

/-! ## The projected solve is `V_N`-valued -/

/-- **The projected solve has no mass above the cut.**  Its eigen-coordinates
vanish outside `eigenIdxFinset g N`, so it takes values in the Galerkin space
`V_N` — the fact the projected energy identity consumes. -/
theorem projSol_mode_zero {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T)
    {i : TensorEigenIdx (I := I) (M := M) g 0 2}
    (hi : i ∉ eigenIdxFinset (I := I) (M := M) g N) :
    timeModeCoeff (I := I) (M := M)
      (maximalRegularitySolField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f)) i = 0 := by
  rw [maximalRegularitySolField_timeModeCoeff (I := I) (M := M) (a := a) hT
      h_compact (timeL2EigenProj (I := I) (M := M) g a T N f) i,
    proj_solModeCoeff (I := I) (M := M) g hT N f i, if_neg hi]

/-- **The projected solve is fixed by the truncation**, the operator form of
`projSol_mode_zero`: the solve of a truncated forcing lies in the range of the
truncation at the gained regularity `H^{a+2}`. -/
theorem projSol_fixed {a T : ℝ} (hT : 0 ≤ T) (N : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g 0 2 a) T) :
    timeL2EigenProj (I := I) (M := M) g (a + 2) T N
        (maximalRegularitySolField (I := I) (M := M) a hT
          (timeL2EigenProj (I := I) (M := M) g a T N f)) =
      maximalRegularitySolField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f) := by
  classical
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [timeProj_modeCoeff (I := I) (M := M) g (a + 2) T N
      (maximalRegularitySolField (I := I) (M := M) a hT
        (timeL2EigenProj (I := I) (M := M) g a T N f)) i]
  by_cases hi : i ∈ eigenIdxFinset (I := I) (M := M) g N
  · rw [if_pos hi]
  · rw [if_neg hi,
      projSol_mode_zero (I := I) (M := M) g hT N h_compact f hi]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
