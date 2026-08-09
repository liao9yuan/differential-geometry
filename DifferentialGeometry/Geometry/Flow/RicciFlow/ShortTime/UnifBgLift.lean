import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifClassBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegLiftSmall

/-!
# Class-first scalar data for the fixed-background adjacent-scale lift

This module records only the numerical data that must be chosen before the
initial metric varies.  Coefficient maps and orbit certificates belong to
separate metricwise packages.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- Scalar data for one class-first adjacent-scale lift.

`coeffRadius` is the common radius on which the completed coefficient maps are
valid.  `contract`, `zero`, and `slope` are their common A2 contraction and A1
affine constants.  `forceCap` is definitionally tied to the force estimate
exported by `IsLowSolveBg`; the margin therefore uses the actual solver bound,
not the unrelated realization radius. -/
structure BgLiftData (K : LowRegBoundData) where
  coeffRadius : ℝ
  contract : ℝ
  zero : ℝ
  slope : ℝ
  forceCap : ℝ
  coeffRadius_pos : 0 < coeffRadius
  contract_nonneg : 0 ≤ contract
  contract_lt_one : contract < 1
  zero_nonneg : 0 ≤ zero
  slope_nonneg : 0 ≤ slope
  forceCap_nonneg : 0 ≤ forceCap
  forceCap_eq :
    forceCap = lowregStateRad K.top K.slope K.outer K.realize / 4
  state_le_radius :
    lowregStateRad K.top K.slope K.outer K.realize ≤ coeffRadius
  coeffRadius_le_realize : coeffRadius ≤ K.realize
  force_margin :
    6 * (2 * slope * forceCap) ≤ (1 - contract) / 2

namespace BgLiftData

/-- The closed adjacent-scale horizon selected by the class-first lift data. -/
def horizon {K : LowRegBoundData} (D : BgLiftData K) : ℝ :=
  lowregLiftHorizon' D.contract D.zero

/-- The class-first adjacent-scale horizon is positive. -/
theorem horizon_pos {K : LowRegBoundData} (D : BgLiftData K) :
    0 < D.horizon :=
  lowregLiftHorizon'_pos D.contract_nonneg D.contract_lt_one D.zero_nonneg

/-- The class-first adjacent-scale horizon is at most one. -/
theorem horizon_le_one {K : LowRegBoundData} (D : BgLiftData K) :
    D.horizon ≤ 1 :=
  lowregLiftHorizon'_le_one

/-- The low-solve and adjacent-scale horizons, both fixed before the class
metric varies. -/
def commonHorizon (K : LowRegBoundData) (D : BgLiftData K) : ℝ :=
  min (lowregHorizon K.top K.base K.slope K.zeroBd K.outer K.realize) D.horizon

/-- The common low/lift horizon is positive. -/
theorem commonHorizon_pos (K : LowRegBoundData) (D : BgLiftData K) :
    0 < D.commonHorizon K := by
  exact lt_min
    (lowregHorizon_pos K.top_nonneg K.base_nonneg K.slope_nonneg
      K.zero_nonneg K.outer_pos K.realize_pos)
    D.horizon_pos

/-- The common low/lift horizon is at most one. -/
theorem commonHorizon_le_one (K : LowRegBoundData) (D : BgLiftData K) :
    D.commonHorizon K ≤ 1 :=
  (min_le_left _ _).trans lowregHorizon_le_one

/-- The common horizon lies below the class-first low-solve horizon. -/
theorem commonHorizon_le_low (K : LowRegBoundData) (D : BgLiftData K) :
    D.commonHorizon K ≤
      lowregHorizon K.top K.base K.slope K.zeroBd K.outer K.realize :=
  min_le_left _ _

/-- The common horizon lies below the adjacent-scale lift horizon. -/
theorem commonHorizon_le_lift (K : LowRegBoundData) (D : BgLiftData K) :
    D.commonHorizon K ≤ D.horizon :=
  min_le_right _ _

end BgLiftData

/-- The force produced by a background low solve obeys the cap stored in the
class-first lift data. -/
theorem IsLowSolveBg.force_le_cap
    {g₀ g_bg : SmoothRiemannianMetric I M}
    {K : LowRegBoundData} {hK : IsLowBoundsAt (I := I) (M := M) g₀ g_bg K}
    {T : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
    {u : MaxRegSolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T}
    {gforce : timeL2
      (tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (hsol : IsLowSolveBg (I := I) (M := M)
      g₀ g_bg K hK hT hT1 u gforce)
    (D : BgLiftData K) :
    ‖gforce‖ ≤ D.forceCap := by
  rw [D.forceCap_eq]
  exact hsol.force_bound

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
