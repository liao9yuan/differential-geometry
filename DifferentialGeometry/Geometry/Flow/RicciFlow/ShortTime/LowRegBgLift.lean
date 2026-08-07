import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.UnifBgLift
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegBgTime

/-!
# Metricwise coefficient certificate for the fixed-background lift

The scalar data in `BgLiftData` is chosen before the class metric varies.  This
module keeps the subsequently constructed A1 maps separate from their proof
certificate and records exactly the durable facts consumed by the adjacent-
scale realization.
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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The two completed first-order maps constructed after the class metric is
known.  Proofs of continuity, core agreement, bounds, and compatibility live
in `IsBgLiftAt`. -/
structure BgLiftOps (g : SmoothRiemannianMetric I M) where
  a1Hi : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
    (tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
  a1Lo : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →
    (tensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
      tensorHs (I := I) (M := M) g 0 2 (1 : ℝ))

namespace BgLiftData

/-- Restrict the low-bound realization certificate to the coefficient radius
stored in the class-first lift data. -/
theorem realize
    {g gB : SmoothRiemannianMetric I M}
    {K : LowRegBoundData} (D : BgLiftData K)
    (hK : IsLowBoundsAt (I := I) (M := M) g gB K)
    (S : SmoothCcTensor g 0 2)
    (hS : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤
      D.coeffRadius) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g S) K.threshold := by
  apply hK.hreal S
  rw [show (((1 : ℕ) : ℝ) + 1) = 2 by norm_num]
  have heq :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S =
        smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) S :=
    tensorHs.ext (funext fun _ => rfl)
  rw [← heq]
  exact hS.trans D.coeffRadius_le_realize

end BgLiftData

/-- Metricwise coefficient certificate at the scalar bounds fixed by
`BgLiftData`.

The A2 maps are the canonical completed maps `lowA2HiBg` and `lowA2LoBg`.
The A1 maps are explicit data because their class-first construction remains a
separate producer.  Both core identities use the actual fixed-background
bundle `lowCoreDataBg`; no self-background refold identity is assumed. -/
structure IsBgLiftAt
    (g gB : SmoothRiemannianMetric I M)
    (K : LowRegBoundData)
    (hK : IsLowBoundsAt (I := I) (M := M) g gB K)
    (D : BgLiftData K) (F : BgLiftOps (I := I) (M := M) g) : Prop where
  a2Hi_cont : Continuous
    (lowA2HiBg (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK))
  a2Lo_cont : Continuous
    (lowA2LoBg (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK))
  a2Hi_bound : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
    ‖lowA2HiBg (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v‖ ≤ D.contract
  a2Lo_bound : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
    ‖lowA2LoBg (I := I) (M := M) g gB D.coeffRadius_pos.le
      hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v‖ ≤ D.contract
  a2Hi_core : ∀ S : SmoothCcTensor g 0 2,
    lowA2HiBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK)
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
      (lowCoreDataBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).a2Hi
          (I := I) (M := M)
  a2Lo_core : ∀ S : SmoothCcTensor g 0 2,
    lowA2LoBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK)
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
      (lowCoreDataBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).a2Lo
          (I := I) (M := M)
  a2_square : ∀ v : tensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ 2 by norm_num)).comp
        (lowA2HiBg (I := I) (M := M) g gB D.coeffRadius_pos.le
          hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v) =
      (lowA2LoBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) v).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (show (3 : ℝ) ≤ 4 by norm_num))
  a1Hi_cont : Continuous F.a1Hi
  a1Lo_cont : Continuous F.a1Lo
  a1Hi_bound : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
    ‖F.a1Hi x‖ ≤ D.zero + D.slope * ‖x‖
  a1Lo_bound : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
    ‖F.a1Lo x‖ ≤ D.zero + D.slope * ‖x‖
  a1Hi_core : ∀ S : SmoothCcTensor g 0 2,
    F.a1Hi (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
      (lowCoreDataBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).a1Hi
          (I := I) (M := M)
  a1Lo_core : ∀ S : SmoothCcTensor g 0 2,
    F.a1Lo (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) S) =
      (lowCoreDataBg (I := I) (M := M) g gB D.coeffRadius_pos.le
        hK.threshold_nonneg hK.threshold_le_third (D.realize hK) S).a1Lo
          (I := I) (M := M)
  a1_square : ∀ x : tensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
      (show (1 : ℝ) ≤ 2 by norm_num)).comp (F.a1Hi x) =
      (F.a1Lo x).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ 3 by norm_num))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
