import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.EnergyLadderData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.AllTimesBounds

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

structure LowRegGateData where
  top : ℝ
  rad : ℝ

structure IsLowGateUnif
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ)
    (K : LowRegGateData) : Prop where
  top_nonneg : 0 ≤ K.top
  rad_nonneg : 0 ≤ K.rad
  gate : ∀ g : SmoothRiemannianMetric I M,
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    IsLowGateOrd (I := I) (M := M) g K.top K.rad

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
