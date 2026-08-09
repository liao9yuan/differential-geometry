import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRungPack
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds

/-!
# The class-uniform ordered low-rung gate interface

The low-regularity energy chain already packages the exact ordered witnesses
for one metric as `IsLowGateOrd`.  This file records the stronger quantifier
order needed by uniform short-time existence: one pair of scalar envelopes is
chosen before every member of the bounded metric class.

No producer is asserted here.  In particular, per-metric choice through
`lowregGatePack` cannot prove this interface by commuting `forall` and
`exists`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The two scalar envelopes that dominate every fixed bottom rung and the
generic higher-rung coefficient over a metric class. -/
structure LowRegGateData where
  top : ℝ
  rad : ℝ

/-- One ordered gate pair works for every metric that is `Λ`-equivalent to the
fixed background and has background-covariant metric jets through order three
bounded by `Λ`.

This predicate exposes the exact `exists`-before-`forall` boundary of the
uniform-existence campaign. -/
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
