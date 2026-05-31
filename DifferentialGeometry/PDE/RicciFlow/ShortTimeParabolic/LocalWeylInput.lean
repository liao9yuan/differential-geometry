/-
The single isolated open analytic input of the Ricci-flow short-time-existence
development: the classical local Weyl law (polynomial eigenvalue-counting bound)
for the intrinsic tensor Laplacian on a closed manifold.

Every other lemma in the short-time-existence proof is proven outright; this file
holds the one deferred classical theorem. Granting it, the clean reduction chain
`EigenvalueCountingBound ⟹ EigenvalueTailSummable ⟹ SpectralChartRegularity ⟹
SpectralSmoothRealizesAsSmooth` (all proven in `SpectralWeylCounting.lean`)
supplies the spectral smooth-representative gate, which is the only obstacle to a
fully axiom-clean headline.
-/
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.SpectralWeylCounting

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **THE single deferred classical input** — the local Weyl law for the intrinsic
tensor Laplacian on a closed manifold: the eigenvalue-counting function
`N(Λ) = #{i : 1 + λᵢ < Λ}` grows at most polynomially in `Λ`. This is a classical
theorem (heat-kernel parametrix / Karamata Tauberian on the heat trace) not present
in Mathlib; it is the ONLY `sorry` on the short-time-existence dependency graph that
is not discharged. Every consumer (smooth-representative gate, eigenvalue-tail
summability) reduces to this one statement via the proven chain in
`SpectralWeylCounting.lean`. -/
theorem local_weyl_eigenvalue_counting_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    EigenvalueCountingBound (I := I) (M := M) g r s := sorry

end DifferentialGeometry.PDE.RicciFlow
