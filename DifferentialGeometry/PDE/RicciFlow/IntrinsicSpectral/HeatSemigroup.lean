import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.Eigenbasis
import DifferentialGeometry.Integral.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.AbstractSemigroup
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingHs

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The intrinsic tensor heat semigroup `S t = e^{-t Δ_∇}` for time `t : ℝ`,
defined predicate-free (no `HasLocallyConstantChartAt` hypothesis), as a
continuous linear operator on the `L²` Hilbert space `TensorL2 r s g`.

For `t ≥ 0` it is the spectral series `Σ_n e^{-t λ_n} ⟨·, eigfun n⟩ eigfun n`
arising from the predicate-free eigenbasis of the connection Laplacian
(intrinsic-spectral-eigenbasis, α.4). For `t < 0` it is the zero operator. -/
noncomputable def tensor_heat_semigroup_predicate_free
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g := sorry

/-- The intrinsic tensor heat semigroup packaged as a bounded strongly
continuous one-parameter contraction semigroup on the `L²` Hilbert space
`TensorL2 r s g`, predicate-free (no `HasLocallyConstantChartAt`). -/
noncomputable def tensor_heat_semigroup_package_boundedC0
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    BoundedC0Semigroup (TensorL2 r s g) := sorry

/-- **Parabolic smoothing.** For initial datum `u₀ ∈ TensorL2 r s g` and any
strictly positive time `t > 0`, the heat-semigroup image
`tensor_heat_semigroup_predicate_free g r s t u₀` has a smooth compactly-
supported representative in `SmoothCcTensor g r s`: it lies in the image of
the canonical inclusion `SmoothCcTensor g r s → TensorL2 r s g`. This is
the parabolic-smoothing statement underlying the lift of the maxReg
solution to a `SmoothRiemannianMetric I M`-valued family. -/
theorem parabolic_smoothing_ensures_Cinf_on_positive_t
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (u₀ : TensorL2 r s g)
    {t : ℝ} (ht : 0 < t) :
    ∃ S : SmoothCcTensor g r s,
      (S : TensorL2 r s g) =
        tensor_heat_semigroup_predicate_free g r s t u₀ := sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
