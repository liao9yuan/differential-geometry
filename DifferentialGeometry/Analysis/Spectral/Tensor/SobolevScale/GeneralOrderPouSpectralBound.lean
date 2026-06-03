import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Order2Equivalence
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

/-!
# General-order intrinsic-Sobolev control by the spectral Sobolev norm

For a closed Riemannian manifold `(M, g₀)` and a smooth compactly-supported
`(0, 2)`-tensor section `T`, the intrinsic order-`2k` Sobolev norm
`‖T.toHs (2k)‖` (the partition-of-unity Hilbert–Schmidt chart-Sobolev completion
norm, `tensorPouSobolevHilbert_norm_eq`) is controlled by the **spectral**
order-`2k` Sobolev norm of `T`, namely the square root of the weighted spectral
square-sum

  `∑ᵢ (1 + λᵢ)^{2k} · (tensorL2Coeff (T.toL2) i)²`

of the eigenbasis coordinates of `T`'s `L²` class against the connection-Laplacian
resolvent eigenbasis.  This is the general-order ("all `k`") analogue of the
order-`2` two-sided comparison
`tensorPouSobolevHs_order2_equiv_pouSobolev`/`Order2NormEquivOnSmooth`
(`Order2Equivalence.lean`): the elliptic-regularity / Gårding direction that
bounds the intrinsic chart-Sobolev norm by the `Δ_∇`-`L²` spectral norm, lifted
from order `2` to every order `2k`.

`pouSobolevToHsNorm_le_spectral`: there is a uniform constant `C ≥ 0` such that
for every order `2k` and every smooth compactly-supported `(0, 2)`-tensor `T`,

  `‖T.toHs (2k)‖ ≤ C · √(∑ᵢ (1 + λᵢ)^{2k} · (tensorL2Coeff (T.toL2) i)²)`.

This is the genuine elliptic ("Gårding") lift to general order; orders `0` and
`1` are chart-locality-free in `L2BanachIso`/`CompactInclusionIntrinsic`, and the
order-`2` Hilbert–Schmidt comparison is `tensorPouSobolevHs_order2_equiv_pouSobolev`.
It carries no chart-locality predicate (no `HasLocallyConstantChartAt`).  The body
is `sorry`, so consumers transitively depend on `sorryAx`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral
namespace SobolevScale

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **General-order intrinsic-Sobolev control by the spectral Sobolev norm
(deep elliptic / Gårding input).**

There is a uniform constant `C ≥ 0` such that for every order `2k` and every smooth
compactly-supported `(0, 2)`-tensor section `T`, the intrinsic order-`2k`
partition-of-unity Hilbert–Schmidt chart-Sobolev norm `‖T.toHs (2k)‖` is bounded by
`C` times the square root of the weighted spectral square-sum
`∑ᵢ (1 + λᵢ)^{2k} · (tensorL2Coeff (T.toL2) i)²` of the eigenbasis coordinates of
`T`'s `L²` class.

This is the general-order ("all `k`") elliptic-regularity / Gårding lift of the
order-`2` two-sided norm comparison `tensorPouSobolevHs_order2_equiv_pouSobolev`: the
intrinsic chart-Sobolev norm is controlled by the `Δ_∇`-`L²` spectral norm at every
order.  It carries no chart-locality predicate.  The conclusion is a uniform norm
bound, structurally distinct from any spectral-decay hypothesis (no packaging).  The
body is `sorry`. -/
theorem pouSobolevToHsNorm_le_spectral
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (T : SmoothCcTensor g₀ 0 2),
      ‖SmoothCcTensor.toHs (g := g₀) (r := 0) (s := 2) (2 * k) T‖ ≤
        C * Real.sqrt (∑' i : TensorEigenIdx (I := I) (M := M) g₀ 0 2,
          tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) *
            (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 T) i) ^ 2) := sorry

end SobolevScale
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
