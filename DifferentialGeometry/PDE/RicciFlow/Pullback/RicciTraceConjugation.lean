import DifferentialGeometry.PDE.RicciFlow.Pullback.RiemannConjugation
import DifferentialGeometry.Integral.Connection.Ricci
import Mathlib.LinearAlgebra.Trace

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Pullback-by-conjugation for the Ricci tensor (pointwise form).**
For a smooth Riemannian metric `g` on `M` and a diffeomorphism
`Φ : M ≃ₘ⟮I, I⟯ M`, the Ricci tensor of the pullback metric `Φ*g`
at a point `x` evaluated on `(v, w) ∈ T_x M × T_x M` agrees with the
Ricci tensor of `g` at `Φ x` evaluated on the pushforward
`(dΦ_x v, dΦ_x w)`.

Geometrically, this is the diffeomorphism-naturality of the Ricci tensor:
since `Ric` is built from `(g, ∇^g)` by metric-independent algebraic
operations (trace of the Riemann endomorphism), and both `g` and `∇^g`
transform naturally under diffeomorphisms, so does `Ric`. The proof
chains Riemann-curvature naturality (`riemann_pullback_conjugation`)
with the conjugation-invariance of the trace (the trace of an
endomorphism is unchanged when conjugated by an invertible linear
map, here `mfderiv I I Φ x`). -/
theorem ricci_trace_pullback_conjugation
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (Diffeomorph.pullbackMetric g Φ) x v w
      = ricciTensor (I := I) g (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Pullback
