import DifferentialGeometry.Flow.RicciFlow.Pullback.Metric
import DifferentialGeometry.Flow.RicciFlow.Pullback.LeviCivitaConjugation
import DifferentialGeometry.Flow.RicciFlow.Pullback.RiemannConjugation
import DifferentialGeometry.Flow.RicciFlow.Pullback.RicciTraceConjugation
import DifferentialGeometry.Flow.RicciFlow.Pullback.MLieBracketNaturality
import DifferentialGeometry.Riemannian.Curvature.RicciConnection
import DifferentialGeometry.Riemannian.Curvature.Curvature
import DifferentialGeometry.Riemannian.Curvature.CurvatureBundling

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

/-- **Naturality of the Ricci tensor under a diffeomorphism.**
For a smooth Riemannian metric `g` on `M` and a diffeomorphism
`Φ : M ≃ₘ⟮I, I⟯ M`, the Ricci tensor of the pullback metric
`Diffeomorph.pullbackMetric g Φ` at `x` evaluated on `(v, w)` equals the
Ricci tensor of `g` at `Φ x` evaluated on the pushed-forward vectors
`(mfderiv I I Φ x v, mfderiv I I Φ x w)`.

This expresses the diffeomorphism-equivariance of the Ricci tensor.

The proof delegates to `ricciTensor_pullback_conjugation`, whose statement
is definitionally the same identity; that lemma carries the substantive
trace-conjugation argument (the trace-of-Riemann-endomorphism expression of
`Ric` transforms naturally under the invertible linear map `mfderiv I I Φ x`
induced by the diffeomorphism). -/
theorem ricci_tensor_pullback_natural_under_diffeomorphism
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (Diffeomorph.pullbackMetric g Φ) x v w
      = ricciTensor (I := I) g (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) :=
  ricciTensor_pullback_conjugation (I := I) g Φ x v w

end DifferentialGeometry.PDE.RicciFlow.Pullback
