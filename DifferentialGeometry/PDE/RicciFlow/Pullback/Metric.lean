import DifferentialGeometry.Metric.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Basic

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- order 400: capstone wrapper-existence
theorem diffeomorph_pullback_metric_exists
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    ∃ g' : SmoothRiemannianMetric I M, True := sorry

-- order 401: fiberwise form
noncomputable def Diffeomorph.pullbackInner
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := sorry

-- order 402: symmetry
theorem Diffeomorph.pullbackInner_symm
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    Diffeomorph.pullbackInner g Φ x v w
      = Diffeomorph.pullbackInner g Φ x w v := sorry

-- order 403: positive-definite
theorem Diffeomorph.pullbackInner_pos
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < Diffeomorph.pullbackInner g Φ x v v := sorry

-- order 404: vN-bounded preservation (placeholder)
theorem Diffeomorph.pullbackInner_isVonNBounded
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

-- order 405: smoothness of the pullback section (placeholder)
theorem Diffeomorph.pullbackInner_contMDiff
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

-- order 406: mfderiv of a diffeomorphism is smooth (depth-3 child of 405)
theorem Diffeomorph.mfderiv_contMDiff
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

-- order 407: bilinear pullback bundle is smooth (depth-3 child)
theorem bilinear_pullback_bundle_smooth
    (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

-- order 408: inner composed with diffeo is smooth (depth-3 child)
theorem inner_comp_smooth_along_diffeo
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    True := sorry

-- order 409: bundled pullback metric
noncomputable def Diffeomorph.pullbackMetric
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M) :
    SmoothRiemannianMetric I M := sorry

-- order 410: pullback under identity diffeomorphism
theorem Diffeomorph.pullbackMetric_refl
    (g : SmoothRiemannianMetric I M) :
    Diffeomorph.pullbackMetric g (_root_.Diffeomorph.refl I M ∞) = g := sorry

end DifferentialGeometry.PDE.RicciFlow.Pullback
