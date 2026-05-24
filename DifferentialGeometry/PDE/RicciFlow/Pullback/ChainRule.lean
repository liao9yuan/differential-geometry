import DifferentialGeometry.PDE.RicciFlow.Pullback.Metric
import DifferentialGeometry.PDE.RicciFlow.Pullback.CartanFormula
import DifferentialGeometry.PDE.DeTurck.LieDerivativeMetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.Basic

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem pullback_time_derivative_chain_rule
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    True := sorry

theorem pullback_metric_evaluation_formula
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    True := sorry

theorem mfderiv_time_derivative_along_flow
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (X_fam : ℝ → ∀ x : M, TangentSpace I x)
    (t : ℝ) (x : M) (v : TangentSpace I x) :
    True := sorry

theorem pullback_metric_derivative_decomposition
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) :
    True := sorry

theorem combine_pullback_derivative_pieces
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) :
    True := sorry

end DifferentialGeometry.PDE.RicciFlow.Pullback
