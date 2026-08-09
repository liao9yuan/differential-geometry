import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H3Principal
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifGridRS

/-!
# Class-first differentiated application estimate

This module feeds the dimension-three class-uniform mixed two-arm grid into
the universal differentiated-contraction estimate.  The resulting coefficient
is fixed before the class metric and the two tensor fields vary.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Dimension-three class-first differentiated application estimate.**

For a fixed background, class parameter, and valences, one coefficient is
chosen before `g`, `Φ`, and `V` vary.  Metric jets through order two transfer
the two `H²` jet radii to the mixed product grid. -/
theorem appCc_grad_unif
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (s c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (Φ : SmoothCcTensor g (s + 2) c)
          (V : SmoothCcTensor g 0 (s + 1)) (A B : ℝ),
          0 ≤ A → 0 ≤ B →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g (s + 2) c j Φ‖ ^ 2) ≤ A ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 (s + 1) j V‖ ^ 2) ≤ B ^ 2 →
          ‖appCc (I := I) (M := M) g (s + 2) (c + 1)
              (covGrad (I := I) (M := M) g (s + 2) c Φ)
              (covGrad (I := I) (M := M) g 0 (s + 1) V)‖ ≤
            C * A * B := by
  obtain ⟨Cg, hCg, hgrid⟩ :=
    DifferentialGeometry.PDE.RicciFlow.grid_rs_unif
      (I := I) (M := M) hDim gBase hΛ (s + 2) 0 c (s + 1)
  refine ⟨Real.sqrt Cg, Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet1 hjet2 Φ V A B hA hB hΦjet hVjet
  obtain ⟨hgridInt, hgridBd⟩ :=
    hgrid g hEq hjet1 hjet2 Φ V A B hA hB hΦjet hVjet
  exact appCc_grad_of_grid (I := I) (M := M) g s c Cg hCg
    Φ V A B hA hB hgridInt hgridBd

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
