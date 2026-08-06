import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.UnifCurvatureJetOne
import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorCurvFirstOrderBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.UnifBochnerGap

/-!
# Explicit rank-two curvature action for the metric class

This module combines the class-uniform tangent `R` and `nabla R` caps with the
native supplied-cap pointwise commutator estimate.  The result is the exact
rank-two, order-zero package used by the finite `H^2` realization route; no
all-order curvature family enters.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The closed rank-two curvature-action coefficient determined by the class
parameter and the supplied fixed-background `R` and `nabla R` caps. -/
noncomputable def unifPtCurvZeroC (d : ℕ) (Λ Kb₀ Kb₁ : ℝ) : ℝ :=
  ptCurvZeroC d
    (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb₀))
    (rmOneOpC Λ Kb₀ Kb₁)

/-- The closed rank-three curvature-action coefficient determined by the class
parameter and the supplied fixed-background `R` and `∇R` caps. -/
noncomputable def unifPtCurvThreeC (d : ℕ) (Λ Kb₀ Kb₁ : ℝ) : ℝ :=
  ptCurvRankC d 3
    (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb₀))
    (rmOneOpC Λ Kb₀ Kb₁)

/-- The class metric jets through order three produce the exact rank-two,
order-zero curvature-action package needed by the finite `H^2` comparison. -/
theorem unifCurvAction0_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    IsCurvAction0 (I := I) (M := M) g₀ 2
      (unifPtCurvZeroC (Module.finrank ℝ E) Λ Kb₀ Kb₁) := by
  have hR0 := unifCurvSup_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀_nonneg hKb₀ hcomp hjet1 hjet2
  have hC1 : 0 ≤ rmOneOpC Λ Kb₀ Kb₁ :=
    rmOneOpC_nonneg (le_trans zero_le_one hΛ) hKb₁_nonneg
  have hR1 := unifRmOpOne_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3
  refine IsCurvAction0.mk
    (ptCurvZeroC_nonneg (Module.finrank ℝ E)
      (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb₀))
      (rmOneOpC Λ Kb₀ Kb₁)) ?_
  intro S
  have h := ptCurv_zero_of (I := I) (M := M) g₀ hR0 hC1 hR1 S
  simpa only [unifPtCurvZeroC, Finset.sum_range_succ, Finset.sum_range_zero,
    iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero, zero_add] using h

/-- The class metric jets through order three produce the rank-three,
order-zero curvature-action package needed by the finite `H^3` comparison. -/
theorem unifCurvAction3_of
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ)
    (hjet3 : MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ) :
    IsCurvAction0 (I := I) (M := M) g₀ 3
      (unifPtCurvThreeC (Module.finrank ℝ E) Λ Kb₀ Kb₁) := by
  have hR0 := unifCurvSup_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀_nonneg hKb₀ hcomp hjet1 hjet2
  have hC1 : 0 ≤ rmOneOpC Λ Kb₀ Kb₁ :=
    rmOneOpC_nonneg (le_trans zero_le_one hΛ) hKb₁_nonneg
  have hR1 := unifRmOpOne_of (I := I) (M := M) gBase g₀ hΛ
    hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3
  refine IsCurvAction0.mk
    (ptCurvRankC_nonneg (Module.finrank ℝ E) 3
      (Λ ^ 2 * (riemannDiffC Λ Λ Λ + Real.sqrt Kb₀))
      (rmOneOpC Λ Kb₀ Kb₁)) ?_
  intro S
  have h := ptCurv_zero_rank_of (I := I) (M := M) g₀ 3 hR0 hC1 hR1 S
  simpa only [unifPtCurvThreeC, Finset.sum_range_succ, Finset.sum_range_zero,
    iteratedCovGrad_zero, iteratedCovGrad_succ, Nat.add_zero, zero_add] using h

end RicciFlow
end PDE
end DifferentialGeometry

end
