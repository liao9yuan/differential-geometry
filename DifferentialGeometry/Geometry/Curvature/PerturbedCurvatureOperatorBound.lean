import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.UniformRiemannOperatorNormBound
import DifferentialGeometry.Analysis.Elliptic.MetricBounds

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
theorem gZeroInner_self_le_of_g1_self_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ P x v w)
    (x : M) (v : TangentSpace I x) {c : ℝ} (hc : g₁.inner x v v ≤ c) :
    (1 - δ) * g₀.inner x v v ≤ c := by
  have hlb := perturbedInner_self_lower_bound (I := I) (M := M) g₀
    (ccTensorBilinSymm (I := I) g₀ P) hδ x v
  rw [perturbedInner_apply] at hlb
  rw [← htie x v v] at hlb
  linarith

set_option linter.unusedSectionVars false in
theorem gZeroInner_self_le_neumann_of_g1_unit
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      g₁.inner x v w = g₀.inner x v w +
        ccTensorBilinSymm (I := I) g₀ P x v w)
    (x : M) (v : TangentSpace I x) (hunit : g₁.inner x v v = 1) :
    g₀.inner x v v ≤ (1 - δ)⁻¹ := by
  have hcoeff : 0 < 1 - δ := by linarith
  have hkey := gZeroInner_self_le_of_g1_self_le (I := I) (M := M) g₀ g₁ P hδ htie x v
    (le_of_eq hunit)
  rw [show (1 - δ)⁻¹ = 1 / (1 - δ) from (one_div _).symm, le_div_iff₀ hcoeff]
  linarith

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_ricEndoRaisedFib_perturbed_gQuadratic_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ max δ₀ 0)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          ∀ v : TangentSpace I x,
            g₀.inner x (ricEndoRaisedFib (I := I) g₁ x v)
                (ricEndoRaisedFib (I := I) g₁ x v) ≤ C ^ 2 * g₀.inner x v v :=
  sorry

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannOp_LeviCivita_perturbed_gQuadratic_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ max δ₀ 0)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          ∀ v w u : TangentSpace I x,
            g₀.inner x (riemannOp (cov := LeviCivita (I := I) g₁) x v w u)
                (riemannOp (cov := LeviCivita (I := I) g₁) x v w u) ≤
              C ^ 2 * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u :=
  sorry

end Curvature
end Geometry
end DifferentialGeometry

end
