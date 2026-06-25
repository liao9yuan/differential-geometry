import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier

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
private theorem orthoFrame_to_basis
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i : Fin (Module.finrank ℝ E), bse i = e i := by
  classical
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  refine ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard, fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private theorem componentSlice_sq_sum_le_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (x : M) (S : TensorRSSpace 2 2 I x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 2 → Fin (Module.finrank ℝ E)) :
    (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g x 2 2 S
        (Module.finrank ℝ E) e K J) ^ 2) ≤
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x S := by
  classical
  obtain ⟨bse, hbse⟩ := orthoFrame_to_basis (I := I) (M := M) g x e horth
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g 2 2 x S e bse rfl hbse horth]
  refine Finset.single_le_sum
    (f := fun K' : Fin 2 → Fin (Module.finrank ℝ E) =>
      ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        (fiberNormSqComponent (I := I) (M := M) g x 2 2 S (Module.finrank ℝ E) e K' J) ^ 2)
    (fun K' _ => Finset.sum_nonneg (fun J _ => sq_nonneg _)) (Finset.mem_univ K)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannBiContrFib_perturbed_riemannianFiberNormSq_le_of_jetEnvelope
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
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              (show TensorRSSpace 2 2 I x from
                TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) ≤ C ^ 2 :=
  sorry

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_ricciArmOrder0CurvCoeffFib_perturbed_riemannianFiberNormSq_le_of_jetEnvelope
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
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              (show TensorRSSpace 2 2 I x from
                TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)) ≤ C ^ 2 :=
  sorry

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannBiContrFib_perturbed_frameComponent_sum_sq_le_of_jetEnvelope
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
          ∀ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
            (_horth : ∀ a b : Fin (Module.finrank ℝ E),
              g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
            (K : Fin 2 → Fin (Module.finrank ℝ E)),
            (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
              (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
                (show TensorRSSpace 2 2 I x from
                  TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
                (Module.finrank ℝ E) e K J) ^ 2) ≤ C ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_riemannBiContrFib_perturbed_riemannianFiberNormSq_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv e horth K
  refine le_trans
    (componentSlice_sq_sum_le_riemannianFiberNormSq (I := I) (M := M) g₀ x
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
      e horth K)
    (hC g₁ P hδ_le hδ htie x henv)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_ricciArmOrder0CurvCoeffFib_perturbed_frameComponent_sum_sq_le_of_jetEnvelope
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
          ∀ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
            (_horth : ∀ a b : Fin (Module.finrank ℝ E),
              g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
            (K : Fin 2 → Fin (Module.finrank ℝ E)),
            (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
              (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
                (show TensorRSSpace 2 2 I x from
                  TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x))
                (Module.finrank ℝ E) e K J) ^ 2) ≤ C ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_ricciArmOrder0CurvCoeffFib_perturbed_riemannianFiberNormSq_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv e horth K
  refine le_trans
    (componentSlice_sq_sum_le_riemannianFiberNormSq (I := I) (M := M) g₀ x
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x))
      e horth K)
    (hC g₁ P hδ_le hδ htie x henv)

end Curvature
end Geometry
end DifferentialGeometry

end
