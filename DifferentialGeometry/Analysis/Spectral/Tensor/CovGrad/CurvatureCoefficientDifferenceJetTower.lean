import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
def ricEndoRaisedField (g : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => ricEndoRaisedFib (I := I) g x
  contMDiff_toFun := ricEndoRaisedFib_contMDiff (I := I) g

set_option backward.isDefEq.respectTransparency false in
def ricEndoBackgroundDifferenceField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ricEndoRaisedField (I := I) (M := M) g₁ - ricEndoRaisedField (I := I) (M := M) g₀

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma ricEndoBackgroundDifferenceField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x =
      ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x := by
  rw [ricEndoBackgroundDifferenceField]
  rw [show ((ricEndoRaisedField (I := I) (M := M) g₁ -
        ricEndoRaisedField (I := I) (M := M) g₀) x) =
      ricEndoRaisedField (I := I) (M := M) g₁ x -
        ricEndoRaisedField (I := I) (M := M) g₀ x from by
    rw [ContMDiffSection.coe_sub]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma curvCoeffSlot_zero_backgroundDifference_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0 =
      slotInsertEndoCc (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0).toSection x) =
      (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0).toSection x -
        (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ 0 x D from rfl]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₀ 0 x D from rfl]
  rw [ricciArmOrder0CurvCoeffFibSlot_toModel, ricciArmOrder0CurvCoeffFibSlot_toModel]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)).toSection x) D =
      slotInsertEndoFib (I := I) (M := M) 2 0 x
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x) D from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [ricEndoBackgroundDifferenceField_apply (I := I) (M := M) g₀ g₁ x]
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.map_update_sub]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma curvCoeffSlot_one_backgroundDifference_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1 =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
        (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1).toSection x) =
      (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1).toSection x -
        (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ 1 x D from rfl]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₀ 1 x D from rfl]
  rw [ricciArmOrder0CurvCoeffFibSlot_toModel, ricciArmOrder0CurvCoeffFibSlot_toModel]
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
        (Equiv.swap (0 : Fin 2) 1)).toSection x) D =
      reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) D
      from rfl]
  rw [reindexCoeffFibGen_apply]
  rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, slotInsertEndoCc_toSection,
    slotInsertEndoFib_apply_eval, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
        Function.update (fun i : Fin 2 => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
          ((ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x)
            (m ((Equiv.swap (0 : Fin 2) 1) 0))) ((Equiv.swap (0 : Fin 2) 1) i)) =
      Function.update m 1
        ((ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x) (m 1)) from by
    funext j
    fin_cases j <;>
      simp [Function.update]]
  rw [ricEndoBackgroundDifferenceField_apply (I := I) (M := M) g₀ g₁ x]
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.map_update_sub]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem ricciArmOrder0CurvCoeff_backgroundDifference_decomp
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀ =
      slotInsertEndoCc (I := I) (M := M) g₀ 1
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) +
        reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
          (Equiv.swap (0 : Fin 2) 1) := by
  rw [← curvCoeffSlot_one_backgroundDifference_eq (I := I) (M := M) g₀ g₁,
    ← curvCoeffSlot_zero_backgroundDifference_eq (I := I) (M := M) g₀ g₁,
    ricciArmOrder0CurvCoeff, ricciArmOrder0CurvCoeff]
  abel

set_option linter.unusedVariables false in
theorem slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2 ≤ K i :=
  sorry

set_option linter.unusedVariables false in
theorem ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i :=
  sorry

set_option linter.unusedVariables false in
theorem ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i := by
  obtain ⟨K, hK_nn, hK⟩ :=
    slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 4 * (Module.finrank ℝ E : ℝ) * K i,
    fun i => mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (hK_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hKi := hK g₁ P hδ_le hδ htie hPball i hi
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
    intro x
    have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
              (Equiv.swap (0 : Fin 2) 1))).toSection x := by
      rw [ricciArmOrder0CurvCoeff_backgroundDifference_decomp (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1)),
        SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) :=
      rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) i x
    rw [hswap]
    have hendo : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) i x
      rw [pow_one] at h
      exact h
    linarith [hendo]
  have hF_int : MeasureTheory.Integrable
      (fun x => 4 * (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))
    (fun x => 4 * (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
    hF_int hpt
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 1 (1 + i)
    (iteratedCovGrad (I := I) g₀ 1 1 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))]
  rw [← SmoothCcTensor.norm_def]
  exact mul_le_mul_of_nonneg_left hKi (by positivity)

end Connection
end Integral
end DifferentialGeometry

end
