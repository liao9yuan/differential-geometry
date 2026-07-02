import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

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
private theorem curvDiffGrid_productTerm_integral_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max R (max C 1))) ^ (7 * i) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max R (max C 1)) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar :=
    le_trans (le_max_right C 1) (le_trans (le_max_right R _) (le_max_right Λ _))
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hR_le : R ≤ Mbar := le_trans (le_max_left R _) (le_max_right Λ _)
  have hC_le : C ≤ Mbar :=
    le_trans (le_trans (le_max_left C 1) (le_max_right R _)) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e2 : R ^ 2 ≤ Mbar ^ 2 := pow_le_pow_left₀ hR hR_le 2
          have e3 : Mbar ^ (2 * i) * Mbar ^ 2 ≤ Mbar ^ (7 * i) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ hMbar1 (by omega)
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith [pow_nonneg hMbar_nn (7 * i)]
          calc Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 := e4
            _ ≤ Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hexp2_nn : 0 ≤ 2 * (e m : ℝ) / i := by positivity
      have hexp2_le : 2 * (e m : ℝ) / i ≤ 2 := by
        rw [mul_div_assoc]; nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hRpow : R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 : ℕ) := by
        calc R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 * (e m : ℝ) / i) :=
              Real.rpow_le_rpow hR hR_le hexp2_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp2_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
          Mbar ^ (5 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        have h2 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
            Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) :=
          mul_le_mul h1 hRpow (Real.rpow_nonneg hR _) (by positivity)
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)
            ≤ Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) := h2
          _ = Mbar ^ (5 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) := by
        apply mul_nonneg (mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)) (Real.rpow_nonneg hR _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM5_one : (1 : ℝ) ≤ Mbar ^ (5 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hM5_one hidiv
        _ = (Mbar ^ (5 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
        _ = Mbar ^ (5 * i) := by rw [← pow_mul]
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * Mbar ^ (5 * i) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * Mbar ^ (5 * i) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) :=
            mul_le_mul_of_nonneg_right e1 (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith [pow_nonneg hMbar_nn (7 * i)]
          calc Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) := e4
            _ = Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5

set_option linter.unusedVariables false in
private theorem curvDiffGrid_integral_ballUniform_window
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a + 2 →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K i := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Lam (max R (max (Cgn k) 1))) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_trans (le_max_right R _) (le_max_right Lam _)))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, ?_, ?_⟩
  · intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  · intro P hPball i hi
    by_cases hi0 : i = 0
    · subst hi0
      have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
        funext x
        simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
          Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
      refine ⟨?_, ?_⟩
      · rw [hgrid0]; exact MeasureTheory.integrable_const 1
      · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
          MeasureTheory.measureReal_def, ← hvol]
        exact le_add_of_nonneg_left
          (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R := hPball i (by omega)
      have hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
          Lam ^ 2 := by
        intro x
        have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
                apply Finset.sum_le_sum
                intro j hj
                have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
                nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
            _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
            ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := by
          have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
          have hsl := Finset.single_le_sum
            (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
            (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
          simpa using hsl
        have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
          refine le_trans (hCemb P x) ?_
          rw [hLam2]
          calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
                mul_le_mul_of_nonneg_left hsum_le (by positivity)
            _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
        exact le_trans hsingle hchain
      have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
      have hGNP : ∀ j : ℕ, 0 < j → j < i →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
            Cgn i * Lam ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)) := by
        intro j hj0 hji
        have hb := hGNspec P Lam hLam_nn hΛsup j hj0 hji
        have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
          rw [hCgn]; simp only [dif_pos hi1]
        rw [hchoose] at hb
        refine le_trans hb ?_
        have hnorm : Integral.L2.tensorL2Norm (I := I) (M := M) g₀ 0 (2 + i)
            (iteratedCovGrad (I := I) g₀ 0 2 i P).toFun = ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ :=
          (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P)).symm
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hNi (by positivity))
          (mul_nonneg (hCgn_nn i) (Real.rpow_nonneg hLam_nn _))
      have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
          MeasureTheory.Integrable (fun x => ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ Gfun i := by
        intro n hn e he
        have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
        have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
        have hres := curvDiffGrid_productTerm_integral_le (I := I) (M := M) g₀ P hR i hi1 hLam_nn hΛsup
          hNi (hCgn_nn i) hGNP n hn_le e hsum_e
        simpa only [hGfun] using hres
      have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        apply MeasureTheory.integrable_finset_sum
        intro n hn
        apply MeasureTheory.integrable_finset_sum
        intro e he
        exact (hPT n hn e he).1
      refine ⟨hgrid_int, ?_⟩
      rw [MeasureTheory.integral_finset_sum _
        (fun n hn => MeasureTheory.integrable_finset_sum _ (fun e he => (hPT n hn e he).1))]
      have hinner : ∀ n ∈ Finset.range (i + 1),
          (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        intro n hn
        exact MeasureTheory.integral_finset_sum _ (fun e he => (hPT n hn e he).1)
      rw [Finset.sum_congr rfl hinner]
      have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
            (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i := by
        apply Finset.sum_le_sum; intro n hn
        apply Finset.sum_le_sum; intro e he
        exact (hPT n hn e he).2
      have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i =
          (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) * Gfun i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro n _
        rw [Finset.sum_const, nsmul_eq_mul]
      refine le_trans hle1 ?_
      rw [heq2]
      exact le_add_of_nonneg_right hvol_nn

private def tGridCount (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ)

private lemma tGridCount_nonneg (j : ℕ) : 0 ≤ tGridCount j :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

private lemma prodTerm_le_antidiagonalTupleGrid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (k n : ℕ) (hn : n < k + 1) (e : Fin n → ℕ)
    (he : e ∈ Finset.Nat.antidiagonalTuple n k) :
    (∏ m : Fin n, b (e m)) ≤ Combinatorics.antidiagonalTupleGrid b k := by
  rw [Combinatorics.antidiagonalTupleGrid]
  have h1 : (∏ m : Fin n, b (e m)) ≤
      ∑ e' ∈ Finset.Nat.antidiagonalTuple n k, ∏ m : Fin n, b (e' m) :=
    Finset.single_le_sum (f := fun e' : Fin n → ℕ => ∏ m : Fin n, b (e' m))
      (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)) he
  refine le_trans h1 ?_
  exact Finset.single_le_sum
    (f := fun n' : ℕ => ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k, ∏ m : Fin n', b (e' m))
    (fun n' _ => Finset.sum_nonneg (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)))
    (Finset.mem_range.mpr hn)

private lemma antidiagonalTupleGrid_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j k : ℕ) :
    Combinatorics.antidiagonalTupleGrid b j * Combinatorics.antidiagonalTupleGrid b k ≤
      (tGridCount j * tGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) := by
  classical
  have hpair : ∀ n ∈ Finset.range (j + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n j,
      ∀ n' ∈ Finset.range (k + 1), ∀ e' ∈ Finset.Nat.antidiagonalTuple n' k,
      (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) ≤
        Combinatorics.antidiagonalTupleGrid b (j + k) := by
    intro n hn e he n' hn' e' he'
    have happend : (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) =
        ∏ m : Fin (n + n'), b (Fin.append e e' m) := by
      rw [Fin.prod_univ_add]
      congr 1
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_left])
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_right])
    rw [happend]
    have hmem : Fin.append e e' ∈ Finset.Nat.antidiagonalTuple (n + n') (j + k) := by
      rw [Finset.Nat.mem_antidiagonalTuple] at he he' ⊢
      rw [Fin.sum_univ_add]
      have h1 : (∑ m : Fin n, Fin.append e e' (Fin.castAdd n' m)) = j := by
        rw [← he]
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_left])
      have h2 : (∑ m : Fin n', Fin.append e e' (Fin.natAdd n m)) = k := by
        rw [← he']
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_right])
      rw [h1, h2]
    have hnn' : n + n' < j + k + 1 := by
      rw [Finset.mem_range] at hn hn'
      omega
    exact prodTerm_le_antidiagonalTupleGrid b hb (j + k) (n + n') hnn' _ hmem
  calc Combinatorics.antidiagonalTupleGrid b j * Combinatorics.antidiagonalTupleGrid b k
      = ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ((∏ m : Fin n, b (e m)) * Combinatorics.antidiagonalTupleGrid b k) := by
        rw [Combinatorics.antidiagonalTupleGrid, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_mul])
    _ ≤ ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          (tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) := by
        refine Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun e he => ?_))
        calc (∏ m : Fin n, b (e m)) * Combinatorics.antidiagonalTupleGrid b k
            = ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                ((∏ m : Fin n, b (e m)) * ∏ m : Fin n', b (e' m)) := by
              rw [Combinatorics.antidiagonalTupleGrid, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n' _ => by rw [Finset.mul_sum])
          _ ≤ ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                Combinatorics.antidiagonalTupleGrid b (j + k) := by
              refine Finset.sum_le_sum (fun n' hn' => Finset.sum_le_sum (fun e' he' => ?_))
              exact hpair n hn e he n' hn' e' he'
          _ = tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k) := by
              rw [tGridCount, Finset.sum_mul]
              exact Finset.sum_congr rfl (fun n' _ => by
                rw [Finset.sum_const, nsmul_eq_mul])
    _ = ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ) *
          (tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) := by
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_const, nsmul_eq_mul])
    _ = (tGridCount j * tGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) := by
        rw [show (tGridCount j * tGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) =
            tGridCount j * (tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) from by
          ring]
        rw [show tGridCount j = ∑ n ∈ Finset.range (j + 1),
            ((Finset.Nat.antidiagonalTuple n j).card : ℝ) from rfl]
        rw [Finset.sum_mul]

private def tWindow (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k

private lemma tWindow_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ) : 0 ≤ tWindow b i :=
  Finset.sum_nonneg (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)

private lemma antidiagonalTupleGrid_le_tWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {k i : ℕ} (hk : k < i + 3) :
    Combinatorics.antidiagonalTupleGrid b k ≤ tWindow b i :=
  Finset.single_le_sum (fun k' _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k')
    (Finset.mem_range.mpr hk)

private lemma tWindow_mono (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {i i' : ℕ} (h : i ≤ i') :
    tWindow b i ≤ tWindow b i' := by
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (show i + 3 ≤ i' + 3 by omega)) ?_
  intro k _ _
  exact Combinatorics.antidiagonalTupleGrid_nonneg b hb k

private lemma one_le_tWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ) : 1 ≤ tWindow b i := by
  rw [← Combinatorics.antidiagonalTupleGrid_zero b]
  exact antidiagonalTupleGrid_le_tWindow b hb (by omega)

private def tWindowMulConst (j l : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j + 3), tGridCount k * tGridCount l

private lemma tWindowMulConst_nonneg (j l : ℕ) : 0 ≤ tWindowMulConst j l :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (tGridCount_nonneg k) (tGridCount_nonneg l))

private lemma tWindow_mul_antidiagonalTupleGrid_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j l : ℕ) :
    tWindow b j * Combinatorics.antidiagonalTupleGrid b l ≤
      tWindowMulConst j l * tWindow b (j + l) := by
  calc tWindow b j * Combinatorics.antidiagonalTupleGrid b l
      = ∑ k ∈ Finset.range (j + 3),
          Combinatorics.antidiagonalTupleGrid b k * Combinatorics.antidiagonalTupleGrid b l := by
        rw [tWindow, Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.range (j + 3), (tGridCount k * tGridCount l) * tWindow b (j + l) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        refine le_trans (antidiagonalTupleGrid_mul_le b hb k l) ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (tGridCount_nonneg k) (tGridCount_nonneg l))
        refine antidiagonalTupleGrid_le_tWindow b hb ?_
        rw [Finset.mem_range] at hk
        omega
    _ = tWindowMulConst j l * tWindow b (j + l) := by
        rw [tWindowMulConst, ← Finset.sum_mul]

set_option linter.unusedSectionVars false in
private lemma tWindow_eq_tripleSum (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (i : ℕ) :
    tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i =
      ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := rfl

set_option linter.unusedSectionVars false in
private lemma antidiagonalTupleGrid_eq_doubleSum (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (l : ℕ) :
    Combinatorics.antidiagonalTupleGrid
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l =
      ∑ n ∈ Finset.range (l + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n l,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := rfl

set_option linter.unusedSectionVars false in
private theorem exists_backgroundJet_rfns_bound (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (S : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i S).toSection x) ≤ c i := by
  have h : ∀ i : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i S).toSection x) ≤ c := fun i =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + i)
      (iteratedCovGrad (I := I) g₀ r s i S)
  choose c hc0 hcb using h
  exact ⟨c, hc0, hcb⟩

section MixedSharpRicci

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
def ricMixedSharpEndoFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap
      map_add' := fun v v' => by
        have h : (ricciTensor (I := I) g₁ x (v + v')).toLinearMap =
            (ricciTensor (I := I) g₁ x v).toLinearMap +
              (ricciTensor (I := I) g₁ x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ricciTensor (I := I) g₁ x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : (ricciTensor (I := I) g₁ x (c • v)).toLinearMap =
            c • (ricciTensor (I := I) g₁ x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ricciTensor (I := I) g₁ x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

set_option linter.unusedSectionVars false in
@[simp] lemma ricMixedSharpEndoFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v =
      metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap := by
  rw [ricMixedSharpEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem ricMixedSharpEndoFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ricciTensor (I := I) g₁ b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hRic : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ricciTensor (I := I) g₁ b)) :=
      ricciTensor_contMDiff (I := I) g₁
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ricciTensor (I := I) g₁ b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hRic.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g₀
    (cv := fun b : M => (ricciTensor (I := I) g₁ b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x (Y x))
  rw [ricMixedSharpEndoFib_apply]

set_option backward.isDefEq.respectTransparency false in
def ricMixedSharpEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x
  contMDiff_toFun := ricMixedSharpEndoFib_contMDiff (I := I) (M := M) g₀ g₁

set_option linter.unusedSectionVars false in
lemma ricMixedSharpEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    ricMixedSharpEndoField (I := I) (M := M) g₀ g₁ x =
      ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x := rfl

set_option linter.unusedSectionVars false in
private lemma ricEndoRaisedFib_eq_mixed_add_gInvDiffRaised
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    ricEndoRaisedFib (I := I) g₁ x v =
      ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v +
        gInvDiffRaisedEndo (I := I) g₀ g₁ x
          (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) := by
  rw [gInvDiffRaisedEndo_apply]
  have hcollapse : ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v +
      (inverseMetricSharpFib (I := I) g₁ x
          (g0FlatCLM (I := I) g₀ x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)) -
        ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) =
      inverseMetricSharpFib (I := I) g₁ x
        (g0FlatCLM (I := I) g₀ x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)) := by
    abel
  rw [hcollapse]
  rw [inverseMetricSharpFib_g0FlatCLM_eq_metricSharp (I := I) g₀ g₁ x
    (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)]
  have hβ : (g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)).toLinearMap =
      (ricciTensor (I := I) g₁ x v).toLinearMap := by
    ext w
    rw [show ((g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)).toLinearMap) w =
        g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) w from rfl]
    rw [ricMixedSharpEndoFib_apply]
    exact inner_metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap w
  rw [hβ, ricEndoRaisedFib_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) =
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)) +
      appCcRS (I := I) (M := M) g₀ 1 1 1
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((((slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)) +
      appCcRS (I := I) (M := M) g₀ 1 1 1
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection) x) =
      ((slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x -
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x) +
      (appCcRS (I := I) (M := M) g₀ 1 1 1
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x from by
    rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub]
    rfl]
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sub_apply]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x) A from rfl]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x) A from rfl]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricEndoRaisedFib (I := I) g₀ x) A from rfl]
  rw [show ((appCcRS (I := I) (M := M) g₀ 1 1 1
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x
          (gInvDiffRaisedEndo (I := I) g₀ g₁ x) A) from rfl]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval]
  rw [Function.update_self, Function.update_idem]
  rw [ricEndoBackgroundDifferenceField_apply (I := I) (M := M) g₀ g₁ x]
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.map_update_sub]
  rw [ricEndoRaisedFib_eq_mixed_add_gInvDiffRaised (I := I) (M := M) g₀ g₁ x (m 0)]
  rw [ContinuousMultilinearMap.map_update_add]
  ring

end MixedSharpRicci

section RiemannLoweredDifference

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

set_option backward.isDefEq.respectTransparency false

def riemannLoweredCovec (gm gc : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ from
    { toFun := fun m =>
        gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_add, ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_smul, ContinuousLinearMap.smul_apply]
      cont := by
        have hR : Continuous (fun m : Fin 4 → TangentSpace I x =>
            riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) :=
          (((riemannOp (LeviCivita (I := I) gc) x).continuous.comp
            (continuous_apply 0)).clm_apply (continuous_apply 2)).clm_apply (continuous_apply 3)
        exact ((gm.inner x).continuous.comp hR).clm_apply (continuous_apply 1) }
    : Tensor0SSpace 4 I x)

set_option linter.unusedSectionVars false in
@[simp] lemma riemannLoweredCovec_apply (gm gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    riemannLoweredCovec (I := I) gm gc x m =
      gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1) := rfl

set_option linter.unusedSectionVars false in
private lemma riemannLoweredScalar_global (gm gc : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) gc) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) gc) hY hp hq
  have hcongr : (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => gm.inner x (riemannSec (LeviCivita (I := I) gc) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) gc) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) gm
    ⟨fun b => riemannSec (LeviCivita (I := I) gc) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

set_option linter.unusedSectionVars false in
private lemma riemannLoweredScalar_contMDiffAt (gm gc : SmoothRiemannianMetric I M)
    (V0 V1 V2 V3 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        gm.inner x (riemannOp (LeviCivita (I := I) gc) x (V0 x) (V2 x) (V3 x)) (V1 x)) x₀ := by
  have hglob := riemannLoweredScalar_global (I := I) (M := M) gm gc
    (Y := fun b => V0 b) (W := fun b => V1 b) (p := fun b => V2 b) (q := fun b => V3 b)
    V0.contMDiff V1.contMDiff V2.contMDiff V3.contMDiff
  exact hglob.contMDiffAt

set_option backward.isDefEq.respectTransparency false in
theorem riemannLoweredCovec_section_contMDiff (gm gc : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x (riemannLoweredCovec (I := I) gm gc x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (riemannLoweredCovec (I := I) gm gc x :
        Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y (σ 0) x) (Y (σ 2) x) (Y (σ 3) x))
        (Y (σ 1) x)) x₀ :=
    riemannLoweredScalar_contMDiffAt (I := I) gm gc (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) (Y (σ 3)) x₀
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 4, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change gm.inner x (riemannOp (LeviCivita (I := I) gc) x
      (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 2))) (e₁.symmL ℝ x (b (σ 3))))
      (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1, hframeEq 2, hframeEq 3]

def riemannLoweredField (gm gc : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  ⟨fun x => riemannLoweredCovec (I := I) gm gc x,
    riemannLoweredCovec_section_contMDiff (I := I) gm gc⟩

def riemannLoweredCc (g₀ gm gc : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (riemannLoweredField (I := I) gm gc)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma riemannLoweredCc_unitModel (g₀ gm gc : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 4 (riemannLoweredCc (I := I) (M := M) g₀ gm gc) x =
      Tensor0SSpace.toModel (riemannLoweredCovec (I := I) gm gc x) := by
  rw [unitModel]
  rw [show (riemannLoweredCc (I := I) (M := M) g₀ gm gc).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (riemannLoweredField (I := I) gm gc x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

set_option linter.unusedSectionVars false in
lemma riemannLoweredCc_unitModel_apply (g₀ gm gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (riemannLoweredCc (I := I) (M := M) g₀ gm gc) x m =
      gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1) := by
  rw [riemannLoweredCc_unitModel]
  rfl

def riemannLoweredBackgroundDifference (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ - riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma riemannLoweredBackgroundDifference_unitModel_apply
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x m =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3)) (m 1) -
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 3)) (m 1) := by
  have hsub : unitModel (I := I) (M := M) g₀ 4
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x m =
      unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m -
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x m := by
    simp only [riemannLoweredBackgroundDifference, unitModel]
    rw [show ((riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ -
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀).toSection x) =
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁).toSection x -
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀).toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  rw [hsub, riemannLoweredCc_unitModel_apply, riemannLoweredCc_unitModel_apply]

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) :=
  sorry

private lemma linearMap_trace_eq_orthoFrame_inner_sum (g₀ : SmoothRiemannianMetric I M)
    (x : M) (G : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x) G =
      ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (G (smoothOrthoFrame (I := I) g₀ x i x))
          (smoothOrthoFrame (I := I) g₀ x i x) := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g₀ x i x with hB_def
  have horth : ∀ i j, g₀.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g₀.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g₀.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (v : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr v j = g₀.inner x v (B j) := by
    intro v j
    conv_rhs => rw [← bB.sum_repr v]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    have hsimp : ∀ i, g₀.inner x (bB.repr v i • bB i) (B j) =
        bB.repr v i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hbB_coe i, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  rw [LinearMap.trace_eq_matrix_trace ℝ bB G]
  unfold Matrix.trace
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply, hrepr (G (bB i)) i, hbB_coe i]

private lemma interiorProduct_toModel_eval_lc (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

set_option linter.unusedSectionVars false in
private lemma toModel_om_eval_lc (x : M) (om : Tensor0SSpace 1 I x) (V : TangentSpace I x) :
    Tensor0SSpace.toModel om (fun _ : Fin 1 => (V : E)) =
      cotangentToDual (I := I) om V := by
  rw [cotangentToDual_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 6400000 in
theorem slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (appCcRS (I := I) (M := M) g₀ 0 4 2
            (cometricDoubleTraceField (I := I) g₀ 2)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) := by
  classical
  set W2 : SmoothCcTensor g₀ 0 2 :=
    appCcRS (I := I) (M := M) g₀ 0 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) with hW2_def
  have hW2unitModel : ∀ (x : M) (mm : Fin 2 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 2 W2 x mm =
        ricciTensor (I := I) g₁ x (mm 0) (mm 1) - ricciTensor (I := I) g₀ x (mm 0) (mm 1) := by
    intro x mm
    have hsec : (W2.toSection x) =
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
            cometricDoubleTraceFib (I := I) g₀ 2 x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x) := by
      rw [hW2_def, appCcRS_toSection, cometricDoubleTraceField_toSection]
    rw [unitModel]
    rw [show (W2.toSection x) (unitTensor (I := I) (M := M) x) =
        cometricDoubleTraceFib (I := I) g₀ 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x)
            (unitTensor (I := I) (M := M) x)) from by rw [hsec]; rfl]
    rw [cometricDoubleTraceFib_toModel]
    rw [modelDoubleTrace_apply]
    have hT : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x := rfl
    rw [hT]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x)
      (fun j => (mm j : E))]
    have hker : ∀ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
              (fun j => (mm j : E)))) =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
            (smoothOrthoFrame (I := I) g₀ x i x) -
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
              (smoothOrthoFrame (I := I) g₀ x i x) := by
      intro i
      rw [riemannLoweredBackgroundDifference_unitModel_apply]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hker i), Finset.sum_sub_distrib]
    have htr1 : (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
        ricciTensor (I := I) g₁ x (mm 0) (mm 1) := by
      rw [ricciTensor_apply (I := I) g₁ x (mm 0) (mm 1),
        linearMap_trace_eq_orthoFrame_inner_sum (I := I) (M := M) g₀ x
          (ricciEndo (I := I) g₁ x (mm 0) (mm 1))]
      rfl
    have htr0 : (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
        ricciTensor (I := I) g₀ x (mm 0) (mm 1) := by
      rw [ricciTensor_apply (I := I) g₀ x (mm 0) (mm 1),
        linearMap_trace_eq_orthoFrame_inner_sum (I := I) (M := M) g₀ x
          (ricciEndo (I := I) g₀ x (mm 0) (mm 1))]
      rfl
    rw [htr1, htr0]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x -
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  apply ContinuousLinearMap.ext
  intro om
  rw [ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x (ricEndoRaisedFib (I := I) g₀ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu_def
  have hupd : ∀ V : TangentSpace I x,
      (Function.update m 0 (show E from V)) = fun _ : Fin 1 => (V : E) := by
    intro V
    funext j
    fin_cases j
    simp [Function.update]
  have hsharp_pair : ∀ α : TangentSpace I x →ₗ[ℝ] ℝ,
      cotangentToDual (I := I) om (metricSharp (I := I) g₀ x α) = α u := by
    intro α
    rw [show cotangentToDual (I := I) om (metricSharp (I := I) g₀ x α) =
        cotangentToDualLinear (I := I) (x := x) om (metricSharp (I := I) g₀ x α) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om (metricSharp (I := I) g₀ x α), ← hu_def]
    exact inner_metricSharp_right (I := I) g₀ x α u
  have hLmix : Tensor0SSpace.toModel om
      (Function.update m 0 (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x (m 0))) =
      (ricciTensor (I := I) g₁ x (m 0)).toLinearMap u := by
    rw [show (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x (m 0)) =
        (show E from metricSharp (I := I) g₀ x
          (ricciTensor (I := I) g₁ x (m 0)).toLinearMap) from
      ricMixedSharpEndoFib_apply (I := I) (M := M) g₀ g₁ x (m 0)]
    rw [hupd, toModel_om_eval_lc, hsharp_pair]
  have hLraised : Tensor0SSpace.toModel om
      (Function.update m 0 (ricEndoRaisedFib (I := I) g₀ x (m 0))) =
      (ricciTensor (I := I) g₀ x (m 0)).toLinearMap u := by
    rw [show (ricEndoRaisedFib (I := I) g₀ x (m 0)) =
        (show E from metricSharp (I := I) g₀ x
          (ricciTensor (I := I) g₀ x (m 0)).toLinearMap) from
      ricEndoRaisedFib_apply (I := I) g₀ x (m 0)]
    rw [hupd, toModel_om_eval_lc, hsharp_pair]
  rw [hLmix, hLraised]
  rw [cometricRaiseSlot0Field_toSection]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
            (unitTensor (I := I) (M := M) x))) om) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
          (unitTensor (I := I) (M := M) x)) from
    cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [interiorProduct_toModel_eval_lc (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om) _ m]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2) x from rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
        (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
          (fun k : Fin 1 => (show E from m k)) : Fin 2 → TangentSpace I x)
          ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![(m 0 : TangentSpace I x), u] : Fin 2 → TangentSpace I x) from by
    funext i
    fin_cases i <;>
      simp [hu_def]]
  rw [hW2unitModel x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

end RiemannLoweredDifference

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck in
theorem rfns_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
                slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cPhi, hcPhi_nn, hcPhi⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  refine ⟨fun i => appCcGdiag (E := E) i * cPhi * (∑ l ∈ Finset.range (i + 1), CA l),
    fun i => mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i) hcPhi_nn)
      (Finset.sum_nonneg fun l _ => hCA_nn l), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace (I := I) (M := M) g₀ g₁]
  rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (appCcRS (I := I) (M := M) g₀ 0 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) i x]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1)
    (appCcRS (I := I) (M := M) g₀ 0 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) i x]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 0 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x) ?_
  have hAzero : ∀ m : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 4 2 (m + 1)
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) = 0 := by
    intro m
    rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 4 2 m
      (cometricDoubleTraceField (I := I) g₀ 2) x]
    rw [show covGrad (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2) =
        (0 : SmoothCcTensor g₀ 4 3) from
      cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2]
    rw [show iteratedCovGrad (I := I) g₀ 4 3 m (0 : SmoothCcTensor g₀ 4 3) =
        (0 : SmoothCcTensor g₀ 4 (3 + m)) from by
      induction m with
      | zero => rw [iteratedCovGrad_zero]
      | succ m' ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]]
    rw [show ((0 : SmoothCcTensor g₀ 4 (3 + m)).toSection x) =
        (0 : TensorRSSpace 4 (3 + m) I x) from by
      rw [SmoothCcTensor.toSection_zero]; rfl]
    exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ 4 (3 + m) x
  have hBmono : ∀ i' : ℕ,
      (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      ∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
    intro i'
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro l _ _
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
  have hterm : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
        (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      (if i' = 0 then
        cPhi * ∑ l ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
      else 0) := by
    intro i' _
    match i' with
    | 0 =>
        rw [if_pos rfl]
        have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 4 2 0
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤ cPhi := by
          rw [iteratedCovGrad_zero]
          exact hcPhi x
        refine mul_le_mul hA0 (hBmono 0) (Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _) hcPhi_nn
    | (m + 1) =>
        rw [if_neg (by omega)]
        rw [hAzero m, zero_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [Finset.sum_ite_eq' (Finset.range (i + 1)) 0]
  rw [if_pos (Finset.mem_range.mpr (by omega))]
  have hBgrid : (∑ l ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      (∑ l ∈ Finset.range (i + 1), CA l) *
        tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    calc (∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))
        ≤ ∑ l ∈ Finset.range (i + 1), CA l *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l := by
          refine Finset.sum_le_sum (fun l _ => ?_)
          have h := hCA g₁ T htie hδ_le hδ0 hbound l x
          rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
          exact h
      _ ≤ ∑ l ∈ Finset.range (i + 1), CA l *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l)
          exact tWindow_mono _ hb (by
            have := Finset.mem_range.mp hl
            omega)
      _ = (∑ l ∈ Finset.range (i + 1), CA l) *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
          rw [Finset.sum_mul]
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  calc appCcGdiag (E := E) i *
        (cPhi * ∑ l ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))
      ≤ appCcGdiag (E := E) i * (cPhi * ((∑ l ∈ Finset.range (i + 1), CA l) *
          tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i)) := by
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        exact mul_le_mul_of_nonneg_left hBgrid hcPhi_nn
    _ = appCcGdiag (E := E) i * cPhi * (∑ l ∈ Finset.range (i + 1), CA l) *
          tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
        ring

set_option linter.unusedSectionVars false in
private lemma diagonalGrid_assembly_arith (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (i : ℕ) (G : ℝ) (hG : 0 ≤ G)
    (CL CD cbg : ℕ → ℝ) (hCL_nn : ∀ k, 0 ≤ CL k) (hCD_nn : ∀ k, 0 ≤ CD k)
    (hcbg_nn : ∀ k, 0 ≤ cbg k)
    (t u ap : ℝ) (wj vl : ℕ → ℝ)
    (ht : t ≤ 2 * u + 2 * ap)
    (hu : u ≤ CL i * tWindow b i)
    (hap : ap ≤ G * ∑ j ∈ Finset.range (i + 1), wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l)
    (hwj : ∀ j, j ≤ i → wj j ≤ (2 * CL j + 2 * cbg j) * tWindow b j)
    (hvl_nn : ∀ l, 0 ≤ vl l)
    (hvl : ∀ l, l ≤ i → vl l ≤ CD l * Combinatorics.antidiagonalTupleGrid b l) :
    t ≤ (2 * CL i + 2 * (G * ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l)) * tWindow b i := by
  have hstep : ∀ j ∈ Finset.range (i + 1),
      wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l ≤
        ((2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
          CD l * tWindowMulConst j l) * tWindow b i := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj_le : j ≤ i := by omega
    have hcj_nn : 0 ≤ 2 * CL j + 2 * cbg j := by
      have := hCL_nn j
      have := hcbg_nn j
      linarith
    have h1 : wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l ≤
        ((2 * CL j + 2 * cbg j) * tWindow b j) * ∑ l ∈ Finset.range (i + 1 - j), vl l :=
      mul_le_mul_of_nonneg_right (hwj j hj_le) (Finset.sum_nonneg (fun l _ => hvl_nn l))
    refine le_trans h1 ?_
    have h2 : ∀ l ∈ Finset.range (i + 1 - j), tWindow b j * vl l ≤
        CD l * tWindowMulConst j l * tWindow b i := by
      intro l hl
      rw [Finset.mem_range] at hl
      have hl_le : l ≤ i := by omega
      have hjl : j + l ≤ i := by omega
      have h3 : tWindow b j * vl l ≤
          tWindow b j * (CD l * Combinatorics.antidiagonalTupleGrid b l) :=
        mul_le_mul_of_nonneg_left (hvl l hl_le) (tWindow_nonneg b hb j)
      refine le_trans h3 ?_
      rw [show tWindow b j * (CD l * Combinatorics.antidiagonalTupleGrid b l) =
          CD l * (tWindow b j * Combinatorics.antidiagonalTupleGrid b l) from by ring]
      calc CD l * (tWindow b j * Combinatorics.antidiagonalTupleGrid b l)
          ≤ CD l * (tWindowMulConst j l * tWindow b (j + l)) :=
            mul_le_mul_of_nonneg_left
              (tWindow_mul_antidiagonalTupleGrid_le b hb j l) (hCD_nn l)
        _ ≤ CD l * (tWindowMulConst j l * tWindow b i) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (tWindow_mono b hb hjl)
                (tWindowMulConst_nonneg j l)) (hCD_nn l)
        _ = CD l * tWindowMulConst j l * tWindow b i := by ring
    calc ((2 * CL j + 2 * cbg j) * tWindow b j) * ∑ l ∈ Finset.range (i + 1 - j), vl l
        = (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j), tWindow b j * vl l := by
          rw [mul_assoc, Finset.mul_sum]
      _ ≤ (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l * tWindow b i :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum h2) hcj_nn
      _ = ((2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l) * tWindow b i := by
          rw [← Finset.sum_mul]
          ring
  have hW_nn : 0 ≤ tWindow b i := tWindow_nonneg b hb i
  have hap2 : ap ≤ G * ((∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
      ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l) * tWindow b i) := by
    refine le_trans hap ?_
    refine mul_le_mul_of_nonneg_left ?_ hG
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    rw [← Finset.sum_mul]
  have hu2 : u ≤ CL i * tWindow b i := hu
  calc t ≤ 2 * u + 2 * ap := ht
    _ ≤ 2 * (CL i * tWindow b i) + 2 * (G * ((∑ j ∈ Finset.range (i + 1),
          (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l) * tWindow b i)) := by linarith
    _ = (2 * CL i + 2 * (G * ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
          ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l)) * tWindow b i := by
        ring

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ :=
    rfns_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀))
  refine ⟨fun i => 2 * CL i + 2 * (appCcGdiag (E := E) i *
      ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l),
    fun i => ?_, ?_⟩
  · have h1 : 0 ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
    have h2 : 0 ≤ ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l :=
      Finset.sum_nonneg (fun j _ => mul_nonneg
        (by have := hCL_nn j; have := hcbg_nn j; linarith)
        (Finset.sum_nonneg (fun l _ => mul_nonneg (hCD_nn l) (tWindowMulConst_nonneg j l))))
    have h3 := mul_nonneg h1 h2
    have h4 := hCL_nn i
    linarith
  · intro g₁ T htie δ hδ_le hδ0 hbound i x
    have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
      fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
    rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    have hsec : (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x =
        (iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x +
          (iteratedCovGrad (I := I) g₀ 1 1 i
            (appCcRS (I := I) (M := M) g₀ 1 1 1
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x := by
      rw [slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 1 1 i _ _, SmoothCcTensor.toSection_add]
      rfl
    have hLHS : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
                slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (appCcRS (I := I) (M := M) g₀ 1 1 1
                (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
                (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) := by
      rw [hsec]
      exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _
    have hu : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
        CL i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
      rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
      exact hCL g₁ T htie hδ_le hδ0 hbound i x
    have hap := rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 1 1 1
      (slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
      (slotInsertEndoCc (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x
    have hwj : ∀ j, j ≤ i → riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 1 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (2 * CL j + 2 * cbg j) *
          tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j := by
      intro j hj
      have hsplit : slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) =
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀)) +
          slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoRaisedField (I := I) (M := M) g₀) := by
        rw [sub_add_cancel]
      have hsec2 : (iteratedCovGrad (I := I) g₀ 1 1 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x =
          (iteratedCovGrad (I := I) g₀ 1 1 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
              slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x +
            (iteratedCovGrad (I := I) g₀ 1 1 j
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x := by
        conv_lhs => rw [hsplit]
        rw [iteratedCovGrad_add (I := I) g₀ 1 1 j _ _, SmoothCcTensor.toSection_add]
        rfl
      rw [hsec2]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + j) x _ _) ?_
      have hone : 1 ≤ tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
          ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j :=
        one_le_tWindow _ hb j
      have hb1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 1 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
              slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
          CL j * tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j := by
        rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x j]
        exact hCL g₁ T htie hδ_le hδ0 hbound j x
      have hb2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 1 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
          cbg j * tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j :=
        le_trans (hcbg j x) (le_mul_of_one_le_right (hcbg_nn j) hone)
      linarith
    have hvl : ∀ l, l ≤ i → riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
        CD l * Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) l := by
      intro l _
      rw [antidiagonalTupleGrid_eq_doubleSum (I := I) (M := M) g₀ T x l]
      exact hCD g₁ T htie hδ_le hδ0 hbound l x
    exact diagonalGrid_assembly_arith
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) hb i
      (appCcGdiag (E := E) i) (appCcGdiag_nonneg (E := E) i)
      CL CD cbg hCL_nn hCD_nn hcbg_nn
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x))
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (appCcRS (I := I) (M := M) g₀ 1 1 1
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x))
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 1 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x))
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x))
      hLHS hu hap hwj
      (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x _)
      hvl

section RiemannMixedBiContr

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.Integral.DivergenceTheorem

def riemannMixedKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => (g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q))
      map_add' := fun v0 v0' => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_add v0 v0',
          ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, map_add]
      map_smul' := fun c v0 => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_smul c v0,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul,
          RingHom.id_apply] }

set_option linter.unusedSectionVars false in
@[simp] theorem riemannMixedKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    riemannMixedKernelBilin (I := I) g₀ g₁ x p q v0 v1 =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [riemannMixedKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]

def riemannMixedSummandFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (riemannMixedKernelBilin (I := I) g₀ g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

set_option linter.unusedSectionVars false in
@[simp] theorem riemannMixedSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannMixedSummandFib (I := I) g₀ g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) p q) (v 1) := by
  rw [riemannMixedSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

def riemannMixedBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x)

set_option linter.unusedSectionVars false in
theorem riemannMixedBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (B a x) (B b x)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [riemannMixedBiContrFibFixedFrame, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, riemannMixedSummandFib_toModel]
  ring

set_option linter.unusedSectionVars false in
theorem mixedKernelScalar_global (g₀ g₁ : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g₁) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) g₁) hY hp hq
  have hcongr : (fun x : M => g₀.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => g₀.inner x (riemannSec (LeviCivita (I := I) g₁) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₀
    ⟨fun b => riemannSec (LeviCivita (I := I) g₁) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

set_option linter.unusedSectionVars false in
theorem riemannMixedKernelBilin_homSection_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x))
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x) (Y x))
  intro W
  have h_scalar := mixedKernelScalar_global (I := I) g₀ g₁ Y.contMDiff W.contMDiff hp hq
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change riemannMixedKernelBilin (I := I) g₀ g₁ y (p y) (q y) (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [riemannMixedKernelBilin_apply]
  rfl

set_option linter.unusedSectionVars false in
theorem riemannMixedBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => riemannMixedKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))
      (riemannMixedKernelBilin_homSection_contMDiff (I := I) g₀ g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x)
          (riemannMixedKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b
    with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [riemannMixedBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

set_option linter.unusedSectionVars false in
theorem riemannMixedBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x)
  intro Y
  exact riemannMixedBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₀ g₁ B hB Y

def frameRiemannMixedKernel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₀.inner x).flip v1 |>.comp
        ((riemannOp (LeviCivita (I := I) g₁) x v0 p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (LeviCivita (I := I) g₁) x v0).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (LeviCivita (I := I) g₁) x v0).map_smul c p, map_smul] }

set_option linter.unusedSectionVars false in
theorem frameRiemannMixedKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameRiemannMixedKernel (I := I) g₀ g₁ x v0 v1 p q =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [frameRiemannMixedKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

def riemannMixedBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x) x

set_option linter.unusedSectionVars false in
theorem riemannMixedBiContrFib_eq_fixedFrame_on_nbhd (g₀ g₁ : SmoothRiemannianMetric I M)
    (x₀ : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ y =
      riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [riemannMixedBiContrFib, riemannMixedBiContrFibFixedFrame_toModel,
    riemannMixedBiContrFibFixedFrame_toModel]
  congr 1
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner y (riemannOp (LeviCivita (I := I) g₁) y (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRiemannMixedKernel (I := I) g₀ g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRiemannMixedKernel_apply (I := I) g₀ g₁ y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₀ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₀ y
    (frameRiemannMixedKernel (I := I) g₀ g₁ y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₀ y a y)
    (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₀ x₀ hy i j)

set_option linter.unusedSectionVars false in
theorem riemannMixedBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₀ x₀) x))) x₀ :=
    riemannMixedBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₀ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (riemannMixedBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ x₀ hy))

def ricciArmOrder0RiemannMixedCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x))
      contMDiff_toFun := riemannMixedBiContrFib_contMDiff (I := I) (M := M) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
theorem ricciArmOrder0RiemannMixedCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem ricciArmOrder0RiemannMixedCoeff_self (g₀ : SmoothRiemannianMetric I M) :
    ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₀ =
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₀).toSection x) D =
      riemannMixedBiContrFib (I := I) (M := M) g₀ g₀ x D from rfl]
  rw [show ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) D =
      riemannBiContrFib (I := I) g₀ x D from rfl]
  rw [riemannMixedBiContrFib, riemannBiContrFib, riemannMixedBiContrFibFixedFrame_toModel,
    riemannBiContrFibFixedFrame_toModel]

end RiemannMixedBiContr

theorem rfns_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_le_loweredDifference
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) :=
  sorry

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannG1LoweringDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) :=
  sorry

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannCoeff_metricFactorTelescope_traceConversion_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            (∑ n ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x)) *
            ∑ l ∈ Finset.range (i + 1 - j),
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) :=
  sorry

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    rfns_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_le_loweredDifference
      (I := I) (M := M) g₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => CB i * CA i, fun i => mul_nonneg (hCB_nn i) (hCA_nn i), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  refine le_trans (hCB g₁ i x) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hCA g₁ T htie hδ_le hδ0 hbound i x) (hCB_nn i)

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannCoeff_metricFactorTelescope_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    rfns_iteratedCovGrad_riemannCoeff_metricFactorTelescope_traceConversion_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    rfns_iteratedCovGrad_riemannG1LoweringDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  refine ⟨fun i => CC i * ∑ j ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
      (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j),
    fun i => mul_nonneg (hCC_nn i) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ =>
      add_nonneg (by have := hcbg_nn l; linarith)
        (mul_nonneg (by have := hCA_nn l; have := hC1_nn l; linarith)
          (tWindowMulConst_nonneg l j))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hP : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
      2 * cbg l + 2 * CA l * tWindow b l := by
    intro l
    have hsplit : riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
        riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ +
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀ := by
      rw [riemannLoweredBackgroundDifference, sub_add_cancel]
    have hsec : (iteratedCovGrad (I := I) g₀ 0 4 l
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x := by
      rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + l) x _ _) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CA l * tWindow b l := by
      have h := hCA g₁ T htie hδ_le hδ0 hbound l x
      rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
      exact h
    have h2 := hcbg l x
    linarith
  have hQ : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
      C1 l * tWindow b l := by
    intro l
    have h := hC1 g₁ T htie hδ_le hδ0 hbound l x
    rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
    exact h
  refine le_trans (hCC g₁ T htie hδ_le hδ0 hbound i x) ?_
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  have hjl : ∀ j ∈ Finset.range (i + 1),
      (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ∏ m : Fin n, b (e m)) *
        (∑ l ∈ Finset.range (i + 1 - j),
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x))) ≤
      (∑ l ∈ Finset.range (i + 1),
        (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j)) * tWindow b i := by
    intro j hj
    have hjle : j ≤ i := by
      have := Finset.mem_range.mp hj
      omega
    have hgrid_eq : (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j, ∏ m : Fin n, b (e m)) =
        Combinatorics.antidiagonalTupleGrid b j := rfl
    rw [hgrid_eq, mul_comm (Combinatorics.antidiagonalTupleGrid b j)]
    rw [Finset.sum_mul]
    have hterm : ∀ l ∈ Finset.range (i + 1 - j),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) *
          Combinatorics.antidiagonalTupleGrid b j ≤
        (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j) * tWindow b i := by
      intro l hl
      have hlle : l ≤ i - j := by
        have := Finset.mem_range.mp hl
        omega
      have hlj : l + j ≤ i := by omega
      have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b j :=
        Combinatorics.antidiagonalTupleGrid_nonneg b hb j
      have hgrid_le : Combinatorics.antidiagonalTupleGrid b j ≤ tWindow b i :=
        antidiagonalTupleGrid_le_tWindow b hb (by omega)
      have hsum_le : (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) ≤
          2 * cbg l + (2 * CA l + C1 l) * tWindow b l := by
        have h1 := hP l
        have h2 := hQ l
        have hW_nn : 0 ≤ tWindow b l := tWindow_nonneg b hb l
        nlinarith [hCA_nn l, hC1_nn l]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) *
            Combinatorics.antidiagonalTupleGrid b j
          ≤ (2 * cbg l + (2 * CA l + C1 l) * tWindow b l) *
              Combinatorics.antidiagonalTupleGrid b j :=
            mul_le_mul_of_nonneg_right hsum_le hgrid_nn
        _ = 2 * cbg l * Combinatorics.antidiagonalTupleGrid b j +
              (2 * CA l + C1 l) * (tWindow b l * Combinatorics.antidiagonalTupleGrid b j) := by
            ring
        _ ≤ 2 * cbg l * tWindow b i +
              (2 * CA l + C1 l) * (tWindowMulConst l j * tWindow b (l + j)) := by
            have hmul := tWindow_mul_antidiagonalTupleGrid_le b hb l j
            have hnn1 : 0 ≤ 2 * cbg l := by have := hcbg_nn l; linarith
            have hnn2 : 0 ≤ 2 * CA l + C1 l := by
              have := hCA_nn l; have := hC1_nn l; linarith
            exact add_le_add (mul_le_mul_of_nonneg_left hgrid_le hnn1)
              (mul_le_mul_of_nonneg_left hmul hnn2)
        _ ≤ 2 * cbg l * tWindow b i +
              (2 * CA l + C1 l) * (tWindowMulConst l j * tWindow b i) := by
            have hnn2 : 0 ≤ 2 * CA l + C1 l := by
              have := hCA_nn l; have := hC1_nn l; linarith
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (tWindow_mono b hb hlj)
                (tWindowMulConst_nonneg l j)) hnn2)
        _ = (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j) * tWindow b i := by
            ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (tWindow_nonneg b hb i)
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro l _ _
    exact add_nonneg (by have := hcbg_nn l; linarith)
      (mul_nonneg (by have := hCA_nn l; have := hC1_nn l; linarith)
        (tWindowMulConst_nonneg l j))
  calc CC i * ∑ j ∈ Finset.range (i + 1),
        (∑ n ∈ Finset.range (j + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
            ∏ m : Fin n, b (e m)) *
          ∑ l ∈ Finset.range (i + 1 - j),
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                    riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x))
      ≤ CC i * ∑ j ∈ Finset.range (i + 1),
          (∑ l ∈ Finset.range (i + 1),
            (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j)) * tWindow b i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hjl) (hCC_nn i)
    _ = CC i * (∑ j ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
          (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j)) * tWindow b i := by
        rw [← Finset.sum_mul]
        ring

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    rfns_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    rfns_iteratedCovGrad_riemannCoeff_metricFactorTelescope_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => 2 * Cb i + 2 * Ca i,
    fun i => by have := hCa_nn i; have := hCb_nn i; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  have hsplit : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ =
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁) +
      (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) := by
    rw [sub_add_sub_cancel]
  have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x =
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x := by
    rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
      Cb i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    exact hCb g₁ T htie hδ_le hδ0 hbound i x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
      Ca i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    exact hCa g₁ T htie hδ_le hδ0 hbound i x
  rw [show (2 * Cb i + 2 * Ca i) *
      tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i =
      2 * (Cb i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i) +
        2 * (Ca i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i) from by ring]
  linarith

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
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2 ≤ K i := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    curvDiffGrid_integral_ballUniform_window (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hkle : ∀ k ∈ Finset.range (i + 3), k ≤ a + 2 := by
      intro k hk
      rw [Finset.mem_range] at hk
      omega
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k (hkle k hk)).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k (hkle k hk)).1)]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun k hk => (hKg P hPball k (hkle k hk)).2)) (hC_nn i)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    simpa using mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))


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
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    curvDiffGrid_integral_ballUniform_window (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hkle : ∀ k ∈ Finset.range (i + 3), k ≤ a + 2 := by
      intro k hk
      rw [Finset.mem_range] at hk
      omega
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k (hkle k hk)).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k (hkle k hk)).1)]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun k hk => (hKg P hPball k (hkle k hk)).2)) (hC_nn i)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    simpa using mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))


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
