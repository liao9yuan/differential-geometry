import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckArm0BackgroundCurvatureCoeffField

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (ricciArmOrder0RiemannCoeff ricciArmOrder0CurvCoeff coeffMixedRmField coeffMixedRmField_appCc_eq
   coeffMixedCurvField coeffMixedCurvField_appCc_eq bgRicEndoRaisedFib bgRicEndoRaisedFib_apply)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def realizedUnitCc (g₀ : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SSpace 2 I x) : SmoothCcTensor g₀ 0 2 where
  toSection :=
    letI : NormedAddCommGroup (TensorRSModel 0 2 ℝ E) :=
      Tensor0SBundle.tensorRSModel_normedAddCommGroup 0 2
    letI : NormedSpace ℝ (TensorRSModel 0 2 ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace 0 2
    Classical.choose (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel 0 2 ℝ E)
      (V := fun z : M => TensorRSSpace 0 2 I z) (n := (⊤ : ℕ∞)) x
      (tensor0SAsRS (I := I) (M := M) x D))
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
private theorem realizedUnitCc_toSection_eq (g₀ : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SSpace 2 I x) :
    (realizedUnitCc (I := I) (M := M) g₀ x D).toSection x = tensor0SAsRS (I := I) (M := M) x D :=
  letI : NormedAddCommGroup (TensorRSModel 0 2 ℝ E) :=
    Tensor0SBundle.tensorRSModel_normedAddCommGroup 0 2
  letI : NormedSpace ℝ (TensorRSModel 0 2 ℝ E) := Tensor0SBundle.tensorRSModel_normedSpace 0 2
  Classical.choose_spec (ContMDiffSection.exists_eq_at (I := I) (F := TensorRSModel 0 2 ℝ E)
    (V := fun z : M => TensorRSSpace 0 2 I z) (n := (⊤ : ℕ∞)) x
    (tensor0SAsRS (I := I) (M := M) x D))

set_option backward.isDefEq.respectTransparency false in
theorem smoothCcTensor22_ext_of_unitModel_appCc (g₀ : SmoothRiemannianMetric I M)
    {S S' : SmoothCcTensor g₀ 2 2}
    (h : ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2 S W) x v =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
          (appCc (I := I) (M := M) g₀ 2 2 S' W) x v) :
    S = S' := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change (S.toSection x : Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x)
      = (S'.toSection x : Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x)
  apply ContinuousLinearMap.ext
  intro D
  have hscal : (tensor00Scalar (I := I) (M := M) x)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I) (M := M) x)
        = 1 := by
    rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
    rfl
  have hWs : (realizedUnitCc (I := I) (M := M) g₀ x D).toSection x
      = tensor0SAsRS (I := I) (M := M) x D := realizedUnitCc_toSection_eq (I := I) (M := M) g₀ x D
  have hWval : ((realizedUnitCc (I := I) (M := M) g₀ x D).toSection x :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x)
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I) (M := M) x)
        = D := by
    rw [show ((realizedUnitCc (I := I) (M := M) g₀ x D).toSection x :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x)
        = (tensor0SAsRS (I := I) (M := M) x D : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x)
        from by rw [hWs]]
    have happ := tensor0SAsRS_apply (I := I) (M := M) x D
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitTensor (I := I) (M := M) x)
    simp only [hscal, one_smul] at happ
    exact happ
  rw [← hWval]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hv := h (realizedUnitCc (I := I) (M := M) g₀ x D) x v
  simpa [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel] using hv

theorem exists_coeffMixedRm_pinned (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ mixed : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 mixed W) x v =
          2 * ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                (smoothOrthoFrame (I := I) g₁ x a' x)
                (smoothOrthoFrame (I := I) g₁ x b' x)) (v 1) *
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
                (I := I) (M := M) g₀ 2 W x
                (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a' x
                  else smoothOrthoFrame (I := I) g₁ x b' x) :=
  ⟨coeffMixedRmField (I := I) (M := M) g₀ g₁ g₀,
    coeffMixedRmField_appCc_eq (I := I) (M := M) g₀ g₁ g₀⟩

noncomputable def coeffMixedRm (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 :=
  Classical.choose (exists_coeffMixedRm_pinned (I := I) (M := M) g₀ g₁)

theorem coeffMixedRm_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (coeffMixedRm (I := I) (M := M) g₀ g₁) W) x v =
      2 * ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
            (smoothOrthoFrame (I := I) g₁ x a' x)
            (smoothOrthoFrame (I := I) g₁ x b' x)) (v 1) *
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
            (I := I) (M := M) g₀ 2 W x
            (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a' x
              else smoothOrthoFrame (I := I) g₁ x b' x) :=
  Classical.choose_spec (exists_coeffMixedRm_pinned (I := I) (M := M) g₀ g₁) W x v

theorem coeffMixedRm_eq_field (g₀ g₁ : SmoothRiemannianMetric I M) :
    coeffMixedRm (I := I) (M := M) g₀ g₁ = coeffMixedRmField (I := I) (M := M) g₀ g₁ g₀ := by
  apply smoothCcTensor22_ext_of_unitModel_appCc (I := I) (M := M) g₀
  intro W x v
  rw [coeffMixedRm_appCc_eq, coeffMixedRmField_appCc_eq]

theorem exists_coeffMixedCurv_pinned (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∃ mixed : SmoothCcTensor g₀ 2 2,
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
            (appCc (I := I) (M := M) g₀ 2 2 mixed W) x v =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
              (I := I) (M := M) g₀ 2 W x
              (Function.update v 0
                (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
                  (ricciTensor (I := I) g₀ x (v 0)).toLinearMap)) +
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
              (I := I) (M := M) g₀ 2 W x
              (Function.update v 1
                (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
                  (ricciTensor (I := I) g₀ x (v 1)).toLinearMap)) := by
  refine ⟨coeffMixedCurvField (I := I) (M := M) g₀ g₁ g₀, fun W x v => ?_⟩
  rw [coeffMixedCurvField_appCc_eq (I := I) (M := M) g₀ g₁ g₀ W x v]
  simp only [bgRicEndoRaisedFib_apply]

noncomputable def coeffMixedCurv (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 :=
  Classical.choose (exists_coeffMixedCurv_pinned (I := I) (M := M) g₀ g₁)

theorem coeffMixedCurv_appCc_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x) :
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
        (appCc (I := I) (M := M) g₀ 2 2 (coeffMixedCurv (I := I) (M := M) g₀ g₁) W) x v =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
          (I := I) (M := M) g₀ 2 W x
          (Function.update v 0
            (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
              (ricciTensor (I := I) g₀ x (v 0)).toLinearMap)) +
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
          (I := I) (M := M) g₀ 2 W x
          (Function.update v 1
            (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
              (ricciTensor (I := I) g₀ x (v 1)).toLinearMap)) :=
  Classical.choose_spec (exists_coeffMixedCurv_pinned (I := I) (M := M) g₀ g₁) W x v

theorem coeffMixedCurv_eq_field (g₀ g₁ : SmoothRiemannianMetric I M) :
    coeffMixedCurv (I := I) (M := M) g₀ g₁ = coeffMixedCurvField (I := I) (M := M) g₀ g₁ g₀ := by
  apply smoothCcTensor22_ext_of_unitModel_appCc (I := I) (M := M) g₀
  intro W x v
  rw [coeffMixedCurv_appCc_eq, coeffMixedCurvField_appCc_eq]
  simp only [bgRicEndoRaisedFib_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem appCcRS_fixedPhi_perOrder_rfns_grid
    (g₀ : SmoothRiemannianMetric I M) (Φ : SmoothCcTensor g₀ 2 2) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (Ψ : SmoothCcTensor g₀ 2 2) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (appCcRS (I := I) (M := M) g₀ 2 2 2 Φ Ψ)).toSection x) ≤
          K i * ∑ l ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 2 l Ψ).toSection x) := by
  classical
  choose Ksup hKsup_nn hKsup using fun i =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i Φ)
  refine ⟨fun i => appCcGdiag (E := E) i * ∑ a ∈ Finset.range (i + 1), Ksup a,
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun a _ => hKsup_nn a), ?_⟩
  intro Ψ i x
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 2 2 2 Φ Ψ x) ?_
  set S : ℝ := ∑ l ∈ Finset.range (i + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 2 l Ψ).toSection x) with hS
  have hS_nn : 0 ≤ S :=
    Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _
  have hgrid : ∑ a ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + a) x
            ((iteratedCovGrad (I := I) g₀ 2 2 a Φ).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 2 l Ψ).toSection x) ≤
      (∑ a ∈ Finset.range (i + 1), Ksup a) * S := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hΨsub : ∑ l ∈ Finset.range (i + 1 - a),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 2 l Ψ).toSection x) ≤ S := by
      rw [hS]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun l _ _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _)
      intro l hl
      simp only [Finset.mem_range] at hl ⊢; omega
    exact mul_le_mul (hKsup a x) hΨsub
      (Finset.sum_nonneg fun l _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + l) x _)
      (hKsup_nn a)
  calc appCcGdiag (E := E) i * ∑ a ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + a) x
              ((iteratedCovGrad (I := I) g₀ 2 2 a Φ).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - a),
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 2 2 l Ψ).toSection x)
      ≤ appCcGdiag (E := E) i * ((∑ a ∈ Finset.range (i + 1), Ksup a) * S) :=
        mul_le_mul_of_nonneg_left hgrid (appCcGdiag_nonneg (E := E) i)
    _ = (appCcGdiag (E := E) i * ∑ a ∈ Finset.range (i + 1), Ksup a) * S := by ring

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
theorem coeffMixedRmField_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (coeffMixedRmField (I := I) (M := M) g₀ g₁ g₀
                - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) :=
  sorry

theorem coeffMixedCurvField_sub_background_eq_appCcRS_add_reindexSwap
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Φ : SmoothCcTensor g₀ 2 2, ∀ (g₁ : SmoothRiemannianMetric I M),
      coeffMixedCurvField (I := I) (M := M) g₀ g₁ g₀
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀ =
        appCcRS (I := I) (M := M) g₀ 2 2 2 Φ (gInvDiffSlotCoeff (I := I) g₀ g₁) +
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen
              (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (appCcRS (I := I) (M := M) g₀ 2 2 2 Φ (gInvDiffSlotCoeff (I := I) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
theorem coeffMixedCurvField_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (coeffMixedCurvField (I := I) (M := M) g₀ g₁ g₀
                - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 2 2 j
                (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) := by
  classical
  obtain ⟨Φ, heq⟩ :=
    coeffMixedCurvField_sub_background_eq_appCcRS_add_reindexSwap (I := I) (M := M) g₀
  obtain ⟨K, hK_nn, hK⟩ := appCcRS_fixedPhi_perOrder_rfns_grid (I := I) (M := M) g₀ Φ
  refine ⟨fun i => 4 * K i, fun i => by have := hK_nn i; positivity, ?_⟩
  intro g₁ i x
  set A : SmoothCcTensor g₀ 2 2 :=
    appCcRS (I := I) (M := M) g₀ 2 2 2 Φ (gInvDiffSlotCoeff (I := I) g₀ g₁) with hA
  set B : SmoothCcTensor g₀ 2 2 :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoeffGen (I := I) (M := M) g₀ 2 2
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) A)
      (Equiv.swap (0 : Fin 2) 1) with hB
  set G : ℝ := ∑ j ∈ Finset.range (i + 1),
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) with hG
  have hG_nn : 0 ≤ G :=
    Finset.sum_nonneg fun j _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + j) x _
  have hAbound : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i A).toSection x) ≤ K i * G := by
    rw [hA, hG]; exact hK (gInvDiffSlotCoeff (I := I) g₀ g₁) i x
  have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i B).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i A).toSection x) := by
    rw [hB]
    exact rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
      (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1) A i x
  have hLHS : (iteratedCovGrad (I := I) g₀ 2 2 i
        (coeffMixedCurvField (I := I) (M := M) g₀ g₁ g₀
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x =
      (iteratedCovGrad (I := I) g₀ 2 2 i A).toSection x
        + (iteratedCovGrad (I := I) g₀ 2 2 i B).toSection x := by
    rw [heq g₁, ← hA, ← hB, iteratedCovGrad_add, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply]
  rw [hLHS]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 2 i A).toSection x)
    ((iteratedCovGrad (I := I) g₀ 2 2 i B).toSection x)) ?_
  rw [hswap]
  nlinarith [hAbound, hG_nn, hK_nn i]

set_option linter.unusedVariables false in
theorem coeffMixedRmField_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (coeffMixedRmField (I := I) (M := M) g₀ g₁ g₀
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
  obtain ⟨C, hC_nn, hP⟩ :=
    coeffMixedRmField_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hF_int : MeasureTheory.Integrable
      (fun x => C i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))).const_mul (C i)
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (coeffMixedRmField (I := I) (M := M) g₀ g₁ g₀
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
    (fun x => C i * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
    hF_int (fun x => hP g₁ P hδ_le hδ htie hPball i hi x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
    (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 2 (2 + j)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))).symm

theorem coeffMixedCurvField_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (coeffMixedCurvField (I := I) (M := M) g₀ g₁ g₀
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 := by
  obtain ⟨C, hC_nn, hP⟩ :=
    coeffMixedCurvField_sub_background_perOrder_rfns_le_gInvDiffSlotCoeff_rfns (I := I) (M := M) g₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ i
  have hF_int : MeasureTheory.Integrable
      (fun x => C i * ∑ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 1))
      (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
        (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))).const_mul (C i)
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (coeffMixedCurvField (I := I) (M := M) g₀ g₁ g₀
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))
    (fun x => C i * ∑ j ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x))
    hF_int (fun x => hP g₁ i x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 1))
    (fun j _ => integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 2 (2 + j)
      (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [SmoothCcTensor.norm_def (I := I) (M := M)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 2 (2 + j)
    (iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁))).symm

set_option linter.unusedVariables false in
theorem coeffMixedRmField_sub_g0coeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C2 : ℕ → ℝ, (∀ i, 0 ≤ C2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (coeffMixedRmField (I := I) (M := M) g₀ g₁ g₀
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C2 i := by
  obtain ⟨K, hK_nn, hK⟩ := gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic
    (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C, hC_nn, hC⟩ :=
    coeffMixedRmField_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => C i * ∑ j ∈ Finset.range (i + 1), K j,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun j _ => hK_nn j), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (coeffMixedRmField (I := I) (M := M) g₀ g₁ g₀
            - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
      ≤ C i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
        hC g₁ P hδ_le hδ htie hPball i hi
    _ ≤ C i * ∑ j ∈ Finset.range (i + 1), K j := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (hC_nn i)
        intro j hj
        exact hK g₁ P hδ_le hδ htie hPball j
          (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi)

set_option linter.unusedVariables false in
theorem coeffMixedCurvField_sub_g0coeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C2 : ℕ → ℝ, (∀ i, 0 ≤ C2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (coeffMixedCurvField (I := I) (M := M) g₀ g₁ g₀
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C2 i := by
  obtain ⟨K, hK_nn, hK⟩ := gInvDiffSlotCoeff_perOrder_l2_ballUniform_generic
    (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C, hC_nn, hC⟩ :=
    coeffMixedCurvField_sub_background_jetL2_le_gInvDiffSlotCoeff_jetL2 (I := I) (M := M) g₀
  refine ⟨fun i => C i * ∑ j ∈ Finset.range (i + 1), K j,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun j _ => hK_nn j), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  calc ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (coeffMixedCurvField (I := I) (M := M) g₀ g₁ g₀
            - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
      ≤ C i * ∑ j ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 j (gInvDiffSlotCoeff (I := I) g₀ g₁)‖ ^ 2 :=
        hC g₁ i
    _ ≤ C i * ∑ j ∈ Finset.range (i + 1), K j := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (hC_nn i)
        intro j hj
        exact hK g₁ P hδ_le hδ htie hPball j
          (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi)

set_option linter.unusedVariables false in
theorem coeffMixedRm_sub_g1coeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C1 : ℕ → ℝ, (∀ i, 0 ≤ C1 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - coeffMixedRm (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ C1 i :=
  sorry

set_option linter.unusedVariables false in
theorem coeffMixedRm_sub_g0coeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C2 : ℕ → ℝ, (∀ i, 0 ≤ C2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (coeffMixedRm (I := I) (M := M) g₀ g₁
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C2 i := by
  obtain ⟨C2, hC2nn, hbd⟩ :=
    coeffMixedRmField_sub_g0coeff_perOrder_l2_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨C2, hC2nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  rw [coeffMixedRm_eq_field (I := I) (M := M) g₀ g₁]
  exact hbd g₁ P hδ_le hδ htie hPball i hi

set_option linter.unusedVariables false in
theorem coeffMixedCurv_sub_g1coeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C1 : ℕ → ℝ, (∀ i, 0 ≤ C1 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
              - coeffMixedCurv (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ C1 i :=
  sorry

set_option linter.unusedVariables false in
theorem coeffMixedCurv_sub_g0coeff_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C2 : ℕ → ℝ, (∀ i, 0 ≤ C2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (coeffMixedCurv (I := I) (M := M) g₀ g₁
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C2 i := by
  obtain ⟨C2, hC2nn, hbd⟩ :=
    coeffMixedCurvField_sub_g0coeff_perOrder_l2_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨C2, hC2nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  rw [coeffMixedCurv_eq_field (I := I) (M := M) g₀ g₁]
  exact hbd g₁ P hδ_le hδ htie hPball i hi

set_option linter.unusedVariables false in
theorem ricciArmOrder0RiemannCoeff_frameSplit_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C1 C2 : ℕ → ℝ, (∀ i, 0 ≤ C1 i) ∧ (∀ i, 0 ≤ C2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∃ mixed : SmoothCcTensor g₀ 2 2,
          (∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
                (appCc (I := I) (M := M) g₀ 2 2 mixed W) x v =
              2 * ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
                g₁.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0)
                    (smoothOrthoFrame (I := I) g₁ x a' x)
                    (smoothOrthoFrame (I := I) g₁ x b' x)) (v 1) *
                  DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
                    (I := I) (M := M) g₀ 2 W x
                    (fun j => if j = 0 then smoothOrthoFrame (I := I) g₁ x a' x
                      else smoothOrthoFrame (I := I) g₁ x b' x)) ∧
          ∀ (i : ℕ), i ≤ a →
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ - mixed)‖ ^ 2 ≤ C1 i ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (mixed - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C2 i := by
  obtain ⟨C1, hC1nn, hb1⟩ :=
    coeffMixedRm_sub_g1coeff_perOrder_l2_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2, hC2nn, hb2⟩ :=
    coeffMixedRm_sub_g0coeff_perOrder_l2_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨C1, C2, hC1nn, hC2nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball
  refine ⟨coeffMixedRm (I := I) (M := M) g₀ g₁,
    coeffMixedRm_appCc_eq (I := I) (M := M) g₀ g₁, ?_⟩
  intro i hi
  exact ⟨hb1 g₁ P hδ_le hδ htie hPball i hi, hb2 g₁ P hδ_le hδ htie hPball i hi⟩

set_option linter.unusedVariables false in
theorem ricciArmOrder0CurvCoeff_frameSplit_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C1 C2 : ℕ → ℝ, (∀ i, 0 ≤ C1 i) ∧ (∀ i, 0 ≤ C2 i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∃ mixed : SmoothCcTensor g₀ 2 2,
          (∀ (W : SmoothCcTensor g₀ 0 2) (x : M) (v : Fin 2 → TangentSpace I x),
            DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel (I := I) (M := M) g₀ 2
                (appCc (I := I) (M := M) g₀ 2 2 mixed W) x v =
              DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
                  (I := I) (M := M) g₀ 2 W x
                  (Function.update v 0
                    (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
                      (ricciTensor (I := I) g₀ x (v 0)).toLinearMap)) +
                DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel
                  (I := I) (M := M) g₀ 2 W x
                  (Function.update v 1
                    (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I) g₁ x
                      (ricciTensor (I := I) g₀ x (v 1)).toLinearMap))) ∧
          ∀ (i : ℕ), i ≤ a →
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ - mixed)‖ ^ 2 ≤ C1 i ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (mixed - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C2 i := by
  obtain ⟨C1, hC1nn, hb1⟩ :=
    coeffMixedCurv_sub_g1coeff_perOrder_l2_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨C2, hC2nn, hb2⟩ :=
    coeffMixedCurv_sub_g0coeff_perOrder_l2_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨C1, C2, hC1nn, hC2nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball
  refine ⟨coeffMixedCurv (I := I) (M := M) g₀ g₁,
    coeffMixedCurv_appCc_eq (I := I) (M := M) g₀ g₁, ?_⟩
  intro i hi
  exact ⟨hb1 g₁ P hδ_le hδ htie hPball i hi, hb2 g₁ P hδ_le hδ htie hPball i hi⟩

set_option linter.unusedVariables false in
theorem ricciArmOrder0RiemannCoeff_sub_background_perOrder_l2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C i := by
  obtain ⟨C1, C2, hC1nn, hC2nn, hbd⟩ :=
    ricciArmOrder0RiemannCoeff_frameSplit_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (C1 i + C2 i),
    fun i => by have h1 := hC1nn i; have h2 := hC2nn i; linarith, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  obtain ⟨mixed, _hpin, hpieces⟩ := hbd g₁ P hδ_le hδ htie hPball
  obtain ⟨hp1, hp2⟩ := hpieces i hi
  have hsplit : (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
      = (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ - mixed)
        + (mixed - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) := by abel
  have e1 := iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ - mixed)
    (mixed - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
  rw [hsplit, e1]
  set u := iteratedCovGrad (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ - mixed) with hu
  set v := iteratedCovGrad (I := I) g₀ 2 2 i
    (mixed - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) with hv
  clear_value u v
  exact sq_le_two_add ‖u + v‖ ‖u‖ ‖v‖ (C1 i) (C2 i)
    (norm_nonneg _) (norm_nonneg u) (norm_nonneg v) (norm_add_le u v) hp1 hp2

set_option linter.unusedVariables false in
theorem ricciArmOrder0CurvCoeff_sub_background_perOrder_l2_ballUniform_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ C i := by
  obtain ⟨C1, C2, hC1nn, hC2nn, hbd⟩ :=
    ricciArmOrder0CurvCoeff_frameSplit_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (C1 i + C2 i),
    fun i => by have h1 := hC1nn i; have h2 := hC2nn i; linarith, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  obtain ⟨mixed, _hpin, hpieces⟩ := hbd g₁ P hδ_le hδ htie hPball
  obtain ⟨hp1, hp2⟩ := hpieces i hi
  have hsplit : (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
      = (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ - mixed)
        + (mixed - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) := by abel
  have e1 := iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ - mixed)
    (mixed - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
  rw [hsplit, e1]
  set u := iteratedCovGrad (I := I) g₀ 2 2 i
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ - mixed) with hu
  set v := iteratedCovGrad (I := I) g₀ 2 2 i
    (mixed - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) with hv
  clear_value u v
  exact sq_le_two_add ‖u + v‖ ‖u‖ ‖v‖ (C1 i) (C2 i)
    (norm_nonneg _) (norm_nonneg u) (norm_nonneg v) (norm_add_le u v) hp1 hp2

set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in
theorem ricciArmOrder0BaseCoeff_perOrder_l2_ballUniform_generic
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
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ K i := by
  obtain ⟨CR, hCR_nn, hCR⟩ :=
    ricciArmOrder0RiemannCoeff_sub_background_perOrder_l2_ballUniform_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    ricciArmOrder0CurvCoeff_sub_background_perOrder_l2_ballUniform_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 3 * (CR i + CC i +
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2), ?_, ?_⟩
  · intro i
    have h1 := hCR_nn i
    have h2 := hCC_nn i
    have h3 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
    change (0 : ℝ) ≤ 3 * (CR i + CC i +
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
    linarith
  · intro g₁ P δ hδ_le hδ htie hPball i hi
    have hR2 := hCR g₁ P hδ_le hδ htie hPball i hi
    have hC2 := hCC g₁ P hδ_le hδ htie hPball i hi
    change ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      3 * (CR i + CC i +
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
            - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2)
    have hsplit : (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)
        = ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
            - (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))
          + (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
              - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) := by abel
    have e1 := iteratedCovGrad_add (I := I) g₀ 2 2 i
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
        - (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
          - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
    have e2 := iteratedCovGrad_sub (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
    rw [hsplit, e1, e2]
    set u := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) with hu
    set v := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) with hv
    set w := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) with hw
    clear_value u v w
    have habc : ∀ (t a b c cr cc : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ t →
        t ≤ a + b + c → a ^ 2 ≤ cr → b ^ 2 ≤ cc →
        t ^ 2 ≤ 3 * (cr + cc + c ^ 2) := by
      intro t a b c cr cc ha hb hc ht hsum hcr hcc
      have hsabc : 0 ≤ a + b + c := by linarith
      nlinarith [mul_le_mul hsum hsum ht hsabc, sq_nonneg (a - b), sq_nonneg (b - c),
        sq_nonneg (a - c), hcr, hcc, ha, hb, hc]
    have htri : ‖(u - v) + w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ := by
      calc ‖(u - v) + w‖ ≤ ‖u - v‖ + ‖w‖ := norm_add_le _ _
        _ ≤ (‖u‖ + ‖v‖) + ‖w‖ := add_le_add (norm_sub_le u v) le_rfl
    exact habc ‖(u - v) + w‖ ‖u‖ ‖v‖ ‖w‖ (CR i) (CC i)
      (norm_nonneg u) (norm_nonneg v) (norm_nonneg w) (norm_nonneg _) htri hR2 hC2

end DifferentialGeometry.Integral.Connection

end
