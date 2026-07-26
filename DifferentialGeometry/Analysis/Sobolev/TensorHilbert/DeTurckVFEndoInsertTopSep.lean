import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVFEndoInsertProducers

/-! # DeTurck vector-field endo-insert top-separated API (split 3/3)

Public API (`connDiffDVFSection`, `realizedFam_*_ballUniform`) and the `DLbTopSeparated`
assembly ending in `deTurckLieWEndoInsert_realizedFam_jetL2_{perOrder,summed}_topSeparated`. -/

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
/-! ## The `wAlphaB` (connection-difference) half as an isolated `(1,1)` insert

The `lc0Insert`-difference `Kc` atom needs the connection-difference half of the DeTurck
endomorphism ISOLATED from its covariant-derivative half.  We expose that half as a smooth
endo section `connDiffDVFSection` whose slot-`0` insertion is exactly
`cometricRaiseSlot0Field g₀ 0 (wAlphaB …)` — the `wAlphaA`-free part of
`deTurckLieWEndoInsert_eq_cometricRaise`. -/

/-- The connection-difference half of the DeTurck endomorphism as a smooth `(1, 1)`-endo
section: `x ↦ connDiff g₁ g₀ x (deTurckVF g₁ g_ref x)`.  `deTurckLieWEndoSection` is this plus
the covariant-derivative (`wAlphaA`) half; its slot-`0` insert is
`cometricRaiseSlot0Field g₀ 0 (wAlphaB g₀ g₁ g_ref)` (`connDiffDVFInsert_eq_cometricRaise`). -/
def connDiffDVFSection (g₀ g₁ g_ref : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (wVF (I := I) (M := M) g₁ g_ref x)
  contMDiff_toFun :=
    ContMDiff.clm_bundle_apply (b := id)
      (connDiffOp_homSection_contMDiff (I := I) g₁ g₀)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g_ref).contMDiff

/-- Slot insertion is subtractive in the inserted endomorphism section. -/
private lemma slotInsertEndoCc_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ Λ' : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (Λ - Λ') =
      slotInsertEndoCc (I := I) (M := M) g₀ s Λ -
        slotInsertEndoCc (I := I) (M := M) g₀ s Λ' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hRHS : (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ s Λ -
          slotInsertEndoCc (I := I) (M := M) g₀ s Λ').toSection x) D =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Λ x) D -
        slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Λ' x) D := by
    rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s Λ -
          slotInsertEndoCc (I := I) (M := M) g₀ s Λ').toSection x) =
        (slotInsertEndoCc (I := I) (M := M) g₀ s Λ).toSection x -
          (slotInsertEndoCc (I := I) (M := M) g₀ s Λ').toSection x from rfl]
    rfl
  rw [hRHS]
  have hLHS : (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ s (Λ - Λ')).toSection x) D =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Λ - Λ') x) D := rfl
  rw [hLHS, show ((Λ - Λ') x) = Λ x - Λ' x from rfl,
    slotInsertEndoFib_sub_left (I := I) (M := M) (s + 1) 0 x (Λ x) (Λ' x)]
  rw [ContinuousLinearMap.sub_apply]

/-- **HOIST.**  Slot-`0` insertion of the connection-difference endomorphism is the slot-`0`
cometric raise of `wAlphaB`.  The `wAlphaA`-free companion of
`deTurckLieWEndoInsert_eq_cometricRaise`. -/
theorem connDiffDVFInsert_eq_cometricRaise (g₀ g₁ g_ref : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (connDiffDVFSection (I := I) (M := M) g₀ g₁ g_ref) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 (wAlphaB (I := I) (M := M) g₀ g₁ g_ref) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [cotangentToDual_cometricRaiseSlot0_gen (I := I) (M := M) g₀
    (wAlphaB (I := I) (M := M) g₀ g₁ g_ref) x om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (connDiffDVFSection (I := I) (M := M) g₀ g₁ g_ref)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (connDiffDVFSection (I := I) (M := M) g₀ g₁ g_ref x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (connDiffDVFSection (I := I) (M := M) g₀ g₁ g_ref x) om w]
  rw [wAlphaB_unitModel_apply (I := I) (M := M) g₀ g₁ g_ref x
    (inverseMetricSharpFib (I := I) g₀ x om) w]
  rw [show cotangentToDual (I := I) om
        (connDiffDVFSection (I := I) (M := M) g₀ g₁ g_ref x w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        (connDiffDVFSection (I := I) (M := M) g₀ g₁ g_ref x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om
      (connDiffDVFSection (I := I) (M := M) g₀ g₁ g_ref x w)).symm]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
    (connDiffDVFSection (I := I) (M := M) g₀ g₁ g_ref x w)]
  rfl

/-- The slot-`0` cometric raise is a jet isometry (generic `(0, s + 2)` field). -/
private lemma norm_iCG_cometricRaiseSlot0Field_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 (s + 2)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 (s + 1) i
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 2) i W‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ s W i x

set_option linter.unusedVariables false in
/-- **Per-order `wAlphaB` jet-`L²` (`ballUniform`).**  The connection-difference half
`wAlphaB = appCc(wCA)(wOmega)` is `∇²P`-free, so each `∇^i` is bounded uniformly over the ball
(the `hBsum` arm of `wAlpha_order0_jetL2_generic`, isolated for reuse by the `lc0Insert`-diff
atom). -/
private theorem wAlphaB_jetL2_perOrder_generic
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ F : ℕ → ℝ, (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ i : ℕ, i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤ F i := by
  classical
  obtain ⟨ΛO, FO, hΛO_nn, hFO_nn, hOgen⟩ :=
    wOmega_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛCd, FCd, hΛCd_nn, hFCd_nn, hCdgen⟩ :=
    connDiffSection_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 0 1)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 1 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 0 2 1 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨fun i => appCcGdiag (E := E) i * (CT i * (ΛO 0 * FCd i + ΛCd 0 * FO i)),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (mul_nonneg (hCT_nn i) (add_nonneg (mul_nonneg (hΛO_nn 0) (hFCd_nn i))
        (mul_nonneg (hΛCd_nn 0) (hFO_nn i)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hOlow, hOsum⟩ := hOgen g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hCdlow, hCdsum⟩ := hCdgen g₁ P htie hδ_le hδ0 hδ hPball
  have hwCAlow : ∀ n : ℕ, n ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)).toSection x) ≤
      ΛCd n := by
    intro n hn x
    rw [rfns_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ n x]
    exact hCdlow n hn x
  have hwCAsum : ∀ i : ℕ, i ≤ a + 1 →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 q (wCA (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ FCd i := by
    intro i hi
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun q _ => ?_))) (hCdsum i hi)
    rw [norm_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ q]
  have hBform : wAlphaB (I := I) (M := M) g₀ g₁ g_bg =
      appCc (I := I) (M := M) g₀ 1 2 (wCA (I := I) (M := M) g₀ g₁)
        (wOmega (I := I) (M := M) g₀ g₁ g_bg) := rfl
  intro i hi
  have hO0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x
      ((wOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ (Real.sqrt (ΛO 0)) ^ 2 := by
    intro x
    rw [Real.sq_sqrt (hΛO_nn 0)]
    have h := hOlow 0 (by omega) x
    simpa only [iteratedCovGrad_zero] using h
  have hCA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
      ((wCA (I := I) (M := M) g₀ g₁).toSection x) ≤ (Real.sqrt (ΛCd 0)) ^ 2 := by
    intro x
    rw [Real.sq_sqrt (hΛCd_nn 0)]
    have h := hwCAlow 0 (by omega) x
    simpa only [iteratedCovGrad_zero] using h
  obtain ⟨hgrid_int, hgrid_bound⟩ := hCT i (wCA (I := I) (M := M) g₀ g₁)
    (wOmega (I := I) (M := M) g₀ g₁ g_bg) (Real.sqrt (ΛCd 0)) (Real.sqrt (ΛO 0))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hCA0 hO0
  rw [hBform]
  have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
    0 (2 + i)
    (iteratedCovGrad (I := I) g₀ 0 2 i
      (appCc (I := I) (M := M) g₀ 1 2 (wCA (I := I) (M := M) g₀ g₁)
        (wOmega (I := I) (M := M) g₀ g₁ g_bg)))
    (fun x => appCcGdiag (E := E) i *
      ∑ n ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (i + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 1 l
                  (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
    (hgrid_int.const_mul (appCcGdiag (E := E) i))
    (fun x => appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 1 2
      (wCA (I := I) (M := M) g₀ g₁) (wOmega (I := I) (M := M) g₀ g₁ g_bg) i x)
  refine le_trans hkey ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
  refine le_trans hgrid_bound ?_
  refine mul_le_mul_of_nonneg_left ?_ (hCT_nn i)
  rw [Real.sq_sqrt (hΛO_nn 0), Real.sq_sqrt (hΛCd_nn 0)]
  have e1 : ΛO 0 * (∑ n ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
      ΛO 0 * FCd i := mul_le_mul_of_nonneg_left (hwCAsum i (by omega)) (hΛO_nn 0)
  have e2 : ΛCd 0 * (∑ l ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 1 l (wOmega (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
      ΛCd 0 * FO i := mul_le_mul_of_nonneg_left (hOsum i (by omega)) (hΛCd_nn 0)
  linarith [e1, e2]

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
theorem deTurckLieWEndoInsert_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
              ((deTurckLieWEndoInsert (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  obtain ⟨Λ0, F, hΛ0_nn, hF_nn, hgen⟩ :=
    wAlpha_order0_jetL2_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨Λ0, hΛ0_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hδP0 : 0 ≤ (1 - s) * δ' + s * δ := by
    obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x, v ≠ 0 := by
      haveI : Nontrivial (TangentSpace I x) := by
        have hfr : 0 < Module.finrank ℝ (TangentSpace I x) := by
          have heq : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
          rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
        exact Module.nontrivial_of_finrank_pos hfr
      exact exists_ne 0
    have hpos : 0 < g₀.inner x v v := g₀.pos x v hv
    have hbound := hδP x v v
    have hsqrt_pos : 0 < Real.sqrt (g₀.inner x v v) := Real.sqrt_pos.mpr hpos
    have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀
        (convexPerturbation (I := I) g₀ T T' s) x v v| := abs_nonneg _
    by_contra hδc
    have hδc' : (1 - s) * δ' + s * δ < 0 := lt_of_not_ge hδc
    have hrhs_neg : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x v v) *
        Real.sqrt (g₀.inner x v v) < 0 := by
      have h1 : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x v v) < 0 :=
        mul_neg_of_neg_of_pos hδc' hsqrt_pos
      exact mul_neg_of_neg_of_pos h1 hsqrt_pos
    linarith [le_trans habs_nn hbound]
  have htr := rfns_iCG_wEndoInsert_eq_wAlpha (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg 0 x
  have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
      ((deTurckLieWEndoInsert (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 0) x
        ((iteratedCovGrad (I := I) g₀ 1 1 0
          (deTurckLieWEndoInsert (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) := by
    rw [iteratedCovGrad_zero]
  rw [h0, htr]
  have hval := (hgen (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball).1 x
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
      ((iteratedCovGrad (I := I) g₀ 0 2 0
        (wAlpha (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((wAlpha (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) := by
    rw [iteratedCovGrad_zero]
  rw [h1]
  exact hval

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
theorem deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
              (deTurckLieWEndoInsert (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  classical
  obtain ⟨Λ0, F, hΛ0_nn, hF_nn, hgen⟩ :=
    wAlpha_order0_jetL2_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨F, hF_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  by_cases hMne : Nonempty M
  · obtain ⟨x₀⟩ := hMne
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    have hδP : gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
        ((1 - s) * δ' + s * δ) :=
      convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
    have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
      have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
      have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
      have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
      linarith [e1, e2, e3]
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
      fun y v w =>
        realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
          (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
    have hPball : ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
      intro j hj
      have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
          = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
        rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
          iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
        _ ≤ (1 - s) * R + s * R :=
            add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
              (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
        _ = R := by ring
    have hδP0 : 0 ≤ (1 - s) * δ' + s * δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδP x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀
          (convexPerturbation (I := I) g₀ T T' s) x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : (1 - s) * δ' + s * δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x₀ v v) *
          Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    rw [norm_iCG_wEndoInsert_eq_wAlpha (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i]
    exact (hgen (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball).2 i hi
  · haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (deTurckLieWEndoInsert (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have := hF_nn i
    nlinarith [hF_nn i]

/-- Squared triangle over two summands: `t ≤ u + v`, `u² ≤ c₁`, `v² ≤ c₂` give
`t² ≤ 2·(c₁ + c₂)`. -/
private theorem sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
/-- **`(1, 1)` endo-difference `ballUniform` producer.**  Per-order jet-`L²` bound for the
slot-`0` insertion of the connection-difference endomorphism DIFFERENCE
`connDiffDVFSection g₀ g₁ g₀ − connDiffDVFSection g₀ g₁ g_bg`, at `g₁ = realizedFam`, uniform
over the ball (`∇²P`-free ⟹ pure `ballUniform`, no top term).  The `lc0Insert`-difference `Kc`
atom consumes this: via `nEndo_diff` the leaf's `(2, 2)` insert-difference reduces to it. -/
theorem connDiffDVFInsertDiff_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (connDiffDVFSection (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ -
                  connDiffDVFSection (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤ K i := by
  classical
  obtain ⟨F0, hF0_nn, hgen0⟩ :=
    wAlphaB_jetL2_perOrder_generic (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Fbg, hFbg_nn, hgenbg⟩ :=
    wAlphaB_jetL2_perOrder_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨fun i => 2 * (F0 i + Fbg i),
    fun i => by have := hF0_nn i; have := hFbg_nn i; linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  by_cases hMne : Nonempty M
  · obtain ⟨x₀⟩ := hMne
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    have hδP : gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
        ((1 - s) * δ' + s * δ) :=
      convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
    have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
      have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
      have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
      have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
      linarith [e1, e2, e3]
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
      fun y v w =>
        realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
          (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
    have hPball : ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
      intro j hj
      have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
          = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
        rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
          iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
        _ ≤ (1 - s) * R + s * R :=
            add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
              (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
        _ = R := by ring
    have hδP0 : 0 ≤ (1 - s) * δ' + s * δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδP x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀
          (convexPerturbation (I := I) g₀ T T' s) x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : (1 - s) * δ' + s * δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x₀ v v) *
          Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hB0 := hgen0 (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball i hi
    have hBbg := hgenbg (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball i hi
    rw [slotInsertEndoCc_sub, connDiffDVFInsert_eq_cometricRaise,
      connDiffDVFInsert_eq_cometricRaise, iteratedCovGrad_sub]
    have hiso0 : ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (wAlphaB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀))‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 i
          (wAlphaB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ :=
      norm_iCG_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
        (wAlphaB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀) i
    have hisobg : ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (wAlphaB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 2 i
          (wAlphaB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ :=
      norm_iCG_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
        (wAlphaB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) i
    have htri' : ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (wAlphaB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)) -
          iteratedCovGrad (I := I) g₀ 1 1 i
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (wAlphaB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ≤
        ‖iteratedCovGrad (I := I) g₀ 0 2 i
            (wAlphaB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀)‖ +
          ‖iteratedCovGrad (I := I) g₀ 0 2 i
            (wAlphaB (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ := by
      rw [← hiso0, ← hisobg]
      exact norm_sub_le _ _
    exact sq_le_two_add _ _ _ (F0 i) (Fbg i) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      htri' hB0 hBbg
  · haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (connDiffDVFSection (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ -
            connDiffDVFSection (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have h0 := hF0_nn i
    have hb := hFbg_nn i
    nlinarith [hF0_nn i, hFbg_nn i]

/-! ### DLb top-separated tower (insert-level producer)

Top-separated `realizedFam` jetL2 producer for `deTurckLieWEndoInsert`, the DLb sibling of the DLa
kernel top separation.  The top order `∇^{i+2}T` enters only through `wAlphaA = ∇^{i+1}wOmega`; the
remainder currency is `antidiagonalTupleGridWindow` (integrated by the tame-window integrator).  See
`DeTurckVectorFieldL2JetBound.md`. -/
section DLbTopSeparated

/-- Pure `Finset` window-shift helper (copied verbatim from the sibling top-separated files). -/
private lemma sum_shift_le (g : ℕ → ℝ) (hg : ∀ j, 0 ≤ g j) (m c : ℕ) :
    ∑ i ∈ Finset.range m, g (i + c) ≤ ∑ j ∈ Finset.range (m + c), g j := by
  classical
  have hsub :
      (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩ ⊆
        Finset.range (m + c) := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_range] at hi ⊢
    simp only [Function.Embedding.coeFn_mk]
    omega
  calc ∑ i ∈ Finset.range m, g (i + c)
      = ∑ j ∈ (Finset.range m).map ⟨fun i => i + c, fun a b h => by simpa using h⟩, g j := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ j ∈ Finset.range (m + c), g j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hg j)

/-- Summation of a per-order top-separated jet bound with independent top offset `p` and low-window
offset `q` (copied from the sibling top-separated files). -/
private lemma jetL2_sum_lowShift
    (a p q : ℕ) (Ktop : ℝ) (hKtop : 0 ≤ Ktop) (Kc : ℕ → ℝ) (hKc : ∀ i, 0 ≤ Kc i)
    (f w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hper : ∀ i, i ≤ a →
        f i ≤ Ktop * w (i + p) + Kc i * (1 + ∑ j ∈ Finset.range (i + q), w j)) :
    ∑ i ∈ Finset.range (a + 1), f i ≤
      Ktop * (∑ j ∈ Finset.range (a + 1 + p), w j) +
      (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + q), w j) := by
  refine le_trans (Finset.sum_le_sum (fun i hi =>
    hper i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))) ?_
  rw [Finset.sum_add_distrib]
  have hB : (∑ i ∈ Finset.range (a + 1), Ktop * w (i + p)) ≤
      Ktop * ∑ j ∈ Finset.range (a + 1 + p), w j := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_shift_le w hw (a + 1) p) hKtop
  have hA : (∑ i ∈ Finset.range (a + 1), Kc i * (1 + ∑ j ∈ Finset.range (i + q), w j)) ≤
      (∑ i ∈ Finset.range (a + 1), Kc i) * (1 + ∑ j ∈ Finset.range (a + q), w j) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine mul_le_mul_of_nonneg_left ?_ (hKc i)
    have hsub : Finset.range (i + q) ⊆ Finset.range (a + q) := by
      intro y hy; rw [Finset.mem_range] at hy ⊢; omega
    have hss : ∑ j ∈ Finset.range (i + q), w j ≤ ∑ j ∈ Finset.range (a + q), w j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
    linarith
  linarith [hA, hB]

/-- Reshape the connDiffSection top-separated engine remainder
`∑_{k<j} b(j-k)·antidiagonalTupleGrid b (k+1)` into `Cj·antidiagonalTupleGridWindow b (j+2)`
(public-grid analogue of the DLa `engineRem_le_dLaGridWin`). -/
private lemma engineRem_le_grid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∑ k ∈ Finset.range j,
        b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (∑ k ∈ Finset.range j,
          Combinatorics.antidiagonalTupleGridCount (j - k) *
            Combinatorics.antidiagonalTupleGridCount (k + 1)) *
        Combinatorics.antidiagonalTupleGridWindow b (j + 2) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  have hg_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b (k + 1) :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb (k + 1)
  have h1 : b (j - k) ≤ Combinatorics.antidiagonalTupleGrid b (j - k) := by
    have hsf := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 (j - k) (by omega)
    rwa [Combinatorics.antidiagonalTupleGrid_zero, mul_one, Nat.zero_add] at hsf
  have h2 : Combinatorics.antidiagonalTupleGrid b (j - k) *
      Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (Combinatorics.antidiagonalTupleGridCount (j - k) *
        Combinatorics.antidiagonalTupleGridCount (k + 1)) *
        Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) :=
    Combinatorics.antidiagonalTupleGrid_mul_le b hb (j - k) (k + 1)
  have h3 : Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) ≤
      Combinatorics.antidiagonalTupleGridWindow b (j + 2) := by
    rw [show (j - k) + (k + 1) = j + 1 from by omega]
    exact Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
  calc b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
      ≤ Combinatorics.antidiagonalTupleGrid b (j - k) *
          Combinatorics.antidiagonalTupleGrid b (k + 1) :=
        mul_le_mul_of_nonneg_right h1 hg_nn
    _ ≤ (Combinatorics.antidiagonalTupleGridCount (j - k) *
          Combinatorics.antidiagonalTupleGridCount (k + 1)) *
          Combinatorics.antidiagonalTupleGrid b ((j - k) + (k + 1)) := h2
    _ ≤ (Combinatorics.antidiagonalTupleGridCount (j - k) *
          Combinatorics.antidiagonalTupleGridCount (k + 1)) *
          Combinatorics.antidiagonalTupleGridWindow b (j + 2) :=
        mul_le_mul_of_nonneg_left h3
          (mul_nonneg (Combinatorics.antidiagonalTupleGridCount_nonneg _)
            (Combinatorics.antidiagonalTupleGridCount_nonneg _))

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **connDiffSection top-separated jet bound in `antidiagonalTupleGridWindow` currency.**  Top
coefficient `Ktop = 2·Kt0` (`R`-independent engine head); remainder is a single grid window (house
`R`-pattern).  Public-grid re-derivation of the DLa `exists_rfns_connDiffSection_topsep_dla`. -/
private theorem exists_rfns_connDiff_topsep
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ j, 0 ≤ Kc j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) P).toSection x) +
          Kc j * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (j + 2) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  refine ⟨2 * Kt0, mul_nonneg (by norm_num) hKt0_nn,
    fun j => 2 * Kc0 j * (∑ k ∈ Finset.range j,
      Combinatorics.antidiagonalTupleGridCount (j - k) *
        Combinatorics.antidiagonalTupleGridCount (k + 1)),
    fun j => mul_nonneg (mul_nonneg (by norm_num) (hKc0_nn j))
      (Finset.sum_nonneg fun k _ =>
        mul_nonneg (Combinatorics.antidiagonalTupleGridCount_nonneg _)
          (Combinatorics.antidiagonalTupleGridCount_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have heng := hbot g₁ P htie hδ_le hδ0 hbound j x
  set Hd : SmoothCcTensor g₀ 1 (2 + j) :=
    appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
      (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHd_def
  have hhead : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) ≤
      Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) P).toSection x) := heng.1
  have hrem := heng.2
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
          Hd).toSection x) := by
    have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (2 + j) x
      (Hd.toSection x)
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) - Hd).toSection x)
    have key :
        (iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x =
          Hd.toSection x +
            (iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
              Hd).toSection x := by
      simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
      abel
    rw [key]
    exact hadd
  have hrem2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) - Hd).toSection x) ≤
      Kc0 j * ((∑ k ∈ Finset.range j,
        Combinatorics.antidiagonalTupleGridCount (j - k) *
          Combinatorics.antidiagonalTupleGridCount (k + 1)) *
        Combinatorics.antidiagonalTupleGridWindow b (j + 2)) :=
    le_trans hrem (mul_le_mul_of_nonneg_left (engineRem_le_grid b hb j) (hKc0_nn j))
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x)
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x (Hd.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
            Hd).toSection x) := hsplit
    _ ≤ 2 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) P).toSection x)) +
        2 * (Kc0 j * ((∑ k ∈ Finset.range j,
          Combinatorics.antidiagonalTupleGridCount (j - k) *
            Combinatorics.antidiagonalTupleGridCount (k + 1)) *
          Combinatorics.antidiagonalTupleGridWindow b (j + 2))) := by
          linarith [hhead, hrem2]
    _ = (2 * Kt0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) P).toSection x) +
        (2 * Kc0 j * (∑ k ∈ Finset.range j,
          Combinatorics.antidiagonalTupleGridCount (j - k) *
            Combinatorics.antidiagonalTupleGridCount (k + 1))) *
          Combinatorics.antidiagonalTupleGridWindow b (j + 2) := by ring

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **connDiffSection L2 top-separated bound.**  Integrates `exists_rfns_connDiff_topsep`: the top
`‖∇^{n+1}P‖²` stays separated with the `R`-free coefficient `Ktop = 2·Kt0`; the grid-window remainder
integrates to a ball-uniform per-order constant `C n` (absorbed into `Kc·1` downstream via the
tame-window integrator + the `hPball` conversion `∑_{j≤k}‖∇^jP‖² ≤ (k+1)R²`). -/
private theorem connDiff_L2_topsep
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ n : ℕ, n ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + C n := by
  classical
  obtain ⟨Ktop_pt, hKtop_pt_nn, Kc_pt, hKc_pt_nn, hpt⟩ :=
    exists_rfns_connDiff_topsep (I := I) (M := M) g₀ hδ₀
  obtain ⟨K, hK_nn, hKint⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Ktop_pt, hKtop_pt_nn,
    fun n => Kc_pt n * ∑ k ∈ Finset.range (n + 2), K k * (1 + ((k : ℝ) + 1) * R ^ 2),
    fun n => mul_nonneg (hKc_pt_nn n)
      (Finset.sum_nonneg fun k _ => mul_nonneg (hK_nn k) (by positivity)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball n hn
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  -- per-index grid integrability + ball-uniform integral bound (via tame-window integrator)
  have hAG : ∀ k : ℕ, k ≤ a + 2 →
      MeasureTheory.Integrable (fun x => Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, Combinatorics.antidiagonalTupleGrid
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          K k * (1 + ((k : ℝ) + 1) * R ^ 2) := by
    intro k hk
    have hExpand : (fun x => Combinatorics.antidiagonalTupleGrid
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) k)
        = (fun x => ∑ m ∈ Finset.range (k + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple m k,
            ∏ i : Fin m, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e i) P).toSection x)) := by
      funext x; rw [Combinatorics.antidiagonalTupleGrid]
    rw [hExpand]
    obtain ⟨hint, hbd⟩ := hKint P hPball k
    refine ⟨hint, le_trans hbd ?_⟩
    have hsum : (∑ j ∈ Finset.range (k + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ ((k : ℝ) + 1) * R ^ 2 := by
      calc ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
          ≤ ∑ j ∈ Finset.range (k + 1), R ^ 2 := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            have hjk : j ≤ a + 2 :=
              le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hk
            have hb := hPball j hjk
            nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hb, hR]
        _ = ((k : ℝ) + 1) * R ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (by linarith [hsum]) (hK_nn k)
  -- window integrability + integral bound
  have hwin_int : MeasureTheory.Integrable (fun x => Combinatorics.antidiagonalTupleGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    refine MeasureTheory.integrable_finset_sum _ (fun k hk => (hAG k ?_).1)
    have := Finset.mem_range.mp hk; omega
  have hwin_bd : (∫ x, Combinatorics.antidiagonalTupleGridWindow
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      ∑ k ∈ Finset.range (n + 2), K k * (1 + ((k : ℝ) + 1) * R ^ 2) := by
    simp only [Combinatorics.antidiagonalTupleGridWindow]
    rw [MeasureTheory.integral_finset_sum _ (fun k hk => (hAG k (by
      have := Finset.mem_range.mp hk; omega)).1)]
    refine Finset.sum_le_sum (fun k hk => (hAG k ?_).2)
    have := Finset.mem_range.mp hk; omega
  -- top integrability
  have htop_int : MeasureTheory.Integrable (fun x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (n + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P)
  -- pointwise top-separated bound, integrated
  have hbridge := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + n)
    (iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀))
    (fun x => Ktop_pt * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x)
      + Kc_pt n * Combinatorics.antidiagonalTupleGridWindow
        (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2))
    ((htop_int.const_mul Ktop_pt).add (hwin_int.const_mul (Kc_pt n)))
    (fun x => hpt g₁ P htie hδ_le hδ0 hδ n x)
  rw [MeasureTheory.integral_add (htop_int.const_mul Ktop_pt) (hwin_int.const_mul (Kc_pt n)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hbridge
  have hnormsq : ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  calc ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2
      ≤ Ktop_pt * (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        + Kc_pt n * (∫ x, Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := hbridge
    _ = Ktop_pt * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2
        + Kc_pt n * (∫ x, Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (n + 2)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) := by rw [hnormsq]
    _ ≤ Ktop_pt * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2
        + Kc_pt n * ∑ k ∈ Finset.range (n + 2), K k * (1 + ((k : ℝ) + 1) * R ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left hwin_bd (hKc_pt_nn n)
        linarith [hmul]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **wXi L2 top-separated bound.**  `wXi = connDiffLoweredCc g₁ − connDiffLoweredCc g_bg`; the
`g₁` part carries the top `‖∇^{n+1}P‖²` (via `connDiff_L2_topsep`), the `g_bg` part is a `T`-free
constant folded into `C n`.  `Ktop = 2·(connDiff Ktop)`, `R`-free. -/
private theorem wXi_L2_topsep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ n : ℕ, n ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + C n := by
  classical
  obtain ⟨Ktop_cd, hKtop_cd_nn, C_cd, hC_cd_nn, hcd⟩ :=
    connDiff_L2_topsep (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨2 * Ktop_cd, mul_nonneg (by norm_num) hKtop_cd_nn,
    fun n => 2 * C_cd n +
      2 * ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg)‖ ^ 2,
    fun n => add_nonneg (mul_nonneg (by norm_num) (hC_cd_nn n))
      (mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball n hn
  have hA : ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 ≤
      Ktop_cd * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + C_cd n := by
    rw [norm_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ n]
    exact hcd g₁ P htie hδ_le hδ0 hδ hPball n hn
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg)‖ := by
    rw [wXi, iteratedCovGrad_sub]
    exact norm_sub_le _ _
  nlinarith [htri, hA,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg)),
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ -
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g_bg)‖)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **wOmega L2 top-separated bound** (genuine corner peel).  `wOmega = appCc cometricCastG0 wXi`;
the argCorner Leibniz decomposition isolates the corner `appCcRS ψ_{n,n} (∇ⁿwXi)` — whose
coefficient fiber norm is the `R`-free order-`0` bound `ΛClow 0` (`rfns_appCcRS_appCcLeibnizPsi_diag_le`
carries no `appCcGdiag`), feeding `wXi_L2_topsep` for the top `‖∇^{n+1}P‖²` — from a top-free lower
sum bounded ball-uniformly by the two-arm grid integrator.  `Ktop = 2·ΛClow 0·Ktop_xi`, `R`-free. -/
private theorem wOmega_L2_topsep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ n : ℕ, n ≤ a + 1 →
          ‖iteratedCovGrad (I := I) g₀ 0 1 n (wOmega (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + C n := by
  classical
  obtain ⟨Ktop_xi, hKtop_xi_nn, Cxi, hCxi_nn, hxi⟩ :=
    wXi_L2_topsep (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛClow, hΛClow_nn, hClow⟩ :=
    cometricCastG0_rfns_lowOrder_le (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛCsup, FC, hΛCsup_nn, hFC_nn, hCgen⟩ :=
    cometricCastG0_order0sup_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛX, FX, hΛX_nn, hFX_nn, hXgen⟩ :=
    wXi_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 3 1) (T : SmoothCcTensor g₀ 0 3)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 3 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 3 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 3 1 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 3 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 3 0 1 3 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨2 * ΛClow 0 * Ktop_xi,
    mul_nonneg (mul_nonneg (by norm_num) (hΛClow_nn 0)) hKtop_xi_nn,
    fun n => 2 * ΛClow 0 * Cxi n +
      2 * ((n : ℝ) * appCcGdiag (E := E) n) *
        (CT n * (ΛX 0 * FC n + ΛCsup ^ 2 * FX n)),
    fun n => add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (hΛClow_nn 0)) (hCxi_nn n))
      (mul_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (Nat.cast_nonneg n) (appCcGdiag_nonneg (E := E) n)))
        (mul_nonneg (hCT_nn n) (add_nonneg (mul_nonneg (hΛX_nn 0) (hFC_nn n))
          (mul_nonneg (sq_nonneg _) (hFX_nn n))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball n hn
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨hCsup, hCsum⟩ := hCgen g₁ P hδ_le hδ htie hPball
  obtain ⟨hXlow, hXsum⟩ := hXgen g₁ P htie hδ_le hδ0 hδ hPball
  -- uniform `R`-free order-0 fiber bound on `cometricCastG0`
  have hc0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
      ((cometricCastG0 (I := I) g₀ g₁).toSection x) ≤ ΛClow 0 := by
    intro x
    have h := hClow g₁ P htie hδ_le hδ0 hδ hPball 0 (by norm_num) x
    simpa only [iteratedCovGrad_zero] using h
  -- order-0 sup bound on `wXi` (`√(ΛX 0)`)
  have hX0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 3 x
      ((wXi (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ (Real.sqrt (ΛX 0)) ^ 2 := by
    intro x
    rw [Real.sq_sqrt (hΛX_nn 0)]
    have h := hXlow 0 (by norm_num) x
    simpa only [iteratedCovGrad_zero] using h
  -- integrability of the two arms of the pointwise envelope
  have hwxi_int : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (3 + n)
      (iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg))
  obtain ⟨htri_int, htri_bd⟩ := hCT n (cometricCastG0 (I := I) g₀ g₁)
    (wXi (I := I) (M := M) g₀ g₁ g_bg) ΛCsup (Real.sqrt (ΛX 0)) hΛCsup_nn (Real.sqrt_nonneg _)
    hCsup hX0
  -- `wOmega = appCcRS 0 (cometricCastG0) (wXi)`
  have hwform : wOmega (I := I) (M := M) g₀ g₁ g_bg =
      appCcRS (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
        (wXi (I := I) (M := M) g₀ g₁ g_bg) := by
    rw [show wOmega (I := I) (M := M) g₀ g₁ g_bg =
        appCc (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
          (wXi (I := I) (M := M) g₀ g₁ g_bg) from rfl]
    exact (appCcRS_zero_eq_appCc (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
      (wXi (I := I) (M := M) g₀ g₁ g_bg)).symm
  -- pointwise top-separated envelope for `∇ⁿ wOmega`
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 1 n (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        (2 * ΛClow 0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
          + (2 * ((n : ℝ) * appCcGdiag (E := E) n)) *
            ∑ i ∈ Finset.range (n + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
                * ∑ l ∈ Finset.range (n + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 3 l
                        (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    intro x
    rw [hwform, iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ 0 3 1
      (cometricCastG0 (I := I) g₀ g₁) (wXi (I := I) (M := M) g₀ g₁ g_bg) n]
    rw [show ((appCcRS (I := I) (M := M) g₀ 0 (3 + n) (1 + n)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n n)
            (iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)) +
          ∑ k ∈ Finset.range n,
            appCcRS (I := I) (M := M) g₀ 0 (3 + k) (1 + n)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n k)
              (iteratedCovGrad (I := I) g₀ 0 3 k
                (wXi (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
        = (appCcRS (I := I) (M := M) g₀ 0 (3 + n) (1 + n)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n n)
            (iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg))).toSection x +
          (∑ k ∈ Finset.range n,
            appCcRS (I := I) (M := M) g₀ 0 (3 + k) (1 + n)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n k)
              (iteratedCovGrad (I := I) g₀ 0 3 k
                (wXi (I := I) (M := M) g₀ g₁ g_bg))).toSection x
        from by rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (1 + n) x _ _) ?_
    -- corner: coefficient fiber norm `≤ ΛClow 0`, no `appCcGdiag`
    have hcorner : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
        ((appCcRS (I := I) (M := M) g₀ 0 (3 + n) (1 + n)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n n)
          (iteratedCovGrad (I := I) g₀ 0 3 n
            (wXi (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤
        ΛClow 0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
      refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁) n
        (iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)) x) ?_
      exact mul_le_mul_of_nonneg_right (hc0 x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + n) x _)
    -- lower sum: top-free, bounded by the two-arm triangular grid
    have hlower : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + n) x
        ((∑ k ∈ Finset.range n,
          appCcRS (I := I) (M := M) g₀ 0 (3 + k) (1 + n)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁) n k)
            (iteratedCovGrad (I := I) g₀ 0 3 k
              (wXi (I := I) (M := M) g₀ g₁ g_bg))).toSection x) ≤
        ((n : ℝ) * appCcGdiag (E := E) n) *
          ∑ i ∈ Finset.range (n + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (n + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 3 l
                      (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
      refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ 0 3 1
        (cometricCastG0 (I := I) g₀ g₁) (wXi (I := I) (M := M) g₀ g₁ g_bg) n x) ?_
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (Nat.cast_nonneg n) (appCcGdiag_nonneg (E := E) n))
      -- antidiagonal ≤ triangular grid
      set A : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
        with hA_def
      set B : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 3 l (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        with hB_def
      have hA_nn : ∀ i, 0 ≤ A i := fun i => riemannianFiberNormSq_nonneg _ _ _ _ _
      have hB_nn : ∀ l, 0 ≤ B l := fun l => riemannianFiberNormSq_nonneg _ _ _ _ _
      have hstep1 : ∑ k ∈ Finset.range n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (n - k)) x
                ((iteratedCovGrad (I := I) g₀ 3 1 (n - k)
                  (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 3 k
                  (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          ∑ k ∈ Finset.range n, A (n - k) * ∑ l ∈ Finset.range (n + 1 - (n - k)), B l := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        refine mul_le_mul_of_nonneg_left ?_ (hA_nn (n - k))
        exact Finset.single_le_sum (fun l _ => hB_nn l)
          (Finset.mem_range.mpr (by omega))
      have hstep2 : ∑ k ∈ Finset.range n, A (n - k) * ∑ l ∈ Finset.range (n + 1 - (n - k)), B l =
          ∑ k ∈ Finset.range n, A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l := by
        rw [← Finset.sum_range_reflect
          (fun k => A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l) n]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        have hk1 : n - 1 - k + 1 = n - k := by omega
        rw [hk1]
      have hstep3 : ∑ k ∈ Finset.range n, A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l ≤
          ∑ i ∈ Finset.range (n + 1), A i * ∑ l ∈ Finset.range (n + 1 - i), B l := by
        rw [Finset.sum_range_succ' (fun i => A i * ∑ l ∈ Finset.range (n + 1 - i), B l) n]
        have h0 : 0 ≤ A 0 * ∑ l ∈ Finset.range (n + 1 - 0), B l :=
          mul_nonneg (hA_nn 0) (Finset.sum_nonneg fun l _ => hB_nn l)
        linarith
      calc ∑ k ∈ Finset.range n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + (n - k)) x
                  ((iteratedCovGrad (I := I) g₀ 3 1 (n - k)
                    (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 3 k
                    (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
            ≤ ∑ k ∈ Finset.range n, A (n - k) * ∑ l ∈ Finset.range (n + 1 - (n - k)), B l := hstep1
          _ = ∑ k ∈ Finset.range n, A (k + 1) * ∑ l ∈ Finset.range (n + 1 - (k + 1)), B l := hstep2
          _ ≤ ∑ i ∈ Finset.range (n + 1), A i * ∑ l ∈ Finset.range (n + 1 - i), B l := hstep3
    nlinarith [hcorner, hlower,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)]
  -- integrate the envelope
  have hbridge := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 0 (1 + n)
    (iteratedCovGrad (I := I) g₀ 0 1 n (wOmega (I := I) (M := M) g₀ g₁ g_bg))
    (fun x => (2 * ΛClow 0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        + (2 * ((n : ℝ) * appCcGdiag (E := E) n)) *
          ∑ i ∈ Finset.range (n + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (n + 1 - i),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 3 l
                      (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
    ((hwxi_int.const_mul (2 * ΛClow 0)).add
      (htri_int.const_mul (2 * ((n : ℝ) * appCcGdiag (E := E) n))))
    hpt
  rw [MeasureTheory.integral_add (hwxi_int.const_mul (2 * ΛClow 0))
      (htri_int.const_mul (2 * ((n : ℝ) * appCcGdiag (E := E) n))),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hbridge
  -- ∫ wxi = ‖∇ⁿ wXi‖²
  have hwxi_eq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      ‖iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def, tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  rw [hwxi_eq] at hbridge
  -- two-arm integral bound → ball-uniform constant
  have hgrid_ballU : (∫ x, (∑ i ∈ Finset.range (n + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (n + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 3 l
                  (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      CT n * (ΛX 0 * FC n + ΛCsup ^ 2 * FX n) := by
    refine le_trans htri_bd ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCT_nn n)
    rw [Real.sq_sqrt (hΛX_nn 0)]
    have e1 : ΛX 0 * (∑ i ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2) ≤
        ΛX 0 * FC n := mul_le_mul_of_nonneg_left (hCsum n hn) (hΛX_nn 0)
    have e2 : ΛCsup ^ 2 * (∑ l ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 3 l (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
        ΛCsup ^ 2 * FX n := mul_le_mul_of_nonneg_left (hXsum n hn) (sq_nonneg ΛCsup)
    linarith [e1, e2]
  -- assemble
  have htop := hxi g₁ P htie hδ_le hδ0 hδ hPball n hn
  have hc1 : (2 * ΛClow 0) *
        ‖iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      2 * ΛClow 0 * Ktop_xi *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + 2 * ΛClow 0 * Cxi n := by
    have h2Λ : 0 ≤ 2 * ΛClow 0 := mul_nonneg (by norm_num) (hΛClow_nn 0)
    calc (2 * ΛClow 0) *
            ‖iteratedCovGrad (I := I) g₀ 0 3 n (wXi (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2
        ≤ (2 * ΛClow 0) * (Ktop_xi *
            ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + Cxi n) :=
          mul_le_mul_of_nonneg_left htop h2Λ
      _ = 2 * ΛClow 0 * Ktop_xi *
            ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) P‖ ^ 2 + 2 * ΛClow 0 * Cxi n := by ring
  have hc2 : (2 * ((n : ℝ) * appCcGdiag (E := E) n)) *
        (∫ x, (∑ i ∈ Finset.range (n + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i) x
              ((iteratedCovGrad (I := I) g₀ 3 1 i (cometricCastG0 (I := I) g₀ g₁)).toSection x)
            * ∑ l ∈ Finset.range (n + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 3 l
                    (wXi (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      2 * ((n : ℝ) * appCcGdiag (E := E) n) * (CT n * (ΛX 0 * FC n + ΛCsup ^ 2 * FX n)) := by
    exact mul_le_mul_of_nonneg_left hgrid_ballU
      (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg n) (appCcGdiag_nonneg (E := E) n)))
  linarith [hbridge, hc1, hc2]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **wAlpha L2 top-separated bound.**  `wAlpha = wAlphaA + wAlphaB`; the `wAlphaA` arm is
`‖∇ⁱwAlphaA‖² = ‖∇^{i+1}wOmega‖²` (`norm_iCG_wAlphaA_eq_succ_wOmega`), top-separated by
`wOmega_L2_topsep` at `n = i+1` (top `‖∇^{i+2}P‖²`); the `wAlphaB` arm is a two-arm product
`appCc wCA wOmega`, bounded ball-uniformly (top-free, folded into `C`).  `Ktop = 2·Ktop_om`. -/
private theorem wAlpha_L2_topsep
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ i : ℕ, i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
            Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 + C i := by
  classical
  obtain ⟨Ktop_om, hKtop_om_nn, Com, hCom_nn, hom⟩ :=
    wOmega_L2_topsep (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛO, FO, hΛO_nn, hFO_nn, hOgen⟩ :=
    wOmega_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨ΛCd, FCd, hΛCd_nn, hFCd_nn, hCdgen⟩ :=
    connDiffSection_lowOrder_jetL2_succ_generic (I := I) (M := M) g₀ a ha_super hR hδ₀
  have hTA_ex : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g₀ 1 2) (T : SmoothCcTensor g₀ 0 1)
        (ΛS' ΛT' : ℝ), 0 ≤ ΛS' → 0 ≤ ΛT' →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x (S.toSection x) ≤ ΛS' ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x (T.toSection x) ≤ ΛT' ^ 2) →
        MeasureTheory.Integrable
            (fun x => ∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 1 l T).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, (∑ i ∈ Finset.range (q + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 i S).toSection x)
                * ∑ l ∈ Finset.range (q + 1 - i),
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                      ((iteratedCovGrad (I := I) g₀ 0 1 l T).toSection x))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
            C * (ΛT' ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 1 2 i S‖ ^ 2
                + ΛS' ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 1 l T‖ ^ 2) := by
    intro q
    obtain ⟨C, hC_nn, hC⟩ :=
      exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 1 0 2 1 q
    exact ⟨C, hC_nn, fun S T ΛS' ΛT' h1 h2 h3 h4 => hC S T ΛS' ΛT' h1 h2 h3 h4⟩
  choose CT hCT_nn hCT using hTA_ex
  refine ⟨2 * Ktop_om, mul_nonneg (by norm_num) hKtop_om_nn,
    fun i => 2 * Com (i + 1) +
      2 * (appCcGdiag (E := E) i * (CT i * (ΛO 0 * FCd i + ΛCd 0 * FO i))),
    fun i => add_nonneg (mul_nonneg (by norm_num) (hCom_nn (i + 1)))
      (mul_nonneg (by norm_num) (mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (mul_nonneg (hCT_nn i) (add_nonneg (mul_nonneg (hΛO_nn 0) (hFCd_nn i))
          (mul_nonneg (hΛCd_nn 0) (hFO_nn i)))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball i hi
  obtain ⟨hOlow, hOsum⟩ := hOgen g₁ P htie hδ_le hδ0 hδ hPball
  obtain ⟨hCdlow, hCdsum⟩ := hCdgen g₁ P htie hδ_le hδ0 hδ hPball
  have hwCAlow : ∀ n : ℕ, n ≤ 1 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)).toSection x) ≤
      ΛCd n := by
    intro n hn x
    rw [rfns_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ n x]
    exact hCdlow n hn x
  have hwCAsum : ∀ i : ℕ, i ≤ a + 1 →
      ∑ q ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 q (wCA (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ FCd i := by
    intro i hi
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun q _ => ?_))) (hCdsum i hi)
    rw [norm_iCG_wCA_eq_connDiffSection (I := I) (M := M) g₀ g₁ q]
  have hBform : wAlphaB (I := I) (M := M) g₀ g₁ g_bg =
      appCc (I := I) (M := M) g₀ 1 2 (wCA (I := I) (M := M) g₀ g₁)
        (wOmega (I := I) (M := M) g₀ g₁ g_bg) := rfl
  -- wAlphaB ball-uniform (top-free)
  have hBi : ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      appCcGdiag (E := E) i * (CT i * (ΛO 0 * FCd i + ΛCd 0 * FO i)) := by
    have hO0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 1 x
        ((wOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x) ≤ (Real.sqrt (ΛO 0)) ^ 2 := by
      intro x
      rw [Real.sq_sqrt (hΛO_nn 0)]
      have h := hOlow 0 (by omega) x
      simpa only [iteratedCovGrad_zero] using h
    have hCA0 : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x
        ((wCA (I := I) (M := M) g₀ g₁).toSection x) ≤ (Real.sqrt (ΛCd 0)) ^ 2 := by
      intro x
      rw [Real.sq_sqrt (hΛCd_nn 0)]
      have h := hwCAlow 0 (by omega) x
      simpa only [iteratedCovGrad_zero] using h
    obtain ⟨hgrid_int, hgrid_bound⟩ := hCT i (wCA (I := I) (M := M) g₀ g₁)
      (wOmega (I := I) (M := M) g₀ g₁ g_bg) (Real.sqrt (ΛCd 0)) (Real.sqrt (ΛO 0))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hCA0 hO0
    rw [hBform]
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      0 (2 + i)
      (iteratedCovGrad (I := I) g₀ 0 2 i
        (appCc (I := I) (M := M) g₀ 1 2 (wCA (I := I) (M := M) g₀ g₁)
          (wOmega (I := I) (M := M) g₀ g₁ g_bg)))
      (fun x => appCcGdiag (E := E) i *
        ∑ n ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
              ((iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)).toSection x)
            * ∑ l ∈ Finset.range (i + 1 - n),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 1 l
                    (wOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x))
      (hgrid_int.const_mul (appCcGdiag (E := E) i))
      (fun x => appCc_iteratedCovGrad_diagonalProductGrid_le (I := I) (M := M) g₀ 1 2
        (wCA (I := I) (M := M) g₀ g₁) (wOmega (I := I) (M := M) g₀ g₁ g_bg) i x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
    refine le_trans hgrid_bound ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCT_nn i)
    rw [Real.sq_sqrt (hΛO_nn 0), Real.sq_sqrt (hΛCd_nn 0)]
    have e1 : ΛO 0 * (∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 1 2 n (wCA (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
        ΛO 0 * FCd i := mul_le_mul_of_nonneg_left (hwCAsum i (by omega)) (hΛO_nn 0)
    have e2 : ΛCd 0 * (∑ l ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 1 l (wOmega (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
        ΛCd 0 * FO i := mul_le_mul_of_nonneg_left (hOsum i (by omega)) (hΛCd_nn 0)
    linarith [e1, e2]
  -- wAlphaA top-separated (top `‖∇^{i+2}P‖²`)
  have hAi : ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      Ktop_om * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 + Com (i + 1) := by
    rw [norm_iCG_wAlphaA_eq_succ_wOmega (I := I) (M := M) g₀ g₁ g_bg i]
    exact hom g₁ P htie hδ_le hδ0 hδ hPball (i + 1) (by omega)
  -- wAlpha = wAlphaA + wAlphaB, triangle
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)‖ := by
    rw [wAlpha, iteratedCovGrad_add]
    exact norm_add_le _ _
  nlinarith [htri, hAi, hBi,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i (wAlpha (I := I) (M := M) g₀ g₁ g_bg)),
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaA (I := I) (M := M) g₀ g₁ g_bg)‖ -
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (wAlphaB (I := I) (M := M) g₀ g₁ g_bg)‖)]

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (convexPerturbation convexPerturbation_gFibreOpBound realizedFam_inner_of_mem
    Icc_subset_realizedSmallSet) in
/-- **`realizedFam` per-order top-separated jet-L2 bound** for the insert-level `deTurckLieWEndoInsert`.
Top `Ktop·(‖∇^{i+2}T‖²+‖∇^{i+2}T'‖²)` with `R`-free `Ktop` (from `wAlpha_L2_topsep` via
`norm_iCG_wEndoInsert_eq_wAlpha`); the ball-uniform remainder is absorbed into `Kc i·(1+∑…)`.  The
DLb sibling of `deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_topSeparated`. -/
theorem deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
              (deTurckLieWEndoInsert (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Ktop_a, hKtop_a_nn, C_a, hC_a_nn, ha⟩ :=
    wAlpha_L2_topsep (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨Ktop_a, hKtop_a_nn, C_a, hC_a_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hsum_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 3),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    add_nonneg zero_le_one
      (Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  by_cases hMne : Nonempty M
  · obtain ⟨x₀⟩ := hMne
    have hs0 : (0 : ℝ) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
    have hδP : gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
        ((1 - s) * δ' + s * δ) :=
      convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
    have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
      have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
      have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
      have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
      linarith [e1, e2, e3]
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
      fun y v w =>
        realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
          (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
    have hPball : ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
      intro j hj
      have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
          = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
        rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
          iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
      rw [heq]
      calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
              + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
          ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
        _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
              + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg h1ms, abs_of_nonneg hs0]
        _ ≤ (1 - s) * R + s * R :=
            add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
              (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
        _ = R := by ring
    have hwin : ∀ j : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2 := by
      intro j
      have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
          = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
        rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
          iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
      have hy_nn : 0 ≤ (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
          + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
        add_nonneg (mul_nonneg h1ms (norm_nonneg _)) (mul_nonneg hs0 (norm_nonneg _))
      have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤
          (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
        rw [heq]
        calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
                + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
            ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
                + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
          _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
                + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg h1ms, abs_of_nonneg hs0]
      nlinarith [mul_le_mul hnorm_le hnorm_le (norm_nonneg
          (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s))) hy_nn,
        mul_nonneg (mul_nonneg hs0 h1ms)
          (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ -
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)),
        mul_nonneg h1ms (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖),
        mul_nonneg hs0 (sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)]
    have hδP0 : 0 ≤ (1 - s) * δ' + s * δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδP x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀
          (convexPerturbation (I := I) g₀ T T' s) x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : (1 - s) * δ' + s * δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x₀ v v) *
          Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : ((1 - s) * δ' + s * δ) * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    rw [norm_iCG_wEndoInsert_eq_wAlpha (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i]
    have hbase := ha (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) htie hδP_le hδP0 hδP hPball i hi
    have htop_le : Ktop_a *
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2)
            (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
        Ktop_a * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hwin (i + 2)) hKtop_a_nn
    have hrem_le : C_a i ≤ C_a i * (1 + ∑ j ∈ Finset.range (i + 3),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
      nlinarith [hC_a_nn i, hsum_nn,
        Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 3)) =>
          add_nonneg (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖))
            (sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖)))]
    linarith [hbase, htop_le, hrem_le]
  · haveI hem : IsEmpty M := not_nonempty_iff.mp hMne
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (deTurckLieWEndoInsert (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hrhs : (0 : ℝ) ≤ Ktop_a * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
        C_a i * (1 + ∑ j ∈ Finset.range (i + 3),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) :=
      add_nonneg (mul_nonneg hKtop_a_nn (add_nonneg (sq_nonneg _) (sq_nonneg _)))
        (mul_nonneg (hC_a_nn i) hsum_nn)
    nlinarith [hrhs]

set_option linter.unusedVariables false in
/-- **Summed** `realizedFam` top-separated jet-L2 bound for `deTurckLieWEndoInsert`.  Both windows
`a+3` (via `jetL2_sum_lowShift a 2 3`), `Ktop` `R`-free, single `Kc = ∑_{i≤a} Kc_perOrder i`.  The
DLb sibling of `deTurckLieDLaCoeffField_realizedFam_jetL2_summed_topSeparated`. -/
theorem deTurckLieWEndoInsert_realizedFam_jetL2_summed_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 1 i
                (deTurckLieWEndoInsert (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hper⟩ :=
    deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨Ktop, hKtop_nn, ∑ i ∈ Finset.range (a + 1), Kc i,
    Finset.sum_nonneg (fun i _ => hKc_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  exact jetL2_sum_lowShift a 2 3 Ktop hKtop_nn Kc hKc_nn
    (fun i => ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (deTurckLieWEndoInsert (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2)
    (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)
    (fun j => add_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun i hi => hper T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi)

end DLbTopSeparated

#print axioms connDiffDVFInsert_eq_cometricRaise
#print axioms connDiffDVFInsertDiff_realizedFam_jetL2_perOrder_ballUniform
end DifferentialGeometry.Integral.Connection

end
