import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem appCc_topOrder_l2_twoArm_mixed_le
    (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ q
            (appCc (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) :=
  sorry

theorem deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Cemb : ℝ, 0 ≤ Cemb ∧
      ∀ (W : SmoothCcTensor g₀ 0 2) (x : M),
        (∑ m ∈ Finset.range 3,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m W).toSection x)) ≤
          Cemb ^ 2 * ∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 :=
  sorry

theorem deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_weighted_ballUniform_order
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀) (q : ℕ) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ max (a + 2) (q + 2) → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ max (a + 2) (q + 2) → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤
            (ΛC * δ₀) ^ 2) ∧
          (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 :=
  sorry

private theorem iteratedCovGrad_compWindow_l2_eq
    (g₀ : SmoothRiemannianMetric I M) (m l : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 := by
  have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
        (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
        ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
          (iteratedCovGrad (I := I) g₀ 0 2 m W)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
      (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W))
  have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) W).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    rw [SmoothCcTensor.norm_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
      (iteratedCovGrad (I := I) g₀ 0 2 (m + l) W)
  rw [hbridgeL, hbridgeR]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  have hrw := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l W x
  simpa only [Nat.add_assoc] using hrw

private theorem iteratedCovGrad_compWindow_jetSum_le
    (g₀ : SmoothRiemannianMetric I M) (q m : ℕ) (W : SmoothCcTensor g₀ 0 2) :
    (∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (q + m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 := by
  rw [show (∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m W)‖ ^ 2) =
      ∑ l ∈ Finset.range (q + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) W‖ ^ 2 from
    Finset.sum_congr rfl (fun l _ => iteratedCovGrad_compWindow_l2_eq (I := I) g₀ m l W)]
  set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2 with hf_def
  have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
  have himg : (Finset.range (q + 1)).image (fun l => m + l) ⊆ Finset.range (q + m + 1) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨l, hl, rfl⟩ := hi
    rw [Finset.mem_range] at hl ⊢
    omega
  have hinj : ∀ l₁ ∈ Finset.range (q + 1), ∀ l₂ ∈ Finset.range (q + 1),
      m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
  calc (∑ l ∈ Finset.range (q + 1), f (m + l))
      = ∑ i ∈ (Finset.range (q + 1)).image (fun l => m + l), f i :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ i ∈ Finset.range (q + m + 1), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
theorem deTurckSmoothRemainderDiff_iteratedCovGrad_l2_weighted_ballUniform_order
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ max (a + 2) (q + 2) → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ max (a + 2) (q + 2) → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * (δ₀ * Real.sqrt (∑ i ∈ Finset.range (q + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
              Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
              Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2)) := by
  classical
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hcoeff⟩ :=
    deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_weighted_ballUniform_order
      (I := I) g₀ g_bg a ha_super hR hδ₀ hδ₀_nn q
  obtain ⟨K₀, hK₀_nn, hK₀⟩ := appCc_topOrder_l2_twoArm_mixed_le (I := I) g₀ 2 2 q
  obtain ⟨K₁, hK₁_nn, hK₁⟩ := appCc_topOrder_l2_twoArm_mixed_le (I := I) g₀ 3 2 q
  obtain ⟨K₂, hK₂_nn, hK₂⟩ := appCc_topOrder_l2_twoArm_mixed_le (I := I) g₀ 4 2 q
  obtain ⟨Cemb1, hCemb1_nn, hemb1⟩ :=
    deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) g₀ a ha_super
  set Kmax : ℝ := max K₀ (max K₁ K₂) with hKmax_def
  have hKmax_nn : 0 ≤ Kmax := le_trans hK₀_nn (le_max_left _ _)
  have hK₀_le : K₀ ≤ Kmax := le_max_left _ _
  have hK₁_le : K₁ ≤ Kmax := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK₂_le : K₂ ≤ Kmax := le_trans (le_max_right _ _) (le_max_right _ _)
  set base : ℝ := Kmax * ((Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1)) with hbase_def
  have hbase_nn : 0 ≤ base := by rw [hbase_def]; positivity
  refine ⟨3 * Real.sqrt base, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set S₂ : ℝ := ∑ i ∈ Finset.range (q + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS₂_def
  set S₁ : ℝ := ∑ i ∈ Finset.range (q + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS₁_def
  set Sf : ℝ := ∑ i ∈ Finset.range (a + 1 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hSf_def
  have hS₂_nn : 0 ≤ S₂ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS₁_nn : 0 ≤ S₁ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSf_nn : 0 ≤ Sf := Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hcoeff T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  set A₀ := appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
  set A₁ := appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
  set A₂ := appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
  have hN_split : deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' = A₀ + A₁ + A₂ := by
    rw [hA₀, hA₁, hA₂]; exact hid
  have hWsup1 : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) ≤
        (Real.sqrt (Cemb1 ^ 2 * Sf)) ^ 2 := by
    intro m hm x
    rw [Real.sq_sqrt (by positivity)]
    have hembx := hemb1 (T - T') x
    rw [hSf_def]
    have hmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    refine le_trans (Finset.single_le_sum
      (f := fun mm => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + mm) x
        ((iteratedCovGrad (I := I) g₀ 0 2 mm (T - T')).toSection x))
      (fun mm _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + mm) x _) hmem) ?_
    exact hembx
  have harmTop : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
      Real.sqrt base * (Real.sqrt Sf + δ₀ * Real.sqrt S₂) := by
    have htame := hK₂ C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
      (ΛC * δ₀) (Real.sqrt (Cemb1 ^ 2 * Sf)) (mul_nonneg hΛC_nn hδ₀_nn) (Real.sqrt_nonneg _)
      hC₂sup (hWsup1 2 (by norm_num))
    have hΛWsq : (Real.sqrt (Cemb1 ^ 2 * Sf)) ^ 2 = Cemb1 ^ 2 * Sf := Real.sq_sqrt (by positivity)
    have hcjet : (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤
        Γ ^ 2 := hC₂jet
    have hwjet : (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 4 l (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2) ≤
        S₂ := by
      have h := iteratedCovGrad_compWindow_jetSum_le (I := I) g₀ q 2 (T - T')
      rw [hS₂_def]
      refine le_trans h ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun i _ _ => sq_nonneg _)
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ^ 2 ≤ base * (Sf + δ₀ ^ 2 * S₂) := by
      rw [hA₂]
      refine le_trans htame ?_
      rw [hΛWsq]
      have ha1 : (Cemb1 ^ 2 * Sf) * ∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2 ≤ (Cemb1 ^ 2 * Sf) * Γ ^ 2 :=
        mul_le_mul_of_nonneg_left hcjet (by positivity)
      have ha2 : (ΛC * δ₀) ^ 2 * ∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 4 l
              (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2 ≤ (ΛC * δ₀) ^ 2 * S₂ :=
        mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
      have hinner :
          (Cemb1 ^ 2 * Sf) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
            + (ΛC * δ₀) ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 4 l
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2
          ≤ (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (Sf + δ₀ ^ 2 * S₂) := by
        have hsum_le :
            (Cemb1 ^ 2 * Sf) * Γ ^ 2 + (ΛC * δ₀) ^ 2 * S₂ ≤
              (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (Sf + δ₀ ^ 2 * S₂) := by
          have hcoeff_le : Cemb1 ^ 2 * Γ ^ 2 ≤
              (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) := by
            nlinarith [sq_nonneg Cemb1, sq_nonneg Γ, sq_nonneg ΛC,
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
          have hΛC_le : ΛC ^ 2 ≤
              (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) := by
            nlinarith [sq_nonneg Cemb1, sq_nonneg Γ, sq_nonneg ΛC,
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
          set B : ℝ := (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) with hB_def
          have hB_nn : 0 ≤ B := by rw [hB_def]; positivity
          have hterm1 : (Cemb1 ^ 2 * Sf) * Γ ^ 2 ≤ B * Sf := by
            rw [show (Cemb1 ^ 2 * Sf) * Γ ^ 2 = (Cemb1 ^ 2 * Γ ^ 2) * Sf by ring]
            exact mul_le_mul_of_nonneg_right hcoeff_le hSf_nn
          have hterm2 : (ΛC * δ₀) ^ 2 * S₂ ≤ B * (δ₀ ^ 2 * S₂) := by
            rw [show (ΛC * δ₀) ^ 2 * S₂ = ΛC ^ 2 * (δ₀ ^ 2 * S₂) by ring]
            exact mul_le_mul_of_nonneg_right hΛC_le (by positivity)
          calc (Cemb1 ^ 2 * Sf) * Γ ^ 2 + (ΛC * δ₀) ^ 2 * S₂
              ≤ B * Sf + B * (δ₀ ^ 2 * S₂) := add_le_add hterm1 hterm2
            _ = B * (Sf + δ₀ ^ 2 * S₂) := by ring
        linarith [ha1, ha2, hsum_le]
      have hinner_nn : 0 ≤ (Cemb1 ^ 2 * Sf) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
            + (ΛC * δ₀) ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 4 l
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2 := by positivity
      calc K₂ * ((Cemb1 ^ 2 * Sf) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
              + (ΛC * δ₀) ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 4 l
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2)
          ≤ Kmax * ((Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (Sf + δ₀ ^ 2 * S₂)) :=
            mul_le_mul hK₂_le hinner hinner_nn hKmax_nn
        _ = base * (Sf + δ₀ ^ 2 * S₂) := by rw [hbase_def]; ring
    have hfinal : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
        Real.sqrt base * (Real.sqrt Sf + δ₀ * Real.sqrt S₂) := by
      have hsqrt_le : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
          Real.sqrt (base * (Sf + δ₀ ^ 2 * S₂)) := by
        rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ =
            Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ^ 2) from
          (Real.sqrt_sq (norm_nonneg _)).symm]
        exact Real.sqrt_le_sqrt hsq
      refine hsqrt_le.trans ?_
      have hsq_rhs : (Real.sqrt base * (Real.sqrt Sf + δ₀ * Real.sqrt S₂)) ^ 2 =
          base * (Sf + δ₀ ^ 2 * S₂ + 2 * δ₀ * (Real.sqrt Sf * Real.sqrt S₂)) := by
        rw [mul_pow, Real.sq_sqrt hbase_nn, add_sq, mul_pow,
          Real.sq_sqrt hSf_nn, Real.sq_sqrt hS₂_nn]
        ring
      have hle_sq : base * (Sf + δ₀ ^ 2 * S₂) ≤
          (Real.sqrt base * (Real.sqrt Sf + δ₀ * Real.sqrt S₂)) ^ 2 := by
        rw [hsq_rhs]
        have hcross_nn : 0 ≤ 2 * δ₀ * (Real.sqrt Sf * Real.sqrt S₂) := by
          have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hδ₀_nn)
            (mul_nonneg (Real.sqrt_nonneg Sf) (Real.sqrt_nonneg S₂))
          linarith [this]
        nlinarith [hbase_nn, hcross_nn, mul_nonneg hbase_nn hcross_nn]
      have hrhs_nn : 0 ≤ Real.sqrt base * (Real.sqrt Sf + δ₀ * Real.sqrt S₂) := by
        have : 0 ≤ Real.sqrt Sf + δ₀ * Real.sqrt S₂ :=
          add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hδ₀_nn (Real.sqrt_nonneg _))
        exact mul_nonneg (Real.sqrt_nonneg _) this
      calc Real.sqrt (base * (Sf + δ₀ ^ 2 * S₂))
          ≤ Real.sqrt ((Real.sqrt base * (Real.sqrt Sf + δ₀ * Real.sqrt S₂)) ^ 2) :=
            Real.sqrt_le_sqrt hle_sq
        _ = Real.sqrt base * (Real.sqrt Sf + δ₀ * Real.sqrt S₂) := Real.sqrt_sq hrhs_nn
    exact hfinal
  have harmLow : ∀ (m : ℕ) (hm : m ≤ 1) (Cm : SmoothCcTensor g₀ (2 + m) 2) (Km : ℝ)
      (hKm_le : Km ≤ Kmax)
      (hKm : ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 2 q (appCc (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
          Km * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2))
      (hCmsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Cm.toSection x) ≤ ΛC ^ 2)
      (hCmjet : (∑ i ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ Γ ^ 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ≤
        Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁) := by
    intro m hm Cm Km hKm_le hKm hCmsup hCmjet
    have htame := hKm Cm (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))
      ΛC (Real.sqrt (Cemb1 ^ 2 * Sf)) hΛC_nn (Real.sqrt_nonneg _) hCmsup
      (hWsup1 m (by omega))
    have hΛWsq : (Real.sqrt (Cemb1 ^ 2 * Sf)) ^ 2 = Cemb1 ^ 2 * Sf := Real.sq_sqrt (by positivity)
    have hcjet : (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤
        Γ ^ 2 := hCmjet
    have hwjet : (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤ S₁ := by
      have h := iteratedCovGrad_compWindow_jetSum_le (I := I) g₀ q m (T - T')
      refine le_trans h ?_
      rw [hS₁_def]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun i _ _ => sq_nonneg _)
    have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2 ≤ base * (Sf + S₁) := by
      refine le_trans htame ?_
      rw [hΛWsq]
      have ha1 : (Cemb1 ^ 2 * Sf) * ∑ i ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 ≤ (Cemb1 ^ 2 * Sf) * Γ ^ 2 :=
        mul_le_mul_of_nonneg_left hcjet (by positivity)
      have ha2 : ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 ≤ ΛC ^ 2 * S₁ :=
        mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
      have hinner :
          (Cemb1 ^ 2 * Sf) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
          ≤ (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (Sf + S₁) := by
        set B : ℝ := (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) with hB_def
        have hB_nn : 0 ≤ B := by rw [hB_def]; positivity
        have hcoeff_le : Cemb1 ^ 2 * Γ ^ 2 ≤ B := by
          rw [hB_def]
          nlinarith [sq_nonneg Cemb1, sq_nonneg Γ, sq_nonneg ΛC,
            mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
        have hΛC_le : ΛC ^ 2 ≤ B := by
          rw [hB_def]
          nlinarith [sq_nonneg Cemb1, sq_nonneg Γ, sq_nonneg ΛC,
            mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
        have hterm1 : (Cemb1 ^ 2 * Sf) * Γ ^ 2 ≤ B * Sf := by
          rw [show (Cemb1 ^ 2 * Sf) * Γ ^ 2 = (Cemb1 ^ 2 * Γ ^ 2) * Sf by ring]
          exact mul_le_mul_of_nonneg_right hcoeff_le hSf_nn
        have hterm2 : ΛC ^ 2 * S₁ ≤ B * S₁ := mul_le_mul_of_nonneg_right hΛC_le hS₁_nn
        have hsum_le : (Cemb1 ^ 2 * Sf) * Γ ^ 2 + ΛC ^ 2 * S₁ ≤ B * (Sf + S₁) := by
          calc (Cemb1 ^ 2 * Sf) * Γ ^ 2 + ΛC ^ 2 * S₁
              ≤ B * Sf + B * S₁ := add_le_add hterm1 hterm2
            _ = B * (Sf + S₁) := by ring
        linarith [ha1, ha2, hsum_le]
      have hinner_nn : 0 ≤ (Cemb1 ^ 2 * Sf) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
            + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 := by positivity
      calc Km * ((Cemb1 ^ 2 * Sf) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
              + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2)
          ≤ Kmax * ((Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (Sf + S₁)) :=
            mul_le_mul hKm_le hinner hinner_nn hKmax_nn
        _ = base * (Sf + S₁) := by rw [hbase_def]; ring
    have hfinal : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
          (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ≤
        Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁) := by
      have hsqrt_le : ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ≤
          Real.sqrt (base * (Sf + S₁)) := by
        rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ =
            Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q
              (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2) from
          (Real.sqrt_sq (norm_nonneg _)).symm]
        exact Real.sqrt_le_sqrt hsq
      refine hsqrt_le.trans ?_
      have hsq_rhs : (Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁)) ^ 2 =
          base * (Sf + S₁ + 2 * (Real.sqrt Sf * Real.sqrt S₁)) := by
        rw [mul_pow, Real.sq_sqrt hbase_nn, add_sq,
          Real.sq_sqrt hSf_nn, Real.sq_sqrt hS₁_nn]
        ring
      have hle_sq : base * (Sf + S₁) ≤
          (Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁)) ^ 2 := by
        rw [hsq_rhs]
        have hcross_nn : 0 ≤ 2 * (Real.sqrt Sf * Real.sqrt S₁) := by
          have := mul_nonneg (Real.sqrt_nonneg Sf) (Real.sqrt_nonneg S₁)
          linarith [this]
        nlinarith [hbase_nn, hcross_nn, mul_nonneg hbase_nn hcross_nn]
      have hrhs_nn : 0 ≤ Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁) :=
        mul_nonneg (Real.sqrt_nonneg _)
          (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      calc Real.sqrt (base * (Sf + S₁))
          ≤ Real.sqrt ((Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁)) ^ 2) :=
            Real.sqrt_le_sqrt hle_sq
        _ = Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁) := Real.sqrt_sq hrhs_nn
    exact hfinal
  have ha0 := harmLow 0 (by norm_num) C₀ K₀ hK₀_le hK₀ hC₀sup hC₀jet
  have ha1 := harmLow 1 (by norm_num) C₁ K₁ hK₁_le hK₁ hC₁sup hC₁jet
  have hnorm0 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀‖ ≤
      Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁) := by
    rw [hA₀]; exact ha0
  have hnorm1 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₁‖ ≤
      Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁) := by
    rw [hA₁]; exact ha1
  rw [hN_split, iteratedCovGrad_add (I := I) g₀ 0 2 q (A₀ + A₁) A₂,
    iteratedCovGrad_add (I := I) g₀ 0 2 q A₀ A₁]
  have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀ +
        iteratedCovGrad (I := I) g₀ 0 2 q A₁ +
        iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
      Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁) +
        Real.sqrt base * (Real.sqrt Sf + Real.sqrt S₁) +
        Real.sqrt base * (Real.sqrt Sf + δ₀ * Real.sqrt S₂) := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hnorm0 hnorm1)) harmTop
  refine htri.trans ?_
  have hsb_nn : 0 ≤ Real.sqrt base := Real.sqrt_nonneg _
  have hs1_nn : 0 ≤ Real.sqrt S₁ := Real.sqrt_nonneg _
  have hs2_nn : 0 ≤ Real.sqrt S₂ := Real.sqrt_nonneg _
  have hsf_nn : 0 ≤ Real.sqrt Sf := Real.sqrt_nonneg _
  nlinarith [hsb_nn, hs1_nn, hs2_nn, hsf_nn, hδ₀_nn,
    mul_nonneg hsb_nn hs1_nn, mul_nonneg hsb_nn hs2_nn, mul_nonneg hsb_nn hsf_nn,
    mul_nonneg (mul_nonneg hδ₀_nn hsb_nn) hs2_nn]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
