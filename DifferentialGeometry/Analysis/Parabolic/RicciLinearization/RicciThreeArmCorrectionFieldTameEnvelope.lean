import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmOrder1KoszulTameEnvelope
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciConnDiffOrder1TameEnvelope

/-!
# Tame jet envelopes for the three-arm correction fields

All-order per-order L² tame jet envelopes for the arm-0 and arm-1 correction subjects of the
linearized Ricci three-arm decomposition along the realized family: the arm-1 correction field
`linearizedRicciConnDiffOrder1Coeff - linearizedRicciArm1BaseCoeff`, and the combined arm-0
subject `linearizedRicciConnDiffOrder0Coeff - linearizedRicciArm0BaseCoeff
+ (3/2) • ricciArmOrder0RiemannCoeff - ricciArmOrder0CurvCoeff` (curvature coefficients at the
realized-family metric). Every covariant-gradient order `i` of the subject is L²-bounded by a
ball-uniform constant times the tame window `1 + ∑_{j < i + 2} (‖∇ʲT‖² + ‖∇ʲT'‖²)`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

set_option linter.unusedVariables false in
/-- All-order per-order L² tame jet envelope for the order-one connection-difference
Ricci-linearization coefficient field, generic in a perturbed metric `g₁ = g₀ + P`.

Proven via the four-trace `appCcRS` refold
`linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS` and the diagonal-product-grid calculus,
mirroring `ricciArmOrder1KoszulCoeff_perOrder_l2_tameEnvelope_generic`. TRANSIT: the two arm
envelopes (`ricciCometricFourTraceCastG0_order0sup_perOrder_l2_tameEnvelope_generic` and
`linearizedRicciConnDiffOrder1KernelField_order0sup_perOrder_l2_tameEnvelope_generic`) are
posited `sorry` children; consumers transitively depend on `sorryAx` until they land. -/
theorem linearizedRicciConnDiffOrder1CoeffField_perOrder_l2_tameEnvelope_generic
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
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciConnDiffOrder1CoeffField (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨ΛΦ, KΦ, hΛΦ, hKΦ_nn, hΦfeed⟩ :=
    ricciCometricFourTraceCastG0_order0sup_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨ΛW, KW, hΛW, hKW_nn, hWfeed⟩ :=
    linearizedRicciConnDiffOrder1KernelField_order0sup_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => appCcGdiag (E := E) i *
      (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
        (I := I) (M := M) g₀ 4 3 2 4 i).choose *
      (ΛW ^ 2 * ∑ n ∈ Finset.range (i + 1), KΦ n
        + ΛΦ ^ 2 * ∑ l ∈ Finset.range (i + 1), KW l),
    fun i => by
      refine mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i)
        (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
          (I := I) (M := M) g₀ 4 3 2 4 i).choose_spec.1) (add_nonneg ?_ ?_)
      · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun n _ => hKΦ_nn n))
      · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun l _ => hKW_nn l)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  obtain ⟨hΦsup, hΦtame⟩ := hΦfeed g₁ P hδ_le hδ htie hPball
  obtain ⟨hWsup, hWtame⟩ := hWfeed g₁ P hδ_le hδ htie hPball
  obtain ⟨hgrid_int, hgrid_bound⟩ :=
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 4 3 2 4 i).choose_spec.2
      (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
      (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)
      ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  rw [linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS (I := I) (M := M) g₀ g₁]
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 3 (2 + i)
    (iteratedCovGrad (I := I) g₀ 3 2 i
      (appCcRS (I := I) (M := M) g₀ 3 4 2
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
        (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)))
    (fun x => appCcGdiag (E := E) i *
      ∑ n ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
            ((iteratedCovGrad (I := I) g₀ 4 2 n
              (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x)
          * ∑ l ∈ Finset.range (i + 1 - n),
              riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 3 4 l
                  (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)).toSection x))
    (hgrid_int.const_mul (appCcGdiag (E := E) i))
    (fun x => rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le (I := I) (M := M) g₀
      i 3 4 2 (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
      (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁) x)
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  have hAnn : (0 : ℝ) ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
  have hCnn : (0 : ℝ) ≤ (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 4 3 2 4 i).choose :=
    (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
      (I := I) (M := M) g₀ 4 3 2 4 i).choose_spec.1
  have hwin2_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hSa : ∑ n ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 4 2 n
          (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
      (∑ n ∈ Finset.range (i + 1), KΦ n) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun n hn => ?_)
    refine le_trans (hΦtame n) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKΦ_nn n)
    have hsub : ∑ j ∈ Finset.range (n + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
      rw [Finset.mem_range] at hn
      omega
    linarith
  have hSc : ∑ l ∈ Finset.range (i + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 4 l
          (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2 ≤
      (∑ l ∈ Finset.range (i + 1), KW l) *
        (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun l hl => ?_)
    refine le_trans (hWtame l) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hKW_nn l)
    have hsub : ∑ j ∈ Finset.range (l + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
        ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
      rw [Finset.mem_range] at hl
      omega
    linarith
  calc appCcGdiag (E := E) i * ∫ x,
          (∑ n ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + n) x
                ((iteratedCovGrad (I := I) g₀ 4 2 n
                  (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)).toSection x)
              * ∑ l ∈ Finset.range (i + 1 - n),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + l) x
                    ((iteratedCovGrad (I := I) g₀ 3 4 l
                      (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)).toSection x))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ appCcGdiag (E := E) i *
          ((exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 4 3 2 4 i).choose *
            (ΛW ^ 2 * ∑ n ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 4 2 n
                  (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 3 4 l
                  (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hgrid_bound hAnn
    _ ≤ appCcGdiag (E := E) i *
          ((exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 4 3 2 4 i).choose *
            ((ΛW ^ 2 * ∑ n ∈ Finset.range (i + 1), KΦ n
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (i + 1), KW l) *
              (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hCnn) hAnn
        have h1 := mul_le_mul_of_nonneg_left hSa (sq_nonneg ΛW)
        have h2 := mul_le_mul_of_nonneg_left hSc (sq_nonneg ΛΦ)
        nlinarith [h1, h2]
    _ = appCcGdiag (E := E) i *
          (exists_integrated_iteratedCovGrad_diagonalProductGrid_twoArm_rs_le
            (I := I) (M := M) g₀ 4 3 2 4 i).choose *
          (ΛW ^ 2 * ∑ n ∈ Finset.range (i + 1), KΦ n
            + ΛΦ ^ 2 * ∑ l ∈ Finset.range (i + 1), KW l) *
          (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        ring

set_option linter.unusedVariables false in
/-- All-order per-order L² tame jet envelope for the arm-1 correction field
`linearizedRicciConnDiffOrder1Coeff - linearizedRicciArm1BaseCoeff` along the realized family:
the difference glue of the order-one connection-difference coefficient envelope with the
order-one Koszul arm coefficient envelope, both at window `i + 2`. -/
theorem exists_corrArm1Field_realizedFam_jetL2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
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
        ∀ (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
              (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s
                - linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨KA, hKA_nn, hKA⟩ :=
    linearizedRicciConnDiffOrder1CoeffField_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KB, hKB_nn, hKB⟩ :=
    ricciArmOrder1KoszulCoeff_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * KA i + 2 * KB i,
    fun i => by linarith [hKA_nn i, hKB_nn i], ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
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
    have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ≤
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
  have hA : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
      KA i * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) :=
    hKA (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i
  have hB : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
      KB i * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2) :=
    hKB (realizedFam (I := I) g₀ T T' hδ hδ' s)
      (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i
  have hwinsum : ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
      ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_le_sum (fun j _ => hwin j)
  have hW_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hWP_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hA' : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
      KA i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
    refine le_trans hA (mul_le_mul_of_nonneg_left (by linarith [hwinsum]) (hKA_nn i))
  have hB' : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ^ 2 ≤
      KB i * (1 + ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
    refine le_trans hB (mul_le_mul_of_nonneg_left (by linarith [hwinsum]) (hKB_nn i))
  rw [iteratedCovGrad_sub]
  have htri : ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)‖ +
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖ :=
    norm_sub_le _ _
  nlinarith [htri, hA', hB',
    norm_nonneg (iteratedCovGrad (I := I) g₀ 3 2 i
      (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 3 2 i
      (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)),
    norm_nonneg (iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)
      - iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)),
    sq_nonneg (‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s)‖ -
      ‖iteratedCovGrad (I := I) g₀ 3 2 i
        (linearizedRicciArm1BaseCoeff (I := I) g₀ T T' hδ hδ' s)‖)]

private theorem corrArm0Combination_eq_order0_add_halfRiemann
    (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
        - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
        + (3 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) =
      linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
        + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) := by
  rw [show linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s =
      linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl,
    show linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s =
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s)
        - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) from rfl,
    show (3 / 2 : ℝ) = 1 + 1 / 2 from by norm_num, add_smul, one_smul]
  abel

set_option linter.unusedVariables false in
/-- Pointwise diagonal-product-grid bound for the covariant gradients of the ∇A-free arm-0
combination `linearizedRicciConnDiffOrder0CoeffField + (1/2) • ricciArmOrder0RiemannCoeff`,
generic in a perturbed metric `g₁ = g₀ + P`, at grid window `i + 2`.

The window is one lower than the moving-metric Riemann grid
(`rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le`,
window `i + 3`): by the certified cancellation anatomy (witness-level:
`Order0∇ = -(1/2) • RmArm∇`) the `∇²P`-linear content of the combination vanishes, and the
residual is one-jet class — the `A⋆A` bi-contraction plus background-curvature commutator
kernels (the `arm0AAField` / `ricciArmOrder0BgRCommCoeffField` families of
`RicciThreeArmCorrectionFieldBound`, with ball-uniform fibre sups there).

DEFERRED INPUT (`sorry`): the field-level Palatini split (`riemannSec_difference`) of the
combination onto the residual families and their covariant-gradient grid calculus
(the `ConnectionDifferenceJetTower` / `CurvatureCoefficientDifferenceJetTower` towers);
consumers transitively depend on `sorryAx` until it lands. -/
theorem rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombination_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 2),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := sorry

set_option linter.unusedVariables false in
/-- All-order per-order L² tame jet envelope for the ∇A-free arm-0 combination
`linearizedRicciConnDiffOrder0CoeffField + (1/2) • ricciArmOrder0RiemannCoeff`, generic in a
perturbed metric `g₁ = g₀ + P`.

By the certified cancellation anatomy (witness-level: the ∇A-content of the order-zero
connection-difference coefficient equals `-(1/2)` times that of the Riemann bi-contraction arm)
the ∇A-linear content of this combination vanishes; the residual is the `A⋆A` bi-contraction
plus the background-curvature commutator kernel — the prebuilt `arm0AAField` /
`ricciArmOrder0BgRCommCoeffField` families of `RicciThreeArmCorrectionFieldBound` (with
ball-uniform fibre sups there), so the combination is one-jet class and every covariant-gradient
order `i` is windowed at `i + 2`.

Proven by integrating the pointwise diagonal-product-grid bound at window `i + 2` against the
ball-uniform grid integrals (`antidiagonalTupleGrid_integral_ballUniform_tameWindow`). TRANSIT:
the grid engine
(`rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombination_diagonalProductGrid_le`)
is a posited `sorry` child; consumers transitively depend on `sorryAx` until it lands. -/
theorem linearizedRicciConnDiffOrder0RiemannHalfCombination_perOrder_l2_tameEnvelope_generic
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
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
                + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨C, hC_nn, hgrid⟩ :=
    rfns_iteratedCovGrad_linearizedRicciConnDiffOrder0RiemannHalfCombination_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 2), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
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
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 2),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁))
      (fun x => C i * ∑ k ∈ Finset.range (i + 2),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k).1)]
    have hsum_le : ∑ k ∈ Finset.range (i + 2),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (∑ k ∈ Finset.range (i + 2), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun k hk => ?_)
      refine le_trans (hKg P hPball k).2 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKg_nn k)
      have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
        rw [Finset.mem_range] at hk
        omega
      linarith
    calc C i * ∑ k ∈ Finset.range (i + 2),
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ C i * ((∑ k ∈ Finset.range (i + 2), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_le (hC_nn i)
      _ = (C i * ∑ k ∈ Finset.range (i + 2), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (linearizedRicciConnDiffOrder0CoeffField (I := I) (M := M) g₀ g₁
          + (1 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 2), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))
    nlinarith [hwin_nn, hK_nn]

set_option linter.unusedVariables false in
/-- All-order per-order L² tame jet envelope for the combined arm-0 correction subject
`linearizedRicciConnDiffOrder0Coeff - linearizedRicciArm0BaseCoeff
+ (3/2) • ricciArmOrder0RiemannCoeff - ricciArmOrder0CurvCoeff` (curvature coefficients at the
realized-family metric) along the realized family, at window `i + 2` — the arm-0 clause of the
reshaped correction-field spec (`corrFieldDataSpec`).

The combined subject is the certified one-jet subject: by the certified weight identity
`RmArm∇ = -2 · Order0∇` the combination equals
`linearizedRicciConnDiffOrder0Coeff + (1/2) • ricciArmOrder0RiemannCoeff`, whose ∇A-linear
content vanishes; the residual is the `A⋆A` bi-contraction plus the background-curvature
commutator kernel (the prebuilt `arm0AAField` / `ricciArmOrder0BgRCommCoeffField` families of
`RicciThreeArmCorrectionFieldBound`).

Proven by the definitional collapse of the combination onto
`linearizedRicciConnDiffOrder0CoeffField + (1/2) • ricciArmOrder0RiemannCoeff` at the realized
metric followed by the generic envelope at the convex perturbation. TRANSIT: the generic engine
(`linearizedRicciConnDiffOrder0RiemannHalfCombination_perOrder_l2_tameEnvelope_generic`) is a
posited `sorry` child; consumers transitively depend on `sorryAx` until it lands. -/
theorem exists_corrArm0Field_realizedFam_jetL2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
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
        ∀ (i : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s
                - linearizedRicciArm0BaseCoeff (I := I) g₀ T T' hδ hδ' s
                + (3 / 2 : ℝ) • ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s)
                - ricciArmOrder0CurvCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨K0, hK0_nn, hK0⟩ :=
    linearizedRicciConnDiffOrder0RiemannHalfCombination_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨K0, hK0_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i s hs
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
    have hnorm_le : ‖iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T T' s)‖ ≤
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
  rw [corrArm0Combination_eq_order0_add_halfRiemann (I := I) (M := M) g₀ T T' hδ hδ' s]
  have hmain := hK0 (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball i
  refine le_trans hmain ?_
  have hwinsum : ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ^ 2 ≤
      ∑ j ∈ Finset.range (i + 2),
        (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_le_sum (fun j _ => hwin j)
  exact mul_le_mul_of_nonneg_left (by linarith [hwinsum]) (hK0_nn i)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
