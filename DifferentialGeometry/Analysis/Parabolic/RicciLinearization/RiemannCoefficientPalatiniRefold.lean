import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldFamilyJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLieCovDerivFamily
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldEndoArmGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldCovDerivArmPairTrace
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLinearizedRefoldIdentity
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldMonomialRefoldL2JetWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldRicciFoldWeightKernel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldSharpGradKoszulResidualSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldResidualFieldBallUniform
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldResidualFieldL2JetWindow


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private lemma real_sq_add_three_le {a b c K0 K1 K2 W : ℝ}
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc : 0 ≤ c)
    (h0 : a ^ 2 ≤ K0 * W) (h1 : b ^ 2 ≤ K1 * W) (h2 : c ^ 2 ≤ K2 * W)
    (_hK0 : 0 ≤ K0) (_hK1 : 0 ≤ K1) (_hK2 : 0 ≤ K2) (_hW : 0 ≤ W) :
    (a + b + c) ^ 2 ≤ 3 * (K0 + K1 + K2) * W := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
    h0, h1, h2, _ha, _hb, _hc, mul_nonneg _hK0 _hW, mul_nonneg _hK1 _hW, mul_nonneg _hK2 _hW]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def riemannPalatiniRefoldC2Family (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  s • ((1 / 2 : ℝ) •
    (curvatureRefoldKernelCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        (qA 0) (qA 1) (qA 2) (qA 3)
      + curvatureRefoldKernelCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        (qB 0) (qB 1) (qB 2) (qB 3)))

set_option linter.unusedSectionVars false in

@[simp] lemma riemannPalatiniRefoldC2Family_zero (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) :
    riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB 0 = 0 := by
  rw [riemannPalatiniRefoldC2Family, zero_smul]

def IsFramePairPartner (qA qB : Fin 4 → Equiv.Perm (Fin 4)) : Prop :=
  ∀ k : Fin 4, qB k = Equiv.swap (0 : Fin 4) 1 * qA k

lemma not_isFramePairPartner_self (q : Fin 4 → Equiv.Perm (Fin 4)) :
    ¬ IsFramePairPartner q q := by
  intro h
  have h0 : Equiv.swap (0 : Fin 4) 1 = 1 := right_eq_mul.mp (h 0)
  have h1 : (Equiv.swap (0 : Fin 4) 1) 0 = (1 : Equiv.Perm (Fin 4)) 0 := by rw [h0]
  rw [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h1
  exact absurd h1 (by decide)

def deTurckLieCovDerivArmField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x))
      contMDiff_toFun := dLaBiContrFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem deTurckLieCovDerivArmField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (dLaBiContrFib (I := I) g₁ g_bg x)) := rfl

def deTurckLieEndoArmField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieDLbFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] theorem deTurckLieEndoArmField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x)) := rfl

set_option linter.unusedSectionVars false in

theorem deTurckLieCoeffField_eq_covDerivArm_add_endoArm
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg
        + deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg := by
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    deTurckLieCoeffField_toSection, deTurckLieCovDerivArmField_toSection,
    deTurckLieEndoArmField_toSection]
  rfl

set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

theorem exists_ricciArmOrder0RiemannCoeff_realizedFam_rfns_ballUniform_sq
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ Λ ^ 2 := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ (max_lt hδ₀ one_pos)
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  obtain ⟨Kbg, hKbg_nn, hKbg_bd⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
  set F : ℝ := (1 + (Csob * R) ^ 2) ^ 2 with hF_def
  have hF_nn : (0 : ℝ) ≤ F := by positivity
  set cnt : ℝ := ∑ k ∈ Finset.range 3, ∑ n ∈ Finset.range (k + 1),
    ((Finset.Nat.antidiagonalTuple n k).card : ℝ) with hcnt_def
  have hcnt_nn : (0 : ℝ) ≤ cnt :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun n _ => Nat.cast_nonneg _
  have hsum_nn : (0 : ℝ) ≤ 2 * (CD 0 * (cnt * F)) + 2 * Kbg := by
    have h1 : (0 : ℝ) ≤ CD 0 * (cnt * F) :=
      mul_nonneg (hCD_nn 0) (mul_nonneg hcnt_nn hF_nn)
    linarith
  refine ⟨Real.sqrt (2 * (CD 0 * (cnt * F)) + 2 * Kbg), Real.sqrt_nonneg _, ?_⟩
  intro T δ hδ_le hδ hδZ hTball s hs x
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    abs_convex_smallConstant_lt_one hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  set m : ℝ := max δ₀ 0 with hm_def
  have hm0 : (0 : ℝ) ≤ m := le_max_right _ _
  have hδs_raw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ + |s| * δ = (1 - s) * δ + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ + s * δ ≤ m := by
    have hδ₀_le : δ₀ ≤ m := le_max_left _ _
    have heq : (1 - s) * δ + s * δ = δ := by ring
    linarith
  have hδP : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) m := by
    intro y v w
    refine le_trans (hδs_raw y v w) ?_
    have hprod : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hle' : |1 - s| * δ + |s| * δ ≤ m := by rw [habs_eq]; exact hsmall_le
    nlinarith [hle', hprod]
  have hCD0 := hCD (realizedFam (I := I) g₀ T 0 hδ hδZ s)
    (convexPerturbation (I := I) g₀ T 0 s) htie (le_of_eq hm_def) hm0 hδP 0 x
  have hicg0 : ∀ j : ℕ,
      iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    intro j
    have h := iteratedCovGrad_sub (I := I) g₀ 0 2 j T T
    simp only [sub_self] at h
    exact h
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j _
    rw [hicg0 j, norm_zero]
    exact hR
  have hCsob_sum := hCsob T 0 hR hTball hZball s ⟨hs0, hs1⟩ x
  have hterm_nn : ∀ j ∈ Finset.range 3, 0 ≤
      (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x‖) := by
    intro j _
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
    exact norm_nonneg _
  have hcell : ∀ j : ℕ, j < 3 →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j
            (convexPerturbation (I := I) g₀ T 0 s)).toSection x) ≤
        1 + (Csob * R) ^ 2 := by
    intro j hj
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
    have hbridge := norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M)
      g₀ 0 (2 + j) x
      (iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T 0 s))
    have hnorm_le : ‖((iteratedCovGrad (I := I) g₀ 0 2 j
        (convexPerturbation (I := I) g₀ T 0 s)).toSection x :
          TensorRSSpace 0 (2 + j) I x)‖ ≤ Csob * R :=
      le_trans (Finset.single_le_sum hterm_nn (Finset.mem_range.mpr hj)) hCsob_sum
    have hsq : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x) =
        ‖((iteratedCovGrad (I := I) g₀ 0 2 j
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x :
            TensorRSSpace 0 (2 + j) I x)‖ ^ 2 := by
      rw [hbridge, Real.sq_sqrt
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _)]
    rw [hsq]
    have h1 : ‖((iteratedCovGrad (I := I) g₀ 0 2 j
        (convexPerturbation (I := I) g₀ T 0 s)).toSection x :
          TensorRSSpace 0 (2 + j) I x)‖ ^ 2 ≤ (Csob * R) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
    linarith
  have hprodcell : ∀ k ∈ Finset.range 3, ∀ n ∈ Finset.range (k + 1),
      ∀ e ∈ Finset.Nat.antidiagonalTuple n k,
      (∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) ≤ F := by
    intro k hk n hn e he
    have hk2 : k ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hn2 : n ≤ 2 := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) hk2
    have hsum_e : (∑ i : Fin n, e i) = k := Finset.Nat.mem_antidiagonalTuple.mp he
    have hem : ∀ m' : Fin n, e m' < 3 := by
      intro m'
      have hle : e m' ≤ k := by
        calc e m' ≤ ∑ i : Fin n, e i :=
              Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ m')
          _ = k := hsum_e
      omega
    have hstep : (∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
          (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) ≤
        ∏ _m' : Fin n, (1 + (Csob * R) ^ 2) :=
      Finset.prod_le_prod
        (fun m' _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m') x _)
        (fun m' _ => hcell (e m') (hem m'))
    refine le_trans hstep ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hF_def]
    exact pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg (Csob * R))) hn2
  have hgrid_le : (∑ k ∈ Finset.range 3, ∑ n ∈ Finset.range (k + 1),
      ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
        ∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
            (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) ≤ cnt * F := by
    rw [hcnt_def, Finset.sum_mul]
    refine Finset.sum_le_sum (fun k hk => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun n hn => ?_)
    calc (∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m' : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m') x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m')
              (convexPerturbation (I := I) g₀ T 0 s)).toSection x))
        ≤ ∑ _e ∈ Finset.Nat.antidiagonalTuple n k, F :=
          Finset.sum_le_sum (fun e he => hprodcell k hk n hn e he)
      _ = (Finset.Nat.antidiagonalTuple n k).card • F := Finset.sum_const F
      _ = ((Finset.Nat.antidiagonalTuple n k).card : ℝ) * F := nsmul_eq_mul _ _
  have hdiff_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤
      CD 0 * (cnt * F) :=
    le_trans hCD0 (mul_le_mul_of_nonneg_left hgrid_le (hCD_nn 0))
  have hbg_le : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤ Kbg :=
    hKbg_bd x
  have hsplit : (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x =
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) +
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) := by
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
    abel
  have hfin : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤
      2 * (CD 0 * (cnt * F)) + 2 * Kbg := by
    rw [hsplit]
    have htri := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x)
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x)
    linarith
  rw [Real.sq_sqrt hsum_nn]
  exact hfin

set_option linter.unusedSectionVars false in
private theorem jointTotalSpaceRS_add_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option linter.unusedSectionVars false in
private theorem jointTotalSpaceRS_sub_local {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

set_option linter.unusedSectionVars false in
private theorem jointTotalSpaceRS_const_smul_local {r s : ℕ} {S : Set ℝ} (a : ℝ)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (a • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  refine ((contMDiffWithinAt_const (c := a)).smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul a (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      a (A p₀)

set_option linter.unusedSectionVars false in
private theorem jointTotalSpaceRS_smulFun_local {r s : ℕ} {S : Set ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (A : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (f p.2 • A p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hfm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => f p.2) :=
    hf.contMDiff.comp contMDiff_snd
  have hfj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => f p.2) ((Set.univ : Set M) ×ˢ S) p₀ :=
    (hfm.contMDiffAt).contMDiffWithinAt
  refine (hfj.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_smul (f p.2) (A p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_smul
      (f p₀.2) (A p₀)

private noncomputable def outerPairBilinChartα (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        (chartInvGramMatrix (I := I) g α x k l * K X (chartBasisVecFiber (I := I) α k x)) •
          (ContinuousLinearMap.flip Dd (chartBasisVecFiber (I := I) α l x))
      map_add' := fun X X' => by
        ext Y'
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_add, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring
      map_smul' := fun c X => by
        ext Y'
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
          ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
          ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        ring }

set_option linter.unusedSectionVars false in
private lemma outerPairBilinChartα_apply (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X X' : TangentSpace I x) :
    outerPairBilinChartα (I := I) g α K Dd X X' =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x k l *
          (K X (chartBasisVecFiber (I := I) α k x) *
            Dd X' (chartBasisVecFiber (I := I) α l x)) := by
  rw [outerPairBilinChartα, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

private lemma double_frame_bilin_trace_chartα
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (K Dd : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (B : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0) :
    ∑ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (K (chartBasisVecFiber (I := I) α m x) (chartBasisVecFiber (I := I) α k x) *
            Dd (chartBasisVecFiber (I := I) α n x) (chartBasisVecFiber (I := I) α l x))) := by
  classical
  have hinner : ∀ a, ∑ b, K (B a) (B b) * Dd (B a) (B b) =
      outerPairBilinChartα (I := I) g α K Dd (B a) (B a) := by
    intro a
    rw [outerPairBilinChartα_apply]
    have h := orthonormal_basis_bilin_trace_chartα (I := I) g α hxbase
      (innerPairBilin (I := I) x K Dd (B a)) B hB
    simp only [innerPairBilin_apply, smul_eq_mul] at h
    rw [h]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have hout := orthonormal_basis_bilin_trace_chartα (I := I) g α hxbase
    (outerPairBilinChartα (I := I) g α K Dd) B hB
  simp only [smul_eq_mul] at hout
  rw [hout]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [outerPairBilinChartα_apply]

private def toModelEvalCLM (s : ℕ) (x : M) (v : Fin s → E) :
    Tensor0SSpace s I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace s I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.toModel (𝕜 := ℝ) D v
      map_add' := fun D₁ D₂ => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul]
        rfl }

set_option linter.unusedSectionVars false in
private lemma toModelEvalCLM_apply (s : ℕ) (x : M) (v : Fin s → E)
    (D : Tensor0SSpace s I x) :
    toModelEvalCLM (I := I) (M := M) s x v D = Tensor0SSpace.toModel (𝕜 := ℝ) D v := rfl

private def pairFeedScalarCLM (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (toModelEvalCLM (I := I) (M := M) s x v).comp
        (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) s x
          ((tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p))
      map_add' := fun p p' => by
        rw [map_add, map_add, ContinuousLinearMap.comp_add]
      map_smul' := fun c p => by
        rw [map_smul, map_smul, RingHom.id_apply]
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          map_smul] }

set_option linter.unusedSectionVars false in
private lemma pairFeedScalarCLM_apply (s : ℕ) (x : M) (G : Tensor0SSpace (s + 2) I x)
    (v : Fin s → E) (p q : TangentSpace I x) :
    pairFeedScalarCLM (I := I) (M := M) s x G v p q =
      Tensor0SSpace.toModel (𝕜 := ℝ) G (Fin.cons (p : E) (Fin.cons (q : E) v)) := by
  rw [pairFeedScalarCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply, toModelEvalCLM_apply,
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (tensor0S_curry (𝕜 := ℝ) (I := I) (M := M) (s + 1) x G) p) (v0 := q) (vs := v),
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := G) (v0 := p) (vs := Fin.cons (q : E) v)]

private lemma curvatureRefoldMonomialBiContrFib_toModel_chartα
    (g : SmoothRiemannianMetric I M) (W : Π b : M, Tensor0SSpace 2 I b)
    (σp : Equiv.Perm (Fin 4)) (α : M) {x : M}
    (hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (G : Tensor0SSpace 4 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        (curvatureRefoldMonomialBiContrFib (I := I) (M := M) g W σp x G) v =
      ∑ m, ∑ n, chartInvGramMatrix (I := I) g α x m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I) g α x k l *
          (Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
              ![(chartBasisVecFiber (I := I) α m x : E),
                (chartBasisVecFiber (I := I) α k x : E)] *
            Tensor0SSpace.toModel (𝕜 := ℝ) G
              (fun i => (Fin.cons ((chartBasisVecFiber (I := I) α n x : E))
                (Fin.cons ((chartBasisVecFiber (I := I) α l x : E)) v) : Fin 4 → E)
                (σp i)))) := by
  classical
  have hBf_on : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  rw [show curvatureRefoldMonomialBiContrFib (I := I) (M := M) g W σp x =
      curvatureRefoldMonomialFibFixedFrame (I := I) (M := M) W σp
        (smoothOrthoFrame (I := I) g x) x from rfl,
    curvatureRefoldMonomialFibFixedFrame_toModel]
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel (𝕜 := ℝ) (W x)
          ![(smoothOrthoFrame (I := I) g x a x : E), (smoothOrthoFrame (I := I) g x b x : E)] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g x a x : E))
            (Fin.cons ((smoothOrthoFrame (I := I) g x b x : E)) v) : Fin 4 → E) (σp i)) =
      pairFeedScalarCLM (I := I) (M := M) 0 x (W x) ![]
          (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x) *
        pairFeedScalarCLM (I := I) (M := M) 2 x
          (slotPerm4Fib (I := I) (M := M) x σp G) v
          (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x b x) := by
    intro a b
    rw [pairFeedScalarCLM_apply, pairFeedScalarCLM_apply, slotPerm4Fib_toModel,
      ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsummand a b))]
  rw [double_frame_bilin_trace_chartα (I := I) g α hxbase
    (pairFeedScalarCLM (I := I) (M := M) 0 x (W x) ![])
    (pairFeedScalarCLM (I := I) (M := M) 2 x (slotPerm4Fib (I := I) (M := M) x σp G) v)
    (fun a => smoothOrthoFrame (I := I) g x a x) hBf_on]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine Finset.sum_congr rfl (fun n _ => ?_)
  refine congrArg (fun t => chartInvGramMatrix (I := I) g α x m n * t) ?_
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine congrArg (fun t => chartInvGramMatrix (I := I) g α x k l * t) ?_
  rw [pairFeedScalarCLM_apply, pairFeedScalarCLM_apply, slotPerm4Fib_toModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

private lemma curvatureRefoldMonomialBiContrFibAppY_chartCoord_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σp : Equiv.Perm (Fin 4))
    (Y : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun x : M => Tensor0SSpace 4 I x⟯)
    (α : M) (σc : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => Tensor0SSpace.toModel
        (curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp p.1 (Y p.1))
        ![(chartBasisVecFiber (I := I) α (σc 0) p.1 : E),
          (chartBasisVecFiber (I := I) α (σc 1) p.1 : E)])
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
  classical
  have htuple : ∀ (y : M) (n l : Fin (Module.finrank ℝ E)) (j : Fin 4),
      (Fin.cons ((chartBasisVecFiber (I := I) α n y : E))
        (Fin.cons ((chartBasisVecFiber (I := I) α l y : E))
          ![(chartBasisVecFiber (I := I) α (σc 0) y : E),
            (chartBasisVecFiber (I := I) α (σc 1) y : E)]) : Fin 4 → E) j =
      ((chartBasisVecFiber (I := I) α
        ((Fin.cons n (Fin.cons l ![σc 0, σc 1]) : Fin 4 → Fin (Module.finrank ℝ E)) j)
        y : E)) := by
    intro y n l j
    fin_cases j <;> rfl
  have hYtuple : ∀ w : Fin 4 → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Tensor0SSpace.toModel (𝕜 := ℝ) (Y p.1)
          (fun i => (chartBasisVecFiber (I := I) α (w i) p.1 : E)))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro w p₀ hp₀
    have hYon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
          (E := fun z : M => Tensor0SSpace 4 I z) p.1 (Y p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      (Y.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hv : ∀ i : Fin 4, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
          (chartBasisVecFiber (I := I) α (w i) p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) p₀ := fun i =>
      (chartBasisVec_jointContMDiffOn (I := I) α (w i) p₀
        ⟨hp₀.1, Set.mem_univ _⟩).mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
    exact TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 4
      (fun b : M => Y b) (hYon p₀ hp₀)
      (fun i => fun b : M => chartBasisVecFiber (I := I) α (w i) b) hv
  have hWpair : ∀ m k : Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Tensor0SSpace.toModel (𝕜 := ℝ) (W p.1)
          ![(chartBasisVecFiber (I := I) α m p.1 : E),
            (chartBasisVecFiber (I := I) α k p.1 : E)])
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro m k p₀ hp₀
    have hWon : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) p.1 (W p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      (hW.comp_contMDiffOn contMDiffOn_fst).mono (Set.subset_univ _)
    have hv : ∀ i : Fin 2, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
          (chartBasisVecFiber (I := I) α
            ((![m, k] : Fin 2 → Fin (Module.finrank ℝ E)) i) p.1))
        ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) p₀ := fun i =>
      (chartBasisVec_jointContMDiffOn (I := I) α
        ((![m, k] : Fin 2 → Fin (Module.finrank ℝ E)) i) p₀
        ⟨hp₀.1, Set.mem_univ _⟩).mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩)
    have happly := TensorMultilinear.contMDiffWithinAt_section_apply_prod (I := I) 2
      (fun b : M => W b) (hWon p₀ hp₀)
      (fun i => fun b : M => chartBasisVecFiber (I := I) α
        ((![m, k] : Fin 2 → Fin (Module.finrank ℝ E)) i) b) hv
    refine happly.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      congr 1
      funext i
      fin_cases i <;> rfl
    · congr 1
      funext i
      fin_cases i <;> rfl
  have hcomb : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
      (fun p : M × ℝ => ∑ m, ∑ n, chartInvGramMatrix (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) α p.1 m n *
        (∑ k, ∑ l, chartInvGramMatrix (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) α p.1 k l *
          (Tensor0SSpace.toModel (𝕜 := ℝ) (W p.1)
              ![(chartBasisVecFiber (I := I) α m p.1 : E),
                (chartBasisVecFiber (I := I) α k p.1 : E)] *
            Tensor0SSpace.toModel (𝕜 := ℝ) (Y p.1)
              (fun i => (Fin.cons ((chartBasisVecFiber (I := I) α n p.1 : E))
                (Fin.cons ((chartBasisVecFiber (I := I) α l p.1 : E))
                  ![(chartBasisVecFiber (I := I) α (σc 0) p.1 : E),
                    (chartBasisVecFiber (I := I) α (σc 1) p.1 : E)]) : Fin 4 → E)
                (σp i)))))
      ((chartAt H α).source ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    refine contMDiffOn_finset_sum (fun m _ => contMDiffOn_finset_sum (fun n _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T 0
      hδ hδZ α m n).mul ?_
    refine contMDiffOn_finset_sum (fun k _ => contMDiffOn_finset_sum (fun l _ => ?_))
    refine (realizedFam_chartInvGramMatrix_jointContMDiffOn_free (I := I) g₀ T 0
      hδ hδZ α k l).mul ?_
    refine (hWpair m k).mul ?_
    refine (hYtuple (fun i => (Fin.cons n (Fin.cons l ![σc 0, σc 1]) :
      Fin 4 → Fin (Module.finrank ℝ E)) (σp i))).congr (fun p _ => ?_)
    congr 1
    funext i
    exact htuple p.1 n l (σp i)
  refine hcomb.congr (fun p hp => ?_)
  have hxbase : p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
    exact hp.1
  rw [curvatureRefoldMonomialBiContrFib_toModel_chartα (I := I) (M := M)
    (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp α hxbase]

private lemma curvatureRefoldMonomialBiContrFibAppY_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σp : Equiv.Perm (Fin 4))
    (Y : Cₛ^∞⟮I; Tensor0SModel 4 ℝ E, fun x : M => Tensor0SSpace 4 I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) p.1
        (curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp p.1 (Y p.1)))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  set gfam : ℝ → SmoothRiemannianMetric I M :=
    fun s => realizedFam (I := I) g₀ T 0 hδ hδZ s with hgfam
  set S := realizedSmallSet (δ := δ) (δ' := δ) with hS
  intro p₀ hp₀
  set α := p₀.1 with hα
  set e := trivializationAt (Tensor0SModel 2 ℝ E)
    (fun z : M => Tensor0SSpace 2 I z) α with he
  set Bcmm := continuousMultilinearMap_basis (𝕜 := ℝ) (F := E) (chartModelBasis E) 2 with hBcmm
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hαsrc : α ∈ (chartAt H α).source := mem_chart_source H α
  have hαbase : α ∈ e.baseSet := by
    rw [he]; exact mem_baseSet_trivializationAt _ _ α
  have hnhd : (chartAt H α).source ×ˢ S ∈ nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S) := by
    refine mem_nhdsWithin.mpr ⟨(chartAt H α).source ×ˢ S,
      (chartAt H α).open_source.prod realizedSmallSet_isOpen, ⟨hαsrc, hp₀.2⟩, fun q hq => hq.1⟩
  have hcoordEach : ∀ σc : Fin 2 → Fin (Module.finrank ℝ E),
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ) ∞
        (fun p : M × ℝ => Bcmm.repr
          (e ⟨p.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
            (gfam p.2) W σp p.1 (Y p.1)⟩).2 σc)
        ((Set.univ : Set M) ×ˢ S) p₀ := by
    intro σc
    have hscal := curvatureRefoldMonomialBiContrFibAppY_chartCoord_jointContMDiffOn
      (I := I) (M := M) g₀ T hδ hδZ W hW σp Y α σc
    have hscalAt := (hscal p₀ ⟨hαsrc, hp₀.2⟩).mono_of_mem_nhdsWithin hnhd
    have hreadout : ∀ {q : M × ℝ}, q.1 ∈ e.baseSet →
        Bcmm.repr (e ⟨q.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
            (gfam q.2) W σp q.1 (Y q.1)⟩).2 σc =
          Tensor0SSpace.toModel (curvatureRefoldMonomialBiContrFib (I := I) (M := M)
              (gfam q.2) W σp q.1 (Y q.1))
            ![(chartBasisVecFiber (I := I) α (σc 0) q.1 : E),
              (chartBasisVecFiber (I := I) α (σc 1) q.1 : E)] := by
      intro q hqbase
      rw [continuousMultilinearMap_basis_repr]
      have hcoe : (e ⟨q.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (gfam q.2) W σp q.1 (Y q.1)⟩).2 =
          (e.linearMapAt ℝ q.1) (curvatureRefoldMonomialBiContrFib (I := I) (M := M)
            (gfam q.2) W σp q.1 (Y q.1)) :=
        (congrFun (Trivialization.coe_linearMapAt_of_mem (R := ℝ) (e := e) hqbase) _).symm
      rw [hcoe]
      have happly := TensorMultilinear.tensor0SBundle_linearMapAt_apply_of_mem (I := I) α q.1
        hqbase
        (curvatureRefoldMonomialBiContrFib (I := I) (M := M) (gfam q.2) W σp q.1 (Y q.1))
        (fun j => (chartModelBasis E) (σc j))
      rw [tensor0SSpace_continuousLinearEquiv_symm_apply] at happly
      rw [happly]
      change Tensor0SSpace.toModel (curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (gfam q.2) W σp q.1 (Y q.1))
          (fun j => (trivializationAt E (TangentSpace I) α).symmL ℝ q.1
            ((chartModelBasis E) (σc j))) = _
      congr 1
      funext j
      fin_cases j <;> rfl
    refine hscalAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hnhd] with q hq
      have hqbaseT : q.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]; exact hq.1
      have hqbase : q.1 ∈ e.baseSet := by rw [he]; exact hqbaseT
      exact hreadout hqbase
    · exact hreadout hαbase
  have hcoordVec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun p : M × ℝ => fun σc : Fin 2 → Fin (Module.finrank ℝ E) =>
        Bcmm.repr (e ⟨p.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (gfam p.2) W σp p.1 (Y p.1)⟩).2 σc)
      ((Set.univ : Set M) ×ˢ S) p₀ :=
    contMDiffWithinAt_pi_space.mpr (fun σc => hcoordEach σc)
  have hfinal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SModel 2 ℝ E) ∞
      (fun p : M × ℝ => (e ⟨p.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
        (gfam p.2) W σp p.1 (Y p.1)⟩).2)
      ((Set.univ : Set M) ×ˢ S) p₀ := by
    have hequiv := (Bcmm.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt
      (x := Bcmm.equivFun
        (e ⟨p₀.1, curvatureRefoldMonomialBiContrFib (I := I) (M := M)
          (gfam p₀.2) W σp p₀.1 (Y p₀.1)⟩).2)).comp_contMDiffWithinAt
      p₀ hcoordVec
    refine hequiv.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      exact (Bcmm.equivFun.symm_apply_apply _).symm
    · exact (Bcmm.equivFun.symm_apply_apply _).symm
  exact hfinal

private theorem curvatureRefoldMonomialCoeffField_realizedFam_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (W : Π b : M, Tensor0SSpace 2 I b)
    (hW : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) b (W b)))
    (σp : Equiv.Perm (Fin 4)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
        ((curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W hW σp).toSection p.1))
      ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
  have hCLM := contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SSpace 4 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ => curvatureRefoldMonomialBiContrFib (I := I) (M := M)
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) W σp p.1)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (fun Y => curvatureRefoldMonomialBiContrFibAppY_realizedFam_jointContMDiffOn
      (I := I) (M := M) g₀ T hδ hδZ W hW σp Y)
  refine hCLM.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [curvatureRefoldMonomialCoeffField_toSection]
  rfl

set_option linter.unusedVariables false in

theorem riemannPalatiniRefoldC2Family_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4)) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB)
      (δ := δ) (δ' := δ) := by
  classical
  have hmono : ∀ σp : Equiv.Perm (Fin 4),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
            (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σp).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
    fun σp => curvatureRefoldMonomialCoeffField_realizedFam_jointContMDiffOn
      (I := I) (M := M) g₀ T hδ hδZ
      (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σp
  have hker : ∀ q : Fin 4 → Equiv.Perm (Fin 4),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((curvatureRefoldKernelCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
            (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
            (q 0) (q 1) (q 2) (q 3)).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
    intro q
    have hadd := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ (hmono (q 0)) (hmono (q 1))
    have hsub1 := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hadd (hmono (q 2))
    have hsub2 := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hsub1 (hmono (q 3))
    have hhalf := jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) (1 / 2 : ℝ) _ hsub2
    refine hhalf.congr (fun p _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
    rw [curvatureRefoldKernelCoeffField, SmoothCcTensor.toSection_smul,
      SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub,
      SmoothCcTensor.toSection_add, ContMDiffSection.coe_smul, Pi.smul_apply,
      ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
      ContMDiffSection.coe_add, Pi.add_apply]
  have hsum := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ (hker qA) (hker qB)
  have hhalf := jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) (1 / 2 : ℝ) _ hsum
  have hfam := jointTotalSpaceRS_smulFun_local (I := I) (M := M) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ)) (f := fun t => t) contDiff_id _ hhalf
  refine hfam.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [riemannPalatiniRefoldC2Family, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_smul, Pi.smul_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    ContMDiffSection.coe_add, Pi.add_apply]

def deTurckLieCovDerivRefoldC2Family (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  s • ∑ i : Fin 3, ε i • ((1 / 2 : ℝ) •
    (curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) (q i)
      + curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        ((q i).trans (Equiv.swap (0 : Fin 4) 1))))

set_option linter.unusedSectionVars false in

@[simp] lemma deTurckLieCovDerivRefoldC2Family_zero (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) :
    deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε 0 = 0 := by
  rw [deTurckLieCovDerivRefoldC2Family, zero_smul]

set_option linter.unusedSectionVars false in

lemma toModel_ccTensorUnitValueSection_domDomCongrSection_swap
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M)
    (p q' : TangentSpace I x) :
    Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x)
        ![(p : E), (q' : E)] =
      Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
        ![(q' : E), (p : E)] := by
  have hbridge : ∀ (S : SmoothCcTensor g₀ 0 2),
      Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀ S x) =
        unitModel (I := I) (M := M) g₀ 2 S x := fun S => rfl
  rw [hbridge, hbridge, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

set_option linter.unusedSectionVars false in

theorem curvatureRefoldMonomialCoeffField_unitValue_trans_swap
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        (σ.trans (Equiv.swap (0 : Fin 4) 1)) =
      curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)) σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [curvatureRefoldMonomialCoeffField_toSection, curvatureRefoldMonomialCoeffField_toSection]
  refine congrArg TensorRSSpace.ofCLM ?_
  refine ContinuousLinearMap.ext (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [curvatureRefoldMonomialBiContrFib, curvatureRefoldMonomialBiContrFib,
    curvatureRefoldMonomialFibFixedFrame_toModel, curvatureRefoldMonomialFibFixedFrame_toModel]
  have hcons : ∀ (p q' : TangentSpace I x) (j : Fin 4),
      (Fin.cons (p : E) (Fin.cons (q' : E) v) : Fin 4 → E) ((Equiv.swap (0 : Fin 4) 1) j) =
        (Fin.cons (q' : E) (Fin.cons (p : E) v) : Fin 4 → E) j := by
    intro p q' j
    fin_cases j <;> rfl
  have hstep : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel (𝕜 := ℝ) (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E))
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E)) v) : Fin 4 → E)
            ((σ.trans (Equiv.swap (0 : Fin 4) 1)) i)) =
      Tensor0SSpace.toModel (𝕜 := ℝ) (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
          ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons ((smoothOrthoFrame (I := I) g₁ x b x : E))
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x a x : E)) v) : Fin 4 → E) (σ i)) := by
    intro a b
    congr 1
    refine congrArg _ ?_
    funext i
    exact hcons _ _ (σ i)
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hstep a b))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [toModel_ccTensorUnitValueSection_domDomCongrSection_swap]

set_option linter.unusedSectionVars false in

lemma ccTensorUnitValueSection_add (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (y : M) :
    ccTensorUnitValueSection (I := I) (M := M) g₀ (S + S') y =
      ccTensorUnitValueSection (I := I) (M := M) g₀ S y +
        ccTensorUnitValueSection (I := I) (M := M) g₀ S' y := by
  have h : ((S + S').toSection y : TensorRSSpace 0 2 I y) =
      (S.toSection y : TensorRSSpace 0 2 I y) + (S'.toSection y : TensorRSSpace 0 2 I y) := by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  rw [ccTensorUnitValueSection, ccTensorUnitValueSection, ccTensorUnitValueSection, h]
  rfl

set_option linter.unusedSectionVars false in

lemma ccTensorUnitValueSection_smul (g₀ : SmoothRiemannianMetric I M) (c : ℝ)
    (S : SmoothCcTensor g₀ 0 2) (y : M) :
    ccTensorUnitValueSection (I := I) (M := M) g₀ (c • S) y =
      c • ccTensorUnitValueSection (I := I) (M := M) g₀ S y := by
  have h : ((c • S).toSection y : TensorRSSpace 0 2 I y) =
      c • (S.toSection y : TensorRSSpace 0 2 I y) := by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [ccTensorUnitValueSection, ccTensorUnitValueSection, h]
  rfl

set_option linter.unusedSectionVars false in

theorem curvatureRefoldMonomialCoeffField_unitValue_add
    (g₀ g₁ : SmoothRiemannianMetric I M) (S S' : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (S + S'))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ (S + S')) σ =
      curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ
        + curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S')
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S') σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    curvatureRefoldMonomialCoeffField_toSection, curvatureRefoldMonomialCoeffField_toSection,
    curvatureRefoldMonomialCoeffField_toSection]
  refine tensorRSSpace_ext 4 2 x (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hadd : (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (TensorRSSpace.ofCLM (curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x)
        + TensorRSSpace.ofCLM (curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S') σ x))) G =
      curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x G
        + curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S') σ x G := rfl
  rw [hadd]
  simp only [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    TensorRSSpace.ofCLM]
  rw [curvatureRefoldMonomialBiContrFib, curvatureRefoldMonomialBiContrFib,
    curvatureRefoldMonomialBiContrFib, curvatureRefoldMonomialFibFixedFrame_toModel,
    curvatureRefoldMonomialFibFixedFrame_toModel, curvatureRefoldMonomialFibFixedFrame_toModel]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ccTensorUnitValueSection_add]
  simp only [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [add_mul]

set_option linter.unusedSectionVars false in

theorem curvatureRefoldMonomialCoeffField_unitValue_smul
    (g₀ g₁ : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (c • S))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ (c • S)) σ =
      c • curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    curvatureRefoldMonomialCoeffField_toSection, curvatureRefoldMonomialCoeffField_toSection]
  refine tensorRSSpace_ext 4 2 x (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hsmul : (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (c • TensorRSSpace.ofCLM (curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x))) G =
      c • curvatureRefoldMonomialBiContrFib (I := I) (M := M) g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x G := rfl
  rw [hsmul]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    TensorRSSpace.ofCLM]
  rw [curvatureRefoldMonomialBiContrFib, curvatureRefoldMonomialBiContrFib,
    curvatureRefoldMonomialFibFixedFrame_toModel, curvatureRefoldMonomialFibFixedFrame_toModel]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ccTensorUnitValueSection_smul]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

set_option linter.unusedSectionVars false in

theorem curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    (1 / 2 : ℝ) •
      (curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σ
        + curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
          (σ.trans (Equiv.swap (0 : Fin 4) 1))) =
      curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (symmS (I := I) (M := M) g₀ T)) σ := by
  rw [show curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (symmS (I := I) (M := M) g₀ T)) σ =
      curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ ((1 / 2 : ℝ) •
          (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ ((1 / 2 : ℝ) •
          (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T))) σ from by
    congr 1]
  rw [curvatureRefoldMonomialCoeffField_unitValue_smul,
    curvatureRefoldMonomialCoeffField_unitValue_add,
    curvatureRefoldMonomialCoeffField_unitValue_trans_swap]

set_option linter.unusedSectionVars false in

theorem deTurckLieCovDerivRefoldC2Family_eq_symmS_weight (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) :
    deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s =
      s • ∑ i : Fin 3, ε i •
        curvatureRefoldMonomialCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (ccTensorUnitValueSection (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ T))
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
            (symmS (I := I) (M := M) g₀ T)) (q i) := by
  rw [deTurckLieCovDerivRefoldC2Family]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  exact curvatureRefoldMonomialCoeffField_unitValue_pair_eq_symmS (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T 0 hδ hδZ s) T (q i)

set_option linter.unusedSectionVars false in

private theorem covDerivArmField_eq_dLaCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieCovDerivArmField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieDLaCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  refine ContMDiffSection.ext (fun x => ?_)
  rfl

set_option linter.unusedSectionVars false in

private theorem endoArmField_eq_dLbCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  refine ContMDiffSection.ext (fun x => ?_)
  rfl

/-- The endomorphism arm in the geometric DeTurck split is exactly the `DLb`
coefficient field used by the low-regularity intrinsic decomposition. -/
theorem endo_eq_dlb
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg :=
  endoArmField_eq_dLbCoeffField (I := I) (M := M) g₀ g₁ g_bg

set_option linter.unusedSectionVars false in

private theorem threeArmHjoint_add_local (g₀ : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => A s + B s) (δ := δ) (δ' := δ') := by
  have hadd := jointTotalSpaceRS_add_local (I := I) (M := M) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hA hB
  refine hadd.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

set_option linter.unusedSectionVars false in

private theorem threeArmHjoint_sub_local (g₀ : SmoothRiemannianMetric I M) {r : ℕ}
    (A B : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hA : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r A (δ := δ) (δ' := δ'))
    (hB : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r B (δ := δ) (δ' := δ')) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r
      (fun s => A s - B s) (δ := δ) (δ' := δ') := by
  have hsub := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := r) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1)
    hA hB
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r 2 I z) p.1 t) ?_
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

set_option linter.unusedSectionVars false in

private theorem covDerivArmField_realizedFam_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieCovDerivArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg) (δ := δ) (δ' := δ) := by
  have h := dLaBiContrFib_realizedFam_jointContMDiffOn (I := I) (M := M)
    g₀ T 0 hδ hδZ g_bg
  refine h.congr (fun p _ => ?_)
  rfl

set_option linter.unusedSectionVars false in

private theorem endoArmField_realizedFam_threeArmHjoint
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (g_bg : SmoothRiemannianMetric I M) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
      (fun s => deTurckLieEndoArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg) (δ := δ) (δ' := δ) := by
  have hC := deTurckLieCoeffField_realizedFam_jointContMDiff (I := I)
    g₀ T 0 hδ hδZ g_bg
  have hA := covDerivArmField_realizedFam_threeArmHjoint (I := I) (M := M)
    g₀ T hδ hδZ g_bg
  have hsub := jointTotalSpaceRS_sub_local (I := I) (M := M) (r := 2) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ))
    (fun p : M × ℝ => (deTurckLieCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1)
    (fun p : M × ℝ => (deTurckLieCovDerivArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1)
    hC hA
  refine hsub.congr (fun p _ => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 2 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 2 2 I z) p.1 t) ?_
  show (deTurckLieEndoArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1 =
    (deTurckLieCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1
      - (deTurckLieCovDerivArmField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).toSection p.1
  have hsplit : deTurckLieEndoArmField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg =
      deTurckLieCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg
        - deTurckLieCovDerivArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact (deTurckLieCoeffField_eq_covDerivArm_add_endoArm (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ p.2) g_bg).symm
  rw [hsplit, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

set_option linter.unusedSectionVars false in

private theorem iteratedCovGrad_smul_real (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) =
      c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih => rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in
private theorem bdExists_fixedField_rfns_jet (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c j := by
  have hex : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c :=
    fun j => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + j)
      (iteratedCovGrad (I := I) g₀ r s j F)
  choose c hc_nn hc using hex
  exact ⟨c, hc_nn, fun j x => hc j x⟩

set_option linter.unusedSectionVars false in
private lemma bdRfns_iCG_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A + B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A + B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (iteratedCovGrad (I := I) g r s j B).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _

set_option linter.unusedSectionVars false in
private lemma bdAppCcRS_sub_right (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    appCcRS (I := I) (M := M) g a b c Φ (W₁ - W₂) =
      appCcRS (I := I) (M := M) g a b c Φ W₁ - appCcRS (I := I) (M := M) g a b c Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((appCcRS (I := I) (M := M) g a b c Φ W₁ -
        appCcRS (I := I) (M := M) g a b c Φ W₂).toSection x) =
      (appCcRS (I := I) (M := M) g a b c Φ W₁).toSection x -
        (appCcRS (I := I) (M := M) g a b c Φ W₂).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((appCcRS (I := I) (M := M) g a b c Φ (W₁ - W₂)).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from (W₁ - W₂).toSection x) D))
      from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((appCcRS (I := I) (M := M) g a b c Φ W₁).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((appCcRS (I := I) (M := M) g a b c Φ W₂).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((W₁ - W₂).toSection x) = W₁.toSection x - W₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
      W₁.toSection x - W₂.toSection x) D) =
      (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D -
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D from rfl]
  rw [map_sub]

set_option linter.unusedSectionVars false in
private def bdVFSec (g₁ gA gB : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  (PDE.DeTurck.deTurckVF (I := I) g₁ gA : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) -
    (PDE.DeTurck.deTurckVF (I := I) g₁ gB : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)

set_option linter.unusedSectionVars false in
private lemma bdVFSec_apply (g₁ gA gB : SmoothRiemannianMetric I M) (b : M) :
    bdVFSec (I := I) (M := M) g₁ gA gB b =
      (PDE.DeTurck.deTurckVF (I := I) g₁ gA :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b -
        (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b := by
  rw [bdVFSec, ContMDiffSection.coe_sub, Pi.sub_apply]

private def bdXiFix (g₀ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 :=
  connDiffLoweredCc (I := I) g₀ g₀ - connDiffLoweredCc (I := I) g₀ g_bg

private def bdOmegaGen (g₀ g₁ gc : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  appCcRS (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
    (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc)

private def bdOmega (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  appCcRS (I := I) (M := M) g₀ 0 3 1 (cometricCastG0 (I := I) g₀ g₁)
    (bdXiFix (I := I) (M := M) g₀ g_bg)

set_option linter.unusedSectionVars false in
private lemma bdOmega_eq_sub (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    bdOmega (I := I) (M := M) g₀ g₁ g_bg =
      bdOmegaGen (I := I) (M := M) g₀ g₁ g_bg - bdOmegaGen (I := I) (M := M) g₀ g₁ g₀ := by
  rw [bdOmegaGen, bdOmegaGen, ← bdAppCcRS_sub_right, bdOmega]
  congr 1
  rw [bdXiFix]
  abel

set_option linter.unusedSectionVars false in
private lemma bdUnitModel_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A - B) x =
      unitModel (I := I) (M := M) g₀ s A x - unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub]

set_option linter.unusedSectionVars false in
private lemma bdUnitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) :
    unitModel (I := I) (M := M) g₀ s (A + B) x =
      unitModel (I := I) (M := M) g₀ s A x + unitModel (I := I) (M := M) g₀ s B x := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]

set_option linter.unusedSectionVars false in
private lemma bdConnDiffLoweredCc_unitModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel (connDiffLoweredCovec (I := I) g₀ g₁ x) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

set_option linter.unusedSectionVars false in
private lemma bdConnDiffLoweredCc_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [bdConnDiffLoweredCc_unitModel]
  rfl

set_option linter.unusedSectionVars false in
private lemma bdXiGen_unitModel_apply (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ gc x (m 0) (m 1)) (m 2) := by
  rw [bdUnitModel_sub, ContinuousMultilinearMap.sub_apply,
    bdConnDiffLoweredCc_unitModel_apply, bdConnDiffLoweredCc_unitModel_apply]
  rw [show g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) -
        g₀.inner x (PDE.DeTurck.connDiff (I := I) gc g₀ x (m 0) (m 1)) (m 2) =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1) -
        PDE.DeTurck.connDiff (I := I) gc g₀ x (m 0) (m 1)) (m 2) from by
    rw [map_sub, ContinuousLinearMap.sub_apply]]
  rw [connDiff_endpoint_cocycle (I := I) g₀ g₁ gc x (m 0) (m 1)]

set_option linter.unusedSectionVars false in
private lemma bdOmegaGen_toSection_unit (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (bdOmegaGen (I := I) (M := M) g₀ g₁ gc).toSection x)
      (unitTensor (I := I) (M := M) x) =
      cometricDoubleTraceFib (I := I) g₁ 1 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc).toSection x)
          (unitTensor (I := I) (M := M) x)) := by
  rw [bdOmegaGen, appCcRS_toSection]
  rfl

set_option linter.unusedSectionVars false in
private lemma bdOmegaGen_unitModel_apply (g₀ g₁ gc : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (bdOmegaGen (I := I) (M := M) g₀ g₁ gc) x
        (fun _ : Fin 1 => z) =
      g₀.inner x ((PDE.DeTurck.deTurckVF (I := I) g₁ gc :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) z := by
  classical
  rw [unitModel, bdOmegaGen_toSection_unit]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  have hdiag := cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₁ 1 x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) D
  rw [hdiag]
  rw [show Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) from
    map_sum (tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x) _ _]
  rw [ContinuousMultilinearMap.sum_apply]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) (fun _ : Fin 1 => z) =
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z := by
    intro i
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D
        (smoothOrthoFrame (I := I) g₁ x i x))
      (v0 := smoothOrthoFrame (I := I) g₁ x i x) (vs := fun _ : Fin 1 => z)]
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := D) (v0 := smoothOrthoFrame (I := I) g₁ x i x)
      (vs := Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
        (fun _ : Fin 1 => (show E from z)))]
    have hm : Tensor0SSpace.toModel D
        (Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
          (Fin.cons (show E from smoothOrthoFrame (I := I) g₁ x i x)
            (fun _ : Fin 1 => (show E from z)))) =
        unitModel (I := I) (M := M) g₀ 3
          (connDiffLoweredCc (I := I) g₀ g₁ - connDiffLoweredCc (I := I) g₀ gc) x
          ![smoothOrthoFrame (I := I) g₁ x i x, smoothOrthoFrame (I := I) g₁ x i x, z] := by
      rw [unitModel, ← hD]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hm, bdXiGen_unitModel_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z) =
      g₀.inner x (∑ i : Fin (Module.finrank ℝ E),
        PDE.DeTurck.connDiff (I := I) g₁ gc x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z from by
    rw [map_sum, ContinuousLinearMap.sum_apply]]
  rw [← PDE.DeTurck.deTurckVF_eq_orthoFrame_trace (I := I) g₁ gc x]

set_option linter.unusedSectionVars false in
private lemma bdOmega_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x
        (fun _ : Fin 1 => z) =
      g₀.inner x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) z := by
  rw [bdOmega_eq_sub, bdUnitModel_sub, ContinuousMultilinearMap.sub_apply,
    bdOmegaGen_unitModel_apply, bdOmegaGen_unitModel_apply, bdVFSec_apply]
  rw [map_sub, ContinuousLinearMap.sub_apply]

private def bdAlphaA (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (covGrad (I := I) (M := M) g₀ 0 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg))

private def bdCA (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
      (connDiffLoweredCc (I := I) g₀ g₁))

private def bdAlphaB (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  appCcRS (I := I) (M := M) g₀ 0 1 2 (bdCA (I := I) (M := M) g₀ g₁)
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg)

private def bdAlpha (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  bdAlphaA (I := I) (M := M) g₀ g₁ g_bg + bdAlphaB (I := I) (M := M) g₀ g₁ g_bg

set_option linter.unusedSectionVars false in
private lemma bdTensor0SCovDeriv01_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 1 V x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀) V x v)
        (Fin.cons (Y x) (fun i => Fin.elim0 i)) =
      directionalDerivAt (I := I)
          (fun b : M =>
            Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v)
              (fun i => Fin.elim0 i)) := by
  classical
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 V hV Y v (fun i => Fin.elim0 i)
  have hbase : Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
        (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) x v)
      (fun i => Fin.elim0 i) =
      directionalDerivAt (I := I)
        (fun b : M =>
          Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) x v]
    have hfun : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) =
        (fun b : M =>
          Tensor0SSpace.toModel (V b) (Fin.cons (Y b) (fun i => Fin.elim0 i))) := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := V b) (v0 := Y b) (vs := (fun i => Fin.elim0 i))]
    rw [hfun]
  rw [hpeel, hbase]

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
private lemma bdOmega_toSection_unit_eq_flat (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = fun _ : Fin 1 => m 0 := by
    funext k; fin_cases k; rfl
  rw [hm]
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => m 0) =
      g₀.inner x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) (m 0) :=
    bdOmega_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x (m 0)
  rw [hL]
  have hR : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x))
      (fun _ : Fin 1 => m 0) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)) (m 0) := by
    rw [cotangentToDual_apply]
    rfl
  rw [hR, cotangentToDual_g0FlatCLM]

set_option linter.unusedSectionVars false in
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
private lemma bdUnitEvalSection_bdOmega_toModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (b : M) (z : TangentSpace I b) :
    Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 1
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg) b)
      (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      g₀.inner b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) z := by
  rw [unitEvalSection_apply]
  rw [show (unitZeroSec (I := I) (M := M) b) = unitTensor (I := I) (M := M) b from rfl]
  rw [bdOmega_toSection_unit_eq_flat]
  have h : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b))
      (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b)) z := by
    rw [cotangentToDual_apply]
    change Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b))
        (Fin.cons (show E from z) (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b))
        (fun _ : Fin 1 => (show E from z))
    congr 1
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k
  rw [h, cotangentToDual_g0FlatCLM]

set_option linter.unusedSectionVars false in
private lemma bdAlphaA_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg) x ![u, w] =
      g₀.inner x
        ((LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) u := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x u
  rw [bdAlphaA, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, w] : Fin 2 → TangentSpace I x) ((Equiv.swap (0 : Fin 2) 1) i)) =
      ![w, u] from by
    funext i; fin_cases i <;> simp]
  rw [unitModel]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 1
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x (unitTensor (I := I) (M := M) x) ![w, u]]
  rw [show (![w, u] : Fin 2 → TangentSpace I x) 0 = w from rfl]
  rw [show Matrix.vecTail (![w, u] : Fin 2 → TangentSpace I x) = ![u] from by
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 1
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x w]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ 1
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection x w]
  have hV : TensorSectionMDiffAt (I := I) 1
      (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) x :=
    ((contMDiff_unitEvalSection (I := I) (M := M) g₀ 1
      (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) x).mdifferentiableAt (by simp)
  have hgen : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 1 I y from
        (bdOmega (I := I) (M := M) g₀ g₁ g_bg).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
      unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) := rfl
  rw [hgen]
  rw [show (![u] : Fin 1 → TangentSpace I x) =
      Fin.cons (Y x) (fun i => Fin.elim0 i) from by
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hYx]; rfl]
  rw [bdTensor0SCovDeriv01_consEval_leibnizDefect (I := I) (M := M) g₀
    (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) hV Y w]
  have hscal : (fun b : M =>
      Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) b)
        (Fin.cons (Y b) (fun i => Fin.elim0 i))) =
      (fun b : M => g₀.inner b (bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) (Y b)) := by
    funext b
    exact bdUnitEvalSection_bdOmega_toModel (I := I) (M := M) g₀ g₁ g_bg b (Y b)
  rw [hscal, directionalDerivAt_eq]
  have hlei := leibniz_inner (I := I) (M := M) g₀
    (V := fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) (W := fun b => Y b)
    (bdVFSec (I := I) (M := M) g₁ g_bg g₀).contMDiff Y.contMDiff (x := x) w
  rw [hlei]
  rw [show Tensor0SSpace.toModel
      (unitEvalSection (I := I) (M := M) g₀ 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x)
      (Fin.cons ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w)
        (fun i => Fin.elim0 i)) =
      g₀.inner x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)
        ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w) from
    bdUnitEvalSection_bdOmega_toModel (I := I) (M := M) g₀ g₁ g_bg x _]
  rw [hYx]
  ring

set_option linter.unusedSectionVars false in
private lemma bdInterior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
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
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (g0FlatCLM cotangentToDual_g0FlatCLM inverseMetricSharpFib_g0FlatCLM) in
private lemma bdAlphaB_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg) x ![u, w] =
      g₀.inner x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) u := by
  classical
  rw [unitModel, bdAlphaB, appCcRS_toSection]
  rw [ContinuousLinearMap.comp_apply]
  rw [bdOmega_toSection_unit_eq_flat (I := I) (M := M) g₀ g₁ g_bg x]
  rw [bdCA, cometricRaiseSlot0Field_toSection]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D
    (g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x))]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)]
  rw [bdInterior_product_toModel_eval (I := I) (M := M) (1 + 1) x
    (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) D ![u, w]]
  have hDm : Tensor0SSpace.toModel D
      (Fin.cons (show E from bdVFSec (I := I) (M := M) g₁ g_bg g₀ x)
        (fun k : Fin 2 => (show E from (![u, w] : Fin 2 → TangentSpace I x) k))) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (connDiffLoweredCc (I := I) g₀ g₁)) x
        ![bdVFSec (I := I) (M := M) g₁ g_bg g₀ x, u, w] := by
    rw [unitModel, ← hD]
    rfl
  rw [hDm, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![bdVFSec (I := I) (M := M) g₁ g_bg g₀ x, u, w] :
        Fin 3 → TangentSpace I x)
        ((Equiv.swap (1 : Fin 3) 2) i)) =
      ![bdVFSec (I := I) (M := M) g₁ g_bg g₀ x, w, u] from by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]]
  rw [bdConnDiffLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

set_option linter.unusedSectionVars false in
private lemma bdLeviCivita_toFun_sub (g₀ : SmoothRiemannianMetric I M)
    (A B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (w : TangentSpace I x) :
    (LeviCivita (I := I) g₀).toFun (fun b => A b - B b) x w =
      (LeviCivita (I := I) g₀).toFun (fun b => A b) x w -
        (LeviCivita (I := I) g₀).toFun (fun b => B b) x w := by
  have hsub : (fun b : M => A b - B b) =
      (fun b : M => A b) + (fun b : M => ((-1 : ℝ) • B) b) := by
    funext b
    rw [Pi.add_apply, ContMDiffSection.coe_smul, Pi.smul_apply, neg_one_smul,
      sub_eq_add_neg]
  have hadd := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.add
    (σ := fun b : M => A b) (σ' := fun b : M => ((-1 : ℝ) • B) b) (x := x)
    (A.mdifferentiableAt (x := x)) (((-1 : ℝ) • B).mdifferentiableAt (x := x))
  have hsmul := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.smul_const
    (σ := fun b : M => B b) (a := (-1 : ℝ)) (x := x) (B.mdifferentiableAt (x := x))
  have hcoe : (fun b : M => ((-1 : ℝ) • B) b) = (-1 : ℝ) • (fun b : M => B b) := by
    funext b
    rw [ContMDiffSection.coe_smul]
  rw [hsub, hadd]
  rw [hcoe, hsmul]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, neg_one_smul,
    sub_eq_add_neg]

set_option linter.unusedSectionVars false in
private lemma bdWEndo_eq_covDeriv_add_connDiff (g₀ g₁ gc : SmoothRiemannianMetric I M)
    (x : M) (w : TangentSpace I x) :
    deTurckLieWEndo (I := I) g₁ gc x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w +
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ gc :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w := by
  have hcd := PDE.DeTurck.connDiff_apply (I := I) g₁ g₀
    (σ := fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) (x := x)
    (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯).mdifferentiableAt w
  have hEndo : deTurckLieWEndo (I := I) g₁ gc x w =
      (LeviCivita (I := I) g₁).toFun
        (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ gc :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w := rfl
  rw [hEndo, hcd]
  abel

set_option linter.unusedSectionVars false in
private lemma bdWEndo_sub_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (w : TangentSpace I x) :
    deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w +
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w := by
  rw [bdWEndo_eq_covDeriv_add_connDiff (I := I) (M := M) g₀ g₁ g_bg x w,
    bdWEndo_eq_covDeriv_add_connDiff (I := I) (M := M) g₀ g₁ g₀ x w]
  have hLC : (LeviCivita (I := I) g₀).toFun
      (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w =
      (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w -
        (LeviCivita (I := I) g₀).toFun
          (fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b) x w := by
    have h := bdLeviCivita_toFun_sub (I := I) (M := M) g₀
      (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x w
    rw [← h]
    rfl
  have hcd : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) w := by
    rw [bdVFSec_apply, map_sub, ContinuousLinearMap.sub_apply]
  rw [hLC, hcd]
  abel

set_option linter.unusedSectionVars false in
private lemma bdCotangentToDual_slotInsertEndoFib (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) w =
      cotangentToDual (I := I) om (Λ w) := by
  rw [cotangentToDual_apply, cotangentToDual_apply]
  rw [show (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) (fun _ : Fin 1 => w)
      = Tensor0SSpace.toModel (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om)
          (fun _ : Fin 1 => (show E from w)) from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Function.update (fun _ : Fin 1 => (show E from w)) 0
        (Λ ((fun _ : Fin 1 => (show E from w)) 0)) =
      (fun _ : Fin 1 => (show E from Λ w)) from by
    funext k; fin_cases k; simp]
  rfl

set_option linter.unusedSectionVars false in
private lemma bdCotangentToDual_cometricRaise_bdAlpha
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (bdAlpha (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) w =
      unitModel (I := I) (M := M) g₀ 2 (bdAlpha (I := I) (M := M) g₀ g₁ g_bg) x
        ![inverseMetricSharpFib (I := I) g₀ x om, w] := by
  rw [cotangentToDual_apply]
  rw [cometricRaiseSlot0Field_toSection]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (bdAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w) : ℝ) =
      Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (bdAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => w) from rfl]
  rw [bdInterior_product_toModel_eval (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
        (bdAlpha (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
  rw [unitModel]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun j' => j'.elim0) j
    rfl

set_option linter.unusedSectionVars false in
private theorem bdWEndoInsert_sub_eq_cometricRaise
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (bdAlpha (I := I) (M := M) g₀ g₁ g_bg) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [bdCotangentToDual_cometricRaise_bdAlpha (I := I) (M := M) g₀ g₁ g_bg x om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        ((deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x -
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀).toSection x)) om =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x) om -
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀).toSection x) om from rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (deTurckLieWEndo (I := I) g₁ g_bg x) om from rfl]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (deTurckLieWEndo (I := I) g₁ g₀ x) om from rfl]
  rw [show cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g_bg x) om -
          slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g₀ x) om) w =
      cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g_bg x) om) w -
        cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
            (deTurckLieWEndo (I := I) g₁ g₀ x) om) w from by
    rw [show cotangentToDual (I := I)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g_bg x) om -
            slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g₀ x) om) =
        cotangentToDualLinear (I := I) (x := x)
          (slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g_bg x) om -
            slotInsertEndoFib (I := I) (M := M) 1 0 x
              (deTurckLieWEndo (I := I) g₁ g₀ x) om) from rfl]
    rw [map_sub]
    rfl]
  rw [bdCotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (deTurckLieWEndo (I := I) g₁ g_bg x) om w]
  rw [bdCotangentToDual_slotInsertEndoFib (I := I) (M := M) x
    (deTurckLieWEndo (I := I) g₁ g₀ x) om w]
  rw [show cotangentToDual (I := I) om (deTurckLieWEndo (I := I) g₁ g_bg x w) -
        cotangentToDual (I := I) om (deTurckLieWEndo (I := I) g₁ g₀ x w) =
      cotangentToDual (I := I) om
        (deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w) from by
    rw [show cotangentToDual (I := I) om
          (deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w) =
        cotangentToDualLinear (I := I) (x := x) om
          (deTurckLieWEndo (I := I) g₁ g_bg x w - deTurckLieWEndo (I := I) g₁ g₀ x w)
        from rfl]
    rw [map_sub]
    rfl]
  rw [bdWEndo_sub_eq (I := I) (M := M) g₀ g₁ g_bg x w]
  rw [bdAlpha, bdUnitModel_add, ContinuousMultilinearMap.add_apply,
    bdAlphaA_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w,
    bdAlphaB_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w +
          PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
      cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) +
        cotangentToDual (I := I) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from by
    rw [show ∀ v : TangentSpace I x, cotangentToDual (I := I) om v =
        cotangentToDualLinear (I := I) (x := x) om v from fun v => rfl]
    exact map_add _ _ _]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        ((LeviCivita (I := I) g₀).toFun
          (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) from by
    rw [show cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) =
        cotangentToDualLinear (I := I) (x := x) om
          ((LeviCivita (I := I) g₀).toFun
            (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w) from rfl]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om _).symm]
  rw [show cotangentToDual (I := I) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from by
    rw [show cotangentToDual (I := I) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w) from rfl]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om _).symm]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
    ((LeviCivita (I := I) g₀).toFun
      (fun b => bdVFSec (I := I) (M := M) g₁ g_bg g₀ b) x w),
    g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (bdVFSec (I := I) (M := M) g₁ g_bg g₀ x) w)]

set_option linter.unusedSectionVars false in
private lemma bdICG_succ_cometricDT_zero (g₀ : SmoothRiemannianMetric I M) (s m : ℕ) :
    iteratedCovGrad (I := I) g₀ (s + 2) s (m + 1)
      (cometricDoubleTraceField (I := I) g₀ s) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ s
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

set_option linter.unusedSectionVars false in
private lemma bdRfns_zero_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      ((0 : SmoothCcTensor g₀ r s).toSection x) = 0 := by
  rw [show ((0 : SmoothCcTensor g₀ r s).toSection x) = (0 : TensorRSSpace r s I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ r s x

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdCometricCastG0_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
            ((iteratedCovGrad (I := I) g₀ 3 1 j
              (cometricCastG0 (I := I) g₀ g₁)).toSection x) ≤
          C j * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (j + 1) := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cfix, hcfix_nn, hcfix⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 3 1
    (cometricDoubleTraceField (I := I) g₀ 1)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun j => 2 * cfix 0 +
      2 * (appCcGdiag (E := E) j * (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l)),
    fun j => by
      have h1 := hcfix_nn 0
      have h2 : 0 ≤ appCcGdiag (E := E) j *
          (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l) :=
        mul_nonneg (appCcGdiag_nonneg (E := E) j) (mul_nonneg (hcfix_nn 0)
          (Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (hCD_nn l)))
      linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hW1 : (1 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (j + 1) :=
    Combinatorics.one_le_antidiagonalTupleGridWindow b hb (by omega)
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by linarith
  rw [cometricCastG0_eq_doubleTrace_add_appCcRS (I := I) (M := M) g₀ g₁]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 3 1 j
    (cometricDoubleTraceField (I := I) g₀ 1)
    (appCcRS (I := I) (M := M) g₀ 3 3 1 (cometricDoubleTraceField (I := I) g₀ 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 2 (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
    x) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
      ((iteratedCovGrad (I := I) g₀ 3 1 j
        (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) ≤ cfix 0 := by
    match j with
    | 0 => exact hcfix 0 x
    | (m + 1) =>
        rw [bdICG_succ_cometricDT_zero (I := I) (M := M) g₀ 1 m]
        rw [bdRfns_zero_toSection]
        exact hcfix_nn 0
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
      ((iteratedCovGrad (I := I) g₀ 3 1 j
        (appCcRS (I := I) (M := M) g₀ 3 3 1 (cometricDoubleTraceField (I := I) g₀ 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 2
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) ≤
      (appCcGdiag (E := E) j * (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l)) *
        Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ j 3 3 1
      (cometricDoubleTraceField (I := I) g₀ 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 2
        (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x) ?_
    have hzero : ∀ i' ∈ Finset.range (j + 1), i' ≠ 0 →
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i'
              (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) = 0 := by
      intro i' _ hi'0
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi'0
      rw [bdICG_succ_cometricDT_zero (I := I) (M := M) g₀ 1 m]
      rw [bdRfns_zero_toSection, zero_mul]
    have hsum_eq : (∑ i' ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i'
              (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + 0) x
            ((iteratedCovGrad (I := I) g₀ 3 1 0
              (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - 0),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
              ((iteratedCovGrad (I := I) g₀ 3 3 l
                (slotInsertEndoCc (I := I) (M := M) g₀ 2
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) := by
      refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_
      intro i' hi' hi'0
      exact hzero i' hi' hi'0
    rw [hsum_eq]
    have hslot : (∑ l ∈ Finset.range (j + 1 - 0),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
          ((iteratedCovGrad (I := I) g₀ 3 3 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)) ≤
        (∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l) *
          Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
        rw [show j + 1 - 0 = j + 1 from rfl, Finset.sum_mul]
        refine Finset.sum_le_sum fun l hl => ?_
        rw [Finset.mem_range] at hl
        refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 2
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) l x) ?_
        have h2 := hCD g₁ P htie hδ_le hδ0 hbound l x
        calc (Module.finrank ℝ E : ℝ) ^ 2 *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (slotInsertEndoCc (I := I) (M := M) g₀ 0
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
            ≤ fr ^ 2 * (CD l * ∑ n ∈ Finset.range (l + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n l,
                  ∏ m : Fin n, b (e m)) := by
              rw [← hfr_def]
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = (fr ^ 2 * CD l) * Combinatorics.antidiagonalTupleGrid b l := by
              rw [Combinatorics.antidiagonalTupleGrid]
              ring
          _ ≤ (fr ^ 2 * CD l) * Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg (by positivity) (hCD_nn l))
              exact Combinatorics.antidiagonalTupleGrid_le_window b hb (by omega)
    have hfix0 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + 0) x
        ((iteratedCovGrad (I := I) g₀ 3 1 0
          (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) ≤ cfix 0 := hcfix 0 x
    have hsum_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (j + 1 - 0),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + l) x
          ((iteratedCovGrad (I := I) g₀ 3 3 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 2
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 3 (3 + l) x _
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hfix0 hslot hsum_nn (hcfix_nn 0)) (appCcGdiag_nonneg (E := E) j)) ?_
    rw [← mul_assoc, ← mul_assoc]
    rw [mul_assoc (appCcGdiag (E := E) j) (cfix 0)]
  have hA' : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + j) x
      ((iteratedCovGrad (I := I) g₀ 3 1 j
        (cometricDoubleTraceField (I := I) g₀ 1)).toSection x) ≤
      cfix 0 * Combinatorics.antidiagonalTupleGridWindow b (j + 1) := by
    refine le_trans hA ?_
    nlinarith [hcfix_nn 0]
  have hB_nn : (0 : ℝ) ≤ appCcGdiag (E := E) j *
      (cfix 0 * ∑ l ∈ Finset.range (j + 1), fr ^ 2 * CD l) :=
    mul_nonneg (appCcGdiag_nonneg (E := E) j) (mul_nonneg (hcfix_nn 0)
      (Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (hCD_nn l)))
  nlinarith [hA', hB, hW_nn, hcfix_nn 0]

set_option linter.unusedSectionVars false in
private lemma bdConnDiffSection_eq_cometricRaise (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [bdInterior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x
          ![u, YZ 0, YZ 1] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![YZ 0, YZ 1, u] from by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]]
  rw [bdConnDiffLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

set_option linter.unusedSectionVars false in
private lemma bdRfns_iCG_connDiffLoweredCc_eq_connDiffSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [bdConnDiffSection_eq_cometricRaise]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdCA_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j
              (bdCA (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C j * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (j + 2) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  refine ⟨CA, hCA_nn, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j
        (bdCA (I := I) (M := M) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 3 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
            (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) := by
    rw [bdCA]
    exact rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
      (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (connDiffLoweredCc (I := I) g₀ g₁)) j x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 3 j
        (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 3 j
          (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (1 : Fin 3) 2) (connDiffLoweredCc (I := I) g₀ g₁) j x
  rw [h1, h2, bdRfns_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ j x]
  refine le_trans (hCA g₁ P htie hδ_le hδ0 hbound j x) ?_
  rw [show Combinatorics.antidiagonalTupleGridWindow b (j + 2) =
      ∑ k ∈ Finset.range (j + 2), Combinatorics.antidiagonalTupleGrid b k from rfl]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdOmega_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 1 l
              (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (l + 1) := by
  classical
  obtain ⟨Cg, hCg_nn, hCg⟩ := bdCometricCastG0_gridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨cxi, hcxi_nn, hcxi⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 0 3
    (bdXiFix (I := I) (M := M) g₀ g_bg)
  refine ⟨fun l => appCcGdiag (E := E) l *
      ∑ i' ∈ Finset.range (l + 1), Cg i' * ∑ l' ∈ Finset.range (l + 1 - i'), cxi l',
    fun l => mul_nonneg (appCcGdiag_nonneg (E := E) l)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCg_nn i')
        (Finset.sum_nonneg fun l' _ => hcxi_nn l')), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (l + 1) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (l + 1)
  rw [bdOmega]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ l 0 3 1
    (cometricCastG0 (I := I) g₀ g₁)
    (bdXiFix (I := I) (M := M) g₀ g_bg) x) ?_
  have hcell : ∀ i' ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 1 i'
            (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
        ∑ l' ∈ Finset.range (l + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 3 l'
              (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x) ≤
      (Cg i' * ∑ l' ∈ Finset.range (l + 1 - i'), cxi l') *
        Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
        ((iteratedCovGrad (I := I) g₀ 3 1 i'
          (cometricCastG0 (I := I) g₀ g₁)).toSection x) ≤
        Cg i' * Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by
      refine le_trans (hCg g₁ P htie hδ_le hδ0 hbound i' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCg_nn i')
      exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    have hA2 : (∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x)) ≤
        ∑ l' ∈ Finset.range (l + 1 - i'), cxi l' :=
      Finset.sum_le_sum fun l' _ => hcxi l' x
    have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x) :=
      Finset.sum_nonneg fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + l') x _
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + i') x
            ((iteratedCovGrad (I := I) g₀ 3 1 i'
              (cometricCastG0 (I := I) g₀ g₁)).toSection x) *
          ∑ l' ∈ Finset.range (l + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 3 l'
                (bdXiFix (I := I) (M := M) g₀ g_bg)).toSection x)
        ≤ (Cg i' * Combinatorics.antidiagonalTupleGridWindow b (l + 1)) *
            ∑ l' ∈ Finset.range (l + 1 - i'), cxi l' :=
          mul_le_mul hA1 hA2 hsum_nn (mul_nonneg (hCg_nn i') hW_nn)
      _ = (Cg i' * ∑ l' ∈ Finset.range (l + 1 - i'), cxi l') *
            Combinatorics.antidiagonalTupleGridWindow b (l + 1) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) l)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdAlphaA_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i
              (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨Cω, hCω_nn, hCω⟩ := bdOmega_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun i => Cω (i + 1), fun i => hCω_nn (i + 1), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  rw [bdAlphaA]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1)
    (covGrad (I := I) (M := M) g₀ 0 1 (bdOmega (I := I) (M := M) g₀ g₁ g_bg)) i x]
  rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 1 i
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x]
  exact hCω g₁ P htie hδ_le hδ0 hbound (i + 1) x

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdAlphaB_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i
              (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := bdCA_gridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨Cω, hCω_nn, hCω⟩ := bdOmega_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun i => appCcGdiag (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), CA i' * ∑ l' ∈ Finset.range (i + 1 - i'),
        Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l',
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCA_nn i')
        (Finset.sum_nonneg fun l' _ => mul_nonneg (hCω_nn l')
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  rw [bdAlphaB]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 0 1 2
    (bdCA (I := I) (M := M) g₀ g₁)
    (bdOmega (I := I) (M := M) g₀ g₁ g_bg) x) ?_
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 1 2 i'
            (bdCA (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l' ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 1 l'
              (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
      (CA i' * ∑ l' ∈ Finset.range (i + 1 - i'),
        Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l') *
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i'
          (bdCA (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CA i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 2) :=
      hCA g₁ P htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l' ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 1 l'
            (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
        ∑ l' ∈ Finset.range (i + 1 - i'),
          Cω l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 1) :=
      Finset.sum_le_sum fun l' _ => hCω g₁ P htie hδ_le hδ0 hbound l' x
    have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (1 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 1 l'
            (bdOmega (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
      Finset.sum_nonneg fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (1 + l') x _
    have hA1_rhs_nn : (0 : ℝ) ≤ CA i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 2) :=
      mul_nonneg (hCA_nn i') (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i' + 2))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (CA i' * ∑ l' ∈ Finset.range (i + 1 - i'),
        Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l') *
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) =
        ∑ l' ∈ Finset.range (i + 1 - i'),
          (CA i' * (Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l')) *
            Combinatorics.antidiagonalTupleGridWindow b (i + 2) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l' hl' => ?_
    rw [Finset.mem_range] at hl'
    have hpair : Combinatorics.antidiagonalTupleGridWindow b (i' + 2) *
        Combinatorics.antidiagonalTupleGridWindow b (l' + 1) ≤
        Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l' *
          Combinatorics.antidiagonalTupleGridWindow b (i' + 1 + l' + 1) := by
      have h := Combinatorics.antidiagonalTupleGridWindow_mul_le b hb (i' + 1) l'
      rw [show i' + 1 + 1 = i' + 2 from rfl] at h
      exact h
    have hmono : Combinatorics.antidiagonalTupleGridWindow b (i' + 1 + l' + 1) ≤
        Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
      Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    calc CA i' * Combinatorics.antidiagonalTupleGridWindow b (i' + 2) *
          (Cω l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 1))
        = (CA i' * Cω l') * (Combinatorics.antidiagonalTupleGridWindow b (i' + 2) *
            Combinatorics.antidiagonalTupleGridWindow b (l' + 1)) := by ring
      _ ≤ (CA i' * Cω l') * (Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l' *
            Combinatorics.antidiagonalTupleGridWindow b (i' + 1 + l' + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hCA_nn i') (hCω_nn l')
      _ ≤ (CA i' * Cω l') * (Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l' *
            Combinatorics.antidiagonalTupleGridWindow b (i + 2)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (hCA_nn i') (hCω_nn l'))
          refine mul_le_mul_of_nonneg_left hmono ?_
          exact Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _
      _ = (CA i' * (Cω l' * Combinatorics.antidiagonalTupleGridWindowMulConst (i' + 1) l')) *
            Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdWEndoInsertDiff_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨CAa, hCAa_nn, hCAa⟩ := bdAlphaA_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  obtain ⟨CAb, hCAb_nn, hCAb⟩ := bdAlphaB_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨fun i => 2 * CAa i + 2 * CAb i,
    fun i => by have h1 := hCAa_nn i; have h2 := hCAb_nn i; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  rw [bdWEndoInsert_sub_eq_cometricRaise (I := I) (M := M) g₀ g₁ g_bg]
  rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (bdAlpha (I := I) (M := M) g₀ g₁ g_bg) i x]
  rw [bdAlpha]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 2 i
    (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg)
    (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg) x) ?_
  have h1 := hCAa g₁ P htie hδ_le hδ0 hbound i x
  have h2 := hCAb g₁ P htie hδ_le hδ0 hbound i x
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  nlinarith [h1, h2, hW_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 2 i
        (bdAlphaA (I := I) (M := M) g₀ g₁ g_bg)).toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 2 i
        (bdAlphaB (I := I) (M := M) g₀ g₁ g_bg)).toSection x)]

set_option linter.unusedSectionVars false in
private theorem bdDLb_eq_slotInsert_sum
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D)
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x) D
        + (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D
      = deTurckLieDLbFib (I := I) g₁ g_bg x D from rfl]
  rw [deTurckLieDLbFib_toModel (I := I) g₁ g_bg x D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x) D
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (deTurckLieWEndo (I := I) g₁ g_bg x) D from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (deTurckLieWEndo (I := I) g₁ g_bg x) D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D
      = reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x) D]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x)
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
            ((slotInsertEndoCc (I := I) (M := M) g₀ 1
              (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)) from by
    rw [rsDomDomCongrSection_toSection]]
  rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
    ((slotInsertEndoCc (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (deTurckLieWEndo (I := I) g₁ g_bg x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))) from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (deTurckLieWEndo (I := I) g₁ g_bg x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))
    (fun i => m ((Equiv.swap (0 : Fin 2) 1) i))]
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have harg : (fun k => Function.update (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
        (deTurckLieWEndo (I := I) g₁ g_bg x
          ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
        ((Equiv.swap (0 : Fin 2) 1) k))
      = Function.update m 1 (deTurckLieWEndo (I := I) g₁ g_bg x (m 1)) := by
    funext k
    have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := Equiv.swap_apply_left 0 1
    have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := Equiv.swap_apply_right 0 1
    simp only [Function.update_apply]
    rw [hswap0, Equiv.swap_apply_self]
    have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
      apply propext
      constructor
      · intro h
        have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
        rwa [Equiv.swap_apply_self, hswap0] at h2
      · intro h
        rw [h, hswap1]
    simp only [hcond]
  rw [harg]

set_option linter.unusedSectionVars false in
private lemma bdSlotInsertEndoCc_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s A - slotInsertEndoCc (I := I) (M := M) g₀ s B =
      slotInsertEndoCc (I := I) (M := M) g₀ s (A - B) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A - B) x) = A x - B x from by rw [ContMDiffSection.coe_sub]; rfl]
  rw [slotInsertEndoFib_sub_left]

set_option linter.unusedSectionVars false in
private lemma bdReindexSwap_sub (g₀ : SmoothRiemannianMetric I M)
    (X Y : SmoothCcTensor g₀ 2 2) :
    reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
        (Equiv.swap (0 : Fin 2) 1) -
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
        (Equiv.swap (0 : Fin 2) 1) =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) (X - Y))
        (Equiv.swap (0 : Fin 2) 1) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
        (Equiv.swap (0 : Fin 2) 1) -
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
        (Equiv.swap (0 : Fin 2) 1)).toSection x) =
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
        (Equiv.swap (0 : Fin 2) 1)).toSection x -
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
        (Equiv.swap (0 : Fin 2) 1)).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  have hpt : ∀ (Z : SmoothCcTensor g₀ 2 2),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Z)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from Z.toSection x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))))
        (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) := by
    intro Z
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Z)
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              Z).toSection x) D from rfl]
    rw [reindexCoeffFibGen_apply]
    rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          Z).toSection x) =
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
            (Z.toSection x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show Tensor0SSpace.toModel
      (((reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
          (Equiv.swap (0 : Fin 2) 1)).toSection x -
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m -
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m from by
    rw [show (((reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
          (Equiv.swap (0 : Fin 2) 1)).toSection x -
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) X)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) -
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) Y)
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D) from rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]]
  rw [hpt X, hpt Y, hpt (X - Y)]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from (X - Y).toSection x)
      (Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
          (Tensor0SSpace.toModel D)))) =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from X.toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))) -
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from Y.toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))) from by
    rw [show ((X - Y).toSection x) = X.toSection x - Y.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rfl]
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

set_option linter.unusedSectionVars false in
private def bdWEndoSecDiff (g₁ g_bg g₀' : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg -
    deTurckLieWEndoSection (I := I) (M := M) g₁ g₀'

set_option linter.unusedSectionVars false in
private theorem bdDLbDiff_eq_slotInsert_sum
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀ =
      slotInsertEndoCc (I := I) (M := M) g₀ 1
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)))
            (Equiv.swap (0 : Fin 2) 1) := by
  rw [bdDLb_eq_slotInsert_sum (I := I) (M := M) g₀ g₁ g_bg,
    bdDLb_eq_slotInsert_sum (I := I) (M := M) g₀ g₁ g₀]
  rw [show (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1))
      - (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1)) =
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
        - slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀))
      + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1)
        - reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1)) from by abel]
  rw [bdSlotInsertEndoCc_sub (I := I) (M := M) g₀ 1
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)]
  rw [bdReindexSwap_sub (I := I) (M := M) g₀
    (slotInsertEndoCc (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))
    (slotInsertEndoCc (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀))]
  rw [bdSlotInsertEndoCc_sub (I := I) (M := M) g₀ 1
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)]
  rfl

set_option linter.unusedSectionVars false in
private lemma bdSlotInsertZero_bdWEndoSecDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0
        (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀) =
      deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g₀ := by
  rw [deTurckLieWEndoInsert, deTurckLieWEndoInsert]
  rw [bdSlotInsertEndoCc_sub (I := I) (M := M) g₀ 0
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g₀)]
  rfl

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdEndoArmDiff_pointwise_gridWindow (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) := by
  classical
  obtain ⟨CW, hCW_nn, hCW⟩ := bdWEndoInsertDiff_gridWindow (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 2 * (fr * CW i) + 2 * (fr * CW i),
    fun i => by have h := mul_nonneg hfr_nn (hCW_nn i); linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  have hW_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (i + 2) :=
    Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i + 2)
  have hbase : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀))).toSection x) ≤
      CW i * Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    rw [bdSlotInsertZero_bdWEndoSecDiff (I := I) (M := M) g₀ g₁ g_bg]
    exact hCW g₁ P htie hδ_le hδ0 hbound i x
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀))).toSection x) ≤
      fr * CW i * Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
      (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀) i x
    rw [pow_one] at h
    refine le_trans h ?_
    rw [← hfr_def, mul_assoc]
    exact mul_le_mul_of_nonneg_left hbase hfr_nn
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)))
          (Equiv.swap (0 : Fin 2) 1))).toSection x) ≤
      fr * CW i * Combinatorics.antidiagonalTupleGridWindow b (i + 2) := by
    have heq := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
      (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)) i x
    rw [heq]
    exact hA
  rw [bdDLbDiff_eq_slotInsert_sum (I := I) (M := M) g₀ g₁ g_bg]
  refine le_trans (bdRfns_iCG_add_le (I := I) (M := M) g₀ 2 2 i _ _ x) ?_
  nlinarith [hA, hB,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀))).toSection x),
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (bdWEndoSecDiff (I := I) (M := M) g₁ g_bg g₀)))
          (Equiv.swap (0 : Fin 2) 1))).toSection x)]

/-- Pointwise low-order product-grid control of the change in the `DLb`
coefficient when only the fixed DeTurck background is changed. -/
theorem dlbDiff_grid (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤
          C i * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2) :=
  bdEndoArmDiff_pointwise_gridWindow (I := I) (M := M) g₀ g_bg hδ₀

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private theorem bdL2_tameEnvelope_of_gridWindow (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kg : ℕ → ℝ, (∀ k, 0 ≤ Kg k) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ) (C : ℝ), 0 ≤ C → ∀ (V : SmoothCcTensor g₀ 2 2),
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i V).toSection x) ≤
          C * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (i + 2)) →
        ‖iteratedCovGrad (I := I) g₀ 2 2 i V‖ ^ 2 ≤
          (C * ∑ k ∈ Finset.range (i + 2), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Kg, hKg_nn, ?_⟩
  intro P hPball i C hC V hpt
  have hwin_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpt' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V).toSection x) ≤
        C * ∑ k ∈ Finset.range (i + 2),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
    intro x
    refine le_trans (hpt x) (le_of_eq ?_)
    congr 1
  have hF_int : MeasureTheory.Integrable
      (fun x => C * ∑ k ∈ Finset.range (i + 2),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum _
      (fun k hk => (hKg P hPball k).1)).const_mul C
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i V)
    (fun x => C * ∑ k ∈ Finset.range (i + 2),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
    hF_int hpt'
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
  calc C * ∑ k ∈ Finset.range (i + 2),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
      ≤ C * ((∑ k ∈ Finset.range (i + 2), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum_le hC
    _ = (C * ∑ k ∈ Finset.range (i + 2), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        ring

set_option linter.unusedSectionVars false in
private lemma bdDelta_nonneg (g₀ : SmoothRiemannianMetric I M) (x₀ : M)
    (P : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ) :
    0 ≤ δ := by
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

set_option linter.unusedSectionVars false in
private lemma bdNorm_zero_of_isEmpty [IsEmpty M] (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (V : SmoothCcTensor g₀ r s) : ‖V‖ = 0 := by
  rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
    MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]

private def bdSigmaE0 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![1, 3, 4, 5, 0, 2] : Fin 6 → Fin 6) i,
   fun i => (![4, 0, 5, 1, 2, 3] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

set_option linter.unusedSectionVars false in
private lemma bdTensor0S_zero_rank_decomp (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) • unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitTensor, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma bdSlotExtendIter_two_toModel (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g₀ 4 X x (fun k : Fin 4 => u (Fin.natAdd 2 k)) := by
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)) from rfl]
  have hkey1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 5)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)))
    (v0 := u 0) (vs := Matrix.vecTail u)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey1
  rw [show (Fin.cons (u 0) (Matrix.vecTail u) : Fin 6 → TangentSpace I x) = u from by
    funext k
    refine Fin.cases rfl (fun i => rfl) k] at hkey1
  rw [← hkey1]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D) (u 0)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))) from rfl]
  rw [show (Matrix.vecTail u : Fin 5 → TangentSpace I x) =
      Fin.cons (u 1) (fun k : Fin 4 => u (Fin.natAdd 2 k)) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · change u (Fin.succ (Fin.succ i)) = u (Fin.natAdd 2 i)
      congr 1
      exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)]
  have hkey2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 4)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))))
    (v0 := u 1) (vs := fun k : Fin 4 => u (Fin.natAdd 2 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey2
  rw [← hkey2]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) (u 1)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)) from rfl]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := u 1)
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := u 0) (vs := Fin.cons (u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := bdTensor0S_zero_rank_decomp (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rfl

private def bdPureDT (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g₀ (s + 2) s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 2) s I x from cometricDoubleTraceFib (I := I) g₁ s x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
private lemma coeffOpApply_slotSwapField_eq_apply_of_symm (g₀ : SmoothRiemannianMetric I M)
    (D : SmoothCcTensor g₀ 2 2) (T : SmoothCcTensor g₀ 0 2)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v) :
    operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 D
          (ccInputSlotSwapField (I := I) (M := M) g₀)) T =
      operatorFieldApply (I := I) (M := M) g₀ 2 2 D T := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
  have hswapfix : inputSlotSwapFib (I := I) (M := M) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
        (unitTensor (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    beta_reduce
    rw [slotSwapFib_apply, Tensor0SSpace.toModel_ofModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hbridge : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
          (unitTensor (I := I) (M := M) x)) = unitModel (I := I) (M := M) g₀ 2 T x := rfl
    rw [hbridge]
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x (v 1) (v 0),
      unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ T x (v 0) (v 1)]
    exact hTsymm x (v 1) (v 0)
  rw [show unitModel (I := I) (M := M) g₀ 2
      (operatorFieldApply (I := I) (M := M) g₀ 2 2
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 2 2 D
          (ccInputSlotSwapField (I := I) (M := M) g₀)) T) x =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from D.toSection x)
        (inputSlotSwapFib (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from T.toSection x)
            (unitTensor (I := I) (M := M) x)))) from rfl]
  rw [hswapfix]
  rfl


theorem exists_riemannPalatini_refold_identity_data
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∃ qA qB : Fin 4 → Equiv.Perm (Fin 4),
      IsFramePairPartner qA qB ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ C0ra : ℝ → SmoothCcTensor g₀ 2 2,
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0ra (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s))
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0ra s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2
                  ((2 : ℝ) • riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ
                    qA qB s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0ra s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0ra s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨ΛQ, hΛQ_nn, hcapQ⟩ :=
    exists_ricciArmOrder0AACommCoeffField_realizedFam_fiberNormSq_ballUniform (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨ΛB, hΛB_nn, hcapB⟩ :=
    exists_ricciArmOrder0BackgroundCurvatureCoeffField_realizedFam_riemannianFiberNormSq_ballUniform
      (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨ΛS, hΛS_nn, hcapS⟩ :=
    exists_ricciArmSharpGradKoszulResidualField_realizedFam_riemannianFiberNormSq_uniformBound
      (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨ΛF, hΛF_nn, hcapF⟩ :=
    exists_ricciArmRicciFoldRemainderField_realizedFam_riemannianFiberNormSq_uniformBound (I := I)
      (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨KRm, hKRm_nn, hKRm⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
  obtain ⟨KB0, hKB0_nn, hKB0⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
  obtain ⟨KQw, hKQw_nn, hwinQ⟩ :=
    exists_ricciArmOrder0AACommCoeffField_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨KBw, hKBw_nn, hwinB⟩ :=
    exists_ricciArmOrder0BgRCommCoeffField_realizedFam_backgroundDifference_l2JetWindow
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KSw, hKSw_nn, hwinS⟩ :=
    exists_ricciArmSharpGradKoszulResidualField_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  obtain ⟨KFw, hKFw_nn, hwinF⟩ :=
    exists_ricciArmRicciFoldRemainderField_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀
  have hΛSQ_nn : (0 : ℝ) ≤
      2 * KRm + 8 * (2 * ΛQ + 2 * (2 * (2 * (2 * ΛB + 2 * KB0) + 2 * ΛS) + 2 * ΛF)) := by
    linarith [hΛQ_nn, hΛB_nn, hΛS_nn, hΛF_nn, hKRm_nn, hKB0_nn]
  refine ⟨Real.sqrt
      (2 * KRm + 8 * (2 * ΛQ + 2 * (2 * (2 * (2 * ΛB + 2 * KB0) + 2 * ΛS) + 2 * ΛF))),
    Real.sqrt_nonneg _,
    fun i => 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2
      + 8 * (2 * KQw i + 2 * (2 * (2 * KBw i + 2 * KSw i) + 2 * KFw i)),
    fun i => by
      have h5 : (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
      linarith [hKQw_nn i, hKBw_nn i, hKSw_nn i, hKFw_nn i],
    ![Equiv.swap (0 : Fin 4) 2, Equiv.swap (1 : Fin 4) 3,
      Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, 1],
    fun k => Equiv.swap (0 : Fin 4) 1 *
      (![Equiv.swap (0 : Fin 4) 2, Equiv.swap (1 : Fin 4) 3,
        Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, 1] k),
    fun _ => rfl, ?_⟩
  intro T hTsymm δ hδ_le hδ hδZ hball
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    have hzero : iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h := iteratedCovGrad_sub (I := I) (g := g₀) (r := 0) (s := 2) (j := j) T T
      rw [sub_self, sub_self] at h
      exact h
    rw [hzero, norm_zero]
    exact hR
  refine ⟨fun s =>
    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀
      + (2 : ℝ) •
        (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
              - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))),
    ?_, ?_, ?_, ?_⟩
  · exact threeArmHjoint_add_local (I := I) (M := M) g₀ _ _
      (threeArmHjoint_const_local (I := I) (M := M) g₀
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
      (threeArmHjoint_const_smul_local (I := I) (M := M) g₀ (2 : ℝ) _
        (threeArmHjoint_add_local (I := I) (M := M) g₀ _ _
          (ricciArmOrder0AACommCoeffField_realizedFam_threeArmHjoint (I := I) (M := M)
            g₀ T hδ hδZ)
          (threeArmHjoint_sub_local (I := I) (M := M) g₀ _ _
            (threeArmHjoint_add_local (I := I) (M := M) g₀ _ _
              (threeArmHjoint_sub_local (I := I) (M := M) g₀ _ _
                (ricciArmOrder0BgRCommCoeffField_realizedFam_threeArmHjoint (I := I) (M := M)
                  g₀ T hδ hδZ)
                (threeArmHjoint_const_local (I := I) (M := M) g₀
                  (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)))
              (threeArmHjoint_const_smul_local (I := I) (M := M) g₀ (1 / 2 : ℝ) _
                (ricciArmSharpGradKoszulResidualField_realizedFam_threeArmHjoint
                  (I := I) (M := M) g₀ T hδ hδZ)))
            (ricciArmRicciFoldRemainderField_realizedFam_threeArmHjoint (I := I) (M := M)
              g₀ T hδ hδZ))))
  · intro s hs
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
      rw [convexPerturbation, smul_zero, zero_add]
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
          g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ (s • T) y v w := by
      intro y v w
      rw [← hcP]
      exact realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
    have hPsymm : ∀ (x : M) (v w : TangentSpace I x),
        smoothCcTensorBilinForm (I := I) g₀ (s • T) x v w =
          smoothCcTensorBilinForm (I := I) g₀ (s • T) x w v := by
      intro x v w
      rw [ccTensorBilin_smul_local, ccTensorBilin_smul_local, hTsymm x v w]
    have hsymmT : ccTensor02Symm (I := I) (M := M) g₀ T = T :=
      symmS_eq_self_of_symm (I := I) (M := M) g₀ T hTsymm
    beta_reduce
    simp only [iteratedCovGrad_zero]
    have hfam : (2 : ℝ) • riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ
        ![Equiv.swap (0 : Fin 4) 2, Equiv.swap (1 : Fin 4) 3,
          Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, 1]
        (fun k => Equiv.swap (0 : Fin 4) 1 *
          (![Equiv.swap (0 : Fin 4) 2, Equiv.swap (1 : Fin 4) 3,
            Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, 1] k)) s =
        (2 * s : ℝ) • curvatureActionKernelCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
          (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
          (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
      rw [riemannPalatiniRefoldC2Family_eq_symmS_kernel (I := I) (M := M) g₀ T hδ hδZ _ _
        (fun _ => rfl) s,
        hsymmT, smul_smul]
      rfl
    rw [hfam, appCc_add_left, appCc_smul_left, appCc_smul_left]
    suffices hfold : (1 / 2 : ℝ) •
        (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)) T
          - operatorFieldApply (I := I) (M := M) g₀ 2 2
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) T) =
        operatorFieldApply (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                    (realizedFam (I := I) g₀ T 0 hδ hδZ s)
                  - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
                  + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
                  - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                      (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))) T
          + operatorFieldApply (I := I) (M := M) g₀ 4 2
              (curvatureActionKernelCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
                (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
                (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
                (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
                (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1)
              (iteratedCovGrad (I := I) g₀ 0 2 2 (s • T)) by
      have h2 : operatorFieldApply (I := I) (M := M) g₀ 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)) T
          - operatorFieldApply (I := I) (M := M) g₀ 2 2
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) T =
          (2 : ℝ) • ((1 / 2 : ℝ) •
            (operatorFieldApply (I := I) (M := M) g₀ 2 2
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s)) T
              - operatorFieldApply (I := I) (M := M) g₀ 2 2
                  (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) T)) := by
        rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
      rw [hfold, iteratedCovGrad_smul_real, appCc_smul_right, smul_add, smul_smul] at h2
      rw [sub_eq_iff_eq_add] at h2
      rw [h2]
      abel
    have hprim :=
      ricciArmOrder0RiemannHalfBgDiff_appCc_eq_residualFieldSum_add_refoldKernelSecondGrad
        (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T) htie hPsymm T
    rw [appCc_add_left, appCc_sub_left, appCc_add_left,
      coeffOpApply_slotSwapField_eq_apply_of_symm (I := I) (M := M) g₀ _ T hTsymm] at hprim
    rw [appCc_add_left, appCc_sub_left, appCc_add_left]
    exact hprim
  · intro s hs x
    have hQ : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x) ≤ ΛQ :=
      hcapQ T hδ_le hδ hδZ hball s hs x
    have hB := hcapB T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    have hS := hcapS T hδ_le hδ hδZ hball s hs x
    have hF := hcapF T hδ_le hδ hδZ hball s hs x
    have hRm := hKRm x
    have hB0 := hKB0 x
    beta_reduce
    rw [Real.sq_sqrt hΛSQ_nn]
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
    have houter := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x)
      ((2 : ℝ) • ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
            + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
            - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))).toSection x))
    have hsm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((2 : ℝ) • ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
              - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))).toSection x)) =
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
              - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))).toSection x) := by
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 2 x]
      norm_num
    have hX : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
              - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))).toSection x) ≤
        2 * ΛQ + 2 * (2 * (2 * (2 * ΛB + 2 * KB0) + 2 * ΛS) + 2 * ΛF) := by
      rw [show ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          + ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀)
              + (1 / 2 : ℝ) • ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)
              - ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T))).toSection x) =
          (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x
          + ((((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x
              - (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x)
              + (1 / 2 : ℝ) • (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x)
            - (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x) from by
        simp only [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub,
          SmoothCcTensor.toSection_smul, ContMDiffSection.coe_add, ContMDiffSection.coe_sub,
          ContMDiffSection.coe_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]]
      have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x)
        (((((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x
            - (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x)
            + (1 / 2 : ℝ) • (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x)
          - (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x))
      have h2 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 2 x
        ((((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x
            - (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x)
            + (1 / 2 : ℝ) • (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x))
        ((ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x)
      have h3 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
        (((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x
          - (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x))
        ((1 / 2 : ℝ) • (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x)
      have h4 := riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)).toSection x)
        ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀).toSection x)
      have h5 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((1 / 2 : ℝ) • (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x) =
          (1 / 4 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x) := by
        rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 2 2 x]
        norm_num
      have h6 : (0 : ℝ) ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)).toSection x) :=
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x _
      linarith [hQ, hB, hS, hF, hB0, h1, h2, h3, h4, h5, h6, hΛS_nn]
    linarith [houter, hsm, hRm, hX]
  · intro i s hs
    have hQ := hwinQ T hδ_le hδ hδZ hball i s hs
    have hD := hwinB T hδ_le hδ hδZ hball i s hs
    have hS := hwinS T hδ_le hδ hδZ hball i s hs
    have hF := hwinF T hδ_le hδ hδZ hball i s hs
    beta_reduce
    rw [iteratedCovGrad_add, iteratedCovGrad_smul_real, iteratedCovGrad_add,
      iteratedCovGrad_sub, iteratedCovGrad_add, iteratedCovGrad_smul_real]
    set jc := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) with hjc_def
    set jq := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0AACommCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)) with hjq_def
    set jd := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        - ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₀) with hjd_def
    set js := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)) with hjs_def
    set jr := iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (s • T)) with hjr_def
    have t1 := norm_add_sq_le_local (I := I) (M := M) g₀ jc
      ((2 : ℝ) • (jq + ((jd + (1 / 2 : ℝ) • js) - jr)))
    have t2 : ‖(2 : ℝ) • (jq + ((jd + (1 / 2 : ℝ) • js) - jr))‖ ^ 2 =
        4 * ‖jq + ((jd + (1 / 2 : ℝ) • js) - jr)‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have t3 := norm_add_sq_le_local (I := I) (M := M) g₀ jq ((jd + (1 / 2 : ℝ) • js) - jr)
    have t4 : ‖(jd + (1 / 2 : ℝ) • js) - jr‖ ^ 2 ≤
        2 * ‖jd + (1 / 2 : ℝ) • js‖ ^ 2 + 2 * ‖jr‖ ^ 2 := by
      have h := norm_add_sq_le_local (I := I) (M := M) g₀ (jd + (1 / 2 : ℝ) • js) (-jr)
      rw [← sub_eq_add_neg, norm_neg] at h
      exact h
    have t5 := norm_add_sq_le_local (I := I) (M := M) g₀ jd ((1 / 2 : ℝ) • js)
    have t6 : ‖(1 / 2 : ℝ) • js‖ ^ 2 = (1 / 4) * ‖js‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    have hjs_nn : (0 : ℝ) ≤ ‖js‖ ^ 2 := sq_nonneg _
    have hW1 : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by
      have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 :=
        Finset.sum_nonneg (fun j _ => sq_nonneg _)
      linarith
    have hcW : ‖jc‖ ^ 2 ≤ ‖jc‖ ^ 2 * (1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) :=
      le_mul_of_one_le_right (sq_nonneg _) hW1
    linarith [t1, t2, t3, t4, t5, t6, hjs_nn, hQ, hD, hS, hF, hcW]


omit [BoundarylessManifold I M] in
theorem riemannPalatiniRefoldC2Family_riemannianFiberNormSq_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_half : δ ≤ 1 / 2)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (hq : IsFramePairPartner qA qB) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (((2 : ℝ) • riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB
          s).toSection x) ≤
      (max (8 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2 := by
  classical
  intro s hs x
  have h1mδ : (0 : ℝ) < 1 - δ := by linarith
  obtain ⟨nx, ex, hnx, horthx, hparsx, hexpx, hrfnsx⟩ :=
    tangent_frame_expansion (I := I) (M := M) g₀ x
  have hnx_pos : 0 < nx := by
    have h0 : Module.finrank ℝ E ≠ 0 := NeZero.ne _
    rw [hnx]
    exact Nat.pos_of_ne_zero h0
  have hδ0 : (0 : ℝ) ≤ δ := by
    have h := hδZ x (ex ⟨0, hnx_pos⟩) (ex ⟨0, hnx_pos⟩)
    have hunit : g₀.inner x (ex ⟨0, hnx_pos⟩) (ex ⟨0, hnx_pos⟩) = 1 := by
      rw [horthx ⟨0, hnx_pos⟩ ⟨0, hnx_pos⟩]
      simp
    rw [hunit, Real.sqrt_one, mul_one, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  obtain ⟨hs0, hs1⟩ := hs
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hmono_cap : ∀ σp : Equiv.Perm (Fin 4),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (ccTensorUnitValueSection (I := I) (M := M) g₀
              (ccTensor02Symm (I := I) (M := M) g₀ T))
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
              (ccTensor02Symm (I := I) (M := M) g₀ T)) σp).toSection x) ≤
        (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) ^ 2 := by
    intro σp
    rw [curvatureRefoldMonomialCoeffField_toSection]
    exact riemannianFiberNormSq_curvatureRefoldMonomialBiContrFib_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (convexPerturbation (I := I) g₀ T 0 s) htie hδ_lt hδP
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      hδ0 (toModel_unitValue_symmS_abs_le (I := I) (M := M) g₀ T hδ) σp x
  rw [riemannPalatiniRefoldC2Family_eq_symmS_kernel (I := I) (M := M) g₀ T hδ hδZ
    qA qB hq s]
  rw [smul_smul, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    riemannianFiberNormSq_smul (I := I) (M := M) g₀ 4 2 x]
  rw [curvatureActionKernelCoeffField, SmoothCcTensor.toSection_smul,
    SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_smul, Pi.smul_apply, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.coe_add, Pi.add_apply,
    riemannianFiberNormSq_smul (I := I) (M := M) g₀ 4 2 x]
  have hB := riemannianFiberNormSq_addsub4_le (I := I) (M := M) g₀ 4 2 x
    ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 0)).toSection x)
    ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 1)).toSection x)
    ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 2)).toSection x)
    ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 3)).toSection x)
  have hc0 := hmono_cap (qA 0)
  have hc1 := hmono_cap (qA 1)
  have hc2 := hmono_cap (qA 2)
  have hc3 := hmono_cap (qA 3)
  set fC : ℝ := deTurckArmFibreConst (Module.finrank ℝ E) with hfC_def
  have hfC_nn : (0 : ℝ) ≤ fC := deTurckArmFibreConst_nonneg _
  have hr1_nn : (0 : ℝ) ≤ δ / (1 - δ) := div_nonneg hδ0 (le_of_lt h1mδ)
  have hrate : δ / (1 - δ) ^ 2 ≤ 2 * (δ / (1 - δ)) := by
    rw [div_le_iff₀ (by positivity)]
    have hexp : 2 * (δ / (1 - δ)) * (1 - δ) ^ 2 = 2 * δ * (1 - δ) := by
      field_simp
    rw [hexp]
    nlinarith [mul_nonneg hδ0 (by linarith : (0 : ℝ) ≤ 1 - 2 * δ)]
  have hstep : 16 * (fC * (δ / (1 - δ) ^ 2)) ^ 2 ≤
      (8 * fC * (δ / (1 - δ))) ^ 2 := by
    have hfr2_nn : (0 : ℝ) ≤ fC * (δ / (1 - δ) ^ 2) :=
      mul_nonneg hfC_nn (div_nonneg hδ0 (sq_nonneg _))
    have hle : fC * (δ / (1 - δ) ^ 2) ≤ fC * (2 * (δ / (1 - δ))) :=
      mul_le_mul_of_nonneg_left hrate hfC_nn
    have hsq := pow_le_pow_left₀ hfr2_nn hle 2
    nlinarith [hsq]
  have hmax : max (8 * fC * (δ / (1 - δ))) 0 = 8 * fC * (δ / (1 - δ)) :=
    max_eq_left (mul_nonneg (mul_nonneg (by norm_num) hfC_nn) hr1_nn)
  rw [hmax]
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
  have hsum_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 2 x
    ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 0)).toSection x
    + (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 1)).toSection x
    - (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 2)).toSection x
    - (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 3)).toSection x)
  nlinarith [hB, hc0, hc1, hc2, hc3, hs2, hsum_nn, hstep, hs0, hs1,
    sq_nonneg (fC * (δ / (1 - δ) ^ 2)),
    mul_nonneg (mul_nonneg hδ0 hδ0) (sq_nonneg (fC * (δ / (1 - δ) ^ 2)))]


theorem exists_riemannPalatiniRefoldC2Family_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (hq : IsFramePairPartner qA qB) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ_half : δ ≤ 1 / 2)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            (((2 : ℝ) • riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB
              s).toSection x) ≤
          (max (8 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) 0) ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            ((2 : ℝ) • riemannPalatiniRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ qA qB
              s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨K0, hK0_nn, hK0⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (qA 0)
  obtain ⟨K1, hK1_nn, hK1⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (qA 1)
  obtain ⟨K2, hK2_nn, hK2⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (qA 2)
  obtain ⟨K3, hK3_nn, hK3⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (qA 3)
  refine ⟨fun i => 4 * (K0 i + K1 i + K2 i + K3 i), fun i => by
    have h0 := hK0_nn i; have h1 := hK1_nn i; have h2 := hK2_nn i; have h3 := hK3_nn i
    linarith, ?_⟩
  intro T δ hδ_le hδ_half hδ hδZ hball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  refine ⟨riemannPalatiniRefoldC2Family_riemannianFiberNormSq_le (I := I) (M := M) g₀ T hδ_lt
    hδ_half hδ hδZ
    qA qB hq, ?_⟩
  intro i s hs
  obtain ⟨hs0, hs1⟩ := hs
  rw [riemannPalatiniRefoldC2Family_eq_symmS_kernel (I := I) (M := M) g₀ T hδ hδZ
    qA qB hq s]
  rw [curvatureActionKernelCoeffField, iteratedCovGrad_smul_real,
    iteratedCovGrad_smul_real, iteratedCovGrad_smul_real,
    iteratedCovGrad_sub, iteratedCovGrad_sub, iteratedCovGrad_add]
  set G0 := iteratedCovGrad (I := I) g₀ 4 2 i
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 0)) with hG0_def
  set G1 := iteratedCovGrad (I := I) g₀ 4 2 i
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 1)) with hG1_def
  set G2 := iteratedCovGrad (I := I) g₀ 4 2 i
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 2)) with hG2_def
  set G3 := iteratedCovGrad (I := I) g₀ 4 2 i
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T)) (qA 3)) with hG3_def
  have hcol : (2 : ℝ) • s • (1 / 2 : ℝ) • (G0 + G1 - G2 - G3) =
      s • (G0 + G1 - G2 - G3) := by
    rw [smul_smul, smul_smul]
    have h2s : (2 : ℝ) * s * (1 / 2) = s := by ring
    rw [h2s]
  rw [hcol]
  have hG0w := hK0 T hδ_le hδ hδZ hball i s ⟨hs0, hs1⟩
  have hG1w := hK1 T hδ_le hδ hδZ hball i s ⟨hs0, hs1⟩
  have hG2w := hK2 T hδ_le hδ hδZ hball i s ⟨hs0, hs1⟩
  have hG3w := hK3 T hδ_le hδ hδZ hball i s ⟨hs0, hs1⟩
  rw [← hG0_def] at hG0w
  rw [← hG1_def] at hG1w
  rw [← hG2_def] at hG2w
  rw [← hG3_def] at hG3w
  have hnorm1 : ‖s • (G0 + G1 - G2 - G3)‖ ≤ ‖G0‖ + ‖G1‖ + ‖G2‖ + ‖G3‖ := by
    have hs_abs : |s| ≤ 1 := by
      rw [abs_of_nonneg hs0]
      exact hs1
    have hsm : ‖s • (G0 + G1 - G2 - G3)‖ ≤ ‖G0 + G1 - G2 - G3‖ := by
      rw [norm_smul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs]
      exact hs_abs
    refine le_trans hsm ?_
    calc ‖G0 + G1 - G2 - G3‖ ≤ ‖G0 + G1 - G2‖ + ‖G3‖ := norm_sub_le _ _
      _ ≤ ‖G0 + G1‖ + ‖G2‖ + ‖G3‖ := by
          have h := norm_sub_le (G0 + G1) G2
          linarith
      _ ≤ ‖G0‖ + ‖G1‖ + ‖G2‖ + ‖G3‖ := by
          have h := norm_add_le G0 G1
          linarith
  have hsq : ‖s • (G0 + G1 - G2 - G3)‖ ^ 2 ≤ (‖G0‖ + ‖G1‖ + ‖G2‖ + ‖G3‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm1 2
  have hcauchy : (‖G0‖ + ‖G1‖ + ‖G2‖ + ‖G3‖) ^ 2 ≤
      4 * (‖G0‖ ^ 2 + ‖G1‖ ^ 2 + ‖G2‖ ^ 2 + ‖G3‖ ^ 2) := by
    nlinarith [sq_nonneg (‖G0‖ - ‖G1‖), sq_nonneg (‖G0‖ - ‖G2‖), sq_nonneg (‖G0‖ - ‖G3‖),
      sq_nonneg (‖G1‖ - ‖G2‖), sq_nonneg (‖G1‖ - ‖G3‖), sq_nonneg (‖G2‖ - ‖G3‖)]
  refine le_trans hsq (le_trans hcauchy ?_)
  have hexp : 4 * (K0 i + K1 i + K2 i + K3 i) *
      (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) =
      4 * (K0 i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)
        + K1 i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)
        + K2 i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)
        + K3 i * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by ring
  rw [hexp]
  linarith [hG0w, hG1w, hG2w, hG3w]


theorem exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ)
    (hε : ∀ i, |ε i| ≤ 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
          (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε)
          (δ := δ) (δ' := δ) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε
              s).toSection x) ≤
          (max (3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) 0) ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨K0, hK0_nn, hK0⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (q 0)
  obtain ⟨K1, hK1_nn, hK1⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (q 1)
  obtain ⟨K2, hK2_nn, hK2⟩ :=
    exists_curvatureRefoldMonomialCoeffField_symmS_realizedFam_l2JetWindow (I := I) (M := M)
      g₀ a ha_super hR hδ₀ (q 2)
  refine ⟨fun i => 3 * (K0 i + K1 i + K2 i),
    fun i => by have h0 := hK0_nn i; have h1 := hK1_nn i; have h2 := hK2_nn i; linarith, ?_⟩
  intro T δ hδ_le hδ hδZ hball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have h1mδ : (0 : ℝ) < 1 - δ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hmono : ∀ σp : Equiv.Perm (Fin 4),
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
            ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
              (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
              (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σp).toSection p.1))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) :=
      fun σp => curvatureRefoldMonomialCoeffField_realizedFam_jointContMDiffOn
        (I := I) (M := M) g₀ T hδ hδZ
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σp
    have hpair : ∀ i : Fin 3,
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
          (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
            (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
            (ε i • ((1 / 2 : ℝ) •
              ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
                (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
                (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
                (q i)).toSection p.1
              + (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ p.2)
                (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
                (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
                ((q i).trans (Equiv.swap (0 : Fin 4) 1))).toSection p.1))))
          ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
      intro i
      have hadd := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
        (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ (hmono (q i))
        (hmono ((q i).trans (Equiv.swap (0 : Fin 4) 1)))
      have hhalf := jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := 4) (s := 2)
        (S := realizedSmallSet (δ := δ) (δ' := δ)) (1 / 2 : ℝ) _ hadd
      exact jointTotalSpaceRS_const_smul_local (I := I) (M := M) (r := 4) (s := 2)
        (S := realizedSmallSet (δ := δ) (δ' := δ)) (ε i) _ hhalf
    have hsum01 := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ (hpair 0) (hpair 1)
    have hsum := jointTotalSpaceRS_add_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) _ _ hsum01 (hpair 2)
    have hfam := jointTotalSpaceRS_smulFun_local (I := I) (M := M) (r := 4) (s := 2)
      (S := realizedSmallSet (δ := δ) (δ' := δ)) (f := fun t => t) contDiff_id _ hsum
    refine hfam.congr (fun p _ => ?_)
    refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
      (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
    rw [deTurckLieCovDerivRefoldC2Family]
    simp only [Fin.sum_univ_three, SmoothCcTensor.toSection_smul,
      SmoothCcTensor.toSection_add, ContMDiffSection.coe_smul, ContMDiffSection.coe_add,
      Pi.smul_apply, Pi.add_apply]
  · intro s hs x
    obtain ⟨nx, ex, hnx, horthx, hparsx, hexpx, hrfnsx⟩ :=
      tangent_frame_expansion (I := I) (M := M) g₀ x
    have hnx_pos : 0 < nx := by
      have h0 : Module.finrank ℝ E ≠ 0 := NeZero.ne _
      rw [hnx]
      exact Nat.pos_of_ne_zero h0
    have hδ0 : (0 : ℝ) ≤ δ := by
      have h := hδZ x (ex ⟨0, hnx_pos⟩) (ex ⟨0, hnx_pos⟩)
      have hunit : g₀.inner x (ex ⟨0, hnx_pos⟩) (ex ⟨0, hnx_pos⟩) = 1 := by
        rw [horthx ⟨0, hnx_pos⟩ ⟨0, hnx_pos⟩]
        simp
      rw [hunit, Real.sqrt_one, mul_one, mul_one] at h
      exact le_trans (abs_nonneg _) h
    have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
    have htie : ∀ (y : M) (v w : TangentSpace I y),
        (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
          g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T 0 s) y v w :=
      fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
    obtain ⟨hs0, hs1⟩ := hs
    have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
      intro y v w
      have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
        ring
      rwa [heq] at hraw
    have hmono_cap : ∀ σp : Equiv.Perm (Fin 4),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              (ccTensorUnitValueSection (I := I) (M := M) g₀
                (ccTensor02Symm (I := I) (M := M) g₀ T))
              (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
                (ccTensor02Symm (I := I) (M := M) g₀ T)) σp).toSection x) ≤
          (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) ^ 2 := by
      intro σp
      rw [curvatureRefoldMonomialCoeffField_toSection]
      exact riemannianFiberNormSq_curvatureRefoldMonomialBiContrFib_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (convexPerturbation (I := I) g₀ T 0 s) htie hδ_lt hδP
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        hδ0 (toModel_unitValue_symmS_abs_le (I := I) (M := M) g₀ T hδ) σp x
    have hterm_le : ∀ (c : ℝ), |c| ≤ 1 → ∀ σp : Equiv.Perm (Fin 4),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            (c • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s)
              (ccTensorUnitValueSection (I := I) (M := M) g₀
                (ccTensor02Symm (I := I) (M := M) g₀ T))
              (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
                (ccTensor02Symm (I := I) (M := M) g₀ T)) σp).toSection x)) ≤
          (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) ^ 2 := by
      intro c hc σp
      rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 4 2 x]
      have h1 := hmono_cap σp
      have hc2 : c ^ 2 ≤ 1 := by nlinarith [abs_nonneg c, sq_abs c, hc]
      have h0 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 2 x
        ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (ccTensorUnitValueSection (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ T))
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ T)) σp).toSection x)
      nlinarith [h1, hc2, h0, sq_nonneg c]
    rw [deTurckLieCovDerivRefoldC2Family_eq_symmS_weight (I := I) (M := M) g₀ T hδ hδZ q ε s]
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      riemannianFiberNormSq_smul (I := I) (M := M) g₀ 4 2 x]
    simp only [Fin.sum_univ_three, SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_add, ContMDiffSection.coe_smul,
      Pi.add_apply, Pi.smul_apply]
    have hr0 := hterm_le (ε 0) (hε 0) (q 0)
    have hr1 := hterm_le (ε 1) (hε 1) (q 1)
    have hr2 := hterm_le (ε 2) (hε 2) (q 2)
    have h3 := riemannianFiberNormSq_add3_le (I := I) (M := M) g₀ 4 2 x
      (ε 0 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 0)).toSection x))
      (ε 1 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 1)).toSection x))
      (ε 2 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 2)).toSection x))
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs0, hs1]
    have hmax : max (3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) 0 =
        3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2) :=
      max_eq_left (mul_nonneg (mul_nonneg (by norm_num)
        (deTurckArmFibreConst_nonneg _)) (div_nonneg hδ0 (sq_nonneg _)))
    rw [hmax]
    have hsum_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 2 x
      (ε 0 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 0)).toSection x)
      + ε 1 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 1)).toSection x)
      + ε 2 • ((curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 2)).toSection x))
    nlinarith [hr0, hr1, hr2, h3, hs2, hsum_nn,
      sq_nonneg (deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2))]
  · intro i s hs
    rw [deTurckLieCovDerivRefoldC2Family_eq_symmS_weight (I := I) (M := M) g₀ T hδ hδZ q ε s,
      iteratedCovGrad_smul_real]
    simp only [Fin.sum_univ_three]
    rw [iteratedCovGrad_add, iteratedCovGrad_add, iteratedCovGrad_smul_real,
      iteratedCovGrad_smul_real, iteratedCovGrad_smul_real]
    have hG0 := hK0 T hδ_le hδ hδZ hball i s hs
    have hG1 := hK1 T hδ_le hδ hδZ hball i s hs
    have hG2 := hK2 T hδ_le hδ hδZ hball i s hs
    obtain ⟨hs0, hs1⟩ := hs
    set G0 := iteratedCovGrad (I := I) g₀ 4 2 i
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 0)) with hG0_def
    set G1 := iteratedCovGrad (I := I) g₀ 4 2 i
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 1)) with hG1_def
    set G2 := iteratedCovGrad (I := I) g₀ 4 2 i
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) (q 2)) with hG2_def
    have hnorm1 : ‖s • (ε 0 • G0 + ε 1 • G1 + ε 2 • G2)‖ ≤ ‖G0‖ + ‖G1‖ + ‖G2‖ := by
      have hsm : ∀ (c : ℝ), |c| ≤ 1 → ∀ (G : SmoothCcTensor g₀ 4 (2 + i)),
          ‖c • G‖ ≤ ‖G‖ := by
        intro c hc G
        rw [norm_smul]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [Real.norm_eq_abs]
        exact hc
      have hs_abs : |s| ≤ 1 := by
        rw [abs_of_nonneg hs0]
        exact hs1
      refine le_trans (hsm s hs_abs _) ?_
      refine le_trans (norm_add_le _ _) ?_
      have h01 : ‖ε 0 • G0 + ε 1 • G1‖ ≤ ‖G0‖ + ‖G1‖ := by
        refine le_trans (norm_add_le _ _) ?_
        exact add_le_add (hsm (ε 0) (hε 0) G0) (hsm (ε 1) (hε 1) G1)
      have h2 : ‖ε 2 • G2‖ ≤ ‖G2‖ := hsm (ε 2) (hε 2) G2
      linarith
    have hsq : ‖s • (ε 0 • G0 + ε 1 • G1 + ε 2 • G2)‖ ^ 2 ≤
        (‖G0‖ + ‖G1‖ + ‖G2‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm1 2
    have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 := by positivity
    refine le_trans hsq ?_
    exact real_sq_add_three_le (norm_nonneg G0) (norm_nonneg G1) (norm_nonneg G2)
      hG0 hG1 hG2 (hK0_nn i) (hK1_nn i) (hK2_nn i) hwin_nn


theorem exists_deTurckLieCovDerivArm_curvatureRefold_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∃ (C0da : ℝ → SmoothCcTensor g₀ 2 2) (C2da : ℝ → SmoothCcTensor g₀ 4 2),
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2 C0da (δ := δ) (δ' := δ) ∧
          linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 C2da (δ := δ) (δ' := δ) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1,
            operatorFieldApply (I := I) (M := M) g₀ 2 2
                (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg)
                (iteratedCovGrad (I := I) g₀ 0 2 0 T) =
              operatorFieldApply (I := I) (M := M) g₀ 2 2 (C0da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 0 T) +
                operatorFieldApply (I := I) (M := M) g₀ 4 2 (C2da s)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 T)) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x ((C0da s).toSection x) ≤
              Λ ^ 2) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x ((C2da s).toSection x) ≤
              (max (3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ) ^ 2)) 0)
                ^ 2) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i (C0da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
            ‖iteratedCovGrad (I := I) g₀ 4 2 i (C2da s)‖ ^ 2 ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λ, hΛ, KA, hKA, q, ε, hε, hmain⟩ :=
    exists_deTurckLieCovDerivArm_refold_identity_data (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨KB, hKB, hfam⟩ :=
    exists_deTurckLieCovDerivRefoldC2Family_cap_l2JetWindow (I := I) (M := M) g₀ a
      ha_super hR hδ₀ q ε hε
  refine ⟨Λ, hΛ, fun i => max (KA i) (KB i),
    fun i => le_trans (hKA i) (le_max_left _ _), ?_⟩
  intro T hTsymm δ hδ_le hδ hδZ hball
  obtain ⟨C0da, hjoint0, hid, hsup0, henv0⟩ := hmain T hTsymm hδ_le hδ hδZ hball
  obtain ⟨hjoint2, hcap2, henv2⟩ := hfam T hδ_le hδ hδZ hball
  refine ⟨C0da, deTurckLieCovDerivRefoldC2Family (I := I) (M := M) g₀ T hδ hδZ q ε,
    hjoint0, hjoint2, hid, hsup0, hcap2, ?_, ?_⟩
  · intro i s hs
    refine le_trans (henv0 i s hs) (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    positivity
  · intro i s hs
    refine le_trans (henv2 i s hs) (mul_le_mul_of_nonneg_right (le_max_right _ _) ?_)
    positivity


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVF_background_sub_eq_connDiff_trace
    (g₁ gA gB : SmoothRiemannianMetric I M) (x : M) :
    (PDE.DeTurck.deTurckVF (I := I) g₁ gA :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x -
      (PDE.DeTurck.deTurckVF (I := I) g₁ gB :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g₁ x x j k •
          PDE.DeTurck.connDiff (I := I) gB gA x
            (chartBasisVecFiber (I := I) x j x)
            (chartBasisVecFiber (I := I) x k x) := by
  classical
  rw [PDE.DeTurck.deTurckVF_apply_eq (I := I) g₁ gA x,
    PDE.DeTurck.deTurckVF_apply_eq (I := I) g₁ gB x,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← smul_sub]
  congr 1
  rw [PDE.DeTurck.connDiff_cocycle (I := I) gB g₁ gA x
      (chartBasisVecFiber (I := I) x j x) (chartBasisVecFiber (I := I) x k x),
    add_sub_cancel_left]


theorem exists_deTurckLieEndoArm_backgroundDifference_perOrder_l2_tameEnvelope_generic
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg -
                deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hpt⟩ := bdEndoArmDiff_pointwise_gridWindow (I := I) (M := M) g₀ g_bg hδ₁_lt
  obtain ⟨Kg, hKg_nn, hKg⟩ := bdL2_tameEnvelope_of_gridWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 2), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ => hKg_nn k), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by positivity
  have hsubj : deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg -
      deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀ =
      deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀ := by
    rw [endoArmField_eq_dLbCoeffField, endoArmField_eq_dLbCoeffField]
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := bdDelta_nonneg (I := I) (M := M) g₀ x₀ P hδ
    have hδ_le' : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    rw [hsubj]
    exact hKg P hPball i (C i) (hC_nn i)
      (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg -
        deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g₀)
      (fun x => hpt g₁ P htie hδ_le' hδ0 hδ i x)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g_bg -
          deTurckLieEndoArmField (I := I) (M := M) g₀ g₁ g₀)‖ = 0 :=
      bdNorm_zero_of_isEmpty (I := I) (M := M) g₀ 2 (2 + i) _
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 2), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ => hKg_nn k)
    nlinarith [hwin_nn, hK_nn]


theorem exists_deTurckLieEndoArm_backgroundDifference_l2JetWindow
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨K, hK_nn, hK⟩ :=
    exists_deTurckLieEndoArm_backgroundDifference_perOrder_l2_tameEnvelope_generic
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨K, hK_nn, ?_⟩
  intro T δ hδ_le hδ hδZ hball i s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w
  obtain ⟨hs0, hs1⟩ := hs
  have habs : |s| ≤ 1 := by
    rw [abs_of_nonneg hs0]
    exact hs1
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
    rw [convexPerturbation, smul_zero, zero_add]
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T 0 s)‖ ≤ R := by
    intro j hj
    rw [hcP, iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
        1 * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
          mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := one_mul _
      _ ≤ R := hball j hj
  refine le_trans (hK (realizedFam (I := I) g₀ T 0 hδ hδZ s)
    (convexPerturbation (I := I) g₀ T 0 s) hδ_le hδP htie hPball i) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hK_nn i)
  refine add_le_add le_rfl ?_
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [hcP, iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, mul_pow]
  have h1 : |s| ^ 2 ≤ 1 := by nlinarith [abs_nonneg s]
  nlinarith [sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖, h1,
    norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j T)]


theorem exists_deTurckLieEndoArm_backgroundDifference_order0_data
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 2
          (fun s => deTurckLieEndoArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
            - deTurckLieEndoArmField (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀) (δ := δ) (δ' := δ) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x) ≤ Λ ^ 2) ∧
        (∀ i : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg
              - deTurckLieEndoArmField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2)) := by
  classical
  obtain ⟨Λbg, hΛbg_nn, hsup_bg⟩ :=
    deTurckLieDLbCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M)
      g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Λz, hΛz_nn, hsup_z⟩ :=
    deTurckLieDLbCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M)
      g₀ g₀ a ha_super hR hδ₀
  obtain ⟨Ke, hKe_nn, henv⟩ :=
    exists_deTurckLieEndoArm_backgroundDifference_l2JetWindow (I := I) (M := M)
      g₀ g_bg a ha_super hR hδ₀
  have hS_nn : (0 : ℝ) ≤ 2 * Λbg + 2 * Λz := by linarith
  refine ⟨Real.sqrt (2 * Λbg + 2 * Λz), Real.sqrt_nonneg _, Ke, hKe_nn, ?_⟩
  intro T δ hδ_le hδ hδZ hball
  have hZball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    have hzero : iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2) = 0 := by
      have h := iteratedCovGrad_sub (I := I) (g := g₀) (r := 0) (s := 2) (j := j) T T
      rw [sub_self, sub_self] at h
      exact h
    rw [hzero, norm_zero]
    exact hR
  refine ⟨?_, ?_, fun i s hs => henv T hδ_le hδ hδZ hball i s hs⟩
  · exact threeArmHjoint_sub_local (I := I) (M := M) g₀ _ _
      (endoArmField_realizedFam_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ g_bg)
      (endoArmField_realizedFam_threeArmHjoint (I := I) (M := M) g₀ T hδ hδZ g₀)
  · intro s hs x
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieEndoArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g_bg).toSection x) ≤ Λbg := by
      rw [endoArmField_eq_dLbCoeffField]
      exact hsup_bg T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((deTurckLieEndoArmField (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀).toSection x) ≤ Λz := by
      rw [endoArmField_eq_dLbCoeffField]
      exact hsup_z T 0 hδ_le hδ hδ_le hδZ hball hZball s hs x
    rw [Real.sq_sqrt hS_nn, SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub,
      Pi.sub_apply]
    refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 2 2 x _ _) ?_
    linarith [h1, h2]


theorem covDerivConnDiff_realizedFam_zero_endpoint_eq_smul_covDerivSharp
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    covDerivConnDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (fun b => X b) (fun b => Y b) (fun b => Z b) x =
      s •
        ((LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).toFun
            (fun b : M =>
              DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
                (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
                (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
                  (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) x (X x)
          - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) x
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) x (Z x)
              (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
                (fun b => X b) (fun b => Y b) x))
          - DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) x
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) x
              (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
                (fun b => X b) (fun b => Z b) x) (Y x))) := by
  classical
  have h0_mem : (0 : ℝ) ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨le_refl (0 : ℝ), zero_le_one⟩
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt hs
  have hexpand : covDerivConnDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
      (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (fun b => X b) (fun b => Y b) (fun b => Z b) x =
      (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).toFun
          (diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
            (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (fun b => Y b) (fun b => Z b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) x (Z x)
            (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
              (fun b => X b) (fun b => Y b) x)
        - PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) x
            (covApply (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
              (fun b => X b) (fun b => Z b) x) (Y x) := rfl
  rw [hexpand]
  have hpoint : ∀ (b : M) (u ζ : TangentSpace I b),
      PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b u ζ =
      s • DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
        (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
          (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b u ζ) := by
    intro b u ζ
    have h := connDiff_realizedFam_eq_smul_sharp (I := I) g₀ T 0 hδ_lt hδ hδ_lt hδZ
      h0_mem hs_mem b u ζ
    rwa [sub_zero] at h
  by_cases hs0 : s = 0
  · subst hs0
    have hconn0 : ∀ (b : M) (u ζ : TangentSpace I b),
        PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
          (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b u ζ = 0 := by
      intro b u ζ
      rw [PDE.DeTurck.connDiff_self]
      rfl
    have hdz : diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
        (fun b => Y b) (fun b => Z b) =
        (0 : ℝ) • fun b : M => X b := by
      funext b
      rw [Pi.smul_apply, zero_smul]
      exact hconn0 b (Z b) (Y b)
    rw [hdz]
    have hσX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b (X b)) x :=
      (X.contMDiff x).mdifferentiableAt (by simp)
    have hsmul := (LeviCivita (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).isCovariantDerivativeOnUniv.smul_const
      (σ := fun b => X b) (x := x) (0 : ℝ) hσX (Set.mem_univ x)
    rw [hsmul, ContinuousLinearMap.smul_apply]
    rw [hconn0 x (Z x) (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Y b) x),
      hconn0 x (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Z b) x) (Y x)]
    rw [zero_smul, zero_smul]
    simp
  · have hconn_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) :=
      PDE.DeTurck.connDiff_contMDiff (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
        Z.contMDiff Y.contMDiff
    have hΨ_eq : (fun b : M =>
        DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
            (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) =
        (fun b : M => s⁻¹ •
          PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)) := by
      funext b
      rw [hpoint b (Z b) (Y b), smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have hΨ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)))) := by
      have hsmul' := ContMDiff.smul_section
        (f := fun _ : M => s⁻¹)
        (s := fun b : M =>
          PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
            (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))
        contMDiff_const hconn_smooth
      refine hsmul'.congr (fun b => ?_)
      refine congrArg (TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b) ?_
      change DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
            (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)) =
        s⁻¹ • PDE.DeTurck.connDiff (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s)
          (realizedFam (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)
      exact congrFun hΨ_eq b
    have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
          (DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)))) x :=
      (hΨ_smooth x).mdifferentiableAt (by simp)
    have hdiffSec : diffSec (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0))
        (LeviCivita (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ s))
        (fun b => Y b) (fun b => Z b) =
        s • (fun b : M =>
          DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
            (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
              (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b))) := by
      funext b
      rw [Pi.smul_apply]
      exact hpoint b (Z b) (Y b)
    rw [hdiffSec]
    have hsmul := (LeviCivita (I := I)
      (realizedFam (I := I) g₀ T 0 hδ hδZ 0)).isCovariantDerivativeOnUniv.smul_const
      (σ := fun b : M =>
        DifferentialGeometry.Integral.DivergenceTheorem.metricSharp (I := I)
          (realizedFam (I := I) g₀ T 0 hδ hδZ s) b
          (linearizedKoszulCovec (I := I) (realizedFam (I := I) g₀ T 0 hδ hδZ 0)
            (realizedVelocityCc (I := I) g₀ T 0 hδ hδZ 0) b (Z b) (Y b)))
      (x := x) s hσ (Set.mem_univ x)
    rw [hsmul, ContinuousLinearMap.smul_apply]
    rw [hpoint x (Z x) (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Y b) x),
      hpoint x (covApply (LeviCivita (I := I)
        (realizedFam (I := I) g₀ T 0 hδ hδZ 0)) (fun b => X b) (fun b => Z b) x) (Y x)]
    module

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
