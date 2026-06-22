import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Geometry.Curvature.CurvatureFiberNormJetBound

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def metricDiffCovJet2Bound
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (K : ℝ) (x : M) : Prop :=
  ∀ j : ℕ, j ≤ 2 →
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j S).toSection x) ≤ K ^ 2

theorem metricDiffCovJet2Bound_mono
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2)
    {K K' : ℝ} (hKK' : K ≤ K') (hK_nn : 0 ≤ K) (x : M)
    (h : metricDiffCovJet2Bound (I := I) g₀ S K x) :
    metricDiffCovJet2Bound (I := I) g₀ S K' x := by
  intro j hj
  refine (h j hj).trans ?_
  have hK'_nn : 0 ≤ K' := le_trans hK_nn hKK'
  exact pow_le_pow_left₀ hK_nn hKK' 2

theorem exists_uniform_riemannBiContrFib_g0_fiberNormSq_bound
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Cg₀ : ℝ, 0 ≤ Cg₀ ∧ ∀ b : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 b
          (show TensorRSSpace 2 2 I b from
            TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₀ b)) ≤ Cg₀ ^ 2 := by
  obtain ⟨Kc, hKc_nn, hKc⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2
      (ricciArmOrder0RiemannCoeffField (I := I) (M := M) g₀ g₀)
  refine ⟨Real.sqrt Kc, Real.sqrt_nonneg _, fun b => ?_⟩
  have hb := hKc b
  rw [ricciArmOrder0RiemannCoeffField_toSection] at hb
  rw [Real.sq_sqrt hKc_nn]
  exact hb

theorem riemannBiContrFib_fiberNormSq_le_of_metricJet_pointwise
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Cg₀ K : ℝ) (hCg₀ : 0 ≤ Cg₀) (hK : 0 ≤ K)
    (hCg₀_bound : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₀ x)) ≤ Cg₀ ^ 2)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ)
    (hjet : metricDiffCovJet2Bound (I := I) g₀ S K x) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) ≤
      (Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 2) ^ 2 :=
  sorry

theorem exists_riemannBiContrFib_fiberNormSq_le_of_metricJet
    (g₀ : SmoothRiemannianMetric I M)
    {K : ℝ} (hK : 0 ≤ K) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2),
        (∀ (b : M) (u w : TangentSpace I b),
          ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w) →
        ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
        gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ →
        ∀ x : M, metricDiffCovJet2Bound (I := I) g₀ S K x →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            (show TensorRSSpace 2 2 I x from
              TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) ≤ Λ ^ 2 := by
  classical
  obtain ⟨Cg₀, hCg₀_nn, hCg₀_sup⟩ :=
    exists_uniform_riemannBiContrFib_g0_fiberNormSq_bound (I := I) (M := M) g₀
  refine ⟨Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 2,
    ?_, ?_⟩
  · have hbase : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 2 := by
      have h1 : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by positivity
      have h2 : 0 ≤ K + K ^ 2 := by positivity
      have h3 : 0 ≤ (1 - δ₀) ^ 2 := sq_nonneg _
      positivity
    linarith
  · intro g₁ S hbil δ hδ_le hδ_nn hδ x hjet
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hcoeff : 0 < 1 - δ := by linarith
    have hcoeff₀ : 0 < 1 - δ₀ := by linarith
    have hptwise := riemannBiContrFib_fiberNormSq_le_of_metricJet_pointwise
      (I := I) (M := M) (x := x) g₀ g₁ S hbil Cg₀ K hCg₀_nn hK
      (hCg₀_sup x) hδ_lt hδ_nn hδ hjet
    refine hptwise.trans ?_
    have hmono : (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 2
        ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 2 := by
      have hnum_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) := by positivity
      have hden_le : (1 - δ₀) ^ 2 ≤ (1 - δ) ^ 2 := by
        have : 1 - δ₀ ≤ 1 - δ := by linarith
        nlinarith [hcoeff₀.le, this]
      apply div_le_div_of_nonneg_left hnum_nn (by positivity) hden_le
    have hbase_nn : 0 ≤ Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 2 := by
      have : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 2 := by positivity
      linarith
    apply pow_le_pow_left₀ hbase_nn (by linarith [hmono]) 2

theorem exists_uniform_ricciArmOrder0CurvCoeff_g0_fiberNormSq_bound
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Cg₀ : ℝ, 0 ≤ Cg₀ ∧ ∀ b : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 b
          ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀).toSection b) ≤ Cg₀ ^ 2 := by
  obtain ⟨Kc, hKc_nn, hKc⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 2
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
  refine ⟨Real.sqrt Kc, Real.sqrt_nonneg _, fun b => ?_⟩
  rw [Real.sq_sqrt hKc_nn]
  exact hKc b

theorem ricciArmOrder0CurvCoeff_fiberNormSq_le_of_metricJet_pointwise
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Cg₀ K : ℝ) (hCg₀ : 0 ≤ Cg₀) (hK : 0 ≤ K)
    (hCg₀_bound : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀).toSection x) ≤ Cg₀ ^ 2)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ)
    (hjet : metricDiffCovJet2Bound (I := I) g₀ S K x) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤
      (Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 3) ^ 2 :=
  sorry

theorem exists_ricciArmOrder0CurvCoeff_fiberNormSq_le_of_metricJet
    (g₀ : SmoothRiemannianMetric I M)
    {K : ℝ} (hK : 0 ≤ K) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2),
        (∀ (b : M) (u w : TangentSpace I b),
          ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w) →
        ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
        gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ →
        ∀ x : M, metricDiffCovJet2Bound (I := I) g₀ S K x →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x) ≤ Λ ^ 2 := by
  classical
  obtain ⟨Cg₀, hCg₀_nn, hCg₀_sup⟩ :=
    exists_uniform_ricciArmOrder0CurvCoeff_g0_fiberNormSq_bound (I := I) (M := M) g₀
  have hcoeff₀' : 0 < 1 - δ₀ := by linarith
  refine ⟨Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 3, ?_, ?_⟩
  · have hbase : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 3 := by positivity
    linarith
  · intro g₁ S hbil δ hδ_le hδ_nn hδ x hjet
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hcoeff : 0 < 1 - δ := by linarith
    have hcoeff₀ : 0 < 1 - δ₀ := by linarith
    have hptwise := ricciArmOrder0CurvCoeff_fiberNormSq_le_of_metricJet_pointwise
      (I := I) (M := M) (x := x) g₀ g₁ S hbil Cg₀ K hCg₀_nn hK
      (hCg₀_sup x) hδ_lt hδ_nn hδ hjet
    refine hptwise.trans ?_
    have hmono : (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 3
        ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 3 := by
      have hnum_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) := by positivity
      have hden_le : (1 - δ₀) ^ 3 ≤ (1 - δ) ^ 3 := by
        have h1 : (1 - δ₀) ≤ (1 - δ) := by linarith
        exact pow_le_pow_left₀ hcoeff₀.le h1 3
      apply div_le_div_of_nonneg_left hnum_nn (pow_pos hcoeff₀ 3) hden_le
    have hbase_nn : 0 ≤ Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 3 := by
      have : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 3 := by positivity
      linarith
    apply pow_le_pow_left₀ hbase_nn (by linarith [hmono]) 2

theorem exists_uniform_ricciArmPrincipalCoeffPure_g0_fiberNormSq_bound
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ Cg₀ : ℝ, 0 ≤ Cg₀ ∧ ∀ b : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 b
          ((ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀).toSection b) ≤ Cg₀ ^ 2 := by
  obtain ⟨Kc, hKc_nn, hKc⟩ :=
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 4 2
      (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀)
  refine ⟨Real.sqrt Kc, Real.sqrt_nonneg _, fun b => ?_⟩
  rw [Real.sq_sqrt hKc_nn]
  exact hKc b

theorem ricciArmPrincipalCoeffPure_fiberNormSq_le_of_cometric_pointwise
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (Cg₀ : ℝ) (hCg₀ : 0 ≤ Cg₀)
    (hCg₀_bound : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₀).toSection x) ≤ Cg₀ ^ 2)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁).toSection x) ≤
      (Cg₀ + (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ) ^ 2) ^ 2 :=
  sorry

theorem exists_ricciArmPrincipalCoeffPure_fiberNormSq_le_of_cometric
    (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2),
        (∀ (b : M) (u w : TangentSpace I b),
          ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w) →
        ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
        gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ →
        ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
            ((ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁).toSection x) ≤ Λ ^ 2 := by
  classical
  obtain ⟨Cg₀, hCg₀_nn, hCg₀_sup⟩ :=
    exists_uniform_ricciArmPrincipalCoeffPure_g0_fiberNormSq_bound (I := I) (M := M) g₀
  refine ⟨Cg₀ + (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ₀) ^ 2, ?_, ?_⟩
  · have hbase : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ₀) ^ 2 := by positivity
    linarith
  · intro g₁ S hbil δ hδ_le hδ_nn hδ x
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hcoeff : 0 < 1 - δ := by linarith
    have hcoeff₀ : 0 < 1 - δ₀ := by linarith
    have hptwise := ricciArmPrincipalCoeffPure_fiberNormSq_le_of_cometric_pointwise
      (I := I) (M := M) (x := x) g₀ g₁ S hbil Cg₀ hCg₀_nn (hCg₀_sup x) hδ_lt hδ_nn hδ
    refine hptwise.trans ?_
    have hmono : (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ) ^ 2
        ≤ (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ₀) ^ 2 := by
      have hnum_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by positivity
      have hden_le : (1 - δ₀) ^ 2 ≤ (1 - δ) ^ 2 := by nlinarith [hcoeff₀.le]
      apply div_le_div_of_nonneg_left hnum_nn (by positivity) hden_le
    have hbase_nn : 0 ≤ Cg₀ + (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ) ^ 2 := by
      have : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ) ^ 2 := by positivity
      linarith
    apply pow_le_pow_left₀ hbase_nn (by linarith [hmono]) 2

end DifferentialGeometry.Geometry.Curvature.CurvatureFiberNormJetBound

end
