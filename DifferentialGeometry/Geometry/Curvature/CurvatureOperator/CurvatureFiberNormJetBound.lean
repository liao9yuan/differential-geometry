import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer
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
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

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

private lemma sqrt_riemannianFiberNormSq_le_sub_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (A B : TensorRSSpace r s I x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x A) ≤
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (A - B)) +
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x B) := by
  have hbridge : ∀ T : TensorRSSpace r s I x,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x T) =
        tensorPointwiseNorm (I := I) (M := M) g r s x (TensorRSSpace.toModel T) := by
    intro T
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x T]
    rfl
  rw [hbridge A, hbridge (A - B), hbridge B]
  have hsum : TensorRSSpace.toModel A =
      TensorRSSpace.toModel (A - B) + TensorRSSpace.toModel B := by
    rw [TensorRSSpace.toModel_sub]; abel
  rw [hsum]
  exact tensorPointwiseNorm_add_le (I := I) (M := M) g r s x _ _

theorem riemannBiContrFib_diff_fiberNormSq_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (K : ℝ) (hK : 0 ≤ K)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ)
    (hjet : metricDiffCovJet2Bound (I := I) g₀ S K x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) -
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₀ x)))) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 :=
  sorry

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
      (Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4) ^ 2 := by
  have hcoeff : 0 < 1 - δ := by linarith
  set A : TensorRSSpace 2 2 I x :=
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) with hA
  set B : TensorRSSpace 2 2 I x :=
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₀ x)) with hB
  have hrfns_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x A
  have hpoly_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by positivity
  have hbase_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x B) ≤ Cg₀ := by
    have hb_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x B :=
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x B
    rw [show Cg₀ = Real.sqrt (Cg₀ ^ 2) from (Real.sqrt_sq hCg₀).symm]
    exact Real.sqrt_le_sqrt hCg₀_bound
  have hdiff := riemannBiContrFib_diff_fiberNormSq_le
    (I := I) (M := M) (x := x) g₀ g₁ S hbil K hK hδ_lt hδ_nn hδ hjet
  have htri := sqrt_riemannianFiberNormSq_le_sub_add
    (I := I) (M := M) g₀ 2 2 x A B
  have hsqrt_bound : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A) ≤
      Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by
    calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A)
        ≤ Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (A - B)) +
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x B) := htri
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 + Cg₀ :=
            add_le_add hdiff hbase_sqrt
      _ = Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by ring
  have heq : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A) ^ 2 :=
    (Real.sq_sqrt hrfns_nn).symm
  rw [heq]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_bound 2

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
  refine ⟨Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4,
    ?_, ?_⟩
  · have hbase : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4 := by
      have h1 : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by positivity
      have h2 : 0 ≤ K + K ^ 2 := by positivity
      have h3 : 0 ≤ (1 - δ₀) ^ 4 := by positivity
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
    have hmono : (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4
        ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4 := by
      have hnum_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) := by positivity
      have hden_le : (1 - δ₀) ^ 4 ≤ (1 - δ) ^ 4 := by
        have h1 : (1 - δ₀) ≤ (1 - δ) := by linarith
        exact pow_le_pow_left₀ hcoeff₀.le h1 4
      apply div_le_div_of_nonneg_left hnum_nn (pow_pos hcoeff₀ 4) hden_le
    have hbase_nn : 0 ≤ Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by
      have : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by positivity
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

theorem ricciArmOrder0CurvCoeff_diff_fiberNormSq_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    (K : ℝ) (hK : 0 ≤ K)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ)
    (hjet : metricDiffCovJet2Bound (I := I) g₀ S K x) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x -
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀).toSection x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 :=
  sorry

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
      (Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4) ^ 2 := by
  have hcoeff : 0 < 1 - δ := by linarith
  set A : TensorRSSpace 2 2 I x :=
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁).toSection x with hA
  set B : TensorRSSpace 2 2 I x :=
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀).toSection x with hB
  have hrfns_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 2 x A
  have hpoly_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by positivity
  have hbase_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x B) ≤ Cg₀ := by
    rw [show Cg₀ = Real.sqrt (Cg₀ ^ 2) from (Real.sqrt_sq hCg₀).symm]
    exact Real.sqrt_le_sqrt hCg₀_bound
  have hdiff := ricciArmOrder0CurvCoeff_diff_fiberNormSq_le
    (I := I) (M := M) (x := x) g₀ g₁ S hbil K hK hδ_lt hδ_nn hδ hjet
  have htri := sqrt_riemannianFiberNormSq_le_sub_add
    (I := I) (M := M) g₀ 2 2 x A B
  have hsqrt_bound : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A) ≤
      Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by
    calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A)
        ≤ Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (A - B)) +
            Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x B) := htri
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 + Cg₀ :=
            add_le_add hdiff hbase_sqrt
      _ = Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by ring
  have heq : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x A) ^ 2 :=
    (Real.sq_sqrt hrfns_nn).symm
  rw [heq]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_bound 2

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
  refine ⟨Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4, ?_, ?_⟩
  · have hbase : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4 := by positivity
    linarith
  · intro g₁ S hbil δ hδ_le hδ_nn hδ x hjet
    have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
    have hcoeff : 0 < 1 - δ := by linarith
    have hcoeff₀ : 0 < 1 - δ₀ := by linarith
    have hptwise := ricciArmOrder0CurvCoeff_fiberNormSq_le_of_metricJet_pointwise
      (I := I) (M := M) (x := x) g₀ g₁ S hbil Cg₀ K hCg₀_nn hK
      (hCg₀_sup x) hδ_lt hδ_nn hδ hjet
    refine hptwise.trans ?_
    have hmono : (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4
        ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ₀) ^ 4 := by
      have hnum_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) := by positivity
      have hden_le : (1 - δ₀) ^ 4 ≤ (1 - δ) ^ 4 := by
        have h1 : (1 - δ₀) ≤ (1 - δ) := by linarith
        exact pow_le_pow_left₀ hcoeff₀.le h1 4
      apply div_le_div_of_nonneg_left hnum_nn (pow_pos hcoeff₀ 4) hden_le
    have hbase_nn : 0 ≤ Cg₀ + (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by
      have : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 3 * (K + K ^ 2) / (1 - δ) ^ 4 := by positivity
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


lemma g0FlatCLM_inverseMetricSharpFib (g₀ : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace 1 I x) :
    g0FlatCLM (I := I) g₀ x (inverseMetricSharpFib (I := I) g₀ x α) = α := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  rw [g0FlatCLM_apply, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent,
    cotangentToDualLinear_apply]
  ext w
  rw [cotangentToDual_apply, ContinuousLinearMap.coe_coe,
    inverseMetricSharpFib_inner (I := I) g₀ x α w, cotangentToDualLinear_apply,
    cotangentToDual_apply]


lemma g0Flat_model_expansion (g₀ : SmoothRiemannianMetric I M) (x : M) (u : TangentSpace I x) :
    (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x)
        (g0FlatCLM (I := I) g₀ x u) =
      ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x u ((Module.finBasis ℝ E) k) •
          Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k) := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.sum_apply]

  have hLHS : (Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x)
        (g0FlatCLM (I := I) g₀ x u) v = g₀.inner x u (v 0) := by
    change (g0FlatCLM (I := I) g₀ x u) v = g₀.inner x u (v 0)
    rw [g0FlatCLM_apply]
    have hv : v = (fun _ : Fin 1 => v 0) := by funext i; fin_cases i; rfl
    rw [hv, dualToCotangent_apply]
    rfl
  rw [hLHS]

  have hcDual : ∀ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k) v =
      (Module.finBasis ℝ E).repr (v 0 : E) k := by
    intro k
    rw [Tensor0SBundle.model_covectorOfCLM_apply]
    rw [show ((Module.finBasis ℝ E).cDualBasis k) =
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
      rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
      congr 1
      exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
    rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  rw [Finset.sum_congr rfl (fun k _ => by
    rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul, hcDual k])]

  have hexp : g₀.inner x u (v 0) =
      ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x u ((Module.finBasis ℝ E) k) * (Module.finBasis ℝ E).repr (v 0 : E) k := by
    have hbexp : (v 0 : TangentSpace I x) =
        ∑ i : Fin (Module.finrank ℝ E),
          (Module.finBasis ℝ E).repr (v 0 : E) i • ((Module.finBasis ℝ E) i : TangentSpace I x) :=
      ((Module.finBasis ℝ E).sum_repr (v 0 : E)).symm
    calc g₀.inner x u (v 0)
        = g₀.inner x u (∑ i : Fin (Module.finrank ℝ E),
            (Module.finBasis ℝ E).repr (v 0 : E) i • ((Module.finBasis ℝ E) i : TangentSpace I x)) :=
          congrArg (g₀.inner x u) hbexp
      _ = ∑ i : Fin (Module.finrank ℝ E),
            g₀.inner x u ((Module.finBasis ℝ E).repr (v 0 : E) i • ((Module.finBasis ℝ E) i : TangentSpace I x)) :=
          map_sum (g₀.inner x u) _ Finset.univ
      _ = ∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x u ((Module.finBasis ℝ E) k) * (Module.finBasis ℝ E).repr (v 0 : E) k := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [show g₀.inner x u
                ((Module.finBasis ℝ E).repr (v 0 : E) k • ((Module.finBasis ℝ E) k : TangentSpace I x))
              = (Module.finBasis ℝ E).repr (v 0 : E) k •
                  g₀.inner x u ((Module.finBasis ℝ E) k) from
            map_smul (g₀.inner x u) _ _]
          rw [smul_eq_mul, mul_comm]
  rw [hexp]

lemma cometricDoubleTrace_fiberComponent_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin 4 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) n e K J =
      g₀.inner x (e (K 0))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1)))) *
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
      (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) n e K J =
      Tensor0SBundle.Tensor0SSpace.toModel
        ((cometricDoubleTraceFib (I := I) g₁ 2 x)
          (coframeS (I := I) (M := M) g₀ x 4 e K))
        (fun k : Fin 2 => ((e (J k) : TangentSpace I x) : E)) := by
    unfold fiberNormSqComponent coframeS
    rfl
  rw [hcomp, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)
      (Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K))
      (fun k : Fin 2 => ((e (J k) : TangentSpace I x) : E))]

  have hsummand : ∀ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)
          (Fin.cons ((cometricLmodel (I := I) g₁ x)
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k)
              (fun k : Fin 2 => ((e (J k) : TangentSpace I x) : E)))) =
        (g₀.inner x (e (K 0)) ((cometricLmodel (I := I) g₁ x)
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))) *
          g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k)) *
            ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
    intro k
    have hcf : Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)
          (Fin.cons ((cometricLmodel (I := I) g₁ x)
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k)
              (fun k : Fin 2 => ((e (J k) : TangentSpace I x) : E))))
        = ∏ a : Fin 4, g₀.inner x (e (K a))
            ((Fin.cons ((cometricLmodel (I := I) g₁ x)
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              (Fin.cons ((Module.finBasis ℝ E) k)
                (fun k : Fin 2 => ((e (J k) : TangentSpace I x) : E))) :
              Fin 4 → TangentSpace I x) a) := by
      change (coframeS (I := I) (M := M) g₀ x 4 e K :
          Tensor0SBundle.Tensor0SSpace 4 I x)
          (Fin.cons ((cometricLmodel (I := I) g₁ x)
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k)
              (fun k : Fin 2 => ((e (J k) : TangentSpace I x) : E)))) = _
      rw [coframeS_apply]
    rw [hcf, Fin.prod_univ_four]
    simp only [Fin.cons_zero, Fin.cons_one]
    rw [show (Fin.cons ((cometricLmodel (I := I) g₁ x)
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k)
            (fun k : Fin 2 => ((e (J k) : TangentSpace I x) : E))) : Fin 4 → TangentSpace I x) 2
        = ((e (J 0) : TangentSpace I x) : E) from rfl,
      show (Fin.cons ((cometricLmodel (I := I) g₁ x)
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k)
            (fun k : Fin 2 => ((e (J k) : TangentSpace I x) : E))) : Fin 4 → TangentSpace I x) 3
        = ((e (J 1) : TangentSpace I x) : E) from rfl]
    rw [horth (K 2) (J 0), horth (K 3) (J 1)]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hsummand k)]

  rw [← Finset.sum_mul]

  refine congrArg (fun t : ℝ => t *
    ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ?_
  have hrhs : g₀.inner x (e (K 0))
        (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1)))) =
      ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x (e (K 0)) ((cometricLmodel (I := I) g₁ x)
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))) *
          g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) := by
    have hfac : inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1))) =
        (cometricLmodel (I := I) g₁ x)
          ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x)
            (g0FlatCLM (I := I) g₀ x (e (K 1)))) := by congr 1
    rw [hfac, g0Flat_model_expansion (I := I) g₀ x (e (K 1))]
    have hcm : (cometricLmodel (I := I) g₁ x)
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) •
              Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))
        = ∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) •
              (cometricLmodel (I := I) g₁ x)
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)) := by
      rw [map_sum (cometricLmodel (I := I) g₁ x) _ Finset.univ]
      exact Finset.sum_congr rfl (fun k _ => map_smul (cometricLmodel (I := I) g₁ x) _ _)
    rw [hcm]
    calc g₀.inner x (e (K 0))
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) •
              (cometricLmodel (I := I) g₁ x)
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
        = ∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 0))
              (g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) •
                (cometricLmodel (I := I) g₁ x)
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) :=
          map_sum (g₀.inner x (e (K 0))) _ Finset.univ
      _ = ∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 0)) ((cometricLmodel (I := I) g₁ x)
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) *
              g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [show g₀.inner x (e (K 0))
                (g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) •
                  (cometricLmodel (I := I) g₁ x)
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k)))
              = g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) •
                  g₀.inner x (e (K 0)) ((cometricLmodel (I := I) g₁ x)
                    (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                      ((Module.finBasis ℝ E).cDualBasis k))) from
            map_smul (g₀.inner x (e (K 0))) _ _]
          rw [smul_eq_mul, mul_comm]
  rw [hrhs]


theorem cometricDoubleTraceFib_fiberNormSq_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) (x : M)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      ccTensorBilin (I := I) g₀ S b u w = g₁.inner b u w - g₀.inner b u w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) g₀ (ccTensorBilin (I := I) g₀ S) δ) :
    Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ) ^ 2 := by
  classical
  have hcoeff : 0 < 1 - δ := by linarith

  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilin (I := I) g₀ S y v w := by
    intro y v w
    rw [hbil y v w]; ring

  obtain ⟨nn, e, bse, hnn, hbse, horth, hpar, hexp, hrepr⟩ :=
    tangent_orthonormalBasisRS_witness (I := I) (M := M) g₀ 4 2 x
  have hnnE : (nn : ℝ) = (Module.finrank ℝ E : ℝ) := by rw [hnn]; rfl
  set Ψ : Fin nn → TangentSpace I x := fun b =>
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)) with hΨ

  have hbrick : ∀ b : Fin nn, g₀.inner x (Ψ b) (Ψ b) ≤ (1 / (1 - δ)) ^ 2 := by
    intro b
    have hsqrt := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le
      (I := I) g₀ g₁ (ccTensorBilin (I := I) g₀ S) htie hδ_lt hδ_nn hδ x (e b)
    have hbb : g₀.inner x (e b) (e b) = 1 := by rw [horth b b]; simp
    rw [hbb, Real.sqrt_one, mul_one] at hsqrt
    have hnn0 : 0 ≤ g₀.inner x (Ψ b) (Ψ b) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x (Ψ b)
    have hsq := Real.sq_sqrt hnn0
    have h1δ : 0 ≤ 1 / (1 - δ) := by positivity
    nlinarith [Real.sqrt_nonneg (g₀.inner x (Ψ b) (Ψ b)), hsqrt, hsq, h1δ]

  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g₀ x 4 2 e hrepr _]

  have hcompsub : ∀ (K : Fin 4 → Fin nn) (J : Fin 2 → Fin nn),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) nn e K J) ^ 2 =
      (g₀.inner x (e (K 0)) (Ψ (K 1))) ^ 2 *
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
    intro K J
    have hΨK : Ψ (K 1) =
        inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1))) := rfl
    rw [cometricDoubleTrace_fiberComponent_eq (I := I) (M := M) g₀ g₁ x e horth K J, hΨK]
    by_cases h2 : K 2 = J 0 <;> by_cases h3 : K 3 = J 1 <;> simp [h2, h3]
  have hKbound : ∀ K : Fin 4 → Fin nn,
      (∑ J : Fin 2 → Fin nn,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) nn e K J) ^ 2)
        ≤ (1 / (1 - δ)) ^ 2 := by
    intro K
    rw [Finset.sum_congr rfl (fun J _ => hcompsub K J)]
    rw [← Finset.mul_sum]
    have hJsum : (∑ J : Fin 2 → Fin nn,
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) = 1 := by
      rw [← (finTwoArrowEquiv (Fin nn)).symm.sum_comp
        (fun J : Fin 2 → Fin nn =>
          (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))]
      rw [Fintype.sum_prod_type]
      simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [Finset.sum_eq_single (K 2)]
      · rw [Finset.sum_eq_single (K 3)]
        · rw [if_pos rfl, if_pos rfl, mul_one]
        · intro b _ hb; rw [if_pos rfl, if_neg (fun h => hb h.symm), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero (fun b _ => ?_)
        rw [if_neg (fun h => ha h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hJsum, mul_one]

    have hcs : (g₀.inner x (e (K 0)) (Ψ (K 1))) ^ 2 ≤ (1 / (1 - δ)) ^ 2 := by
      have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K 0)) (Ψ (K 1))
      have hkk : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
      rw [hkk, Real.sqrt_one, one_mul] at habs
      have hΨnn : 0 ≤ g₀.inner x (Ψ (K 1)) (Ψ (K 1)) :=
        metric_inner_self_nonneg (I := I) (M := M) g₀ x (Ψ (K 1))
      have hsqle : Real.sqrt (g₀.inner x (Ψ (K 1)) (Ψ (K 1))) ≤ 1 / (1 - δ) := by
        rw [show (1 : ℝ) / (1 - δ) = Real.sqrt ((1 / (1 - δ)) ^ 2) from by
          rw [Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_le_sqrt (hbrick (K 1))
      have hsq_abs : (g₀.inner x (e (K 0)) (Ψ (K 1))) ^ 2 ≤
          (Real.sqrt (g₀.inner x (Ψ (K 1)) (Ψ (K 1)))) ^ 2 := by
        have hsqabs : (g₀.inner x (e (K 0)) (Ψ (K 1))) ^ 2 =
            |g₀.inner x (e (K 0)) (Ψ (K 1))| ^ 2 := (sq_abs _).symm
        rw [hsqabs]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      calc (g₀.inner x (e (K 0)) (Ψ (K 1))) ^ 2
          ≤ (Real.sqrt (g₀.inner x (Ψ (K 1)) (Ψ (K 1)))) ^ 2 := hsq_abs
        _ ≤ (1 / (1 - δ)) ^ 2 := by
            have := hsqle
            nlinarith [Real.sqrt_nonneg (g₀.inner x (Ψ (K 1)) (Ψ (K 1))), hsqle,
              (by positivity : (0:ℝ) ≤ 1 / (1 - δ))]
    exact hcs

  have hsum_le : (∑ K : Fin 4 → Fin nn, ∑ J : Fin 2 → Fin nn,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) nn e K J) ^ 2)
        ≤ ((nn : ℝ) ^ 4) * (1 / (1 - δ)) ^ 2 := by
    calc (∑ K : Fin 4 → Fin nn, ∑ J : Fin 2 → Fin nn,
          (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
            (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) nn e K J) ^ 2)
        ≤ ∑ _K : Fin 4 → Fin nn, (1 / (1 - δ)) ^ 2 :=
          Finset.sum_le_sum (fun K _ => hKbound K)
      _ = ((nn : ℝ) ^ 4) * (1 / (1 - δ)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
          push_cast
          ring

  refine le_trans (Real.sqrt_le_sqrt hsum_le) ?_
  rw [show ((nn : ℝ) ^ 4) * (1 / (1 - δ)) ^ 2 = ((nn : ℝ) ^ 2 / (1 - δ)) ^ 2 from by
    rw [div_pow, one_pow, div_pow]; ring]
  rw [Real.sqrt_sq (by positivity)]
  rw [hnnE]
  have hδpow : (1 - δ) ^ 2 ≤ (1 - δ) := by nlinarith [hcoeff.le]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hδpow


set_option linter.unusedVariables false in
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
      (Cg₀ + (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ) ^ 2) ^ 2 := by
  have hcoeff : 0 < 1 - δ := by linarith
  have hcore := cometricDoubleTraceFib_fiberNormSq_le
    (I := I) (M := M) (x := x) g₀ g₁ S hbil hδ_lt hδ_nn hδ
  have hns : (ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) :=
    ricciArmPrincipalCoeffPure_toSection (I := I) (M := M) g₀ g₁ x
  rw [hns]
  have hrfns_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 4 2 x _
  have hpoly_nn : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ) ^ 2 := by positivity
  have heq : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x) =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x)) ^ 2 :=
    (Real.sq_sqrt hrfns_nn).symm
  rw [heq]
  have hbound : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x)) ≤
      Cg₀ + (Module.finrank ℝ E : ℝ) ^ 2 / (1 - δ) ^ 2 := by
    have := hcore
    linarith
  have hsqrt_nn : 0 ≤ Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      (show TensorRSSpace 4 2 I x from cometricDoubleTraceFib (I := I) g₁ 2 x)) :=
    Real.sqrt_nonneg _
  exact pow_le_pow_left₀ hsqrt_nn hbound 2

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
